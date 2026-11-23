#Requires -Version 7.4
param([ValidateRange(1, 16)][int] $Jobs = 2)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$root = Split-Path $PSScriptRoot -Parent
$out = Join-Path '.verification-work' ([DateTimeOffset]::UtcNow.ToString('yyyyMMdd-HHmmss-ffff'))
Push-Location $root
try {
    $null = New-Item -ItemType Directory -Path $out -Force
    $tools = 'lean', 'lake', 'leanexport', 'con-leche', 'con-ron', 'leanchecker'
    $resolvedLean = (& elan which lean | Out-String).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Elan could not resolve the pinned Lean toolchain.' }
    $leanBin = Split-Path $resolvedLean -Parent
    $suffix = [IO.Path]::GetExtension($resolvedLean)
    $binaryHashes = foreach ($tool in $tools) {
        $binary = Join-Path $leanBin ($tool + $suffix)
        [pscustomobject]@{ tool = $tool; sha256 = (Get-FileHash -LiteralPath $binary).Hash.ToLowerInvariant() }
    }
    $binaryHashes | ConvertTo-Json | Set-Content -Encoding utf8NoBOM "$out/binaries.json"
    & lake env lean --version > "$out/lean-version.txt"
    if ($LASTEXITCODE -ne 0) { throw 'Could not identify the compiler.' }
    & lake build *> "$out/build.log"
    if ($LASTEXITCODE -ne 0) { throw "Build failed. See $out/build.log" }
    & lake env lean verification/Audit.lean > "$out/axioms.log" 2> "$out/axioms.stderr"
    if ($LASTEXITCODE -ne 0) { throw "Axiom audit failed. See $out/axioms.log" }

    foreach ($group in 'association', 'compression', 'measurement', 'examples') {
        $roots = Get-Content -LiteralPath "verification/roots/$group.txt"
        $proof = "$out/$group.ndjson"
        & lake env leanexport VerificationAll -- @roots > $proof 2> "$out/$group.export.stderr"
        if ($LASTEXITCODE -ne 0) { throw "Export failed for $group." }
        $digest = (Get-FileHash -LiteralPath $proof).Hash
        foreach ($checker in 'con-leche', 'con-ron', 'leanchecker') {
            $arguments = if ($checker -eq 'leanchecker') {
                @('--from-export', $proof)
            } else {
                @('--verified', "--jobs=$Jobs", $proof)
            }
            & lake env $checker @arguments > "$out/$group.$checker.stdout" 2> "$out/$group.$checker.stderr"
            if ($LASTEXITCODE -ne 0) { throw "$checker rejected $group. See its logs in $out." }
            if ((Get-FileHash -LiteralPath $proof).Hash -cne $digest) { throw "$group changed during checking." }
            Write-Host "$group / $checker / exit 0"
        }
    }
    & node verification/CheckExports.mjs $out
    if ($LASTEXITCODE -ne 0) { throw 'Export membership or axiom coverage did not match the inventory.' }
    Write-Host "Results and exported proof objects are in $out"
} finally {
    Pop-Location
}
