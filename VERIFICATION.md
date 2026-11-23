# Verification of the formal propositions

On 23 November 2026 the Lean 4.36.0 kernel compiled the source in this release. Two external checkers, **con-leche** and **con-ron**, each accepted four exports in verified mode. The Lean reference kernel also replayed each export with `leanchecker --from-export`. Every one of the **562 named public theorems** occurs in an accepted export as a theorem record containing a proof expression. The four exports cover **899 explicitly named public declarations** across 16 source modules. The report records the SHA-256 digest of each source and each export, together with the compiler and checker binary digests. [Machine-readable results](verification/evidence/results.json)

The checked objects are the propositions written in the Lean files. For a statement about an instrument, waveform model or analysis, the interpretation depends on identifying its observable, target and assumptions with those in the formal proposition. The article and theorem index give those identifications where used. [Research article](README.md) · [Theorem index](docs/theorem-index.md)

## What the checkers accepted

| Export and list of root names | Named declarations selected | Theorem proofs selected | Declarations accepted by each external checker | Lean reference kernel |
| --- | ---: | ---: | ---: | --- |
| [Association, calibration and congruence](verification/roots/association.txt) | 293 | 214 | 1,697 | Accepted |
| [Compression, null spaces and the three supplements](verification/roots/compression.txt) | 288 | 173 | 2,010 | Accepted |
| [Equality, measurement, LIGO transformations and the published ledger](verification/roots/measurement.txt) | 261 | 147 | 2,068 | Accepted |
| [Quantity-kind and unit-calibration examples](verification/roots/examples.txt) | 57 | 28 | 2,270 | Accepted |

Each checker read the same export bytes for a given row and exited with status 0. The 899 names are distinct across the four root lists. The larger acceptance counts include the dependencies needed to type-check the selected declarations. Some of those dependencies occur in more than one export. The checker logs retain their remarks about inductive blocks modelled in process and declarations processed ahead of pinned natural-number operations. [Checker transcripts](verification/evidence/checkers.log)

The source inventory gives the module, fully qualified name, declaration kind and source line. It covers explicit public names for theorems, definitions, abbreviations and types. Private proof helpers and compiler-generated declarations enter an export through the public results that depend on them. The membership check reads the name table and declaration records in each exported proof object and verifies the theorem proof-expression fields. [Declaration inventory](verification/declarations.tsv) · [Membership checker](verification/CheckExports.mjs)

## Axiom audit

Lean evaluated `#print axioms` for each of the 899 inventoried declarations. The audit matched all 899 distinct names to the inventory. For 525 declarations the kernel reported no axiom dependencies. The remaining declarations use the standard Lean axioms shown below. No custom axiom or `sorryAx` appeared in these transitive dependency reports. [Exact reports by declaration](verification/evidence/axioms.log) · [Audit source](verification/Audit.lean)

| Transitive axiom set | Named declarations |
| --- | ---: |
| None | 525 |
| `propext` | 163 |
| `Quot.sound` | 3 |
| `propext`, `Quot.sound` | 181 |
| `propext`, `Quot.sound`, `Classical.choice` | 27 |

The full clean build completed 36 Lake jobs with exit status 0. Its 26 warnings concern deprecated proof syntax or unused simplification arguments and variables. The log retains the warnings and the compiler's in-source axiom reports. [Build transcript](verification/evidence/build.log)

## Reproduce the checks

The release pins `leanprover/lean4:v4.36.0`. The recorded run used the Windows x86-64 release of Lean at commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The Lake manifest contains no external package dependencies. For the full replay, use Elan with the pinned toolchain, access to its `leanexport`, `con-leche`, `con-ron` and `leanchecker` executables, PowerShell 7.4 or later and Node.js 18 or later. The script locates the checker binaries next to the compiler. [Toolchain](lean-toolchain) · [Lake configuration](lakefile.toml) · [Replay script](verification/Run.ps1)

From a clean checkout, run the following in the repository root.

```powershell
pwsh -NoProfile -File ./verification/Run.ps1 -Jobs 4
```

The run writes a new directory inside `.verification-work/`. It contains the build log, per-declaration axiom reports, the exact four NDJSON exports, stdout and stderr from each checker, and `results.json`. Check the export hashes against the published report for a byte-for-byte comparison. For a Lean build and axiom audit alone, these are the two commands used by the script.

```powershell
lake build
lake env lean verification/Audit.lean
```

For example, these commands reproduce the association export and its three kernel checks from a build. Run them in PowerShell 7.4 or later so that native stdout redirected to a file retains its bytes.

```powershell
$roots = Get-Content verification/roots/association.txt
lake env leanexport VerificationAll -- @roots > association.ndjson
lake env con-leche --verified --jobs=4 association.ndjson
lake env con-ron --verified --jobs=4 association.ndjson
lake env leanchecker --from-export association.ndjson
```

## Source provenance

The research manuscript supplied the ten source bodies for `PerfectAssociation.lean`, seven of its library modules (algebra, equality bridge, LIGO anchors, calibration, congruence, model and statistics), and the equality and measurement modules of `RequestProject`. The publication preserves those bodies, normalizing line endings and their boundaries as files.

Five additional original modules provide the manuscript's concrete results on [compression](PerfectAssociation/LigoCompression.lean), [the null space](PerfectAssociation/LigoNullSpace.lean), [LIGO measurement transformations](RequestProject/LIGO_specious_measures.lean), [the published numerical ledger](RequestProject/LIGO_published_ledger.lean) and [unit calibration](RequestProject/Examples.lean). Two archived proof expressions in the transformations module needed explicit elaboration for Lean 4.36.0. One projects the first component of an equality of pairs. The other reduces a closed integer goal to `4 ≠ 2`. The names, statements and mathematical witnesses are preserved. Reversing the two-hunk patch recovers the archived file at SHA-256 `90f1b290f81a8dfe40b89c4f10d0b78733953f1436ed6a1b3ae41f94b00c467f`. [Exact compatibility patch](verification/lean-4.36-compatibility.patch)

The manuscript states three supplemental propositions by full name and provides their derivations in Part I §§38, 39 and 43. For this release their proof terms were reconstructed from those derivations using the original moment, row and state definitions. All three have the same compiler, axiom and independent-checker evidence as the other theorem roots. The aggregate import module assembles the checked release. [Supplemental proofs](VerificationCorrections.lean) · [Aggregate imports](VerificationAll.lean)
