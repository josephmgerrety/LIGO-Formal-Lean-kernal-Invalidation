import { createReadStream, readFileSync, statSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { join } from 'node:path';
import { createInterface } from 'node:readline';

const directory = process.argv[2];
if (!directory) throw Error('Usage from the repository root: node verification/CheckExports.mjs <run-directory>');
const read = (path) => readFileSync(path, 'utf8');
const lines = (path) => read(path).trimEnd().split(/\r?\n/);
const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');
const groups = ['association', 'compression', 'measurement', 'examples'];
const declarations = new Map(lines('verification/declarations.tsv').slice(1).map(line => {
  const [module, name, kind, lineNumber] = line.split('\t');
  return [name, { module, kind, line: Number(lineNumber) }];
}));
const allowed = new Set(['propext', 'Quot.sound', 'Classical.choice']);
const audited = new Map();
for (const line of lines(join(directory,'axioms.log'))) {
  const match = /^'(.+)' (?:does not depend on any axioms|depends on axioms: \[(.*)\])$/.exec(line);
  if (!match) throw Error('Unrecognized axiom report: ' + line);
  const name = match[1];
  if (!declarations.has(name) || audited.has(name)) throw Error('Unexpected or duplicate axiom report: ' + name);
  const axioms = match[2] ? match[2].split(', ').map(x=>x.trim()) : [];
  for (const ax of axioms) if (!allowed.has(ax)) throw Error('Unexpected axiom in ' + name + ': ' + ax);
  audited.set(name, axioms);
}
if (audited.size !== declarations.size) throw Error('Missing declaration axiom reports');
const evidence = [];
const allSelected = new Set();

for (const group of groups) {
  const roots = lines('verification/roots/' + group + '.txt');
  const expect = new Set(roots);
  for (const name of roots) {
    if (!declarations.has(name) || allSelected.has(name)) throw Error('Unexpected or repeated export root: ' + name);
    allSelected.add(name);
  }
  const file = join(directory, group + '.ndjson');
  const names = [''];
  const observed = new Set();
  const check = (id, kind) => {
    const name = names[id];
    if (!expect.has(name)) return;
    if (['theorem','lemma'].includes(declarations.get(name).kind) && kind !== 'thm') {
      throw Error(name + ' has no theorem record in its export');
    }
    observed.add(name);
  };
  for await (const line of createInterface({ input: createReadStream(file), crlfDelay: Infinity })) {
    const item = JSON.parse(line);
    if (item.str || item.num) {
      const node = item.str || item.num;
      const prefix = names[node.pre];
      if (prefix === undefined) throw Error('Missing export name prefix ' + node.pre);
      names[item.in] = (prefix ? prefix + '.' : '') + (node.str ?? node.i);
    } else if (item.inductive) {
      for (const decl of item.inductive.types) check(decl.name, 'inductive');
      for (const decl of item.inductive.ctors) check(decl.name, 'ctor');
      for (const decl of item.inductive.recs) check(decl.name, 'recursor');
    } else {
      for (const kind of ['thm','def','opaque','axiom']) if (item[kind]) {
        if (kind === 'thm' && !Number.isInteger(item.thm.value)) throw Error('Theorem with missing proof expression');
        check(item[kind].name, kind);
      }
    }
  }
  const missing = roots.filter(root => !observed.has(root));
  if (missing.length) throw Error('Roots missing from ' + group + ': ' + missing.join(', '));
  const accept = {};
  for (const checker of ['con-leche','con-ron','leanchecker']) {
    const output = read(join(directory,group+'.'+checker+'.stdout')).trim();
    if (checker === 'leanchecker') {
      if (!output.includes('Lean default kernel accepts the solution')) throw Error('Missing Lean kernel acceptance');
      accept[checker] = output;
    } else {
      const match = /^con-(?:leche|ron): accepted (\d+) declarations \(--verified\)$/.exec(output);
      if (!match) throw Error('Missing verified-mode acceptance from ' + checker);
      accept[checker] = { declarations: Number(match[1]), mode: 'verified' };
    }
  }
  evidence.push({ group, selectedRoots: roots.length,
    theoremRoots: roots.filter(name=>['theorem','lemma'].includes(declarations.get(name).kind)).length,
    rootsPresent: observed.size, exportBytes: statSync(file).size,
    exportSHA256: sha256(readFileSync(file)), acceptance: accept });
}
if (declarations.size !== allSelected.size) throw Error('The root lists do not cover every inventoried declaration');
const dependencies = {};
for (const axioms of audited.values()) {
  const set = [...axioms].sort().join(', ') || 'none';
  dependencies[set] = (dependencies[set] || 0) + 1;
}
const sourcePaths = new Set(['lean-toolchain','lakefile.toml','lake-manifest.json','VerificationAll.lean',
  'verification/declarations.tsv', 'verification/Audit.lean',
  ...groups.map(group => 'verification/roots/' + group + '.txt')]);
for (const {module} of declarations.values()) sourcePaths.add(module.replaceAll('.','/')+'.lean');
const sources = Object.fromEntries([...sourcePaths].sort().map(p=>[p,sha256(readFileSync(p))]));
const report = { lean: read(join(directory,'lean-version.txt')).trim(), publicDeclarations: declarations.size,
  publicTheorems: evidence.reduce((n,g)=>n+g.theoremRoots,0),
  declarationAxiomReports: audited.size, axiomDependencyCounts: dependencies, exports: evidence,
  sourceSHA256: sources, binarySHA256: JSON.parse(read(join(directory,'binaries.json'))) };
writeFileSync(join(directory,'results.json'),JSON.stringify(report,null,2)+'\n');
console.log(report.publicDeclarations + ' named declarations and ' + report.publicTheorems +
  ' theorem proof records verified across ' + evidence.length + ' exports.');
