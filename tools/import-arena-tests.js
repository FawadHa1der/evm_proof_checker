#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { createHash } = require('crypto');
const { build } = require('./build');
const { outcomeMatches } = require('./checker');
const { MODEL } = require('./budgets');
const { parseArgs, selectFiles } = require('./run-arena-tests');
const ROOT = path.join(__dirname, '..');
const hash = bytes => createHash('sha256').update(bytes).digest('hex');

function safeRelative(name) {
  if (!/^(good|bad|either)\/.+\.ndjson$/.test(name)
    || name.includes('\\') || name.split('/').some(x => x === '..' || x === '.' || !x)) {
    throw new Error(`invalid fixture path: ${name}`);
  }
  return name;
}

function validateCoverage(rows, selected) {
  const measured = new Set(rows.map(x => safeRelative(x.rel)));
  if (measured.size !== rows.length || measured.size !== selected.length
    || selected.some(x => !measured.has(x.rel))) {
    throw new Error('measurement must cover every corpus file exactly once; filtered reports cannot replace the snapshot');
  }
}

function existingHashes(dir, result = new Map()) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    if (dir === path.join(ROOT, 'tests') && ent.name === 'upstream') continue;
    const file = path.join(dir, ent.name);
    if (ent.isDirectory()) existingHashes(file, result);
    else if (ent.isFile() && file.endsWith('.ndjson')) {
      result.set(hash(fs.readFileSync(file)), path.relative(ROOT, file).split(path.sep).join('/'));
    }
  }
  return result;
}

function main(argv = process.argv.slice(2)) {
  if (argv.length !== 3) throw new Error('usage: node tools/import-arena-tests.js <corpus-dir> <report.json> <provenance.json>');
  const [corpus, reportFile, provenanceFile] = argv.map(x => path.resolve(x));
  const report = JSON.parse(fs.readFileSync(reportFile, 'utf8'));
  const provenance = JSON.parse(fs.readFileSync(provenanceFile, 'utf8'));
  validateCoverage(report.rows, selectFiles(parseArgs([corpus])).selected);
  if (report.profile !== 'glamsterdam' || report.budgetModel !== MODEL || report.summary.failed
    || report.summary.skipped || report.sourceHash !== build().sourceHash) {
    throw new Error('requires a complete, successful draft-profile report for the current build');
  }
  const existing = existingHashes(path.join(ROOT, 'tests'));
  const tests = [], aliases = [], excluded = [], staged = [];
  for (const row of report.rows) {
    const rel = safeRelative(row.rel);
    if (!row.matched || !outcomeMatches(row.expected, row.verdict) || !row.budget?.fitsTransaction) {
      excluded.push({ file: rel, outcome: row.expected, category: row.category, reason: row.reason });
      continue;
    }
    const bytes = fs.readFileSync(path.join(corpus, rel));
    const sha256 = hash(bytes);
    if (sha256 !== row.sha256) throw new Error(`fixture changed since measurement: ${rel}`);
    const entry = { name: rel.replace(/\.ndjson$/, ''), outcome: row.expected, sha256,
      bytes: bytes.length, measuredGas: row.gas,
      estimatedTransactionGas: row.budget.estimatedTransactionGas, requireTransactionFit: true };
    if (existing.has(sha256)) {
      aliases.push({ ...entry, coveredBy: existing.get(sha256) });
    } else {
      tests.push(entry);
      staged.push({ rel, bytes });
      existing.set(sha256, `tests/upstream/${rel}`);
    }
  }
  if (!tests.length && !aliases.length) throw new Error('no feasible checked fixtures in report');
  const dest = path.join(ROOT, 'tests/upstream');
  // Check all hashes and paths before changing the bundled snapshot.
  for (const { rel, bytes } of staged) {
    const file = path.join(dest, rel);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, bytes);
  }
  fs.mkdirSync(dest, { recursive: true });
  fs.writeFileSync(path.join(dest, 'manifest.json'), JSON.stringify({
    provenance, budgetModel: MODEL, sourceHash: report.sourceHash, compiler: report.compiler,
    measuredAt: report.timestamp, tests, aliases, excluded,
  }, null, 2) + '\n');
  console.log(`Bundled ${tests.length} byte-real fixtures; ${aliases.length} byte-identical cases already covered; ${excluded.length} explicit exclusions.`);
}

if (require.main === module) {
  try { main(); } catch (error) { console.error(error.message || error); process.exitCode = 1; }
}
module.exports = { safeRelative, validateCoverage };
