#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { makeChecker, checkFile, outcomeMatches } = require('./checker');
const { VERDICT } = require('./lib');
const { DEFAULT_GAS_LIMIT, MODEL, parseLimit, parseByteLimit } = require('./budgets');

function usage() {
  return [
    'usage: node tools/run-arena-tests.js <arena-test-dir> [options]',
    '  --tutorial                     run only tutorial/*',
    '  --include=<regex>              filter relative paths',
    '  --max-bytes=<n>                explicitly skip larger files',
    '  --entrypoint-max-bytes=<n>     decline larger files (0 disables)',
    '  --gas-limit=<n>                local call budget (default 10 billion)',
    '  --profile=local|glamsterdam    local EVM or draft direct-call budget model',
    '  --allow-decline                tolerate declines, reported separately',
    '  --allow-non-tutorial-decline   tolerate declines outside tutorial/*',
    '  --json=<path>                  write a complete machine-readable report',
    '  --verbose                     print each test and its result',
    'Reads good/, bad/, and either/. Arena currently omits either/ from its tarball.',
  ].join('\n');
}

function parseArgs(argv) {
  const opts = { root: null, tutorial: false, include: null, maxBytes: null,
    entrypointMaxBytes: 0, allowDecline: false, allowNonTutorialDecline: false,
    gasLimit: DEFAULT_GAS_LIMIT, profile: 'local', json: null, verbose: false };
  for (const arg of argv) {
    if (arg === '--tutorial') opts.tutorial = true;
    else if (arg === '--allow-decline') opts.allowDecline = true;
    else if (arg === '--allow-non-tutorial-decline') opts.allowNonTutorialDecline = true;
    else if (arg === '--verbose') opts.verbose = true;
    else if (arg.startsWith('--include=')) opts.include = new RegExp(arg.slice('--include='.length));
    else if (arg.startsWith('--max-bytes=')) opts.maxBytes = parseByteLimit(arg.slice('--max-bytes='.length), '--max-bytes');
    else if (arg.startsWith('--entrypoint-max-bytes=')) opts.entrypointMaxBytes = parseByteLimit(arg.slice('--entrypoint-max-bytes='.length), '--entrypoint-max-bytes');
    else if (arg.startsWith('--gas-limit=')) opts.gasLimit = parseLimit(arg.slice('--gas-limit='.length), '--gas-limit');
    else if (arg.startsWith('--profile=')) opts.profile = arg.slice('--profile='.length);
    else if (arg.startsWith('--json=')) opts.json = path.resolve(arg.slice('--json='.length));
    else if (!arg.startsWith('-') && !opts.root) opts.root = path.resolve(arg);
    else throw new Error('unknown argument: ' + arg);
  }
  if (!opts.root) throw new Error('missing arena-test-dir');
  if (!['local', 'glamsterdam'].includes(opts.profile)) throw new Error('invalid --profile');
  return opts;
}

function walk(dir, out = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    const file = path.join(dir, ent.name);
    if (ent.isDirectory()) walk(file, out);
    else if (ent.isFile() && file.endsWith('.ndjson')) out.push(file);
  }
  return out;
}

function selectFiles(opts) {
  const selected = [], skipped = [];
  for (const [group, expected] of [['good', 'accept'], ['bad', 'reject'], ['either', 'either']]) {
    const dir = path.join(opts.root, group);
    if (!fs.existsSync(dir)) continue;
    for (const file of walk(dir)) {
      const rel = path.relative(opts.root, file).split(path.sep).join('/');
      if (opts.tutorial && !rel.includes('/tutorial/')) continue;
      if (opts.include && !opts.include.test(rel)) continue;
      const entry = { file, rel, expected, bytes: fs.statSync(file).size };
      if (opts.maxBytes !== null && entry.bytes > opts.maxBytes) skipped.push(entry);
      else selected.push(entry);
    }
  }
  return { selected: selected.sort((a, b) => a.rel.localeCompare(b.rel)), skipped };
}

async function main(argv = process.argv.slice(2)) {
  if (argv.includes('--help') || argv.includes('-h')) { console.log(usage()); return; }
  const opts = parseArgs(argv);
  const { selected, skipped } = selectFiles(opts);
  if (!selected.length) throw new Error('no .ndjson files selected');
  const checker = await makeChecker();
  console.log('profile=' + opts.profile + '; ' + selected.length + ' selected, ' + skipped.length
    + ' skipped; local gas budget=' + opts.gasLimit);
  if (opts.profile === 'glamsterdam') console.log('Budget model: ' + MODEL + '; Cancun EVM, not a full fork client.');
  const summary = { selected: selected.length, skipped: skipped.length, exact: 0,
    eitherChecked: 0, declined: 0, declinedOk: 0, failed: 0, transactionCandidates: 0 };
  const rows = [];
  for (const entry of selected) {
    if (opts.verbose) console.log('checking ' + entry.rel);
    const result = await checkFile(entry.file, checker, {
      maxBytes: opts.entrypointMaxBytes, gasLimit: opts.gasLimit, profile: opts.profile,
    });
    const matched = outcomeMatches(entry.expected, result.verdict);
    const declineOk = result.verdict === 2 && (opts.allowDecline
      || (opts.allowNonTutorialDecline && !entry.rel.includes('/tutorial/')));
    if (matched) {
      if (entry.expected === 'either') summary.eitherChecked++;
      else summary.exact++;
    }
    if (result.verdict === 2) summary.declined++;
    if (declineOk) summary.declinedOk++;
    if (!matched && !declineOk) summary.failed++;
    if (matched && result.budget?.fitsTransaction) summary.transactionCandidates++;
    const row = { rel: entry.rel, expected: entry.expected, got: VERDICT[result.verdict],
      ok: matched || declineOk, matched, ...result };
    rows.push(row);
    if (opts.verbose || !row.ok) console.log(entry.rel + ': ' + row.got + '; gas=' + result.gas
      + '; ' + result.category + ': ' + result.reason);
  }
  const report = {
    timestamp: new Date().toISOString(), profile: opts.profile, budgetModel: MODEL,
    sourceHash: checker.artifacts.sourceHash, compiler: checker.artifacts.compiler,
    deployedSize: checker.artifacts.LeanKernel.deployedSize,
    initcodeSize: checker.artifacts.LeanKernel.initcodeSize,
    gasLimit: opts.gasLimit, entrypointMaxBytes: opts.entrypointMaxBytes,
    summary, skipped: skipped.map(({ file, ...entry }) => entry), rows,
  };
  if (opts.json) {
    fs.mkdirSync(path.dirname(opts.json), { recursive: true });
    fs.writeFileSync(opts.json, JSON.stringify(report, (_, v) => typeof v === 'bigint' ? String(v) : v, 2) + '\n');
  }
  console.log('arena tests: ' + summary.selected + ' selected, ' + summary.exact + ' exact, '
    + summary.eitherChecked + ' either checked, ' + summary.declined + ' declined ('
    + summary.declinedOk + ' tolerated), ' + summary.failed + ' failed, ' + summary.skipped + ' skipped');
  console.log('Direct-call transaction candidates under ' + MODEL + ': '
    + summary.transactionCandidates + '; not deployment evidence.');
  if (summary.failed) process.exitCode = 1;
  return report;
}

if (require.main === module) main().catch((error) => { console.error(error.message || error); process.exitCode = 1; });
module.exports = { parseArgs, selectFiles, main };
