#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');
const YAML = require('yaml');
const ROOT = path.join(__dirname, '..');
const REPO = 'leanprover/lean-kernel-arena';

function validateOutcome(text, name) {
  const meta = YAML.parse(text);
  if (!meta || !['accept', 'reject', 'either'].includes(meta.outcome)) {
    throw new Error(`${name}: missing or invalid outcome (accept/reject/either required)`);
  }
  return meta.outcome;
}

function walk(dir, base = dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap(ent => {
    const file = path.join(dir, ent.name);
    if (ent.isDirectory()) return walk(file, base);
    return ent.isFile() ? [path.relative(base, file).split(path.sep).join('/')] : [];
  });
}

async function download(url, json = false) {
  const headers = { 'User-Agent': 'evmlean-arena-test-sync' };
  if (process.env.GITHUB_TOKEN && new URL(url).hostname === 'api.github.com') {
    headers.Authorization = `Bearer ${process.env.GITHUB_TOKEN}`;
  }
  const response = await fetch(url, { headers, signal: AbortSignal.timeout(60000) });
  if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
  return json ? response.json() : response.text();
}

async function main(argv = process.argv.slice(2)) {
  let source = null, ref = 'master';
  for (const arg of argv) {
    if (arg.startsWith('--source=')) source = path.resolve(arg.slice(9));
    else if (arg.startsWith('--ref=')) ref = arg.slice(6);
    else throw new Error(`unknown argument: ${arg}`);
  }
  let revision, files, read;
  if (source) {
    revision = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: source, encoding: 'utf8' }).trim();
    files = walk(path.join(source, 'tests'));
    read = async name => fs.readFileSync(path.join(source, 'tests', name), 'utf8');
  } else {
    const commit = await download(`https://api.github.com/repos/${REPO}/commits/${encodeURIComponent(ref)}`, true);
    revision = commit.sha;
    const tree = await download(`https://api.github.com/repos/${REPO}/git/trees/${commit.commit.tree.sha}?recursive=1`, true);
    if (tree.truncated) throw new Error('GitHub returned a truncated tree; use --source=<local-clone>');
    files = tree.tree.filter(x => x.type === 'blob' && x.path.startsWith('tests/')).map(x => x.path.slice(6));
    read = name => download(`https://raw.githubusercontent.com/${REPO}/${revision}/tests/${name}`);
  }
  const staged = [];
  for (const file of files.filter(x => x.endsWith('.ndjson')).sort()) {
    if (file.split('/').some(x => x === '..' || x === '') || path.isAbsolute(file)) throw new Error('invalid upstream path');
    const yaml = file.replace(/\.ndjson$/, '.yaml');
    if (!files.includes(yaml)) throw new Error(`${file}: missing YAML metadata`);
    const text = await read(file);
    const metadata = await read(yaml);
    const outcome = validateOutcome(metadata, yaml);
    staged.push({ file, yaml, text, metadata, outcome });
  }
  if (!staged.length) throw new Error('no static Arena fixtures found');
  // Validate every download before replacing any bundled fixture.
  for (const item of staged) {
    for (const [name, text] of [[item.file, item.text], [item.yaml, item.metadata]]) {
      const dest = path.join(ROOT, 'tests/arena', name);
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.writeFileSync(dest, text);
    }
    console.log(`${item.file}: ${item.outcome}`);
  }
  fs.writeFileSync(path.join(ROOT, 'tests/arena/source.json'), JSON.stringify({
    repository: `https://github.com/${REPO}`, revision,
    files: staged.map(({ file, outcome }) => ({ file, outcome })),
  }, null, 2) + '\n');
  console.log(`Synced ${staged.length} static tests at ${revision}; generated Lean tests are separate.`);
}

if (require.main === module) main().catch(error => { console.error(error.message || error); process.exitCode = 1; });
module.exports = { validateOutcome };
