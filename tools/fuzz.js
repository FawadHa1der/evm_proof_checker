#!/usr/bin/env node
// Mutation fuzzer for the kernel's headline safety property: no input, however
// malformed, may produce a checker error — and a mutated valid proof must not
// be accepted unless the mutation happened to preserve meaning.
//
// Takes known-good exports, applies seeded structural mutations, and runs each
// through the contract in one in-process EVM. Reports the verdict distribution,
// every checker error (always a bug), and a sample of accepts for review.
//
//   node tools/fuzz.js [--seed=1] [--per-file=25] [--files=<glob-substring>]
'use strict';

const fs = require('fs');
const path = require('path');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('./lib');
const { build } = require('./build');
const { makeVm, installKernel, callContract, bytesToHex } = require('./evm');

const args = process.argv.slice(2);
const opt = (n, d) => {
  const a = args.find((x) => x.startsWith(`--${n}=`));
  return a ? a.slice(n.length + 3) : d;
};
const SEED = Number(opt('seed', 1));
const PER_FILE = Number(opt('per-file', 25));
const FILTER = opt('files', null);

// deterministic PRNG so a reported failure can be replayed exactly
let state = SEED >>> 0 || 1;
function rnd() {
  state ^= state << 13; state >>>= 0;
  state ^= state >> 17;
  state ^= state << 5; state >>>= 0;
  return state / 0x100000000;
}
const pick = (a) => a[Math.floor(rnd() * a.length)];
const rint = (n) => Math.floor(rnd() * n);

// --- mutations -------------------------------------------------------------
// Each takes the array of parsed NDJSON objects and returns a short label, or
// null if it did not apply to this file.

const MUTATIONS = [
  function bumpExprRef(lines) {
    const cands = [];
    lines.forEach((o, i) => {
      if (o.ie === undefined) return;
      for (const [k, v] of Object.entries(o)) {
        if (k === 'ie') continue;
        if (v && typeof v === 'object') {
          for (const f of ['fn', 'arg', 'type', 'body', 'value', 'struct']) {
            if (typeof v[f] === 'number') cands.push([i, k, f]);
          }
        }
      }
    });
    if (!cands.length) return null;
    const [i, k, f] = pick(cands);
    const o = lines[i];
    o[k][f] = rint(Math.max(1, i));
    return `expr#${i}.${k}.${f}`;
  },

  function bumpSortLevel(lines) {
    const cands = lines.map((o, i) => (o.sort !== undefined ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    lines[i].sort = rint(6);
    return `sort#${i}`;
  },

  function swapConstName(lines) {
    const cands = lines.map((o, i) => (o.const ? i : -1)).filter((i) => i >= 0);
    const names = lines.filter((o) => o.in !== undefined).map((o) => o.in);
    if (!cands.length || !names.length) return null;
    const i = pick(cands);
    lines[i].const.name = pick(names);
    return `const#${i}.name`;
  },

  function perturbInductiveCounts(lines) {
    const cands = lines.map((o, i) => (o.inductive ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const ind = lines[pick(cands)].inductive;
    const what = pick(['tp', 'ct', 'rc']);
    if (what === 'tp' && ind.types.length) {
      const t = pick(ind.types);
      const f = pick(['numParams', 'numIndices', 'numNested']);
      t[f] = Math.max(0, (t[f] || 0) + (rnd() < 0.5 ? 1 : -1));
      return `ind.type.${f}`;
    }
    if (what === 'ct' && ind.ctors.length) {
      const c = pick(ind.ctors);
      const f = pick(['numParams', 'numFields', 'cidx']);
      c[f] = Math.max(0, (c[f] || 0) + (rnd() < 0.5 ? 1 : -1));
      return `ind.ctor.${f}`;
    }
    if (what === 'rc' && ind.recs.length) {
      const r = pick(ind.recs);
      const f = pick(['numParams', 'numIndices', 'numMotives', 'numMinors']);
      r[f] = Math.max(0, (r[f] || 0) + (rnd() < 0.5 ? 1 : -1));
      return `ind.rec.${f}`;
    }
    return null;
  },

  function flipRecursorK(lines) {
    const cands = lines.map((o, i) => (o.inductive && o.inductive.recs.length ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const r = pick(lines[pick(cands)].inductive.recs);
    r.k = !r.k;
    return 'ind.rec.k';
  },

  function rewireRecursorRule(lines) {
    const cands = lines.map((o, i) => (o.inductive && o.inductive.recs.some((r) => r.rules.length) ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const ind = lines[pick(cands)].inductive;
    const r = pick(ind.recs.filter((x) => x.rules.length));
    const rule = pick(r.rules);
    if (rnd() < 0.5) rule.rhs = rint(Math.max(1, rule.rhs || 1));
    else rule.nfields = Math.max(0, (rule.nfields || 0) + 1);
    return 'ind.rec.rule';
  },

  function retypeDecl(lines) {
    const cands = lines.map((o, i) => (o.def || o.thm || o.axiom || o.opaque ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    const key = Object.keys(lines[i])[0];
    const d = lines[i][key];
    const f = d.value !== undefined && rnd() < 0.5 ? 'value' : 'type';
    d[f] = rint(Math.max(1, d[f] || 1));
    return `${key}.${f}`;
  },

  function perturbProj(lines) {
    const cands = lines.map((o, i) => (o.proj ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    if (rnd() < 0.5) lines[i].proj.idx += 1;
    else {
      const names = lines.filter((o) => o.in !== undefined).map((o) => o.in);
      if (names.length) lines[i].proj.typeName = pick(names);
    }
    return `proj#${i}`;
  },

  function perturbLevelParams(lines) {
    const cands = lines.map((o, i) => {
      const k = Object.keys(o)[0];
      return o[k] && o[k].levelParams ? i : -1;
    }).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    const d = lines[i][Object.keys(lines[i])[0]];
    if (d.levelParams.length && rnd() < 0.5) d.levelParams = d.levelParams.slice(0, -1);
    else d.levelParams = [...d.levelParams, d.levelParams[0] ?? 1];
    return 'levelParams';
  },

  function dropDecl(lines) {
    const cands = lines.map((o, i) => {
      const k = Object.keys(o)[0];
      return ['def', 'thm', 'axiom', 'opaque', 'inductive', 'quot'].includes(k) ? i : -1;
    }).filter((i) => i >= 0);
    if (cands.length < 2) return null;
    const i = pick(cands.slice(0, -1)); // keep the last decl so there is still something to check
    lines.splice(i, 1);
    return 'dropDecl';
  },

  function perturbNatLit(lines) {
    const cands = lines.map((o, i) => (o.natVal !== undefined ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    lines[i].natVal = String(Math.max(0, Number(lines[i].natVal) + (rnd() < 0.5 ? 1 : -1)));
    return `natVal#${i}`;
  },

  function perturbStrLit(lines) {
    const cands = lines.map((o, i) => (o.strVal !== undefined ? i : -1)).filter((i) => i >= 0);
    if (!cands.length) return null;
    const i = pick(cands);
    const s = String(lines[i].strVal);
    lines[i].strVal = s.length ? s.slice(0, -1) + String.fromCharCode(s.charCodeAt(s.length - 1) + 1) : 'x';
    return `strVal#${i}`;
  },
];

// --- harness ---------------------------------------------------------------

function collectGood() {
  const out = [];
  for (const g of ['good']) {
    const dir = path.join(__dirname, '..', 'tests', g);
    if (!fs.existsSync(dir)) continue;
    for (const f of fs.readdirSync(dir).filter((x) => x.endsWith('.ndjson'))) {
      if (FILTER && !f.includes(FILTER)) continue;
      out.push(path.join(dir, f));
    }
  }
  return out.sort();
}

async function main() {
  const artifacts = build();
  const vm = await makeVm();
  const addr = await installKernel(vm, artifacts);
  const iface = new ethers.Interface(KERNEL_ABI);

  async function check(lines) {
    const ndjson = lines.map((o) => JSON.stringify(o)).join('\n');
    let enc;
    try { enc = encodeForChain(parseNdjson(ndjson)); } catch (e) { return { v: 'ENCODE', reason: e.message }; }
    const cd = iface.encodeFunctionData('check', [enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab]);
    let r;
    try { r = await callContract(vm, addr, cd); } catch (e) { return { v: 'THROW', reason: String(e.message).slice(0, 80) }; }
    if (r.execResult.exceptionError) return { v: 'EVM-ERROR', reason: r.execResult.exceptionError.error };
    const [v, d, reason] = iface.decodeFunctionResult('check', bytesToHex(r.execResult.returnValue));
    return { v: VERDICT[Number(v)], decl: Number(d), reason: REASONS[Number(reason)] || String(reason) };
  }

  const files = collectGood();
  const tally = {};
  const alarms = [];
  const accepts = [];
  let n = 0;

  for (const f of files) {
    const base = fs.readFileSync(f, 'utf8').trim().split('\n').filter(Boolean).map((l) => JSON.parse(l));
    // sanity: the unmutated file must still be accepted
    const sane = await check(JSON.parse(JSON.stringify(base)));
    if (sane.v !== 'accept') {
      alarms.push({ file: path.basename(f), mutation: '(none - baseline)', ...sane });
    }
    for (let k = 0; k < PER_FILE; k++) {
      const lines = JSON.parse(JSON.stringify(base));
      const mut = pick(MUTATIONS);
      const label = mut(lines);
      if (!label) continue;
      const res = await check(lines);
      n++;
      tally[res.v] = (tally[res.v] || 0) + 1;
      // A checker error on ANY input is a bug: resource exhaustion must be
      // reported as such, never as a crash.
      if (res.v === 'EVM-ERROR' || res.v === 'THROW' || res.v === 'error') {
        alarms.push({ file: path.basename(f), mutation: `${mut.name}:${label}`, ...res });
      }
      if (res.v === 'accept') {
        accepts.push({ file: path.basename(f), mutation: `${mut.name}:${label}` });
      }
    }
  }

  console.log(`fuzz: seed=${SEED} files=${files.length} mutants=${n}`);
  console.log('verdicts:', JSON.stringify(tally));
  console.log(`accepts (mutation may have preserved meaning - review): ${accepts.length}`);
  for (const a of accepts.slice(0, 20)) console.log(`  ${a.file}  ${a.mutation}`);
  if (accepts.length > 20) console.log(`  ... and ${accepts.length - 20} more`);
  console.log(`\nALARMS (checker errors / bad baselines): ${alarms.length}`);
  for (const a of alarms) console.log(`  ${a.file}  ${a.mutation}  -> ${a.v} ${a.reason || ''}`);
  process.exit(alarms.length ? 1 : 0);
}

main().catch((e) => { console.error(e); process.exit(3); });
