// Shared library: lean4export NDJSON (v3.x) parsing, chain encoding,
// and a small HOAS builder used to generate test vectors.
'use strict';

const F = (1n << 48n) - 1n;
const NONE = F;

// expr tags (must match LeanKernel.sol)
const E = { BVAR: 0n, SORT: 1n, CONST: 2n, APP: 3n, LAM: 4n, PI: 5n, LET: 6n, NAT: 7n, STR: 8n, PROJ: 9n, UNSUP: 10n };
const L = { ZERO: 0n, SUCC: 1n, MAX: 2n, IMAX: 3n, PARAM: 4n };
const D = { AXIOM: 0n, DEF: 1n, THM: 2n, OPAQUE: 3n, QUOT: 4n, GROUP: 5n, IND: 6n, CTOR: 7n, REC: 8n, UNSUP: 9n };
const QUOT_KINDS = { type: 0n, ctor: 1n, lift: 2n, ind: 3n };

// ---------------------------------------------------------------------------
// NDJSON parsing
// ---------------------------------------------------------------------------
function parseNdjson(text) {
  const names = [{ tag: 'anon' }];
  const levels = [{ tag: 'zero' }];
  const exprs = [];
  const decls = [];
  let meta = null;

  const setAt = (arr, idx, v) => {
    while (arr.length < idx) arr.push(undefined);
    if (arr.length === idx) arr.push(v);
    else arr[idx] = v;
  };

  for (const line of text.split('\n')) {
    const s = line.trim();
    if (!s) continue;
    const o = JSON.parse(s);
    if (o.meta) { meta = o.meta; continue; }

    if (o.str !== undefined) { setAt(names, o.in, { tag: 'str', pre: o.str.pre, str: o.str.str }); continue; }
    if (o.num !== undefined) { setAt(names, o.in, { tag: 'num', pre: o.num.pre, i: o.num.i }); continue; }

    if (o.succ !== undefined) { setAt(levels, o.il, { tag: 'succ', a: o.succ }); continue; }
    if (o.max !== undefined) { setAt(levels, o.il, { tag: 'max', a: o.max[0], b: o.max[1] }); continue; }
    if (o.imax !== undefined) { setAt(levels, o.il, { tag: 'imax', a: o.imax[0], b: o.imax[1] }); continue; }
    if (o.param !== undefined) { setAt(levels, o.il, { tag: 'param', a: o.param }); continue; }

    if (o.bvar !== undefined) { setAt(exprs, o.ie, { tag: 'bvar', a: o.bvar }); continue; }
    if (o.sort !== undefined) { setAt(exprs, o.ie, { tag: 'sort', a: o.sort }); continue; }
    if (o.const !== undefined) { setAt(exprs, o.ie, { tag: 'const', name: o.const.name, us: o.const.us || [] }); continue; }
    if (o.app !== undefined) { setAt(exprs, o.ie, { tag: 'app', fn: o.app.fn, arg: o.app.arg }); continue; }
    if (o.lam !== undefined) { setAt(exprs, o.ie, { tag: 'lam', type: o.lam.type, body: o.lam.body }); continue; }
    if (o.forallE !== undefined) { setAt(exprs, o.ie, { tag: 'forallE', type: o.forallE.type, body: o.forallE.body }); continue; }
    if (o.letE !== undefined) { setAt(exprs, o.ie, { tag: 'letE', type: o.letE.type, value: o.letE.value, body: o.letE.body }); continue; }
    if (o.natVal !== undefined) { setAt(exprs, o.ie, { tag: 'natVal', v: String(o.natVal) }); continue; }
    if (o.strVal !== undefined) { setAt(exprs, o.ie, { tag: 'strVal', v: String(o.strVal) }); continue; }
    if (o.proj !== undefined) { setAt(exprs, o.ie, { tag: 'proj', typeName: o.proj.typeName, idx: o.proj.idx, struct: o.proj.struct }); continue; }
    if (o.mdata !== undefined) { setAt(exprs, o.ie, { tag: 'mdata', expr: o.mdata.expr }); continue; }

    if (o.axiom) { decls.push({ kind: 'axiom', ...o.axiom }); continue; }
    if (o.def) { decls.push({ kind: 'def', ...o.def }); continue; }
    if (o.thm) { decls.push({ kind: 'thm', ...o.thm }); continue; }
    if (o.opaque) { decls.push({ kind: 'opaque', ...o.opaque }); continue; }
    if (o.quot) {
      decls.push({
        kind: 'quot', name: o.quot.name, levelParams: o.quot.levelParams || [],
        type: o.quot.type, quotKindResolved: o.quot.kind,
      });
      continue;
    }
    if (o.inductive) { decls.push({ kind: 'inductive', types: o.inductive.types || [], ctors: o.inductive.ctors || [], recs: o.inductive.recs || [] }); continue; }
    decls.push({ kind: 'unsup' });
  }

  // resolve mdata nodes transparently (kernel-irrelevant wrapper)
  for (let i = 0; i < exprs.length; i++) {
    let e = exprs[i];
    const seen = new Set();
    while (e && e.tag === 'mdata' && !seen.has(e.expr)) {
      seen.add(e.expr);
      e = exprs[e.expr];
    }
    if (exprs[i] && exprs[i].tag === 'mdata') exprs[i] = e && e.tag !== 'mdata' ? e : { tag: 'unsup' };
  }
  return { meta, names, levels, exprs, decls };
}

// ---------------------------------------------------------------------------
// Chain encoding (must mirror LeanKernel.sol layouts)
// ---------------------------------------------------------------------------
function normalizeHints(h) {
  if (h === 'abbrev' || h === 'opaque') return h;
  if (h && typeof h === 'object') {
    if (h.regular !== undefined) return { regular: Number(h.regular) };
    if (h.kind === 'abbrev' || h.kind === 'opaque') return h.kind;
    if (h.kind === 'regular') return { regular: Number(h.height || 0) };
  }
  return { regular: 0 };
}

function encodeForChain(parsed) {
  const { names, levels, exprs, decls } = parsed;

  // names
  const nameTab = [0n];
  const strChunks = [];
  let strOff = 0n;
  for (let i = 1; i < names.length; i++) {
    const n = names[i] || { tag: 'str', pre: 0, str: '' };
    if (n.tag === 'str') {
      const bytes = Buffer.from(n.str, 'utf8');
      strChunks.push(bytes);
      nameTab.push((0n << 248n) | BigInt(n.pre) | (strOff << 48n) | (BigInt(bytes.length) << 96n));
      strOff += BigInt(bytes.length);
    } else {
      const v = BigInt(n.i);
      if (v > F) throw new Error('num name component exceeds 48 bits');
      nameTab.push((1n << 248n) | BigInt(n.pre) | (v << 48n));
    }
  }
  const nameStrs = '0x' + Buffer.concat(strChunks).toString('hex');

  // levels (index 0 = zero)
  const levelTab = [0n];
  for (let i = 1; i < levels.length; i++) {
    const l = levels[i];
    if (!l) { levelTab.push(0n); continue; }
    if (l.tag === 'succ') levelTab.push((L.SUCC << 248n) | BigInt(l.a));
    else if (l.tag === 'max') levelTab.push((L.MAX << 248n) | BigInt(l.a) | (BigInt(l.b) << 48n));
    else if (l.tag === 'imax') levelTab.push((L.IMAX << 248n) | BigInt(l.a) | (BigInt(l.b) << 48n));
    else if (l.tag === 'param') levelTab.push((L.PARAM << 248n) | BigInt(l.a));
    else levelTab.push(0n);
  }

  // exprs + pool
  const pool = [];
  const exprTab = [];
  const pushWindow = (items) => {
    const ptr = BigInt(pool.length);
    pool.push(BigInt(items.length));
    for (const it of items) pool.push(BigInt(it));
    return ptr;
  };
  for (let i = 0; i < exprs.length; i++) {
    const e = exprs[i];
    if (!e) { exprTab.push(E.UNSUP << 248n); continue; }
    switch (e.tag) {
      case 'bvar': exprTab.push((E.BVAR << 248n) | BigInt(e.a)); break;
      case 'sort': exprTab.push((E.SORT << 248n) | BigInt(e.a)); break;
      case 'const': {
        const s = BigInt(pool.length);
        for (const u of e.us) pool.push(BigInt(u));
        exprTab.push((E.CONST << 248n) | BigInt(e.name) | (s << 48n) | (BigInt(e.us.length) << 96n));
        break;
      }
      case 'app': exprTab.push((E.APP << 248n) | BigInt(e.fn) | (BigInt(e.arg) << 48n)); break;
      case 'lam': exprTab.push((E.LAM << 248n) | BigInt(e.type) | (BigInt(e.body) << 48n)); break;
      case 'forallE': exprTab.push((E.PI << 248n) | BigInt(e.type) | (BigInt(e.body) << 48n)); break;
      case 'letE': exprTab.push((E.LET << 248n) | BigInt(e.type) | (BigInt(e.value) << 48n) | (BigInt(e.body) << 96n)); break;
      case 'natVal': {
        let v;
        try { v = BigInt(e.v); } catch { v = null; }
        if (v === null || v < 0n) { exprTab.push(E.UNSUP << 248n); break; }
        const limbs = [];
        let x = v;
        while (x > 0n) { limbs.push(x & ((1n << 256n) - 1n)); x >>= 256n; }
        if (limbs.length === 0) limbs.push(0n);
        const ptr = BigInt(pool.length);
        pool.push(BigInt(limbs.length));
        for (const limb of limbs) pool.push(limb);
        exprTab.push((E.NAT << 248n) | ptr);
        break;
      }
      case 'strVal': {
        const bytes = Buffer.from(e.v, 'utf8');
        const words = [];
        for (let k = 0; k < bytes.length; k += 32) {
          const chunk = Buffer.alloc(32);
          bytes.copy(chunk, 0, k, Math.min(k + 32, bytes.length));
          words.push(BigInt('0x' + chunk.toString('hex')));
        }
        const ptr = BigInt(pool.length);
        pool.push(BigInt(bytes.length));
        for (const w of words) pool.push(w);
        exprTab.push((E.STR << 248n) | ptr);
        break;
      }
      case 'proj':
        exprTab.push((E.PROJ << 248n) | BigInt(e.typeName) | (BigInt(e.idx) << 48n) | (BigInt(e.struct) << 96n));
        break;
      default: exprTab.push(E.UNSUP << 248n);
    }
  }

  // decls
  const declTab = [];
  const word0 = (kind, name, type, value, lps) => {
    const lpS = BigInt(pool.length);
    for (const lp of lps || []) pool.push(BigInt(lp));
    return (kind << 248n) | BigInt(name) | (BigInt(type) << 48n) | (value << 96n) | (lpS << 144n) | (BigInt((lps || []).length) << 192n);
  };
  for (const d of decls) {
    if (d.kind === 'unsup') { declTab.push(D.UNSUP << 248n, 0n); continue; }
    if (d.kind === 'axiom') {
      if (d.isUnsafe) { declTab.push(D.UNSUP << 248n, 0n); continue; }
      declTab.push(word0(D.AXIOM, d.name, d.type, NONE, d.levelParams), 0n);
      continue;
    }
    if (d.kind === 'def' || d.kind === 'thm' || d.kind === 'opaque') {
      if (d.kind === 'def' && d.safety && d.safety !== 'safe') { declTab.push(D.UNSUP << 248n, 0n); continue; }
      if (d.kind === 'opaque' && d.isUnsafe) { declTab.push(D.UNSUP << 248n, 0n); continue; }
      const kind = { def: D.DEF, thm: D.THM, opaque: D.OPAQUE }[d.kind];
      let w1 = 0n;
      if (d.kind === 'def') {
        const h = normalizeHints(d.hints);
        if (h === 'abbrev') w1 = (1n << 248n) | (1n << 40n);
        else if (h === 'opaque') w1 = 2n << 248n;
        else w1 = BigInt(h.regular);
      }
      declTab.push(word0(kind, d.name, d.type, BigInt(d.value), d.levelParams), w1);
      continue;
    }
    if (d.kind === 'quot') {
      const qk = QUOT_KINDS[d.quotKindResolved ?? d.quotKind];
      if (qk === undefined) { declTab.push(D.UNSUP << 248n, 0n); continue; }
      declTab.push(word0(D.QUOT, d.name, d.type, NONE, d.levelParams), qk);
      continue;
    }
    if (d.kind === 'inductive') {
      const anyUnsafe = d.types.some((t) => t.isUnsafe) || d.ctors.some((c) => c.isUnsafe) || d.recs.some((r) => r.isUnsafe);
      if (anyUnsafe) { declTab.push(D.UNSUP << 248n, 0n); continue; }
      declTab.push(
        (D.GROUP << 248n),
        BigInt(d.types.length) | (BigInt(d.ctors.length) << 48n) | (BigInt(d.recs.length) << 96n)
      );
      for (const t of d.types) {
        const ctorsPtr = pushWindow(t.ctors || []);
        declTab.push(
          word0(D.IND, t.name, t.type, NONE, t.levelParams),
          BigInt(t.numParams) | (BigInt(t.numIndices) << 48n) | (ctorsPtr << 96n) | (BigInt(t.numNested || 0) << 144n)
        );
      }
      for (const c of d.ctors) {
        declTab.push(
          word0(D.CTOR, c.name, c.type, NONE, c.levelParams),
          BigInt(c.induct) | (BigInt(c.cidx) << 48n) | (BigInt(c.numParams) << 96n) | (BigInt(c.numFields) << 144n)
        );
      }
      for (const r of d.recs) {
        const rules = [];
        for (const rule of r.rules || []) rules.push(rule.ctor, rule.nfields, rule.rhs);
        const rulesPtr = BigInt(pool.length);
        pool.push(BigInt((r.rules || []).length));
        for (const x of rules) pool.push(BigInt(x));
        declTab.push(
          word0(D.REC, r.name, r.type, NONE, r.levelParams),
          (r.k ? (1n << 248n) : 0n) | BigInt(r.numParams) | (BigInt(r.numIndices) << 48n) |
            (BigInt(r.numMotives) << 96n) | (BigInt(r.numMinors) << 144n) | (rulesPtr << 192n)
        );
      }
      continue;
    }
    declTab.push(D.UNSUP << 248n, 0n);
  }

  return { nameTab, nameStrs, levelTab, exprTab, pool, declTab };
}

const KERNEL_ABI = [
  'function check(uint256[] nameTab, bytes nameStrs, uint256[] levelTab, uint256[] exprTab, uint256[] pool, uint256[] declTab) pure returns (uint8 verdict, uint64 failedDecl, uint16 reason)',
];
const REGISTRY_ABI = [
  'constructor(address kernel)',
  'function submit(uint256[] nameTab, bytes nameStrs, uint256[] levelTab, uint256[] exprTab, uint256[] pool, uint256[] declTab) returns (uint8 verdict)',
  'function isChecked(bytes32 exportHash) view returns (bool)',
  'function exportHashOf(uint256[] nameTab, bytes nameStrs, uint256[] levelTab, uint256[] exprTab, uint256[] pool, uint256[] declTab) pure returns (bytes32)',
  'event ExportChecked(bytes32 indexed exportHash, uint64 decls)',
];

const VERDICT = ['accept', 'reject', 'decline', 'error'];
const REASONS = [
  'ok', 'duplicate name', 'duplicate universe param', 'unknown constant',
  'universe count mismatch', 'undeclared universe param', 'type is not a sort',
  'theorem type not a Prop', 'value/type mismatch', 'bvar out of range',
  'application of non-function', 'application argument type mismatch',
  'binder domain is not a sort', 'let value type mismatch', 'unsupported feature',
  'step limit', 'depth limit',
  'inductive shape', 'constructor shape', 'positivity violation',
  'constructor result type', 'constructor result levels', 'field universe too large',
  'elimination universe violation', 'invalid K flag', 'recursor shape',
  'recursor rule invalid', 'projection violation', 'quotient shape',
];

// ---------------------------------------------------------------------------
// HOAS export builder (for generating test vectors)
// ---------------------------------------------------------------------------
class ExportBuilder {
  constructor() {
    this.names = [{ tag: 'anon' }];
    this.nameCache = new Map();
    this.levels = [{ tag: 'zero' }];
    this.levelCache = new Map();
    this.exprs = [];
    this.exprCache = new Map();
    this.decls = [];
    this.heights = new Map();
  }

  nameRaw(pre, str) {
    this.names.push({ tag: 'str', pre, str });
    return this.names.length - 1;
  }
  name(dotted) {
    let cur = 0;
    for (const part of String(dotted).split('.')) {
      const key = `${cur}:${part}`;
      if (this.nameCache.has(key)) cur = this.nameCache.get(key);
      else {
        cur = this.nameRaw(cur, part);
        this.nameCache.set(key, cur);
      }
    }
    return cur;
  }

  _lvl(node, key) {
    if (this.levelCache.has(key)) return this.levelCache.get(key);
    this.levels.push(node);
    const i = this.levels.length - 1;
    this.levelCache.set(key, i);
    return i;
  }
  lz() { return 0; }
  ls(a) { return this._lvl({ tag: 'succ', a }, `s:${a}`); }
  lnat(n) { let l = 0; for (let i = 0; i < n; i++) l = this.ls(l); return l; }
  lmax(a, b) { return this._lvl({ tag: 'max', a, b }, `m:${a}:${b}`); }
  limax(a, b) { return this._lvl({ tag: 'imax', a, b }, `i:${a}:${b}`); }
  lparam(n) { const ni = typeof n === 'string' ? this.name(n) : n; return this._lvl({ tag: 'param', a: ni }, `p:${ni}`); }

  _expr(node, key) {
    if (this.exprCache.has(key)) return this.exprCache.get(key);
    this.exprs.push(node);
    const i = this.exprs.length - 1;
    this.exprCache.set(key, i);
    return i;
  }
  eBVar(n) { return this._expr({ tag: 'bvar', a: n }, `b:${n}`); }
  eSort(l) { return this._expr({ tag: 'sort', a: l }, `s:${l}`); }
  eConst(n, us = []) {
    const ni = typeof n === 'string' ? this.name(n) : n;
    return this._expr({ tag: 'const', name: ni, us }, `c:${ni}:${us.join(',')}`);
  }
  eApp(f, a) { return this._expr({ tag: 'app', fn: f, arg: a }, `a:${f}:${a}`); }
  eLam(ty, body, nm = 0) { return this._expr({ tag: 'lam', type: ty, body, name: nm }, `l:${ty}:${body}`); }
  ePi(ty, body, nm = 0) { return this._expr({ tag: 'forallE', type: ty, body, name: nm }, `p:${ty}:${body}`); }
  eLet(ty, value, body, nm = 0) { return this._expr({ tag: 'letE', type: ty, value, body, name: nm }, `e:${ty}:${value}:${body}`); }
  eNatLit(s) { this.exprs.push({ tag: 'natVal', v: String(s) }); return this.exprs.length - 1; }
  eStrLit(s) { this.exprs.push({ tag: 'strVal', v: String(s) }); return this.exprs.length - 1; }
  eProj(typeName, idx, struct) {
    const tn = typeof typeName === 'string' ? this.name(typeName) : typeName;
    this.exprs.push({ tag: 'proj', typeName: tn, idx, struct });
    return this.exprs.length - 1;
  }

  // HOAS terms: functions of {depth, vars}
  S(l) { return () => this.eSort(l); }
  C(n, us = []) { return () => this.eConst(n, us); }
  A(f, ...args) { return (cx) => args.reduce((acc, t) => this.eApp(acc, t(cx)), f(cx)); }
  V(sym) { return (cx) => this.eBVar(cx.depth - 1 - cx.vars.get(sym)); }
  NAT(s) { return () => this.eNatLit(s); }
  STRL(s) { return () => this.eStrLit(s); }
  PROJ(typeName, idx, structT) { return (cx) => this.eProj(typeName, idx, structT(cx)); }
  _binder(mk, ty, fn) {
    return (cx) => {
      cx = cx || { depth: 0, vars: new Map() };
      const tyIdx = ty(cx);
      const sym = Symbol('x');
      const vars2 = new Map(cx.vars);
      vars2.set(sym, cx.depth);
      const body = fn(this.V(sym))({ depth: cx.depth + 1, vars: vars2 });
      return mk(tyIdx, body);
    };
  }
  Lam(ty, fn) { return this._binder((t, b) => this.eLam(t, b), ty, fn); }
  Pi(ty, fn) { return this._binder((t, b) => this.ePi(t, b), ty, fn); }
  Arrow(a, b) { return this.Pi(a, () => b); }
  Let(ty, val, fn) {
    return (cx) => {
      cx = cx || { depth: 0, vars: new Map() };
      const tyIdx = ty(cx);
      const valIdx = val(cx);
      const sym = Symbol('x');
      const vars2 = new Map(cx.vars);
      vars2.set(sym, cx.depth);
      const body = fn(this.V(sym))({ depth: cx.depth + 1, vars: vars2 });
      return this.eLet(tyIdx, valIdx, body);
    };
  }
  compile(term) { return typeof term === 'number' ? term : term({ depth: 0, vars: new Map() }); }

  _heightOfExpr(idx, seen = new Set()) {
    if (seen.has(idx)) return 0;
    seen.add(idx);
    const e = this.exprs[idx];
    if (!e) return 0;
    switch (e.tag) {
      case 'const': return this.heights.get(e.name) || 0;
      case 'app': return Math.max(this._heightOfExpr(e.fn, seen), this._heightOfExpr(e.arg, seen));
      case 'lam': case 'forallE':
        return Math.max(this._heightOfExpr(e.type, seen), this._heightOfExpr(e.body, seen));
      case 'letE':
        return Math.max(this._heightOfExpr(e.type, seen), this._heightOfExpr(e.value, seen), this._heightOfExpr(e.body, seen));
      case 'proj': return this._heightOfExpr(e.struct, seen);
      default: return 0;
    }
  }
  axiom(name, lps, ty) {
    const n = typeof name === 'string' ? this.name(name) : name;
    this.decls.push({ kind: 'axiom', name: n, levelParams: lps.map((s) => this.name(s)), type: this.compile(ty), isUnsafe: false });
    return n;
  }
  def(name, lps, ty, val, hints) {
    const n = typeof name === 'string' ? this.name(name) : name;
    const t = this.compile(ty);
    const v = this.compile(val);
    const h = hints !== undefined ? hints : { regular: this._heightOfExpr(v) + 1 };
    if (h && typeof h === 'object') this.heights.set(n, h.regular);
    this.decls.push({ kind: 'def', name: n, levelParams: lps.map((s) => this.name(s)), type: t, value: v, hints: h, safety: 'safe', all: [n] });
    return n;
  }
  thm(name, lps, ty, val) {
    const n = typeof name === 'string' ? this.name(name) : name;
    this.decls.push({ kind: 'thm', name: n, levelParams: lps.map((s) => this.name(s)), type: this.compile(ty), value: this.compile(val), all: [n] });
    return n;
  }
  opaque(name, lps, ty, val) {
    const n = typeof name === 'string' ? this.name(name) : name;
    this.decls.push({ kind: 'opaque', name: n, levelParams: lps.map((s) => this.name(s)), type: this.compile(ty), value: this.compile(val), isUnsafe: false, all: [n] });
    return n;
  }
  quot(name, lps, ty, quotKind) {
    const n = typeof name === 'string' ? this.name(name) : name;
    this.decls.push({ kind: 'quot', name: n, levelParams: lps.map((s) => this.name(s)), type: this.compile(ty), quotKind });
    return n;
  }
  /// types/ctors/recs use the same field names as the export format; type/rhs
  /// fields may be HOAS terms or raw expr indices.
  inductive(group) {
    const conv = (o, extra = {}) => ({
      ...o,
      ...extra,
      name: typeof o.name === 'string' ? this.name(o.name) : o.name,
      levelParams: (o.levelParams || []).map((s) => (typeof s === 'string' ? this.name(s) : s)),
      type: this.compile(o.type),
    });
    this.decls.push({
      kind: 'inductive',
      types: group.types.map((t) => conv({ numNested: 0, isRec: false, isUnsafe: false, isReflexive: false, ...t }, {
        all: (t.all || group.types.map((x) => x.name)).map((s) => (typeof s === 'string' ? this.name(s) : s)),
        ctors: (t.ctors || []).map((s) => (typeof s === 'string' ? this.name(s) : s)),
      })),
      ctors: (group.ctors || []).map((c) => conv({ isUnsafe: false, ...c }, {
        induct: typeof c.induct === 'string' ? this.name(c.induct) : c.induct,
      })),
      recs: (group.recs || []).map((r) => conv({ isUnsafe: false, k: false, ...r }, {
        all: (r.all || group.types.map((x) => x.name)).map((s) => (typeof s === 'string' ? this.name(s) : s)),
        rules: (r.rules || []).map((rule) => ({
          ctor: typeof rule.ctor === 'string' ? this.name(rule.ctor) : rule.ctor,
          nfields: rule.nfields,
          rhs: this.compile(rule.rhs),
        })),
      })),
    });
  }

  emit() {
    const out = [];
    out.push(JSON.stringify({
      meta: {
        exporter: { name: 'evmlean-gen', version: '0.1.0' },
        lean: { githash: '0000000000000000000000000000000000000000', version: '4.27.0-rc1' },
        format: { version: '3.1.0' },
      },
    }));
    for (let i = 1; i < this.names.length; i++) {
      const n = this.names[i];
      out.push(JSON.stringify(n.tag === 'str' ? { str: { pre: n.pre, str: n.str }, in: i } : { num: { pre: n.pre, i: n.i }, in: i }));
    }
    for (let i = 1; i < this.levels.length; i++) {
      const l = this.levels[i];
      if (l.tag === 'succ') out.push(JSON.stringify({ succ: l.a, il: i }));
      else if (l.tag === 'max') out.push(JSON.stringify({ max: [l.a, l.b], il: i }));
      else if (l.tag === 'imax') out.push(JSON.stringify({ imax: [l.a, l.b], il: i }));
      else out.push(JSON.stringify({ param: l.a, il: i }));
    }
    for (let i = 0; i < this.exprs.length; i++) {
      const e = this.exprs[i];
      switch (e.tag) {
        case 'bvar': out.push(JSON.stringify({ bvar: e.a, ie: i })); break;
        case 'sort': out.push(JSON.stringify({ sort: e.a, ie: i })); break;
        case 'const': out.push(JSON.stringify({ const: { name: e.name, us: e.us }, ie: i })); break;
        case 'app': out.push(JSON.stringify({ app: { fn: e.fn, arg: e.arg }, ie: i })); break;
        case 'lam': out.push(JSON.stringify({ lam: { name: e.name || 0, type: e.type, body: e.body, binderInfo: 'default' }, ie: i })); break;
        case 'forallE': out.push(JSON.stringify({ forallE: { name: e.name || 0, type: e.type, body: e.body, binderInfo: 'default' }, ie: i })); break;
        case 'letE': out.push(JSON.stringify({ letE: { name: e.name || 0, type: e.type, value: e.value, body: e.body, nondep: false }, ie: i })); break;
        case 'natVal': out.push(JSON.stringify({ natVal: e.v, ie: i })); break;
        case 'strVal': out.push(JSON.stringify({ strVal: e.v, ie: i })); break;
        case 'proj': out.push(JSON.stringify({ proj: { typeName: e.typeName, idx: e.idx, struct: e.struct }, ie: i })); break;
        default: throw new Error('emit: bad expr tag ' + e.tag);
      }
    }
    for (const d of this.decls) {
      const { kind, ...rest } = d;
      if (kind === 'inductive') {
        out.push(JSON.stringify({ inductive: { types: d.types, ctors: d.ctors, recs: d.recs } }));
      } else if (kind === 'quot') {
        const { quotKind, ...q } = rest;
        out.push(JSON.stringify({ quot: { ...q, kind: quotKind } }));
      } else {
        out.push(JSON.stringify({ [kind]: rest }));
      }
    }
    return out.join('\n') + '\n';
  }
}

module.exports = {
  parseNdjson, encodeForChain, ExportBuilder,
  KERNEL_ABI, REGISTRY_ABI, VERDICT, REASONS, NONE,
};
