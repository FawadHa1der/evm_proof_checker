// Generates NDJSON test vectors mirroring the Lean Kernel Arena tutorial
// sequence (https://arena.lean-lang.org/ → tutorial/Tutorial.lean), in the
// lean4export v3.1.0 NDJSON format, for the fragment evmlean supports.
//
// Layout: tests/good/*.ndjson (expect accept), tests/bad/*.ndjson (expect
// reject), tests/decline/*.ndjson (expect decline) + tests/manifest.json.
'use strict';

const fs = require('fs');
const path = require('path');
const { ExportBuilder } = require('./lib');

const ROOT = path.join(__dirname, '..', 'tests');
const tests = [];

function write(group, name, builderFn, note) {
  const B = new ExportBuilder();
  builderFn(B);
  const dir = path.join(ROOT, group);
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, `${name}.ndjson`), B.emit());
  tests.push({ group, name, note });
}

// --- shared snippets -------------------------------------------------------

// def constType : Type → Type → Type := fun x y => x
function addConstType(B) {
  const Ty = B.S(B.lnat(1));
  return B.def('constType', [],
    B.Arrow(Ty, B.Arrow(Ty, Ty)),
    B.Lam(Ty, (x) => B.Lam(Ty, () => x)));
}

// Church-numeral Peano arithmetic (tutorial's PN development), universe u.
function addPeanoBase(B) {
  const u = B.lparam('u');
  const Su = B.S(u);
  // PN : Sort (imax (u+1) u) := ∀ α : Sort u, (α → α) → (α → α)
  B.def('PN', ['u'],
    B.S(B.limax(B.ls(u), u)),
    B.Pi(Su, (al) => B.Arrow(B.Arrow(al, al), B.Arrow(al, al))));
  const PN = (us) => B.C('PN', us);
  // PN.zero : PN := fun α s z => z
  B.def('PN.zero', ['u'], PN([u]),
    B.Lam(Su, (al) => B.Lam(B.Arrow(al, al), () => B.Lam(al, (z) => z))));
  // PN.succ : PN → PN := fun n α s z => s (n α s z)
  B.def('PN.succ', ['u'], B.Arrow(PN([u]), PN([u])),
    B.Lam(PN([u]), (n) => B.Lam(Su, (al) => B.Lam(B.Arrow(al, al), (s) => B.Lam(al, (z) =>
      B.A(s, B.A(n, al, s, z)))))));
  // lits
  B.def('PN.lit0', ['u'], PN([u]), B.C('PN.zero', [u]));
  B.def('PN.lit1', ['u'], PN([u]), B.A(B.C('PN.succ', [u]), B.C('PN.lit0', [u])));
  B.def('PN.lit2', ['u'], PN([u]), B.A(B.C('PN.succ', [u]), B.C('PN.lit1', [u])));
  B.def('PN.lit3', ['u'], PN([u]), B.A(B.C('PN.succ', [u]), B.C('PN.lit2', [u])));
  B.def('PN.lit4', ['u'], PN([u]), B.A(B.C('PN.succ', [u]), B.C('PN.lit3', [u])));
  // add / mul
  B.def('PN.add', ['u'], B.Arrow(PN([u]), B.Arrow(PN([u]), PN([u]))),
    B.Lam(PN([u]), (n) => B.Lam(PN([u]), (m) => B.Lam(Su, (al) => B.Lam(B.Arrow(al, al), (s) => B.Lam(al, (z) =>
      B.A(n, al, s, B.A(m, al, s, z))))))));
  B.def('PN.mul', ['u'], B.Arrow(PN([u]), B.Arrow(PN([u]), PN([u]))),
    B.Lam(PN([u]), (n) => B.Lam(PN([u]), (m) => B.Lam(Su, (al) => B.Lam(B.Arrow(al, al), (s) => B.Lam(al, (z) =>
      B.A(n, al, B.A(m, al, s), z)))))));
  return { u, PN };
}

// ∀ (t : PN → Prop) (v : ∀ n, t n), t <target>
function peanoThmType(B, u, target) {
  const PNu = B.C('PN', [u]);
  return B.Pi(B.Arrow(PNu, B.S(0)), (t) =>
    B.Arrow(B.Pi(PNu, (n) => B.A(t, n)), B.A(t, target)));
}
function peanoThmVal(B, u, witness) {
  const PNu = B.C('PN', [u]);
  return B.Lam(B.Arrow(PNu, B.S(0)), (t) =>
    B.Lam(B.Pi(PNu, (n) => B.A(t, n)), (v) => B.A(v, witness)));
}

// === GOOD ====================================================================

write('good', '001_basicDef', (B) => {
  B.def('basicDef', [], B.S(B.lnat(1)), B.S(0));
}, 'Basic definition: def basicDef : Type := Prop');

write('good', '003_arrowType', (B) => {
  B.def('arrowType', [], B.S(B.lnat(1)), B.Arrow(B.S(0), B.S(0)));
}, 'Arrow type: def arrowType : Type := Prop → Prop');

write('good', '004_dependentType', (B) => {
  B.def('dependentType', [], B.S(0), B.Pi(B.S(0), (p) => p));
}, 'Dependent type: def dependentType : Prop := ∀ (p : Prop), p');

write('good', '005_constType', (B) => {
  addConstType(B);
}, 'Lambda: def constType : Type → Type → Type := fun x y => x');

write('good', '006_betaReduction', (B) => {
  addConstType(B);
  B.def('betaReduction', [],
    B.A(B.C('constType'), B.S(0), B.Arrow(B.S(0), B.S(0))),
    B.Pi(B.S(0), (p) => p));
}, 'Beta: def betaReduction : constType Prop (Prop → Prop) := ∀ p : Prop, p');

write('good', '007_betaReduction2', (B) => {
  addConstType(B);
  B.def('betaReduction2', [],
    B.Pi(B.S(0), () => B.A(B.C('constType'), B.S(0), B.Arrow(B.S(0), B.S(0)))),
    B.Lam(B.S(0), (p) => p));
}, 'Beta under binder');

write('good', '008_forallSortWhnf', (B) => {
  const u = B.lparam('u');
  B.def("id'", ['u'],
    B.Pi(B.S(u), (al) => B.Arrow(al, al)),
    B.Lam(B.S(u), (al) => B.Lam(al, (a) => a)));
  // forallSortWhnf : Prop := ∀ (p : id' Type Prop) (x : p), p
  const idTypeProp = B.A(B.C("id'", [B.lnat(2)]), B.S(B.lnat(1)), B.S(0));
  B.def('forallSortWhnf', [], B.S(0),
    B.Pi(idTypeProp, (p) => B.Pi(p, () => p)));
}, 'Binder domain needs whnf before becoming a sort');

write('good', '012_levelComp1', (B) => {
  B.def('levelComp1', [], B.S(B.lnat(1)), B.S(B.limax(B.lnat(1), B.lnat(0))), 'opaque');
}, 'Sort (imax 1 0) : Sort 1');

write('good', '013_levelComp2', (B) => {
  B.def('levelComp2', [], B.S(B.lnat(2)), B.S(B.limax(B.lnat(0), B.lnat(1))), 'opaque');
}, 'Sort (imax 0 1) : Sort 2');

write('good', '014_levelComp3', (B) => {
  B.def('levelComp3', [], B.S(B.lnat(3)), B.S(B.limax(B.lnat(2), B.lnat(1))), 'opaque');
}, 'Sort (imax 2 1) : Sort 3');

write('good', '015_levelParams', (B) => {
  const u = B.lparam('u');
  B.def('levelParamF', ['u'],
    B.Arrow(B.S(u), B.Arrow(B.S(u), B.S(u))),
    B.Lam(B.S(u), (a) => B.Lam(B.S(u), () => a)));
  B.def('levelParams', [],
    B.A(B.C('levelParamF', [B.lnat(1)]), B.S(0), B.Arrow(B.S(0), B.S(0))),
    B.Pi(B.S(0), (p) => p));
}, 'Universe-polymorphic function applied at level 1');

write('good', '017_levelComp4', (B) => {
  const u = B.lparam('u');
  B.def('levelComp4', ['u'], B.S(B.lnat(1)), B.S(B.limax(u, B.lnat(0))), 'opaque');
}, 'Sort (imax u 0) : Type 0');

write('good', '018_levelComp5', (B) => {
  const u = B.lparam('u');
  B.def('levelComp5', ['u'], B.S(B.ls(u)), B.S(B.limax(u, u)), 'opaque');
}, 'Sort (imax u u) : Type u');

write('good', '019_imax1', (B) => {
  B.def('imax1', [],
    B.Pi(B.S(0), () => B.S(0)),
    B.Lam(B.S(0), (p) => B.Arrow(B.S(B.lnat(1)), p)));
}, 'imax in forall inference: fun p => (Type → p) : Prop → Prop');

write('good', '020_imax2', (B) => {
  B.def('imax2', [],
    B.Pi(B.S(B.lnat(1)), () => B.S(B.lnat(2))),
    B.Lam(B.S(B.lnat(1)), (al) => B.Arrow(B.S(B.lnat(1)), al)));
}, 'imax in forall inference: fun α => (Type → α) : Type → Type 1');

write('good', '021_inferVar', (B) => {
  B.def('inferVar', [],
    B.Pi(B.S(0), (f) => B.Arrow(f, f)),
    B.Lam(B.S(0), (f) => B.Lam(f, (g) => g)));
}, 'Type inference of local variables');

write('good', '022_defEqLambda', (B) => {
  const PP = B.Arrow(B.S(0), B.S(0));
  const inner = B.Lam(B.S(0), (p) => B.Arrow(p, p));
  B.def('defEqLambda', [],
    B.Pi(B.Arrow(PP, B.S(0)), (f) =>
      B.Arrow(B.Pi(PP, (a) => B.A(f, a)), B.A(f, inner))),
    B.Lam(B.Arrow(PP, B.S(0)), (f) =>
      B.Lam(B.Pi(PP, (a) => B.A(f, a)), (g) => B.A(g, inner))));
}, 'Definitional equality between lambdas');

write('good', '023_peano1', (B) => {
  const { u } = addPeanoBase(B);
  B.thm('peano1', ['u'],
    peanoThmType(B, u, B.C('PN.lit2', [u])),
    peanoThmVal(B, u, B.C('PN.lit2', [u])));
}, 'Peano: 2 = 2');

write('good', '024_peano2', (B) => {
  const { u } = addPeanoBase(B);
  B.thm('peano2', ['u'],
    peanoThmType(B, u, B.C('PN.lit2', [u])),
    peanoThmVal(B, u, B.A(B.C('PN.add', [u]), B.C('PN.lit1', [u]), B.C('PN.lit1', [u]))));
}, 'Peano: 1 + 1 = 2 (δβ-normalization of Church numerals)');

write('good', '025_peano3', (B) => {
  const { u } = addPeanoBase(B);
  B.thm('peano3', ['u'],
    peanoThmType(B, u, B.C('PN.lit4', [u])),
    peanoThmVal(B, u, B.A(B.C('PN.mul', [u]), B.C('PN.lit2', [u]), B.C('PN.lit2', [u]))));
}, 'Peano: 2 * 2 = 4 (δβ-normalization of Church numerals)');

write('good', '026_letType', (B) => {
  B.def('letType', [], B.S(B.lnat(1)),
    B.Let(B.S(B.lnat(1)), B.S(0), (x) => x), 'opaque');
}, 'Non-dependent let');

write('good', '027_letTypeDep', (B) => {
  B.axiom('aDepProp', [], B.Arrow(B.S(B.lnat(1)), B.S(0)));
  B.axiom('mkADepProp', [], B.Pi(B.S(B.lnat(1)), (t) => B.A(B.C('aDepProp'), t)));
  B.def('letTypeDep', [],
    B.A(B.C('aDepProp'), B.S(0)),
    B.Let(B.S(B.lnat(1)), B.S(0), (x) => B.A(B.C('mkADepProp'), x)), 'opaque');
}, 'Dependent let');

write('good', '028_letRed', (B) => {
  B.axiom('aProp', [], B.S(0));
  B.def('letRed', [],
    B.Let(B.S(B.lnat(1)), B.S(0), (x) => x),
    B.C('aProp'), 'opaque');
}, 'Reducing a let (zeta) in the declared type');

write('good', '029_axioms', (B) => {
  B.axiom('aType', [], B.S(B.lnat(1)));
  B.axiom('aProp', [], B.S(0));
  B.axiom('aDepProp', [], B.Arrow(B.S(B.lnat(1)), B.S(0)));
  B.axiom('mkADepProp', [], B.Pi(B.S(B.lnat(1)), (t) => B.A(B.C('aDepProp'), t)));
}, 'Plain axioms');

write('good', '030_proofIrrel', (B) => {
  // axiom p : Prop ; axioms h1 h2 : p ; theorem irrel : ∀ (q : p → Prop), q h1 → q h2
  B.axiom('p', [], B.S(0));
  B.axiom('h1', [], B.C('p'));
  B.axiom('h2', [], B.C('p'));
  B.thm('irrel', [],
    B.Pi(B.Arrow(B.C('p'), B.S(0)), (q) => B.Arrow(B.A(q, B.C('h1')), B.A(q, B.C('h2')))),
    B.Lam(B.Arrow(B.C('p'), B.S(0)), (q) => B.Lam(B.A(q, B.C('h1')), (x) => x)));
}, 'Proof irrelevance: q h1 and q h2 are defeq');

write('good', '031_funEta', (B) => {
  // axiom f : Prop → Prop ; def g : Prop → Prop := fun x => f x
  // theorem eta : ∀ (q : (Prop → Prop) → Prop), q (fun x => f x) → q f
  B.axiom('f', [], B.Arrow(B.S(0), B.S(0)));
  const PP = B.Arrow(B.S(0), B.S(0));
  B.thm('funEta', [],
    B.Pi(B.Arrow(PP, B.S(0)), (q) =>
      B.Arrow(B.A(q, B.Lam(B.S(0), (x) => B.A(B.C('f'), x))), B.A(q, B.C('f')))),
    B.Lam(B.Arrow(PP, B.S(0)), (q) =>
      B.Lam(B.A(q, B.Lam(B.S(0), (x) => B.A(B.C('f'), x))), (h) => h)));
}, 'Function eta: (fun x => f x) ≡ f');

// === BAD =====================================================================

write('bad', '002_badDef', (B) => {
  B.def('badDef', [], B.S(0), B.S(B.lnat(1)));
}, 'Mismatched types: def badDef : Prop := Type');

write('bad', '009_forallSortBad', (B) => {
  const u = B.lparam('u');
  B.def("id'", ['u'],
    B.Pi(B.S(u), (al) => B.Arrow(al, al)),
    B.Lam(B.S(u), (al) => B.Lam(al, (a) => a)));
  const idTypeProp = B.A(B.C("id'", [B.lnat(2)]), B.S(B.lnat(1)), B.S(0));
  // ∀ (p : id' Type Prop) (x : p) (y : x), p   — binding domain `x` is a proof
  B.def('forallSortBad', [], B.S(0),
    B.Pi(idTypeProp, (p) => B.Pi(p, (x) => B.Pi(x, () => p))), 'opaque');
}, 'Binder domain must be a sort (proof used as a type)');

write('bad', '010_nonTypeType', (B) => {
  addConstType(B);
  B.def('nonTypeType', [], B.C('constType'), B.S(0), 'opaque');
}, "Declaration's type must be a type, not a function");

write('bad', '011_nonPropThm', (B) => {
  B.thm('nonPropThm', [], B.S(0), B.Pi(B.S(0), (p) => p));
}, 'Theorem type must be a Prop (Sort 0 itself is not)');

write('bad', '016_dupLevelParams', (B) => {
  B.def('tut06_bad01', ['u', 'u'], B.S(B.lnat(1)), B.S(0), 'opaque');
}, 'Duplicate universe parameters');

write('bad', '033_wrongPeano', (B) => {
  const { u } = addPeanoBase(B);
  B.thm('peanoWrong', ['u'],
    peanoThmType(B, u, B.C('PN.lit3', [u])),
    peanoThmVal(B, u, B.C('PN.lit2', [u])));
}, 'Claim about 3 proved with witness for 2 must fail');

write('bad', '034_dupDefs', (B) => {
  const n1 = B.nameRaw(0, 'dup_defs');
  const n2 = B.nameRaw(0, 'dup_defs'); // distinct index, same rendered name
  B.def(n1, [], B.S(B.lnat(1)), B.S(0));
  B.def(n2, [], B.S(B.lnat(1)), B.S(0));
}, 'Two declarations with the same (re-interned) name');

write('bad', '035_unknownConst', (B) => {
  B.def('usesGhost', [], B.S(B.lnat(1)), B.C('ghost'));
}, 'Reference to an undeclared constant');

write('bad', '036_bvarOutOfRange', (B) => {
  B.def('escape', [], B.S(B.lnat(1)), (cx) => B.eBVar(0));
}, 'Loose bound variable');

write('bad', '037_undeclaredParam', (B) => {
  const u = B.lparam('u');
  B.def('noParams', [], B.S(B.ls(u)), B.S(u));
}, 'Universe parameter used but not declared');

write('bad', '038_constLevelMismatch', (B) => {
  addConstType(B); // 0 level params
  B.def('badLevels', [], B.S(B.lnat(1)), B.A(B.C('constType', [B.lnat(1)]), B.S(0), B.S(0)));
}, 'Constant applied to wrong number of universe levels');

write('bad', '039_axiomCollision', (B) => {
  B.axiom('a', [], B.S(0));
  B.axiom('a', [], B.S(0));
}, 'Axiom name collision');

write('bad', '042_proofIrrelBad', (B) => {
  // Proof irrelevance must be limited to Prop: elements of a Type are not defeq.
  B.axiom('T', [], B.S(B.lnat(1)));
  B.axiom('t1', [], B.C('T'));
  B.axiom('t2', [], B.C('T'));
  B.thm('irrelBad', [],
    B.Pi(B.Arrow(B.C('T'), B.S(0)), (q) => B.Arrow(B.A(q, B.C('t1')), B.A(q, B.C('t2')))),
    B.Lam(B.Arrow(B.C('T'), B.S(0)), (q) => B.Lam(B.A(q, B.C('t1')), (x) => x)));
}, 'Proof irrelevance must not apply at Type');

write('bad', '043_funEtaBad', (B) => {
  // Eta must not identify functions with different bodies.
  B.axiom('f', [], B.Arrow(B.S(0), B.S(0)));
  B.axiom('g', [], B.Arrow(B.S(0), B.S(0)));
  const PP = B.Arrow(B.S(0), B.S(0));
  B.thm('funEtaBad', [],
    B.Pi(B.Arrow(PP, B.S(0)), (q) =>
      B.Arrow(B.A(q, B.Lam(B.S(0), (x) => B.A(B.C('f'), B.A(B.C('g'), x)))), B.A(q, B.C('f')))),
    B.Lam(B.Arrow(PP, B.S(0)), (q) =>
      B.Lam(B.A(q, B.Lam(B.S(0), (x) => B.A(B.C('f'), B.A(B.C('g'), x)))), (h) => h)));
}, 'Eta must not equate fun x => f (g x) with f');

write('bad', '044_wrongPeanoMul', (B) => {
  const { u } = addPeanoBase(B);
  // claim 2*2 = 3
  B.thm('peanoWrongMul', ['u'],
    peanoThmType(B, u, B.C('PN.lit3', [u])),
    peanoThmVal(B, u, B.A(B.C('PN.mul', [u]), B.C('PN.lit2', [u]), B.C('PN.lit2', [u]))));
}, '2*2 = 3 must fail after full normalization');

// === INDUCTIVE FAMILY (shared snippets) =====================================

function addBool(B, name = 'Bool') {
  const u = B.lparam('u_1');
  const Bl = B.C(name);
  B.inductive({
    types: [{ name, levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: [`${name}.false`, `${name}.true`] }],
    ctors: [
      { name: `${name}.false`, levelParams: [], type: Bl, induct: name, cidx: 0, numParams: 0, numFields: 0 },
      { name: `${name}.true`, levelParams: [], type: Bl, induct: name, cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: `${name}.rec`, levelParams: ['u_1'],
      type: B.Pi(B.Arrow(Bl, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C(`${name}.false`)), () =>
          B.Pi(B.A(mo, B.C(`${name}.true`)), () =>
            B.Pi(Bl, (b) => B.A(mo, b))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: `${name}.false`, nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C(`${name}.false`)), (f) => B.Lam(B.A(mo, B.C(`${name}.true`)), () => f))) },
        { ctor: `${name}.true`, nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C(`${name}.false`)), () => B.Lam(B.A(mo, B.C(`${name}.true`)), (t) => t))) },
      ],
      k: false,
    }],
  });
}

// Nat-shaped inductive (zero / succ) with the standard recursor.
function addNatLike(B, name) {
  const u = B.lparam('u_1');
  const N = B.C(name);
  const recC = B.C(`${name}.rec`, [u]);
  const motiveTy = B.Arrow(N, B.S(u));
  const succCaseTy = (mo) => B.Pi(N, (n) => B.Arrow(B.A(mo, n), B.A(mo, B.A(B.C(`${name}.succ`), n))));
  B.inductive({
    types: [{ name, levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: [`${name}.zero`, `${name}.succ`], isRec: true }],
    ctors: [
      { name: `${name}.zero`, levelParams: [], type: N, induct: name, cidx: 0, numParams: 0, numFields: 0 },
      { name: `${name}.succ`, levelParams: [], type: B.Arrow(N, N), induct: name, cidx: 1, numParams: 0, numFields: 1 },
    ],
    recs: [{
      name: `${name}.rec`, levelParams: ['u_1'],
      type: B.Pi(motiveTy, (mo) =>
        B.Pi(B.A(mo, B.C(`${name}.zero`)), () =>
          B.Pi(succCaseTy(mo), () =>
            B.Pi(N, (t) => B.A(mo, t))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        {
          ctor: `${name}.zero`, nfields: 0,
          rhs: B.Lam(motiveTy, (mo) => B.Lam(B.A(mo, B.C(`${name}.zero`)), (z) => B.Lam(succCaseTy(mo), () => z))),
        },
        {
          ctor: `${name}.succ`, nfields: 1,
          rhs: B.Lam(motiveTy, (mo) => B.Lam(B.A(mo, B.C(`${name}.zero`)), (z) => B.Lam(succCaseTy(mo), (s) =>
            B.Lam(N, (n) => B.A(s, n, B.A(recC, mo, z, s, n)))))),
        },
      ],
      k: false,
    }],
  });
}

// Eq with params {α, a}, one index, K-enabled recursor (mirrors lean4export).
function addEq(B) {
  const v = B.lparam('v');
  const u = B.lparam('u_1');
  const Sv = B.S(v);
  B.inductive({
    types: [{
      name: 'Eq', levelParams: ['v'],
      type: B.Pi(Sv, (al) => B.Arrow(al, B.Arrow(al, B.S(0)))),
      numParams: 2, numIndices: 1, ctors: ['Eq.refl'],
    }],
    ctors: [{
      name: 'Eq.refl', levelParams: ['v'],
      type: B.Pi(Sv, (al) => B.Pi(al, (a) => B.A(B.C('Eq', [v]), al, a, a))),
      induct: 'Eq', cidx: 0, numParams: 2, numFields: 0,
    }],
    recs: [{
      name: 'Eq.rec', levelParams: ['u_1', 'v'],
      type: B.Pi(Sv, (al) => B.Pi(al, (a) =>
        B.Pi(B.Pi(al, (b) => B.Arrow(B.A(B.C('Eq', [v]), al, a, b), B.S(u))), (mo) =>
          B.Pi(B.A(mo, a, B.A(B.C('Eq.refl', [v]), al, a)), () =>
            B.Pi(al, (b) => B.Pi(B.A(B.C('Eq', [v]), al, a, b), (t) => B.A(mo, b, t))))))),
      numParams: 2, numIndices: 1, numMotives: 1, numMinors: 1,
      rules: [{
        ctor: 'Eq.refl', nfields: 0,
        rhs: B.Lam(Sv, (al) => B.Lam(al, (a) =>
          B.Lam(B.Pi(al, (b) => B.Arrow(B.A(B.C('Eq', [v]), al, a, b), B.S(u))), (mo) =>
            B.Lam(B.A(mo, a, B.A(B.C('Eq.refl', [v]), al, a)), (re) => re)))),
      }],
      k: true,
    }],
  });
}

write('good', '045_empty', (B) => {
  const u = B.lparam('u_1');
  B.inductive({
    types: [{ name: 'Empty', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: [] }],
    ctors: [],
    recs: [{
      name: 'Empty.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(B.C('Empty'), B.S(u)), (mo) => B.Pi(B.C('Empty'), (t) => B.A(mo, t))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 0, rules: [], k: false,
    }],
  });
  B.def('emptyElim', ['u_1'],
    B.Pi(B.Arrow(B.C('Empty'), B.S(u)), (mo) => B.Pi(B.C('Empty'), (x) => B.A(mo, x))),
    B.Lam(B.Arrow(B.C('Empty'), B.S(u)), (mo) => B.Lam(B.C('Empty'), (x) => B.A(B.C('Empty.rec', [u]), mo, x))));
}, 'Empty inductive + large-eliminating recursor');

write('good', '046_bool', (B) => {
  addBool(B);
  const Bl = B.C('Bool');
  B.def('myNot', [], B.Arrow(Bl, Bl),
    B.Lam(Bl, (b) => B.A(B.C('Bool.rec', [B.lnat(1)]), B.Lam(Bl, () => Bl), B.C('Bool.true'), B.C('Bool.false'), b)));
  // forces ι: myNot true must reduce to false at the type level
  B.def('iotaForce', [],
    B.Pi(B.Arrow(Bl, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.A(B.C('myNot'), B.C('Bool.true'))), B.A(mo, B.C('Bool.false')))),
    B.Lam(B.Arrow(Bl, B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.A(B.C('myNot'), B.C('Bool.true'))), (x) => x)));
}, 'Bool + recursor + ι-reduction forced through the type');

write('good', '047_natN', (B) => {
  addNatLike(B, 'N');
  const N = B.C('N');
  const one = B.A(B.C('N.succ'), B.C('N.zero'));
  const two = B.A(B.C('N.succ'), one);
  B.def('add', [], B.Arrow(N, B.Arrow(N, N)),
    B.Lam(N, (a) => B.Lam(N, (b) =>
      B.A(B.C('N.rec', [B.lnat(1)]), B.Lam(N, () => N), a,
        B.Lam(N, () => B.Lam(N, (ih) => B.A(B.C('N.succ'), ih))), b))));
  B.def('addForce', [],
    B.Pi(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.A(B.C('add'), one, one)), B.A(mo, two))),
    B.Lam(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.A(B.C('add'), one, one)), (x) => x)));
}, 'Recursive inductive: 1+1 computed by recursor ι-reduction');

write('good', '048_eqRuleK', (B) => {
  addBool(B);
  addEq(B);
  const Bl = B.C('Bool');
  const tru = B.C('Bool.true');
  const EqB = (x, y) => B.A(B.C('Eq', [B.lnat(1)]), Bl, x, y);
  // @Eq.rec Bool true (fun b _ => Bool) a2 true h
  const recApp = (a2, h) =>
    B.A(B.C('Eq.rec', [B.lnat(1), B.lnat(1)]), Bl, tru,
      B.Lam(Bl, () => B.Lam(EqB(tru, (cx) => cx.lastB ?? B.eBVar(0), 0) || B.S(0), () => Bl)), a2, tru, h);
  // NOTE: motive's second binder type is Eq Bool true b — build with HOAS below
  B.thm('ruleK', [],
    B.Pi(EqB(tru, tru), (h) => B.Pi(Bl, (a2) =>
      EqB(
        B.A(B.C('Eq.rec', [B.lnat(1), B.lnat(1)]), Bl, tru,
          B.Lam(Bl, (b) => B.Lam(EqB(tru, b), () => Bl)), a2, tru, h),
        a2
      ))),
    B.Lam(EqB(tru, tru), () => B.Lam(Bl, (a2) => B.A(B.C('Eq.refl', [B.lnat(1)]), Bl, a2))));
}, 'K-like reduction for Eq with a stuck major premise');

write('good', '050_struct', (B) => {
  addBool(B);
  const u = B.lparam('u_1');
  const Bl = B.C('Bool');
  const P = B.C('P');
  B.inductive({
    types: [{ name: 'P', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['P.mk'] }],
    ctors: [{ name: 'P.mk', levelParams: [], type: B.Arrow(Bl, B.Arrow(Bl, P)), induct: 'P', cidx: 0, numParams: 0, numFields: 2 }],
    recs: [{
      name: 'P.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(P, B.S(u)), (mo) =>
        B.Pi(B.Pi(Bl, (x) => B.Pi(Bl, (y) => B.A(mo, B.A(B.C('P.mk'), x, y)))), () =>
          B.Pi(P, (t) => B.A(mo, t)))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 1,
      rules: [{
        ctor: 'P.mk', nfields: 2,
        rhs: B.Lam(B.Arrow(P, B.S(u)), (mo) =>
          B.Lam(B.Pi(Bl, (x) => B.Pi(Bl, (y) => B.A(mo, B.A(B.C('P.mk'), x, y)))), (mk) =>
            B.Lam(Bl, (x) => B.Lam(Bl, (y) => B.A(mk, x, y))))),
      }],
      k: false,
    }],
  });
  B.def('pFst', [], B.Arrow(P, Bl), B.Lam(P, (p) => B.PROJ('P', 0, p)));
  B.def('projForce', [],
    B.Pi(B.Arrow(Bl, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.PROJ('P', 1, B.A(B.C('P.mk'), B.C('Bool.true'), B.C('Bool.false')))), B.A(mo, B.C('Bool.false')))),
    B.Lam(B.Pi(Bl, () => B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.PROJ('P', 1, B.A(B.C('P.mk'), B.C('Bool.true'), B.C('Bool.false')))), (x) => x)));
  B.def('etaForce', [],
    B.Pi(P, (p) => B.Pi(B.Arrow(P, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.A(B.C('P.mk'), B.PROJ('P', 0, p), B.PROJ('P', 1, p))), B.A(mo, p)))),
    B.Lam(P, (p) => B.Lam(B.Arrow(P, B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.A(B.C('P.mk'), B.PROJ('P', 0, p), B.PROJ('P', 1, p))), (x) => x))));
}, 'Structure: projection typing, projection ι, structure eta');

write('good', '051_natLit', (B) => {
  addNatLike(B, 'Nat');
  const N = B.C('Nat');
  B.def('aNatLit', [], N, B.NAT('0'));
  B.def('litForce', [],
    B.Pi(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.NAT('2')), B.A(mo, B.A(B.C('Nat.succ'), B.A(B.C('Nat.succ'), B.C('Nat.zero')))))),
    B.Lam(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.NAT('2')), (x) => x)));
  B.def('pred', [], B.Arrow(N, N),
    B.Lam(N, (n) => B.A(B.C('Nat.rec', [B.lnat(1)]), B.Lam(N, () => N), B.C('Nat.zero'),
      B.Lam(N, (k) => B.Lam(N, () => k)), n)));
  B.def('predForce', [],
    B.Pi(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, B.A(B.C('pred'), B.NAT('2'))), B.A(mo, B.NAT('1')))),
    B.Lam(B.Arrow(N, B.S(B.lnat(1))), (mo) =>
      B.Lam(B.A(mo, B.A(B.C('pred'), B.NAT('2'))), (x) => x)));
}, 'Nat literals: typing, literal↔constructor conversion, ι on a literal');

write('good', '052_unit', (B) => {
  const u = B.lparam('u_1');
  const U = B.C('U');
  B.inductive({
    types: [{ name: 'U', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['U.unit'] }],
    ctors: [{ name: 'U.unit', levelParams: [], type: U, induct: 'U', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [{
      name: 'U.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(U, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('U.unit')), () => B.Pi(U, (t) => B.A(mo, t)))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 1,
      rules: [{
        ctor: 'U.unit', nfields: 0,
        rhs: B.Lam(B.Arrow(U, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('U.unit')), (h) => h)),
      }],
      k: false,
    }],
  });
  B.def('unitEta', [],
    B.Pi(U, (u1) => B.Pi(U, (u2) => B.Pi(B.Arrow(U, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, u1), B.A(mo, u2))))),
    B.Lam(U, () => B.Lam(U, () => B.Lam(B.Arrow(U, B.S(B.lnat(1))), (mo) =>
      B.Lam((cx) => B.eApp(mo(cx), B.eBVar(2)), (x) => x)))));
}, 'Unit-like eta: any two elements of a unit type are defeq');

write('good', '053_quot', (B) => {
  addBool(B);
  addEq(B);
  const v = B.lparam('v');
  const w = B.lparam('w');
  const Sv = B.S(v);
  const Bl = B.C('Bool');
  const EqB = B.A(B.C('Eq', [B.lnat(1)]), Bl); // Eq Bool : Bool → Bool → Prop (partially applied)
  // Quot primitives
  B.quot('Quot', ['v'],
    B.Pi(Sv, (al) => B.Arrow(B.Arrow(al, B.Arrow(al, B.S(0))), Sv)), 'type');
  B.quot('Quot.mk', ['v'],
    B.Pi(Sv, (al) => B.Pi(B.Arrow(al, B.Arrow(al, B.S(0))), (r) =>
      B.Arrow(al, B.A(B.C('Quot', [v]), al, r)))), 'ctor');
  B.quot('Quot.lift', ['v', 'w'],
    B.Pi(Sv, (al) => B.Pi(B.Arrow(al, B.Arrow(al, B.S(0))), (r) =>
      B.Pi(B.S(w), (be) =>
        B.Pi(B.Arrow(al, be), (f) =>
          B.Arrow(
            B.Pi(al, (a) => B.Pi(al, (b) => B.Arrow(B.A(r, a, b), B.A(B.C('Eq', [w]), be, B.A(f, a), B.A(f, b))))),
            B.Arrow(B.A(B.C('Quot', [v]), al, r), be)))))), 'lift');
  B.quot('Quot.ind', ['v'],
    B.Pi(Sv, (al) => B.Pi(B.Arrow(al, B.Arrow(al, B.S(0))), (r) =>
      B.Pi(B.Arrow(B.A(B.C('Quot', [v]), al, r), B.S(0)), (be) =>
        B.Arrow(
          B.Pi(al, (a) => B.A(be, B.A(B.C('Quot.mk', [v]), al, r, a))),
          B.Pi(B.A(B.C('Quot', [v]), al, r), (q) => B.A(be, q)))))), 'ind');
  // f := id on Bool; h : ∀ a b, Eq Bool a b → Eq Bool (f a) (f b)
  B.def('idB', [], B.Arrow(Bl, Bl), B.Lam(Bl, (b) => b));
  B.def('hResp', [],
    B.Pi(Bl, (a) => B.Pi(Bl, (b) =>
      B.Arrow(B.A(EqB, a, b), B.A(B.C('Eq', [B.lnat(1)]), Bl, B.A(B.C('idB'), a), B.A(B.C('idB'), b))))),
    B.Lam(Bl, () => B.Lam(Bl, () => B.Lam((cx) => {
      // Eq Bool a b at current depth: a = bvar1, b = bvar0
      const eq = B.eConst('Eq', [B.lnat(1)]);
      return B.eApp(B.eApp(B.eApp(eq, B.eConst('Bool')), B.eBVar(1)), B.eBVar(0));
    }, (hh) => hh))));
  // Quot.lift idB hResp (Quot.mk EqBool true) ≡ idB true ≡ true
  const liftApp = B.A(B.C('Quot.lift', [B.lnat(1), B.lnat(1)]), Bl, EqB, Bl, B.C('idB'), B.C('hResp'),
    B.A(B.C('Quot.mk', [B.lnat(1)]), Bl, EqB, B.C('Bool.true')));
  B.def('quotForce', [],
    B.Pi(B.Arrow(Bl, B.S(B.lnat(1))), (mo) =>
      B.Arrow(B.A(mo, liftApp), B.A(mo, B.C('Bool.true')))),
    B.Lam(B.Arrow(Bl, B.S(B.lnat(1))), (mo) => B.Lam(B.A(mo, liftApp), (x) => x)));
}, 'Quotients: registration + Quot.lift ι-reduction');

write('bad', '071_quotBadSignature', (B) => {
  const v = B.lparam('v');
  const Sv = B.S(v);
  B.quot('Quot', ['v'],
    B.Pi(Sv, (al) => B.Arrow(B.Arrow(al, B.Arrow(al, B.S(0))), Sv)), 'type');
  B.quot('Quot.ind', ['v'], B.S(0), 'ind');
}, 'Quot primitive declarations must have canonical signatures');

write('bad', '072_quotBadTypeShape', (B) => {
  const v = B.lparam('v');
  const Sv = B.S(v);
  B.quot('Quot', ['v'], B.Pi(Sv, () => B.Arrow(Sv, Sv)), 'type');
}, 'Quot type primitive must quantify a Prop-valued relation');

write('bad', '073_quotBadMkArg', (B) => {
  const v = B.lparam('v');
  const Sv = B.S(v);
  B.quot('Quot', ['v'],
    B.Pi(Sv, (al) => B.Arrow(B.Arrow(al, B.Arrow(al, B.S(0))), Sv)), 'type');
  B.quot('Quot.mk', ['v'],
    B.Pi(Sv, (al) => B.Pi(B.Arrow(al, B.Arrow(al, B.S(0))), (r) =>
      B.Arrow(Sv, B.A(B.C('Quot', [v]), al, r)))), 'ctor');
}, 'Quot.mk element argument must have type α');

// === BAD: inductive declarations ============================================

write('bad', '054_indNonSort', (B) => {
  B.axiom('A', [], B.S(B.lnat(1)));
  B.inductive({
    types: [{ name: 'J', levelParams: [], type: B.C('A'), numParams: 0, numIndices: 0, ctors: [] }],
    ctors: [], recs: [],
  });
}, 'Inductive type must be a sort');

write('bad', '055_indDupLp', (B) => {
  B.inductive({
    types: [{ name: 'J', levelParams: ['u', 'u'], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: [] }],
    ctors: [], recs: [],
  });
}, 'Inductive with duplicate universe params');

write('bad', '056_indTooFewParams', (B) => {
  B.inductive({
    types: [{ name: 'J', levelParams: [], type: B.Arrow(B.S(0), B.S(B.lnat(1))), numParams: 2, numIndices: 0, ctors: [] }],
    ctors: [], recs: [],
  });
}, 'Inductive with too few parameters in its type');

write('bad', '057_ctorSwappedParams', (B) => {
  B.inductive({
    types: [{ name: 'W', levelParams: [], type: B.Arrow(B.S(0), B.Arrow(B.S(0), B.S(B.lnat(1)))), numParams: 2, numIndices: 0, ctors: ['W.mk'] }],
    ctors: [{
      name: 'W.mk', levelParams: [],
      type: B.Pi(B.S(0), (x) => B.Pi(B.S(0), (y) => B.A(B.C('W'), y, x))),
      induct: 'W', cidx: 0, numParams: 2, numFields: 0,
    }],
    recs: [],
  });
}, 'Constructor result must apply the inductive to its params in order');

write('bad', '058_ctorSwappedLevels', (B) => {
  const u1 = B.lparam('u1');
  const u2 = B.lparam('u2');
  B.inductive({
    types: [{ name: 'V', levelParams: ['u1', 'u2'], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['V.mk'] }],
    ctors: [{
      name: 'V.mk', levelParams: ['u1', 'u2'],
      type: B.C('V', [u2, u1]),
      induct: 'V', cidx: 0, numParams: 0, numFields: 0,
    }],
    recs: [],
  });
}, 'Constructor result universe params must match in order');

write('bad', '059_indNegative', (B) => {
  B.inductive({
    types: [{ name: 'G', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['G.mk'] }],
    ctors: [{
      name: 'G.mk', levelParams: [],
      type: B.Arrow(B.Arrow(B.C('G'), B.C('G')), B.C('G')),
      induct: 'G', cidx: 0, numParams: 0, numFields: 1,
    }],
    recs: [],
  });
}, 'Negative recursive occurrence');

write('bad', '060_indInIndex', (B) => {
  B.axiom('aP', [], B.S(0));
  B.inductive({
    types: [{ name: 'X', levelParams: [], type: B.Arrow(B.S(0), B.S(0)), numParams: 0, numIndices: 1, ctors: ['X.mk'] }],
    ctors: [{
      name: 'X.mk', levelParams: [],
      type: B.A(B.C('X'), B.A(B.C('X'), B.C('aP'))),
      induct: 'X', cidx: 0, numParams: 0, numFields: 0,
    }],
    recs: [],
  });
}, 'Recursive occurrence in index position');

write('bad', '061_ctorBadResult', (B) => {
  B.axiom('aType', [], B.S(B.lnat(1)));
  B.inductive({
    types: [{ name: 'K1', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['K1.mk'] }],
    ctors: [{ name: 'K1.mk', levelParams: [], type: B.C('aType'), induct: 'K1', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
}, "Constructor result must target its inductive");

write('bad', '062_fieldTooLarge', (B) => {
  B.inductive({
    types: [{ name: 'T0', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['T0.mk'] }],
    ctors: [{
      name: 'T0.mk', levelParams: [],
      type: B.Arrow(B.S(B.lnat(1)), B.C('T0')),
      induct: 'T0', cidx: 0, numParams: 0, numFields: 1,
    }],
    recs: [],
  });
}, 'Field universe exceeds the inductive universe');

write('bad', '063_projOutOfRange', (B) => {
  addBool(B);
  const Bl = B.C('Bool');
  const P = B.C('P2');
  B.inductive({
    types: [{ name: 'P2', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['P2.mk'] }],
    ctors: [{ name: 'P2.mk', levelParams: [], type: B.Arrow(Bl, B.Arrow(Bl, P)), induct: 'P2', cidx: 0, numParams: 0, numFields: 2 }],
    recs: [],
  });
  B.def('bad', [], Bl, B.PROJ('P2', 5, B.A(B.C('P2.mk'), B.C('Bool.true'), B.C('Bool.false'))));
}, 'Out-of-range projection');

write('bad', '064_projNotStruct', (B) => {
  addNatLike(B, 'N2');
  B.def('bad', [], B.C('N2'), B.PROJ('N2', 0, B.C('N2.zero')));
}, 'Projection out of a non-structure');

write('bad', '065_recWrongRule', (B) => {
  const u = B.lparam('u_1');
  const Bl = B.C('B2');
  B.inductive({
    types: [{ name: 'B2', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['B2.false', 'B2.true'] }],
    ctors: [
      { name: 'B2.false', levelParams: [], type: Bl, induct: 'B2', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'B2.true', levelParams: [], type: Bl, induct: 'B2', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: 'B2.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(Bl, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('B2.false')), () =>
          B.Pi(B.A(mo, B.C('B2.true')), () =>
            B.Pi(Bl, (b) => B.A(mo, b))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: 'B2.false', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('B2.false')), (f) => B.Lam(B.A(mo, B.C('B2.true')), () => f))) },
        // WRONG: the true-rule also returns the false case
        { ctor: 'B2.true', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('B2.false')), (f) => B.Lam(B.A(mo, B.C('B2.true')), () => f))) },
      ],
      k: false,
    }],
  });
}, 'Recursor rule with the wrong type must be rejected (nat-rec-rules class)');

write('bad', '070_recBadResult', (B) => {
  const u = B.lparam('u_1');
  const Bl = B.C('B4');
  B.axiom('False', [], B.S(0));
  B.inductive({
    types: [{ name: 'B4', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['B4.false', 'B4.true'] }],
    ctors: [
      { name: 'B4.false', levelParams: [], type: Bl, induct: 'B4', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'B4.true', levelParams: [], type: Bl, induct: 'B4', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: 'B4.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(Bl, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('B4.false')), () =>
          B.Pi(B.A(mo, B.C('B4.true')), () =>
            B.C('False')))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: 'B4.false', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('B4.false')), (f) => B.Lam(B.A(mo, B.C('B4.true')), () => f))) },
        { ctor: 'B4.true', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('B4.false')), () => B.Lam(B.A(mo, B.C('B4.true')), (t) => t))) },
      ],
      k: false,
    }],
  });
}, 'Recursor declaration must end in motive applied to indices and major');

write('bad', '074_recSwappedMinors', (B) => {
  const u = B.lparam('u_1');
  const Bl = B.C('Bswap');
  B.inductive({
    types: [{ name: 'Bswap', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['Bswap.false', 'Bswap.true'] }],
    ctors: [
      { name: 'Bswap.false', levelParams: [], type: Bl, induct: 'Bswap', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'Bswap.true', levelParams: [], type: Bl, induct: 'Bswap', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: 'Bswap.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(Bl, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('Bswap.true')), () =>
          B.Pi(B.A(mo, B.C('Bswap.false')), () =>
            B.Pi(Bl, (b) => B.A(mo, b))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: 'Bswap.false', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('Bswap.true')), () => B.Lam(B.A(mo, B.C('Bswap.false')), (f) => f))) },
        { ctor: 'Bswap.true', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('Bswap.true')), (t) => B.Lam(B.A(mo, B.C('Bswap.false')), () => t))) },
      ],
      k: false,
    }],
  });
}, 'Recursor minor premises must match constructor order and result motives');

write('bad', '066_kOnData', (B) => {
  const u = B.lparam('u_1');
  const Bl = B.C('B3');
  B.inductive({
    types: [{ name: 'B3', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['B3.mk'] }],
    ctors: [{ name: 'B3.mk', levelParams: [], type: Bl, induct: 'B3', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [{
      name: 'B3.rec', levelParams: ['u_1'],
      type: B.Pi(B.Arrow(Bl, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('B3.mk')), () => B.Pi(Bl, (b) => B.A(mo, b)))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 1,
      rules: [{ ctor: 'B3.mk', nfields: 0, rhs: B.Lam(B.Arrow(Bl, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('B3.mk')), (h) => h)) }],
      k: true, // INVALID: K on a Type-valued inductive
    }],
  });
}, 'K flag on a non-Prop inductive must be rejected');

write('bad', '067_elimViolation', (B) => {
  const u = B.lparam('u_1');
  const BP = B.C('BP');
  B.inductive({
    types: [{ name: 'BP', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['BP.a', 'BP.b'] }],
    ctors: [
      { name: 'BP.a', levelParams: [], type: BP, induct: 'BP', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'BP.b', levelParams: [], type: BP, induct: 'BP', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: 'BP.rec', levelParams: ['u_1'],
      // motive eliminates into Sort u — illegal for a 2-constructor Prop
      type: B.Pi(B.Arrow(BP, B.S(u)), (mo) =>
        B.Pi(B.A(mo, B.C('BP.a')), () =>
          B.Pi(B.A(mo, B.C('BP.b')), () =>
            B.Pi(BP, (t) => B.A(mo, t))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: 'BP.a', nfields: 0, rhs: B.Lam(B.Arrow(BP, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('BP.a')), (a) => B.Lam(B.A(mo, B.C('BP.b')), () => a))) },
        { ctor: 'BP.b', nfields: 0, rhs: B.Lam(B.Arrow(BP, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('BP.a')), () => B.Lam(B.A(mo, B.C('BP.b')), (b) => b))) },
      ],
      k: false,
    }],
  });
}, 'Large elimination from a 2-constructor Prop must be rejected');

// === DECLINE =================================================================

write('decline', '068_nested', (B) => {
  B.inductive({
    types: [{ name: 'Nst', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: [], numNested: 1 }],
    ctors: [], recs: [],
  });
}, 'Nested inductives are out of fragment → decline');

write('decline', '069_unsafeDef', (B) => {
  const n = B.name('unsafeThing');
  B.decls.push({
    kind: 'def', name: n, levelParams: [], type: B.compile(B.S(B.lnat(1))),
    value: B.compile(B.S(0)), hints: { regular: 1 }, safety: 'partial', all: [n],
  });
}, 'Partial/unsafe definitions are out of fragment → decline');

fs.mkdirSync(ROOT, { recursive: true });
fs.writeFileSync(path.join(ROOT, 'manifest.json'), JSON.stringify(tests, null, 2));
console.log(`generated ${tests.length} test vectors in tests/`);
