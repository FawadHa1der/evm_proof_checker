'use strict';
const { ExportBuilder } = require('./lib');

// ---- shared snippets -------------------------------------------------------
function addBool(B) {
  B.inductive({
    types: [{ name: 'Bool', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['Bool.false', 'Bool.true'] }],
    ctors: [
      { name: 'Bool.false', levelParams: [], type: B.C('Bool'), induct: 'Bool', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'Bool.true', levelParams: [], type: B.C('Bool'), induct: 'Bool', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [],
  });
}
function addFalseTrue(B) {
  B.inductive({ types: [{ name: 'False', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: [] }], ctors: [], recs: [] });
  B.inductive({
    types: [{ name: 'True', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['True.intro'] }],
    ctors: [{ name: 'True.intro', levelParams: [], type: B.C('True'), induct: 'True', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
}
function addEq(B) {
  const v = B.lparam('v'); const u = B.lparam('u_1'); const Sv = B.S(v);
  B.inductive({
    types: [{ name: 'Eq', levelParams: ['v'], type: B.Pi(Sv, (al) => B.Arrow(al, B.Arrow(al, B.S(0)))), numParams: 2, numIndices: 1, ctors: ['Eq.refl'] }],
    ctors: [{ name: 'Eq.refl', levelParams: ['v'], type: B.Pi(Sv, (al) => B.Pi(al, (a) => B.A(B.C('Eq', [v]), al, a, a))), induct: 'Eq', cidx: 0, numParams: 2, numFields: 0 }],
    recs: [{
      name: 'Eq.rec', levelParams: ['u_1', 'v'],
      type: B.Pi(Sv, (al) => B.Pi(al, (a) =>
        B.Pi(B.Pi(al, (b) => B.Arrow(B.A(B.C('Eq', [v]), al, a, b), B.S(u))), (mo) =>
          B.Pi(B.A(mo, a, B.A(B.C('Eq.refl', [v]), al, a)), () =>
            B.Pi(al, (b) => B.Pi(B.A(B.C('Eq', [v]), al, a, b), (t) => B.A(mo, b, t))))))),
      numParams: 2, numIndices: 1, numMotives: 1, numMinors: 1,
      rules: [{ ctor: 'Eq.refl', nfields: 0,
        rhs: B.Lam(Sv, (al) => B.Lam(al, (a) =>
          B.Lam(B.Pi(al, (b) => B.Arrow(B.A(B.C('Eq', [v]), al, a, b), B.S(u))), (mo) =>
            B.Lam(B.A(mo, a, B.A(B.C('Eq.refl', [v]), al, a)), (re) => re)))) }],
      k: true,
    }],
  });
}

const V = {};

// ---- T1 proj-of-imax-prop --------------------------------------------------
V['T1_projImaxProp'] = ['reject', (B) => {
  addBool(B);
  // W : Sort (imax 1 0)  -- normalises to Prop
  B.inductive({
    types: [{ name: 'W', levelParams: [], type: B.S(B.limax(B.lnat(1), 0)), numParams: 0, numIndices: 0, ctors: ['W.mk'] }],
    ctors: [{ name: 'W.mk', levelParams: [], type: B.Arrow(B.C('Bool'), B.C('W')), induct: 'W', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.def('bad', [], B.C('Bool'), B.PROJ('W', 0, B.A(B.C('W.mk'), B.C('Bool.true'))));
}];
// control: same but W : Type -> must accept
V['T1b_projTypeControl'] = ['accept', (B) => {
  addBool(B);
  B.inductive({
    types: [{ name: 'W', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['W.mk'] }],
    ctors: [{ name: 'W.mk', levelParams: [], type: B.Arrow(B.C('Bool'), B.C('W')), induct: 'W', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.def('bad', [], B.C('Bool'), B.PROJ('W', 0, B.A(B.C('W.mk'), B.C('Bool.true'))));
}];
// control: W : Prop written literally as Sort 0, data field -> must reject
V['T1c_projLiteralProp'] = ['reject', (B) => {
  addBool(B);
  B.inductive({
    types: [{ name: 'W', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['W.mk'] }],
    ctors: [{ name: 'W.mk', levelParams: [], type: B.Arrow(B.C('Bool'), B.C('W')), induct: 'W', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.def('bad', [], B.C('Bool'), B.PROJ('W', 0, B.A(B.C('W.mk'), B.C('Bool.true'))));
}];

// ---- T2 proj-of-prop -------------------------------------------------------
V['T2_projOfProp'] = ['reject', (B) => {
  addFalseTrue(B);
  B.inductive({
    types: [{ name: 'Wrapper', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['Wrapper.mk'] }],
    ctors: [{ name: 'Wrapper.mk', levelParams: [], type: B.Arrow(B.C('False'), B.C('Wrapper')), induct: 'Wrapper', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.thm('badFalse', [], B.C('False'), B.PROJ('Wrapper', 0, B.A(B.C('Wrapper.mk'), B.C('True.intro'))));
}];

// ---- T3 proj-non-structure -------------------------------------------------
V['T3_projNonStructure'] = ['reject', (B) => {
  addFalseTrue(B);
  B.inductive({
    types: [{ name: 'Bad', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['Bad.mk1', 'Bad.mk2'] }],
    ctors: [
      { name: 'Bad.mk1', levelParams: [], type: B.Arrow(B.C('False'), B.C('Bad')), induct: 'Bad', cidx: 0, numParams: 0, numFields: 1 },
      { name: 'Bad.mk2', levelParams: [], type: B.Arrow(B.C('True'), B.C('Bad')), induct: 'Bad', cidx: 1, numParams: 0, numFields: 1 },
    ],
    recs: [],
  });
  B.thm('bad', [], B.C('False'), B.PROJ('Bad', 0, B.A(B.C('Bad.mk2'), B.C('True.intro'))));
}];

// ---- T4 ctor-num-fields ----------------------------------------------------
V['T4_ctorNumFields'] = ['reject', (B) => {
  addBool(B);
  B.inductive({
    types: [{ name: 'S', levelParams: [], type: B.S(B.lnat(1)), numParams: 0, numIndices: 0, ctors: ['S.mk'] }],
    ctors: [{ name: 'S.mk', levelParams: [], type: B.Arrow(B.C('Bool'), B.C('S')), induct: 'S', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
}];

// ---- T5 large-elim-prop-bool ----------------------------------------------
function newBoolBlock(B, sortLvl, kFlag) {
  const u = B.lparam('u');
  const NB = B.C('NB');
  B.inductive({
    types: [{ name: 'NB', levelParams: [], type: B.S(sortLvl), numParams: 0, numIndices: 0, ctors: ['NB.tt', 'NB.ff'] }],
    ctors: [
      { name: 'NB.tt', levelParams: [], type: NB, induct: 'NB', cidx: 0, numParams: 0, numFields: 0 },
      { name: 'NB.ff', levelParams: [], type: NB, induct: 'NB', cidx: 1, numParams: 0, numFields: 0 },
    ],
    recs: [{
      name: 'NB.rec', levelParams: ['u'],
      type: B.Pi(B.Arrow(NB, B.S(u)), (mo) =>
        B.Arrow(B.A(mo, B.C('NB.tt')), B.Arrow(B.A(mo, B.C('NB.ff')), B.Pi(NB, (t) => B.A(mo, t))))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 2,
      rules: [
        { ctor: 'NB.tt', nfields: 0, rhs: B.Lam(B.Arrow(NB, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('NB.tt')), (a) => B.Lam(B.A(mo, B.C('NB.ff')), () => a))) },
        { ctor: 'NB.ff', nfields: 0, rhs: B.Lam(B.Arrow(NB, B.S(u)), (mo) => B.Lam(B.A(mo, B.C('NB.tt')), () => B.Lam(B.A(mo, B.C('NB.ff')), (b) => b))) },
      ],
      k: kFlag,
    }],
  });
}
V['T5_largeElimPropBool'] = ['reject', (B) => { newBoolBlock(B, 0, false); }];
V['T5b_largeElimTypeControl'] = ['accept', (B) => { newBoolBlock(B, B.lnat(1), false); }];
// ---- T6 rec-k-lie ----------------------------------------------------------
V['T6_recKLie'] = ['reject', (B) => { newBoolBlock(B, B.lnat(1), true); }];

// ---- T7 proof-irrel (must ACCEPT) -----------------------------------------
V['T7_proofIrrel'] = ['accept', (B) => {
  B.axiom('A', [], B.S(B.lnat(1)));
  B.axiom('a', [], B.C('A'));
  B.axiom('b', [], B.C('A'));
  B.axiom('P', [], B.S(0));
  B.axiom('Q', [], B.Arrow(B.C('P'), B.S(0)));
  const AtoP = B.Arrow(B.C('A'), B.C('P'));
  B.axiom('foo', [], B.Pi(AtoP, (h) => B.A(B.C('Q'), B.A(h, B.C('b')))));
  B.thm('bar', [], B.Pi(AtoP, (h) => B.A(B.C('Q'), B.A(h, B.C('a')))), B.C('foo'));
}];

// ---- T8 k-rec-conv ---------------------------------------------------------
V['T8_kRecConv'] = ['reject', (B) => {
  addBool(B);
  addEq(B);
  const Bl = B.C('Bool');
  const one = B.lnat(1);
  const BB = B.Arrow(Bl, Bl);
  const idB = B.Lam(Bl, (x) => x);
  // T : Type := (y : Bool) → @Eq (Bool→Bool) (fun x => x) (fun _ => y) → Bool
  B.def('T', [], B.S(one),
    B.Pi(Bl, (y) => B.Arrow(B.A(B.C('Eq', [one]), BB, idB, B.Lam(Bl, () => y)), Bl)));
  // t2 : T := fun _ _ => Bool.false
  B.def('t2', [], B.C('T'),
    B.Lam(Bl, (y) => B.Lam(B.A(B.C('Eq', [one]), BB, idB, B.Lam(Bl, () => y)), () => B.C('Bool.false'))));
  // t1 : T := fun y h => @Eq.rec (Bool→Bool) (fun x=>x) (fun _ _ => Bool) Bool.false (fun _ => y) h
  B.def('t1', [], B.C('T'),
    B.Lam(Bl, (y) => B.Lam(B.A(B.C('Eq', [one]), BB, idB, B.Lam(Bl, () => y)), (h) =>
      B.A(B.C('Eq.rec', [one, one]), BB, idB,
        B.Lam(BB, (bb) => B.Lam(B.A(B.C('Eq', [one]), BB, idB, bb), () => Bl)),
        B.C('Bool.false'), B.Lam(Bl, () => y), h))));
  B.thm('bad', [], B.A(B.C('Eq', [one]), B.C('T'), B.C('t1'), B.C('t2')),
    B.A(B.C('Eq.refl', [one]), B.C('T'), B.C('t1')));
}];

// ---- T9 stuck / computed result sort of an inductive -----------------------
// benign: codomain is a plain definition that beta-reduces to Prop
V['T9a_computedPropSort'] = ['accept', (B) => {
  addFalseTrue(B);
  B.def('R', [], B.Arrow(B.C('True'), B.S(B.lnat(1))), B.Lam(B.C('True'), () => B.S(0)));
  B.inductive({
    types: [{ name: 'I', levelParams: [], type: B.Pi(B.C('True'), (h) => B.A(B.C('R'), h)), numParams: 0, numIndices: 1, ctors: ['I.mk'] }],
    ctors: [{ name: 'I.mk', levelParams: [], type: B.A(B.C('I'), B.C('True.intro')), induct: 'I', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
}];
// the proj-of-subst-prop shape: codomain only reduces to a sort via K on the binder
V['T9b_kStuckPropSort'] = ['reject', (B) => {
  addBool(B);
  addFalseTrue(B);
  const u = B.lparam('u');
  // U1 : Prop, single 0-field ctor -> legitimately K-like
  B.inductive({
    types: [{ name: 'U1', levelParams: [], type: B.S(0), numParams: 0, numIndices: 0, ctors: ['U1.mk'] }],
    ctors: [{ name: 'U1.mk', levelParams: [], type: B.C('U1'), induct: 'U1', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [{
      name: 'U1.rec', levelParams: ['u'],
      type: B.Pi(B.Arrow(B.C('U1'), B.S(u)), (mo) => B.Arrow(B.A(mo, B.C('U1.mk')), B.Pi(B.C('U1'), (t) => B.A(mo, t)))),
      numParams: 0, numIndices: 0, numMotives: 1, numMinors: 1,
      rules: [{ ctor: 'U1.mk', nfields: 0, rhs: B.Lam(B.Arrow(B.C('U1'), B.S(u)), (mo) => B.Lam(B.A(mo, B.C('U1.mk')), (a) => a)) }],
      k: true,
    }],
  });
  // gate : U1 → Type 1 := fun h => U1.rec (motive := fun _ => Type 1) Prop h
  B.def('gate', [], B.Arrow(B.C('U1'), B.S(B.lnat(1))),
    B.Lam(B.C('U1'), (h) => B.A(B.C('U1.rec', [B.lnat(2)]), B.Lam(B.C('U1'), () => B.S(B.lnat(1))), B.S(0), h)));
  // Owner : ∀ (h : U1), gate h   -- Lean: reduces to Prop via K; evmlean: ?
  B.inductive({
    types: [{ name: 'Owner', levelParams: [], type: B.Pi(B.C('U1'), (h) => B.A(B.C('gate'), h)), numParams: 0, numIndices: 1, ctors: ['Owner.mk'] }],
    ctors: [{ name: 'Owner.mk', levelParams: [], type: B.Arrow(B.C('Bool'), B.A(B.C('Owner'), B.C('U1.mk'))), induct: 'Owner', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
}];

module.exports = V;

// ---- T9c: computed-but-Prop codomain must still block data projection ------
V['T9c_computedPropProj'] = ['reject', (B) => {
  addBool(B); addFalseTrue(B);
  B.def('R', [], B.Arrow(B.C('True'), B.S(B.lnat(1))), B.Lam(B.C('True'), () => B.S(0)));
  B.inductive({
    types: [{ name: 'I', levelParams: [], type: B.Pi(B.C('True'), (h) => B.A(B.C('R'), h)), numParams: 1, numIndices: 0, ctors: ['I.mk'] }],
    ctors: [{ name: 'I.mk', levelParams: [], type: B.Pi(B.C('True'), (h) => B.Arrow(B.C('Bool'), B.A(B.C('I'), h))), induct: 'I', cidx: 0, numParams: 1, numFields: 1 }],
    recs: [],
  });
  B.def('bad', [], B.C('Bool'), B.PROJ('I', 0, B.A(B.C('I.mk'), B.C('True.intro'), B.C('Bool.true'))));
}];

// ---- T10: proj-maybe-prop (arena outcome: either) --------------------------
V['T10_projMaybeProp'] = ['accept', (B) => {
  const u = B.lparam('u');
  B.inductive({
    types: [{ name: 'PUnit', levelParams: ['u'], type: B.S(u), numParams: 0, numIndices: 0, ctors: ['PUnit.unit'] }],
    ctors: [{ name: 'PUnit.unit', levelParams: ['u'], type: B.C('PUnit', [u]), induct: 'PUnit', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
  B.inductive({
    types: [{ name: 'MaybeProp', levelParams: ['u'], type: B.S(u), numParams: 0, numIndices: 0, ctors: ['MaybeProp.mk'] }],
    ctors: [{ name: 'MaybeProp.mk', levelParams: ['u'], type: B.Arrow(B.C('PUnit', [u]), B.C('MaybeProp', [u])), induct: 'MaybeProp', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.def('projMaybeProp', ['u'], B.Arrow(B.C('MaybeProp', [u]), B.C('PUnit', [u])),
    B.Lam(B.C('MaybeProp', [u]), (s) => B.PROJ('MaybeProp', 0, s)));
}];

// ---- T11: instantiating that same projection at u := 0 (a genuine Prop) ----
V['T11_projMaybePropAtZero'] = ['reject', (B) => {
  const u = B.lparam('u');
  B.inductive({
    types: [{ name: 'PUnit', levelParams: ['u'], type: B.S(u), numParams: 0, numIndices: 0, ctors: ['PUnit.unit'] }],
    ctors: [{ name: 'PUnit.unit', levelParams: ['u'], type: B.C('PUnit', [u]), induct: 'PUnit', cidx: 0, numParams: 0, numFields: 0 }],
    recs: [],
  });
  addBool(B);
  // MaybeProp2.{u} : Sort u with a *Bool* field -- illegal unless u >= 1
  B.inductive({
    types: [{ name: 'MP2', levelParams: ['u'], type: B.S(u), numParams: 0, numIndices: 0, ctors: ['MP2.mk'] }],
    ctors: [{ name: 'MP2.mk', levelParams: ['u'], type: B.Arrow(B.C('Bool'), B.C('MP2', [u])), induct: 'MP2', cidx: 0, numParams: 0, numFields: 1 }],
    recs: [],
  });
  B.def('bad', [], B.C('Bool'), B.PROJ('MP2', 0, B.A(B.C('MP2.mk', [0]), B.C('Bool.true'))));
}];
