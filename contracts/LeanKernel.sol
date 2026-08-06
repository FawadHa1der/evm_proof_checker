// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.28;

/// @title  LeanKernel — a fragment of the Lean 4 kernel on the EVM
/// @notice Checks declarations from the lean4export NDJSON format (v3.1.0),
///         re-encoded into flat word arrays by tools/encode.js (a pure format
///         translation; all *semantic* work happens here, on-chain).
///
/// Supported:   Name hashing, universe levels (full leq with imax case-split),
///              expressions, beta/delta/zeta/iota reduction, definitional
///              equality with function eta, structure/unit eta, proof
///              irrelevance, type inference, declaration checking for
///              axiom/def/theorem/opaque, inductive families/recursors,
///              projections, quotients, and Nat literals.
/// Declined:    unsafe/partial declarations — mirroring the Arena's
///              "decline" verdict (exit code 2) for features a checker
///              does not support.
///
/// Verdicts:    0 = accept, 1 = reject, 2 = decline, 3 = resource error.
contract LeanKernel {
    // ------------------------------------------------------------------
    // Node encodings (one uint256 per node, fields are 48-bit)
    // ------------------------------------------------------------------
    // Names   : tag 0 = str  (a = pre, b = strOff, c = strLen)
    //           tag 1 = num  (a = pre, b = value)
    // Levels  : index 0 is Zero. tag 1 = succ(a), 2 = max(a,b),
    //           3 = imax(a,b), 4 = param(a = nameIdx)
    // Exprs   : tag 0 = bvar(a), 1 = sort(a = level),
    //           2 = const(a = name, b = usStart, c = usLen),
    //           3 = app(a = fn, b = arg), 4 = lam(a = ty, b = body),
    //           5 = pi(a = ty, b = body), 6 = let(a = ty, b = val, c = body),
    //           7 = nat literal, 8 = string literal, 9 = projection,
    //           10 = unsupported
    // Decls   : two words per record, see DECL_* below.

    uint256 internal constant F = (1 << 48) - 1; // 48-bit field mask
    uint256 internal constant NONE = F;

    // expr tags
    uint256 internal constant E_BVAR = 0;
    uint256 internal constant E_SORT = 1;
    uint256 internal constant E_CONST = 2;
    uint256 internal constant E_APP = 3;
    uint256 internal constant E_LAM = 4;
    uint256 internal constant E_PI = 5;
    uint256 internal constant E_LET = 6;
    uint256 internal constant E_NAT = 7; // a = pool ptr: [limbCount, limbs...]
    uint256 internal constant E_STRL = 8; // a = pool ptr: [byteLen, words...]
    uint256 internal constant E_PROJ = 9; // a = typeName, b = idx, c = struct
    uint256 internal constant E_UNSUP = 10;

    // level tags
    uint256 internal constant L_ZERO = 0;
    uint256 internal constant L_SUCC = 1;
    uint256 internal constant L_MAX = 2;
    uint256 internal constant L_IMAX = 3;
    uint256 internal constant L_PARAM = 4;

    // decl kinds
    uint256 internal constant D_AXIOM = 0;
    uint256 internal constant D_DEF = 1;
    uint256 internal constant D_THM = 2;
    uint256 internal constant D_OPAQUE = 3;
    uint256 internal constant D_QUOT = 4; // word1.a = quot kind (0 type, 1 ctor, 2 lift, 3 ind)
    uint256 internal constant D_GROUP = 5; // word1: a=#types b=#ctors c=#recs
    uint256 internal constant D_IND = 6; // word1: a=numParams b=numIndices c=ctorsPtr d=numNested, bit192=isRec
    uint256 internal constant D_CTOR = 7; // word1: a=induct b=cidx c=numParams d=numFields
    uint256 internal constant D_REC = 8; // word1: a=p b=i c=M d=m e=rulesPtr, tagbyte=k
    uint256 internal constant D_UNSUP = 9;

    /// Longest string literal we will expand into cons cells. Lean expands
    /// lazily; we build the whole spine eagerly, so a huge literal would blow
    /// the arena. Declining is honest; a resource error would not be.
    uint256 internal constant STR_EXPAND_MAX = 512;

    // verdicts
    uint8 internal constant V_ACCEPT = 0;
    uint8 internal constant V_REJECT = 1;
    uint8 internal constant V_DECLINE = 2;
    uint8 internal constant V_ERROR = 3;

    // failure reasons (informational)
    uint16 internal constant R_NONE = 0;
    uint16 internal constant R_DUP_NAME = 1;
    uint16 internal constant R_DUP_LPARAM = 2;
    uint16 internal constant R_UNKNOWN_CONST = 3;
    uint16 internal constant R_CONST_LEVELS = 4;
    uint16 internal constant R_UNDECLARED_PARAM = 5;
    uint16 internal constant R_TYPE_NOT_SORT = 6;
    uint16 internal constant R_THM_NOT_PROP = 7;
    uint16 internal constant R_VALUE_MISMATCH = 8;
    uint16 internal constant R_BVAR_RANGE = 9;
    uint16 internal constant R_APP_NOT_PI = 10;
    uint16 internal constant R_APP_ARG = 11;
    uint16 internal constant R_BINDER_NOT_SORT = 12;
    uint16 internal constant R_LET_MISMATCH = 13;
    uint16 internal constant R_UNSUPPORTED = 14;
    uint16 internal constant R_STEPS = 15;
    uint16 internal constant R_DEPTH = 16;
    uint16 internal constant R_IND_SHAPE = 17;
    uint16 internal constant R_CTOR_SHAPE = 18;
    uint16 internal constant R_POSITIVITY = 19;
    uint16 internal constant R_CTOR_RESULT = 20;
    uint16 internal constant R_CTOR_LEVELS = 21;
    uint16 internal constant R_FIELD_UNIVERSE = 22;
    uint16 internal constant R_ELIM_UNIVERSE = 23;
    uint16 internal constant R_K_FLAG = 24;
    uint16 internal constant R_REC_SHAPE = 25;
    uint16 internal constant R_REC_RULE = 26;
    uint16 internal constant R_PROJ = 27;
    uint16 internal constant R_MALFORMED = 29;
    uint16 internal constant R_NESTED = 30;
    uint16 internal constant R_QUOT_SHAPE = 28;

    uint256 internal constant MAX_STEPS = 30_000_000;
    uint256 internal constant MAX_DEPTH = 160;

    /// Cap on auxiliary types from nested-inductive elimination. `numNested`
    /// in real exports is tiny (Lean.Syntax has 2); an absurd declared value
    /// would otherwise size our worklist arrays. Declining is honest.
    uint256 internal constant MAX_NESTED = 256;

    struct M {
        // expression arena (grows: beta/inst/subst create nodes)
        uint256[] ex;
        uint256 exLen;
        // level arena (grows)
        uint256[] lv;
        uint256 lvLen;
        // shared index pool (const universe lists, level-param lists; grows)
        uint256[] pool;
        uint256 poolLen;
        // immutable name table data
        bytes32[] nameHash;
        // environment: parallel arrays of declared constants
        bytes32[] envHash;
        uint256[] envDecl0; // word0 of decl record
        uint256[] envDecl1; // word1 of decl record
        uint256 envLen;
        // memo: nameIdx -> envSlot+1 (0 = unresolved)
        uint256[] envOf;
        // local context: expr indices of binder types (de Bruijn)
        uint256[] ctx;
        // parallel to ctx: the *value* of a `let`-bound local (NONE for
        // ordinary binders). Enables zeta-delta unfolding of local lets, so
        // _inferLet need not eagerly substitute (Lean: local_decl value /
        // is_let_fvar, src/kernel/type_checker.cpp).
        uint256[] ctxVal;
        uint256 ctxLen;
        // current declaration's universe parameters (window into pool)
        uint256 lpStart;
        uint256 lpLen;
        // status
        uint256 fail; // 0 ok / verdict otherwise
        uint16 reason;
        uint256 steps;
        uint256 depth;
        // well-known name indices (0 = absent)
        uint256 natIdx;
        uint256 natZeroIdx;
        uint256 natSuccIdx;
        uint256 stringIdx;
        uint256 stringMkIdx;
        uint256 stringOfListIdx;
        uint256 listNilIdx;
        uint256 listConsIdx;
        uint256 charIdx;
        uint256 charOfNatIdx;
        uint256 boolTrueIdx;
        uint256 boolFalseIdx;
        // Nat.add sub mul pow gcd mod div beq ble land lor xor shiftLeft shiftRight
        uint256[14] natOp;
        uint256 quotIdx;
    }

    /// Per-inductive-group checking state.
    struct G {
        uint256 base; // decl record index of first type record
        uint256 nT;
        uint256 nC;
        uint256 nR;
        bytes32[] indHashes;
        uint256[] indD0; // type records (word0)
        uint256[] indD1;
        bool smallElimOnly;
        // ---- nested-inductive elimination (Lean's elim_nested_inductive_fn).
        // Auxiliary type k is represented in RESTORED form: the application
        // `I_k Ds_k` of a previously declared inductive I_k to parameter
        // arguments Ds_k. Ds_k live in the context of the group's shared
        // parameter telescope (innermost parameter = bvar 0).
        uint256 np; // the group's shared parameter count
        uint256 nAux; // number of auxiliary types derived (must == numNested)
        uint256 nCtorsAux; // total constructors across auxiliary types
        uint256[] auxSlot; // env index (slot-1) of I_k's D_IND record
        uint256[] auxUs; // pool window of I_k's written universe args
        uint256[][] auxDs; // canonical Ds_k
        uint256[] vcSlot; // per virtual ctor: env index of the ctor decl
        uint256[] vcAux; // per virtual ctor: owning aux index k
    }

    // ------------------------------------------------------------------
    // Entry point
    // ------------------------------------------------------------------

    /// @param nameTab  packed name nodes (index 0 = anonymous, unused slot 0)
    /// @param nameStrs concatenated UTF-8 bytes of all string components
    /// @param levelTab packed level nodes (index 0 = Level.zero)
    /// @param exprTab  packed expression nodes
    /// @param pool     index pool for universe lists / level-param lists
    /// @param declTab  two words per declaration record
    function check(
        uint256[] calldata nameTab,
        bytes calldata nameStrs,
        uint256[] calldata levelTab,
        uint256[] calldata exprTab,
        uint256[] calldata pool,
        uint256[] calldata declTab
    ) external pure returns (uint8 verdict, uint64 failedDecl, uint16 reason) {
        M memory m = _init(nameTab, nameStrs, levelTab, exprTab, pool);
        _checkTables(m, exprTab.length, levelTab.length, nameTab.length);
        if (m.fail != 0) return (uint8(m.fail), 0, m.reason);
        _checkLevelAcyclic(m, levelTab.length);
        if (m.fail != 0) return (uint8(m.fail), 0, m.reason);
        _checkDeclTable(m, declTab, exprTab.length, nameTab.length);
        if (m.fail != 0) return (uint8(m.fail), 0, m.reason);
        uint256 nDecls = declTab.length / 2;
        uint256 i = 0;
        while (i < nDecls) {
            uint256 d0 = declTab[2 * i];
            uint256 consumed = 1;
            if ((d0 >> 248) == D_GROUP) {
                consumed = _checkGroup(m, declTab, i);
            } else {
                _checkDecl(m, d0, declTab[2 * i + 1]);
            }
            if (m.fail != 0) {
                return (uint8(m.fail), uint64(i), m.reason);
            }
            i += consumed;
        }
        return (V_ACCEPT, uint64(nDecls), R_NONE);
    }

    // ------------------------------------------------------------------
    // Setup: copy tables into growable arenas, hash names
    // ------------------------------------------------------------------

    function _init(
        uint256[] calldata nameTab,
        bytes calldata nameStrs,
        uint256[] calldata levelTab,
        uint256[] calldata exprTab,
        uint256[] calldata pool
    ) internal pure returns (M memory m) {
        uint256 exCap = exprTab.length * 4 + 4096;
        m.ex = new uint256[](exCap);
        for (uint256 i = 0; i < exprTab.length; i++) m.ex[i] = exprTab[i];
        m.exLen = exprTab.length;

        uint256 lvCap = levelTab.length * 4 + 1024;
        m.lv = new uint256[](lvCap);
        for (uint256 i = 0; i < levelTab.length; i++) m.lv[i] = levelTab[i];
        m.lvLen = levelTab.length;
        if (m.lvLen == 0) m.lvLen = 1; // slot 0 = Zero

        uint256 pCap = pool.length * 4 + 1024;
        m.pool = new uint256[](pCap);
        for (uint256 i = 0; i < pool.length; i++) m.pool[i] = pool[i];
        m.poolLen = pool.length;

        // hash names: H(0) = 0; str: keccak(pre, 0x00, bytes); num: keccak(pre, 0x01, val)
        m.nameHash = new bytes32[](nameTab.length);
        for (uint256 i = 1; i < nameTab.length; i++) {
            uint256 w = nameTab[i];
            uint256 tag = w >> 248;
            uint256 pre = w & F;
            // A prefix must name an already-hashed entry. Silently treating a
            // forward or out-of-range prefix as the root would let an export
            // manufacture any qualified name it likes — and every soundness
            // hole found in this kernel so far came from quietly reinterpreting
            // a malformed field instead of rejecting it.
            if (pre >= i) {
                m.fail = V_REJECT;
                m.reason = R_MALFORMED;
                return m;
            }
            bytes32 ph = m.nameHash[pre];
            if (tag == 0) {
                uint256 off = (w >> 48) & F;
                uint256 len = (w >> 96) & F;
                bytes memory s = new bytes(len);
                for (uint256 j = 0; j < len; j++) s[j] = nameStrs[off + j];
                m.nameHash[i] = keccak256(abi.encodePacked(ph, uint8(0), s));
            } else {
                uint256 v = (w >> 48) & F;
                m.nameHash[i] = keccak256(abi.encodePacked(ph, uint8(1), uint64(v)));
            }
        }

        m.envHash = new bytes32[](256);
        m.envDecl0 = new uint256[](256);
        m.envDecl1 = new uint256[](256);
        m.envOf = new uint256[](nameTab.length + 1);
        m.ctx = new uint256[](256);
        m.ctxVal = new uint256[](256);

        // locate well-known names (for Nat literal semantics / String typing)
        bytes32 hNat = keccak256(abi.encodePacked(bytes32(0), uint8(0), "Nat"));
        bytes32 hNatZero = keccak256(abi.encodePacked(hNat, uint8(0), "zero"));
        bytes32 hNatSucc = keccak256(abi.encodePacked(hNat, uint8(0), "succ"));
        bytes32 hString = keccak256(abi.encodePacked(bytes32(0), uint8(0), "String"));
        bytes32 hQuot = keccak256(abi.encodePacked(bytes32(0), uint8(0), "Quot"));
        // needed by string_lit_to_constructor: String.mk (List.cons (Char.ofNat c) ...)
        bytes32 hStringMk = keccak256(abi.encodePacked(hString, uint8(0), "mk"));
        // Lean >= 4.26 wraps the char list with String.ofList (a def, so the
        // result still has to be whnf'd); earlier versions used String.mk.
        bytes32 hStringOfList = keccak256(abi.encodePacked(hString, uint8(0), "ofList"));
        bytes32 hList = keccak256(abi.encodePacked(bytes32(0), uint8(0), "List"));
        bytes32 hListNil = keccak256(abi.encodePacked(hList, uint8(0), "nil"));
        bytes32 hListCons = keccak256(abi.encodePacked(hList, uint8(0), "cons"));
        bytes32 hChar = keccak256(abi.encodePacked(bytes32(0), uint8(0), "Char"));
        bytes32 hCharOfNat = keccak256(abi.encodePacked(hChar, uint8(0), "ofNat"));
        for (uint256 i = 1; i < nameTab.length; i++) {
            bytes32 h = m.nameHash[i];
            if (h == hNat) m.natIdx = i;
            else if (h == hNatZero) m.natZeroIdx = i;
            else if (h == hNatSucc) m.natSuccIdx = i;
            else if (h == hString) m.stringIdx = i;
            else if (h == hQuot) m.quotIdx = i;
            else if (h == hStringMk) m.stringMkIdx = i;
            else if (h == hStringOfList) m.stringOfListIdx = i;
            else if (h == hListNil) m.listNilIdx = i;
            else if (h == hListCons) m.listConsIdx = i;
            else if (h == hChar) m.charIdx = i;
            else if (h == hCharOfNat) m.charOfNatIdx = i;
        }
        _locateNatOps(m, nameTab.length, hNat);
    }

    /// Locate the constants Lean's `reduce_nat` accelerates, plus the Bool
    /// constructors its predicates return.
    function _locateNatOps(M memory m, uint256 nNames, bytes32 hNat) internal pure {
        bytes32[14] memory h;
        h[0] = keccak256(abi.encodePacked(hNat, uint8(0), "add"));
        h[1] = keccak256(abi.encodePacked(hNat, uint8(0), "sub"));
        h[2] = keccak256(abi.encodePacked(hNat, uint8(0), "mul"));
        h[3] = keccak256(abi.encodePacked(hNat, uint8(0), "pow"));
        h[4] = keccak256(abi.encodePacked(hNat, uint8(0), "gcd"));
        h[5] = keccak256(abi.encodePacked(hNat, uint8(0), "mod"));
        h[6] = keccak256(abi.encodePacked(hNat, uint8(0), "div"));
        h[7] = keccak256(abi.encodePacked(hNat, uint8(0), "beq"));
        h[8] = keccak256(abi.encodePacked(hNat, uint8(0), "ble"));
        h[9] = keccak256(abi.encodePacked(hNat, uint8(0), "land"));
        h[10] = keccak256(abi.encodePacked(hNat, uint8(0), "lor"));
        h[11] = keccak256(abi.encodePacked(hNat, uint8(0), "xor"));
        h[12] = keccak256(abi.encodePacked(hNat, uint8(0), "shiftLeft"));
        h[13] = keccak256(abi.encodePacked(hNat, uint8(0), "shiftRight"));
        bytes32 hBool = keccak256(abi.encodePacked(bytes32(0), uint8(0), "Bool"));
        bytes32 hTrue = keccak256(abi.encodePacked(hBool, uint8(0), "true"));
        bytes32 hFalse = keccak256(abi.encodePacked(hBool, uint8(0), "false"));
        for (uint256 i = 1; i < nNames; i++) {
            bytes32 nh = m.nameHash[i];
            if (nh == hTrue) m.boolTrueIdx = i;
            else if (nh == hFalse) m.boolFalseIdx = i;
            else {
                for (uint256 k = 0; k < 14; k++) {
                    if (nh == h[k]) {
                        m.natOp[k] = i;
                        break;
                    }
                }
            }
        }
    }

    /// Structural validation of the input tables, before any judgement runs.
    ///
    /// Two invariants, both load-bearing for termination rather than typing:
    ///
    ///  * every expression node references only strictly smaller expression
    ///    indices. lean4export always emits expressions in dependency order
    ///    (verified across the whole Arena corpus), so this is free, and it
    ///    rules out the cyclic graphs a malformed export would otherwise use to
    ///    drive `_lift` / `_inst` / `_exactEq` into unbounded recursion.
    ///  * every level and name reference is inside the table it names. The
    ///    level and expression arenas grow during checking, so an out-of-range
    ///    input index would silently alias a node manufactured later — and
    ///    those can be cyclic, which hangs the level algorithms.
    ///
    /// Level indices are NOT required to be ordered: forward references are
    /// legal there and the Arena exercises them.
    function _checkTables(M memory m, uint256 nEx, uint256 nLv, uint256 nNm) internal pure {
        for (uint256 i = 1; i < nLv; i++) {
            uint256 t = _lt(m, i);
            bool bad;
            if (t == L_SUCC) bad = _la(m, i) >= nLv;
            else if (t == L_MAX || t == L_IMAX) bad = _la(m, i) >= nLv || _lb(m, i) >= nLv;
            else if (t == L_PARAM) bad = _la(m, i) >= nNm;
            if (bad) {
                _setFail(m, V_REJECT, R_MALFORMED);
                return;
            }
        }
        for (uint256 i = 0; i < nEx; i++) {
            uint256 t = _tag(m, i);
            bool bad;
            if (t == E_APP || t == E_LAM || t == E_PI) {
                bad = _a(m, i) >= i || _b(m, i) >= i;
            } else if (t == E_LET) {
                bad = _a(m, i) >= i || _b(m, i) >= i || _c(m, i) >= i;
            } else if (t == E_PROJ) {
                bad = _c(m, i) >= i || _a(m, i) >= nNm;
            } else if (t == E_NAT) {
                // pool window: [limbCount, limbs...]
                uint256 p = _a(m, i);
                if (p >= m.poolLen) bad = true;
                else {
                    uint256 cnt = m.pool[p];
                    if (cnt > m.poolLen || p + 1 > m.poolLen - cnt) bad = true;
                }
            } else if (t == E_STRL) {
                // pool window: [byteLen, 32-byte words...]
                uint256 p = _a(m, i);
                if (p >= m.poolLen) bad = true;
                else {
                    // ceil(n/32) WITHOUT `n + 31`: the stored byte length is
                    // attacker controlled, and `n + 31` wraps for n near 2^256,
                    // yielding a tiny word count that sails past the bound.
                    uint256 n = m.pool[p];
                    uint256 words = n / 32 + (n % 32 == 0 ? 0 : 1);
                    if (words > m.poolLen || p + 1 > m.poolLen - words) bad = true;
                }
            } else if (t == E_SORT) {
                bad = _a(m, i) >= nLv;
            } else if (t == E_CONST) {
                bad = _a(m, i) >= nNm;
                uint256 s = _b(m, i);
                uint256 k = _c(m, i);
                if (!bad && (k > m.poolLen || s > m.poolLen - k)) bad = true;
                for (uint256 j = 0; !bad && j < k; j++) {
                    if (m.pool[s + j] >= nLv) bad = true;
                }
            }
            if (bad) {
                _setFail(m, V_REJECT, R_MALFORMED);
                return;
            }
        }
    }

    /// The level graph must be acyclic.
    ///
    /// Levels may legitimately reference *forward* — the Arena has a test for
    /// it — so unlike expressions they cannot be required to be index-ordered.
    /// But a cycle (`succ` pointing at itself, or any loop) sends `_simp` and
    /// `_leqCore` into unbounded recursion and blows the EVM stack, which is a
    /// checker fault rather than a verdict. Explicit-stack DFS, three-colour.
    function _checkLevelAcyclic(M memory m, uint256 nLv) internal pure {
        uint8[] memory color = new uint8[](nLv);
        uint256[] memory stk = new uint256[](2 * nLv + 4);
        for (uint256 root = 1; root < nLv; root++) {
            if (color[root] != 0) continue;
            uint256 sp = 0;
            stk[sp++] = root;
            while (sp != 0) {
                uint256 v = stk[sp - 1];
                if (color[v] != 0) {
                    if (color[v] == 1) color[v] = 2;
                    sp--;
                    continue;
                }
                color[v] = 1;
                uint256 t = _lt(m, v);
                // L_PARAM's payload is a NAME index, not a level: do not follow.
                if (t != L_SUCC && t != L_MAX && t != L_IMAX) continue;
                uint256 nKids = t == L_SUCC ? 1 : 2;
                for (uint256 kx = 0; kx < nKids; kx++) {
                    uint256 c = kx == 0 ? _la(m, v) : _lb(m, v);
                    if (color[c] == 1) {
                        _setFail(m, V_REJECT, R_MALFORMED);
                        return;
                    }
                    if (color[c] == 0 && sp < stk.length) stk[sp++] = c;
                }
            }
        }
    }

    /// Validate every index and pool window carried by a declaration record.
    ///
    /// `_checkTables` covers the level and expression tables; nothing covered
    /// the declaration table itself, so an out-of-range `type`, `value`, name,
    /// level-param window, constructor list or rule list addressed the arenas
    /// unchecked. Those arenas GROW during checking, so such an index does not
    /// read zeroes — it aliases nodes the kernel manufactures later. The same
    /// class already produced two soundness holes (the `numNested` bit-spill
    /// and the forward name prefix), and left ~80 inputs reverting rather than
    /// returning a verdict, which the Arena reads as a broken checker.
    function _checkDeclTable(M memory m, uint256[] calldata declTab, uint256 nEx, uint256 nNm)
        internal
        pure
    {
        uint256 nD = declTab.length / 2;
        for (uint256 i = 0; i < nD; i++) {
            uint256 d0 = declTab[2 * i];
            uint256 kind = d0 >> 248;
            // group headers carry counts (validated in _checkGroup against the
            // records that follow) and no indices; UNSUP carries nothing.
            if (kind == D_GROUP || kind == D_UNSUP) continue;

            bool bad = _dName(d0) >= nNm || _dType(d0) >= nEx;
            {
                uint256 v = _dValue(d0);
                if (!bad && v != NONE && v >= nEx) bad = true;
            }
            {
                uint256 s = _dLpStart(d0);
                uint256 k = _dLpLen(d0);
                if (!bad && (k > m.poolLen || s > m.poolLen - k)) bad = true;
                for (uint256 j = 0; !bad && j < k; j++) {
                    if (m.pool[s + j] >= nNm) bad = true;
                }
            }
            uint256 d1 = declTab[2 * i + 1];
            if (!bad && kind == D_CTOR && (d1 & F) >= nNm) bad = true;
            if (!bad && kind == D_IND) bad = _badNameWindow(m, (d1 >> 96) & F, nNm);
            if (!bad && kind == D_REC) bad = _badRuleWindow(m, (d1 >> 192) & F, nEx, nNm);
            if (bad) {
                _setFail(m, V_REJECT, R_MALFORMED);
                return;
            }
        }
    }

    /// A pool window holding a count followed by that many name indices.
    function _badNameWindow(M memory m, uint256 p, uint256 nNm) internal pure returns (bool) {
        if (p >= m.poolLen) return true;
        uint256 cnt = m.pool[p];
        if (cnt > m.poolLen || p + 1 > m.poolLen - cnt) return true;
        for (uint256 j = 1; j <= cnt; j++) {
            if (m.pool[p + j] >= nNm) return true;
        }
        return false;
    }

    /// A pool window holding a count followed by that many (ctorName, nfields,
    /// rhs) triples.
    function _badRuleWindow(M memory m, uint256 p, uint256 nEx, uint256 nNm) internal pure returns (bool) {
        if (p >= m.poolLen) return true;
        uint256 cnt = m.pool[p];
        if (cnt > (m.poolLen / 3) + 1 || p + 1 + 3 * cnt > m.poolLen) return true;
        for (uint256 j = 0; j < cnt; j++) {
            if (m.pool[p + 1 + 3 * j] >= nNm) return true;
            if (m.pool[p + 1 + 3 * j + 2] >= nEx) return true;
        }
        return false;
    }

    // ------------------------------------------------------------------
    // Tiny helpers
    // ------------------------------------------------------------------

    function _tag(M memory m, uint256 e) internal pure returns (uint256) {
        return m.ex[e] >> 248;
    }
    function _a(M memory m, uint256 e) internal pure returns (uint256) {
        return m.ex[e] & F;
    }
    function _b(M memory m, uint256 e) internal pure returns (uint256) {
        return (m.ex[e] >> 48) & F;
    }
    function _c(M memory m, uint256 e) internal pure returns (uint256) {
        return (m.ex[e] >> 96) & F;
    }
    function _lt(M memory m, uint256 l) internal pure returns (uint256) {
        return m.lv[l] >> 248;
    }
    function _la(M memory m, uint256 l) internal pure returns (uint256) {
        return m.lv[l] & F;
    }
    function _lb(M memory m, uint256 l) internal pure returns (uint256) {
        return (m.lv[l] >> 48) & F;
    }

    function _pushEx(M memory m, uint256 word) internal pure returns (uint256 idx) {
        if (m.exLen == m.ex.length) {
            uint256[] memory n = new uint256[](m.ex.length * 2);
            for (uint256 i = 0; i < m.exLen; i++) n[i] = m.ex[i];
            m.ex = n;
        }
        idx = m.exLen;
        m.ex[idx] = word;
        m.exLen = idx + 1;
    }

    function _pushLv(M memory m, uint256 word) internal pure returns (uint256 idx) {
        if (m.lvLen == m.lv.length) {
            uint256[] memory n = new uint256[](m.lv.length * 2);
            for (uint256 i = 0; i < m.lvLen; i++) n[i] = m.lv[i];
            m.lv = n;
        }
        idx = m.lvLen;
        m.lv[idx] = word;
        m.lvLen = idx + 1;
    }

    function _pushPool(M memory m, uint256 v) internal pure returns (uint256 idx) {
        if (m.poolLen == m.pool.length) {
            uint256[] memory n = new uint256[](m.pool.length * 2);
            for (uint256 i = 0; i < m.poolLen; i++) n[i] = m.pool[i];
            m.pool = n;
        }
        idx = m.poolLen;
        m.pool[idx] = v;
        m.poolLen = idx + 1;
    }

    function _mkE(uint256 t, uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return (t << 248) | a | (b << 48) | (c << 96);
    }
    function _mkL(uint256 t, uint256 a, uint256 b) internal pure returns (uint256) {
        return (t << 248) | a | (b << 48);
    }

    function _setFail(M memory m, uint256 verdict, uint16 r) internal pure {
        if (m.fail == 0) {
            m.fail = verdict;
            m.reason = r;
        }
    }

    function _step(M memory m) internal pure returns (bool ok) {
        unchecked {
            m.steps++;
        }
        if (m.steps > MAX_STEPS) {
            _setFail(m, V_ERROR, R_STEPS);
            return false;
        }
        return true;
    }

    function _enter(M memory m) internal pure returns (bool ok) {
        unchecked {
            m.depth++;
        }
        if (m.depth > MAX_DEPTH) {
            _setFail(m, V_ERROR, R_DEPTH);
            return false;
        }
        return true;
    }

    function _exit(M memory m) internal pure {
        unchecked {
            m.depth--;
        }
    }

    function _pushCtx(M memory m, uint256 ty) internal pure {
        _pushCtxLet(m, ty, NONE);
    }

    /// Push a binder of type `ty`; `val` is its definition when the binder
    /// came from a `let` (NONE otherwise).
    function _pushCtxLet(M memory m, uint256 ty, uint256 val) internal pure {
        if (m.ctxLen == m.ctx.length) {
            uint256[] memory n = new uint256[](m.ctx.length * 2);
            uint256[] memory nv = new uint256[](m.ctx.length * 2);
            for (uint256 i = 0; i < m.ctxLen; i++) {
                n[i] = m.ctx[i];
                nv[i] = m.ctxVal[i];
            }
            m.ctx = n;
            m.ctxVal = nv;
        }
        m.ctx[m.ctxLen] = ty;
        m.ctxVal[m.ctxLen] = val;
        m.ctxLen++;
    }

    function _popCtx(M memory m) internal pure {
        m.ctxLen--;
    }

    // ------------------------------------------------------------------
    // Universe levels
    // ------------------------------------------------------------------

    /// Structural equality of levels (fast path only).
    function _lvlExactEq(M memory m, uint256 x, uint256 y) internal pure returns (bool) {
        if (x == y) return true;
        uint256 tx_ = _lt(m, x);
        if (tx_ != _lt(m, y)) return false;
        if (tx_ == L_ZERO) return true;
        if (tx_ == L_SUCC) return _lvlExactEq(m, _la(m, x), _la(m, y));
        if (tx_ == L_PARAM) return m.nameHash[_la(m, x)] == m.nameHash[_la(m, y)];
        return _lvlExactEq(m, _la(m, x), _la(m, y)) && _lvlExactEq(m, _lb(m, x), _lb(m, y));
    }

    /// Normalization pass: eliminates imax whose second component is
    /// zero / succ / max / imax / equal to the first.
    function _simp(M memory m, uint256 l) internal pure returns (uint256) {
        uint256 t = _lt(m, l);
        if (t == L_ZERO || t == L_PARAM) return l;
        if (t == L_SUCC) {
            uint256 s = _simp(m, _la(m, l));
            return s == _la(m, l) ? l : _pushLv(m, _mkL(L_SUCC, s, 0));
        }
        uint256 a = _simp(m, _la(m, l));
        uint256 b = _simp(m, _lb(m, l));
        if (t == L_MAX) {
            if (_lvlExactEq(m, a, b)) return a;
            if (_lt(m, a) == L_ZERO) return b;
            if (_lt(m, b) == L_ZERO) return a;
            if (a == _la(m, l) && b == _lb(m, l)) return l;
            return _pushLv(m, _mkL(L_MAX, a, b));
        }
        // imax
        uint256 tb = _lt(m, b);
        if (tb == L_ZERO) return b; // imax l 0 = 0
        if (tb == L_SUCC) {
            // imax l (succ x) = max l (succ x)
            if (_lvlExactEq(m, a, b)) return a;
            if (_lt(m, a) == L_ZERO) return b;
            return _pushLv(m, _mkL(L_MAX, a, b));
        }
        if (_lvlExactEq(m, a, b)) return a; // imax l l = l
        if (tb == L_MAX) {
            // imax a (max c d) = max (imax a c) (imax a d)
            uint256 x = _simp(m, _pushLv(m, _mkL(L_IMAX, a, _la(m, b))));
            uint256 y = _simp(m, _pushLv(m, _mkL(L_IMAX, a, _lb(m, b))));
            return _simp(m, _pushLv(m, _mkL(L_MAX, x, y)));
        }
        if (tb == L_IMAX) {
            // imax a (imax c d) = max (imax a d) (imax c d)
            uint256 x = _simp(m, _pushLv(m, _mkL(L_IMAX, a, _lb(m, b))));
            uint256 y = _simp(m, _pushLv(m, _mkL(L_IMAX, _la(m, b), _lb(m, b))));
            return _simp(m, _pushLv(m, _mkL(L_MAX, x, y)));
        }
        if (a == _la(m, l) && b == _lb(m, l)) return l;
        return _pushLv(m, _mkL(L_IMAX, a, b));
    }

    /// Substitute occurrences of `param p` (by name hash) with `repl`.
    function _lvlSubstParam(M memory m, uint256 l, bytes32 p, uint256 repl) internal pure returns (uint256) {
        uint256 t = _lt(m, l);
        if (t == L_ZERO) return l;
        if (t == L_PARAM) return m.nameHash[_la(m, l)] == p ? repl : l;
        if (t == L_SUCC) {
            uint256 s = _lvlSubstParam(m, _la(m, l), p, repl);
            return s == _la(m, l) ? l : _pushLv(m, _mkL(L_SUCC, s, 0));
        }
        uint256 a = _lvlSubstParam(m, _la(m, l), p, repl);
        uint256 b = _lvlSubstParam(m, _lb(m, l), p, repl);
        if (a == _la(m, l) && b == _lb(m, l)) return l;
        return _pushLv(m, _mkL(t, a, b));
    }

    /// Find an imax whose second component is a param; returns its name hash
    /// (or bytes32(0) if none) — used for the case-split in leq.
    function _findImaxParam(M memory m, uint256 l) internal pure returns (bytes32) {
        uint256 t = _lt(m, l);
        if (t == L_ZERO || t == L_PARAM) return bytes32(0);
        if (t == L_SUCC) return _findImaxParam(m, _la(m, l));
        if (t == L_IMAX && _lt(m, _lb(m, l)) == L_PARAM) {
            return m.nameHash[_la(m, _lb(m, l))];
        }
        bytes32 h = _findImaxParam(m, _la(m, l));
        if (h != bytes32(0)) return h;
        return _findImaxParam(m, _lb(m, l));
    }

    /// Complete decision procedure for `a + diff >= ... ` i.e. a <= b + diff
    /// after normalization (standard Lean kernel algorithm).
    function _leqCore(M memory m, uint256 a, uint256 b, int256 diff) internal pure returns (bool) {
        if (!_step(m)) return false;
        uint256 ta = _lt(m, a);
        uint256 tb = _lt(m, b);

        if (ta == L_ZERO && diff >= 0) return true;
        if (tb == L_ZERO && diff < 0 && ta == L_ZERO) return false;

        if (ta == L_PARAM && tb == L_ZERO) return false;
        if (ta == L_ZERO && tb == L_PARAM) return diff >= 0;
        if (ta == L_PARAM && tb == L_PARAM) {
            return m.nameHash[_la(m, a)] == m.nameHash[_la(m, b)] && diff >= 0;
        }

        if (ta == L_SUCC) return _leqCore(m, _la(m, a), b, diff - 1);
        if (tb == L_SUCC) return _leqCore(m, a, _lb_succ(m, b), diff + 1);

        if (ta == L_MAX) {
            return _leqCore(m, _la(m, a), b, diff) && _leqCore(m, _lb(m, a), b, diff);
        }
        if ((ta == L_PARAM || ta == L_ZERO) && tb == L_MAX) {
            return _leqCore(m, a, _la(m, b), diff) || _leqCore(m, a, _lb(m, b), diff);
        }

        // imax with identical components — only sound when no successor debt
        // remains (leq(imax(u,v)+1, imax(u,v)) must NOT pass; cf. the Arena's
        // level-imax-leq soundness test, which caught nanoda on exactly this).
        if (ta == L_IMAX && tb == L_IMAX && diff >= 0 && _lvlExactEq(m, a, b)) return true;

        // case split on an imax-with-param (must exist post-normalization)
        bytes32 p = _findImaxParam(m, a);
        if (p == bytes32(0)) p = _findImaxParam(m, b);
        if (p != bytes32(0)) {
            // p := 0
            uint256 a0 = _simp(m, _lvlSubstParam(m, a, p, 0));
            uint256 b0 = _simp(m, _lvlSubstParam(m, b, p, 0));
            if (!_leqCore(m, a0, b0, diff)) return false;
            // p := succ p'  (reuse a param node with same hash, wrapped in succ)
            uint256 pn = _paramNode(m, a, b, p);
            uint256 sp = _pushLv(m, _mkL(L_SUCC, pn, 0));
            uint256 a1 = _simp(m, _lvlSubstParam(m, a, p, sp));
            uint256 b1 = _simp(m, _lvlSubstParam(m, b, p, sp));
            return _leqCore(m, a1, b1, diff);
        }
        return false;
    }

    function _lb_succ(M memory m, uint256 l) internal pure returns (uint256) {
        // pred of succ node
        return _la(m, l);
    }

    /// Locate (any) param node with hash p inside a or b so we can rebuild succ(p).
    function _paramNode(M memory m, uint256 a, uint256 b, bytes32 p) internal pure returns (uint256) {
        uint256 r = _findParamNode(m, a, p);
        if (r != NONE) return r;
        r = _findParamNode(m, b, p);
        return r;
    }

    function _findParamNode(M memory m, uint256 l, bytes32 p) internal pure returns (uint256) {
        uint256 t = _lt(m, l);
        if (t == L_ZERO) return NONE;
        if (t == L_PARAM) return m.nameHash[_la(m, l)] == p ? l : NONE;
        if (t == L_SUCC) return _findParamNode(m, _la(m, l), p);
        uint256 r = _findParamNode(m, _la(m, l), p);
        if (r != NONE) return r;
        return _findParamNode(m, _lb(m, l), p);
    }

    function _lvlLeq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        return _leqCore(m, _simp(m, a), _simp(m, b), 0);
    }

    function _lvlEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        if (x_eq(m, a, b)) return true;
        return _lvlLeq(m, a, b) && _lvlLeq(m, b, a);
    }

    function x_eq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        return _lvlExactEq(m, a, b);
    }

    function _lvlIsZero(M memory m, uint256 l) internal pure returns (bool) {
        return _lvlLeq(m, l, 0) && _lvlLeq(m, 0, l);
    }

    /// Pairwise equality of two universe lists (pool windows).
    function _usEq(M memory m, uint256 s1, uint256 n1, uint256 s2, uint256 n2) internal pure returns (bool) {
        if (n1 != n2) return false;
        for (uint256 i = 0; i < n1; i++) {
            if (!_lvlEq(m, m.pool[s1 + i], m.pool[s2 + i])) return false;
        }
        return true;
    }

    // ------------------------------------------------------------------
    // Expressions: lift / instantiate / level substitution
    // ------------------------------------------------------------------

    /// Shift loose bvars >= cutoff by amt.
    function _lift(M memory m, uint256 e, uint256 amt, uint256 cutoff) internal pure returns (uint256) {
        if (amt == 0) return e;
        uint256 t = _tag(m, e);
        if (t == E_BVAR) {
            uint256 i = _a(m, e);
            return i >= cutoff ? _pushEx(m, _mkE(E_BVAR, i + amt, 0, 0)) : e;
        }
        if (t == E_SORT || t == E_CONST || t == E_UNSUP || t == E_NAT || t == E_STRL) return e;
        if (t == E_PROJ) {
            uint256 s = _lift(m, _c(m, e), amt, cutoff);
            return s == _c(m, e) ? e : _pushEx(m, _mkE(E_PROJ, _a(m, e), _b(m, e), s));
        }
        if (t == E_APP) {
            uint256 f = _lift(m, _a(m, e), amt, cutoff);
            uint256 x = _lift(m, _b(m, e), amt, cutoff);
            if (f == _a(m, e) && x == _b(m, e)) return e;
            return _pushEx(m, _mkE(E_APP, f, x, 0));
        }
        if (t == E_LAM || t == E_PI) {
            uint256 ty = _lift(m, _a(m, e), amt, cutoff);
            uint256 bd = _lift(m, _b(m, e), amt, cutoff + 1);
            if (ty == _a(m, e) && bd == _b(m, e)) return e;
            return _pushEx(m, _mkE(t, ty, bd, 0));
        }
        // let
        uint256 lty = _lift(m, _a(m, e), amt, cutoff);
        uint256 lv_ = _lift(m, _b(m, e), amt, cutoff);
        uint256 lbd = _lift(m, _c(m, e), amt, cutoff + 1);
        if (lty == _a(m, e) && lv_ == _b(m, e) && lbd == _c(m, e)) return e;
        return _pushEx(m, _mkE(E_LET, lty, lv_, lbd));
    }

    /// Substitute bvar(depth) with v (lifted), lowering deeper bvars by one.
    function _inst(M memory m, uint256 e, uint256 v, uint256 depth) internal pure returns (uint256) {
        uint256 t = _tag(m, e);
        if (t == E_BVAR) {
            uint256 i = _a(m, e);
            if (i == depth) return _lift(m, v, depth, 0);
            if (i > depth) return _pushEx(m, _mkE(E_BVAR, i - 1, 0, 0));
            return e;
        }
        if (t == E_SORT || t == E_CONST || t == E_UNSUP || t == E_NAT || t == E_STRL) return e;
        if (t == E_PROJ) {
            uint256 s = _inst(m, _c(m, e), v, depth);
            return s == _c(m, e) ? e : _pushEx(m, _mkE(E_PROJ, _a(m, e), _b(m, e), s));
        }
        if (t == E_APP) {
            uint256 f = _inst(m, _a(m, e), v, depth);
            uint256 x = _inst(m, _b(m, e), v, depth);
            if (f == _a(m, e) && x == _b(m, e)) return e;
            return _pushEx(m, _mkE(E_APP, f, x, 0));
        }
        if (t == E_LAM || t == E_PI) {
            uint256 ty = _inst(m, _a(m, e), v, depth);
            uint256 bd = _inst(m, _b(m, e), v, depth + 1);
            if (ty == _a(m, e) && bd == _b(m, e)) return e;
            return _pushEx(m, _mkE(t, ty, bd, 0));
        }
        uint256 lty = _inst(m, _a(m, e), v, depth);
        uint256 lv_ = _inst(m, _b(m, e), v, depth);
        uint256 lbd = _inst(m, _c(m, e), v, depth + 1);
        if (lty == _a(m, e) && lv_ == _b(m, e) && lbd == _c(m, e)) return e;
        return _pushEx(m, _mkE(E_LET, lty, lv_, lbd));
    }

    /// Substitute a declaration's level params (pool window lpS..lpS+lpN, name
    /// indices) by the universe list (pool window usS..usS+usN, level indices)
    /// throughout expression e.
    function _instLevels(
        M memory m,
        uint256 e,
        uint256 lpS,
        uint256 lpN,
        uint256 usS,
        uint256 usN
    ) internal pure returns (uint256) {
        if (lpN == 0 || usN == 0) return e;
        uint256 t = _tag(m, e);
        if (t == E_BVAR || t == E_UNSUP || t == E_NAT || t == E_STRL) return e;
        if (t == E_PROJ) {
            uint256 s = _instLevels(m, _c(m, e), lpS, lpN, usS, usN);
            return s == _c(m, e) ? e : _pushEx(m, _mkE(E_PROJ, _a(m, e), _b(m, e), s));
        }
        if (t == E_SORT) {
            uint256 l = _substLvlParams(m, _a(m, e), lpS, lpN, usS);
            return l == _a(m, e) ? e : _pushEx(m, _mkE(E_SORT, l, 0, 0));
        }
        if (t == E_CONST) {
            uint256 us = _b(m, e);
            uint256 n = _c(m, e);
            bool changed = false;
            uint256 ns = m.poolLen;
            for (uint256 i = 0; i < n; i++) {
                uint256 l2 = _substLvlParams(m, m.pool[us + i], lpS, lpN, usS);
                if (l2 != m.pool[us + i]) changed = true;
                _pushPool(m, l2);
            }
            if (!changed) {
                m.poolLen = ns; // roll back
                return e;
            }
            return _pushEx(m, _mkE(E_CONST, _a(m, e), ns, n));
        }
        if (t == E_APP) {
            uint256 f = _instLevels(m, _a(m, e), lpS, lpN, usS, usN);
            uint256 x = _instLevels(m, _b(m, e), lpS, lpN, usS, usN);
            if (f == _a(m, e) && x == _b(m, e)) return e;
            return _pushEx(m, _mkE(E_APP, f, x, 0));
        }
        if (t == E_LAM || t == E_PI) {
            uint256 ty = _instLevels(m, _a(m, e), lpS, lpN, usS, usN);
            uint256 bd = _instLevels(m, _b(m, e), lpS, lpN, usS, usN);
            if (ty == _a(m, e) && bd == _b(m, e)) return e;
            return _pushEx(m, _mkE(t, ty, bd, 0));
        }
        uint256 a3 = _instLevels(m, _a(m, e), lpS, lpN, usS, usN);
        uint256 b3 = _instLevels(m, _b(m, e), lpS, lpN, usS, usN);
        uint256 c3 = _instLevels(m, _c(m, e), lpS, lpN, usS, usN);
        if (a3 == _a(m, e) && b3 == _b(m, e) && c3 == _c(m, e)) return e;
        return _pushEx(m, _mkE(E_LET, a3, b3, c3));
    }

    function _substLvlParams(M memory m, uint256 l, uint256 lpS, uint256 lpN, uint256 usS)
        internal
        pure
        returns (uint256)
    {
        uint256 t = _lt(m, l);
        if (t == L_ZERO) return l;
        if (t == L_PARAM) {
            bytes32 h = m.nameHash[_la(m, l)];
            for (uint256 i = 0; i < lpN; i++) {
                if (m.nameHash[m.pool[lpS + i]] == h) return m.pool[usS + i];
            }
            return l;
        }
        if (t == L_SUCC) {
            uint256 s = _substLvlParams(m, _la(m, l), lpS, lpN, usS);
            return s == _la(m, l) ? l : _pushLv(m, _mkL(L_SUCC, s, 0));
        }
        uint256 a = _substLvlParams(m, _la(m, l), lpS, lpN, usS);
        uint256 b = _substLvlParams(m, _lb(m, l), lpS, lpN, usS);
        if (a == _la(m, l) && b == _lb(m, l)) return l;
        return _pushLv(m, _mkL(t, a, b));
    }

    // ------------------------------------------------------------------
    // Environment
    // ------------------------------------------------------------------

    function _envAdd(M memory m, uint256 d0, uint256 d1) internal pure {
        if (m.envLen == m.envHash.length) {
            bytes32[] memory nh = new bytes32[](m.envHash.length * 2);
            uint256[] memory n0 = new uint256[](m.envHash.length * 2);
            uint256[] memory n1 = new uint256[](m.envHash.length * 2);
            for (uint256 i = 0; i < m.envLen; i++) {
                nh[i] = m.envHash[i];
                n0[i] = m.envDecl0[i];
                n1[i] = m.envDecl1[i];
            }
            m.envHash = nh;
            m.envDecl0 = n0;
            m.envDecl1 = n1;
        }
        m.envHash[m.envLen] = m.nameHash[d0 & F];
        m.envDecl0[m.envLen] = d0;
        m.envDecl1[m.envLen] = d1;
        m.envOf[d0 & F] = m.envLen + 1;
        m.envLen++;
    }

    /// Resolve a name index to env slot + 1, or 0 if unknown.
    function _envLookup(M memory m, uint256 nameIdx) internal pure returns (uint256) {
        uint256 cached = m.envOf[nameIdx];
        if (cached != 0) return cached;
        bytes32 h = m.nameHash[nameIdx];
        for (uint256 i = 0; i < m.envLen; i++) {
            if (m.envHash[i] == h) {
                m.envOf[nameIdx] = i + 1;
                return i + 1;
            }
        }
        return 0;
    }

    // decl word0 layout: kind<<248 | name | type<<48 | value<<96 | lpStart<<144 | lpLen<<192
    // decl word1 layout: hintKind<<248 | height   (hintKind: 0 regular, 1 abbrev, 2 opaque)
    function _dKind(uint256 d0) internal pure returns (uint256) {
        return d0 >> 248;
    }
    function _dName(uint256 d0) internal pure returns (uint256) {
        return d0 & F;
    }
    function _dType(uint256 d0) internal pure returns (uint256) {
        return (d0 >> 48) & F;
    }
    function _dValue(uint256 d0) internal pure returns (uint256) {
        return (d0 >> 96) & F;
    }
    function _dLpStart(uint256 d0) internal pure returns (uint256) {
        return (d0 >> 144) & F;
    }
    function _dLpLen(uint256 d0) internal pure returns (uint256) {
        return (d0 >> 192) & F;
    }
    function _dHeight(uint256 d1) internal pure returns (uint256) {
        return d1 & F;
    }

    // ------------------------------------------------------------------
    // Reduction
    // ------------------------------------------------------------------

    /// Weak head normal form without delta: beta + zeta + proj + iota + quot.
    function _whnfCore(M memory m, uint256 e) internal pure returns (uint256) {
        if (m.fail != 0) return e;
        if (!_step(m) || !_enter(m)) return e;
        for (;;) {
            uint256 t = _tag(m, e);
            if (t == E_APP) {
                uint256 f = _whnfCore(m, _a(m, e));
                if (m.fail != 0) break;
                if (_tag(m, f) == E_LAM) {
                    e = _inst(m, _b(m, f), _b(m, e), 0);
                    continue;
                }
                if (f != _a(m, e)) e = _pushEx(m, _mkE(E_APP, f, _b(m, e), 0));
                // fall through to iota/quot attempts below
            } else if (t == E_LET) {
                e = _inst(m, _c(m, e), _b(m, e), 0);
                continue;
            } else if (t == E_BVAR) {
                // zeta-delta: unfold a `let`-bound local (Lean's is_let_fvar
                // case of whnf_core / whnf). The stored value lives in the
                // context prefix below the binder, so lift it over the i+1
                // binders introduced since.
                uint256 bi = _a(m, e);
                if (bi >= m.ctxLen) break;
                uint256 bv = m.ctxVal[m.ctxLen - 1 - bi];
                if (bv == NONE) break;
                e = _lift(m, bv, bi + 1, 0);
                continue;
            } else if (t == E_PROJ) {
                (uint256 e2p, bool chp) = _projStep(m, e);
                if (m.fail != 0) break;
                if (chp) {
                    e = e2p;
                    continue;
                }
                break;
            } else {
                break;
            }
            // application spine: try iota (recursor / quotient reduction)
            (uint256 e2, bool ch) = _iotaStep(m, e);
            if (m.fail != 0) break;
            if (ch) {
                e = e2;
                continue;
            }
            (e2, ch) = _quotStep(m, e);
            if (m.fail != 0) break;
            if (ch) {
                e = e2;
                continue;
            }
            break;
        }
        _exit(m);
        return e;
    }

    /// Head of the application spine; nArgs counted.
    function _spineHead(M memory m, uint256 e) internal pure returns (uint256 h, uint256 nArgs) {
        h = e;
        while (_tag(m, h) == E_APP) {
            nArgs++;
            h = _a(m, h);
        }
    }

    /// Collect spine args in application order.
    function _collectArgs(M memory m, uint256 e, uint256 nArgs) internal pure returns (uint256[] memory args) {
        args = new uint256[](nArgs);
        uint256 cur = e;
        for (uint256 i = nArgs; i > 0; i--) {
            args[i - 1] = _b(m, cur);
            cur = _a(m, cur);
        }
    }

    function _applyRange(M memory m, uint256 base, uint256[] memory args, uint256 from, uint256 to)
        internal
        pure
        returns (uint256 r)
    {
        r = base;
        for (uint256 i = from; i < to; i++) {
            r = _pushEx(m, _mkE(E_APP, r, args[i], 0));
        }
    }

    // --- Nat literals ---------------------------------------------------

    function _natIsZero(M memory m, uint256 e) internal pure returns (bool) {
        uint256 p = _a(m, e);
        uint256 n = m.pool[p];
        for (uint256 i = 1; i <= n; i++) {
            if (m.pool[p + i] != 0) return false;
        }
        return true;
    }

    /// natlit(n) -> Nat.zero | Nat.succ (natlit (n-1)); false if Nat ctors unknown.
    function _expandNat(M memory m, uint256 e) internal pure returns (uint256, bool) {
        if (m.natZeroIdx == 0 || m.natSuccIdx == 0) {
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return (e, false);
        }
        if (_natIsZero(m, e)) {
            return (_pushEx(m, _mkE(E_CONST, m.natZeroIdx, 0, 0)), true);
        }
        // decrement limbs (little-endian words)
        uint256 p = _a(m, e);
        uint256 n = m.pool[p];
        uint256 np = _pushPool(m, n);
        bool borrow = true;
        for (uint256 i = 1; i <= n; i++) {
            uint256 limb = m.pool[p + i];
            if (borrow) {
                if (limb == 0) {
                    _pushPool(m, type(uint256).max);
                } else {
                    _pushPool(m, limb - 1);
                    borrow = false;
                }
            } else {
                _pushPool(m, limb);
            }
        }
        uint256 lit = _pushEx(m, _mkE(E_NAT, np, 0, 0));
        uint256 succ = _pushEx(m, _mkE(E_CONST, m.natSuccIdx, 0, 0));
        return (_pushEx(m, _mkE(E_APP, succ, lit, 0)), true);
    }

    // --- Nat literal acceleration (Lean's reduce_nat) ----------------------

    /// Read a Nat literal argument. Mirrors Lean's `is_nat_lit_ext`: `Nat.zero`
    /// counts as the literal 0. Operands wider than one 256-bit limb are
    /// reported as unavailable, which costs completeness on astronomically
    /// large literals but never soundness — we simply do not reduce.
    function _natArg(M memory m, uint256 e) internal pure returns (uint256 v, bool ok) {
        uint256 w = _whnf(m, e);
        if (m.fail != 0) return (0, false);
        uint256 t = _tag(m, w);
        if (t == E_CONST) {
            // Lean's `is_nat_lit_ext` compares against `g_nat_zero`, a Const
            // node whose LEVEL LIST IS EMPTY, and expr equality includes that
            // list. Matching on the name alone would read a declared
            // `Nat.zero.{u}` as the literal 0 and fold e.g. `Nat.ble` over it —
            // enough to prove False from an otherwise honest export.
            if (
                m.natZeroIdx != 0 && _c(m, w) == 0
                    && m.nameHash[_a(m, w)] == m.nameHash[m.natZeroIdx]
            ) return (0, true);
            return (0, false);
        }
        if (t != E_NAT) return (0, false);
        uint256 p = _a(m, w);
        uint256 n = _natLimbs(m, p);
        if (n == 0) return (0, true);
        if (n > 1) return (0, false);
        return (m.pool[p + 1], true);
    }

    /// Two-limb Nat literal (little-endian limbs), normalised to one limb when
    /// the high word is zero so `_natEq`'s limb-count comparison stays exact.
    function _natLit2(M memory m, uint256 hi, uint256 lo) internal pure returns (uint256) {
        if (hi == 0) return _pushEx(m, _mkE(E_NAT, _natLitOf(m, lo), 0, 0));
        uint256 ptr = _pushPool(m, 2);
        _pushPool(m, lo);
        _pushPool(m, hi);
        return _pushEx(m, _mkE(E_NAT, ptr, 0, 0));
    }

    function _boolLit(M memory m, bool b) internal pure returns (uint256, bool) {
        uint256 idx = b ? m.boolTrueIdx : m.boolFalseIdx;
        if (idx == 0 || _envLookup(m, idx) == 0) return (0, false);
        return (_pushEx(m, _mkE(E_CONST, idx, 0, 0)), true);
    }

    /// Lean's `reduce_nat`: constant-fold Nat operations on literal arguments.
    /// Without this, `Nat.beq 2 2` only reduces by unfolding Nat.beq's
    /// recursive definition, which real exports (Init.Prelude) rely on being
    /// short-circuited.
    function _reduceNat(M memory m, uint256 e) internal pure returns (uint256, bool) {
        (uint256 h, uint256 nArgs) = _spineHead(m, e);
        if (_tag(m, h) != E_CONST || _c(m, h) != 0) return (e, false);
        bytes32 nh = m.nameHash[_a(m, h)];

        // Lean's reduce_nat also folds `Nat.succ <lit>` into a literal. We
        // deliberately do not: `_expandNat` walks the other way (literal ->
        // `Nat.succ (lit n-1)`) for iota and for literal-vs-constructor defeq,
        // and having both would oscillate. The two directions meet at the
        // literal comparison either way.
        if (nArgs != 2) return (e, false);

        uint256 op = type(uint256).max;
        for (uint256 k = 0; k < 14; k++) {
            if (m.natOp[k] != 0 && nh == m.nameHash[m.natOp[k]]) {
                op = k;
                break;
            }
        }
        if (op == type(uint256).max) return (e, false);

        uint256[] memory args = _collectArgs(m, e, 2);
        (uint256 a, bool oka) = _natArg(m, args[0]);
        if (!oka || m.fail != 0) return (e, false);
        (uint256 b, bool okb) = _natArg(m, args[1]);
        if (!okb || m.fail != 0) return (e, false);

        if (op == 7) return _boolLit(m, a == b); // beq
        if (op == 8) return _boolLit(m, a <= b); // ble
        return _natBinOp(m, op, a, b);
    }

    function _natBinOp(M memory m, uint256 op, uint256 a, uint256 b) internal pure returns (uint256, bool) {
        unchecked {
            if (op == 0) {
                uint256 s = a + b;
                return (_natLit2(m, s < a ? 1 : 0, s), true);
            }
            if (op == 1) return (_natLit2(m, 0, a >= b ? a - b : 0), true); // truncated
            if (op == 2) {
                uint256 lo = a * b;
                uint256 mm = mulmod(a, b, type(uint256).max);
                uint256 hi = mm - lo - (mm < lo ? 1 : 0);
                return (_natLit2(m, hi, lo), true);
            }
            if (op == 3) {
                // pow: bail out rather than reduce once the result leaves one limb
                if (b > 256) return (0, false);
                uint256 r = 1;
                for (uint256 i = 0; i < b; i++) {
                    if (a != 0 && r > type(uint256).max / a) return (0, false);
                    r *= a;
                }
                return (_natLit2(m, 0, r), true);
            }
            if (op == 4) {
                uint256 x = a;
                uint256 y = b;
                while (y != 0) {
                    (x, y) = (y, x % y);
                }
                return (_natLit2(m, 0, x), true);
            }
            if (op == 5) return (_natLit2(m, 0, b == 0 ? a : a % b), true); // Nat.mod n 0 = n
            if (op == 6) return (_natLit2(m, 0, b == 0 ? 0 : a / b), true); // Nat.div n 0 = 0
            if (op == 9) return (_natLit2(m, 0, a & b), true);
            if (op == 10) return (_natLit2(m, 0, a | b), true);
            if (op == 11) return (_natLit2(m, 0, a ^ b), true);
            if (op == 12) {
                if (b >= 256 || (b != 0 && a > type(uint256).max >> b)) return (0, false);
                return (_natLit2(m, 0, a << b), true);
            }
            if (op == 13) return (_natLit2(m, 0, b >= 256 ? 0 : a >> b), true);
        }
        return (0, false);
    }

    // --- projection reduction --------------------------------------------

    function _projStep(M memory m, uint256 e) internal pure returns (uint256, bool) {
        uint256 s = _whnf(m, _c(m, e));
        if (m.fail != 0) return (e, false);
        // Lean's reduce_proj_core: a string literal is first turned into its
        // constructor form, otherwise projecting out of one is stuck forever.
        if (_tag(m, s) == E_STRL) {
            (uint256 sx, bool sok) = _expandString(m, s);
            if (!sok) return (e, false);
            s = _whnf(m, sx);
            if (m.fail != 0) return (e, false);
        }
        (uint256 h, uint256 nArgs) = _spineHead(m, s);
        if (_tag(m, h) == E_CONST) {
            uint256 slot = _envLookup(m, _a(m, h));
            if (slot != 0 && _dKind(m.envDecl0[slot - 1]) == D_CTOR) {
                uint256 cd1 = m.envDecl1[slot - 1];
                uint256 np = (cd1 >> 96) & F;
                uint256 nf = (cd1 >> 144) & F;
                uint256 idx = _b(m, e);
                // The constructor must belong to the structure named by the
                // projection node (cf. lean4#14576). Leave the projection stuck
                // rather than failing: _projStep runs inside speculative whnf
                // calls that are not all rollback-protected, and refusing to
                // reduce can only make a later defEq fail, never wrongly succeed.
                if (m.nameHash[cd1 & F] == m.nameHash[_a(m, e)] && nArgs == np + nf && idx < nf) {
                    uint256[] memory args = _collectArgs(m, s, nArgs);
                    return (args[np + idx], true);
                }
            }
        }
        if (s != _c(m, e)) {
            return (_pushEx(m, _mkE(E_PROJ, _a(m, e), _b(m, e), s)), false);
        }
        return (e, false);
    }

    // --- iota (recursor) reduction ----------------------------------------

    function _iotaStep(M memory m, uint256 e) internal pure returns (uint256, bool) {
        (uint256 h, uint256 nArgs) = _spineHead(m, e);
        if (_tag(m, h) != E_CONST) return (e, false);
        uint256 slot = _envLookup(m, _a(m, h));
        if (slot == 0 || _dKind(m.envDecl0[slot - 1]) != D_REC) return (e, false);
        uint256 rd1 = m.envDecl1[slot - 1];
        uint256 majorPos;
        {
            uint256 p = rd1 & F;
            uint256 idxs = (rd1 >> 48) & F;
            uint256 motives = (rd1 >> 96) & F;
            uint256 minors = (rd1 >> 144) & F;
            majorPos = p + motives + minors + idxs;
        }
        if (nArgs <= majorPos) return (e, false);
        uint256[] memory args = _collectArgs(m, e, nArgs);

        // Order follows Lean's inductive_reduce_rec: K-conversion on the raw
        // major, then whnf, then literal-or-structure conversion.
        uint256 major = args[majorPos];
        if ((rd1 >> 248) == 1) {
            major = _toCtorWhenK(m, slot, major);
            if (m.fail != 0) return (e, false);
        }
        major = _whnf(m, major);
        if (m.fail != 0) return (e, false);

        uint256 mt = _tag(m, major);
        if (mt == E_NAT) {
            (uint256 ex, bool ok) = _expandNat(m, major);
            if (!ok) return (e, false);
            major = ex;
        } else if (mt == E_STRL) {
            (uint256 sx, bool sok) = _expandString(m, major);
            if (!sok) return (e, false);
            major = _whnf(m, sx);
            if (m.fail != 0) return (e, false);
        } else {
            major = _toCtorWhenStructure(m, slot, major);
            if (m.fail != 0) return (e, false);
        }

        return _iotaApply(m, e, h, slot, args, majorPos, major);
    }

    function _iotaApply(
        M memory m,
        uint256 e,
        uint256 h,
        uint256 recSlot,
        uint256[] memory args,
        uint256 majorPos,
        uint256 major
    ) internal pure returns (uint256, bool) {
        (uint256 ch, uint256 cArgs) = _spineHead(m, major);
        if (_tag(m, ch) != E_CONST) return (e, false);
        uint256 cslot = _envLookup(m, _a(m, ch));
        if (cslot == 0 || _dKind(m.envDecl0[cslot - 1]) != D_CTOR) return (e, false);
        uint256 cnp = (m.envDecl1[cslot - 1] >> 96) & F;
        if (cArgs != cnp + ((m.envDecl1[cslot - 1] >> 144) & F)) return (e, false);

        uint256 rd1 = m.envDecl1[recSlot - 1];
        uint256 rhs = NONE;
        uint256 nfields = 0;
        {
            uint256 rulesPtr = (rd1 >> 192) & F;
            bytes32 chash = m.envHash[cslot - 1];
            uint256 nRules = m.pool[rulesPtr];
            for (uint256 r = 0; r < nRules; r++) {
                if (m.nameHash[m.pool[rulesPtr + 1 + 3 * r]] == chash) {
                    nfields = m.pool[rulesPtr + 1 + 3 * r + 1];
                    rhs = m.pool[rulesPtr + 1 + 3 * r + 2];
                    break;
                }
            }
        }
        if (rhs == NONE) return (e, false);
        // A recursor becomes reducible as soon as it is registered, which is
        // before pass 4 validates its rules — so `nfields` is still attacker
        // controlled here and is about to index the constructor's argument
        // slice. Line 1444 has already pinned `cArgs == cnp + numFields`, so
        // this is exactly pass 4's check, applied early enough to matter.
        if (nfields != cArgs - cnp) return (e, false);

        uint256 v;
        {
            uint256 rd0 = m.envDecl0[recSlot - 1];
            v = _instLevels(m, rhs, _dLpStart(rd0), _dLpLen(rd0), _b(m, h), _c(m, h));
        }
        v = _applyRange(m, v, args, 0, (rd1 & F) + ((rd1 >> 96) & F) + ((rd1 >> 144) & F));
        {
            uint256[] memory cargs = _collectArgs(m, major, cArgs);
            v = _applyRange(m, v, cargs, cnp, cnp + nfields);
        }
        v = _applyRange(m, v, args, majorPos + 1, args.length);
        return (v, true);
    }

    function _toCtorWhenK(M memory m, uint256 recSlot, uint256 major) internal pure returns (uint256) {
        // already a constructor application?
        (uint256 h, ) = _spineHead(m, major);
        if (_tag(m, h) == E_CONST) {
            uint256 s = _envLookup(m, _a(m, h));
            if (s != 0 && _dKind(m.envDecl0[s - 1]) == D_CTOR) return major;
        }
        uint256 rd1 = m.envDecl1[recSlot - 1];
        uint256 rulesPtr = (rd1 >> 192) & F;
        if (m.pool[rulesPtr] == 0) return major; // no constructor to convert to
        uint256 ctorName = m.pool[rulesPtr + 1];
        uint256 cslot = _envLookup(m, ctorName);
        if (cslot == 0) return major;
        uint256 tmaj = _inferSilent(m, major);
        if (tmaj == NONE || m.fail != 0) return major;
        tmaj = _whnf(m, tmaj);
        if (m.fail != 0) return major;
        (uint256 th, uint256 tArgs) = _spineHead(m, tmaj);
        if (_tag(m, th) != E_CONST) return major;
        uint256 cnp = (m.envDecl1[cslot - 1] >> 96) & F;
        if (tArgs < cnp) return major;
        uint256[] memory targs = _collectArgs(m, tmaj, tArgs);
        uint256 cand = _pushEx(m, _mkE(E_CONST, ctorName, _b(m, th), _c(m, th)));
        cand = _applyRange(m, cand, targs, 0, cnp);
        uint256 tcand = _inferSilent(m, cand);
        if (tcand == NONE || m.fail != 0) return major;
        if (_isDefEq(m, tcand, tmaj)) return cand;
        return major;
    }

    /// The inductive a recursor eliminates, via its first rule's constructor.
    /// Returns 0 if it cannot be determined.
    function _recMajorInduct(M memory m, uint256 recSlot) internal pure returns (uint256) {
        uint256 rulesPtr = (m.envDecl1[recSlot - 1] >> 192) & F;
        if (m.pool[rulesPtr] == 0) return 0;
        uint256 cslot = _envLookup(m, m.pool[rulesPtr + 1]);
        if (cslot == 0 || _dKind(m.envDecl0[cslot - 1]) != D_CTOR) return 0;
        uint256 islot = _envLookup(m, m.envDecl1[cslot - 1] & F);
        if (islot == 0 || _dKind(m.envDecl0[islot - 1]) != D_IND) return 0;
        return islot;
    }

    /// Lean's `to_cnstr_when_structure`: when the major premise is stuck and its
    /// type is a *non-recursive structure* (one constructor, no indices, not
    /// recursive, not a Prop), eta-expand it to
    /// `mk params (proj I 0 e) ... (proj I n-1 e)` so ι can fire. Without this a
    /// singleton in `Type` never reduces on a variable major.
    function _toCtorWhenStructure(M memory m, uint256 recSlot, uint256 major) internal pure returns (uint256) {
        (uint256 h0, ) = _spineHead(m, major);
        if (_tag(m, h0) == E_CONST) {
            uint256 s0 = _envLookup(m, _a(m, h0));
            if (s0 != 0 && _dKind(m.envDecl0[s0 - 1]) == D_CTOR) return major;
        }
        uint256 islot = _recMajorInduct(m, recSlot);
        if (islot == 0) return major;
        uint256 id1 = m.envDecl1[islot - 1];
        // non-recursive structure: exactly one ctor, no indices, not recursive
        if (m.pool[(id1 >> 96) & F] != 1 || ((id1 >> 48) & F) != 0 || ((id1 >> 192) & 1) != 0) return major;
        uint256 cslot = _envLookup(m, m.pool[((id1 >> 96) & F) + 1]);
        if (cslot == 0) return major;

        uint256 ty = _inferSilent(m, major);
        if (ty == NONE || m.fail != 0) return major;
        ty = _whnf(m, ty);
        if (m.fail != 0) return major;
        (uint256 th, uint256 tArgs) = _spineHead(m, ty);
        if (_tag(m, th) != E_CONST || m.nameHash[_a(m, th)] != m.envHash[islot - 1]) return major;
        if (_indInstanceIsProp(m, islot, th) || m.fail != 0) return major;

        uint256 cd1 = m.envDecl1[cslot - 1];
        uint256 cnp = (cd1 >> 96) & F;
        uint256 cnf = (cd1 >> 144) & F;
        if (tArgs < cnp) return major;
        uint256[] memory targs = _collectArgs(m, ty, tArgs);
        uint256 r = _pushEx(m, _mkE(E_CONST, _dName(m.envDecl0[cslot - 1]), _b(m, th), _c(m, th)));
        r = _applyRange(m, r, targs, 0, cnp);
        for (uint256 i = 0; i < cnf; i++) {
            r = _pushEx(m, _mkE(E_APP, r, _pushEx(m, _mkE(E_PROJ, _a(m, th), i, major)), 0));
        }
        return r;
    }

    /// Lean's `string_lit_to_constructor`: "abc" becomes
    /// `String.mk (List.cons (Char.ofNat 97) (List.cons ... List.nil))`, with the
    /// list at `Char` and each element the Unicode scalar value of a UTF-8
    /// decoded character.
    function _expandString(M memory m, uint256 e) internal pure returns (uint256, bool) {
        // prefer String.ofList (Lean >= 4.26), fall back to String.mk
        // Every Lean from 4.26 on builds the char list with `String.ofList`,
        // unconditionally — there is no `String.mk` to fall back to. Falling
        // back would accept a literal/constructor equation that the Lean which
        // produced the export would reject on an unknown constant.
        uint256 wrapIdx = m.stringOfListIdx;
        if (
            wrapIdx == 0 || m.listNilIdx == 0 || m.listConsIdx == 0 || m.charIdx == 0
                || m.charOfNatIdx == 0
        ) {
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return (e, false);
        }
        uint256 p = _a(m, e);
        uint256 n = m.pool[p];
        if (n > STR_EXPAND_MAX) {
            // expanding a long literal into cons cells would blow the arena;
            // declining is the honest verdict rather than a resource error.
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return (e, false);
        }
        uint256 charTy = _pushEx(m, _mkE(E_CONST, m.charIdx, 0, 0));
        // List.nil.{0} Char   /   List.cons.{0} Char
        uint256 nilPtr = _pushPool(m, 0);
        uint256 r = _pushEx(m, _mkE(E_CONST, m.listNilIdx, nilPtr, 1));
        r = _pushEx(m, _mkE(E_APP, r, charTy, 0));

        uint256[] memory cps = new uint256[](n);
        uint256 count = _utf8Decode(m, p, n, cps);
        if (m.fail != 0) return (e, false);
        for (uint256 k = count; k > 0; k--) {
            uint256 consPtr = _pushPool(m, 0);
            uint256 cons = _pushEx(m, _mkE(E_CONST, m.listConsIdx, consPtr, 1));
            cons = _pushEx(m, _mkE(E_APP, cons, charTy, 0));
            uint256 lit = _pushEx(m, _mkE(E_NAT, _natLitOf(m, cps[k - 1]), 0, 0));
            uint256 ch = _pushEx(m, _mkE(E_APP, _pushEx(m, _mkE(E_CONST, m.charOfNatIdx, 0, 0)), lit, 0));
            cons = _pushEx(m, _mkE(E_APP, cons, ch, 0));
            r = _pushEx(m, _mkE(E_APP, cons, r, 0));
        }
        r = _pushEx(m, _mkE(E_APP, _pushEx(m, _mkE(E_CONST, wrapIdx, 0, 0)), r, 0));
        return (r, true);
    }

    /// Decode the UTF-8 bytes of a string literal in the pool into Unicode
    /// scalar values. Returns the number of code points written to `out`.
    function _utf8Decode(M memory m, uint256 p, uint256 n, uint256[] memory out)
        internal
        pure
        returns (uint256)
    {
        // Mirrors Lean's next_utf8 (src/runtime/utf8.cpp), including its
        // fallback: any sequence that fails the length or range test yields the
        // raw leading byte as the code point rather than an error.
        uint256 count = 0;
        uint256 i = 0;
        while (i < n) {
            uint256 c = _strByte(m, p, i);
            uint256 cp;
            uint256 width;
            if ((c & 0x80) == 0) {
                cp = c;
                width = 1;
            } else if ((c & 0xE0) == 0xC0 && i + 1 < n) {
                cp = ((c & 0x1F) << 6) | (_strByte(m, p, i + 1) & 0x3F);
                width = cp >= 0x80 ? 2 : 0;
            } else if ((c & 0xF0) == 0xE0 && i + 2 < n) {
                cp = ((c & 0x0F) << 12) | ((_strByte(m, p, i + 1) & 0x3F) << 6)
                    | (_strByte(m, p, i + 2) & 0x3F);
                width = (cp >= 0x800 && (cp < 0xD800 || cp > 0xDFFF)) ? 3 : 0;
            } else if ((c & 0xF8) == 0xF0 && i + 3 < n) {
                cp = ((c & 0x07) << 18) | ((_strByte(m, p, i + 1) & 0x3F) << 12)
                    | ((_strByte(m, p, i + 2) & 0x3F) << 6) | (_strByte(m, p, i + 3) & 0x3F);
                width = (cp >= 0x10000 && cp <= 0x10FFFF) ? 4 : 0;
            } else {
                cp = c;
                width = 1;
            }
            if (width == 0) {
                cp = c;
                width = 1;
            }
            out[count++] = cp;
            i += width;
        }
        return count;
    }

    /// Byte `i` of the string literal whose pool window starts at `p`.
    function _strByte(M memory m, uint256 p, uint256 i) internal pure returns (uint256) {
        uint256 w = m.pool[p + 1 + i / 32];
        return (w >> (8 * (31 - (i % 32)))) & 0xFF;
    }

    /// A single-limb Nat literal pool window holding `v`. Always writes one
    /// limb, matching the encoder (tools/lib.js) so `_natEq`'s limb-count
    /// comparison lines up for zero.
    function _natLitOf(M memory m, uint256 v) internal pure returns (uint256) {
        uint256 ptr = _pushPool(m, 1);
        _pushPool(m, v);
        return ptr;
    }

    // --- quotient reduction ------------------------------------------------

    function _quotStep(M memory m, uint256 e) internal pure returns (uint256, bool) {
        (uint256 h, uint256 nArgs) = _spineHead(m, e);
        if (_tag(m, h) != E_CONST) return (e, false);
        uint256 slot = _envLookup(m, _a(m, h));
        if (slot == 0 || _dKind(m.envDecl0[slot - 1]) != D_QUOT) return (e, false);
        uint256 qk = m.envDecl1[slot - 1] & F;
        uint256 majorPos;
        if (qk == 2) majorPos = 5; // lift: {α r β} f h q
        else if (qk == 3) majorPos = 4; // ind: {α r β} mk q
        else return (e, false);
        if (nArgs <= majorPos) return (e, false);
        uint256[] memory args = _collectArgs(m, e, nArgs);
        uint256 major = _whnf(m, args[majorPos]);
        if (m.fail != 0) return (e, false);
        (uint256 mh, uint256 mArgs) = _spineHead(m, major);
        if (_tag(m, mh) != E_CONST || mArgs != 3) return (e, false);
        uint256 mslot = _envLookup(m, _a(m, mh));
        if (mslot == 0 || _dKind(m.envDecl0[mslot - 1]) != D_QUOT) return (e, false);
        if ((m.envDecl1[mslot - 1] & F) != 1) return (e, false); // Quot.mk
        uint256[] memory margs = _collectArgs(m, major, 3);
        uint256 eliminator = qk == 2 ? args[majorPos - 2] : args[majorPos - 1]; // lift: f; ind: mk
        uint256 r = _pushEx(m, _mkE(E_APP, eliminator, margs[2], 0));
        r = _applyRange(m, r, args, majorPos + 1, nArgs);
        return (r, true);
    }

    /// If the spine head is a delta-unfoldable definition, unfold it once.
    /// Returns (newExpr, true) or (e, false).
    function _deltaStep(M memory m, uint256 e) internal pure returns (uint256, bool) {
        (uint256 h, uint256 nArgs) = _spineHead(m, e);
        if (_tag(m, h) != E_CONST) return (e, false);
        uint256 slot = _envLookup(m, _a(m, h));
        if (slot == 0) return (e, false);
        uint256 d0 = m.envDecl0[slot - 1];
        // Lean's `is_delta` accepts any constant with a value — definitions AND
        // theorems (`constant_info::has_value()`); only `opaque` is excluded.
        // Theorems must unfold: a recursor whose major premise comes from a
        // hoisted proof constant, e.g. `Acc.rec .. (foo._proof_2 h)`, is
        // otherwise permanently stuck and the ι rule can never fire. Safe
        // because `_checkDef` only registers a theorem after its value has been
        // kernel-checked against its type.
        uint256 dk = _dKind(d0);
        if (dk != D_DEF && dk != D_THM) return (e, false);
        uint256 v = _instLevels(m, _dValue(d0), _dLpStart(d0), _dLpLen(d0), _b(m, h), _c(m, h));
        if (nArgs == 0) return (v, true);
        // re-apply spine args (collect then rebuild)
        uint256[] memory args = new uint256[](nArgs);
        uint256 cur = e;
        for (uint256 i = nArgs; i > 0; i--) {
            args[i - 1] = _b(m, cur);
            cur = _a(m, cur);
        }
        uint256 r = v;
        for (uint256 i = 0; i < nArgs; i++) {
            r = _pushEx(m, _mkE(E_APP, r, args[i], 0));
        }
        return (r, true);
    }

    /// Full weak head normal form: beta + zeta + delta.
    function _whnf(M memory m, uint256 e) internal pure returns (uint256) {
        for (;;) {
            if (m.fail != 0) return e;
            e = _whnfCore(m, e);
            // Lean's whnf order: whnf_core, then reduce_nat, then
            // unfold_definition (type_checker.cpp). Folding here is NOT
            // optional — omitting it makes definitional equality intransitive,
            // because a term reachable only through delta would compare equal
            // to a literal in one direction and not the other, which is enough
            // to derive False. (The earlier oscillation with `_expandNat` came
            // from also folding `Nat.succ <lit>`; that case is gone.)
            (uint256 en, bool natred) = _reduceNat(m, e);
            if (m.fail != 0) return e;
            if (natred) {
                e = en;
                continue;
            }
            (uint256 e2, bool changed) = _deltaStep(m, e);
            if (!changed) return e;
            e = e2;
        }
    }

    // ------------------------------------------------------------------
    // Definitional equality
    // ------------------------------------------------------------------

    /// Cheap structural equality (no unfolding; levels compared exactly).
    function _exactEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        if (a == b) return true;
        uint256 t = _tag(m, a);
        if (t != _tag(m, b)) return false;
        if (t == E_BVAR) return _a(m, a) == _a(m, b);
        if (t == E_SORT) return _lvlExactEq(m, _a(m, a), _a(m, b));
        if (t == E_CONST) {
            if (m.nameHash[_a(m, a)] != m.nameHash[_a(m, b)]) return false;
            uint256 n = _c(m, a);
            if (n != _c(m, b)) return false;
            for (uint256 i = 0; i < n; i++) {
                if (!_lvlExactEq(m, m.pool[_b(m, a) + i], m.pool[_b(m, b) + i])) return false;
            }
            return true;
        }
        if (t == E_APP) return _exactEq(m, _a(m, a), _a(m, b)) && _exactEq(m, _b(m, a), _b(m, b));
        if (t == E_LAM || t == E_PI) {
            return _exactEq(m, _a(m, a), _a(m, b)) && _exactEq(m, _b(m, a), _b(m, b));
        }
        if (t == E_LET) {
            return _exactEq(m, _a(m, a), _a(m, b)) && _exactEq(m, _b(m, a), _b(m, b))
                && _exactEq(m, _c(m, a), _c(m, b));
        }
        if (t == E_NAT) return _natEq(m, a, b);
        if (t == E_STRL) return _strEq(m, a, b);
        if (t == E_PROJ) {
            return m.nameHash[_a(m, a)] == m.nameHash[_a(m, b)] && _b(m, a) == _b(m, b)
                && _exactEq(m, _c(m, a), _c(m, b));
        }
        return false;
    }

    /// Numeric equality of two Nat literals, comparing VALUES rather than limb
    /// counts. `_expandNat`'s decrement keeps the source width, so
    /// `Nat.succ (2^256 - 1)` yields a two-limb representation of a value that
    /// the encoder would have written in one limb; a count-first comparison
    /// rejected those as unequal.
    function _natEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        uint256 pa = _a(m, a);
        uint256 pb = _a(m, b);
        if (pa == pb) return true;
        uint256 na = _natLimbs(m, pa);
        if (na != _natLimbs(m, pb)) return false;
        for (uint256 i = 1; i <= na; i++) {
            if (m.pool[pa + i] != m.pool[pb + i]) return false;
        }
        return true;
    }

    /// Significant limb count: the stored count with high zero limbs ignored.
    function _natLimbs(M memory m, uint256 p) internal pure returns (uint256) {
        uint256 n = m.pool[p];
        while (n > 0 && m.pool[p + n] == 0) n--;
        return n;
    }

    function _strEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        uint256 pa = _a(m, a);
        uint256 pb = _a(m, b);
        if (pa == pb) return true;
        uint256 n = m.pool[pa]; // byte length
        if (n != m.pool[pb]) return false;
        uint256 words = (n + 31) / 32;
        for (uint256 i = 1; i <= words; i++) {
            if (m.pool[pa + i] != m.pool[pb + i]) return false;
        }
        return true;
    }

    function _isDefEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        if (m.fail != 0) return false;
        if (!_step(m) || !_enter(m)) return false;
        bool r = _isDefEqCore(m, a, b);
        _exit(m);
        return r;
    }

    function _isDefEqCore(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        if (_exactEq(m, a, b)) return true;
        a = _whnfCore(m, a);
        b = _whnfCore(m, b);
        if (m.fail != 0) return false;
        if (_exactEq(m, a, b)) return true;

        // Proof irrelevance goes HERE, right after whnf_core and before lazy
        // delta — where Lean puts it (is_def_eq_proof_irrel, tc.cpp:1087).
        // Two proofs of the same Prop should be settled by their types in O(1);
        // running this last instead meant unfolding both sides and recursing
        // into their arguments first, and if that exhausted the step budget
        // `_inferSilent` would then return NONE and proof irrelevance could
        // never fire at all.
        if (_proofIrrelEq(m, a, b)) return true;
        if (m.fail != 0) return false;

        // Constant-fold Nat operations on either side before anything else
        // looks at the literals, mirroring Lean's reduce_nat inside
        // lazy_delta_reduction. Doing this after the literal-expansion branch
        // below would compare `Nat.succ 4` against an unreduced `Nat.add 2 3`.
        // Fold in place rather than recursing back through _isDefEq: a chain of
        // Nat.succ applications would otherwise burn one recursion level per
        // step and hit the depth guard.
        for (bool folded = true; folded;) {
            folded = false;
            (uint256 an, bool ar) = _reduceNat(m, a);
            if (m.fail != 0) return false;
            if (ar) {
                a = _whnfCore(m, an);
                folded = true;
            }
            (uint256 bn, bool br) = _reduceNat(m, b);
            if (m.fail != 0) return false;
            if (br) {
                b = _whnfCore(m, bn);
                folded = true;
            }
            if (m.fail != 0) return false;
        }
        if (_exactEq(m, a, b)) return true;

        uint256 ta = _tag(m, a);
        uint256 tb = _tag(m, b);

        // literals
        if (ta == E_NAT || tb == E_NAT) {
            if (ta == E_NAT && tb == E_NAT) return _natEq(m, a, b);
            // expand the literal side one constructor step and retry
            uint256 lit = ta == E_NAT ? a : b;
            uint256 oth = ta == E_NAT ? b : a;
            uint256 to = _tag(m, oth);
            if (to == E_APP || to == E_CONST) {
                (uint256 ex, bool ok) = _expandNat(m, lit);
                if (!ok) return false;
                return _isDefEq(m, ex, oth);
            }
        }
        if (ta == E_STRL || tb == E_STRL) {
            if (ta == E_STRL && tb == E_STRL) return _strEq(m, a, b);
            // literal vs constructor form: expand the literal (Lean's
            // string_lit_to_constructor) and retry.
            uint256 slit = ta == E_STRL ? a : b;
            uint256 soth = ta == E_STRL ? b : a;
            uint256 sto = _tag(m, soth);
            if (sto == E_APP || sto == E_CONST) {
                (uint256 sx, bool sok) = _expandString(m, slit);
                if (!sok) return false;
                return _isDefEq(m, sx, soth);
            }
            return false;
        }

        if (ta == E_SORT && tb == E_SORT) return _lvlEq(m, _a(m, a), _a(m, b));

        if ((ta == E_LAM && tb == E_LAM) || (ta == E_PI && tb == E_PI)) {
            if (!_isDefEq(m, _a(m, a), _a(m, b))) return false;
            _pushCtx(m, _a(m, a));
            bool r = _isDefEq(m, _b(m, a), _b(m, b));
            _popCtx(m);
            return r;
        }

        // eta: lam vs non-lam
        if (ta == E_LAM && tb != E_LAM) {
            if (_etaEq(m, a, b)) return true;
        } else if (tb == E_LAM && ta != E_LAM) {
            if (_etaEq(m, b, a)) return true;
        }

        // lazy delta: unfold definition heads (larger height first)
        (a, b) = _lazyDelta(m, a, b);
        if (m.fail != 0) return false;
        if (_exactEq(m, a, b)) return true;
        ta = _tag(m, a);
        tb = _tag(m, b);

        // literals can surface after delta unfolding (e.g. a definition
        // reducing to a Nat literal compared against constructor form)
        if (ta == E_NAT || tb == E_NAT) {
            if (ta == E_NAT && tb == E_NAT) return _natEq(m, a, b);
            uint256 lit2 = ta == E_NAT ? a : b;
            uint256 oth2 = ta == E_NAT ? b : a;
            uint256 to2 = _tag(m, oth2);
            if (to2 == E_APP || to2 == E_CONST) {
                (uint256 ex2, bool ok2) = _expandNat(m, lit2);
                if (!ok2) return false;
                return _isDefEq(m, ex2, oth2);
            }
        }

        if (ta == E_SORT && tb == E_SORT) return _lvlEq(m, _a(m, a), _a(m, b));
        if ((ta == E_LAM && tb == E_LAM) || (ta == E_PI && tb == E_PI)) {
            if (!_isDefEq(m, _a(m, a), _a(m, b))) return false;
            _pushCtx(m, _a(m, a));
            bool r2 = _isDefEq(m, _b(m, a), _b(m, b));
            _popCtx(m);
            return r2;
        }
        if (ta == E_LAM && tb != E_LAM) {
            if (_etaEq(m, a, b)) return true;
        } else if (tb == E_LAM && ta != E_LAM) {
            if (_etaEq(m, b, a)) return true;
        }

        if (ta == E_CONST && tb == E_CONST) {
            if (
                m.nameHash[_a(m, a)] == m.nameHash[_a(m, b)]
                    && _usEq(m, _b(m, a), _c(m, a), _b(m, b), _c(m, b))
            ) return true;
        }
        // Congruence for two stuck projections (Lean's is_def_eq_proj):
        // `s.i =?= t.i` when `s =?= t`. Required by every `Nat.brecOn`-style
        // structural recursion, where both sides bottom out as a stuck
        // `(Nat.rec ...).PProd#0` whose structs are definitionally but not
        // syntactically equal. Comparing only the index matches Lean; the
        // structure name is already pinned by `_inferProj`.
        if (ta == E_PROJ && tb == E_PROJ && _b(m, a) == _b(m, b)) {
            if (_isDefEq(m, _c(m, a), _c(m, b))) return true;
        }
        if (ta == E_APP && tb == E_APP) {
            if (_isDefEq(m, _a(m, a), _a(m, b)) && _isDefEq(m, _b(m, a), _b(m, b))) return true;
        }

        // structure / unit eta
        if (_tryEtaStruct(m, a, b)) return true;
        if (_tryEtaStruct(m, b, a)) return true;
        if (_unitLikeEq(m, a, b)) return true;

        // proof irrelevance
        if (_proofIrrelEq(m, a, b)) return true;

        return false;
    }

    /// Unit-like eta: any two elements of a one-constructor, zero-field,
    /// index-free inductive are definitionally equal (Prop case is covered by
    /// proof irrelevance instead).
    function _unitLikeEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        uint256 tA = _inferSilent(m, a);
        if (tA == NONE || m.fail != 0) return false;
        tA = _whnf(m, tA);
        if (m.fail != 0) return false;
        (uint256 th, ) = _spineHead(m, tA);
        if (_tag(m, th) != E_CONST) return false;
        uint256 islot = _envLookup(m, _a(m, th));
        if (islot == 0 || _dKind(m.envDecl0[islot - 1]) != D_IND) return false;
        uint256 id1 = m.envDecl1[islot - 1];
        if (((id1 >> 48) & F) != 0) return false; // no indices
        if (((id1 >> 192) & 1) != 0) return false; // not recursive (is_non_rec_structure)
        uint256 ctorsPtr = (id1 >> 96) & F;
        if (m.pool[ctorsPtr] != 1) return false;
        uint256 cslot = _envLookup(m, m.pool[ctorsPtr + 1]);
        if (cslot == 0) return false;
        if (((m.envDecl1[cslot - 1] >> 144) & F) != 0) return false; // no fields
        if (_indInstanceIsProp(m, islot, th)) return false;
        if (m.fail != 0) return false;
        uint256 tB = _inferSilent(m, b);
        if (tB == NONE || m.fail != 0) return false;
        return _isDefEq(m, tA, tB);
    }

    /// Structure eta: if c is a fully applied constructor of a single-ctor,
    /// index-free, non-Prop inductive and x's type is that inductive, compare
    /// x against ctor ps (proj 0 x) ... (proj n-1 x).
    function _tryEtaStruct(M memory m, uint256 x, uint256 c) internal pure returns (bool) {
        (uint256 ch, uint256 cn) = _spineHead(m, c);
        if (_tag(m, ch) != E_CONST) return false;
        uint256 cslot = _envLookup(m, _a(m, ch));
        if (cslot == 0 || _dKind(m.envDecl0[cslot - 1]) != D_CTOR) return false;
        uint256 cd1 = m.envDecl1[cslot - 1];
        uint256 np = (cd1 >> 96) & F;
        uint256 nf = (cd1 >> 144) & F;
        if (cn != np + nf) return false;
        uint256 islot = _envLookup(m, cd1 & F);
        if (islot == 0 || _dKind(m.envDecl0[islot - 1]) != D_IND) return false;
        uint256 id1 = m.envDecl1[islot - 1];
        if (((id1 >> 48) & F) != 0) return false; // no indices
        if (m.pool[(id1 >> 96) & F] != 1) return false; // single ctor
        // Lean's is_non_rec_structure also demands !is_rec: eta on a recursive
        // structure would equate a variable with its own unfolding.
        if (((id1 >> 192) & 1) != 0) return false;
        uint256 tX = _inferSilent(m, x);
        if (tX == NONE || m.fail != 0) return false;
        tX = _whnf(m, tX);
        if (m.fail != 0) return false;
        (uint256 th, uint256 tn) = _spineHead(m, tX);
        if (_tag(m, th) != E_CONST || m.nameHash[_a(m, th)] != m.envHash[islot - 1] || tn != np) return false;
        if (_indInstanceIsProp(m, islot, th)) return false; // proof irrelevance handles Props
        if (m.fail != 0) return false;

        // The two sides must be at the same instance of the structure.
        {
            uint256 tC = _inferSilent(m, c);
            if (tC == NONE || m.fail != 0) return false;
            if (!_isDefEq(m, tX, tC)) return false;
        }

        // Compare `proj i x` against c's i-th field, field by field — Lean's
        // try_eta_struct_core. Building `ctor (proj 0 x) ...` and handing that
        // back to _isDefEq would re-enter this function on the freshly built
        // term and recurse without bound whenever the fields disagree.
        uint256[] memory cargs = _collectArgs(m, c, cn);
        for (uint256 i = 0; i < nf; i++) {
            uint256 pr = _pushEx(m, _mkE(E_PROJ, _a(m, th), i, x));
            if (!_isDefEq(m, pr, cargs[np + i])) return false;
        }
        return true;
    }

    function _etaEq(M memory m, uint256 lam_, uint256 other) internal pure returns (bool) {
        // other must have a Pi type
        uint256 ty = _inferSilent(m, other);
        if (ty == NONE) return false;
        uint256 w = _whnf(m, ty);
        if (m.fail != 0 || _tag(m, w) != E_PI) return false;
        // compare lam.body with (lift other) (bvar 0) under the binder
        uint256 lifted = _lift(m, other, 1, 0);
        uint256 expanded = _pushEx(m, _mkE(E_APP, lifted, _pushEx(m, _mkE(E_BVAR, 0, 0, 0)), 0));
        if (!_isDefEq(m, _a(m, lam_), _a(m, w))) return false;
        _pushCtx(m, _a(m, lam_));
        bool r = _isDefEq(m, _b(m, lam_), expanded);
        _popCtx(m);
        return r;
    }

    function _proofIrrelEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        uint256 tA = _inferSilent(m, a);
        if (tA == NONE || m.fail != 0) return false;
        // is tA a proposition? sort of tA must be Sort 0
        uint256 sA = _inferSilent(m, tA);
        if (sA == NONE || m.fail != 0) return false;
        sA = _whnf(m, sA);
        if (m.fail != 0 || _tag(m, sA) != E_SORT || !_lvlIsZero(m, _a(m, sA))) return false;
        uint256 tB = _inferSilent(m, b);
        if (tB == NONE || m.fail != 0) return false;
        return _isDefEq(m, tA, tB);
    }

    /// Unfold definition heads until neither side is a definition application
    /// or the two sides become exactly equal.
    /// Lean's `is_def_eq_args`: same spine length and pairwise definitionally
    /// equal arguments. Speculative — a negative answer only means "try
    /// harder" — so any rejection raised while probing is rolled back, since
    /// `m.fail` is global state where Lean's is a pure return value.
    /// Constants `_deltaStep` will unfold: definitions and theorems, not opaque.
    function _isUnfoldable(M memory m, uint256 slot) internal pure returns (bool) {
        uint256 k = _dKind(m.envDecl0[slot - 1]);
        return k == D_DEF || k == D_THM;
    }

    function _isDefEqArgsSilent(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        uint256 savedFail = m.fail;
        uint16 savedReason = m.reason;
        bool r = true;
        while (_tag(m, a) == E_APP && _tag(m, b) == E_APP) {
            if (!_isDefEq(m, _b(m, a), _b(m, b))) {
                r = false;
                break;
            }
            a = _a(m, a);
            b = _a(m, b);
        }
        if (r) r = _tag(m, a) != E_APP && _tag(m, b) != E_APP;
        if (!r && savedFail == 0) {
            m.fail = savedFail;
            m.reason = savedReason;
        }
        return r;
    }

    function _lazyDelta(M memory m, uint256 a, uint256 b) internal pure returns (uint256, uint256) {
        for (;;) {
            if (m.fail != 0) return (a, b);
            if (!_step(m)) return (a, b);
            // Lean's lazy_delta_reduction tries reduce_nat at the top of every
            // iteration, before any unfolding. Without it a literal reachable
            // only through delta (`def foo := Nat.add 100 100`) is unfolded
            // into its recursive definition instead of folded, and the step
            // budget runs out.
            {
                (uint256 an, bool ar) = _reduceNat(m, a);
                if (m.fail != 0) return (a, b);
                if (ar) {
                    a = _whnfCore(m, an);
                    if (m.fail != 0) return (a, b);
                    continue;
                }
                (uint256 bn, bool br) = _reduceNat(m, b);
                if (m.fail != 0) return (a, b);
                if (br) {
                    b = _whnfCore(m, bn);
                    if (m.fail != 0) return (a, b);
                    continue;
                }
            }
            (uint256 ha, ) = _spineHead(m, a);
            (uint256 hb, ) = _spineHead(m, b);
            uint256 sa = _tag(m, ha) == E_CONST ? _envLookup(m, _a(m, ha)) : 0;
            uint256 sb = _tag(m, hb) == E_CONST ? _envLookup(m, _a(m, hb)) : 0;
            bool ua = sa != 0 && _isUnfoldable(m, sa);
            bool ub = sb != 0 && _isUnfoldable(m, sb);
            if (!ua && !ub) return (a, b);

            if (ua && ub) {
                // same head with same levels: try comparing args first (cheap path)
                if (m.envHash[sa - 1] == m.envHash[sb - 1]) {
                    // Congruence before unfolding — this is not merely an
                    // optimisation. It is the only route by which arguments
                    // equal for a *non-reductive* reason (proof irrelevance)
                    // are discovered: unfolding instead sends the two sides
                    // down reduction paths that never reconverge.
                    if (
                        _tag(m, a) == E_APP && _tag(m, b) == E_APP
                            && (m.envDecl1[sa - 1] >> 248) == 0 // regular hint only
                            && _usEq(m, _b(m, ha), _c(m, ha), _b(m, hb), _c(m, hb))
                            && _isDefEqArgsSilent(m, a, b)
                    ) return (a, a); // caller's next step is _exactEq(a, b)
                    if (m.fail != 0) return (a, b);
                    // unfold both (simplest sound strategy)
                    (a, ) = _deltaStep(m, a);
                    (b, ) = _deltaStep(m, b);
                } else {
                    uint256 hA = _dHeight(m.envDecl1[sa - 1]);
                    uint256 hB = _dHeight(m.envDecl1[sb - 1]);
                    if (hA >= hB) {
                        (a, ) = _deltaStep(m, a);
                    } else {
                        (b, ) = _deltaStep(m, b);
                    }
                }
            } else if (ua) {
                (a, ) = _deltaStep(m, a);
            } else {
                (b, ) = _deltaStep(m, b);
            }
            a = _whnfCore(m, a);
            b = _whnfCore(m, b);
            if (_exactEq(m, a, b)) return (a, b);
        }
    }

    // ------------------------------------------------------------------
    // Type inference
    // ------------------------------------------------------------------

    /// Inference that reports failure as NONE without setting reject status
    /// (used inside defEq heuristics: eta, proof irrelevance).
    function _inferSilent(M memory m, uint256 e) internal pure returns (uint256) {
        uint256 savedFail = m.fail;
        uint16 savedReason = m.reason;
        uint256 r = _infer(m, e);
        if (m.fail == V_REJECT && savedFail == 0) {
            // roll back rejection raised during speculative inference
            m.fail = savedFail;
            m.reason = savedReason;
            return NONE;
        }
        return r;
    }

    function _infer(M memory m, uint256 e) internal pure returns (uint256) {
        if (m.fail != 0) return NONE;
        if (!_step(m) || !_enter(m)) return NONE;
        uint256 r = _inferCore(m, e);
        _exit(m);
        return r;
    }

    function _inferCore(M memory m, uint256 e) internal pure returns (uint256) {
        uint256 t = _tag(m, e);

        if (t == E_BVAR) {
            uint256 i = _a(m, e);
            if (i >= m.ctxLen) {
                _setFail(m, V_REJECT, R_BVAR_RANGE);
                return NONE;
            }
            return _lift(m, m.ctx[m.ctxLen - 1 - i], i + 1, 0);
        }

        if (t == E_SORT) {
            uint256 s = _pushLv(m, _mkL(L_SUCC, _a(m, e), 0));
            return _pushEx(m, _mkE(E_SORT, s, 0, 0));
        }

        if (t == E_CONST) {
            uint256 slot = _envLookup(m, _a(m, e));
            if (slot == 0) {
                _setFail(m, V_REJECT, R_UNKNOWN_CONST);
                return NONE;
            }
            uint256 d0 = m.envDecl0[slot - 1];
            if (_dLpLen(d0) != _c(m, e)) {
                _setFail(m, V_REJECT, R_CONST_LEVELS);
                return NONE;
            }
            return _instLevels(m, _dType(d0), _dLpStart(d0), _dLpLen(d0), _b(m, e), _c(m, e));
        }

        if (t == E_APP) {
            uint256 tf = _infer(m, _a(m, e));
            if (m.fail != 0) return NONE;
            tf = _whnf(m, tf);
            if (m.fail != 0) return NONE;
            if (_tag(m, tf) != E_PI) {
                _setFail(m, V_REJECT, R_APP_NOT_PI);
                return NONE;
            }
            uint256 targ = _infer(m, _b(m, e));
            if (m.fail != 0) return NONE;
            if (!_isDefEq(m, targ, _a(m, tf))) {
                _setFail(m, V_REJECT, R_APP_ARG);
                return NONE;
            }
            return _inst(m, _b(m, tf), _b(m, e), 0);
        }

        if (t == E_LAM) {
            _ensureSort(m, _a(m, e));
            if (m.fail != 0) return NONE;
            _pushCtx(m, _a(m, e));
            uint256 bt = _infer(m, _b(m, e));
            _popCtx(m);
            if (m.fail != 0) return NONE;
            return _pushEx(m, _mkE(E_PI, _a(m, e), bt, 0));
        }

        if (t == E_PI) {
            uint256 u = _sortOf(m, _a(m, e));
            if (m.fail != 0) return NONE;
            _pushCtx(m, _a(m, e));
            uint256 v = _sortOf(m, _b(m, e));
            _popCtx(m);
            if (m.fail != 0) return NONE;
            uint256 im = _simp(m, _pushLv(m, _mkL(L_IMAX, u, v)));
            return _pushEx(m, _mkE(E_SORT, im, 0, 0));
        }

        if (t == E_LET) return _inferLet(m, e);

        if (t == E_NAT) {
            if (m.natIdx == 0 || _envLookup(m, m.natIdx) == 0) {
                _setFail(m, V_DECLINE, R_UNSUPPORTED);
                return NONE;
            }
            return _pushEx(m, _mkE(E_CONST, m.natIdx, 0, 0));
        }

        if (t == E_STRL) {
            if (m.stringIdx == 0 || _envLookup(m, m.stringIdx) == 0) {
                _setFail(m, V_DECLINE, R_UNSUPPORTED);
                return NONE;
            }
            return _pushEx(m, _mkE(E_CONST, m.stringIdx, 0, 0));
        }

        if (t == E_PROJ) {
            return _inferProj(m, e);
        }

        _setFail(m, V_DECLINE, R_UNSUPPORTED);
        return NONE;
    }

    /// Type a `let` cascade.
    ///
    /// Lean's `infer_let` (src/kernel/type_checker.cpp) walks the whole chain
    /// in a loop, binding each `let` as a local *with a value*, and only ever
    /// instantiates the small type/value subterms -- it never rewrites the
    /// remaining chain. Substituting the value into the body instead (the
    /// obvious de Bruijn reading) is quadratic in the chain length *and* turns
    /// each successive value into a nested lambda tower, so term size and
    /// inference recursion depth both grow with the chain. On the EVM the
    /// 1024-slot stack makes that fatal at ~40 binders. Mirror Lean: iterate,
    /// push (type, value) onto the context, infer the final body once, then
    /// re-abstract by substituting the values back, innermost first.
    function _inferLet(M memory m, uint256 e) internal pure returns (uint256) {
        uint256[] memory lets = new uint256[](16);
        uint256 n = 0;
        uint256 cur = e;
        while (_tag(m, cur) == E_LET) {
            if (!_step(m)) break;
            _ensureSort(m, _a(m, cur));
            if (m.fail != 0) break;
            uint256 tv = _infer(m, _b(m, cur));
            if (m.fail != 0) break;
            if (!_isDefEq(m, tv, _a(m, cur))) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_LET_MISMATCH);
                break;
            }
            (lets, n) = _wlPush(lets, n, cur);
            _pushCtxLet(m, _a(m, cur), _b(m, cur));
            cur = _c(m, cur);
        }
        uint256 r = NONE;
        if (m.fail == 0) r = _infer(m, cur);
        // pop the binders and bring the result type back to the outer context
        for (uint256 k = n; k > 0; k--) {
            _popCtx(m);
            if (m.fail == 0) r = _inst(m, r, _b(m, lets[k - 1]), 0);
        }
        return m.fail == 0 ? r : NONE;
    }

    /// Type a structure projection, enforcing the Prop-projection rules:
    /// out of a Prop structure one may only project Prop fields, and only
    /// when no preceding *dependent* data field exists.
    function _inferProj(M memory m, uint256 e) internal pure returns (uint256) {
        uint256 sTy = _infer(m, _c(m, e));
        if (m.fail != 0) return NONE;
        sTy = _whnf(m, sTy);
        if (m.fail != 0) return NONE;
        (uint256 h, uint256 nArgs) = _spineHead(m, sTy);
        if (_tag(m, h) != E_CONST) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        uint256 slot = _envLookup(m, _a(m, h));
        if (slot == 0 || _dKind(m.envDecl0[slot - 1]) != D_IND) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        // The structure named by the projection node must be the inductive we
        // actually inferred for the projected value. Without this, `proj C i v`
        // with `v : W` (C != W) is typed off W's constructor and the recorded
        // name is inert — the laxness behind lean4#14576.
        if (m.nameHash[_a(m, e)] != m.nameHash[_a(m, h)]) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        uint256 id1 = m.envDecl1[slot - 1];
        uint256 np = id1 & F;
        // structures: no indices, exactly one constructor, fully applied params
        uint256 ctorsPtr = (id1 >> 96) & F;
        if (((id1 >> 48) & F) != 0 || m.pool[ctorsPtr] != 1 || nArgs != np) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        uint256 cslot = _envLookup(m, m.pool[ctorsPtr + 1]);
        if (cslot == 0) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        bool isProp = _indInstanceIsProp(m, slot, h);
        if (m.fail != 0) return NONE;

        uint256 cur;
        {
            uint256 cd0 = m.envDecl0[cslot - 1];
            cur = _instLevels(m, _dType(cd0), _dLpStart(cd0), _dLpLen(cd0), _b(m, h), _c(m, h));
        }
        // consume parameters
        {
            uint256[] memory args = _collectArgs(m, sTy, nArgs);
            for (uint256 k = 0; k < np; k++) {
                cur = _whnf(m, cur);
                if (m.fail != 0) return NONE;
                if (_tag(m, cur) != E_PI) {
                    _setFail(m, V_REJECT, R_PROJ);
                    return NONE;
                }
                cur = _inst(m, _b(m, cur), args[k], 0);
            }
        }
        // walk fields
        uint256 idx = _b(m, e);
        for (uint256 i = 0; i < idx; i++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) return NONE;
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_PROJ);
                return NONE;
            }
            if (isProp && _hasLooseBVar(m, _b(m, cur), 0)) {
                // dependent field: must itself be a proof
                uint256 fs = _sortOf(m, _a(m, cur));
                if (m.fail != 0) return NONE;
                if (!_lvlLeq(m, fs, 0)) {
                    _setFail(m, V_REJECT, R_PROJ);
                    return NONE;
                }
            }
            uint256 pr = _pushEx(m, _mkE(E_PROJ, _a(m, e), i, _c(m, e)));
            cur = _inst(m, _b(m, cur), pr, 0);
        }
        cur = _whnf(m, cur);
        if (m.fail != 0) return NONE;
        if (_tag(m, cur) != E_PI) {
            _setFail(m, V_REJECT, R_PROJ);
            return NONE;
        }
        uint256 fieldTy = _a(m, cur);
        if (isProp) {
            uint256 fsr = _sortOf(m, fieldTy);
            if (m.fail != 0) return NONE;
            if (!_lvlLeq(m, fsr, 0)) {
                _setFail(m, V_REJECT, R_PROJ);
                return NONE;
            }
        }
        return fieldTy;
    }

    /// Is this instance of the inductive a Prop? (sort level of its type,
    /// instantiated with the instance's universe arguments, is zero)
    function _indInstanceIsProp(M memory m, uint256 slot, uint256 headConst) internal pure returns (bool) {
        uint256 d0 = m.envDecl0[slot - 1];
        uint256 d1 = m.envDecl1[slot - 1];
        uint256 cur = _instLevels(m, _dType(d0), _dLpStart(d0), _dLpLen(d0), _b(m, headConst), _c(m, headConst));
        uint256 total = (d1 & F) + ((d1 >> 48) & F);
        for (uint256 k = 0; k < total; k++) {
            cur = _whnf(m, cur);
            if (m.fail != 0 || _tag(m, cur) != E_PI) return false;
            cur = _b(m, cur);
        }
        cur = _whnf(m, cur);
        if (m.fail != 0 || _tag(m, cur) != E_SORT) return false;
        return _lvlLeq(m, _a(m, cur), 0);
    }

    function _hasLooseBVar(M memory m, uint256 e, uint256 k) internal pure returns (bool) {
        uint256 t = _tag(m, e);
        if (t == E_BVAR) return _a(m, e) == k;
        if (t == E_APP) return _hasLooseBVar(m, _a(m, e), k) || _hasLooseBVar(m, _b(m, e), k);
        if (t == E_LAM || t == E_PI) {
            return _hasLooseBVar(m, _a(m, e), k) || _hasLooseBVar(m, _b(m, e), k + 1);
        }
        if (t == E_LET) {
            return _hasLooseBVar(m, _a(m, e), k) || _hasLooseBVar(m, _b(m, e), k)
                || _hasLooseBVar(m, _c(m, e), k + 1);
        }
        if (t == E_PROJ) return _hasLooseBVar(m, _c(m, e), k);
        return false;
    }

    /// Does e mention any constant from the hash set?
    function _hasIndOcc(M memory m, uint256 e, bytes32[] memory inds) internal pure returns (bool) {
        uint256 t = _tag(m, e);
        if (t == E_CONST) {
            bytes32 h = m.nameHash[_a(m, e)];
            for (uint256 i = 0; i < inds.length; i++) {
                if (inds[i] == h) return true;
            }
            return false;
        }
        if (t == E_APP) return _hasIndOcc(m, _a(m, e), inds) || _hasIndOcc(m, _b(m, e), inds);
        if (t == E_LAM || t == E_PI) {
            return _hasIndOcc(m, _a(m, e), inds) || _hasIndOcc(m, _b(m, e), inds);
        }
        if (t == E_LET) {
            return _hasIndOcc(m, _a(m, e), inds) || _hasIndOcc(m, _b(m, e), inds)
                || _hasIndOcc(m, _c(m, e), inds);
        }
        if (t == E_PROJ) return _hasIndOcc(m, _c(m, e), inds);
        return false;
    }

    /// The type of e must reduce to a sort; returns its level.
    function _sortOf(M memory m, uint256 e) internal pure returns (uint256) {
        uint256 ty = _infer(m, e);
        if (m.fail != 0) return 0;
        ty = _whnf(m, ty);
        if (m.fail != 0) return 0;
        if (_tag(m, ty) != E_SORT) {
            _setFail(m, V_REJECT, R_BINDER_NOT_SORT);
            return 0;
        }
        return _a(m, ty);
    }

    /// e itself must be a type (its inferred type reduces to a sort).
    function _ensureSort(M memory m, uint256 e) internal pure {
        _sortOf(m, e);
    }

    // ------------------------------------------------------------------
    // Well-formedness scan (context-independent checks, with memo)
    // ------------------------------------------------------------------

    /// Iterative worklist push (grows the array in place).
    function _wlPush(uint256[] memory st, uint256 sp, uint256 v)
        internal
        pure
        returns (uint256[] memory, uint256)
    {
        if (sp == st.length) {
            uint256[] memory n = new uint256[](st.length * 2);
            for (uint256 i = 0; i < sp; i++) n[i] = st[i];
            st = n;
        }
        st[sp] = v;
        return (st, sp + 1);
    }

    /// Well-formedness scan. Iterative (explicit worklist): the EVM stack is
    /// 1024 slots deep, so a recursive walk overflows on a deeply nested term
    /// (e.g. a 1000-deep `let` cascade) with no chance for a depth counter to
    /// fire first -- the result is an EVM exception, not a verdict.
    function _wfExpr(M memory m, uint256 root, uint256[] memory seen) internal pure {
        uint256[] memory st = new uint256[](64);
        uint256 sp;
        (st, sp) = _wlPush(st, 0, root);
        while (sp != 0) {
            if (m.fail != 0) return;
            sp--;
            uint256 e = st[sp];
            uint256 w = seen[e / 256];
            if ((w >> (e % 256)) & 1 == 1) continue;
            seen[e / 256] = w | (1 << (e % 256));

            uint256 t = _tag(m, e);
            if (t == E_UNSUP) {
                _setFail(m, V_DECLINE, R_UNSUPPORTED);
                return;
            }
            if (t == E_SORT) {
                _wfLevel(m, _a(m, e));
                continue;
            }
            if (t == E_CONST) {
                uint256 slot = _envLookup(m, _a(m, e));
                if (slot == 0) {
                    _setFail(m, V_REJECT, R_UNKNOWN_CONST);
                    return;
                }
                if (_dLpLen(m.envDecl0[slot - 1]) != _c(m, e)) {
                    _setFail(m, V_REJECT, R_CONST_LEVELS);
                    return;
                }
                for (uint256 i = 0; i < _c(m, e); i++) _wfLevel(m, m.pool[_b(m, e) + i]);
                continue;
            }
            if (t == E_APP || t == E_LAM || t == E_PI) {
                (st, sp) = _wlPush(st, sp, _a(m, e));
                (st, sp) = _wlPush(st, sp, _b(m, e));
                continue;
            }
            if (t == E_LET) {
                (st, sp) = _wlPush(st, sp, _a(m, e));
                (st, sp) = _wlPush(st, sp, _b(m, e));
                (st, sp) = _wlPush(st, sp, _c(m, e));
                continue;
            }
            if (t == E_PROJ) {
                if (_envLookup(m, _a(m, e)) == 0) {
                    _setFail(m, V_REJECT, R_UNKNOWN_CONST);
                    return;
                }
                (st, sp) = _wlPush(st, sp, _c(m, e));
                continue;
            }
            // bvar/natlit/strlit: nothing here
        }
    }

    function _wfLevel(M memory m, uint256 l) internal pure {
        if (m.fail != 0) return;
        uint256 t = _lt(m, l);
        if (t == L_ZERO) return;
        if (t == L_PARAM) {
            bytes32 h = m.nameHash[_la(m, l)];
            for (uint256 i = 0; i < m.lpLen; i++) {
                if (m.nameHash[m.pool[m.lpStart + i]] == h) return;
            }
            _setFail(m, V_REJECT, R_UNDECLARED_PARAM);
            return;
        }
        if (t == L_SUCC) {
            _wfLevel(m, _la(m, l));
            return;
        }
        _wfLevel(m, _la(m, l));
        _wfLevel(m, _lb(m, l));
    }

    // ------------------------------------------------------------------
    // Declaration checking
    // ------------------------------------------------------------------

    function _requireFresh(M memory m, uint256 nameIdx) internal pure {
        bytes32 h = m.nameHash[nameIdx];
        for (uint256 i = 0; i < m.envLen; i++) {
            if (m.envHash[i] == h) {
                _setFail(m, V_REJECT, R_DUP_NAME);
                return;
            }
        }
    }

    function _requireLpsDistinct(M memory m, uint256 lpS, uint256 lpN) internal pure {
        for (uint256 i = 0; i < lpN; i++) {
            for (uint256 j = i + 1; j < lpN; j++) {
                if (m.nameHash[m.pool[lpS + i]] == m.nameHash[m.pool[lpS + j]]) {
                    _setFail(m, V_REJECT, R_DUP_LPARAM);
                    return;
                }
            }
        }
    }

    function _checkDecl(M memory m, uint256 d0, uint256 d1) internal pure {
        uint256 kind = _dKind(d0);
        if (kind == D_QUOT) {
            _checkQuot(m, d0, d1);
            return;
        }
        if (kind > D_OPAQUE) {
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return;
        }

        _requireFresh(m, _dName(d0));
        if (m.fail != 0) return;

        uint256 lpS = _dLpStart(d0);
        uint256 lpN = _dLpLen(d0);
        _requireLpsDistinct(m, lpS, lpN);
        if (m.fail != 0) return;
        m.lpStart = lpS;
        m.lpLen = lpN;

        // well-formedness scan (unknown consts, undeclared params, unsupported)
        uint256[] memory seen = new uint256[]((m.exLen + 255) / 256 + 1);
        _wfExpr(m, _dType(d0), seen);
        if (m.fail != 0) return;
        uint256 v = _dValue(d0);
        if (v != NONE) {
            _wfExpr(m, v, seen);
            if (m.fail != 0) return;
        }

        // the type must be a type: infer(type) reduces to a sort
        m.ctxLen = 0;
        uint256 tt = _infer(m, _dType(d0));
        if (m.fail != 0) return;
        tt = _whnf(m, tt);
        if (m.fail != 0) return;
        if (_tag(m, tt) != E_SORT) {
            _setFail(m, V_REJECT, R_TYPE_NOT_SORT);
            return;
        }
        if (kind == D_THM && !_lvlIsZero(m, _a(m, tt))) {
            _setFail(m, V_REJECT, R_THM_NOT_PROP);
            return;
        }

        // the value must have the declared type
        if (v != NONE) {
            m.ctxLen = 0;
            uint256 vt = _infer(m, v);
            if (m.fail != 0) return;
            if (!_isDefEq(m, vt, _dType(d0))) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_VALUE_MISMATCH);
                return;
            }
        } else if (kind != D_AXIOM) {
            _setFail(m, V_REJECT, R_VALUE_MISMATCH);
            return;
        }

        _envAdd(m, d0, d1);
    }

    // ------------------------------------------------------------------
    // Quotients
    // ------------------------------------------------------------------

    function _checkQuot(M memory m, uint256 d0, uint256 d1) internal pure {
        _requireFresh(m, _dName(d0));
        if (m.fail != 0) return;
        _requireLpsDistinct(m, _dLpStart(d0), _dLpLen(d0));
        if (m.fail != 0) return;
        m.lpStart = _dLpStart(d0);
        m.lpLen = _dLpLen(d0);
        uint256[] memory seen = new uint256[]((m.exLen + 255) / 256 + 1);
        _wfExpr(m, _dType(d0), seen);
        if (m.fail != 0) return;
        m.ctxLen = 0;
        uint256 tt = _infer(m, _dType(d0));
        if (m.fail != 0) return;
        tt = _whnf(m, tt);
        if (m.fail != 0) return;
        if (_tag(m, tt) != E_SORT) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return;
        }
        _checkQuotSignature(m, d0, d1);
        if (m.fail != 0) return;
        _envAdd(m, d0, d1);
    }

    function _checkQuotSignature(M memory m, uint256 d0, uint256 d1) internal pure {
        uint256 qk = d1 & F;
        bytes32 hQuot = keccak256(abi.encodePacked(bytes32(0), uint8(0), "Quot"));
        bytes32 h = m.nameHash[_dName(d0)];
        if (qk == 0) {
            if (h != hQuot || _dLpLen(d0) != 1) {
                _setFail(m, V_REJECT, R_QUOT_SHAPE);
                return;
            }
            _checkQuotTypeDecl(m, d0);
            return;
        }
        if (m.quotIdx == 0 || _envLookup(m, m.quotIdx) == 0) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return;
        }
        if (qk == 1) {
            if (h != keccak256(abi.encodePacked(hQuot, uint8(0), "mk")) || _dLpLen(d0) != 1) {
                _setFail(m, V_REJECT, R_QUOT_SHAPE);
                return;
            }
            _checkQuotCtorDecl(m, d0);
        } else if (qk == 2) {
            if (h != keccak256(abi.encodePacked(hQuot, uint8(0), "lift")) || _dLpLen(d0) != 2) {
                _setFail(m, V_REJECT, R_QUOT_SHAPE);
                return;
            }
            _checkQuotLiftDecl(m, d0);
        } else if (qk == 3) {
            if (h != keccak256(abi.encodePacked(hQuot, uint8(0), "ind")) || _dLpLen(d0) != 1) {
                _setFail(m, V_REJECT, R_QUOT_SHAPE);
                return;
            }
            _checkQuotIndDecl(m, d0);
        } else {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
        }
    }

    function _checkQuotTypeDecl(M memory m, uint256 d0) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        uint256 cur = _dType(d0);
        cur = _quotExpectPi(m, cur, _sortParam(m, _dLpStart(d0), 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotRelType(m, 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _whnf(m, cur);
        uint256 u = _pushLv(m, _mkL(L_PARAM, m.pool[_dLpStart(d0)], 0));
        if (m.fail == 0 && (_tag(m, cur) != E_SORT || !_lvlEq(m, _a(m, cur), u))) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
        }
        m.ctxLen = savedCtx;
    }

    function _checkQuotCtorDecl(M memory m, uint256 d0) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        uint256 cur = _dType(d0);
        cur = _quotExpectPi(m, cur, _sortParam(m, _dLpStart(d0), 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotRelType(m, 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _pushEx(m, _mkE(E_BVAR, 1, 0, 0)));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _whnf(m, cur);
        uint256 expected = _quotAppAt(m, _dLpStart(d0), 2, 1);
        if (m.fail == 0 && !_isDefEq(m, cur, expected)) _setFail(m, V_REJECT, R_QUOT_SHAPE);
        m.ctxLen = savedCtx;
    }

    function _checkQuotLiftDecl(M memory m, uint256 d0) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        uint256 cur = _dType(d0);
        cur = _quotExpectPi(m, cur, _sortParam(m, _dLpStart(d0), 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotRelType(m, 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _sortParam(m, _dLpStart(d0), 1));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _arrow(m, _pushEx(m, _mkE(E_BVAR, 2, 0, 0)), _pushEx(m, _mkE(E_BVAR, 0, 0, 0))));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotLiftRespType(m, _dLpStart(d0)));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotAppAt(m, _dLpStart(d0), 4, 3));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _whnf(m, cur);
        uint256 expected = _pushEx(m, _mkE(E_BVAR, 3, 0, 0));
        if (m.fail == 0 && !_isDefEq(m, cur, expected)) _setFail(m, V_REJECT, R_QUOT_SHAPE);
        m.ctxLen = savedCtx;
    }

    function _checkQuotIndDecl(M memory m, uint256 d0) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        uint256 cur = _dType(d0);
        cur = _quotExpectPi(m, cur, _sortParam(m, _dLpStart(d0), 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotRelType(m, 0));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _arrow(m, _quotAppAt(m, _dLpStart(d0), 1, 0), _pushEx(m, _mkE(E_SORT, 0, 0, 0))));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotIndMinorType(m, _dLpStart(d0)));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _quotExpectPi(m, cur, _quotAppAt(m, _dLpStart(d0), 3, 2));
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        cur = _whnf(m, cur);
        uint256 expected = _pushEx(m, _mkE(E_APP, _pushEx(m, _mkE(E_BVAR, 2, 0, 0)), _pushEx(m, _mkE(E_BVAR, 0, 0, 0)), 0));
        if (m.fail == 0 && !_isDefEq(m, cur, expected)) _setFail(m, V_REJECT, R_QUOT_SHAPE);
        m.ctxLen = savedCtx;
    }

    function _quotExpectPi(M memory m, uint256 cur, uint256 expectedDomain) internal pure returns (uint256) {
        cur = _whnf(m, cur);
        if (m.fail != 0) return cur;
        if (_tag(m, cur) != E_PI) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return cur;
        }
        if (!_isDefEq(m, _a(m, cur), expectedDomain)) {
            if (m.fail == 0) _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return cur;
        }
        _pushCtx(m, _a(m, cur));
        return _b(m, cur);
    }

    function _sortParam(M memory m, uint256 lpStart, uint256 off) internal pure returns (uint256) {
        uint256 u = _pushLv(m, _mkL(L_PARAM, m.pool[lpStart + off], 0));
        return _pushEx(m, _mkE(E_SORT, u, 0, 0));
    }

    function _arrow(M memory m, uint256 dom, uint256 cod) internal pure returns (uint256) {
        return _pushEx(m, _mkE(E_PI, dom, _lift(m, cod, 1, 0), 0));
    }

    function _quotRelType(M memory m, uint256 alphaBVar) internal pure returns (uint256) {
        uint256 prop = _pushEx(m, _mkE(E_SORT, 0, 0, 0));
        uint256 alpha = _pushEx(m, _mkE(E_BVAR, alphaBVar, 0, 0));
        uint256 alphaUnder1 = _pushEx(m, _mkE(E_BVAR, alphaBVar + 1, 0, 0));
        return _pushEx(m, _mkE(E_PI, alpha, _pushEx(m, _mkE(E_PI, alphaUnder1, prop, 0)), 0));
    }

    function _quotLiftRespType(M memory m, uint256 lpStart) internal pure returns (uint256) {
        uint256 eqName = _envNameByHash(m, keccak256(abi.encodePacked(bytes32(0), uint8(0), "Eq")));
        if (eqName == 0) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return NONE;
        }
        uint256 aTy = _pushEx(m, _mkE(E_BVAR, 3, 0, 0));
        uint256 bTy = _pushEx(m, _mkE(E_BVAR, 4, 0, 0));
        uint256 betaTy = _pushEx(m, _mkE(E_BVAR, 3, 0, 0));
        uint256 f = _pushEx(m, _mkE(E_BVAR, 2, 0, 0));
        uint256 a = _pushEx(m, _mkE(E_BVAR, 1, 0, 0));
        uint256 b = _pushEx(m, _mkE(E_BVAR, 0, 0, 0));
        uint256 r = _pushEx(m, _mkE(E_BVAR, 4, 0, 0));
        uint256 rab = _pushEx(m, _mkE(E_APP, _pushEx(m, _mkE(E_APP, r, a, 0)), b, 0));
        uint256 fa = _pushEx(m, _mkE(E_APP, f, a, 0));
        uint256 fb = _pushEx(m, _mkE(E_APP, f, b, 0));
        uint256 eq = _eqApp(m, eqName, lpStart, 1, betaTy, fa, fb);
        uint256 proof = _arrow(m, rab, eq);
        return _pushEx(m, _mkE(E_PI, aTy, _pushEx(m, _mkE(E_PI, bTy, proof, 0)), 0));
    }

    function _quotIndMinorType(M memory m, uint256 lpStart) internal pure returns (uint256) {
        uint256 mkName = _envNameByHash(
            m, keccak256(abi.encodePacked(keccak256(abi.encodePacked(bytes32(0), uint8(0), "Quot")), uint8(0), "mk"))
        );
        if (mkName == 0) {
            _setFail(m, V_REJECT, R_QUOT_SHAPE);
            return NONE;
        }
        uint256 mk = _constWithParam(m, mkName, lpStart, 0);
        mk = _pushEx(m, _mkE(E_APP, mk, _pushEx(m, _mkE(E_BVAR, 3, 0, 0)), 0));
        mk = _pushEx(m, _mkE(E_APP, mk, _pushEx(m, _mkE(E_BVAR, 2, 0, 0)), 0));
        mk = _pushEx(m, _mkE(E_APP, mk, _pushEx(m, _mkE(E_BVAR, 0, 0, 0)), 0));
        uint256 body = _pushEx(m, _mkE(E_APP, _pushEx(m, _mkE(E_BVAR, 1, 0, 0)), mk, 0));
        return _pushEx(m, _mkE(E_PI, _pushEx(m, _mkE(E_BVAR, 2, 0, 0)), body, 0));
    }

    function _eqApp(
        M memory m,
        uint256 eqName,
        uint256 lpStart,
        uint256 lpOff,
        uint256 ty,
        uint256 a,
        uint256 b
    ) internal pure returns (uint256 r) {
        r = _constWithParam(m, eqName, lpStart, lpOff);
        r = _pushEx(m, _mkE(E_APP, r, ty, 0));
        r = _pushEx(m, _mkE(E_APP, r, a, 0));
        r = _pushEx(m, _mkE(E_APP, r, b, 0));
    }

    function _constWithParam(M memory m, uint256 nameIdx, uint256 lpStart, uint256 lpOff) internal pure returns (uint256) {
        uint256 usS = m.poolLen;
        uint256 lvl = _pushLv(m, _mkL(L_PARAM, m.pool[lpStart + lpOff], 0));
        _pushPool(m, lvl);
        return _pushEx(m, _mkE(E_CONST, nameIdx, usS, 1));
    }

    function _envNameByHash(M memory m, bytes32 h) internal pure returns (uint256) {
        for (uint256 i = 0; i < m.envLen; i++) {
            if (m.envHash[i] == h) return _dName(m.envDecl0[i]);
        }
        return 0;
    }

    function _quotAppAt(M memory m, uint256 lpStart, uint256 alphaBVar, uint256 relBVar) internal pure returns (uint256 r) {
        uint256 usS = m.poolLen;
        uint256 lvl = _pushLv(m, _mkL(L_PARAM, m.pool[lpStart], 0));
        _pushPool(m, lvl);
        r = _pushEx(m, _mkE(E_CONST, m.quotIdx, usS, 1));
        r = _pushEx(m, _mkE(E_APP, r, _pushEx(m, _mkE(E_BVAR, alphaBVar, 0, 0)), 0));
        r = _pushEx(m, _mkE(E_APP, r, _pushEx(m, _mkE(E_BVAR, relBVar, 0, 0)), 0));
    }

    // ------------------------------------------------------------------
    // Inductive groups
    // ------------------------------------------------------------------

    /// The first `np` binder domains of two inductive types must agree
    /// definitionally — the shared-parameter discipline of a mutual block.
    function _paramTelescopesEq(M memory m, uint256 a, uint256 b, uint256 np) internal pure returns (bool) {
        uint256 saved = m.ctxLen;
        m.ctxLen = 0;
        bool ok = true;
        for (uint256 k = 0; k < np; k++) {
            a = _whnf(m, a);
            b = _whnf(m, b);
            if (m.fail != 0) {
                ok = false;
                break;
            }
            if (_tag(m, a) != E_PI || _tag(m, b) != E_PI) {
                ok = false;
                break;
            }
            if (!_isDefEq(m, _a(m, a), _a(m, b))) {
                ok = false;
                break;
            }
            _pushCtx(m, _a(m, a));
            a = _b(m, a);
            b = _b(m, b);
        }
        m.ctxLen = saved;
        return ok;
    }

    /// Returns the number of declaration records consumed (header + members).
    function _checkGroup(M memory m, uint256[] calldata declTab, uint256 gi) internal pure returns (uint256) {
        G memory g;
        {
            uint256 d1g = declTab[2 * gi + 1];
            g.nT = d1g & F;
            g.nC = (d1g >> 48) & F;
            g.nR = (d1g >> 96) & F;
        }
        g.base = gi + 1;
        uint256 total = 1 + g.nT + g.nC + g.nR;
        // nT bound keeps the 16-bit block-position stash in _envAdd exact
        if ((g.base + g.nT + g.nC + g.nR) * 2 > declTab.length || g.nT == 0 || g.nT > 0xFFFF) {
            _setFail(m, V_REJECT, R_IND_SHAPE);
            return total;
        }
        g.indHashes = new bytes32[](g.nT);
        g.indD0 = new uint256[](g.nT);
        g.indD1 = new uint256[](g.nT);
        uint256[] memory indLevels = new uint256[](g.nT);

        // Lean checks EVERY member's type in the pre-environment
        // (check_inductive_types runs to completion before
        // declare_inductive_types), so a member's type referring to another
        // member is an unknown constant there. We register members as we go, so
        // without this a later member's type could legally mention an earlier
        // one — `{ A : Type ; B : A -> Type }` would be accepted.
        for (uint256 t = 0; t < g.nT; t++) {
            uint256 d0t = declTab[2 * (g.base + t)];
            if (_dKind(d0t) != D_IND) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
            g.indHashes[t] = m.nameHash[_dName(d0t)];
        }
        for (uint256 t = 0; t < g.nT; t++) {
            if (_hasIndOcc(m, _dType(declTab[2 * (g.base + t)]), g.indHashes)) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
        }

        // pass 1: validate and register the inductive types
        for (uint256 t = 0; t < g.nT; t++) {
            uint256 d0 = declTab[2 * (g.base + t)];
            uint256 d1 = declTab[2 * (g.base + t) + 1];
            if (_dKind(d0) != D_IND) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
            // Every type in a mutual block shares one parameter telescope and
            // one universe-parameter list; only the indices may differ.
            if (t != 0) {
                uint256 f0 = declTab[2 * g.base];
                uint256 f1 = declTab[2 * g.base + 1];
                if ((d1 & F) != (f1 & F)) {
                    _setFail(m, V_REJECT, R_IND_SHAPE);
                    return total;
                }
                if (!_lpWindowsEq(m, _dLpStart(d0), _dLpLen(d0), _dLpStart(f0), _dLpLen(f0))) {
                    _setFail(m, V_REJECT, R_IND_SHAPE);
                    return total;
                }
                // Matching the parameter COUNT is not enough — Lean requires
                // each parameter's domain to be definitionally equal to the
                // first type's ("parameters of all inductive datatypes must
                // match", inductive.cpp check_inductive_types). Two members
                // with telescopes `(a : Type)` and `(p : Prop)` otherwise share
                // one parameter list that is not in fact shared.
                if (!_paramTelescopesEq(m, _dType(f0), _dType(d0), d1 & F)) {
                    if (m.fail == 0) _setFail(m, V_REJECT, R_IND_SHAPE);
                    return total;
                }
            }
            _requireFresh(m, _dName(d0));
            _requireLpsDistinct(m, _dLpStart(d0), _dLpLen(d0));
            if (m.fail != 0) return total;
            m.lpStart = _dLpStart(d0);
            m.lpLen = _dLpLen(d0);
            {
                uint256[] memory seen = new uint256[]((m.exLen + 255) / 256 + 1);
                _wfExpr(m, _dType(d0), seen);
            }
            if (m.fail != 0) return total;
            m.ctxLen = 0;
            uint256 tt = _infer(m, _dType(d0));
            if (m.fail != 0) return total;
            tt = _whnf(m, tt);
            if (m.fail != 0) return total;
            if (_tag(m, tt) != E_SORT) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
            // strip numParams + numIndices pis, ending in a sort
            uint256 cur = _dType(d0);
            uint256 binderCount = (d1 & F) + ((d1 >> 48) & F);
            for (uint256 k = 0; k < binderCount; k++) {
                cur = _whnf(m, cur);
                if (m.fail != 0) return total;
                if (_tag(m, cur) != E_PI) {
                    _setFail(m, V_REJECT, R_IND_SHAPE);
                    return total;
                }
                cur = _b(m, cur);
            }
            cur = _whnf(m, cur);
            if (m.fail != 0) return total;
            if (_tag(m, cur) != E_SORT) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
            indLevels[t] = _a(m, cur);
            // all members of a mutual block live in one universe
            if (t != 0 && !(_lvlLeq(m, indLevels[t], indLevels[0]) && _lvlLeq(m, indLevels[0], indLevels[t]))) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return total;
            }
            // Bits above `isRec` (192) must be clear on input. The record's
            // fields are read back masked to 48 bits, so an out-of-range
            // numNested would otherwise spill into the stash below and forge a
            // target's mutual-sibling range.
            if ((d1 >> 193) != 0) {
                _setFail(m, V_REJECT, R_MALFORMED);
                return total;
            }
            g.indHashes[t] = m.nameHash[_dName(d0)];
            g.indD0[t] = d0;
            g.indD1[t] = d1;
            // Stash the member's block position/size into free bits of the env
            // word so nested elimination can later recover a target's mutual
            // siblings (its `all` list) — members occupy consecutive env slots.
            _envAdd(m, d0, d1 | (t << 200) | (g.nT << 216));
        }

        // phase 0 (nested inductives): rerun Lean's nested->mutual elimination
        // to derive the auxiliary types, then verify the declared numNested.
        g.np = g.indD1[0] & F;
        _nestedElim(m, declTab, g);
        if (m.fail != 0) return total;
        for (uint256 t = 0; t < g.nT; t++) {
            if (((g.indD1[t] >> 144) & F) != g.nAux) {
                _setFail(m, V_REJECT, R_NESTED);
                return total;
            }
        }
        // pass 2: constructors
        bool fieldsElimOk = true;
        for (uint256 c = 0; c < g.nC; c++) {
            bool ok = _checkGroupCtor(m, declTab, g, indLevels, c);
            if (m.fail != 0) return total;
            fieldsElimOk = fieldsElimOk && ok;
        }
        _checkCtorWindows(m, declTab, g);
        if (m.fail != 0) return total;
        _recomputeIsRec(m, declTab, g);
        // pass 2b: the auxiliary types' (virtual) constructors — positivity
        // and universe bounds on the expanded group is exactly what makes
        // `List Tree` legal and `Cont Bad` illegal; there is no separate
        // "nested positivity rule".
        _checkAuxCtors(m, g, indLevels);
        if (m.fail != 0) return total;

        // elimination eligibility (over the whole auxiliary block: a nested
        // inductive always has >= 2 members, so a nested Prop is small-elim)
        {
            uint256 one = _pushLv(m, _mkL(L_SUCC, 0, 0));
            bool largeOK;
            if (g.nT == 1 && g.nAux == 0) {
                largeOK = _lvlLeq(m, one, indLevels[0]) || g.nC == 0 || (g.nC == 1 && fieldsElimOk);
            } else {
                largeOK = true;
                for (uint256 t = 0; t < g.nT; t++) {
                    largeOK = largeOK && _lvlLeq(m, one, indLevels[t]);
                }
            }
            g.smallElimOnly = !largeOK;
        }

        // pass 3: recursor declarations, then (pass 4) their reduction rules —
        // a rule RHS may reference a sibling recursor of the same block.
        for (uint256 r = 0; r < g.nR; r++) {
            _checkGroupRec(m, declTab, g, indLevels, r);
            if (m.fail != 0) return total;
        }
        for (uint256 r = 0; r < g.nR; r++) {
            _checkGroupRecRules(m, declTab, g, r);
            if (m.fail != 0) return total;
        }

        // The lean4#14577 guard: type-check each nested application `I_k Ds_k`.
        // The `Ds` are dropped from the auxiliary declaration, so they would
        // otherwise escape checking entirely — that is lean4#14576. Also
        // enforces that every auxiliary type lives in the block's universe.
        //
        // Run LAST, exactly where PR #14577 puts it: the environment must be
        // the RESTORED one, holding this block's types, constructors *and*
        // recursors, because a `Ds` may legitimately mention any of them.
        // Checking earlier makes our environment a strict subset of Lean's and
        // false-rejects e.g. `E.mk : Box E E.base -> E`.
        _checkNestedApps(m, g, indLevels);
        if (m.fail != 0) return total;
        return total;
    }

    // ------------------------------------------------------------------
    // Nested inductives (Lean's elim_nested_inductive_fn, inductive.cpp)
    // ------------------------------------------------------------------

    /// Derive the auxiliary-type table by re-running Lean's nested->mutual
    /// elimination: a worklist over the (growing) member list, scanning every
    /// constructor's post-parameter type for applications `I Ds is` of an
    /// already-declared inductive whose first numParams arguments mention the
    /// group. Purely syntactic, exactly like Lean's `replace`.
    function _nestedElim(M memory m, uint256[] calldata declTab, G memory g) internal pure {
        uint256 cap = (g.indD1[0] >> 144) & F;
        if (cap > MAX_NESTED) {
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return;
        }
        g.auxSlot = new uint256[](cap);
        g.auxUs = new uint256[](cap);
        g.auxDs = new uint256[][](cap);
        for (uint256 q = 0; q < g.nT + g.nAux; q++) {
            if (q < g.nT) {
                // declared ctors of member q, in export order
                for (uint256 ci = 0; ci < g.nC; ci++) {
                    uint256 cd1 = declTab[2 * (g.base + g.nT + ci) + 1];
                    if (m.nameHash[cd1 & F] != g.indHashes[q]) continue;
                    uint256 cur = _dType(declTab[2 * (g.base + g.nT + ci)]);
                    for (uint256 p = 0; p < g.np; p++) {
                        if (_tag(m, cur) != E_PI) {
                            _setFail(m, V_REJECT, R_CTOR_SHAPE);
                            return;
                        }
                        cur = _b(m, cur);
                    }
                    _nestedScan(m, g, cur, 0);
                    if (m.fail != 0) return;
                }
            } else {
                _nestedScanAux(m, g, q - g.nT);
                if (m.fail != 0) return;
            }
        }
        // collect the virtual constructors (aux entries in order, ctors in order)
        uint256 total = 0;
        for (uint256 k = 0; k < g.nAux; k++) {
            total += m.pool[(m.envDecl1[g.auxSlot[k]] >> 96) & F];
        }
        g.vcSlot = new uint256[](total);
        g.vcAux = new uint256[](total);
        g.nCtorsAux = total;
        uint256 v = 0;
        for (uint256 k = 0; k < g.nAux; k++) {
            uint256 ptr = (m.envDecl1[g.auxSlot[k]] >> 96) & F;
            for (uint256 j = 0; j < m.pool[ptr]; j++) {
                g.vcSlot[v] = _envLookup(m, m.pool[ptr + 1 + j]) - 1; // validated in _nestedScanAux
                g.vcAux[v] = k;
                v++;
            }
        }
    }

    /// Scan one auxiliary entry's constructors: I_k's declared ctors with
    /// levels := the occurrence's universe args and params := Ds_k.
    function _nestedScanAux(M memory m, G memory g, uint256 k) internal pure {
        uint256 islot = g.auxSlot[k];
        uint256 ptr = (m.envDecl1[islot] >> 96) & F;
        for (uint256 j = 0; j < m.pool[ptr]; j++) {
            uint256 cslot = _envLookup(m, m.pool[ptr + 1 + j]);
            if (
                cslot == 0 || _dKind(m.envDecl0[cslot - 1]) != D_CTOR
                    || m.nameHash[m.envDecl1[cslot - 1] & F] != m.envHash[islot]
                    || ((m.envDecl1[cslot - 1] >> 96) & F) != g.auxDs[k].length
            ) {
                _setFail(m, V_REJECT, R_NESTED);
                return;
            }
            uint256 cur = _instAuxCtorType(m, g, k, cslot - 1, 0);
            if (m.fail != 0) return;
            _nestedScan(m, g, cur, 0);
            if (m.fail != 0) return;
        }
    }

    /// I_k's ctor `cidx` (env index) with levels instantiated at the aux
    /// entry's universe args and the first numParams binders instantiated at
    /// Ds_k lifted by `liftAmt`; returns the remaining telescope.
    function _instAuxCtorType(M memory m, G memory g, uint256 k, uint256 cidx, uint256 liftAmt)
        internal
        pure
        returns (uint256 cur)
    {
        uint256 cd0 = m.envDecl0[cidx];
        cur = _instLevels(
            m, _dType(cd0), _dLpStart(cd0), _dLpLen(cd0), g.auxUs[k], _dLpLen(m.envDecl0[g.auxSlot[k]])
        );
        uint256[] memory ds = g.auxDs[k];
        for (uint256 p = 0; p < ds.length; p++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_NESTED);
                return NONE;
            }
            cur = _inst(m, _b(m, cur), liftAmt == 0 ? ds[p] : _lift(m, ds[p], liftAmt, 0), 0);
        }
    }

    /// Top-down syntactic traversal; children of a matched occurrence are NOT
    /// revisited (mirrors Lean's `replace`). `depth` = binders below the
    /// group's parameter telescope.
    function _nestedScan(M memory m, G memory g, uint256 e, uint256 depth) internal pure {
        if (m.fail != 0) return;
        if (!_step(m)) return;
        uint256 t = _tag(m, e);
        if (t == E_APP) {
            if (_nestedScanApp(m, g, e, depth) || m.fail != 0) return;
            _nestedScan(m, g, _a(m, e), depth);
            _nestedScan(m, g, _b(m, e), depth);
        } else if (t == E_LAM || t == E_PI) {
            _nestedScan(m, g, _a(m, e), depth);
            _nestedScan(m, g, _b(m, e), depth + 1);
        } else if (t == E_LET) {
            _nestedScan(m, g, _a(m, e), depth);
            _nestedScan(m, g, _b(m, e), depth);
            _nestedScan(m, g, _c(m, e), depth + 1);
        } else if (t == E_PROJ) {
            _nestedScan(m, g, _c(m, e), depth);
        } else if (t == E_UNSUP) {
            // cannot scan what we cannot represent — decline, never guess
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
        }
    }

    /// Is `e` a nested occurrence? If so, dedup or create auxiliary entries
    /// (one per member of the target's mutual block, in `all` order).
    function _nestedScanApp(M memory m, G memory g, uint256 e, uint256 depth) internal pure returns (bool) {
        (uint256 h, uint256 nArgs) = _spineHead(m, e);
        if (_tag(m, h) != E_CONST) return false;
        {
            bytes32 hh = m.nameHash[_a(m, h)];
            for (uint256 i = 0; i < g.indHashes.length; i++) {
                if (g.indHashes[i] == hh) return false; // group member itself
            }
        }
        uint256 islot = _envLookup(m, _a(m, h));
        if (islot == 0 || _dKind(m.envDecl0[islot - 1]) != D_IND) return false;
        uint256 npI = m.envDecl1[islot - 1] & F;
        if (npI == 0 || nArgs < npI) return false;
        if (_c(m, h) != _dLpLen(m.envDecl0[islot - 1])) return false; // ill-leveled; wf rejects later
        uint256[] memory args = _collectArgs(m, e, nArgs);
        {
            bool mentions = false;
            for (uint256 j = 0; j < npI && !mentions; j++) {
                mentions = _hasIndOcc(m, args[j], g.indHashes);
            }
            if (!mentions) return false;
        }
        // "nested inductive datatypes parameters cannot contain local
        // variables": Ds may mention the group's params but nothing deeper.
        uint256[] memory ds = new uint256[](npI);
        for (uint256 j = 0; j < npI; j++) {
            ds[j] = _lowerChecked(m, args[j], depth, 0);
            if (m.fail != 0) return true;
        }
        // dedup by structural equality (deliberately not defeq, as in Lean)
        for (uint256 k = 0; k < g.nAux; k++) {
            if (_auxEq(m, g, k, h, ds)) return true;
        }
        // miss: create an aux entry for every member of I's block
        uint256 first = (islot - 1) - ((m.envDecl1[islot - 1] >> 200) & 0xFFFF);
        uint256 size = (m.envDecl1[islot - 1] >> 216) & 0xFFFF;
        for (uint256 jm = 0; jm < size; jm++) {
            if (g.nAux == g.auxSlot.length) {
                _setFail(m, V_REJECT, R_NESTED); // more aux types than declared
                return true;
            }
            g.auxSlot[g.nAux] = first + jm;
            g.auxUs[g.nAux] = _b(m, h);
            g.auxDs[g.nAux] = ds;
            g.nAux++;
        }
        return true;
    }

    /// Does aux entry k equal head `h` (name + universe args) applied to `ds`?
    function _auxEq(M memory m, G memory g, uint256 k, uint256 h, uint256[] memory ds)
        internal
        pure
        returns (bool)
    {
        uint256 islot = g.auxSlot[k];
        if (m.nameHash[_a(m, h)] != m.envHash[islot]) return false;
        uint256[] memory dk = g.auxDs[k];
        if (dk.length != ds.length) return false;
        uint256 usN = _dLpLen(m.envDecl0[islot]);
        if (_c(m, h) != usN) return false;
        for (uint256 j = 0; j < usN; j++) {
            if (!_lvlStructEq(m, m.pool[_b(m, h) + j], m.pool[g.auxUs[k] + j])) return false;
        }
        for (uint256 j = 0; j < ds.length; j++) {
            if (!_structEq(m, dk[j], ds[j], 0, 0)) return false;
        }
        return true;
    }

    /// If spine `e` (head `h`) is an occurrence of some aux member at binder
    /// depth `depth` below the group's params, return its index; else max.
    function _auxMatch(M memory m, G memory g, uint256 e, uint256 h, uint256 nArgs, uint256 depth)
        internal
        pure
        returns (uint256)
    {
        for (uint256 k = 0; k < g.nAux; k++) {
            uint256 islot = g.auxSlot[k];
            if (m.nameHash[_a(m, h)] != m.envHash[islot]) continue;
            uint256 npk = g.auxDs[k].length;
            if (nArgs < npk) continue;
            uint256 usN = _dLpLen(m.envDecl0[islot]);
            if (_c(m, h) != usN) continue;
            bool ok = true;
            for (uint256 j = 0; j < usN && ok; j++) {
                ok = _lvlStructEq(m, m.pool[g.auxUs[k] + j], m.pool[_b(m, h) + j]);
            }
            if (!ok) continue;
            uint256[] memory args = _collectArgs(m, e, nArgs);
            for (uint256 j = 0; j < npk && ok; j++) {
                ok = _structEq(m, g.auxDs[k][j], args[j], depth, 0);
            }
            if (ok) return k;
        }
        return type(uint256).max;
    }

    function _auxNI(M memory m, G memory g, uint256 k) internal pure returns (uint256) {
        return (m.envDecl1[g.auxSlot[k]] >> 48) & F;
    }

    /// The restored application `I_k Ds_k`, with Ds lifted by `liftAmt`.
    function _auxApp(M memory m, G memory g, uint256 k, uint256 liftAmt) internal pure returns (uint256 r) {
        uint256 islot = g.auxSlot[k];
        r = _pushEx(m, _mkE(E_CONST, _dName(m.envDecl0[islot]), g.auxUs[k], _dLpLen(m.envDecl0[islot])));
        uint256[] memory ds = g.auxDs[k];
        for (uint256 j = 0; j < ds.length; j++) {
            r = _pushEx(m, _mkE(E_APP, r, _lift(m, ds[j], liftAmt, 0), 0));
        }
    }

    /// Copy `e` lowering loose bvars by `amt`; a bvar landing inside the gap
    /// (a reference to a binder below the group's params) is Lean's hard error.
    function _lowerChecked(M memory m, uint256 e, uint256 amt, uint256 cutoff) internal pure returns (uint256) {
        if (amt == 0 || m.fail != 0) return e;
        uint256 t = _tag(m, e);
        if (t == E_BVAR) {
            uint256 i = _a(m, e);
            if (i < cutoff) return e;
            if (i < cutoff + amt) {
                _setFail(m, V_REJECT, R_NESTED);
                return e;
            }
            return _pushEx(m, _mkE(E_BVAR, i - amt, 0, 0));
        }
        if (t == E_SORT || t == E_CONST || t == E_UNSUP || t == E_NAT || t == E_STRL) return e;
        if (t == E_PROJ) {
            uint256 s = _lowerChecked(m, _c(m, e), amt, cutoff);
            return s == _c(m, e) ? e : _pushEx(m, _mkE(E_PROJ, _a(m, e), _b(m, e), s));
        }
        if (t == E_APP) {
            uint256 f = _lowerChecked(m, _a(m, e), amt, cutoff);
            uint256 x = _lowerChecked(m, _b(m, e), amt, cutoff);
            if (f == _a(m, e) && x == _b(m, e)) return e;
            return _pushEx(m, _mkE(E_APP, f, x, 0));
        }
        if (t == E_LAM || t == E_PI) {
            uint256 ty = _lowerChecked(m, _a(m, e), amt, cutoff);
            uint256 bd = _lowerChecked(m, _b(m, e), amt, cutoff + 1);
            if (ty == _a(m, e) && bd == _b(m, e)) return e;
            return _pushEx(m, _mkE(t, ty, bd, 0));
        }
        uint256 lty = _lowerChecked(m, _a(m, e), amt, cutoff);
        uint256 lv_ = _lowerChecked(m, _b(m, e), amt, cutoff);
        uint256 lbd = _lowerChecked(m, _c(m, e), amt, cutoff + 1);
        if (lty == _a(m, e) && lv_ == _b(m, e) && lbd == _c(m, e)) return e;
        return _pushEx(m, _mkE(E_LET, lty, lv_, lbd));
    }

    /// Structural equality: b == lift(a, amt, cutoff), without allocating.
    function _structEq(M memory m, uint256 a, uint256 b, uint256 amt, uint256 cutoff)
        internal
        pure
        returns (bool)
    {
        if (!_step(m)) return false;
        if (amt == 0 && a == b) return true;
        uint256 t = _tag(m, a);
        if (t != _tag(m, b)) return false;
        if (t == E_BVAR) {
            uint256 i = _a(m, a);
            return _a(m, b) == (i >= cutoff ? i + amt : i);
        }
        if (t == E_SORT) return _lvlStructEq(m, _a(m, a), _a(m, b));
        if (t == E_CONST) {
            if (m.nameHash[_a(m, a)] != m.nameHash[_a(m, b)] || _c(m, a) != _c(m, b)) return false;
            for (uint256 i = 0; i < _c(m, a); i++) {
                if (!_lvlStructEq(m, m.pool[_b(m, a) + i], m.pool[_b(m, b) + i])) return false;
            }
            return true;
        }
        if (t == E_APP) {
            return _structEq(m, _a(m, a), _a(m, b), amt, cutoff) && _structEq(m, _b(m, a), _b(m, b), amt, cutoff);
        }
        if (t == E_LAM || t == E_PI) {
            return _structEq(m, _a(m, a), _a(m, b), amt, cutoff)
                && _structEq(m, _b(m, a), _b(m, b), amt, cutoff + 1);
        }
        if (t == E_LET) {
            return _structEq(m, _a(m, a), _a(m, b), amt, cutoff) && _structEq(m, _b(m, a), _b(m, b), amt, cutoff)
                && _structEq(m, _c(m, a), _c(m, b), amt, cutoff + 1);
        }
        if (t == E_PROJ) {
            return m.nameHash[_a(m, a)] == m.nameHash[_a(m, b)] && _b(m, a) == _b(m, b)
                && _structEq(m, _c(m, a), _c(m, b), amt, cutoff);
        }
        if (t == E_NAT || t == E_STRL) {
            uint256 pa = _a(m, a);
            uint256 pb = _a(m, b);
            if (pa == pb) return true;
            uint256 n = m.pool[pa];
            if (m.pool[pb] != n) return false;
            uint256 w = t == E_NAT ? n : (n + 31) / 32;
            for (uint256 i = 1; i <= w; i++) {
                if (m.pool[pa + i] != m.pool[pb + i]) return false;
            }
            return true;
        }
        return false; // E_UNSUP
    }

    function _lvlStructEq(M memory m, uint256 a, uint256 b) internal pure returns (bool) {
        if (a == b) return true;
        uint256 t = _lt(m, a);
        if (t != _lt(m, b)) return false;
        if (t == L_ZERO) return true;
        if (t == L_PARAM) return m.nameHash[_la(m, a)] == m.nameHash[_la(m, b)];
        if (t == L_SUCC) return _lvlStructEq(m, _la(m, a), _la(m, b));
        return _lvlStructEq(m, _la(m, a), _la(m, b)) && _lvlStructEq(m, _lb(m, a), _lb(m, b));
    }

    /// Reset the context to the group's shared parameter telescope.
    function _pushGroupParams(M memory m, G memory g) internal pure {
        m.ctxLen = 0;
        uint256 cur = _dType(g.indD0[0]);
        for (uint256 p = 0; p < g.np; p++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) return;
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return;
            }
            _pushCtx(m, _a(m, cur));
            cur = _b(m, cur);
        }
    }

    /// lean4#14577: type-check every nested application `I_k Ds_k` under the
    /// group's parameters, and require it to live in the block's universe.
    function _checkNestedApps(M memory m, G memory g, uint256[] memory indLevels) internal pure {
        if (g.nAux == 0) return;
        m.lpStart = _dLpStart(g.indD0[0]);
        m.lpLen = _dLpLen(g.indD0[0]);
        _pushGroupParams(m, g);
        if (m.fail != 0) return;
        for (uint256 k = 0; k < g.nAux; k++) {
            uint256 ty = _infer(m, _auxApp(m, g, k, 0));
            if (m.fail != 0) return;
            for (uint256 j = 0; j < _auxNI(m, g, k); j++) {
                ty = _whnf(m, ty);
                if (m.fail != 0) return;
                if (_tag(m, ty) != E_PI) {
                    _setFail(m, V_REJECT, R_NESTED);
                    return;
                }
                ty = _b(m, ty);
            }
            ty = _whnf(m, ty);
            if (m.fail != 0) return;
            if (
                _tag(m, ty) != E_SORT
                    || !(_lvlLeq(m, _a(m, ty), indLevels[0]) && _lvlLeq(m, indLevels[0], _a(m, ty)))
            ) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_NESTED);
                return;
            }
        }
        m.ctxLen = 0;
    }

    /// Pass 2b: check the auxiliary types' constructors — strict positivity,
    /// field-universe bounds, and the lean4#2125 index guard on the result.
    function _checkAuxCtors(M memory m, G memory g, uint256[] memory indLevels) internal pure {
        if (g.nAux == 0) return;
        m.lpStart = _dLpStart(g.indD0[0]);
        m.lpLen = _dLpLen(g.indD0[0]);
        bool indIsProp = _lvlLeq(m, indLevels[0], 0);
        for (uint256 v = 0; v < g.nCtorsAux; v++) {
            uint256 k = g.vcAux[v];
            _pushGroupParams(m, g);
            if (m.fail != 0) return;
            uint256 cur = _instAuxCtorType(m, g, k, g.vcSlot[v], 0);
            if (m.fail != 0) return;
            uint256 nf = (m.envDecl1[g.vcSlot[v]] >> 144) & F;
            for (uint256 j = 0; j < nf; j++) {
                if (_tag(m, cur) != E_PI) {
                    _setFail(m, V_REJECT, R_NESTED);
                    return;
                }
                _posCheck(m, _a(m, cur), g, j);
                if (m.fail != 0) return;
                uint256 fs = _sortOf(m, _a(m, cur));
                if (m.fail != 0) return;
                if (!indIsProp && !_lvlLeq(m, fs, indLevels[0])) {
                    _setFail(m, V_REJECT, R_FIELD_UNIVERSE);
                    return;
                }
                _pushCtx(m, _a(m, cur));
                cur = _b(m, cur);
            }
            (uint256 h, uint256 nArgs) = _spineHead(m, cur);
            if (
                _tag(m, h) != E_CONST || m.nameHash[_a(m, h)] != m.envHash[g.auxSlot[k]]
                    || nArgs != g.auxDs[k].length + _auxNI(m, g, k)
            ) {
                _setFail(m, V_REJECT, R_NESTED);
                return;
            }
            uint256[] memory args = _collectArgs(m, cur, nArgs);
            for (uint256 j = g.auxDs[k].length; j < nArgs; j++) {
                if (_hasIndOcc(m, args[j], g.indHashes)) {
                    _setFail(m, V_REJECT, R_CTOR_RESULT);
                    return;
                }
            }
        }
        m.ctxLen = 0;
    }

    /// Decimal digits of v (>= 1), for the `rec_{k}` recursor-name suffix.
    function _decSuffix(uint256 v) internal pure returns (bytes memory b) {
        uint256 len = 0;
        for (uint256 x = v; x > 0; x /= 10) len++;
        b = new bytes(len);
        for (uint256 x = v; x > 0; x /= 10) {
            len--;
            b[len] = bytes1(uint8(48 + (x % 10)));
        }
    }

    struct CtorCtx {
        uint256 d0;
        uint256 d1;
        uint256 tpos;
        uint256 np;
        uint256 nf;
        uint256 fieldPropBits; // bit j set = field j is a proof
    }

    /// Each type's `ctors` name window must list exactly the constructors the
    /// block declares for it — same count, same names.
    ///
    /// lean4export states an inductive's constructors twice: as a name list on
    /// the type record, and as full declarations in the block's `ctors` array.
    /// Only the latter was validated. For a plain inductive a lying window is
    /// harmless, because minor premises are counted from the declared ctors;
    /// but the nested machinery reads the window as the authority for an
    /// *auxiliary* type's constructor set, so an empty window would present an
    /// inhabited type as having no cases — and the recursor of an empty type
    /// over an inhabited one proves False. Lean cannot express the discrepancy:
    /// its `inductive_type` carries its constructors inline.
    function _checkCtorWindows(M memory m, uint256[] calldata declTab, G memory g) internal pure {
        for (uint256 t = 0; t < g.nT; t++) {
            uint256 ptr = (g.indD1[t] >> 96) & F;
            uint256 declared = m.pool[ptr];
            uint256 j = 0;
            // Walk the block's constructors in declaration order; those
            // belonging to this type must be exactly the window, position for
            // position. Cardinality plus membership is NOT enough: a window
            // repeating one constructor would satisfy both while silently
            // dropping another, which is the same soundness hole reached by a
            // different lie. This demands a bijection.
            for (uint256 c = 0; c < g.nC; c++) {
                uint256 cd0 = declTab[2 * (g.base + g.nT + c)];
                uint256 cd1 = declTab[2 * (g.base + g.nT + c) + 1];
                if (m.nameHash[cd1 & F] != g.indHashes[t]) continue;
                if (j >= declared || m.nameHash[m.pool[ptr + 1 + j]] != m.nameHash[_dName(cd0)]) {
                    _setFail(m, V_REJECT, R_IND_SHAPE);
                    return;
                }
                j++;
            }
            if (j != declared) {
                _setFail(m, V_REJECT, R_IND_SHAPE);
                return;
            }
        }
    }

    /// Lean *computes* `is_rec` (inductive.cpp:265) — a block is recursive when
    /// some constructor has a field whose type mentions a member — and stores
    /// one block-wide value on every type. We must not trust the exported flag:
    /// it gates structure eta, unit eta and `_toCtorWhenStructure`, so a forged
    /// `isRec: false` on a recursive type would let eta equate a variable with
    /// its own unfolding. Overwrite the registered bit with the computed value.
    function _recomputeIsRec(M memory m, uint256[] calldata declTab, G memory g) internal pure {
        bool rec_;
        for (uint256 c = 0; c < g.nC && !rec_; c++) {
            uint256 cd0 = declTab[2 * (g.base + g.nT + c)];
            uint256 cd1 = declTab[2 * (g.base + g.nT + c) + 1];
            uint256 np = (cd1 >> 96) & F;
            uint256 nf = (cd1 >> 144) & F;
            uint256 cur = _dType(cd0);
            for (uint256 k = 0; k < np && _tag(m, cur) == E_PI; k++) cur = _b(m, cur);
            for (uint256 k = 0; k < nf && !rec_ && _tag(m, cur) == E_PI; k++) {
                if (_hasIndOcc(m, _a(m, cur), g.indHashes)) rec_ = true;
                cur = _b(m, cur);
            }
        }
        for (uint256 t = 0; t < g.nT; t++) {
            uint256 slot = _envLookup(m, _dName(g.indD0[t]));
            if (slot == 0) continue;
            uint256 w = m.envDecl1[slot - 1] & ~(uint256(1) << 192);
            if (rec_) w |= (uint256(1) << 192);
            m.envDecl1[slot - 1] = w;
            g.indD1[t] = (g.indD1[t] & ~(uint256(1) << 192)) | (rec_ ? (uint256(1) << 192) : 0);
        }
    }

    function _checkGroupCtor(
        M memory m,
        uint256[] calldata declTab,
        G memory g,
        uint256[] memory indLevels,
        uint256 ci
    ) internal pure returns (bool elimOk) {
        CtorCtx memory cc;
        cc.d0 = declTab[2 * (g.base + g.nT + ci)];
        cc.d1 = declTab[2 * (g.base + g.nT + ci) + 1];
        if (_dKind(cc.d0) != D_CTOR) {
            _setFail(m, V_REJECT, R_CTOR_SHAPE);
            return false;
        }
        _requireFresh(m, _dName(cc.d0));
        if (m.fail != 0) return false;

        cc.tpos = type(uint256).max;
        {
            bytes32 ih = m.nameHash[cc.d1 & F];
            for (uint256 t = 0; t < g.nT; t++) {
                if (g.indHashes[t] == ih) {
                    cc.tpos = t;
                    break;
                }
            }
        }
        if (cc.tpos == type(uint256).max) {
            _setFail(m, V_REJECT, R_CTOR_SHAPE);
            return false;
        }
        if (!_lpWindowsEq(m, _dLpStart(cc.d0), _dLpLen(cc.d0), _dLpStart(g.indD0[cc.tpos]), _dLpLen(g.indD0[cc.tpos]))) {
            _setFail(m, V_REJECT, R_CTOR_SHAPE);
            return false;
        }
        m.lpStart = _dLpStart(cc.d0);
        m.lpLen = _dLpLen(cc.d0);
        {
            uint256[] memory seen = new uint256[]((m.exLen + 255) / 256 + 1);
            _wfExpr(m, _dType(cc.d0), seen);
        }
        if (m.fail != 0) return false;
        m.ctxLen = 0;
        {
            uint256 tt = _infer(m, _dType(cc.d0));
            if (m.fail != 0) return false;
            tt = _whnf(m, tt);
            if (m.fail != 0) return false;
            if (_tag(m, tt) != E_SORT) {
                _setFail(m, V_REJECT, R_CTOR_SHAPE);
                return false;
            }
        }
        cc.np = (cc.d1 >> 96) & F;
        cc.nf = (cc.d1 >> 144) & F;
        m.ctxLen = 0;
        uint256 cur = _ctorTelescope(m, g, indLevels, cc);
        if (m.fail != 0) return false;
        elimOk = _ctorResult(m, g, cc, cur);
        if (m.fail != 0) return false;
        m.ctxLen = 0;
        _envAdd(m, cc.d0, cc.d1);
    }

    /// Walk constructor params (must match the inductive's) and fields
    /// (positivity + universe bounds); returns the result expression.
    function _ctorTelescope(M memory m, G memory g, uint256[] memory indLevels, CtorCtx memory cc)
        internal
        pure
        returns (uint256 cur)
    {
        cur = _dType(cc.d0);
        uint256 indCur = _dType(g.indD0[cc.tpos]);
        for (uint256 k = 0; k < cc.np; k++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_CTOR_SHAPE);
                return cur;
            }
            indCur = _whnf(m, indCur);
            if (m.fail != 0) return cur;
            if (_tag(m, indCur) != E_PI || !_isDefEq(m, _a(m, cur), _a(m, indCur))) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_CTOR_SHAPE);
                return cur;
            }
            _pushCtx(m, _a(m, indCur));
            cur = _b(m, cur);
            indCur = _b(m, indCur);
        }
        bool indIsProp = _lvlLeq(m, indLevels[cc.tpos], 0);
        for (uint256 j = 0; j < cc.nf; j++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_CTOR_SHAPE);
                return cur;
            }
            _posCheck(m, _a(m, cur), g, j);
            if (m.fail != 0) return cur;
            uint256 fs = _sortOf(m, _a(m, cur));
            if (m.fail != 0) return cur;
            if (_lvlLeq(m, fs, 0)) cc.fieldPropBits |= (1 << j);
            if (!indIsProp && !_lvlLeq(m, fs, indLevels[cc.tpos])) {
                _setFail(m, V_REJECT, R_FIELD_UNIVERSE);
                return cur;
            }
            _pushCtx(m, _a(m, cur));
            cur = _b(m, cur);
        }
    }

    /// Validate the constructor's result type; returns elimination eligibility
    /// of the fields (every non-proof field appears among the result indices).
    function _ctorResult(M memory m, G memory g, CtorCtx memory cc, uint256 cur) internal pure returns (bool elimOk) {
        elimOk = true;
        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST || m.nameHash[_a(m, h)] != g.indHashes[cc.tpos]) {
            _setFail(m, V_REJECT, R_CTOR_RESULT);
            return false;
        }
        {
            uint256 usN = _c(m, h);
            if (usN != m.lpLen) {
                _setFail(m, V_REJECT, R_CTOR_LEVELS);
                return false;
            }
            for (uint256 k = 0; k < usN; k++) {
                uint256 l = m.pool[_b(m, h) + k];
                if (_lt(m, l) != L_PARAM || m.nameHash[_la(m, l)] != m.nameHash[m.pool[m.lpStart + k]]) {
                    _setFail(m, V_REJECT, R_CTOR_LEVELS);
                    return false;
                }
            }
        }
        if (nArgs != cc.np + ((g.indD1[cc.tpos] >> 48) & F)) {
            _setFail(m, V_REJECT, R_CTOR_RESULT);
            return false;
        }
        uint256[] memory args = _collectArgs(m, cur, nArgs);
        for (uint256 k = 0; k < cc.np; k++) {
            if (_tag(m, args[k]) != E_BVAR || _a(m, args[k]) != cc.nf + cc.np - 1 - k) {
                _setFail(m, V_REJECT, R_CTOR_RESULT);
                return false;
            }
        }
        for (uint256 k = cc.np; k < nArgs; k++) {
            if (_hasIndOcc(m, args[k], g.indHashes)) {
                _setFail(m, V_REJECT, R_CTOR_RESULT);
                return false;
            }
        }
        for (uint256 j = 0; j < cc.nf; j++) {
            if ((cc.fieldPropBits >> j) & 1 == 1) continue;
            bool occurs = false;
            for (uint256 k = cc.np; k < nArgs && !occurs; k++) {
                occurs = _hasLooseBVar(m, args[k], cc.nf - 1 - j);
            }
            if (!occurs) elimOk = false;
        }
    }

    function _lpWindowsEq(M memory m, uint256 s1, uint256 n1, uint256 s2, uint256 n2) internal pure returns (bool) {
        if (n1 != n2) return false;
        for (uint256 i = 0; i < n1; i++) {
            if (m.nameHash[m.pool[s1 + i]] != m.nameHash[m.pool[s2 + i]]) return false;
        }
        return true;
    }

    /// Strict positivity for a constructor field type. `depth` = binders below
    /// the group's parameter telescope (for matching aux occurrences).
    function _posCheck(M memory m, uint256 t, G memory g, uint256 depth) internal pure {
        if (m.fail != 0) return;
        if (!_step(m)) return;
        if (!_hasIndOcc(m, t, g.indHashes)) return;
        t = _whnf(m, t);
        if (m.fail != 0) return;
        if (!_hasIndOcc(m, t, g.indHashes)) return;
        if (_tag(m, t) == E_PI) {
            if (_hasIndOcc(m, _a(m, t), g.indHashes)) {
                _setFail(m, V_REJECT, R_POSITIVITY);
                return;
            }
            _posCheck(m, _b(m, t), g, depth + 1);
            return;
        }
        (uint256 h, uint256 nArgs) = _spineHead(m, t);
        if (_tag(m, h) == E_CONST) {
            bytes32 hh = m.nameHash[_a(m, h)];
            for (uint256 i = 0; i < g.indHashes.length; i++) {
                if (g.indHashes[i] == hh) {
                    // valid recursive occurrence: arguments may not mention the group
                    uint256[] memory args = _collectArgs(m, t, nArgs);
                    for (uint256 k = 0; k < nArgs; k++) {
                        if (_hasIndOcc(m, args[k], g.indHashes)) {
                            _setFail(m, V_REJECT, R_POSITIVITY);
                            return;
                        }
                    }
                    return;
                }
            }
            // auxiliary member occurrence I_k Ds_k is: exactly I_k's index
            // count beyond Ds, and no group occurrence in the indices
            uint256 k2 = _auxMatch(m, g, t, h, nArgs, depth);
            if (k2 != type(uint256).max && nArgs == g.auxDs[k2].length + _auxNI(m, g, k2)) {
                uint256[] memory args2 = _collectArgs(m, t, nArgs);
                for (uint256 j = g.auxDs[k2].length; j < nArgs; j++) {
                    if (_hasIndOcc(m, args2[j], g.indHashes)) {
                        _setFail(m, V_REJECT, R_POSITIVITY);
                        return;
                    }
                }
                return;
            }
        }
        _setFail(m, V_REJECT, R_POSITIVITY);
    }

    struct RecCtx {
        uint256 p;
        uint256 i;
        uint256 M_;
        uint256 mm;
        uint256 recLpStart;
        uint256 extra;
        uint256 indLpLen;
        uint256 tpos; // which type of the group this recursor eliminates
    }

    function _checkGroupRec(
        M memory m,
        uint256[] calldata declTab,
        G memory g,
        uint256[] memory indLevels,
        uint256 ri
    ) internal pure {
        uint256 d0 = declTab[2 * (g.base + g.nT + g.nC + ri)];
        uint256 d1 = declTab[2 * (g.base + g.nT + g.nC + ri) + 1];
        if (_dKind(d0) != D_REC) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return;
        }
        uint256 rtpos = _recursorTypePos(m, g, _dName(d0));
        if (rtpos == type(uint256).max) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return;
        }
        _requireFresh(m, _dName(d0));
        _requireLpsDistinct(m, _dLpStart(d0), _dLpLen(d0));
        if (m.fail != 0) return;

        RecCtx memory rc;
        rc.p = d1 & F;
        rc.i = (d1 >> 48) & F;
        rc.M_ = (d1 >> 96) & F;
        rc.mm = (d1 >> 144) & F;
        rc.recLpStart = _dLpStart(d0);
        rc.indLpLen = _dLpLen(g.indD0[0]);
        rc.tpos = rtpos;
        {
            uint256 recLpLen = _dLpLen(d0);
            if (recLpLen < rc.indLpLen || recLpLen - rc.indLpLen > 1) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return;
            }
            rc.extra = recLpLen - rc.indLpLen;
            for (uint256 k = 0; k < rc.indLpLen; k++) {
                if (m.nameHash[m.pool[rc.recLpStart + rc.extra + k]] != m.nameHash[m.pool[_dLpStart(g.indD0[0]) + k]]) {
                    _setFail(m, V_REJECT, R_REC_SHAPE);
                    return;
                }
            }
        }
        // params are shared across the block; indices are per-type, so the
        // recursor's index count must match the type IT eliminates. Motives =
        // one per member of the auxiliary block, minors = one per constructor.
        if (
            rc.p != g.np
                || rc.i != (rc.tpos < g.nT ? (g.indD1[rc.tpos] >> 48) & F : _auxNI(m, g, rc.tpos - g.nT))
                || rc.M_ != g.nT + g.nAux || rc.mm != g.nC + g.nCtorsAux
        ) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return;
        }

        m.lpStart = rc.recLpStart;
        m.lpLen = _dLpLen(d0);
        {
            uint256[] memory seen = new uint256[]((m.exLen + 255) / 256 + 1);
            _wfExpr(m, _dType(d0), seen);
        }
        if (m.fail != 0) return;
        m.ctxLen = 0;
        {
            uint256 tt = _infer(m, _dType(d0));
            if (m.fail != 0) return;
            tt = _whnf(m, tt);
            if (m.fail != 0) return;
            if (_tag(m, tt) != E_SORT) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return;
            }
        }

        // walk the recursor type: params, motives (with elim check), minors
        uint256[] memory binders = new uint256[](rc.p + rc.M_ + rc.mm);
        uint256 recTail;
        {
            uint256 cur = _dType(d0);
            for (uint256 k = 0; k < binders.length; k++) {
                cur = _whnf(m, cur);
                if (m.fail != 0) return;
                if (_tag(m, cur) != E_PI) {
                    _setFail(m, V_REJECT, R_REC_SHAPE);
                    return;
                }
                binders[k] = _a(m, cur);
                if (k >= rc.p && k < rc.p + rc.M_) {
                    _checkMotiveSort(m, g, _a(m, cur), k - rc.p);
                    if (m.fail != 0) return;
                }
                cur = _b(m, cur);
            }
            recTail = cur;
        }
        _checkRecursorTail(m, g, rc, binders, recTail);
        if (m.fail != 0) return;
        _checkRecursorMinors(m, declTab, g, rc, binders);
        if (m.fail != 0) return;

        // K flag validation (never K for a mutual or nested block)
        if ((d1 >> 248) == 1) {
            bool okK = g.nT == 1 && g.nAux == 0 && _lvlLeq(m, indLevels[0], 0) && g.nC <= 1;
            if (okK && g.nC == 1) {
                uint256 cD1 = declTab[2 * (g.base + g.nT) + 1];
                okK = ((cD1 >> 144) & F) == 0;
            }
            if (!okK) {
                _setFail(m, V_REJECT, R_K_FLAG);
                return;
            }
        }

        // Register now; rules are validated in a second pass. In a mutual block
        // a rule's RHS may call a *sibling* recursor (Tree.rec's rule for
        // Tree.node calls Forest.rec), so every recursor of the block must be in
        // the environment before any rule is inferred.
        _envAdd(m, d0, d1);
    }

    /// Second recursor pass: reduction rules, with the whole block registered.
    /// A recursor carries rules for exactly its own type's constructors, even
    /// though it binds minor premises for every constructor in the block.
    function _checkGroupRecRules(M memory m, uint256[] calldata declTab, G memory g, uint256 ri)
        internal
        pure
    {
        uint256 d0 = declTab[2 * (g.base + g.nT + g.nC + ri)];
        uint256 d1 = declTab[2 * (g.base + g.nT + g.nC + ri) + 1];

        RecCtx memory rc;
        rc.p = d1 & F;
        rc.i = (d1 >> 48) & F;
        rc.M_ = (d1 >> 96) & F;
        rc.mm = (d1 >> 144) & F;
        rc.recLpStart = _dLpStart(d0);
        rc.indLpLen = _dLpLen(g.indD0[0]);
        rc.tpos = _recursorTypePos(m, g, _dName(d0));
        rc.extra = _dLpLen(d0) - rc.indLpLen;

        m.lpStart = rc.recLpStart;
        m.lpLen = _dLpLen(d0);

        uint256[] memory binders = new uint256[](rc.p + rc.M_ + rc.mm);
        {
            uint256 cur = _dType(d0);
            for (uint256 k = 0; k < binders.length; k++) {
                cur = _whnf(m, cur);
                if (m.fail != 0) return;
                if (_tag(m, cur) != E_PI) {
                    _setFail(m, V_REJECT, R_REC_SHAPE);
                    return;
                }
                binders[k] = _a(m, cur);
                cur = _b(m, cur);
            }
        }

        uint256 rulesPtr = (d1 >> 192) & F;
        uint256 ownCtors = rc.tpos < g.nT
            ? m.pool[(g.indD1[rc.tpos] >> 96) & F]
            : m.pool[(m.envDecl1[g.auxSlot[rc.tpos - g.nT]] >> 96) & F];
        if (m.pool[rulesPtr] != ownCtors) {
            _setFail(m, V_REJECT, R_REC_RULE);
            return;
        }
        for (uint256 r = 0; r < ownCtors; r++) {
            uint256 nfields = m.pool[rulesPtr + 1 + 3 * r + 1];
            uint256 rhs = m.pool[rulesPtr + 1 + 3 * r + 2];
            uint256 cslot = _envLookup(m, m.pool[rulesPtr + 1 + 3 * r]);
            if (cslot == 0 || _dKind(m.envDecl0[cslot - 1]) != D_CTOR) {
                _setFail(m, V_REJECT, R_REC_RULE);
                return;
            }
            uint256 cd1 = m.envDecl1[cslot - 1];
            if (nfields != ((cd1 >> 144) & F)) {
                _setFail(m, V_REJECT, R_REC_RULE);
                return;
            }
            // The rules must line up with this type's constructor window
            // position for position. Checking only the count lets a window name
            // one constructor twice (leaving another with no ι-rule); checking
            // only injectivity still admits a permutation. Lean derives the
            // rules in constructor order, and all 502 recursors in the Arena
            // corpus agree, so demand the bijection outright.
            {
                uint256 cw = rc.tpos < g.nT
                    ? (g.indD1[rc.tpos] >> 96) & F
                    : (m.envDecl1[g.auxSlot[rc.tpos - g.nT]] >> 96) & F;
                if (m.nameHash[m.pool[cw + 1 + r]] != m.nameHash[m.pool[rulesPtr + 1 + 3 * r]]) {
                    _setFail(m, V_REJECT, R_REC_RULE);
                    return;
                }
            }
            uint256 expected;
            if (rc.tpos < g.nT) {
                uint256 tpos = type(uint256).max;
                {
                    bytes32 ih = m.nameHash[cd1 & F];
                    for (uint256 t = 0; t < g.nT; t++) {
                        if (g.indHashes[t] == ih) {
                            tpos = t;
                            break;
                        }
                    }
                }
                if (tpos != rc.tpos || ((cd1 >> 96) & F) != rc.p) {
                    // a rule for a sibling type's constructor does not belong here
                    _setFail(m, V_REJECT, R_REC_RULE);
                    return;
                }
                expected = _ruleExpected(m, g, rc, binders, cslot, tpos);
            } else {
                // aux recursor: the rule ctor must belong to THIS entry's
                // nesting target (the same head may serve several entries —
                // the expected type below pins the entry's own Ds)
                uint256 k = rc.tpos - g.nT;
                if (
                    m.nameHash[cd1 & F] != m.envHash[g.auxSlot[k]]
                        || ((cd1 >> 96) & F) != g.auxDs[k].length
                ) {
                    _setFail(m, V_REJECT, R_REC_RULE);
                    return;
                }
                expected = _ruleExpectedAux(m, g, rc, binders, cslot - 1, k);
            }
            if (m.fail != 0) return;
            m.ctxLen = 0;
            uint256 vt = _infer(m, rhs);
            if (m.fail != 0) return;
            if (!_isDefEq(m, vt, expected)) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_REC_RULE);
                return;
            }
        }
    }

    /// Which type of the group does this recursor eliminate? Returns the type's
    /// position, or type(uint256).max if the name is not a canonical recursor
    /// name for any member. In a mutual block each type gets its own recursor,
    /// so the position — not just validity — matters: it selects the motive and
    /// the major premise's inductive.
    function _recursorTypePos(M memory m, G memory g, uint256 nameIdx) internal pure returns (uint256) {
        bytes32 h = m.nameHash[nameIdx];
        for (uint256 t = 0; t < g.nT; t++) {
            if (h == keccak256(abi.encodePacked(g.indHashes[t], uint8(0), "rec"))) return t;
        }
        // aux type k's recursor is <types[0]>.rec_{k+1} (always under the
        // FIRST declared type's name, even in a mutual block)
        for (uint256 k = 0; k < g.nAux; k++) {
            if (h == keccak256(abi.encodePacked(g.indHashes[0], uint8(0), "rec_", _decSuffix(k + 1)))) {
                return g.nT + k;
            }
        }
        return type(uint256).max;
    }

    /// Validate the recursor declaration's tail after params/motives/minors:
    ///   ∀ indices, major : I params indices, motive indices major
    function _checkRecursorTail(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256[] memory binders,
        uint256 cur
    ) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        for (uint256 k = 0; k < binders.length; k++) _pushCtx(m, binders[k]);

        for (uint256 k = 0; k < rc.i; k++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) {
                m.ctxLen = savedCtx;
                return;
            }
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                m.ctxLen = savedCtx;
                return;
            }
            _pushCtx(m, _a(m, cur));
            cur = _b(m, cur);
        }

        cur = _whnf(m, cur);
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        if (_tag(m, cur) != E_PI) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            m.ctxLen = savedCtx;
            return;
        }

        uint256 expectedMajor = _recursorIndApp(m, g, rc);
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }
        if (!_isDefEq(m, _a(m, cur), expectedMajor)) {
            if (m.fail == 0) _setFail(m, V_REJECT, R_REC_SHAPE);
            m.ctxLen = savedCtx;
            return;
        }

        _pushCtx(m, _a(m, cur));
        cur = _b(m, cur);
        cur = _whnf(m, cur);
        if (m.fail != 0) {
            m.ctxLen = savedCtx;
            return;
        }

        // motive j sits at bvar (indices + minors + M_ - j); this recursor
        // returns its own type's motive, not necessarily the first.
        uint256 expectedResult = _pushEx(m, _mkE(E_BVAR, rc.i + 1 + rc.mm + (rc.M_ - 1 - rc.tpos), 0, 0));
        for (uint256 k = 0; k < rc.i; k++) {
            expectedResult = _pushEx(m, _mkE(E_APP, expectedResult, _pushEx(m, _mkE(E_BVAR, rc.i - k, 0, 0)), 0));
        }
        expectedResult = _pushEx(m, _mkE(E_APP, expectedResult, _pushEx(m, _mkE(E_BVAR, 0, 0, 0)), 0));
        if (!_isDefEq(m, cur, expectedResult) && m.fail == 0) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
        }
        m.ctxLen = savedCtx;
    }

    function _checkRecursorMinors(
        M memory m,
        uint256[] calldata declTab,
        G memory g,
        RecCtx memory rc,
        uint256[] memory binders
    ) internal pure {
        uint256 savedCtx = m.ctxLen;
        m.ctxLen = 0;
        for (uint256 k = 0; k < rc.p + rc.M_; k++) _pushCtx(m, binders[k]);
        for (uint256 r = 0; r < rc.mm; r++) {
            uint256 expected;
            if (r < g.nC) {
                uint256 cd0 = declTab[2 * (g.base + g.nT + r)];
                uint256 cd1 = declTab[2 * (g.base + g.nT + r) + 1];
                uint256 tpos = type(uint256).max;
                {
                    bytes32 ih = m.nameHash[cd1 & F];
                    for (uint256 t = 0; t < g.nT; t++) {
                        if (g.indHashes[t] == ih) {
                            tpos = t;
                            break;
                        }
                    }
                }
                if (tpos == type(uint256).max) {
                    _setFail(m, V_REJECT, R_REC_SHAPE);
                    m.ctxLen = savedCtx;
                    return;
                }
                expected = _minorExpected(m, g, rc, cd0, cd1, tpos, r);
            } else {
                // virtual ctor of an auxiliary type
                expected = _minorExpectedAux(m, g, rc, g.vcAux[r - g.nC], g.vcSlot[r - g.nC], r);
            }
            if (m.fail != 0) {
                m.ctxLen = savedCtx;
                return;
            }
            if (!_isDefEq(m, binders[rc.p + rc.M_ + r], expected)) {
                if (m.fail == 0) _setFail(m, V_REJECT, R_REC_SHAPE);
                m.ctxLen = savedCtx;
                return;
            }
            _pushCtx(m, binders[rc.p + rc.M_ + r]);
        }
        m.ctxLen = savedCtx;
    }

    function _minorExpected(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256 cd0,
        uint256 cd1,
        uint256 tpos,
        uint256 priorMinors
    ) internal pure returns (uint256) {
        uint256 nf = (cd1 >> 144) & F;
        uint256 cur = _dType(cd0);
        for (uint256 k = 0; k < rc.p; k++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) return NONE;
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return NONE;
            }
            cur = _b(m, cur);
        }
        cur = _lift(m, cur, rc.M_ + priorMinors, 0);

        uint256[] memory domains = new uint256[](nf * 2 + 1);
        uint256[] memory fieldTypes = new uint256[](nf);
        uint256[] memory fieldPos = new uint256[](nf);
        uint256 nBinders = 0;
        for (uint256 j = 0; j < nf; j++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) return NONE;
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return NONE;
            }
            uint256 fieldTy = _a(m, cur);
            domains[nBinders] = fieldTy;
            fieldTypes[j] = fieldTy;
            fieldPos[j] = nBinders;
            nBinders++;
            cur = _b(m, cur);
        }

        uint256 nIH = 0;
        for (uint256 j = 0; j < nf; j++) {
            (bool rec, uint256 ihTy) = _ihForField(
                m,
                g,
                rc,
                _lift(m, fieldTypes[j], nf - j + nIH, 0),
                _pushEx(m, _mkE(E_BVAR, nf - 1 - j + nIH, 0, 0)),
                priorMinors,
                nBinders
            );
            if (m.fail != 0) return NONE;
            if (rec) {
                domains[nBinders] = ihTy;
                nBinders++;
                nIH++;
                cur = _lift(m, cur, 1, 0);
            }
        }

        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST || m.nameHash[_a(m, h)] != g.indHashes[tpos]) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return NONE;
        }
        uint256[] memory rargs = _collectArgs(m, cur, nArgs);
        uint256 body = _pushEx(m, _mkE(E_BVAR, nBinders + priorMinors + (rc.M_ - 1 - tpos), 0, 0));
        uint256 ni = (g.indD1[tpos] >> 48) & F;
        for (uint256 k = rc.p; k < rc.p + ni && k < nArgs; k++) {
            body = _pushEx(m, _mkE(E_APP, body, rargs[k], 0));
        }

        uint256 capp = _ctorAppForMinor(m, rc, cd0, nf, nBinders, priorMinors, fieldPos);
        body = _pushEx(m, _mkE(E_APP, body, capp, 0));
        for (uint256 i = nBinders; i > 0; i--) {
            body = _pushEx(m, _mkE(E_PI, domains[i - 1], body, 0));
        }
        return body;
    }

    /// Expected minor premise for a VIRTUAL constructor (ctor `cidx` of the
    /// nesting target, instantiated at aux entry k's levels and Ds):
    ///   ∀ fields, ∀ IHs, motive_{nT+k} idxs (ctor Ds fields)
    function _minorExpectedAux(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256 k,
        uint256 cidx,
        uint256 priorMinors
    ) internal pure returns (uint256) {
        uint256 nf = (m.envDecl1[cidx] >> 144) & F;
        uint256 cur = _instAuxCtorType(m, g, k, cidx, rc.M_ + priorMinors);
        if (m.fail != 0) return NONE;

        uint256[] memory domains = new uint256[](nf * 2 + 1);
        uint256[] memory fieldTypes = new uint256[](nf);
        uint256[] memory fieldPos = new uint256[](nf);
        uint256 nBinders = 0;
        for (uint256 j = 0; j < nf; j++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return NONE;
            }
            domains[nBinders] = _a(m, cur);
            fieldTypes[j] = _a(m, cur);
            fieldPos[j] = nBinders;
            nBinders++;
            cur = _b(m, cur);
        }

        uint256 nIH = 0;
        for (uint256 j = 0; j < nf; j++) {
            (bool rec, uint256 ihTy) = _ihForField(
                m,
                g,
                rc,
                _lift(m, fieldTypes[j], nf - j + nIH, 0),
                _pushEx(m, _mkE(E_BVAR, nf - 1 - j + nIH, 0, 0)),
                priorMinors,
                nBinders
            );
            if (m.fail != 0) return NONE;
            if (rec) {
                domains[nBinders] = ihTy;
                nBinders++;
                nIH++;
                cur = _lift(m, cur, 1, 0);
            }
        }

        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST || m.nameHash[_a(m, h)] != m.envHash[g.auxSlot[k]]) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return NONE;
        }
        uint256[] memory rargs = _collectArgs(m, cur, nArgs);
        uint256 body = _pushEx(m, _mkE(E_BVAR, nBinders + priorMinors + (rc.M_ - 1 - (g.nT + k)), 0, 0));
        {
            uint256 npk = g.auxDs[k].length;
            uint256 ni = _auxNI(m, g, k);
            for (uint256 j = npk; j < npk + ni && j < nArgs; j++) {
                body = _pushEx(m, _mkE(E_APP, body, rargs[j], 0));
            }
        }
        body = _pushEx(
            m, _mkE(E_APP, body, _auxCtorApp(m, g, k, cidx, nf, nBinders, nBinders + priorMinors + rc.M_, fieldPos), 0)
        );
        for (uint256 i = nBinders; i > 0; i--) {
            body = _pushEx(m, _mkE(E_PI, domains[i - 1], body, 0));
        }
        return body;
    }

    /// `ctor.{us_k} Ds_k fields` for a virtual ctor. `dsLift` = binder depth
    /// below the group's params at the application site; field j sits at bvar
    /// nBinders - 1 - fieldPos[j].
    function _auxCtorApp(
        M memory m,
        G memory g,
        uint256 k,
        uint256 cidx,
        uint256 nf,
        uint256 nBinders,
        uint256 dsLift,
        uint256[] memory fieldPos
    ) internal pure returns (uint256 capp) {
        capp = _pushEx(
            m, _mkE(E_CONST, _dName(m.envDecl0[cidx]), g.auxUs[k], _dLpLen(m.envDecl0[g.auxSlot[k]]))
        );
        uint256[] memory ds = g.auxDs[k];
        for (uint256 p = 0; p < ds.length; p++) {
            capp = _pushEx(m, _mkE(E_APP, capp, _lift(m, ds[p], dsLift, 0), 0));
        }
        for (uint256 j = 0; j < nf; j++) {
            capp = _pushEx(m, _mkE(E_APP, capp, _pushEx(m, _mkE(E_BVAR, nBinders - 1 - fieldPos[j], 0, 0)), 0));
        }
    }

    function _ihForField(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256 cur,
        uint256 fieldApp,
        uint256 priorMinors,
        uint256 innerCount
    ) internal pure returns (bool rec, uint256 ihTy) {
        cur = _whnf(m, cur);
        if (m.fail != 0) return (false, NONE);
        if (!_hasIndOcc(m, cur, g.indHashes)) return (false, NONE);
        if (_tag(m, cur) == E_PI) {
            uint256 app = _pushEx(m, _mkE(E_APP, _lift(m, fieldApp, 1, 0), _pushEx(m, _mkE(E_BVAR, 0, 0, 0)), 0));
            (bool subRec, uint256 subTy) = _ihForField(m, g, rc, _b(m, cur), app, priorMinors, innerCount + 1);
            if (m.fail != 0) return (false, NONE);
            if (!subRec) {
                _setFail(m, V_DECLINE, R_UNSUPPORTED);
                return (false, NONE);
            }
            return (true, _pushEx(m, _mkE(E_PI, _a(m, cur), subTy, 0)));
        }
        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST) {
            _setFail(m, V_DECLINE, R_UNSUPPORTED);
            return (false, NONE);
        }
        uint256 tpos = type(uint256).max;
        {
            bytes32 hh = m.nameHash[_a(m, h)];
            for (uint256 t = 0; t < g.nT; t++) {
                if (g.indHashes[t] == hh) {
                    tpos = t;
                    break;
                }
            }
        }
        uint256 pskip = rc.p;
        uint256 ni;
        if (tpos == type(uint256).max) {
            // an aux occurrence I_k Ds_k is: the IH uses motive_{nT+k} and the
            // occurrence's own indices (after its np_k parameter args)
            uint256 k2 = _auxMatch(m, g, cur, h, nArgs, rc.M_ + priorMinors + innerCount);
            if (k2 == type(uint256).max) {
                _setFail(m, V_DECLINE, R_UNSUPPORTED);
                return (false, NONE);
            }
            tpos = g.nT + k2;
            pskip = g.auxDs[k2].length;
            ni = _auxNI(m, g, k2);
        } else {
            ni = (g.indD1[tpos] >> 48) & F;
        }
        uint256[] memory args = _collectArgs(m, cur, nArgs);
        uint256 body = _pushEx(m, _mkE(E_BVAR, innerCount + priorMinors + (rc.M_ - 1 - tpos), 0, 0));
        for (uint256 k = pskip; k < pskip + ni && k < nArgs; k++) {
            body = _pushEx(m, _mkE(E_APP, body, args[k], 0));
        }
        body = _pushEx(m, _mkE(E_APP, body, fieldApp, 0));
        return (true, body);
    }

    function _ctorAppForMinor(
        M memory m,
        RecCtx memory rc,
        uint256 cd0,
        uint256 nf,
        uint256 nBinders,
        uint256 priorMinors,
        uint256[] memory fieldPos
    ) internal pure returns (uint256 capp) {
        uint256 usS = m.poolLen;
        for (uint256 k = 0; k < rc.indLpLen; k++) {
            uint256 lvl = _pushLv(m, _mkL(L_PARAM, m.pool[rc.recLpStart + rc.extra + k], 0));
            _pushPool(m, lvl);
        }
        capp = _pushEx(m, _mkE(E_CONST, _dName(cd0), usS, rc.indLpLen));
        for (uint256 k = 0; k < rc.p; k++) {
            capp = _pushEx(
                m,
                _mkE(E_APP, capp, _pushEx(m, _mkE(E_BVAR, nBinders + priorMinors + rc.M_ + rc.p - 1 - k, 0, 0)), 0)
            );
        }
        for (uint256 j = 0; j < nf; j++) {
            capp = _pushEx(m, _mkE(E_APP, capp, _pushEx(m, _mkE(E_BVAR, nBinders - 1 - fieldPos[j], 0, 0)), 0));
        }
    }

    function _recursorIndApp(M memory m, G memory g, RecCtx memory rc) internal pure returns (uint256 r) {
        if (rc.tpos >= g.nT) {
            // restored aux type: I_k Ds_k, Ds lifted past motives/minors/indices
            r = _auxApp(m, g, rc.tpos - g.nT, m.ctxLen - rc.p);
        } else {
            uint256 usS = m.poolLen;
            for (uint256 k = 0; k < rc.indLpLen; k++) {
                uint256 lvl = _pushLv(m, _mkL(L_PARAM, m.pool[rc.recLpStart + rc.extra + k], 0));
                _pushPool(m, lvl);
            }
            r = _pushEx(m, _mkE(E_CONST, _dName(g.indD0[rc.tpos]), usS, rc.indLpLen));
            for (uint256 k = 0; k < rc.p; k++) {
                r = _pushEx(m, _mkE(E_APP, r, _pushEx(m, _mkE(E_BVAR, m.ctxLen - 1 - k, 0, 0)), 0));
            }
        }
        for (uint256 k = 0; k < rc.i; k++) {
            r = _pushEx(m, _mkE(E_APP, r, _pushEx(m, _mkE(E_BVAR, rc.i - 1 - k, 0, 0)), 0));
        }
    }

    /// The motive for type j: ∀ indices, I params indices → Sort u; extract u
    /// and enforce the elimination restriction.
    function _checkMotiveSort(M memory m, G memory g, uint256 motiveTy, uint256 j) internal pure {
        uint256 ni = j < g.nT ? (g.indD1[j] >> 48) & F : _auxNI(m, g, j - g.nT);
        uint256 cur = motiveTy;
        for (uint256 k = 0; k < ni + 1; k++) {
            cur = _whnf(m, cur);
            if (m.fail != 0) return;
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_SHAPE);
                return;
            }
            cur = _b(m, cur);
        }
        cur = _whnf(m, cur);
        if (m.fail != 0) return;
        if (_tag(m, cur) != E_SORT) {
            _setFail(m, V_REJECT, R_REC_SHAPE);
            return;
        }
        if (g.smallElimOnly && !_lvlLeq(m, _a(m, cur), 0)) {
            _setFail(m, V_REJECT, R_ELIM_UNIVERSE);
        }
    }

    /// Independently reconstruct the type a recursor rule's RHS must have:
    ///   ∀ params motives minors fields, motive idxs (ctor params fields)
    function _ruleExpected(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256[] memory binders,
        uint256 cslot,
        uint256 tpos
    ) internal pure returns (uint256) {
        uint256 cd0 = m.envDecl0[cslot - 1];
        uint256 nf = (m.envDecl1[cslot - 1] >> 144) & F;
        uint256 cur = _dType(cd0);
        for (uint256 k = 0; k < rc.p; k++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_RULE);
                return NONE;
            }
            cur = _b(m, cur);
        }
        cur = _lift(m, cur, rc.M_ + rc.mm, 0);
        uint256[] memory fb = new uint256[](nf);
        for (uint256 j = 0; j < nf; j++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_RULE);
                return NONE;
            }
            fb[j] = _a(m, cur);
            cur = _b(m, cur);
        }
        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST) {
            _setFail(m, V_REJECT, R_REC_RULE);
            return NONE;
        }
        uint256[] memory rargs = _collectArgs(m, cur, nArgs);
        // motive applied to the result indices and the constructor application
        uint256 body = _pushEx(m, _mkE(E_BVAR, nf + rc.mm + (rc.M_ - 1 - tpos), 0, 0));
        {
            uint256 ni = (g.indD1[tpos] >> 48) & F;
            for (uint256 k = rc.p; k < rc.p + ni && k < nArgs; k++) {
                body = _pushEx(m, _mkE(E_APP, body, rargs[k], 0));
            }
        }
        {
            // ctor applied at the inductive's level params (suffix of rec's)
            uint256 usN = rc.indLpLen;
            uint256 usS = m.poolLen;
            for (uint256 k = 0; k < usN; k++) {
                uint256 lvl = _pushLv(m, _mkL(L_PARAM, m.pool[rc.recLpStart + rc.extra + k], 0));
                _pushPool(m, lvl);
            }
            uint256 capp = _pushEx(m, _mkE(E_CONST, _dName(cd0), usS, usN));
            for (uint256 k = 0; k < rc.p; k++) {
                capp = _pushEx(m, _mkE(E_APP, capp, _pushEx(m, _mkE(E_BVAR, nf + rc.mm + rc.M_ + rc.p - 1 - k, 0, 0)), 0));
            }
            for (uint256 j = 0; j < nf; j++) {
                capp = _pushEx(m, _mkE(E_APP, capp, _pushEx(m, _mkE(E_BVAR, nf - 1 - j, 0, 0)), 0));
            }
            body = _pushEx(m, _mkE(E_APP, body, capp, 0));
        }
        for (uint256 j = nf; j > 0; j--) {
            body = _pushEx(m, _mkE(E_PI, fb[j - 1], body, 0));
        }
        for (uint256 r = binders.length; r > 0; r--) {
            body = _pushEx(m, _mkE(E_PI, binders[r - 1], body, 0));
        }
        return body;
    }

    /// Expected rule-RHS type for an AUX recursor's rule (ctor `cidx` of the
    /// nesting target at aux entry k's levels and Ds):
    ///   ∀ params motives minors fields, motive_{nT+k} idxs (ctor Ds fields)
    function _ruleExpectedAux(
        M memory m,
        G memory g,
        RecCtx memory rc,
        uint256[] memory binders,
        uint256 cidx,
        uint256 k
    ) internal pure returns (uint256) {
        uint256 nf = (m.envDecl1[cidx] >> 144) & F;
        uint256 cur = _instAuxCtorType(m, g, k, cidx, rc.M_ + rc.mm);
        if (m.fail != 0) return NONE;
        uint256[] memory fb = new uint256[](nf);
        for (uint256 j = 0; j < nf; j++) {
            if (_tag(m, cur) != E_PI) {
                _setFail(m, V_REJECT, R_REC_RULE);
                return NONE;
            }
            fb[j] = _a(m, cur);
            cur = _b(m, cur);
        }
        (uint256 h, uint256 nArgs) = _spineHead(m, cur);
        if (_tag(m, h) != E_CONST || m.nameHash[_a(m, h)] != m.envHash[g.auxSlot[k]]) {
            _setFail(m, V_REJECT, R_REC_RULE);
            return NONE;
        }
        uint256[] memory rargs = _collectArgs(m, cur, nArgs);
        uint256 body = _pushEx(m, _mkE(E_BVAR, nf + rc.mm + (rc.M_ - 1 - (g.nT + k)), 0, 0));
        {
            uint256 npk = g.auxDs[k].length;
            uint256 ni = _auxNI(m, g, k);
            for (uint256 j = npk; j < npk + ni && j < nArgs; j++) {
                body = _pushEx(m, _mkE(E_APP, body, rargs[j], 0));
            }
        }
        {
            uint256[] memory fieldPos = new uint256[](nf);
            for (uint256 j = 0; j < nf; j++) fieldPos[j] = j;
            body = _pushEx(
                m, _mkE(E_APP, body, _auxCtorApp(m, g, k, cidx, nf, nf, nf + rc.mm + rc.M_, fieldPos), 0)
            );
        }
        for (uint256 j = nf; j > 0; j--) {
            body = _pushEx(m, _mkE(E_PI, fb[j - 1], body, 0));
        }
        for (uint256 r = binders.length; r > 0; r--) {
            body = _pushEx(m, _mkE(E_PI, binders[r - 1], body, 0));
        }
        return body;
    }
}
