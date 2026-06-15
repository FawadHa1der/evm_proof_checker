# Running Lean Kernel Arena tests against evmlean

The [Lean Kernel Arena](https://arena.lean-lang.org/) drives every checker the
same way: it hands the checker a [lean4export NDJSON](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md)
file via the `$IN` environment variable and reads the exit code:
**0 = accept, 1 = reject, 2 = decline (out of scope), anything else = checker bug.**
`bin/evmlean.js` implements exactly this contract, with the actual checking
performed by the `LeanKernel` Solidity contract inside an in-process EVM.

## Route A — the bundled suite (zero setup)

The repo ships 65 generated tutorial-parity vectors plus the Arena's five
hand-crafted adversarial soundness tests (real files from the
[lean-kernel-arena repo](https://github.com/leanprover/lean-kernel-arena/tree/master/tests):
`constlevels`, `level-imax-leq`, `level-imax-normalization`, `nat-rec-rules`,
`large-elim-param` — each a proof of `False` exploiting a historical kernel bug):

```bash
npm install
npm run gen     # regenerate tests/good|bad|decline
npm test        # compile + run all 70 in a local EVM, with gas report
```

Run any single export through the Arena-style entry point:

```bash
node bin/evmlean.js tests/arena/nat-rec-rules.ndjson ; echo "exit=$?"   # → 1 (reject)
IN=tests/good/053_quot.ndjson node bin/evmlean.js    ; echo "exit=$?"   # → 0 (accept)
```

To re-download the static Arena files (e.g. after upstream adds new ones, or
because you don't trust the bundled copies):

```bash
bash tools/fetch-arena-tests.sh && npm test
```

## Route B — the Arena's own test set

Most Arena tests (`tutorial/*`, `bogus1`, `proj-of-prop`, `std`, `mathlib`, …)
are *generated* from Lean sources by the Arena's tooling, so they need a Lean
toolchain. Two options:

**B1. Download the test zip.** The Arena website offers a zip of all test
exports excluding the giant ones (see the [Arena README](https://github.com/leanprover/lean-kernel-arena)
— "On the arena website you can download a zipfile with the arena tests").
Then simply:

```bash
unzip arena-tests.zip -d arena-tests
for f in $(find arena-tests -name '*.ndjson' | sort); do
  node bin/evmlean.js "$f"; echo "$f → exit $?"
done
```

**B2. Run the official harness (`lka.py`).** This is how the leaderboard
itself is produced:

```bash
git clone https://github.com/leanprover/lean-kernel-arena && cd lean-kernel-arena
# deps: uv (https://docs.astral.sh/uv/), elan, rustc/cargo, GNU time
#   — or just `nix develop` if you use Nix
uv run lka.py build-test          # builds the test exports (downloads Lean toolchains)
uv run lka.py build-checker       # builds the registered checkers
uv run lka.py run                 # runs checkers × tests
uv run lka.py build-site && python3 -m http.server 8880 --directory _out
```

`build-test`, `build-checker` and `run` accept specific test/checker names to
limit the work (check `uv run lka.py --help`); building *everything* includes
multi-GB mathlib exports you probably don't want locally.

To register evmlean as a checker in your local Arena clone, copy
`arena/evmlean.yaml` into `lean-kernel-arena/checkers/` and edit `url`/`rev`
to point at your published copy of this repo (the Arena builds checkers from
git). The yaml's contract is just:

```yaml
build: npm install --no-audit --no-fund && node tools/build.js
run: node bin/evmlean.js $IN
```

Upstream submission is the same file as a PR to `leanprover/lean-kernel-arena`
(see "Contributing Checkers" in their README; maintainers ask for pinned
revisions and good-faith behavior — checkers are not sandboxed).

## Route C — make your own test from any Lean file

```bash
git clone https://github.com/leanprover/lean4export && cd lean4export
lake build
cd /path/to/your/lean/project
lake env /path/to/lean4export/.lake/build/bin/lean4export YourModule -- yourTheorem > out.ndjson
node /path/to/this/repo/bin/evmlean.js out.ndjson
```

(Keep lean4export's toolchain in sync with your project's `lean-toolchain`;
the export format is versioned and still evolving — evmlean declines major
versions it doesn't recognize.)

## What to expect today

| Test class | Expected result |
|---|---|
| Arena static adversarial 5 (constlevels, level-imax-leq, level-imax-normalization, nat-rec-rules, large-elim-param) | **reject — all pass, at exactly the poisoned declaration** |
| Tutorial-ladder material: defs/theorems, universe algebra, δβζ, defeq, lets, Church-numeral Peano, inductives, recursors+ι, rule K, projections, structure/unit eta, proof irrelevance, function eta, Nat literals, quotients | accept/reject correctly (70/70 in the bundled mirror suite) |
| Nested inductives (`numNested > 0`), unsafe/partial declarations, String-literal *reduction* | decline (exit 2) — honest out-of-fragment verdicts |
| Mutual inductive blocks | implemented but lightly tested — treat as experimental |
| Multi-hundred-MB exports (std, mathlib, init) | impractical in an EVM today: expect step-limit/garbage-collection walls long before completion (decline/error). That's the expected placement for this checker — see PLAN.md §6/§7 for the multi-tx and zkVM routes to scale |

Gas intuition from the bundled runs: ~160k gas for a trivial def, 2.5–3M for
Church-numeral arithmetic, 6.3M for all 24 prelude-style declarations of
`constlevels` (False/True/Bool/Eq + Eq.symm + false_ne_true + casesOn), 6.5M
for the quotient test — every single test fits within one post-Fusaka mainnet
transaction (16.77M cap).

## On-chain variants

Anything the local runner does can be replayed against a deployed kernel:

```bash
# local node with a raised code-size limit (kernel is 29.5KB — Glamsterdam-class):
anvil --code-size-limit 65536
RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=<anvil key> node scripts/deploy.js
KERNEL=0x... node scripts/check-onchain.js tests/arena/level-imax-leq.ndjson
# record an accepted export permanently:
KERNEL=0x... REGISTRY=0x... PRIVATE_KEY=... SUBMIT=1 node scripts/check-onchain.js tests/good/048_eqRuleK.ndjson
```

On public chains: today's L1 enforces EIP-170 (24,576 B), so the single-contract
kernel waits on EIP-7907 (Glamsterdam) — until then use a devnet/L2 with a
raised code-size limit, or the library-split build planned in PLAN.md §8 (M4).
