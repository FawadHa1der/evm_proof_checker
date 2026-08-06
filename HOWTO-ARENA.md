# Running Lean Kernel Arena tests against evmlean

The [Lean Kernel Arena](https://arena.lean-lang.org/) drives every checker the
same way: it hands the checker a [lean4export NDJSON](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md)
file via the `$IN` environment variable and reads the exit code:
**0 = accept, 1 = reject, 2 = decline (out of scope), anything else = checker bug.**
`bin/evmlean.js` implements exactly this contract, with the actual checking
performed by the `LeanKernel` Solidity contract inside an in-process EVM.

## Route A — the bundled suite (zero setup)

The repo ships 94 generated tutorial-parity/regression vectors plus 29 byte-real
`lean4export` fixtures under `tests/nested/` and `tests/lean/` (12 of them adversarial
soundness regressions from a red-team audit), plus the Arena's five
hand-crafted adversarial soundness tests (real files from the
[lean-kernel-arena repo](https://github.com/leanprover/lean-kernel-arena/tree/master/tests):
`constlevels`, `level-imax-leq`, `level-imax-normalization`, `nat-rec-rules`,
`large-elim-param` — each a proof of `False` exploiting a historical kernel bug):

```bash
npm install
npm run gen     # regenerate tests/good|bad|decline
npm test        # compile + run all 128 in a local EVM, with gas report
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

**B1. Download the test tarball.** The Arena website offers
`lean-arena-tests.tar.gz` for generated exports under 10 MB; as of
2026-06-15 it contains 97 good and 49 bad files. Then run the byte-real
exports through the single-VM harness:

```bash
curl -fsSL https://arena.lean-lang.org/lean-arena-tests.tar.gz -o /tmp/lean-arena-tests.tar.gz
mkdir -p /tmp/lean-arena-tests
tar -xzf /tmp/lean-arena-tests.tar.gz -C /tmp/lean-arena-tests

# Acceptance criterion for M1: byte-real tutorial parity.
node tools/run-arena-tests.js /tmp/lean-arena-tests --tutorial

# Submission-shaped check for the downloadable tarball: run every export that
# fits the single-transaction guard, and count the same explicit size declines
# that bin/evmlean.js will report to the Arena.
node tools/run-arena-tests.js /tmp/lean-arena-tests --entrypoint-max-bytes=128000 --allow-non-tutorial-decline
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
| Tutorial-ladder material: defs/theorems, universe algebra, δβζ, defeq, lets, Church-numeral Peano, inductives, recursors+ι, rule K, projections, structure/unit eta, proof irrelevance, function eta, Nat literals, quotients | accept/reject correctly (128/128 bundled; see README for the full-corpus figure) |
| Nested inductives (`numNested > 0`), multi-type mutual blocks, String-literal *reduction*, Nat-literal arithmetic | **checked** — accept/reject on the merits |
| unsafe/partial declarations | decline (exit 2) — a deliberate reading for a proof checker |
| Large perf/init/std/mathlib exports | `bin/evmlean.js` declines files above `EVMLEAN_MAX_BYTES` (default 128000). That's the expected placement for this checker — see PLAN.md §6/§7 for the multi-tx and zkVM routes to scale |

Gas intuition from the bundled runs: ~160k gas for a trivial def, 3.0M for
Church-numeral arithmetic, 6.3M for all 24 prelude-style declarations of
`constlevels` (False/True/Bool/Eq + Eq.symm + false_ne_true + casesOn), 6.8M
for the quotient test — 119 of the 128 tests fit within one post-Fusaka mainnet
transaction (16.77M cap); the seven byte-real lean4export fixtures (17.5–40.4M) do not.

## On-chain variants

Anything the local runner does can be replayed against a deployed kernel:

```bash
# local node with a raised code-size limit (kernel is 58.0KB — Glamsterdam-class):
anvil --code-size-limit 65536
ALLOW_EIP7907=1 RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=<anvil key> node scripts/deploy.js
KERNEL=0x... node scripts/check-onchain.js tests/arena/level-imax-leq.ndjson
# record an accepted export permanently:
KERNEL=0x... REGISTRY=0x... PRIVATE_KEY=... SUBMIT=1 node scripts/check-onchain.js tests/good/048_eqRuleK.ndjson
```

On public chains: today's L1 enforces EIP-170 (24,576 B), so the single-contract
kernel waits on EIP-7907 (Glamsterdam) — until then use a devnet/L2 with a
raised code-size limit, or the library-split build planned in PLAN.md §8 (M4).
