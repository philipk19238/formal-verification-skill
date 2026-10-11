---
name: formal-verification
description: Verify concurrency protocols with TLA+ (TLC) and pure logic with Lean 4, always on remote containers, never on the laptop. Use when asked to formalize, model-check, prove, or "verify the state machine", or when a bug is intermittent, ordering-dependent, or "stuck until refresh". Covers picking what to model, a fast-tier/full-tier loop with recall checks, parallel workflows, and closing the gap to real code.
---

# Formal verification (TLA+ and Lean)

Every TLC and Lean run goes through `scripts/formal`, which runs on Modal (8 CPU, 16 GB per check, up to 100 in parallel). Never start `java` or `lean`/`lake` locally. Local TLC once ran 12 JVMs at the same time and made the laptop unusable.

```bash
F=~/.claude/skills/formal-verification/scripts/formal
$F check Spec.tla                 # every cfg/*.cfg and ./*.cfg in parallel, checked against its expectation (fast tier)
$F check Spec.tla --tier full     # only the expensive cfgs; --tier all runs everything
$F check Spec.tla cfg/A.cfg -- -deadlock          # chosen cfgs, extra TLC args after --
$F check Spec.tla cfg/Bug-X.cfg -- -workers 1     # shortest counterexample (BFS with one worker)
$F tlc -config X.cfg Spec.tla     # one raw TLC run, streamed; counterexample files copied back
$F lean                           # lake build (default targets) or `lean` on every file if there is no lakefile
$F lean Demo.Basic                # one lake target
$F lean --freeze                  # record theorem statements + definition bodies in <File>.statements (sorry allowed)
$F mutate Spec.mutations          # plant each listed bug in a copy of Spec.tla (or Spec.lean); its property must fail
$F trace traces/Bug-X.txt         # a TLC log reduced to what each step changed (check writes traces/<cfg>.trace.txt itself)
$F deploy                         # after editing formal.py
```

Put this line in every agent brief that touches TLA+ or Lean:

> Run TLC and Lean only through `~/.claude/skills/formal-verification/scripts/formal` (`check`, `tlc`, `lean`, `mutate`). Never start java, lean or lake locally.

## 1. Pick problems that are cheap to verify

Verify where a short model can catch a bug that tests miss. Rank candidates by **bug likelihood × how small the model can be**.

Good targets (minutes to model, seconds to check):
- **Several actors sharing state over unreliable delivery**, such as pub/sub, websockets, retries, reconnects, leases, locks, CAS, idempotency keys, at-most-once and at-least-once delivery, sequence numbers with gaps, resync barriers, and Temporal signals racing activities.
- **Timers racing events**, such as a heartbeat against a done event, a watchdog against a late delta, or a debounce against a cancel.
- **"Ordering is assumed" code**: "send hello after subscribe", "flush before close", "last writer wins".
- **Bug reports with these symptoms**: intermittent, "sometimes stuck", "fixed by refresh", "only under load", "duplicate", "lost".
- **Search to find them:** `rg` for `asyncio.Lock`, `Condition`, `Event`, `create_task`, `gather`, `CancelledError`, `wait_for`, `SET NX`, `WATCH`, `xadd`, `publish`, `setTimeout`, `AbortController`, `onclose`, `reconnect`, and state names like `pending`, `inflight`, `done`, `closed`, `cursor`, `seq`, `epoch`. Classify each hit; leave library-owned queues and executors alone and model the calling code.
- **A fix that adds a flag, guard, epoch, or retry.** Model it to check that the guard is both needed and enough.
- **For Lean**, pure deterministic logic with an algebraic contract:
  - routing and pattern overlap;
  - order independence;
  - batch == sequential fold;
  - parse/print round-trip;
  - cursor and index arithmetic;
  - "compaction preserves X".

Poor targets: UI layout, performance numbers, LLM behaviour, single-threaded CRUD, and code whose difficulty is data volume or I/O rather than interleaving. Use tests or a harness for those.

Triage, done quickly:
1. List the state machines. For each, name the actors, the shared state and the messages, and point to the code (`file:line`).
2. Write the property as one line, for example `content shown is always a prefix of content sent` or `a finished run is eventually idle`. If it doesn't fit on one line, the machine is too big; split it.
3. Estimate the size: about 2–4 actors, values per variable of 3 or fewer, and fewer than about 150 lines of TLA. Above that, cut detail until the property still means something.
4. Start with the machines that have the highest risk and the smallest models. Compose machines (for example producer × channel × client) only after each one holds on its own.

## 2. Work in parallel

The machines are independent. Model and check them concurrently, never one after another.

Use the Workflow tool when it is available. Invoking this skill counts as opt-in. Otherwise spawn parallel Agent subagents. All agents run on Opus. The shape:

```
Discover  (1 agent, or do it inline)  -> list of machines with code pointers + one-line properties
Model     (pipeline, 1 agent / machine) -> spec + cfgs with expectations + .mutations, fast tier green, `formal mutate` all DETECTED
Verify    (per violation)             -> reproduce in real code (e2e or harness) or mark as a model artifact
Fix       (main loop)                 -> code fix + the spec's fixed variant must hold
Full tier (once, at the end)          -> `formal check --tier full` on every spec
```

- Use `pipeline()` so that a machine that finishes modelling goes straight to verification.
- Each agent works in its own folder (`<root>/NN-<machine>/`) and writes nowhere else.
- Modal handles the parallel load. Agents don't need to coordinate their TLC runs.
- Agents return structured results: machine, property, verdict, state count, counterexample summary, code pointer, and real-or-artifact.
- Agents don't run lint or unit suites. They verify with `formal check` and a repro.

Keep spec folders out of `/tmp`, because macOS reaps old files there. Use `~/workspace/formal/<topic>/` or the branch. Spec folders are uploaded, so they hold abstract models only: no source code, secrets or customer data.

## 3. The loop: fast tier for speed, recall checks for trust

Every cfg starts with a header line (a TLA comment):

```
\* expect: holds | violated <PropertyName> | deadlock
\* tier: fast | full          (default fast)
```

`formal check` runs every cfg in parallel and prints `ok`/`FAIL` against its expectation. It exits 0 only if every result matched. A test cfg that should fail is just as important as one that should hold.

Each spec ships these cfgs:

| cfg | expect | tier | purpose |
|---|---|---|---|
| `Verified` | holds | fast | every safety invariant together, at small constants |
| `Witness-<Situation>` | violated `Not<Situation>` | fast | **vacuity guard**: proves the dangerous situation is reachable (for example `NotGapDuringResync == ~(gap /\ resyncInFlight)`). If this holds, the safety result above means nothing. |
| `Ablate-<Guard>` | violated `<Invariant>` | fast | **recall check**: turn one protection off with a constant switch (`AtomicCas = FALSE`). The model must catch the bug the guard exists for; if not, the model or the bounds are too weak. |
| `Bug-<Name>` | violated `<Invariant>` | fast | the shipped (pre-fix) behaviour, which reproduces the reported bug |
| `Live-<Property>` | holds | fast | liveness at the **smallest constants that still express the scenario** |
| `Full-*` | holds | full | the same properties at larger constants. Run once at the end, not per edit. |

Rules:
- **Iterate on the fast tier only.** It should finish in about a minute. If a fast cfg takes longer, shrink its constants and move the big version to `full`.
- **Size constants to a written scenario, not to "small".** Write down the worst interleaving you care about, for example "a second delta lost while the first resync is in flight, then a reconnect". Pick the smallest constants that can express it, and add a Witness cfg proving it is reachable.
- **Keep one property per expected-violation cfg**, so the expectation is exact. Safety cfgs that should hold can list all invariants together; one exploration checks them all.
- **Switch guards with constants, never by editing the spec.** Ablations are cfg constants (or a scratch copy of the spec). Never test an ablation by mutating production code.
- **Run the full tier once, at the end.** Report its state counts next to the fast tier's.

### Mutations: every property must be able to fail

`Ablate-` cfgs prove the guards you added are load-bearing. A `<Spec>.mutations` file beside the spec covers the plausible bugs that have no switch: `while` → `if`, a missing broadcast or resync, FIFO → LIFO, a flag never cleared, an item taken but not removed, `<` → `≤`. Each mutation replaces exact text in a temporary copy of the spec, so the spec never carries the bug. Write mutations in the code's terms; each one should be a bug someone could plausibly ship.

```
# a line starting with # is a comment; no trailing comments on directive lines
mutation resync forgets the gap
detects NoLostDelta
- /\ gap' = FALSE
+ /\ gap' = gap

mutation reconnect never subscribes
detects witness:Witness-GapDuringResync
cfg Witness-GapDuringResync
-        /\ subscribed' = TRUE
+        /\ subscribed' = subscribed
```

- `mutation <label>` names the bug; `detects <Property>` is the invariant or property that must now fail; `detects witness:<cfg>` means that Witness cfg must now hold (the situation became unreachable).
- `- ` lines are text that must occur exactly once in the spec (consecutive `- ` lines form one block, indentation included); `+ ` lines replace it, and no `+ ` lines deletes it. `cfg <stem>...` optionally limits the cfgs used.

`formal mutate Spec.mutations` runs every mutant in parallel on Modal. For `detects P` it reruns each `expect: holds` cfg of the tier that checks `P`, with only `P` checked (and `-deadlock` for an invariant, so a deadlock elsewhere can't mask it). It prints `DETECTED`, `MISSED` or `ERROR` per mutation, then `UNCOVERED` for each invariant or property of a holds cfg that no mutation and no `Ablate-`/`Bug-` cfg targets. It exits 0 only when every mutation is detected and nothing is uncovered.
- A `MISSED` mutation means the property is too weak, the bounds too small, or the mutation harmless. Fix the property or the bounds; drop the mutation only if it is really harmless.
- Run mutations once the fast tier is green, and again after any property is rewritten. Report the `SUMMARY` line with the check results.
- Mutant logs go to `traces/mutants/`. Mutant runs copy no trace files back.

### Liveness is the expensive part

Measured on 2026-10-07: TLC checks safety at about 0.5–1.3M distinct states per minute with 8 workers. Liveness checking is mostly single-threaded and runs about 10–15× slower (788k states took 627 s, while 3.9M safety states took 46 s). A 4M-state liveness cfg took 26 min.
- Keep liveness models much smaller than safety models. Run liveness in its own cfgs; never add `PROPERTIES` to `Verified`.
- **Bounded counters can make liveness vacuous.** When the sequence, retry or budget counter hits its cap, every behaviour stops, so "eventually X" can hold only because nothing else can happen. A real livelock needs room to cycle. Add an `Ablate-` cfg that removes the progress mechanism (for example the gap timer); liveness must then fail. Known cases:
  - `drain` was vacuous at K=2 and needs K≥3;
  - `Budget=1` could not reach a multi-section edit.
- **Put fairness only on the actions the property needs** (delivery, the resync timer). Fairness on everything inflates the behaviour graph and can assume the progress you are trying to prove. A `Terminates` property holds only if every fair action is bounded.
- For long behaviours, run simulation first: `formal tlc -simulate num=200000 -depth 100 -config Live-X.cfg Spec.tla`. It isn't exhaustive, but it finds livelocks that a tight exhaustive bound cuts off.
- `SYMMETRY` cuts safety state spaces a lot, but TLC's liveness checking is unsound under symmetry. Never use it in `Live-` cfgs.

## 4. Writing the TLA+ model

- **Model the code as it is, with a pointer for each action.** Put a comment on every action naming the code it stands for (`\* ChatSocketContextProvider.tsx handleMessageDelta`). The spec mirrors the code; it is not an idealised protocol. Model the fix as a constant switch so `Bug-` and `Verified` share one spec.
- Use one variable per real piece of state: Redis keys, in-memory buffers, sockets, client refs. Model channels as sequences (FIFO) or bags (unordered), matching the real transport. Model loss as an explicit `Drop` action bounded by a constant.
- `TypeOK` comes first in every invariant list.
- **Let the caller do anything it can do.** The consumer may call, stop calling, cancel or close from any idle point: before the first event, after the last, and after an error. Inject failures with a constant set (`FailAt = {1, 3}`) so a failure can hit any step, not one hand-picked step.
- **Track ownership when resources move.** For buffers, slots, leases or subscriptions, add an invariant that each one is free, held by exactly one actor, or in exactly one queue, plus "no leak at closed".
- **Waits:** model an `await`/condition wait as a program-counter value that only a notify (or a spurious wakeup, with no fairness) can leave, and reread the state after waking. A lost wakeup then shows as a liveness violation, not a TLC deadlock, so a wait needs a `Live-` cfg.
- **Exceptions and cancellation are exits too.** An `await` is where `CancelledError`, a timeout or an exception can leave a multi-step update half done (one Redis key written, the other not; a lock or lease held; a buffer taken but not returned). Give each such step a failure branch that keeps the half-done state, and check that cleanup (`finally`, `__aexit__`, a TTL) restores the ownership invariant.
- **Keep `UNCHANGED` short.** Group each actor's variables (`server == <<seq, buf>>`) and list the untouched groups, not every variable.
- Compose machines with an `INSTANCE` per machine, or by sharing variables, only after each holds alone.
- **Counterexamples:** with 8 workers, the first trace found isn't always the shortest, and its depth varies between runs. Compare trace shapes, not depths. To get the shortest trace, rerun that one cfg with `formal check Spec.tla cfg/X.cfg -- -workers 1` (BFS with one worker reports a shortest path to a safety violation; the runner accepts `-workers` 1 to 8). Trace files `*_TTrace_*.tla` are copied back.
- **Read the reduced trace, not the raw log.** `formal check` writes `traces/<cfg>.trace.txt` for every run that has a counterexample (one block per state: the action, then only the variables that changed) and prints it under each `FAIL`. `formal trace <log>` does the same for any TLC log. Don't write per-spec trace summarisers. Map each step to a code event and `file:line`.
- **How `formal check` reads a run** (exit code first, then the log):
  - `holds` only on exit 0 with `Model checking completed. No error has been found.`;
  - 11 `deadlock`; 12 `violated <Name>` for an invariant or a `[]P` property (TLC prints it as `Invariant P is violated`); 13 `violated <Name>` for a temporal property (`Temporal property P was violated`), an action property, or a property false in the initial state; 14 `violated Assert`;
  - everything else is `error exit <code>`: 10 an `ASSUME` is false, 150 parse or semantic error, 151 cfg error, out of memory or disk, a container lost mid-run, or a log with no completion line. `error` is never a valid expectation.

## 5. Lean

- **Use Lean for pure functions with a clean contract. Prove the property and a counterexample.** Next to `foo_sound`, prove that the old or naive version fails (`old_overlaps_unsound`, `naive_loses_enter`). That is Lean's recall check: it shows the theorem has teeth and that the guard is load-bearing.
- **The gate is `formal lean`.** It fails on errors, on any `sorry`, and on axioms outside `propext`, `Quot.sound` and `Classical.choice`. In a Lake project it audits every declaration of every module it built, so `native_decide` (`Lean.ofReduceBool`) or a declared `axiom` fails even without `#print axioms`. Keep `#print axioms Name` after headline theorems for readers, and because a project with no lakefile is not audited. A whole-project `formal lean` (no targets) fails with `UNBUILT X.lean` when no default target builds a source file, because that file was never checked; add it to a default `lean_lib` or move it out. With explicit targets, unbuilt files only get a `note:`.
- **Freeze the statements before proving.** Write the definitions (transcribed from the code) and every theorem statement with `sorry`, then run `formal lean --freeze`. It records each declaration's type and each non-instance definition's body in `<File>.statements` beside the source. Later `formal lean` runs fail with `FROZEN <name>: statement changed` if a theorem was weakened, a definition was edited to make a proof go through, or a frozen declaration was deleted. Changing proofs and adding lemmas is fine. Re-freeze only when the code changed, a differential test showed the transcription wrong, or after reviewing a toolchain bump, and say why in the report. This is the guard against an agent proving an easier theorem than the one asked.
- **Search before you prove.** Before a proof, add a bounded exhaustive check with `#guard` (for example, no state up to n=6 where one step breaks the invariant), and a `#guard` that a bounded search from the initial state reaches the boundary state the property is about (a full window, a gap). Set the bound above the code's real constants. A failing `#guard` gives concrete inputs for a unit test; a reach `#guard` is Lean's Witness cfg.
- **Mutate the model.** A `<File>.mutations` beside `<File>.lean` (same syntax as for TLA+; `detects <TheoremName>` is optional) plants `<`→`≤`, a missing `+ 1`, or swapped arguments. `formal mutate Model/X.mutations` (run from the project root) builds the project once, then elaborates each mutant on its own, and reports the theorems and `#guard`s that fail. A mutant that breaks a `def` is an `ERROR`, not a detection.
- **Toolchain:** a `lean-toolchain` file pins the version (the current local one is `leanprover/lean4:v4.34.1`). Without one, `stable` is used. Toolchains and `.lake` builds are cached in a Modal volume keyed by the folder name, so keep project folder names unique.
- Avoid mathlib unless you need it; core Lean is enough for most protocol and data-structure proofs. If you use it, the first build fetches its cache (minutes); later builds take seconds.
- Gotchas:
  - core Lean has no `List.swap`;
  - `if_pos`, `if_true` and `if_false` are deprecated, so use `simp` with the hypothesis;
  - build single targets while iterating.
- **State the abstraction's premises as a pytest.** If the proof assumes "at most one remainder segment", add a test that every installed pattern fits (`test_installed_patterns_fit_the_routing_proof`). Otherwise code drift silently breaks the proof's relevance.

## 6. Closing the gap to the real code

A proof covers the model, not the code. Every finding ends in the real system:
- **A violation is a hypothesis until it is reproduced.** Reproduce it in the real stack: an e2e harness or a focused test that forces the interleaving with events and barriers, never sleeps. Show the repro failing before the fix and passing after it. If it can't be reproduced, label it a model artifact and fix the model.
- **Differential oracle (Lean):** at minimum, end the model with an `#eval` that prints one `VECTOR` line per boundary and in-range input (inputs and the model's outputs), and compare those with the production function in a pytest. Claim that a proof describes the code only after they agree, and give the agreement count; otherwise say the comparison was not run. For more coverage, compile the Lean model into an executable and compare it with the Python implementation on thousands of generated inputs. Plant mutations; the harness must catch every one.
- **Check reachability against shipped settings.** If the trace needs `Slots=1` and the code ships `Slots=4`, decide whether the trace needs the smaller value. Label every counterexample as one of: `reproduced` (a test fails on the real code), `reachable at shipped settings` (shipped constants and callers allow it, not yet reproduced), or `model-only` (needs a configuration or caller the code never uses). Keep the boundary cfg either way.
- Write for a reader who knows the code and has used neither tool. Lead with what goes wrong for a user, in the code's terms, with the steps in order and `file:line`. Define a tool term beside its first use: an invariant is always true; a liveness property says something eventually happens; fairness assumes a step that stays enabled does happen; `sorry` is an unfinished proof; an axiom is assumed without proof; a detected mutation is a planted bug the checks caught, which shows they can fail.
- Report as a table: machine, property (a sentence about the code, such as "the user never sees a reply missing a chunk"), expectation, verdict, states, depth, label, mutations detected, and the code fix. Say what a pass means where it first appears: TLC tried every ordering of the modelled steps at these sizes; Lean proved it for every input under the listed hypotheses. Then say what a pass leaves open: the sizes checked, the code behaviour the model leaves out, and each theorem's hypotheses. Treat specs as scratch by default: rather than merging spec folders into PRs, mention the branch or folder that holds them in the PR body.

## Runner details

- `check`, `tlc` and `mutate` upload only `*.tla` and `*.cfg`. `lean` uploads only `*.lean`, the `lakefile.*`, `lean-toolchain` and `lake-manifest.json`; `.statements` files stay local and are compared on the laptop. Folders named `states/`, `traces/`, `.lake/` and `build/` are skipped.
- Per-cfg logs go to `traces/<cfg>.txt` (set `FORMAL_OUT` to change this).
- `-metadir` is overridden and the heap is pinned to 12 GB. Workers default to 8; `-workers N` is honoured only for N from 1 to 8 (anything else is dropped). The JVM sees the host (24 cores, about 288 GB), so never use `-workers auto` or `MaxRAMPercentage`.
- Containers stay warm for 180 s after a call (`FORMAL_WARM_S`). A warm single check takes about 2 s end to end; the first batch after a quiet period pays roughly 1–1.5 min of cold start.
- Lean cold start (installing elan and the toolchain into the volume) took about 3 min once; after that a warm build takes about 10 s, and about 1 s when nothing changed.
- **Credentials:** Modal's own config (`modal token new`), or `MODAL_TOKEN_ID` and `MODAL_TOKEN_SECRET` in the environment, or a dotenv file named by `FORMAL_DEV_ENV` that defines them. Never print them.
- Modal app `formal`, environment `dev`, volume `formal-cache`. Run `formal deploy` after editing `formal.py`. Right after a deploy, an old warm container can serve one more call.
