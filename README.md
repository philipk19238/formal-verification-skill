# Formal Verification Skill

A skill for coding agents that verifies concurrency protocols with [TLA+](https://lamport.azurewebsites.net/tla/tla.html) (TLC) and pure logic with [Lean 4](https://lean-lang.org/). Every check runs on [Modal](https://modal.com) containers (8 CPU and 16 GB each, up to 100 in parallel), never on your laptop.

## Overview

Tests catch the orderings someone thought to write down. A model checker tries every ordering. This skill teaches an agent to find the state machines in your code that are worth modelling, to model them small, and to check them in parallel. Every pass is trusted only after the agent shows it could have failed. Every failure is trusted only after it's reproduced in the real code.

It triggers when you ask an agent to formalize, model-check, prove, or "verify the state machine". It also triggers when a bug is intermittent, depends on ordering, or is "stuck until refresh".

## Installation

### Via `npx skills` (all major coding agents)

```bash
npx skills add philipk19238/formal-verification-skill
```

### Via cloning the repo

Clone it into your agent's skills directory, for example:

```bash
git clone https://github.com/philipk19238/formal-verification-skill ~/.agents/skills/formal-verification
```

### One-time runner setup

1. Install [uv](https://docs.astral.sh/uv/). The runner uses it to start `modal` without a project environment.
2. Download the TLA+ tools jar to the path the runner bakes into its image. Override the path with `FORMAL_TLA_JAR`.
   ```bash
   mkdir -p ~/.local/share/formal
   curl -L -o ~/.local/share/formal/tla2tools.jar \
     https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
   ```
3. Authenticate with Modal (`uvx modal token new`), or export `MODAL_TOKEN_ID` and `MODAL_TOKEN_SECRET`.
4. Create a Modal environment named `dev`, or set `FORMAL_MODAL_ENV` to another one. Then deploy the app from the skill folder:
   ```bash
   scripts/formal deploy
   ```

The first Lean run installs elan and the toolchain into the `formal-cache` Modal volume, which takes a few minutes. Later builds take seconds.

## Structure

```
formal-verification/
├── SKILL.md            # Entrypoint loaded into agent context: the method
├── README.md           # This file
└── scripts/
    ├── formal          # CLI wrapper (zsh): loads Modal credentials, runs formal.py via uv
    └── formal.py       # Modal app + local driver for TLC, Lean, mutation testing, trace reduction
```

## Commands

```bash
formal check Spec.tla [CFG...] [--tier fast|full|all] [-- TLC ARGS]
                                    # every cfg in parallel, each compared with its `\* expect:` header
formal mutate Spec.mutations        # plant each listed bug in a copy of the spec; its property must fail
formal tlc -config X.cfg Spec.tla   # one raw TLC run, streamed; counterexample files copied back
formal lean [--freeze] [TARGET...]  # lake build + sorry/axiom audit + frozen-statement check
formal trace traces/X.txt           # a TLC counterexample reduced to what each step changed
formal deploy                       # redeploy the Modal app after editing formal.py
```

## Core Principles

1. **Never verify locally.** TLC and Lean run only through the runner. One local TLC run once started 12 JVMs and froze the laptop.
2. **Pick cheap, likely bugs.** Rank candidates by bug likelihood × how small the model can be: shared state over unreliable delivery, timers racing events, and code that assumes an ordering.
3. **Every property must be able to fail.**
   - Witness cfgs prove the dangerous situation is reachable.
   - Ablation cfgs switch off one guard and must catch its bug.
   - Mutation files plant plausible bugs, each of which must be detected.
4. **Iterate on the fast tier.** Fast checks finish in about a minute. Larger constants run once, at the end.
5. **Freeze Lean statements before proving**, so a proof can't quietly prove an easier theorem.
6. **A violation is a hypothesis until reproduced.** Every counterexample ends as a failing test on the real code, or is labelled a model artifact.

## Configuration

| Variable | Default | Purpose |
|---|---|---|
| `FORMAL_MODAL_ENV` | `dev` | Modal environment the app is deployed to |
| `FORMAL_TLA_JAR` | `~/.local/share/formal/tla2tools.jar` | TLA+ tools jar baked into the TLC image |
| `FORMAL_CPU` / `FORMAL_MEMORY_MB` | `8` / `16384` | Size of each container |
| `FORMAL_WARM_S` | `180` | Seconds a container stays warm after a call |
| `FORMAL_OUT` | `traces` | Where per-cfg logs and reduced traces are written |
| `FORMAL_DEV_ENV` | unset | Dotenv file holding `MODAL_TOKEN_ID` / `MODAL_TOKEN_SECRET` |

Only `*.tla`/`*.cfg` files (TLA+) or `*.lean`, lakefile and toolchain files (Lean) are uploaded. Keep spec folders free of source code and secrets.
