# formal-verification

A Claude Code skill for verifying concurrency protocols with TLA+ (TLC) and pure logic with Lean 4. Every check runs on [Modal](https://modal.com) containers (8 CPU, 16 GB each, up to 100 in parallel), never on your laptop.

`SKILL.md` is the method:
- what to model;
- fast-tier and full-tier checks;
- vacuity witnesses, ablations and mutation testing, so every property is shown able to fail;
- frozen Lean statements;
- closing the gap between the model and the real code.

`scripts/formal` is the runner.

```bash
formal check Spec.tla              # every cfg in parallel, each compared with its `\* expect:` header
formal mutate Spec.mutations       # plant each listed bug in a copy of the spec; its property must fail
formal tlc -config X.cfg Spec.tla  # one raw TLC run, streamed
formal lean [--freeze] [TARGET]    # lake build + sorry/axiom audit + frozen-statement check
formal trace traces/X.txt          # a TLC counterexample reduced to what each step changed
formal deploy                      # deploy the Modal app (after editing formal.py)
```

## Setup

1. Install the skill:
   ```bash
   git clone https://github.com/philipk19238/formal-verification-skill ~/.claude/skills/formal-verification
   ```
2. Install [uv](https://docs.astral.sh/uv/). The runner uses it to start `modal` without a project environment.
3. Download the TLA+ tools jar to the path the runner bakes into its image (override it with `FORMAL_TLA_JAR`):
   ```bash
   mkdir -p ~/.local/share/formal
   curl -L -o ~/.local/share/formal/tla2tools.jar \
     https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
   ```
4. Authenticate with Modal (`uvx modal token new`), or export `MODAL_TOKEN_ID`/`MODAL_TOKEN_SECRET`. Alternatively, point `FORMAL_DEV_ENV` at a dotenv file that defines them.
5. Create a Modal environment named `dev`, or set `FORMAL_MODAL_ENV`. Then deploy:
   ```bash
   ~/.claude/skills/formal-verification/scripts/formal deploy
   ```

The first Lean run installs elan and the toolchain into the `formal-cache` Modal volume, which takes a few minutes; later builds take seconds.

## Settings

| Variable | Default | |
|---|---|---|
| `FORMAL_MODAL_ENV` | `dev` | Modal environment |
| `FORMAL_TLA_JAR` | `~/.local/share/formal/tla2tools.jar` | jar baked into the TLC image |
| `FORMAL_CPU` / `FORMAL_MEMORY_MB` | `8` / `16384` | per-container size |
| `FORMAL_WARM_S` | `180` | seconds a container stays warm |
| `FORMAL_OUT` | `traces` | where per-cfg logs and reduced traces go |
| `FORMAL_DEV_ENV` | unset | dotenv file with Modal tokens |

Only `*.tla`/`*.cfg` files (TLA+) or `*.lean`, lakefile and toolchain files (Lean) are uploaded. Keep spec folders free of source code and secrets.
