"""Run TLA+ (TLC) and Lean checks on Modal instead of the local machine.

Usage (from the spec or project directory):
    formal check SPEC.tla [CFG...] [--tier fast|full|all] [-- TLC ARGS]
        Run every cfg (default: cfg/*.cfg and ./*.cfg) in parallel and compare each
        result with the `\\* expect:` line in its cfg. Exit 0 only if all match.
    formal tlc [TLC ARGS...]       one TLC run, same args as `java ... tlc2.TLC`
    formal lean [--freeze] [TARGET...]
        `lake build` (or `lean FILE` without a lakefile), failing on errors, `sorry`, or
        non-standard axioms under any declaration of the built modules. `--freeze`
        records each module's statements in <File>.statements (sorry allowed); later
        runs fail when a recorded theorem type or definition body changes.
    formal mutate NAME.mutations [--tier fast|full|all] [-- TLC ARGS]
        Apply each planted bug to a copy of NAME.tla (or NAME.lean) and check that
        the property it names now fails. All mutants run in parallel.
    formal trace LOG...            reduce a TLC log to what each step changed
    formal deploy                  (re)deploy the Modal app

cfg header lines (TLA comments, anywhere in the cfg):
    \\* expect: holds | violated [NAME] | deadlock     default: holds
    \\* tier: fast | full                             default: fast

mutations file (beside NAME.tla or NAME.lean):
    mutation <label>              starts a mutation
    detects <Property>            TLA: the invariant/property that must now fail
    detects witness:<cfg>         TLA: this Witness cfg must now hold (state unreachable)
    detects <Theorem>             Lean, optional: this declaration must be among the failures
    cfg <stem> [stem...]          TLA, optional: only these cfgs
    - <line>                      text to replace; consecutive lines must occur exactly once
    + <line>                      replacement lines; none deletes the text
"""

from __future__ import annotations

import io
import json
import os
import re
import sys
import tarfile
import time
from pathlib import Path

import modal

APP_NAME = "formal"
MODAL_ENV = os.environ.get("FORMAL_MODAL_ENV", "dev")
JAR = Path(os.environ.get("FORMAL_TLA_JAR", "~/.local/share/formal/tla2tools.jar")).expanduser()
CPU = float(os.environ.get("FORMAL_CPU", "8"))
MEMORY_MB = int(os.environ.get("FORMAL_MEMORY_MB", "16384"))
WARM_S = int(os.environ.get("FORMAL_WARM_S", "180"))
SKIP_DIRS = {"states", "traces", ".git", "__pycache__", ".lake", "build"}
TLA_FILES = {".tla", ".cfg"}
LEAN_FILES = {".lean"}
LEAN_NAMES = {"lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"}
AUDIT_TIMEOUT_S = int(os.environ.get("FORMAL_AUDIT_TIMEOUT_S", "600"))
STD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

app = modal.App(APP_NAME)
cache = modal.Volume.from_name("formal-cache", create_if_missing=True)
tla_image = (
    modal.Image.from_registry("eclipse-temurin:21-jre", add_python="3.12")
    .add_local_file(JAR, "/opt/tla2tools.jar", copy=True)
    .env({"TLC_HEAP_MB": str(int(MEMORY_MB * 0.75)), "TLC_WORKERS": str(int(CPU))})
)
lean_image = (
    modal.Image.from_registry("debian:bookworm-slim", add_python="3.12")
    .apt_install("curl", "git", "ca-certificates")
    .env({"ELAN_HOME": "/cache/elan", "PATH": "/cache/elan/bin:/usr/local/bin:/usr/bin:/bin"})
)


def _bundle(root: Path, keep, overrides: dict[str, bytes] | None = None) -> bytes:
    overrides = overrides or {}
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as tar:
        for path in root.rglob("*"):
            rel = path.relative_to(root)
            if any(part in SKIP_DIRS for part in rel.parts[:-1]):
                continue
            if path.is_file() and keep(path) and str(rel) not in overrides:
                tar.add(path, arcname=str(rel))
        for rel, data in overrides.items():
            info = tarfile.TarInfo(rel)
            info.size, info.mtime = len(data), int(time.time())
            tar.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def _tla_bundle(root: Path, overrides: dict[str, bytes] | None = None) -> bytes:
    return _bundle(root, lambda p: p.suffix in TLA_FILES and "_TTrace_" not in p.name, overrides)


def _lean_bundle(root: Path) -> bytes:
    return _bundle(root, lambda p: p.suffix in LEAN_FILES or p.name in LEAN_NAMES)


def _remote_args(args: list[str]) -> list[str]:
    """Drop -metadir, and -workers unless it asks for 1..CPU workers (1 makes BFS traces shortest)."""
    out: list[str] = []
    it = iter(args)
    for arg in it:
        if arg in ("-metadir", "-workers"):
            value = next(it, "")
            if arg == "-workers" and value.isdigit() and 1 <= int(value) <= int(CPU):
                out += [arg, value]
            continue
        out.append(arg)
    return out


@app.function(image=tla_image, cpu=CPU, memory=MEMORY_MB, timeout=3 * 3600, max_containers=100, scaledown_window=WARM_S)
def tlc(bundle: bytes, args: list[str]):
    import subprocess
    import tempfile

    work = Path(tempfile.mkdtemp(prefix="tlc-"))
    with tarfile.open(fileobj=io.BytesIO(bundle), mode="r:gz") as tar:
        tar.extractall(work, filter="data")
    before = {p for p in work.rglob("*") if p.is_file()}
    cmd = [
        "java", f"-Xmx{os.environ['TLC_HEAP_MB']}m", "-XX:+UseParallelGC", "-cp", "/opt/tla2tools.jar", "tlc2.TLC",
        *([] if "-workers" in args else ["-workers", os.environ["TLC_WORKERS"]]), "-metadir", str(work / "states"), *args,
    ]
    proc = subprocess.Popen(cmd, cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert proc.stdout is not None
    for line in proc.stdout:
        yield ("out", line)
    rc = proc.wait()
    files = {}
    for p in work.rglob("*"):
        rel = p.relative_to(work)
        if p.is_file() and p not in before and rel.parts[0] != "states":
            files[str(rel)] = p.read_bytes()
    yield ("files", files)
    yield ("rc", rc)


AUDIT_LEAN = r"""
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : Array Name := #[MODULES]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited := 0
  for (module, data) in env.header.moduleNames.zip env.header.moduleData do
   unless targets.contains module do continue
   for name in data.constNames do
    let user := (privateToUserName? name).getD name
    if user.isInternal then continue
    let some info := env.find? name | continue
    if info matches .axiomInfo _ then
      IO.println s!"AXIOMS {user} declares an axiom"
      continue
    audited := audited + 1
    let extra := (← collectAxioms name).filter (!standard.contains ·)
    unless extra.isEmpty do IO.println s!"AXIOMS {user} depends on {extra.toList}"
    if (← findDeclarationRanges? name).isNone then continue
    let (kind, value) := match info with
      | .thmInfo _ => ("theorem", none)
      | .defnInfo v => ("definition", if Meta.isInstanceCore env name then none else some v.value)
      | .opaqueInfo _ => ("opaque", none)
      | .inductInfo _ => ("inductive", none)
      | .ctorInfo _ => ("constructor", none)
      | .recInfo _ => ("recursor", none)
      | _ => ("other", none)
    let pp ← liftTermElabM <| Meta.ppExpr info.type
    let record := Json.mkObj [
      ("module", toJson module.toString), ("name", toJson user.toString), ("kind", toJson kind),
      ("typeHash", toJson s!"{mixHash (hash info.levelParams) info.type.hash}"),
      ("valueHash", match value with | some v => toJson s!"{v.hash}" | none => Json.null),
      ("type", toJson pp.pretty)]
    IO.println s!"STATEMENT {record.compress}"
  IO.println s!"AUDITED {audited} declarations"
"""


@app.function(image=lean_image, cpu=CPU, memory=MEMORY_MB, timeout=3600, volumes={"/cache": cache}, scaledown_window=WARM_S)
def lean(bundle: bytes, project: str, targets: list[str], audit: bool = False, mutants: list | None = None):
    import subprocess
    import tempfile

    def run(cmd: list[str] | str, cwd: Path) -> int:
        proc = subprocess.Popen(cmd, cwd=cwd, shell=isinstance(cmd, str), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        assert proc.stdout is not None
        for line in proc.stdout:
            out.append(line)
        return proc.wait()

    out: list[str] = []
    cache.reload()
    if not Path("/cache/elan/bin/elan").exists():
        run("curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none", Path("/"))
    work = Path("/cache/projects") / project
    work.mkdir(parents=True, exist_ok=True)
    previous: dict[str, tuple[bytes, float]] = {}
    for p in work.rglob("*"):
        rel = p.relative_to(work)
        if p.is_file() and not (rel.parts and rel.parts[0] == ".lake") and (p.suffix in LEAN_FILES or p.name in LEAN_NAMES):
            previous[str(rel)] = (p.read_bytes(), p.stat().st_mtime)
            p.unlink()
    with tarfile.open(fileobj=io.BytesIO(bundle), mode="r:gz") as tar:
        tar.extractall(work, filter="data")
        sources = [m.name for m in tar.getmembers() if m.name.endswith(".lean") and Path(m.name).name != "lakefile.lean"]
    # An unchanged file keeps its old mtime and a changed one is stamped now, so an
    # .olean older than its source always means "not rebuilt since the change".
    now = time.time()
    for rel in sources:
        old = previous.get(rel)
        stamp = old[1] if old and old[0] == (work / rel).read_bytes() else now
        os.utime(work / rel, (stamp, stamp))
    if not (work / "lean-toolchain").exists():
        (work / "lean-toolchain").write_text("leanprover/lean4:stable\n")
    yield ("out", "".join(out))
    out.clear()

    lakefile = (work / "lakefile.lean").exists() or (work / "lakefile.toml").exists()
    if lakefile:
        manifest = work / "lake-manifest.json"
        if manifest.exists() and "mathlib" in manifest.read_text() and not (work / ".lake/packages/mathlib").exists():
            run(["lake", "exe", "cache", "get"], work)
        rc = run(["lake", "build", *targets], work)
    else:
        files = targets or sorted(str(p.relative_to(work)) for p in work.rglob("*.lean"))
        rc = 0
        for f in files:
            out.append(f"--- {f}\n")
            rc = max(rc, run(["lean", f], work))
    cache.commit()
    yield ("out", "".join(out))
    out.clear()

    if lakefile and rc == 0 and audit:
        # A source is audited only when its .olean is at least as new as the source,
        # so a module these targets did not (re)build is reported, never audited stale.
        modules: dict[str, str] = {}
        for src in sources:
            parts = Path(src).with_suffix("").parts
            found = [(".".join(parts[i:]), olean) for i in range(len(parts)) for lib in ("lib/lean", "lib")
                     if (olean := (work / ".lake/build" / lib / Path(*parts[i:])).with_suffix(".olean")).exists()]
            if found and found[0][1].stat().st_mtime >= (work / src).stat().st_mtime:
                modules[src] = found[0][0]
        for src in sources:
            if src not in modules:
                out.append(f"UNBUILT {src}\n")
        for src, module in modules.items():
            out.append(f"MODULE {src} {module}\n")
        if modules:
            mods = sorted(set(modules.values()))
            program = "import Lean\n" + "".join(f"import {m}\n" for m in mods)
            program += AUDIT_LEAN.replace("MODULES", ", ".join(f"`{m}" for m in mods))
            tmp = Path(tempfile.mkdtemp(prefix="audit-")) / "Audit.lean"
            tmp.write_text(program)
            arc = run(["timeout", str(AUDIT_TIMEOUT_S), "lake", "env", "lean", str(tmp)], work)
            out.append(f"AUDIT_RC {arc}\n")
        yield ("audit", "".join(out))
        out.clear()

    if mutants is not None:
        if rc != 0:
            yield ("out", "base build failed; mutants not checked\n")
        else:
            for i, (label, rel, content) in enumerate(mutants):
                tmp = Path(tempfile.mkdtemp(prefix=f"mut{i}-")) / Path(rel).name
                tmp.write_text(content)
                mrc = run(["lake", "env", "lean", str(tmp)] if lakefile else ["lean", str(tmp)], work)
                yield ("mutant", (label, mrc, str(tmp), "".join(out)))
                out.clear()
    yield ("rc", rc)


def _collect(gen, sink, extras: dict | None = None, keep_files: bool = True) -> int:
    rc = 1
    try:
        for kind, value in gen:
            if kind == "out":
                sink.write(value)
                sink.flush()
            elif kind in ("audit", "mutant") and extras is not None:
                extras.setdefault(kind, []).append(value)
            elif kind == "files" and keep_files:
                for rel, data in value.items():
                    dest = Path.cwd() / rel
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes(data)
            elif kind == "rc":
                rc = value
    except Exception as exc:
        sink.write(f"\nformal: remote run failed before it finished: {exc!r}\n")
        return -1
    return rc


def _fn(name: str):
    return modal.Function.from_name(APP_NAME, name, environment_name=MODAL_ENV)


TLC_VIOLATION = re.compile(
    r"Invariant (\S+) is violated"
    r"|Temporal properties were violated"
    r"|Temporal property (\S+) (?:was|is) violated"
    r"|(?:Action )?[Pp]roperty (\S+) is violated"
)
TLC_ASSERT = "The first argument of Assert evaluated to FALSE"
TLC_DONE = "Model checking completed. No error has been found."


def _verdict(text: str, rc: int) -> tuple[str, str]:
    """A TLC run's result from its exit code and log: holds only on exit 0 with the completion line.

    Exit codes: 11 deadlock, 12 invariant or `[]P` property, 13 temporal, action, or initial-state
    property, 14 Assert. Anything else (10 assumption, 150 parse/semantic, 151 cfg, OOM, disk, a lost
    container) is an error, never a pass.
    """
    m = TLC_VIOLATION.search(text)
    name = next((g for g in m.groups() if g), "") if m else ""
    deadlock = "Deadlock reached" in text
    if rc == 11 or (rc == 0 and deadlock):
        return "deadlock", ""
    if rc in (12, 13) or (rc == 0 and m):
        return "violated", name
    if rc == 14 or (rc == 0 and TLC_ASSERT in text):
        return "violated", "Assert"
    if rc == 0 and TLC_DONE in text:
        return "holds", ""
    return "error", f"exit {rc}"


def _stats(text: str) -> str:
    states = re.findall(r"([\d,]+) distinct states found", text)
    depth = re.findall(r"depth of the complete state graph search is (\d+)", text)
    return " ".join(x for x in (f"{states[-1]} states" if states else "", f"depth {depth[-1]}" if depth else "") if x)


def _header(cfg: Path) -> tuple[str, str, str]:
    text = cfg.read_text()
    expect = re.search(r"\\\*[ \t]*expect:[ \t]*(holds|violated|deadlock)[ \t]*(\S*)", text)
    tier = re.search(r"\\\*[ \t]*tier:[ \t]*(fast|full)", text)
    return (expect.group(1) if expect else "holds", expect.group(2) if expect else "", tier.group(1) if tier else "fast")


def reduce_trace(text: str) -> str:
    """The first error trace in a TLC log: one block per state, listing only the variables that changed."""
    lines = text.splitlines()
    start = next((i for i, line in enumerate(lines) if re.match(r"^State 1: ", line)), None)
    if start is None:
        return ""
    blocks: list[tuple[str, dict[str, str]]] = []
    title: str | None = None
    values: dict[str, str] = {}
    var = None
    for line in lines[start:]:
        if m := re.match(r"^State (\d+): <?(.*?)>?$", line):
            if title:
                blocks.append((title, values))
            action = re.sub(r" line \d+, col \d+ to line \d+, col \d+ of module \w+$", "", m[2])
            title, values, var = f"state {m[1]}: {action}", {}, None
        elif line.startswith("Back to state") or line.strip() == "Stuttering":
            if title:
                blocks.append((title, values))
            blocks.append((line.strip(), {}))
            title = None
        elif title and (m := re.match(r"^(?:/\\ )?(\w+) = (.*)$", line)):
            var = m[1]
            values[var] = m[2]
        elif title and var and line.startswith(" ") and line.strip():
            values[var] += "\n" + line
        elif line.strip() and not title:
            break
        elif not line.strip() and title:
            blocks.append((title, values))
            title = None
    if title:
        blocks.append((title, values))
    out: list[str] = []
    prev: dict[str, str] = {}
    for title, vals in blocks:
        out.append(f"--- {title}")
        out += [f"    {k} = {v}" for k, v in vals.items() if prev.get(k) != v]
        prev = vals or prev
    return "\n".join(out)


CFG_KEYWORDS = {"CONSTANT", "CONSTANTS", "INIT", "NEXT", "SPECIFICATION", "INVARIANT", "INVARIANTS", "PROPERTY",
                "PROPERTIES", "SYMMETRY", "VIEW", "CONSTRAINT", "CONSTRAINTS", "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS",
                "CHECK_DEADLOCK", "POSTCONDITION", "ALIAS"}


def _cfg_checks(text: str) -> tuple[dict[str, str], str]:
    """The cfg's checked names (name -> INVARIANT | PROPERTY) and the cfg text without those sections."""
    kinds: dict[str, str] = {}
    kept: list[str] = []
    section = None
    for line in text.splitlines():
        words = line.split("\\*")[0].split()
        if words and words[0] in CFG_KEYWORDS:
            section, words = words[0], words[1:]
        if section in ("INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES"):
            kinds.update(dict.fromkeys(words, "INVARIANT" if section.startswith("INV") else "PROPERTY"))
        else:
            kept.append(line)
    return kinds, "\n".join(kept) + "\n"


def _split_tier(argv: list[str]) -> tuple[list[str], list[str], str]:
    extra: list[str] = []
    if "--" in argv:
        i = argv.index("--")
        argv, extra = argv[:i], argv[i + 1 :]
    tier = "fast"
    if "--tier" in argv:
        i = argv.index("--tier")
        tier = argv[i + 1]
        argv = argv[:i] + argv[i + 2 :]
    return argv, extra, tier


def run_tlc(args: list[str]) -> int:
    return _collect(_fn("tlc").remote_gen(_tla_bundle(Path.cwd()), _remote_args(args)), sys.stdout)


def run_check(argv: list[str]) -> int:
    from concurrent.futures import ThreadPoolExecutor, as_completed

    argv, extra, tier = _split_tier(argv)
    spec, cfg_args = argv[0], argv[1:]
    cfgs = [Path(c) for c in cfg_args] or sorted([*Path("cfg").glob("*.cfg"), *Path(".").glob("*.cfg")])
    jobs = [(c, *_header(c)) for c in cfgs]
    skipped = [c for c, _, _, t in jobs if tier != "all" and t != tier]
    jobs = [j for j in jobs if j[0] not in skipped]
    if skipped:
        print(f"skipping {len(skipped)} cfg(s) outside tier {tier}: {' '.join(c.stem for c in skipped)}", flush=True)
    bundle = _tla_bundle(Path.cwd())
    fn = _fn("tlc")
    out_dir = Path(os.environ.get("FORMAL_OUT", "traces"))
    out_dir.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()

    def one(job):
        cfg, want, name, _ = job
        t0 = time.monotonic()
        buf = io.StringIO()
        rc = _collect(fn.remote_gen(bundle, _remote_args([*extra, "-config", str(cfg), spec])), buf)
        text = buf.getvalue()
        (out_dir / f"{cfg.stem}.txt").write_text(text)
        trace = reduce_trace(text)
        if trace:
            (out_dir / f"{cfg.stem}.trace.txt").write_text(trace + "\n")
        got, got_name = _verdict(text, rc)
        ok = got == want and (not name or got_name in ("", name))
        return cfg, ok, want if not name else f"{want} {name}", got if not got_name else f"{got} {got_name}", _stats(text), time.monotonic() - t0, trace

    failed = 0
    with ThreadPoolExecutor(max_workers=len(jobs) or 1) as pool:
        for future in as_completed([pool.submit(one, j) for j in jobs]):
            cfg, ok, want, got, stats, secs, trace = future.result()
            failed += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {cfg.stem:<40} expect {want:<24} got {got:<24} {stats} ({secs:.0f}s)", flush=True)
            if not ok and trace:
                print("\n".join("     " + t for t in trace.splitlines()), flush=True)
    print(f"{len(jobs) - failed}/{len(jobs)} as expected in {time.monotonic() - start:.0f}s; logs in {out_dir}/")
    return 1 if failed else 0


def _toolchain(root: Path) -> str:
    pin = root / "lean-toolchain"
    return pin.read_text().strip() if pin.exists() else "leanprover/lean4:stable"


def _statements(audit: str, modules: dict[str, str], root: Path, freeze: bool, whole_project: bool) -> list[str]:
    """Write (--freeze) or check each audited source's <File>.statements. Returns failure lines."""
    records: dict[str, dict[str, dict]] = {}
    for line in audit.splitlines():
        if line.startswith("STATEMENT "):
            rec = json.loads(line.removeprefix("STATEMENT "))
            rec["type"] = " ".join(rec["type"].split())
            records.setdefault(rec.pop("module"), {})[rec["name"]] = rec
    toolchain = _toolchain(root)
    failures: list[str] = []
    for src, module in sorted(modules.items()):
        path = (root / src).with_suffix(".statements")
        current = records.get(module, {})
        if freeze:
            path.write_text(json.dumps({"format": 1, "toolchain": toolchain, "module": module,
                                        "declarations": [current[n] for n in sorted(current)]}, indent=2, ensure_ascii=False) + "\n")
            print(f"FROZEN {path.relative_to(root)}: {len(current)} statements recorded; proofs not checked")
            continue
        if not path.exists():
            continue
        frozen = json.loads(path.read_text())
        if frozen["toolchain"] != toolchain:
            failures.append(f"FROZEN {src}: toolchain changed from {frozen['toolchain']} to {toolchain}; review, then `formal lean --freeze`")
            continue
        for old in frozen["declarations"]:
            new = current.get(old["name"])
            if new and all(old[k] == new[k] for k in ("kind", "typeHash", "valueHash")):
                continue
            failures.append(f"FROZEN {old['name']}: statement changed\n  old: {old['type']}\n  new: {new['type'] if new else '(deleted)'}"
                            + ("\n  definition body changed" if new and old["valueHash"] != new["valueHash"] else ""))
    if whole_project and not freeze:
        for path in sorted(root.rglob("*.statements")):
            src = str(path.relative_to(root).with_suffix(".lean"))
            if ".lake" not in path.parts and src not in modules:
                failures.append(f"FROZEN {src}: has a .statements record but was not built and audited (source deleted, or no default target owns it)")
    return failures


def run_lean(argv: list[str]) -> int:
    freeze = "--freeze" in argv
    targets = [a for a in argv if a != "--freeze"]
    root = Path.cwd()
    lakefile = (root / "lakefile.lean").exists() or (root / "lakefile.toml").exists()
    if freeze and not lakefile:
        print("--freeze needs a Lake project (lakefile.toml or lakefile.lean)")
        return 2
    buf = io.StringIO()
    extras: dict[str, list] = {}
    start = time.monotonic()
    rc = _collect(_fn("lean").remote_gen(_lean_bundle(root), root.name, targets, audit=True), buf, extras)
    text = buf.getvalue()
    sys.stdout.write(text)
    audit = "".join(extras.get("audit", []))
    sorries = len(re.findall(r"declaration uses ['`]sorry['`]", text))
    axioms = set()
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", text):
        axioms |= {a.strip() for a in m.group(1).split(",") if a.strip()}
    flagged = [line for line in audit.splitlines() if line.startswith("AXIOMS ")]
    if freeze:
        flagged = [line for line in flagged if not re.fullmatch(r"AXIOMS \S+ depends on \[sorryAx\]", line)]
    extra = sorted((axioms - STD_AXIOMS) - ({"sorryAx"} if freeze else set()))
    modules = dict(line.split()[1:3] for line in audit.splitlines() if line.startswith("MODULE "))
    unbuilt = [line.split()[1] for line in audit.splitlines() if line.startswith("UNBUILT ")]
    audit_rc = re.search(r"^AUDIT_RC (\d+)$", audit, re.M)
    audit_ok = not modules or (audit_rc is not None and audit_rc.group(1) == "0" and re.search(r"^AUDITED \d+ declarations$", audit, re.M))
    if not audit_ok:
        print("axiom audit did not run cleanly:\n" + "\n".join(line for line in audit.splitlines() if line.strip())[-4000:])
    for line in flagged:
        print(line)
    for src in unbuilt:
        if targets:
            print(f"note: {src} was not built by these targets; it was not audited")
        else:
            print(f"UNBUILT {src}: no default target builds it, so it was not checked; add it to a default lean_lib or move it out")
    failures = _statements(audit, modules, root, freeze, whole_project=not targets) if rc == 0 and audit_ok and lakefile else []
    for line in failures:
        print(line)
    ok = rc == 0 and (freeze or not sorries) and not extra and not flagged and audit_ok and not failures and not (unbuilt and not targets)
    audited = re.search(r"^AUDITED (\d+)", audit, re.M)
    print(f"\nlean {'ok' if ok else 'FAILED'}{' (frozen; proofs not checked)' if freeze and ok else ''} rc={rc} sorry={sorries} "
          f"non-standard axioms={len(flagged) or extra or 'none'} audited={audited.group(1) if audited else 0} "
          f"frozen-statement changes={len(failures)} unbuilt={len(unbuilt)} ({time.monotonic() - start:.0f}s)")
    return 0 if ok else (rc or 1)


def _parse_mutations(path: Path) -> list[dict]:
    mutations: list[dict] = []
    for n, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        key, _, rest = line.partition(" ")
        if key == "mutation":
            mutations.append({"label": rest.strip(), "detects": "", "cfg": [], "old": [], "new": []})
        elif not mutations:
            raise SystemExit(f"{path}:{n}: '{line}' before any mutation line")
        elif key == "detects":
            mutations[-1]["detects"] = rest.strip()
        elif key == "cfg":
            mutations[-1]["cfg"] = rest.split()
        elif key in ("-", "+"):
            mutations[-1]["old" if key == "-" else "new"].append(rest)
        else:
            raise SystemExit(f"{path}:{n}: unknown directive: {line}")
    return mutations


def _apply(text: str, m: dict) -> str:
    old = "\n".join(m["old"])
    count = text.count(old) if old else 0
    if count != 1:
        raise SystemExit(f"mutation '{m['label']}': its - text occurs {count} times, want exactly 1")
    return text.replace(old, "\n".join(m["new"]))


def _mutate_tla(spec: Path, mutations: list[dict], tier: str, extra: list[str]) -> int:
    from concurrent.futures import ThreadPoolExecutor

    root = Path.cwd()
    spec_rel = str(spec.resolve().relative_to(root.resolve()))
    cfgs = sorted([*Path("cfg").glob("*.cfg"), *Path(".").glob("*.cfg")])
    info = {c.stem: (c, *_header(c), *_cfg_checks(c.read_text())) for c in cfgs}  # stem -> cfg, want, name, tier, kinds, base
    in_tier = {s: v for s, v in info.items() if tier == "all" or v[3] == tier}
    out_dir = Path(os.environ.get("FORMAL_OUT", "traces")) / "mutants"
    out_dir.mkdir(parents=True, exist_ok=True)
    fn = _fn("tlc")
    spec_text = spec.read_text()

    jobs = []  # (mutation index, cfg stem, cfg path in bundle, kind, args)
    bundles: dict[int, dict[str, bytes]] = {}
    for i, m in enumerate(mutations):
        overrides = {spec_rel: _apply(spec_text, m).encode()}
        if m["detects"].startswith("witness:"):
            stem = m["detects"].removeprefix("witness:")
            if stem not in info:
                raise SystemExit(f"mutation '{m['label']}': no cfg named {stem}")
            jobs.append((i, stem, str(info[stem][0]), "WITNESS", extra))
        else:
            prop = m["detects"]
            cands = [s for s, v in in_tier.items() if v[1] == "holds" and prop in v[4] and (not m["cfg"] or s in m["cfg"])]
            if not cands:
                raise SystemExit(f"mutation '{m['label']}': no `expect: holds` cfg in tier {tier} checks {prop!r}")
            for stem in cands:
                kind = info[stem][4][prop]
                rel = f"__mutant_{i}_{stem}.cfg"
                overrides[rel] = (info[stem][5] + f"{kind} {prop}\n").encode()
                jobs.append((i, stem, rel, kind, [*extra, "-deadlock"] if kind == "INVARIANT" else extra))
        bundles[i] = _tla_bundle(root, overrides)

    def one(job):
        i, stem, cfg_rel, kind, args = job
        buf = io.StringIO()
        rc = _collect(fn.remote_gen(bundles[i], _remote_args([*args, "-config", cfg_rel, spec_rel])), buf, keep_files=False)
        text = buf.getvalue()
        slug = re.sub(r"[^A-Za-z0-9]+", "-", mutations[i]["label"]).strip("-")[:60]
        (out_dir / f"{i:02d}-{slug}--{stem}.txt").write_text(text)
        got, name = _verdict(text, rc)
        prop = mutations[i]["detects"]
        if kind == "WITNESS":
            hit = got == "holds"
        elif kind == "INVARIANT":
            hit = got == "violated" and name == prop
        else:
            hit = got == "deadlock" or (got == "violated" and name in ("", prop))
        return i, stem, hit, got if not name else f"{got} {name}", _stats(text)

    start = time.monotonic()
    with ThreadPoolExecutor(max_workers=len(jobs) or 1) as pool:
        results = list(pool.map(one, jobs))
    detected = 0
    for i, m in enumerate(mutations):
        mine = [r for r in results if r[0] == i]
        hits = [r for r in mine if r[2]]
        errors = [r for r in mine if r[3].startswith("error")]
        if hits:
            detected += 1
            what = "now holds (state unreachable)" if m["detects"].startswith("witness:") else f"{m['detects']} fails"
            print(f"DETECTED {m['label']}: {what} in {', '.join(f'{r[1]} ({r[4]})' for r in hits)}")
        elif errors:
            print(f"ERROR    {m['label']}: TLC error in {', '.join(r[1] for r in errors)}; see {out_dir}/")
        else:
            print(f"MISSED   {m['label']}: {'; '.join(f'{r[1]} got {r[3]}' for r in mine)}")
    needed = {n for v in in_tier.values() if v[1] == "holds" for n in v[4]}
    covered = {m["detects"] for m in mutations} | {v[2] for v in info.values() if v[1] == "violated" and v[2]}
    uncovered = sorted(needed - covered)
    for name in uncovered:
        print(f"UNCOVERED {name}: no mutation or violated-expect cfg (Ablate-/Bug-) targets it")
    print(f"SUMMARY {detected} of {len(mutations)} mutations detected"
          + (f", {len(uncovered)} properties without a mutation" if uncovered else "")
          + f" in {time.monotonic() - start:.0f}s; logs in {out_dir}/")
    return 0 if detected == len(mutations) and not uncovered else 1


LEAN_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                       r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|#guard|#eval)\b\s*([^\s:(\[{]*)")


def _mutate_lean(model: Path, mutations: list[dict]) -> int:
    root = Path.cwd()
    rel = str(model.resolve().relative_to(root.resolve()))
    text = model.read_text()
    payload = [(m["label"], rel, _apply(text, m)) for m in mutations]
    extras: dict[str, list] = {}
    buf = io.StringIO()
    start = time.monotonic()
    rc = _collect(_fn("lean").remote_gen(_lean_bundle(root), root.name, [], mutants=payload), buf, extras)
    if rc != 0:
        sys.stdout.write(buf.getvalue())
        print("base build failed; fix the unmutated model first")
        return 1
    detected = 0
    for (label, mrc, tmp, output), (_, _, source), m in zip(extras.get("mutant", []), payload, mutations):
        lines = source.splitlines()
        failed: list[str] = []
        for match in re.finditer(rf"^{re.escape(tmp)}:(\d+):\d+: error", output, re.M):
            for line in reversed(lines[: int(match[1])]):
                if d := LEAN_DECL.match(line):
                    name = f"{d[1]} {d[2]}".strip() if not d[1].startswith("#") else line.strip()[:60]
                    if name not in failed:
                        failed.append(name)
                    break
        props = all(f.startswith(("theorem", "lemma", "example", "#guard")) for f in failed)
        named = not m["detects"] or any(f.split()[-1] == m["detects"] or f.endswith(" " + m["detects"]) for f in failed)
        if mrc == 0:
            print(f"MISSED   {label}")
        elif failed and props and named:
            detected += 1
            print(f"DETECTED {label}: fails {'; '.join(failed)}")
        else:
            reason = "a definition no longer compiles" if failed and not props else f"{m['detects']} did not fail" if failed else "no error located"
            print(f"ERROR    {label}: {reason}: {'; '.join(failed)}\n" + "\n".join("    " + x for x in output.splitlines()[:20]))
    print(f"SUMMARY {detected} of {len(mutations)} mutations detected ({time.monotonic() - start:.0f}s)")
    return 0 if detected == len(mutations) else 1


def run_mutate(argv: list[str]) -> int:
    argv, extra, tier = _split_tier(argv)
    path = Path(argv[0])
    mutations = _parse_mutations(path)
    if not mutations:
        raise SystemExit(f"{path} has no mutation")
    if path.with_suffix(".tla").exists():
        return _mutate_tla(path.with_suffix(".tla"), mutations, tier, extra)
    if path.with_suffix(".lean").exists():
        return _mutate_lean(path.with_suffix(".lean"), mutations)
    raise SystemExit(f"no {path.with_suffix('.tla').name} or {path.with_suffix('.lean').name} beside {path}")


def run_trace(paths: list[str]) -> int:
    found = False
    for p in paths:
        trace = reduce_trace(Path(p).read_text())
        found |= bool(trace)
        print(f"== {p}\n{trace or '(no error trace)'}")
    return 0 if found else 1


def main(argv: list[str]) -> int:
    cmd, rest = (argv[0], argv[1:]) if argv else ("", [])
    if cmd == "deploy":
        with modal.enable_output():
            app.deploy(environment_name=MODAL_ENV)
        return 0
    if cmd == "check":
        return run_check(rest)
    if cmd == "tlc":
        return run_tlc(rest)
    if cmd == "lean":
        return run_lean(rest)
    if cmd == "mutate":
        return run_mutate(rest)
    if cmd == "trace":
        return run_trace(rest)
    print(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
