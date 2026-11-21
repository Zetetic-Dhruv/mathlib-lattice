#!/usr/bin/env python3
"""Compile MathlibLattice modules against design-lab's root Mathlib, in import order.

usage:
  tools/check.py MODULE_OR_FILE ...   compile these (and any stale project dependencies)
  tools/check.py --all                compile every module under MathlibLattice/
  tools/check.py --snippet FILE       compile a scratch file (not written to the build)

A module is recompiled when its source, or a project module it imports, is newer than its
.olean. Prints one verdict per module:
  clean    no messages
  sorry    only "declaration uses 'sorry'" warnings
  warning  other warnings (lint, unused variables, ...)
  error    errors (the module's .olean is not written)
followed by the messages. design-lab's root options are used (autoImplicit off), warnings
stay warnings so that sorries are reported apart from other warnings, and Mathlib's
line-length linter is on. The toolchain and the Mathlib build are read from design-lab's
lean-toolchain and lake-manifest.json; oleans go to mathlib-lattice/.lake/build."""
import fcntl
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DESIGN_LAB = os.path.dirname(ROOT)
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
with open(os.path.join(DESIGN_LAB, "lean-toolchain"), encoding="utf-8") as _f:
    _TC = _f.read().strip()  # e.g. leanprover/lean4:v4.31.0
TOOLCHAIN = os.path.expanduser(
    "~/.elan/toolchains/" + _TC.replace("/", "--").replace(":", "---"))
LEAN = os.path.join(TOOLCHAIN, "bin", "lean")
os.environ["PATH"] = os.path.join(TOOLCHAIN, "bin") + ":" + os.environ["PATH"]
FLAGS = ["-DautoImplicit=false", "-Dweak.linter.style.longLine=true"]

IMP = re.compile(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")
SORRY = re.compile(r"declaration uses [`']sorry[`']")


def is_sorry(sev, text):
    return sev == "warning" and SORRY.fullmatch(str(text).strip()) is not None


def lean_path():
    with open(os.path.join(DESIGN_LAB, "lake-manifest.json"), encoding="utf-8") as f:
        names = [p["name"] for p in json.load(f)["packages"]]
    pkgs = [os.path.join(DESIGN_LAB, ".lake", "packages", n, ".lake", "build", "lib", "lean")
            for n in names]
    libdir = subprocess.run([LEAN, "--print-libdir"], capture_output=True,
                            text=True).stdout.strip()
    return [BUILD] + [p for p in pkgs if os.path.isdir(p)] + [libdir]


def flags():
    return FLAGS


def module_of(path):
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    return rel[:-5].replace(os.sep, ".")


def path_of(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def project_imports(mod):
    out = []
    with open(path_of(mod), encoding="utf-8") as f:
        for line in f:
            s = line.strip()
            if not s or s.startswith("--") or s == "module":
                continue
            m = IMP.match(s)
            if not m:
                break
            if m.group(1).split(".")[0] == "MathlibLattice":
                out.append(m.group(1))
    return out


def all_modules():
    mods = []
    for d, _, fs in os.walk(os.path.join(ROOT, "MathlibLattice")):
        for f in fs:
            if f.endswith(".lean"):
                mods.append(module_of(os.path.join(d, f)))
    if os.path.exists(os.path.join(ROOT, "MathlibLattice.lean")):
        mods.append("MathlibLattice")
    return sorted(mods)


def order(targets):
    seen, out = set(), []

    def visit(m, stack):
        if m in seen:
            return
        if m in stack:
            sys.exit("import cycle through " + m)
        for d in project_imports(m):
            visit(d, stack | {m})
        seen.add(m)
        out.append(m)

    for t in targets:
        visit(t, set())
    return out


def olean(mod):
    return os.path.join(BUILD, *mod.split(".")) + ".olean"


def stale(mod, rebuilt):
    o = olean(mod)
    if not os.path.exists(o):
        return True
    if os.path.getmtime(path_of(mod)) > os.path.getmtime(o):
        return True
    return any(d in rebuilt or os.path.getmtime(olean(d)) > os.path.getmtime(o)
               for d in project_imports(mod) if os.path.exists(olean(d)))


def run(path, out=None):
    cmd = [LEAN, "--json"] + flags()
    if out:
        os.makedirs(os.path.dirname(out), exist_ok=True)
        cmd += ["-R", ROOT, "-o", out + ".olean", "-i", out + ".ilean"]
    env = dict(os.environ, LEAN_PATH=":".join(lean_path()))
    r = subprocess.run(cmd + [path], cwd=ROOT, env=env, capture_output=True, text=True,
                       timeout=3600)
    msgs = []
    for line in r.stdout.splitlines() + ([r.stderr] if r.stderr.strip() else []):
        try:
            m = json.loads(line)
            msgs.append((m["severity"], m["pos"]["line"], m["data"]))
        except (ValueError, KeyError, TypeError):
            if line.strip():
                msgs.append(("output", None, line.strip()))
    sev = [s for s, _, t in msgs]
    if r.returncode or "error" in sev:
        v = "error"
    elif all(is_sorry(s, t) for s, _, t in msgs if s == "warning") and "warning" in sev:
        v = "sorry"
    elif "warning" in sev:
        v = "warning"
    else:
        v = "clean"
    return v, msgs


def report(label, v, msgs, limit=40):
    n_sorry = sum(1 for s, _, t in msgs if is_sorry(s, t))
    print("%s: %s%s" % (label, v, " (%d sorry)" % n_sorry if n_sorry else ""), flush=True)
    shown = 0
    for s, line, t in msgs:
        if is_sorry(s, t) or s == "information":
            continue
        print("  %s line %s: %s" % (s, line, " ".join(str(t).split())[:400]), flush=True)
        shown += 1
        if shown >= limit:
            print("  ...", flush=True)
            break


def main(argv):
    if not argv:
        sys.exit(__doc__)
    if argv[0] == "--snippet":
        for p in argv[1:]:
            v, msgs = run(os.path.abspath(p))
            report(p, v, msgs)
        return
    targets = all_modules() if argv[0] == "--all" else \
        [module_of(a) if a.endswith(".lean") else a for a in argv]
    rebuilt, bad = set(), []
    for m in order(targets):
        if m not in targets and not stale(m, rebuilt):
            continue
        lock = olean(m) + ".lock"
        os.makedirs(os.path.dirname(lock), exist_ok=True)
        with open(lock, "w") as lf:
            fcntl.flock(lf, fcntl.LOCK_EX)
            v, msgs = run(path_of(m), olean(m)[:-6])
            fcntl.flock(lf, fcntl.LOCK_UN)
        rebuilt.add(m)
        report(m, v, msgs)
        if v == "error":
            bad.append(m)
    if bad:
        print("MODULES WITH ERRORS:", ", ".join(bad))
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv[1:])
