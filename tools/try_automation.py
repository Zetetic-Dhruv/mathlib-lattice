#!/usr/bin/env python3
"""Try standard closers on every `sorry` of the project, one scratch copy per tactic.

usage: tools/try_automation.py [--all | MODULE_OR_FILE ...] [--out FILE] [--jobs N]

For each module and each tactic (rfl, decide, simp, grind, aesop, tauto, exact?), every
`sorry` is replaced by the tactic in a scratch copy, which is compiled against the project
build. A declaration counts as closed by a tactic when that copy reports no error inside the
declaration. `exact?` successes record the lemma Lean suggests (a citation). The (module,
tactic) compiles run in parallel, N at a time (default 4). The sources are never modified.
Output: one JSON object per declaration with a sorry."""
import concurrent.futures
import json
import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check  # noqa: E402

TACTICS = ["rfl", "decide", "simp", "grind", "aesop", "tauto", "exact?"]
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|example|structure|class|inductive)\s*([^\s:({\[]*)")
SORRY = re.compile(r"\bsorry\b")


def strip_comments(src):
    """Blank out comments and strings, keeping offsets."""
    out, i, n, depth = list(src), 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth:
            if src[i] != "\n":
                out[i] = " "
            i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                if src[k] != "\n":
                    out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


def declarations(src):
    """(start_line, name, kind) for each declaration, 1-based lines."""
    res = []
    for ln, line in enumerate(src.split("\n"), 1):
        m = DECL.match(line)
        if m:
            res.append((ln, m.group(2) or "(anonymous)", m.group(1)))
    return res


def owner(decls, line):
    best = None
    for d in decls:
        if d[0] <= line:
            best = d
        else:
            break
    return best


def replace(src, clean, tactic):
    out, last = [], 0
    for m in SORRY.finditer(clean):
        before = clean[:m.start()].rstrip()
        out.append(src[last:m.start()])
        if before.endswith(":="):
            out.append("by " + tactic)
        else:
            out.append(tactic)
        last = m.end()
    out.append(src[last:])
    return "".join(out)


def prepare(mod):
    path = check.path_of(mod)
    src = open(path, encoding="utf-8").read()
    clean = strip_comments(src)
    decls = declarations(clean)
    targets = {}
    for m in SORRY.finditer(clean):
        ln = clean[:m.start()].count("\n") + 1
        d = owner(decls, ln)
        if d:
            targets.setdefault(d, set()).add(ln)
    return src, clean, decls, targets


def run_job(mod, tac, src, clean, decls):
    text = replace(src, clean, tac)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=os.environ.get("TMPDIR"),
                                     delete=False, encoding="utf-8") as f:
        f.write(text)
        tmp = f.name
    try:
        _, msgs = check.run(tmp)
    finally:
        os.unlink(tmp)
    bad, suggestions = set(), {}
    for sev, line, txt in msgs:
        if line is None:
            if sev in ("error", "output"):
                bad.add(None)
            continue
        d = owner(decls, line)
        if sev == "error" and d:
            bad.add(d)
        if tac == "exact?" and sev == "information" and "Try this" in str(txt) and d:
            suggestions[d] = " ".join(str(txt).split())[:300]
    return bad, suggestions


def main(argv):
    out, jobs = None, 4
    if "--out" in argv:
        i = argv.index("--out")
        out = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if "--jobs" in argv:
        i = argv.index("--jobs")
        jobs = int(argv[i + 1])
        argv = argv[:i] + argv[i + 2:]
    mods = check.all_modules() if argv == ["--all"] else \
        [check.module_of(a) if a.endswith(".lean") else a for a in argv]
    mods = [m for m in mods if m != "MathlibLattice"]
    prep = {m: prepare(m) for m in mods}
    prep = {m: p for m, p in prep.items() if p[3]}
    results = {m: {d: {"closed_by": [], "citation": None} for d in p[3]} for m, p in prep.items()}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(run_job, m, t, p[0], p[1], p[2]): (m, t)
                for m, p in prep.items() for t in TACTICS}
        for fut in concurrent.futures.as_completed(futs):
            m, t = futs[fut]
            bad, sugg = fut.result()
            targets = prep[m][3]
            for d in targets:
                if d not in bad and None not in bad:
                    results[m][d]["closed_by"].append(t)
                    if t == "exact?" and d in sugg:
                        results[m][d]["citation"] = sugg[d]
            n = sum(1 for d in targets if d not in bad and None not in bad)
            print("  %s: %s closes %d/%d" % (m, t, n, len(targets)), flush=True)
    allres = []
    for m in mods:
        if m not in results:
            continue
        for d, r in results[m].items():
            r["closed_by"].sort(key=TACTICS.index)
            allres.append({"module": m, "line": d[0], "name": d[1], "kind": d[2],
                           "closed_by": r["closed_by"], "citation": r["citation"]})
    if out:
        with open(out, "w", encoding="utf-8") as f:
            json.dump(allres, f, indent=1, ensure_ascii=False)
    else:
        print(json.dumps(allres, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main(sys.argv[1:])
