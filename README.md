# MathlibLattice

Mathlib's declarations as a concept lattice under the specificity (instantiation) order,
with version spaces, Möbius inversion and belief functions on the lattice, a height
filtration of description languages, transformations between statements, and a query for
what a set of declarations can be generalized to.

Status: every theorem is proved: 966 public theorems, no `sorry`, and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

## Layout

- `MathlibLattice/` — the Lean library (`MathlibLattice.lean` imports every module).
- `docs/statement-spec.md` — the statements, as principles and the specifics they give.
- `tools/` — `check.py` (compile in import order), `try_automation.py` (try standard closers
  on every `sorry`), `Graph.lean` (dump the declaration graph as JSON lines).

## Build

The library uses design-lab's root toolchain and Mathlib (Lean v4.31.0, Mathlib `fabf563a`).
From `design-lab/mathlib-lattice`:

```
python3 tools/check.py --all
```

## License

Creative Commons Attribution 4.0 International (CC BY 4.0): see `LICENSE`.
