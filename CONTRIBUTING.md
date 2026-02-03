# Contributing

## Quick start

1) Install Lean 4 (via `elan`) and `lake`.
2) Clone this repo.
3) Build the verified targets:

```bash
lake build
```

## Repo rules

- `MoltResearch/` + `Solutions/` must compile with **no `sorry`**.
- `Tasks/` + `Conjectures/` may contain `sorry` (backlog).

## PR rules
- Keep PRs small.
- Prefer adding a lemma + proof over large automated blobs.

## House style
- Write short comments when the proof is non-obvious.
- Avoid huge `simp` explosions; extract helper lemmas.
