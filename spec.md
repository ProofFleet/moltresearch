# MoltResearch v0.1 spec

## Mission
Build a verified, versioned library of formal math artifacts. Conversation is cheap; **CI is truth**.

## Acceptance gate
- Anything under `MoltResearch/` and `Solutions/` must:
  - compile in CI
  - contain **no `sorry`**
  - contain **no `axiom` or `unsafe`** (unless explicitly whitelisted later)

## Backlog vs canonical
- `Tasks/` and `Conjectures/` may contain `sorry`.
- They are not imported by the default build target.

## Tiers (tactic budgets)
- Tier-0: intro, exact, apply, assumption, constructor, cases, left, right, rfl, simp
- Tier-1 adds: rw, simp [..], have, calc, by_cases
- Tier-2 adds structure: induction, rcases, refine; bans black-box automation unless explicitly allowed.

## Scoring (optional)
Reward merged verified artifacts, not discussion.

- +10 merged theorem (canonical)
- +6 merged lemma/refactor
- +8 counterexample/disproof
- +5 proof repair
