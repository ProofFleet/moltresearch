import MoltResearch.Discrepancy

/-!
# Tao 2015 (Track C): Erdős discrepancy proof skeleton — Stage-1 API

This module is **Conjectures-only**: it may contain `sorry`, but it should *compile*.

Design goal: provide a small, stable interface (`Tao2015.ReductionOutput`) that packages the
pure “index gymnastics” reduction used by later Track C stages.

We intentionally keep this file lightweight: it is glue around the verified discrepancy nucleus in
`MoltResearch.Discrepancy`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Small helper API: sign sequences are stable under shifts
-/

namespace IsSignSequence

/-- Shifting the index preserves the sign-sequence property. -/
theorem shift_add {f : ℕ → ℤ} (hf : IsSignSequence f) (a : ℕ) :
    IsSignSequence (fun k => f (k + a)) := by
  intro k
  simpa using hf (k + a)

/-- A common special case: shift by a multiple `m*d`. -/
theorem shift_add_mul {f : ℕ → ℤ} (hf : IsSignSequence f) (m d : ℕ) :
    IsSignSequence (fun k => f (k + m * d)) := by
  simpa using (shift_add (f := f) hf (a := m * d))

end IsSignSequence

/-!
## Tiny congruence helpers
-/

/-- `apSum` respects pointwise equality of the underlying sequence. -/
theorem apSum_congr {f g : ℕ → ℤ} (h : ∀ k, f k = g k) (d n : ℕ) : apSum f d n = apSum g d n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact h _

/-!
## Bridge lemmas: shifting ↔ offset sums; offset ↔ affine sums

These are lightweight wrappers around verified substrate bridge lemmas.
-/

/-- A shifted homogeneous AP sum is an offset AP sum. -/
theorem apSum_shift_add_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  -- In the substrate, the canonical orientation is `apSumOffset = apSum (shift ...)`.
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Reverse orientation of `apSum_shift_add_mul_eq_apSumOffset`. -/
theorem apSumOffset_eq_apSum_shift_add_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Offset AP sum as an affine AP sum starting at `m*d`. -/
theorem apSumOffset_eq_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumFrom f (m * d) d n := by
  -- Specialize the bridge lemma with `a = 0`.
  simpa using
    (apSumOffset_shift_add_eq_apSumFrom_bridge (f := f) (a := 0) (d := d) (m := m) (n := n))

/-- `Int.natAbs` form of `apSumOffset_eq_apSumFrom_mul`. -/
theorem natAbs_apSumOffset_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) = Int.natAbs (apSumFrom f (m * d) d n) := by
  exact congrArg Int.natAbs (apSumOffset_eq_apSumFrom_mul (f := f) (d := d) (m := m) (n := n))

/-- Rewrite `discOffset` in terms of the affine AP-sum nucleus `apSumFrom`. -/
theorem discOffset_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumFrom f (m * d) d n) := by
  -- `discOffset` is definitionally `Int.natAbs (apSumOffset ...)`.
  unfold discOffset
  exact natAbs_apSumOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)

/-!
## Context: packaging global bounded discrepancy

`BoundedDiscrepancy` is in the verified substrate.  This record is just a convenient way to
thread around a chosen bound `B` and its corresponding bound lemma.
-/

structure Context (f : ℕ → ℤ) : Type where
  B : ℕ
  bound_apSum : ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B

namespace Context

variable {f : ℕ → ℤ}

/-- Build a `Context f` from a bounded-discrepancy witness. -/
noncomputable def ofBoundedDiscrepancy (hb : BoundedDiscrepancy f) : Context f := by
  classical
  refine ⟨Classical.choose hb, ?_⟩
  simpa using (Classical.choose_spec hb)

/-- Bound offset sums using the global `Context` bound, with the standard factor-2 loss. -/
theorem bound_apSumOffset (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSumOffset f d m n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset = apSum (m+n) - apSum m`.
  calc
    Int.natAbs (apSumOffset f d m n)
        = Int.natAbs (apSum f d (m + n) - apSum f d m) := by
          simp [apSumOffset_eq_sub]
    _ ≤ Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) := by
          simpa using (Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m))
    _ ≤ ctx.B + ctx.B := by
          exact Nat.add_le_add (ctx.bound_apSum (d := d) (n := m + n) hd)
            (ctx.bound_apSum (d := d) (n := m) hd)

/-- Offset-sum bound in terms of the discrepancy wrapper `discOffset`, with factor 2. -/
theorem bound_discOffset_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ 2 * ctx.B := by
  -- `2*B = B+B`.
  have : discOffset f d m n ≤ ctx.B + ctx.B := by
    -- `discOffset` is definitionally `Int.natAbs (apSumOffset ...)`.
    unfold discOffset
    exact ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd
  simpa [two_mul] using this

end Context

/-!
## Fixed-step bounded/unbounded discrepancy normal forms
-/

/-- Bounded discrepancy along a *fixed* step size `d`. -/
def BoundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discrepancy f d n ≤ B

/-- Unbounded discrepancy along a *fixed* step size `d` (witness form). -/
def UnboundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discrepancy f d n

/-- “Discrepancy at least `C`” along a fixed step size `d`. -/
def HasDiscrepancyAtLeastAlong (f : ℕ → ℤ) (d C : ℕ) : Prop :=
  ∃ n : ℕ, discrepancy f d n > C

namespace HasDiscrepancyAtLeastAlong

/-- `∀ C, HasDiscrepancyAtLeastAlong` is just the unbounded witness form. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong f d C) ↔ UnboundedDiscrepancyAlong f d := by
  constructor
  · intro h B
    simpa [HasDiscrepancyAtLeastAlong, UnboundedDiscrepancyAlong] using h B
  · intro h C
    simpa [HasDiscrepancyAtLeastAlong, UnboundedDiscrepancyAlong] using h C

end HasDiscrepancyAtLeastAlong

namespace UnboundedDiscrepancyAlong

/-- Unboundedness is the negation of boundedness (fixed-step version). -/
theorem iff_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ ¬ BoundedDiscrepancyAlong f d := by
  classical
  constructor
  · intro hunb hb
    rcases hb with ⟨B, hB⟩
    rcases hunb B with ⟨n, hn⟩
    exact (not_le_of_gt hn) (hB n)
  · intro hnb B
    by_contra h
    have hB : ∀ n : ℕ, discrepancy f d n ≤ B := by
      intro n
      have : ¬ B < discrepancy f d n := by
        intro hn
        exact h ⟨n, hn⟩
      exact le_of_not_gt this
    exact hnb ⟨B, hB⟩

end UnboundedDiscrepancyAlong

/-- Unbounded offset discrepancy witness form. -/
def UnboundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n

/-!
## Stage 1: packaged shift reduction output
-/

structure ReductionOutput (f : ℕ → ℤ) : Type where
  g : ℕ → ℤ
  d : ℕ
  m : ℕ
  hd : d > 0
  hg : IsSignSequence g
  g_eq : ∀ k : ℕ, g k = f (k + m * d)

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-- Canonical Stage-1 reduction: `g k := f (k + m*d)`. -/
def ofShift (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) : ReductionOutput f := by
  refine
    { g := fun k => f (k + m * d)
      d := d
      m := m
      hd := hd
      hg := IsSignSequence.shift_add_mul (f := f) hf m d
      g_eq := ?_ }
  intro k
  rfl

/-- `apSum` contract: the reduced homogeneous sum equals the original offset sum. -/
theorem apSum_eq_apSumOffset_via_contract (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumOffset f out.d out.m n := by
  have hfun : ∀ k : ℕ, out.g k = (fun t => f (t + out.m * out.d)) k := by
    intro k
    simpa using out.g_eq k
  -- Rewrite `apSum out.g` to `apSum (shift f)`, then use the bridge lemma.
  calc
    apSum out.g out.d n = apSum (fun t => f (t + out.m * out.d)) out.d n := by
      simpa using (apSum_congr (f := out.g) (g := fun t => f (t + out.m * out.d)) hfun out.d n)
    _ = apSumOffset f out.d out.m n :=
      apSum_shift_add_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n)

/-- Discrepancy contract: the reduced discrepancy equals the bundled offset discrepancy. -/
theorem discrepancy_eq_discOffset_via_contract (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Unfold both wrappers and use the `apSum` contract.
  change Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n)
  simpa using congrArg Int.natAbs (out.apSum_eq_apSumOffset_via_contract (f := f) n)

/-- Transfer a uniform bound on the bundled offset discrepancies to the reduced discrepancies. -/
theorem contract_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hB n

/-- Consumer-facing normal form: `HasDiscrepancyAtLeastAlong` for the reduced sequence is an
`apSumFrom` witness for the original sequence. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Rewrite `discrepancy out.g` to `discOffset f`, then to `natAbs(apSumFrom ...)`.
    have : discOffset f out.d out.m n > C := by
      -- `hn : discrepancy out.g out.d n > C`.
      simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hn
    -- Now rewrite `discOffset` through the affine nucleus.
    simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using this
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Rewrite back to `discOffset` then transport via the contract.
    have : discOffset f out.d out.m n > C := by
      simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hn
    simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using this

/-- Unbounded discrepancy along the reduced fixed step rewritten as explicit offset-discrepancy witnesses. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  constructor
  · intro hunb B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hn
  · intro hunb B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hn

/-- Variant of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt` expanding `discOffset`. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  constructor
  · intro hunb B
    rcases ((out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)).1 hunb B) with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Unfold `discOffset` in the witness.
    unfold discOffset at hn
    exact hn
  · intro hunb
    -- Convert to the `discOffset` witness form, then refold.
    refine (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)).2 ?_
    intro B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold discOffset
    exact hn

/-- If the bundled offset discrepancy family is unbounded, then `f` is not globally bounded. -/
theorem not_boundedDiscrepancy_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (hunb : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    ¬ BoundedDiscrepancy f := by
  intro hb
  classical
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  have hbound : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    exact ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  rcases hunb (2 * ctx.B) with ⟨n, hn⟩
  exact (not_le_of_gt hn) (hbound n)

end ReductionOutput

end Tao2015

end MoltResearch
