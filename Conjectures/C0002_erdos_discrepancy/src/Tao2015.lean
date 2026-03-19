import MoltResearch.Discrepancy

/-!
# Tao 2015: Erdős discrepancy theorem (Track C skeleton — Stage 1 API)

This module is **Conjectures-only**: it may contain `sorry`.

It provides the minimal, typed *stage-1 reduction interface* (`Tao2015.ReductionOutput`) and a
small amount of bounded/unbounded discrepancy glue used by the Track C stage boundaries.

Design rule: anything reusable/verified should live under `MoltResearch/Discrepancy/*`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Fixed-step boundedness / unboundedness

These are Track-C convenience wrappers (not part of the verified substrate).
-/

/-- Bounded discrepancy along a fixed step `d` (existential normal form). -/
def BoundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discrepancy f d n ≤ B

/-- A `ContextAlong f d` packages a uniform bound on `discrepancy f d n`. -/
structure ContextAlong (f : ℕ → ℤ) (d : ℕ) : Type where
  B : ℕ
  bound_discrepancy : ∀ n : ℕ, discrepancy f d n ≤ B

namespace ContextAlong

variable {f : ℕ → ℤ} {d : ℕ}

/-- Build a `ContextAlong` from the existential boundedness statement.

Note: this is noncomputable because it extracts data from a `Prop` witness.
-/
noncomputable def ofBoundedDiscrepancyAlong (h : BoundedDiscrepancyAlong f d) : ContextAlong f d :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Turn `ContextAlong` back into the existential boundedness statement. -/
theorem toBoundedDiscrepancyAlong (ctx : ContextAlong f d) : BoundedDiscrepancyAlong f d :=
  ⟨ctx.B, ctx.bound_discrepancy⟩

/-- Nucleus-level bound: `|apSum|` is bounded whenever `discrepancy` is bounded. -/
theorem bound_natAbs_apSum (ctx : ContextAlong f d) (n : ℕ) :
    Int.natAbs (apSum f d n) ≤ ctx.B := by
  -- Avoid simp loops between `discrepancy` and `Int.natAbs (apSum ...)`.
  simpa [discrepancy, -natAbs_apSum_eq_discrepancy] using (ctx.bound_discrepancy n)

end ContextAlong

/-- Track-C alias: unbounded discrepancy along `d`.

This is definitionally the same as `MoltResearch.UnboundedDiscrepancyAlong`.
-/
abbrev UnboundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  _root_.MoltResearch.UnboundedDiscrepancyAlong f d

/-- Unbounded *offset* discrepancy witness family (at fixed parameters `d,m`). -/
def UnboundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n

namespace UnboundedDiscrepancyAlong

/-- Unbounded discrepancy along `d` is equivalent to *not* being bounded along `d`.

The `→` direction is constructive; the `←` direction uses classical logic.
-/
theorem iff_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ ¬ BoundedDiscrepancyAlong f d := by
  classical
  constructor
  · intro hunb hbd
    rcases hbd with ⟨B, hB⟩
    -- `hunb B` gives `∃ n, discrepancy f d n > B`.
    rcases (hunb B) with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn
  · intro hnb C
    -- If all discrepancies were ≤ C, we'd have boundedness with bound C.
    by_contra h
    have hle : ∀ n : ℕ, discrepancy f d n ≤ C := by
      intro n
      have : ¬ discrepancy f d n > C := by
        intro hgt
        exact h ⟨n, hgt⟩
      exact le_of_not_gt this
    exact hnb ⟨C, hle⟩

end UnboundedDiscrepancyAlong

namespace HasDiscrepancyAtLeastAlong

/-- Definitional bridge: `UnboundedDiscrepancyAlong` is literally `∀ C, HasDiscrepancyAtLeastAlong`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C) ↔ Tao2015.UnboundedDiscrepancyAlong g d :=
  Iff.rfl

end HasDiscrepancyAtLeastAlong

/-!
## Global boundedness context

We use the verified predicate `BoundedDiscrepancy` (from `MoltResearch.Discrepancy.Unbounded`) but
package its witness as a record so downstream code can carry around a single object.
-/

/-- A global boundedness witness packaged as a record. -/
structure Context (f : ℕ → ℤ) : Type where
  B : ℕ
  bound_natAbs_apSum : ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B

namespace Context

variable {f : ℕ → ℤ}

/-- Build a `Context` from `BoundedDiscrepancy f`.

Note: this is noncomputable because it extracts data from a `Prop` witness.
-/
noncomputable def ofBoundedDiscrepancy (f : ℕ → ℤ) (hb : BoundedDiscrepancy f) : Context f :=
  ⟨Classical.choose hb, Classical.choose_spec hb⟩

/-- Convenience: bound `discrepancy` from a `Context`. -/
theorem bound_discrepancy (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    discrepancy f d n ≤ ctx.B := by
  simpa [discrepancy, -natAbs_apSum_eq_discrepancy] using (ctx.bound_natAbs_apSum d n hd)

/-- A global discrepancy bound yields a `2*B` bound on all offset discrepancies.

Reason: an offset sum is a difference of two prefix sums.
-/
theorem bound_discOffset_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ 2 * ctx.B := by
  -- Expand `discOffset` and rewrite `apSumOffset` as a difference of two `apSum`s.
  unfold discOffset
  -- `apSumOffset f d m n = apSum f d (m+n) - apSum f d m`.
  rw [apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)]
  -- Triangle inequality for subtraction.
  have htri :
      Int.natAbs (apSum f d (m + n) - apSum f d m) ≤
        Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) := by
    simpa using (Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m))
  have h₁ : Int.natAbs (apSum f d (m + n)) ≤ ctx.B := ctx.bound_natAbs_apSum d (m + n) hd
  have h₂ : Int.natAbs (apSum f d m) ≤ ctx.B := ctx.bound_natAbs_apSum d m hd
  have hsum :
      Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) ≤ ctx.B + ctx.B :=
    Nat.add_le_add h₁ h₂
  have hle :
      Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ ctx.B + ctx.B :=
    le_trans htri hsum
  -- Rewrite `ctx.B + ctx.B` as `2*ctx.B`.
  simpa [two_mul] using hle

end Context

/-!
## Stage 1 reduction interface

A `ReductionOutput f` packages a shift reduction from the original sequence `f` to a derived
sequence `g`, together with a fixed step size `d` and offset parameter `m`.

For Track C we only need the *shift-by-`m*d`* reduction.
-/

/-- Stage-1 reduction output (Track C).

`g` should be thought of as `k ↦ f (k + m*d)`.
-/
structure ReductionOutput (f : ℕ → ℤ) : Type where
  d : ℕ
  m : ℕ
  hd : d > 0
  g : ℕ → ℤ
  hg : IsSignSequence g
  g_eq : ∀ k : ℕ, g k = f (k + m * d)

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-- The canonical stage-1 reduction: literal shift by `m*d`.

This is the only constructor we currently expose in Track C.
-/
def ofShift (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) : ReductionOutput f := by
  refine
    { d := d
      m := m
      hd := hd
      g := fun k => f (k + m * d)
      hg := ?_
      g_eq := ?_ }
  · intro k
    simpa using hf (k + m * d)
  · intro k
    rfl

/-- A convenient extensional equality: `out.g` is the literal shift `k ↦ f (k + out.m*out.d)`.

This is primarily used to `simp` goals to the existing shift lemmas in the verified substrate.
-/
lemma g_eq_shift (out : ReductionOutput f) :
    out.g = fun k => f (k + out.m * out.d) := by
  funext k
  simpa using out.g_eq k

/-- Core stage-1 contract: discrepancy of the reduced sequence is the bundled offset discrepancy
of the original sequence.
-/
theorem discrepancy_eq_discOffset_via_contract (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Rewrite `out.g` to the literal shift and use the verified shift lemma.
  have hgEq : out.g = fun k => f (k + out.m * out.d) := out.g_eq_shift
  -- `discrepancy (shift) = natAbs (apSumOffset ...)` and `natAbs(apSumOffset)=discOffset` by simp.
  simpa [hgEq] using
    (_root_.MoltResearch.discrepancy_shift_mul (f := f) (a := out.m) (d := out.d) (n := n))

/-- Transfer a uniform `discOffset` bound into a uniform `discrepancy` bound for the reduced
sequence.
-/
theorem contract_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hB n

/-- Consumer-facing normal form: along-`d` discrepancy for the reduced sequence corresponds to an
`apSumFrom` witness for the original sequence.

This is the normal form most later analytic stages want.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  -- Reduce to a `discOffset` witness statement using the verified shift bridge.
  have hgEq : out.g = fun k => f (k + out.m * out.d) := out.g_eq_shift
  have hshift :
      HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
    -- `shift_mul_iff_exists_discOffset_lt` is in the verified substrate.
    simpa [hgEq] using
      (HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt
        (f := f) (d := out.d) (m := out.m) (C := C))
  -- Rewrite `discOffset` to `Int.natAbs (apSumFrom ...)` using the affine bridge lemma.
  constructor
  · intro h
    rcases (hshift.1 h) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Convert `<` to `>` and rewrite the nucleus.
    have hn' : Int.natAbs (apSumOffset f out.d out.m n) > C := by
      -- Unfold `discOffset` without looping.
      unfold discOffset at hn
      simpa [gt_iff_lt, -natAbs_apSumOffset_eq_discOffset] using hn
    -- Rewrite `apSumOffset` to `apSumFrom` (specialize the bridge lemma to `a = 0`).
    have hbridge : apSumOffset f out.d out.m n = apSumFrom f (out.m * out.d) out.d n := by
      simpa using
        (apSumOffset_shift_add_eq_apSumFrom_bridge (f := f) (a := 0) (d := out.d)
          (m := out.m) (n := n))
    -- Transport through `Int.natAbs`.
    simpa [hbridge] using hn'
  · rintro ⟨n, hn⟩
    -- Go back to `discOffset` witness form.
    have hn' : Int.natAbs (apSumOffset f out.d out.m n) > C := by
      -- Rewrite `apSumFrom` back to `apSumOffset`.
      have hbridge : apSumOffset f out.d out.m n = apSumFrom f (out.m * out.d) out.d n := by
        simpa using
          (apSumOffset_shift_add_eq_apSumFrom_bridge (f := f) (a := 0) (d := out.d)
            (m := out.m) (n := n))
      simpa [hbridge] using hn
    have hwit : ∃ n : ℕ, C < discOffset f out.d out.m n := by
      refine ⟨n, ?_⟩
      -- Repackage as `discOffset` (avoid simp loops).
      unfold discOffset
      simpa [gt_iff_lt, -natAbs_apSumOffset_eq_discOffset] using hn'
    exact hshift.2 hwit

/-- Unbounded discrepancy of the reduced sequence rewrites to an explicit `discOffset` witness
family for the original sequence.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔ (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  have hgEq : out.g = fun k => f (k + out.m * out.d) := out.g_eq_shift
  -- Use the verified shift bridge for unboundedness.
  simpa [hgEq, Tao2015.UnboundedDiscrepancyAlong] using
    (_root_.MoltResearch.UnboundedDiscrepancyAlong.shift_mul_iff_forall_exists_discOffset_lt
      (f := f) (d := out.d) (m := out.m))

/-- Variant of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt` exposing the raw nucleus
`apSumOffset` under `Int.natAbs`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ C : ℕ, ∃ n : ℕ, C < Int.natAbs (apSumOffset f out.d out.m n)) := by
  constructor
  · intro hunb C
    rcases (unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f) out).1 hunb C with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Unfold `discOffset` on the witness.
    unfold discOffset at hn
    simpa [-natAbs_apSumOffset_eq_discOffset] using hn
  · intro hunb
    -- Repackage back into `discOffset`.
    refine (unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f) out).2 ?_
    intro C
    rcases hunb C with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Fold `discOffset` back.
    unfold discOffset
    simpa [-natAbs_apSumOffset_eq_discOffset] using hn

/-- If we can produce arbitrarily large bundled offset discrepancy witnesses for `f` (at the
parameters `(out.d, out.m)`), then `f` cannot have globally bounded discrepancy.
-/
theorem not_boundedDiscrepancy_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (hunb : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    ¬ BoundedDiscrepancy f := by
  intro hb
  -- Extract the global bound and contradict it using the `2*B` offset bound.
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  -- From boundedness, every offset discrepancy is ≤ `2*ctx.B`.
  have hbd : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    exact ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  -- Choose a witness exceeding that bound.
  rcases hunb (2 * ctx.B) with ⟨n, hn⟩
  exact (not_lt_of_ge (hbd n)) hn

end ReductionOutput

end Tao2015

end MoltResearch
