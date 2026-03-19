import MoltResearch.Discrepancy

/-!
# Tao 2015: Erdős discrepancy theorem (Track C proof skeleton)

This module is **Conjectures-only** glue: it may contain `sorry`.

Hard requirement for Track C automation: this module must compile so that

`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`

builds cleanly.

Scope policy:
- Keep the API surface *small* and typed: records for stage boundaries, plus a few transport lemmas.
- Prefer reusing the verified discrepancy substrate (`MoltResearch/Discrepancy/*.lean`) rather than
  re-stating it here.
- Avoid `simp` loops: do **not** unfold `discrepancy`/`discOffset` inside `simp`.
-/

namespace MoltResearch

namespace Tao2015

set_option autoImplicit false

/-!
## Packaging boundedness as data (`Context`)

`BoundedDiscrepancy f` is an existential.  For later stage boundaries it is convenient to package
its witness `B` and the bound lemma as a single object.
-/

/-- Data form of `BoundedDiscrepancy`: a witness bound plus its proof. -/
structure Context (f : ℕ → ℤ) : Type where
  B : ℕ
  bound : ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B

/-- Extract a `Context` from a boundedness hypothesis.

Noncomputable: we use classical choice to pick the witness bound.
-/
noncomputable def Context.ofBoundedDiscrepancy {f : ℕ → ℤ} (hb : BoundedDiscrepancy f) :
    Context f := by
  classical
  refine ⟨Classical.choose hb, ?_⟩
  simpa using (Classical.choose_spec hb)

namespace Context

variable {f : ℕ → ℤ}

/-- Turn `Context f` back into `BoundedDiscrepancy f`. -/
theorem toBoundedDiscrepancy (ctx : Context f) : BoundedDiscrepancy f := by
  refine ⟨ctx.B, ?_⟩
  intro d n hd
  exact ctx.bound d n hd

/-- Convenience: the homogeneous AP-sum bound. -/
theorem bound_apSum (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    Int.natAbs (apSum f d n) ≤ ctx.B :=
  ctx.bound d n hd

/-- Global bounded discrepancy implies a uniform bound on any fixed offset discrepancy.

The factor `2` comes from writing an offset sum as a difference of two prefix sums.
-/
theorem bound_discOffset_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ 2 * ctx.B := by
  -- `discOffset` is a wrapper around `Int.natAbs (apSumOffset ...)`.
  unfold discOffset

  -- Rewrite the offset nucleus as a difference of homogeneous prefix sums.
  -- Then apply `|x-y| ≤ |x| + |y|` and the `Context` bounds.
  have hsub :
      Int.natAbs (apSum f d (m + n) - apSum f d m) ≤
        Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) :=
    Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m)

  have h₁ : Int.natAbs (apSum f d (m + n)) ≤ ctx.B :=
    ctx.bound_apSum (d := d) (n := m + n) hd

  have h₂ : Int.natAbs (apSum f d m) ≤ ctx.B :=
    ctx.bound_apSum (d := d) (n := m) hd

  have hsum :
      Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) ≤ ctx.B + ctx.B :=
    Nat.add_le_add h₁ h₂

  have h : Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ ctx.B + ctx.B :=
    le_trans hsub hsum

  have h' : Int.natAbs (apSumOffset f d m n) ≤ ctx.B + ctx.B := by
    simpa [apSumOffset_eq_sub] using h

  -- `2 * B = B + B`.
  simpa [two_mul] using h'

end Context

/-!
## Fixed-step boundedness / unboundedness

These are tiny, Conjectures-only normal forms that downstream stage boundaries consume.
-/

/-- Existential boundedness along a fixed step size `d`. -/
def BoundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discrepancy g d n ≤ B

/-- Witness normal form of unbounded discrepancy along a fixed step size `d`. -/
def UnboundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n

namespace UnboundedDiscrepancyAlong

/-- Unboundedness witness form is logically equivalent to `¬ BoundedDiscrepancyAlong`. -/
theorem iff_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ ¬ BoundedDiscrepancyAlong f d := by
  classical
  constructor
  · intro hunb hb
    rcases hb with ⟨B, hB⟩
    rcases hunb B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n) hn)
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

namespace HasDiscrepancyAtLeastAlong

/-- Relate the `∀ C, HasDiscrepancyAtLeastAlong ... C` packaging to the witness normal form used
in Track C (`UnboundedDiscrepancyAlong`).

This lemma lives in `Conjectures/` because `BoundedDiscrepancyAlong` is also Conjectures-only.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C) ↔ Tao2015.UnboundedDiscrepancyAlong g d := by
  -- Both sides are `∀ C, ∃ n, C < discrepancy ...` after rewriting `>` as `<`.
  unfold Tao2015.UnboundedDiscrepancyAlong HasDiscrepancyAtLeastAlong
  simp [gt_iff_lt]

end HasDiscrepancyAtLeastAlong

/-- Witness normal form of unbounded offset discrepancy (fixed `d,m`). -/
def UnboundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n

/-!
## Stage 1 boundary: shift reduction output

For now the only Stage-1 reduction we expose is a literal shift by `m*d`:
`g k = f (k + m*d)`.

This suffices for the current Track C stage boundary files.
-/

/-- Stage-1 output: a reduced sequence `g` (a shift of `f`) together with the parameters used.

The record fields are intentionally minimal: `g_eq` is the core contract.
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

/-- Canonical Stage-1 reduction: shift by `m*d` (keeping the same step size `d`). -/
def ofShift (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) : ReductionOutput f := by
  refine
    { g := fun k => f (k + m * d)
      d := d
      m := m
      hd := hd
      hg := IsSignSequence.shift_add (k := m * d) (hf := hf)
      g_eq := ?_ }
  intro k
  rfl

/-- Core contract: discrepancy of the reduced sequence is the corresponding offset discrepancy of `f`. -/
theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Avoid `simp [discOffset]` (it can loop); unfold the wrapper explicitly.
  unfold discOffset
  -- Rewrite `out.g` as the literal shift, then apply the verified shift lemma directly.
  have hgfun : out.g = (fun k => f (k + out.m * out.d)) := funext out.g_eq
  -- Now the goal matches `discrepancy_shift_mul`.
  -- (No `simpa`: `discrepancy_shift_mul` is a simp lemma and `simpa using` can collapse it to `True`.)
  rw [hgfun]
  exact discrepancy_shift_mul (f := f) (a := out.m) (d := out.d) (n := n)

/-- Boundedness transport: a uniform `discOffset` bound implies the corresponding `discrepancy` bound
for the reduced sequence. -/
theorem contract_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) (n : ℕ) :
    discrepancy out.g out.d n ≤ B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Rewrite the reduced discrepancy nucleus into the affine-tail nucleus `apSumFrom`. -/
theorem discrepancy_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  -- Start from the core contract `discrepancy = discOffset`, then unfold `discOffset`.
  have h₁ : discrepancy out.g out.d n = discOffset f out.d out.m n :=
    out.discrepancy_eq_discOffset (f := f) (n := n)
  unfold discOffset at h₁

  -- Bridge `apSumOffset` to `apSumFrom` (specializing the verified bridge with `a = 0`).
  have h₂ : Int.natAbs (apSumOffset f out.d out.m n) =
      Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
    simpa using
      (natAbs_apSumOffset_shift_add_eq_natAbs_apSumFrom_bridge
        (f := f) (a := 0) (d := out.d) (m := out.m) (n := n))

  exact h₁.trans h₂

/-- Consumer-facing contract: along-`d` discrepancy witnesses for the reduced sequence are
exactly affine-tail witnesses for the original sequence.

This is the Stage-1 “nucleus boundary” used by later stages.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn

/-- Unboundedness transport: reduced unbounded discrepancy rewrites to explicit `discOffset` witnesses
for the original sequence at `(d,m)`. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  constructor
  · intro hunb B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' := hn
    -- Rewrite the reduced discrepancy into the original offset discrepancy.
    rw [out.discrepancy_eq_discOffset (f := f) (n := n)] at hn'
    exact hn'
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' := hn
    -- Rewrite back.
    rw [← out.discrepancy_eq_discOffset (f := f) (n := n)] at hn'
    exact hn'

/-- Variant of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt` exposing the raw nucleus
`apSumOffset` under `Int.natAbs`. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  -- Derive from the `discOffset` witness form by unfolding `discOffset` (definitional).
  have h := out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)
  constructor
  · intro hunb B
    rcases (h.mp hunb) B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
    unfold discOffset at hn
    exact hn
  · intro hunb
    apply h.mpr
    intro B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    unfold discOffset
    exact hn

/-- If we have arbitrarily large offset discrepancies for `f` at `(out.d, out.m)`, then `f` is
not globally bounded (i.e. `¬ BoundedDiscrepancy f`).

This is the proved boundary used by Stage 3.
-/
theorem not_boundedDiscrepancy_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (hunb : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    ¬ BoundedDiscrepancy f := by
  intro hb
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb

  -- Global boundedness gives a uniform offset bound (cost: factor `2`).
  have hbound : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    exact ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd

  -- Contradict the uniform bound using the unbounded witness family.
  rcases hunb (2 * ctx.B) with ⟨n, hn⟩
  exact (not_lt_of_ge (hbound n)) hn

end ReductionOutput

end Tao2015

end MoltResearch
