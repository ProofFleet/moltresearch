import MoltResearch.Discrepancy

/-!
# Tao 2015: Erdős discrepancy theorem (Track C / conjectures-only)

This file is **Conjectures-only**: it may contain `sorry`.

Track C goal: make the Tao 2015 proof pipeline explicit as a chain of *typed interfaces*.
We keep everything here (under `Conjectures/`) while the architecture is still evolving.

Hard rule reminder: nothing here should modify the verified substrate under `MoltResearch/`.
-/

namespace MoltResearch
namespace Tao2015

/-!
## Tiny rewrite glue: shift ↔ offset sums

These are small, but they are the connective tissue of many reductions.
We keep them here (not in `MoltResearch/`) as “pipeline ergonomics”.
-/

/-- Shifting the index preserves the sign-sequence property. -/
theorem IsSignSequence.shift_add {f : ℕ → ℤ} (hf : IsSignSequence f) (a : ℕ) :
    IsSignSequence (fun k => f (k + a)) := by
  intro k
  simpa using hf (k + a)

/-- A common special case: shift by a multiple `m*d`. -/
theorem IsSignSequence.shift_add_mul {f : ℕ → ℤ} (hf : IsSignSequence f) (m d : ℕ) :
    IsSignSequence (fun k => f (k + m * d)) := by
  simpa using (IsSignSequence.shift_add (f := f) hf (a := m * d))

/-- A shifted homogeneous AP sum is an offset AP sum. -/
theorem apSum_shift_add_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  -- The library lemma is oriented in the reverse direction.
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Discrepancy version of `apSum_shift_add_mul_eq_apSumOffset`. -/
theorem discrepancy_shift_add_mul_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    discrepancy (fun k => f (k + m * d)) d n = discOffset f d m n := by
  -- Avoid `simp` loops by unfolding the wrappers explicitly.
  unfold discrepancy discOffset
  simpa using congrArg Int.natAbs
    (apSum_shift_add_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-!
## Fixed-step boundedness (local predicate)

Many intermediate reductions work at a single step-size `d`. We package this as a local
predicate; it may later be refined/moved.
-/

def BoundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discrepancy f d n ≤ B

/-- Unboundedness along a fixed `d` rewritten into a witness-normal form. -/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g : ℕ → ℤ) (d : ℕ) :
    (¬ BoundedDiscrepancyAlong g d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n) := by
  classical
  constructor
  · intro hnot B
    by_contra hcontra
    have hle : ∀ n : ℕ, discrepancy g d n ≤ B := by
      intro n
      have : ¬ B < discrepancy g d n := by
        intro hlt
        exact hcontra ⟨n, hlt⟩
      exact le_of_not_gt this
    exact hnot ⟨B, hle⟩
  · intro hforall hbd
    rcases hbd with ⟨B, hB⟩
    rcases hforall B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn

/-!
## Stage-1 reduction interface (the “plane” foundation)

This is the first nontrivial *consumer-facing* API for the proof pipeline.
It packages:
- a derived sign sequence `g`
- parameters `d,m` with `d>0`
- an AP-sum rewrite contract `apSum g d = apSumOffset f d m`
- a discrepancy transfer contract, so consumers can work on either side interchangeably.

Downstream stages should depend on this interface instead of re-proving shift/offset rewrites.
-/

structure ReductionOutput (f : ℕ → ℤ) : Type where
  d : ℕ
  m : ℕ
  hd : d > 0
  g : ℕ → ℤ
  hg : IsSignSequence g
  /-- Defining equation: `g` is (currently) just a shift of `f` by `m*d`. -/
  g_eq : g = fun k => f (k + m * d)
  /-- Main rewrite rule for homogeneous sums. -/
  apSum_contract : ∀ n : ℕ, apSum g d n = apSumOffset f d m n
  /-- Transfer contract: uniform bounds on the offset discrepancy transfer to bounds on `g`. -/
  contract_discrepancy_le :
    ∀ B : ℕ, (∀ n : ℕ, discOffset f d m n ≤ B) → ∀ n : ℕ, discrepancy g d n ≤ B

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-- Discrepancy is rewritten to the offset discrepancy by the stage-1 contract. -/
theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Unfold wrappers and use the AP-sum contract.
  unfold discrepancy discOffset
  simpa using congrArg Int.natAbs (out.apSum_contract n)

/-- Default constructor: build `ReductionOutput` from a literal shift `g k := f (k + m*d)`. -/
def mk_of_shift (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    ReductionOutput f := by
  classical
  refine
    { d := d
      m := m
      hd := hd
      g := fun k => f (k + m * d)
      hg := IsSignSequence.shift_add_mul (f := f) hf m d
      g_eq := rfl
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · intro n
    simpa using (apSum_shift_add_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))
  · intro B hB n
    -- `discrepancy (shift f) = discOffset f` and we can transfer bounds by rewriting.
    calc
      discrepancy (fun k => f (k + m * d)) d n = discOffset f d m n :=
        discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)
      _ ≤ B := hB n

end ReductionOutput

/-!
## Top-level Tao2015 theorem stub

Track C is building the pipeline; the actual proof is filled in incrementally.
For now we expose the one theorem consumed by `ErdosDiscrepancy.lean`.
-/

theorem tao2015_not_boundedDiscrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  -- TODO (Track C): implement the Tao 2015 reduction chain.
  sorry

end Tao2015

/-- Re-export: the Tao2015 proof skeleton’s main output, in the `MoltResearch` namespace.

`ErdosDiscrepancy.lean` expects this name without the `Tao2015.` prefix.
-/
theorem tao2015_not_boundedDiscrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f :=
  Tao2015.tao2015_not_boundedDiscrepancy (f := f) (hf := hf)

end MoltResearch
