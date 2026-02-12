import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.Offset

/-!
# Discrepancy bounds

This file provides simple triangle‑inequality bounds for the arithmetic‑progression sum
functions defined in `MoltResearch.Discrepancy.Affine`.  Given a uniform bound `B` on the
pointwise `Int.natAbs` of a function `f : ℕ → ℤ`, we show that the absolute value of the
sums is bounded by `n * B`.
-/

namespace MoltResearch

/-- Bound the absolute value of a finite sum over `Finset.range`. -/
lemma natAbs_sum_range_le_mul (g : ℕ → ℤ) (B : ℕ)
    (hB : ∀ i, Int.natAbs (g i) ≤ B) (n : ℕ) :
    Int.natAbs ((Finset.range n).sum g) ≤ n * B := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsum :
          Int.natAbs ((Finset.range (Nat.succ n)).sum g) ≤
            Int.natAbs ((Finset.range n).sum g) + Int.natAbs (g n) := by
        simpa [Finset.sum_range_succ] using
          (Int.natAbs_add_le ((Finset.range n).sum g) (g n))
      have hgn : Int.natAbs (g n) ≤ B := hB n
      have hbound :
          Int.natAbs ((Finset.range n).sum g) + Int.natAbs (g n) ≤ n * B + B :=
        Nat.add_le_add ih hgn
      have : Int.natAbs ((Finset.range (Nat.succ n)).sum g) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSum_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n * B := by
  simpa [apSum] using
    (natAbs_sum_range_le_mul (g := fun i => f ((i + 1) * d)) (B := B)
      (hB := fun i => hB ((i + 1) * d)) (n := n))

lemma natAbs_apSumOffset_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n * B := by
  simpa [apSumOffset] using
    (natAbs_sum_range_le_mul (g := fun i => f ((m + i + 1) * d)) (B := B)
      (hB := fun i => hB ((m + i + 1) * d)) (n := n))

lemma natAbs_apSum_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n * B := by
  have h := natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub] using h

lemma natAbs_apSumFrom_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) ≤ n * B := by
  simpa [apSumFrom] using
    (natAbs_sum_range_le_mul (g := fun i => f (a + (i + 1) * d)) (B := B)
      (hB := fun i => hB (a + (i + 1) * d)) (n := n))

lemma natAbs_apSumFrom_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d m n : ℕ) :
    Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ n * B := by
  have h := natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB)
    (a := a + m * d) (d := d) (n := n)
  simpa [apSumFrom_tail_eq_sub] using h

lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSum f d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨d, n, hd, hgt⟩
  have hle : Int.natAbs (apSum f d n) ≤ n * B :=
    natAbs_apSum_le_mul (f := f) (B := B) (hB := hB) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨d, n, hd, hnB, hgt⟩

lemma HasAffineDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨a, d, n, hd, hgt⟩
  have hle : Int.natAbs (apSumFrom f a d n) ≤ n * B :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨a, d, n, hd, hnB, hgt⟩

end MoltResearch
