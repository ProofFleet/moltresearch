import Mathlib

theorem T0_06 (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp =>
      right
      exact hp
  | inr hq =>
      left
      exact hq
