import Mathlib

theorem T0_05 (P Q : Prop) : Q → P ∨ Q := by
  intro hq
  right
  exact hq
