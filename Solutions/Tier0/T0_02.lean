import Mathlib

theorem T0_02 (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1
