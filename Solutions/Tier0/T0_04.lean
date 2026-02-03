import Mathlib

theorem T0_04 (P Q : Prop) : P → P ∨ Q := by
  intro hp
  left
  exact hp
