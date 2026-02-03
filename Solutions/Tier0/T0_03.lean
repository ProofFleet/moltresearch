import Mathlib

theorem T0_03 (P Q : Prop) : P → Q → P ∧ Q := by
  intro hp hq
  constructor
  · exact hp
  · exact hq
