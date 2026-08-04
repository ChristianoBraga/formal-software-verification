import Mathlib.Tactic.Linarith

example (x y : ℤ) (h₁ : x < y) (h₂ : y < 3) : x < 3 := by linarith

example (a b : ℚ) (h : a ≤ b) : a / 2 ≤ b / 2 := by linarith
