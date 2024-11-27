import Mathlib

def f : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | (n + 3) => f (n + 2) + 2 * f (n + 1)


theorem f_closed_form (n : ℕ) : f (n + 1) = 2^(n + 1) + (-1)^(n + 1) := by
  induction' n using Nat.twoStepInduction with k IH1 IH2
  . calc f 1 = 1 := by rw [f]
    _ = 2^(0 + 1) + (-1)^(0 + 1) := by rfl
  . calc f 2 = 5 := by rw [f]
    _ = 2^(1 + 1) + (-1)^(1 + 1) := by rfl
  . calc f (k + 3) = f (k + 2) + 2 * f (k + 1) := by rw [f]
    _ = (2 ^ (k + 2) + (-1)^(k + 2)) + 2 * (2 ^ (k + 1) + (-1)^(k + 1)) := by rw [IH1, IH2]
    _ = 2 ^ (k + 3) + (-1)^(k + 3) := by ring
