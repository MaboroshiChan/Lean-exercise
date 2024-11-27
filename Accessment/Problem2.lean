import Mathlib

theorem binom_sym {n k: ℕ}(h: k ≤ n): n.choose k = n.choose (n - k) :=
  have h1: n - k ≤ n := by omega
  calc n.choose k = n.factorial / (k.factorial * (n - k).factorial) := by exact Nat.choose_eq_factorial_div_factorial h
                _ = n.factorial / (((k).factorial) * ((n - k).factorial)) := by linarith
                _ = n.factorial / (((n - k).factorial) * ((k).factorial)) := by rw [mul_comm]
                _ = n.factorial / (((n - k).factorial) * ((n - (n - k)).factorial)) := by rw [Nat.sub_sub_self h]
                _ = n.choose (n - k) := by exact (Nat.choose_eq_factorial_div_factorial h1).symm

example {n: ℕ}: n.choose 0 = n.choose n ∧ n.choose 0 = 1 :=
  have h: 0 ≤ n := by linarith
  have l: n.choose 0 = n.choose n := by exact (binom_sym h)
  have r: n.choose 0 = 1 := by
    calc n.choose 0 = n.factorial / ((0).factorial * (n - 0).factorial) := by exact Nat.choose_eq_factorial_div_factorial h
                _ = n.factorial / (1 * n.factorial) := by exact rfl
                _ = n.factorial / n.factorial := by rw [one_mul]
                _ = 1 := by exact Nat.div_self (Nat.pos_of_ne_zero (Nat.factorial_ne_zero n))
  And.intro l r
