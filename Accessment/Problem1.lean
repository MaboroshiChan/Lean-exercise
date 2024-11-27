import Mathlib

open Finset BigOperators

#check Nat.mul_right_inj

#check Nat.mul_div_assoc

theorem p1 (a r : ℝ) (n : ℕ) (h : r ≠ 1) :
    a * r^(n + 1) = (a * r^(n + 1) * (r - 1))/(r - 1) := by
  have h1 : (r - 1)/(r - 1) = 1 := by
    exact div_self (sub_ne_zero.mpr h)
  calc a * r^(n + 1) = a * r^(n + 1) * 1 := by rw [mul_one]
    _ = a * r^(n + 1) * ((r - 1)/(r - 1)) := by rw [h1]
    _ = (a * r^(n + 1) * (r - 1))/(r - 1) := by field_simp [h]

theorem p2 (a r : ℝ) (n : ℕ) (h : r ≠ 1) :
  (a * r^(n + 1) - a) / (r - 1) + a * r^(n + 1) = (a * r^(n + 1 + 1) - a) / (r - 1) :=
  have h0 : r - 1 ≠ 0 := sub_ne_zero.mpr h
  have h1 : a * r^(n + 1) = (a * r^(n + 1) * (r - 1)) / (r - 1) := p1 a r n h
  calc
    (a * r^(n + 1) - a) / (r - 1) + a * r^(n + 1)
        = (a * r^(n + 1) - a) / (r - 1) + (a * r^(n + 1) * (r - 1)) / (r - 1) := by rw [←h1]
    _   = ((a * r^(n + 1) - a) + (a * r^(n + 1) * (r - 1))) / (r - 1)         := by rw [add_div]
    _   = (a * r^(n + 1) * r - a) / (r - 1)                                  := by ring
    _   = (a * r^(n + 1 + 1) - a) / (r - 1)                                      := by hint

-- Problem 1
example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) :=
  by induction n with
  | zero =>  
  simp
  have h0: r - 1 ≠ 0 := by exact sub_ne_zero.mpr h
  have h1 : a * r - a = a * (r - 1) := by ring
  have rhs: (a * r - a) / (r - 1) = a := by
    calc
      (a * r - a) / (r - 1) = (a * (r - 1)) / (r - 1) := by rw [h1]
                          _ = a * ((r - 1) / (r - 1)) := by rw [mul_div_assoc]
                          _ = a * 1                   := by rw [div_self h0]
                          _ = a                       := by rw [mul_one]
  apply Eq.symm
  exact rhs
  | succ n ith =>
    rw [Finset.sum_range_succ]
    rw[ith]
    have h2 := p2 a r n h
    exact h2
