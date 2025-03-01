import Mathlib
theorem foo (a b c d : ℕ) (det : a * d = b * c + 1) : (a + c).gcd (b + d) = 1 := by
  -- Assume for contradiction that gcd(a + c, b + d) = k > 1.
  apply Nat.eq_one_of_dvd_one
  -- Use the given equation ad = bc + 1 to derive a contradiction.
  apply Nat.dvd_of_mod_eq_zero
  -- Simplify the congruences based on the divisibility assumption.
  rw [← Nat.mod_add_div (a + c) (b + d)]
  -- Substitute the congruences into the original equation and simplify.
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_eq_of_lt, Nat.succ_pos] at det ⊢
  -- Use the omega tactic to solve the resulting linear congruence.
  omega
