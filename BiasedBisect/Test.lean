import Mathlib
def zerosVec : (n : ℕ) → Fin n → (ℕ × ℕ)
| 0 => ![]
| (n+1) => Matrix.vecCons (0,0) (zerosVec n)

example (n : Nat) : ∀ (i : Fin n), (zerosVec n) i = (0, 0) := by
  induction n using zerosVec.induct with
  | case1 => simp only [Prod.mk_zero_zero, IsEmpty.forall_iff]
  | case2 n h =>
    intro i
    rw [zerosVec]
    induction i using Fin.induction with
    | zero => simp only [Prod.mk_zero_zero, Matrix.cons_val_zero]
    | succ i =>
      simp only [Prod.mk_zero_zero, Matrix.cons_val_succ]
      exact h i
