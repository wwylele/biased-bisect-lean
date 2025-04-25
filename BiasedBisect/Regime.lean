import BiasedBisect.Inert

import Mathlib.Data.Nat.Factorial.Basic

lemma J_sum (p n: ℕ): ∑q ∈ Finset.range (n + 1), Jₚ (p, q) = Jₚ (p + 1, n) := by
  induction n with
  | zero =>
    unfold Jₚ
    simp
  | succ n prev =>
    rw [Finset.sum_range_add, prev, Finset.sum_range_one, Jₚ_rec]



lemma nBranchingFormula' (s t: ℕ+) :
nBranching s t = 1 + ∑ p ∈ Finset.range t, Jₚ (p + 1, (s * (t - p) - 1) / t) := by
  unfold nBranching
  have : (Λtriangle s t).toFinset = ΛtriangleFinset s t :=
    Set.toFinset_ofFinset (ΛtriangleFinset s t) (Λtriangle_is_Finset s t)
  rw [this]
  unfold ΛtriangleFinset
  rw [Finset.sum_biUnion (by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    aesop
  )]
  simp only [Finset.singleton_product, Finset.sum_map, Function.Embedding.coeFn_mk]
  have : ∀ p ∈ Finset.range t, ∑ q ∈ Finset.range ((s * (t - p) + (t - 1)) / t), Jₚ (p, q) =
    Jₚ (p + 1, (s * (t - p) - 1) / t) := by
    intro p hp
    simp only [Finset.mem_range] at hp
    convert J_sum p ((s * (t - p) - 1) / t) using 3
    rw [← Nat.add_div_right _ (by simp)]
    congr 1
    rw [← Nat.add_sub_assoc (by norm_cast; exact PNat.one_le t)]
    rw [← Nat.sub_add_comm (one_le_mul_of_one_le_of_one_le
      (by norm_cast; exact PNat.one_le s)
      (Nat.le_sub_of_add_le' hp))]

  rw [Finset.sum_congr rfl this]

lemma J_asProd (p q: ℕ) :
Jₚ (p, q) * p.factorial = ∏ n ∈ Finset.range p, (q + n + 1) := by
  induction p with
  | zero =>
    unfold Jₚ
    simp
  | succ p prev =>
    rw [Finset.prod_range_add, ← prev, Nat.factorial]
    unfold Jₚ
    simp only [Nat.succ_eq_add_one, Finset.range_one, Finset.prod_singleton, add_zero]
    rw [← mul_assoc, Nat.choose_succ_right_eq]
    have : (p + q).choose p * p.factorial * (q + p + 1) = (p + q).choose p * (p + q + 1) * p.factorial := by ring
    rw [this, Nat.choose_mul_succ_eq]
    have : p + 1 + q = p + q + 1 := add_right_comm p 1 q
    rw [this]


lemma nBranchingBound (s t: ℕ+) :
(s / t: ℝ) ^ (t:ℕ) / (Nat.factorial t) < nBranching s t := by
  rw [nBranchingFormula']
  push_cast
  apply lt_add_of_pos_of_le (by simp)
  have : Finset.range t = Finset.range (t.natPred + 1) := by simp
  rw [this, Finset.sum_range_add, Finset.sum_range_one]
  apply le_add_of_nonneg_of_le (Finset.sum_nonneg (by simp))
  have : t - t.natPred = 1 := by
    apply Nat.sub_eq_of_eq_add'
    simp
  simp only [add_zero, PNat.natPred_add_one, this, mul_one]
  apply (div_le_iff₀ (by norm_cast; exact Nat.factorial_pos t)).mpr
  norm_cast
  rw [J_asProd]
  push_cast
  have : (s / t: ℝ) ^ (t:ℕ) = ∏ _ ∈ Finset.range t, (s / t: ℝ) := by
    simp only [Finset.prod_const, Finset.card_range]
  rw [this]
  apply Finset.prod_le_prod
  · intro _ _
    apply div_nonneg
    all_goals simp
  · intro i h
    trans (((↑s - 1) / ↑t:ℕ):ℝ) + 1
    · apply (div_le_iff₀ (by simp)).mpr
      norm_cast
      zify
      have : ((s  - 1: ℕ): ℤ) = (s - 1: ℤ) := by simp
      rw [this]
      apply Int.le_of_sub_one_lt
      rw [← Int.tdiv_eq_ediv_of_nonneg (by
        simp only [Int.sub_nonneg, Nat.one_le_cast];
        exact NeZero.one_le)]
      exact Int.lt_tdiv_add_one_mul_self _ (by simp)
    · simp
