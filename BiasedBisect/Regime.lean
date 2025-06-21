import BiasedBisect.Inert

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Asymptotics Filter

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

lemma J_asymptotic (p: ℕ):
(fun q ↦ (Jₚ (p, q): ℝ)) ~[atTop] (fun q ↦ q ^ p / p.factorial) := by
  suffices (fun q ↦ (Jₚ (p, q): ℝ) * p.factorial) ~[atTop] (fun q ↦ q ^ p) by
    convert this.div (IsEquivalent.refl (u := fun q ↦ (p.factorial: ℝ)))
    rw [mul_div_cancel_right₀ _ (by norm_cast; exact Nat.factorial_ne_zero p)]
  norm_cast
  simp_rw [J_asProd]
  push_cast
  have: (fun (q:ℕ) ↦ (q:ℝ)^p) = (fun (q:ℕ) ↦ ∏ n ∈ Finset.range p, (q:ℝ)) := by simp
  rw [this]
  apply Asymptotics.IsEquivalent.finsetProd
  intro n hn
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr ?_
  · apply eventually_atTop.mpr
    use 1
    aesop
  · have : (fun (q:ℕ) ↦ (q + n + 1: ℝ)) / (fun (q:ℕ) ↦ (q: ℝ)) =ᶠ[atTop] fun (q:ℕ) ↦ (1 + (n + 1) / q: ℝ) := by
      apply eventually_atTop.mpr
      use 1
      intro q hq
      simp only [Pi.div_apply]
      rw [add_assoc, add_div]
      rw [div_self (by norm_cast; exact ne_of_gt (lt_of_lt_of_le (by simp) hq))]
    apply Tendsto.congr' this.symm
    rw [(by simp: nhds (1:ℝ) = nhds (1 + 0))]
    exact tendsto_const_nhds.add (tendsto_natCast_atTop_atTop.const_div_atTop _)


lemma sub_natPred (t: ℕ+) : t - t.natPred = 1 := by
  apply Nat.sub_eq_of_eq_add'
  simp

lemma nBranchingBound (s t: ℕ+) :
(s / t: ℝ) ^ (t:ℕ) / (Nat.factorial t) < nBranching s t := by
  rw [nBranchingFormula']
  push_cast
  apply lt_add_of_pos_of_le (by simp)
  have : Finset.range t = Finset.range (t.natPred + 1) := by simp
  rw [this, Finset.sum_range_add, Finset.sum_range_one]
  apply le_add_of_nonneg_of_le (Finset.sum_nonneg (by simp))
  simp only [add_zero, PNat.natPred_add_one, sub_natPred, mul_one]
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

lemma PNat_val_tendsto : Tendsto PNat.val atTop atTop := by
  refine tendsto_atTop_atTop.mpr ?_
  intro n
  use n.toPNat'
  intro m h
  exact Nat.le_of_pred_lt h

lemma divEquivalent (d:ℕ): (fun (n:ℕ) ↦ ((n / d:ℕ):ℝ)) ~[atTop] (fun (n:ℕ) ↦ (n / d:ℝ)) := by
  by_cases hd: d = 0
  · rw [hd]
    simpa using IsEquivalent.refl
  · refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr ?_
    · apply eventually_atTop.mpr
      use 1
      intro x hx
      simp [(ne_of_gt (lt_of_lt_of_le (by simp) hx): x ≠ 0), hd]
    · have : Tendsto (fun (n:ℕ) ↦ (n / d:ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_div_const (by simpa using Nat.zero_lt_of_ne_zero hd)
      apply (tendsto_nat_floor_div_atTop.comp this).congr
      intro n
      simp [Nat.floor_div_eq_div]


lemma nBranchingAsymptotic (t: ℕ+) :
(fun (s:ℕ+) ↦ (s / t: ℝ) ^ (t:ℕ) / (Nat.factorial t)) ~[atTop] (fun (s:ℕ+) ↦ nBranching s t) := by
  simp_rw [nBranchingFormula']
  push_cast
  have : Finset.range t = Finset.range (t.natPred + 1) := by simp
  simp_rw [this, Finset.sum_range_add, Finset.sum_range_one]
  simp only [add_zero, PNat.natPred_add_one, sub_natPred, mul_one]
  simp_rw [← add_assoc]
  refine (IsLittleO.add_isEquivalent ?_ ?_).symm
  · apply IsLittleO.add
    · simp only [isLittleO_one_left_iff, norm_div, norm_pow, Real.norm_natCast]
      apply Tendsto.atTop_div_const (by simpa using Nat.factorial_pos t)
      simp_rw [← Real.rpow_natCast]
      refine (tendsto_rpow_atTop (by simp)).comp ?_
      apply Tendsto.atTop_div_const (by simp)
      exact tendsto_natCast_atTop_atTop.comp PNat_val_tendsto
    · apply IsLittleO.sum
      intro n hn
      have hn': 1 ≤ t - n := by
        refine Nat.le_sub_of_add_le' (le_of_lt ?_)
        exact Nat.add_lt_of_lt_sub (Finset.mem_range.mp hn)
      have stn: Tendsto (fun s ↦ s * (t - n) - 1) atTop atTop := by
        refine (Filter.tendsto_sub_atTop_nat _).comp ?_
        refine Filter.tendsto_id.atTop_mul_one_le ?_
        intro _
        exact hn'
      refine IsLittleO.comp_tendsto (?_:
        (fun (s:ℕ) ↦ (Jₚ (n + 1, (s * (t - n) - 1) / ↑t): ℝ)) =o[atTop] fun (s:ℕ) ↦ ((s / t) ^ (t:ℕ) / Nat.factorial t: ℝ)
        ) PNat_val_tendsto
      refine ((J_asymptotic _).comp_tendsto ?_).trans_isLittleO ?_
      · apply (Nat.tendsto_div_const_atTop (by simp)).comp
        exact stn
      · conv in (fun (q:ℕ) ↦ (q ^ (n + 1) / Nat.factorial (n + 1): ℝ)) =>
          ext q
          rw [div_eq_inv_mul]
        conv in (fun (s:ℕ) ↦ (s / t: ℝ) ^ (t:ℕ) / (Nat.factorial t: ℝ)) =>
          ext s
          rw [div_eq_inv_mul]
        apply IsLittleO.const_mul_right (by simpa using Nat.factorial_ne_zero t)
        apply IsLittleO.const_mul_left
        refine IsBigO.trans_isLittleO (g := fun (s:ℕ) ↦ (s / t:ℝ) ^ (n + 1)) ?_ ?_
        · apply IsBigO.pow
          refine ((divEquivalent _).comp_tendsto stn).trans_isBigO ?_
          simp_rw [div_eq_inv_mul]
          apply IsBigO.const_mul_right (by simp)
          apply IsBigO.const_mul_left
          simp only
          have : (fun (s:ℕ) ↦ ((s * (t - n) - 1:ℕ):ℝ)) =ᶠ[atTop] (fun (s:ℕ) ↦ ((s * (t - n:ℕ) - 1):ℝ)) := by
            apply eventually_atTop.mpr
            use 1
            intro s h
            simp only
            have : 1 ≤ s * (t - n) := one_le_mul_of_one_le_of_one_le h hn'
            rw [Nat.cast_sub this]
            simp
          refine IsBigO.congr' ?_ (this.symm) (EventuallyEq.refl _ _)
          apply Asymptotics.IsBigO.natCast_atTop (f := fun (s:ℝ) ↦ ((s * (t - n:ℕ) - 1):ℝ)) (g := id)
          apply Asymptotics.IsBigO.sub
          · refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ ((t - n:ℕ):ℝ) ?_
            · apply Eventually.of_forall
              simp [imp_or]
            · have (c: ℝ) : (fun (x:ℝ) ↦ x * c) / id =ᶠ[atTop] fun _ ↦ c := by
                apply eventually_atTop.mpr
                use 1
                intro x hx
                simp [(ne_of_gt (lt_of_lt_of_le (by simp) hx): x ≠ 0)]
              apply Tendsto.congr' (this _).symm
              simp
          · refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ 0 ?_
            · apply eventually_atTop.mpr
              use 1
              intro x hx
              simp [(ne_of_gt (lt_of_lt_of_le (by simp) hx): x ≠ 0)]
            · exact Filter.tendsto_id.const_div_atTop _
        · have : Tendsto (fun (s:ℕ) ↦ (s/t:ℝ)) atTop atTop := by
            apply Tendsto.atTop_div_const (by simp)
            exact tendsto_natCast_atTop_atTop
          refine IsLittleO.comp_tendsto (?_: (fun x ↦ x^(n+1)) =o[atTop] (fun x ↦ x^(t:ℕ))) this
          apply isLittleO_pow_pow_atTop_of_lt
          exact Nat.add_lt_of_lt_sub (Finset.mem_range.mp hn)
  · refine IsEquivalent.comp_tendsto (?_:
      (fun (s:ℕ) ↦ (Jₚ (t, (s - 1) / t): ℝ)) ~[atTop] fun (s:ℕ) ↦ (↑s / ↑↑t) ^ (t:ℕ) / (Nat.factorial t)
      ) PNat_val_tendsto
    trans (fun s ↦ (((s - 1) / t: ℕ):ℝ) ^ (t:ℕ) / (Nat.factorial t))
    · apply (J_asymptotic _).comp_tendsto
      apply (Nat.tendsto_div_const_atTop (by simp)).comp (tendsto_sub_atTop_nat 1)
    · refine IsEquivalent.div (IsEquivalent.pow ?_ _) IsEquivalent.refl
      trans fun (s:ℕ) ↦ ((s - 1:ℕ):ℝ) / (t:ℝ)
      · exact (divEquivalent t).comp_tendsto (tendsto_sub_atTop_nat 1)
      · refine IsEquivalent.div ?_ (IsEquivalent.refl)
        unfold IsEquivalent
        have : (fun s ↦ ((s - 1:ℕ):ℝ)) - (fun (s:ℕ) ↦ (s:ℝ)) =ᶠ[atTop] (fun _ ↦ -1) := by
          apply eventually_atTop.mpr
          use 1
          aesop
        refine IsLittleO.congr' ?_ this.symm (EventuallyEq.refl _ _)
        simpa using tendsto_natCast_atTop_atTop
