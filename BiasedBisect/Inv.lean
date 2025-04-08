import BiasedBisect.Basic

/-
In this file, we will explore more about the function φ,
which is the "inverse function" of dE

φ is simply defined as Jceiled shifted by 1
-/
noncomputable
def φ (s t δ: ℝ) [PosReal s] [PosReal t] := 1 + Jceiled s t δ

/-
φ is also a stair-case like function. It doesn't really have a inverse function
in the strict sense, but we can describe its relation ship with dE by the following
-/
noncomputable
def δceiledByφ (s t n: ℝ) [PosReal s] [PosReal t] := {δ | φ s t δ ≤ n}

lemma φ_inv (s t n: ℝ) (n1: n ≥ 1) [PosReal s] [PosReal t]:
δceiledByφ s t n = Set.Iio (dE s t n) := by
  unfold δceiledByφ
  unfold dE
  unfold Set.Iio
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  rw [keq]
  simp only
  unfold kₙ at keq
  unfold φ
  ext δ
  constructor
  · simp only [Nat.cast_add, Nat.cast_one, Set.mem_setOf_eq]
    intro JceiledLe
    contrapose JceiledLe with δGe
    simp only [not_le]
    simp only [not_lt] at δGe
    have JceiledLe: (1: ℝ) + Jceiled s t (δₖ s t k) ≤ 1 + Jceiled s t δ := by
      simp only [add_le_add_iff_left, Nat.cast_le]
      apply Jceiled_mono
      exact δGe
    apply gt_of_ge_of_gt JceiledLe
    have pull_cast: (1: ℝ) + (Jceiled s t (δₖ s t k)) = ((1 + Jceiled s t (δₖ s t k): ℕ): ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
    have n_accum: 1 + Jceiled s t (δₖ s t k) = nₖ s t (k + 1) := by
      rw [nₖ_accum]
      simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        add_tsub_cancel_right]
    rw [pull_cast]
    rw [n_accum]
    by_contra nle
    simp only [gt_iff_lt, not_lt] at nle
    have kp1mem: k + 1 ∈ (kceiled s t n).toFinset := by
      unfold kceiled
      simp only [Set.mem_toFinset, Set.mem_setOf_eq]
      exact nle
    have what: k + 1 ≤ k := by exact Finset.le_max_of_eq kp1mem keq
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at what
  · simp only [Set.mem_setOf_eq, Nat.cast_add, Nat.cast_one]
    intro δlt
    by_cases k0: k = 0
    · rw [k0] at δlt
      rw [δ₀] at δlt
      rw [Jceiled_neg s t δ δlt]
      simp only [CharP.cast_eq_zero, add_zero]
      exact n1
    · have kmem: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
      unfold kceiled at kmem
      simp only [Set.mem_toFinset, Set.mem_setOf_eq] at kmem
      rw [nₖ_accum] at kmem
      simp only [k0, ↓reduceIte, Nat.cast_add, Nat.cast_one] at kmem
      apply le_trans ?_ kmem
      simp only [add_le_add_iff_left, Nat.cast_le]
      apply Jceiled_gap'
      rw [← δₖ]
      have h: (k - 1).succ = k := by exact Nat.succ_pred_eq_of_ne_zero k0
      rw [h]
      exact δlt

/-
Another way to show this, is that φ maps δₖ back to nₖ,
though the index k is shifted due to our convention of close/open intervals
-/
lemma φδₖ(s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
φ s t (δₖ s t k) = nₖ s t (k + 1) := by
  unfold φ
  rw [nₖ_accum]
  simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right]

/-
Analog to w_eq/w_lt/w_gt lemmas, φ maps (δₖ - t) back to wₖ (again with shifted k)
-/
lemma φδₖt(s t: ℝ) (k: ℕ) (kh: k ≥ 1) [PosReal s] [PosReal t]:
φ s t (δₖ s t k - t) = wₖ s t (k + 1) := by
  have wleft (w: ℝ) (w1: w ≥ 1) (h: w < wₖ s t (k + 1)): dE s t w ≤ δₖ s t k - t := by
    obtain lt|ge := lt_or_ge w (wₖ s t k)
    · apply le_of_lt
      exact w_lt _ _ _ _ kh w1 lt
    · apply le_of_eq
      exact w_eq _ _ _ _ kh ge h
  have wright (w: ℝ) (h: w ≥ wₖ s t (k + 1)): dE s t w > δₖ s t k - t := by
    exact w_gt _ _ _ _ h
  have equiv (w: ℝ) (h: w ≥ 1): δₖ s t k - t < dE s t w ↔ wₖ s t (k + 1) ≤ w := by
    constructor
    · contrapose
      simp only [not_le, not_lt]
      apply wleft w h
    · apply wright

  have equiv2 (w: ℝ) (h: w ≥ 1): δₖ s t k - t < dE s t w ↔ δₖ s t k - t ∈ δceiledByφ s t w := by
    rw [φ_inv s t w h]
    simp only [Set.mem_Iio]

  have equiv3 (w: ℝ): δₖ s t k - t ∈ δceiledByφ s t w ↔ φ s t (δₖ s t k - t) ≤ w := by
    unfold δceiledByφ
    simp only [Set.mem_setOf_eq]

  have equiv4 (w: ℝ) (h: w ≥ 1): wₖ s t (k + 1) ≤ w ↔ φ s t (δₖ s t k - t) ≤ w := by
    rw [← equiv w h, equiv2 w h, equiv3]

  have equiv5 (w: ℝ): wₖ s t (k + 1) ≤ w ↔ φ s t (δₖ s t k - t) ≤ w := by
    constructor
    · intro h
      have w1: 1 ≤ w := by
        refine le_trans ?_ h
        norm_cast
        exact wₖ_min' s t (k + 1)
      apply (equiv4 w w1).mp h
    · intro h
      have w1: 1 ≤ w := by
        refine le_trans ?_ h
        norm_cast
        unfold φ
        simp only [le_add_iff_nonneg_right, zero_le]
      apply (equiv4 w w1).mpr h

  obtain equiv6 := equiv5 (wₖ s t (k + 1))
  simp only [le_refl, Nat.cast_le, true_iff] at equiv6
  obtain equiv7 := (equiv5 (φ s t (δₖ s t k - t)))
  simp only [Nat.cast_le, le_refl, iff_true] at equiv7
  exact Nat.le_antisymm equiv6 equiv7

/-
Two lemmas similar to Jline_s and Jline_t
-/
lemma Jceiled_s (s t δ: ℝ) [PosReal s] [PosReal t]:
Jceiled s t (δ - s) = ∑⟨p, q⟩ ∈ (Λceiled s t δ).toFinset, shut p (Jₚ (p - 1, q)) := by
  unfold Jceiled
  apply Finset.sum_of_injOn (fun pq ↦ (pq.1 + 1, pq.2))
  · unfold Set.InjOn
    simp only [Set.coe_toFinset, Prod.forall, Prod.mk.injEq]
    intro a b abmem c d cdmem ab_eq_cd
    simp only [Prod.mk.injEq, add_left_inj] at ab_eq_cd
    trivial
  · simp only [Set.coe_toFinset]
    unfold Λceiled Set.MapsTo
    intro ⟨p, q⟩  pqmem
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at pqmem ⊢
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro ⟨p, q⟩ pqmem pqnmem
    have p0: p = 0 := by
      unfold Λceiled at pqmem
      simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq] at pqmem
      unfold Λceiled at pqnmem
      simp only [Set.coe_toFinset, Set.mem_image, Set.mem_preimage, Prod.exists, not_exists,
        not_and] at pqnmem
      contrapose pqnmem
      apply not_forall.mpr
      use p - 1
      apply not_forall.mpr
      use q
      simp only [Classical.not_imp, Decidable.not_not]
      constructor
      · simp only [Set.mem_setOf_eq]
        have p1: p ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr pqnmem
        push_cast [p1]
        linarith
      · simp only [Prod.mk.injEq, and_true]
        apply Nat.exists_eq_succ_of_ne_zero at pqnmem
        rcases pqnmem with ⟨n, np⟩
        rw [np]
        simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
    rw [p0]
    unfold shut
    simp only
  · intro δ δmem
    unfold shut
    simp only [add_tsub_cancel_right, Prod.mk.eta]

lemma Jceiled_t (s t δ: ℝ) [PosReal s] [PosReal t]:
Jceiled s t (δ - t) = ∑⟨p, q⟩ ∈ (Λceiled s t δ).toFinset, shut q (Jₚ (p, q - 1)) := by
  rw [Jceiled_symm]
  rw [Jceiled_s]
  apply Finset.sum_of_injOn (fun pq ↦ (pq.2, pq.1))
  · unfold Set.InjOn
    simp only [Set.coe_toFinset, Prod.mk.injEq, and_imp, Prod.forall]
    intro p q pqmem p' q' pqmem' qeq peq
    exact ⟨peq, qeq⟩
  · unfold Set.MapsTo
    simp only [Set.coe_toFinset, Prod.forall]
    apply Λceiled_symm
  · simp only [Set.mem_toFinset, Set.coe_toFinset, Set.mem_image, Prod.exists, not_exists, not_and,
      Prod.forall, Prod.mk.injEq]
    intro p q mem mem2
    obtain mem_symm := Λceiled_symm _ _ _ _ _ mem
    obtain what := mem2 q p mem_symm rfl
    simp only [not_true_eq_false] at what
  · simp only [Set.mem_toFinset, Prod.forall]
    intro p q mem
    rw [Jₚ_symm]

/-
φ(δ) is the unique function that satifies the following conditions:
 - φ(< 0) = 1
 - φ(δ ≥ 0) = φ(δ - s) + φ(δ - t)
-/
lemma φ_neg (s t δ: ℝ) (dneg: δ < 0) [PosReal s] [PosReal t]:
φ s t δ = 1 := by
  unfold φ
  rw [Jceiled_neg _ _ _ dneg]

lemma φ_rec (s t δ: ℝ) (dpos: δ ≥ 0) [PosReal s] [PosReal t]:
φ s t δ = φ s t (δ - s) + φ s t (δ - t) := by
  unfold φ
  zify
  suffices (1:ℤ) = Jceiled s t δ - (Jceiled s t (δ - s) + Jceiled s t (δ - t)) by omega
  rw [Jceiled_s, Jceiled_t, Jceiled]
  push_cast
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib]
  symm
  rw [Finset.sum_eq_single (0, 0)]
  · unfold Jₚ shut
    simp only [add_zero, Nat.choose_self, Nat.cast_one, CharP.cast_eq_zero, sub_zero]
  · unfold shut
    rintro ⟨p, q⟩ mem not0
    apply sub_eq_zero_of_eq
    norm_cast
    obtain p0|p1 := Nat.eq_zero_or_eq_succ_pred p
    · obtain q0|q1 := Nat.eq_zero_or_eq_succ_pred q
      · absurd not0
        exact Prod.ext p0 q0
      · unfold Jₚ
        rw [p0, q1]
        simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, zero_add, Nat.choose_zero_right,
          add_tsub_cancel_right]
    · obtain q0|q1 := Nat.eq_zero_or_eq_succ_pred q
      · unfold Jₚ
        rw [p1, q0]
        simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, add_zero, Nat.choose_self,
          add_tsub_cancel_right]
      · rw [p1, q1]
        simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, add_tsub_cancel_right]
        rw [add_comm (Jₚ _)]
        apply Jₚ_rec
  · intro h
    absurd h
    unfold Λceiled
    simp only [Prod.mk_zero_zero, Set.mem_toFinset, Set.mem_setOf_eq, Prod.fst_zero,
      CharP.cast_eq_zero, zero_mul, Prod.snd_zero, add_zero]
    exact dpos

noncomputable
def ρf (s t: ℝ) [PosReal s] [PosReal t] (ρ: ℝ) := Real.exp (-s * ρ) + Real.exp (-t * ρ)

lemma ρf_anti (s t: ℝ) [PosReal s] [PosReal t]: StrictAnti (ρf s t) := by
  apply StrictAnti.add
  all_goals
  · apply StrictMono.comp_strictAnti (Real.exp_strictMono)
    exact strictAnti_mul_left (neg_lt_zero.mpr PosReal.pos)

lemma ρ_exist (s t: ℝ) [PosReal s] [PosReal t]:
∃! ρ ≥ 0, ρf s t ρ = 1 := by
  have tend: Filter.Tendsto (ρf s t) Filter.atTop (nhds 0) := by
    rw [(by simp: (0:ℝ) = 0 + 0)]
    apply Filter.Tendsto.add
    all_goals
    · apply Real.tendsto_exp_comp_nhds_zero.mpr
      apply Filter.Tendsto.neg_mul_atTop (neg_lt_zero.mpr PosReal.pos)
        tendsto_const_nhds
      exact fun ⦃U⦄ a ↦ a
  obtain ⟨ρbound, ρboundspec⟩ := tendsto_atTop_nhds.mp tend (Set.Iio 1) (by simp) isOpen_Iio
  obtain ρboundspec := Set.mem_Iio.mp (ρboundspec ρbound (le_refl _))

  have cont: ContinuousOn (ρf s t) (Set.Icc 0 ρbound) := by unfold ρf; fun_prop
  have ρ0: 0 < ρbound := by
    apply (ρf_anti s t).lt_iff_lt.mp
    apply lt_trans ρboundspec
    unfold ρf
    simp

  obtain ⟨ρs, ρssubset, ρsspec⟩ := Set.subset_image_iff.mp (
    intermediate_value_Icc' (le_of_lt ρ0) cont)

  have onemem: 1 ∈ ρf s t '' ρs := by
    rw [ρsspec]
    simp only [Set.mem_Icc]
    constructor
    · exact le_of_lt ρboundspec
    · unfold ρf
      simp
  obtain ⟨ρ, ρrange, ρspec⟩  := (Set.mem_image _ _ _).mp onemem
  use ρ
  constructor
  · constructor
    · refine Set.mem_of_mem_of_subset ρrange (ρssubset.trans ?_)
      exact (Set.Icc_subset_Ici_iff (le_of_lt ρ0)).mpr (le_refl _)
    · exact ρspec
  · intro q ⟨qrange, qeq⟩
    apply (((ρf_anti s t).strictAntiOn Set.univ).eq_iff_eq (by simp) (by simp)).mp
    rw [qeq]
    unfold ρf
    exact ρspec

noncomputable
def ρ (s t: ℝ) [PosReal s] [PosReal t] := (ρ_exist s t).choose

lemma ρ_satisfies (s t: ℝ) [PosReal s] [PosReal t]:
ρf s t (ρ s t) = 1 := by
  obtain ⟨⟨_, eq⟩, _⟩ := (ρ_exist s t).choose_spec
  exact eq

lemma ρ_range (s t: ℝ) [PosReal s] [PosReal t]: 0 < ρ s t := by
  obtain ⟨⟨range, eq⟩, _⟩ := (ρ_exist s t).choose_spec
  apply lt_of_le_of_ne range
  contrapose! eq
  rw [← eq]
  unfold ρf
  simp

lemma φ_bound (s t x: ℝ) (h: -max s t ≤ x) [PosReal s] [PosReal t]:
(φ s t x: ℝ) ∈ Set.Icc (Real.exp (ρ s t * x)) (Real.exp (ρ s t * (x + max s t))) := by
  have inductor (n: ℕ): ∀ x ∈ Set.Ico (- max s t) (n * min s t),
    (φ s t x: ℝ) ∈ Set.Icc (Real.exp (ρ s t * x)) (Real.exp (ρ s t * (x + max s t))) := by
    induction n with
    | zero =>
      intro x ⟨xleft, xright⟩
      simp only [CharP.cast_eq_zero, zero_mul] at xright
      rw [φ_neg s t x xright]
      simp only [Nat.cast_one, Set.mem_Icc, Real.exp_le_one_iff]
      constructor
      · exact le_of_lt (mul_neg_of_pos_of_neg (ρ_range s t) xright)
      · rw [← Real.exp_zero]
        apply Real.exp_monotone
        exact mul_nonneg (le_of_lt (ρ_range s t)) (neg_le_iff_add_nonneg.mp xleft)
    | succ n prev =>
      intro x ⟨xleft, xright⟩
      obtain small|large := lt_or_ge x (n * min s t)
      · exact prev x ⟨xleft, small⟩
      · have nstpos: 0 ≤ n * min s t :=
          (mul_nonneg (by simp) (le_of_lt (lt_min_iff.mpr ⟨PosReal.pos, PosReal.pos⟩)))
        rw [φ_rec s t x (le_trans nstpos large)]
        push_cast
        have stle: -max s t ≤ x - s ∧ -max s t ≤ x - t := by
          constructor
          all_goals
          apply le_sub_right_of_add_le
          exact le_trans (le_trans (by simp) nstpos) large
        have xlest: x - s < n * min s t ∧ x - t < n * min s t := by
          constructor
          all_goals
          apply sub_right_lt_of_lt_add
          refine lt_of_lt_of_le xright ?_
          push_cast
          rw [add_one_mul]
          simp
        obtain prevs := prev (x - s) ⟨stle.1, xlest.1⟩
        obtain prevt := prev (x - t) ⟨stle.2, xlest.2⟩
        obtain prevst := Set.add_mem_add prevs prevt
        apply Set.mem_of_mem_of_subset prevst
        apply Set.Subset.trans (Set.Icc_add_Icc_subset _ _ _ _)
        apply le_of_eq
        have exprec: Real.exp (ρ s t * (x - s)) + Real.exp (ρ s t * (x - t))
          = Real.exp (ρ s t * x) := by
          rw [mul_sub, mul_sub, sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add, ← mul_add]
          convert mul_one (Real.exp (ρ s t * x))
          rw [mul_comm _ s, mul_comm _ t, ← neg_mul, ← neg_mul]
          apply ρ_satisfies
        rw [mul_add, mul_add, mul_add, Real.exp_add, Real.exp_add, Real.exp_add, ← add_mul, exprec]

  let n := (⌈x / min s t⌉ + 1).toNat
  have bound: x ∈ Set.Ico (- max s t) (n * min s t) := by
    simp only [Set.mem_Ico]
    constructor
    · exact h
    · apply (div_lt_iff₀ (by simp only [lt_inf_iff]; exact ⟨PosReal.pos, PosReal.pos⟩)).mp
      unfold n
      have toNatRaise: (⌈x / (s ⊓ t)⌉ + 1: ℝ) ≤ ((⌈x / (s ⊓ t)⌉ + 1).toNat: ℝ) := by
        norm_cast
        apply Int.self_le_toNat
      refine lt_of_lt_of_le (lt_of_le_of_lt (by apply Int.le_ceil) ?_) toNatRaise
      apply lt_add_of_pos_right
      norm_num

  exact inductor n x bound
