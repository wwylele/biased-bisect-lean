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
