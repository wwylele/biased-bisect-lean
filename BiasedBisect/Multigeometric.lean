import BiasedBisect.Basic


lemma ΛDecompMem (p q: ℕ): p ∈ Finset.range (p + q + 1) := by
  simp only [Finset.mem_range]
  linarith

def ΛDecomp: ((j:ℕ) × Finset.range (j + 1)) ≃ (ℕ × ℕ) where
  toFun | ⟨j, n⟩ => (n, j - n)
  invFun | ⟨p, q⟩ => ⟨p + q, ⟨p, ΛDecompMem p q⟩⟩
  left_inv := by
    unfold Function.LeftInverse
    simp only
    rintro ⟨j, ⟨n, nmem⟩⟩
    simp only [Finset.mem_range] at nmem
    simp only [Sigma.mk.injEq]
    constructor
    · rw [add_comm]
      rw [Nat.sub_add_cancel]
      exact Nat.le_of_lt_succ nmem
    · refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
      intro k
      rw [add_comm n]
      rw [Nat.sub_add_cancel]
      exact Nat.le_of_lt_succ nmem

  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    simp only [add_tsub_cancel_left, Prod.mk.eta, implies_true]

lemma bigeometric_series {K : Type*} [RCLike K] (x y: K) (xbound: ‖x‖ < 2⁻¹) (ybound: ‖y‖ < 2⁻¹):
HasSum (fun pq ↦ Jₚ pq * x ^ pq.1 * y ^ pq.2) (1 - (x + y))⁻¹ := by
  apply (Equiv.hasSum_iff ΛDecomp).mp
  unfold ΛDecomp Function.comp
  simp only [Equiv.coe_fn_mk]

  let term := fun (⟨j, c⟩:(j:ℕ) × Finset.range (j + 1)) ↦ ((Jₚ (c, j - c)) * x ^ (c:ℕ) * y ^ (j - c))
  have binom: ∀(j:ℕ), HasSum (fun (c:Finset.range (j + 1)) ↦ term ⟨j, c⟩) ((x + y) ^ j) := by
    intro j
    rw [add_pow]
    let f(c: ℕ) := x ^ c * y ^ (j - c) * (j.choose c)
    have left: ∀ c, (fun c ↦ term ⟨j, c⟩) c = ((fun (c:Finset.range (j + 1)) ↦ f c) ∘ (↑)) c := by
      intro c
      unfold term Jₚ f
      simp only [Function.comp_apply]
      obtain cbound := Nat.le_of_lt_succ (Finset.mem_range.mp c.property)
      rw [(by zify [cbound]; ring: c + (j - c) = j)]
      ring
    apply HasSum.congr_fun ?_ left
    exact Finset.hasSum _ _ (SummationFilter.unconditional _)

  refine HasSum.sigma_of_hasSum ?_ binom ?_
  · apply hasSum_geometric_of_norm_lt_one
    apply lt_of_le_of_lt (by apply norm_add_le)
    rw [(by norm_num: (1:ℝ) = 2⁻¹ + 2⁻¹)]
    exact add_lt_add xbound ybound
  · apply (Equiv.summable_iff ΛDecomp.symm).mp
    unfold ΛDecomp Function.comp
    simp only [Equiv.coe_fn_symm_mk, add_tsub_cancel_left, Prod.mk.eta]
    show Summable fun (pq: ℕ × ℕ) ↦ Jₚ pq * x ^ pq.1  * y ^ pq.2
    let termBound := fun (pq: ℕ × ℕ) ↦ ‖(2 * x) ^ pq.1 * (2 * y) ^ pq.2‖
    have raise(pq: ℕ × ℕ): ‖Jₚ pq * x ^ pq.1  * y ^ pq.2‖ ≤ termBound pq := by
      unfold termBound
      rw [(by rw [← norm_mul]; ring_nf: ‖(2 * x) ^ pq.1 * (2 * y) ^ pq.2‖ = ‖(2 ^ pq.1 * 2 ^ pq.2: K)‖ * ‖x ^ pq.1 * y ^ pq.2‖)]
      rw [(by rw [← norm_mul]; ring_nf: ‖(Jₚ pq) * x ^ pq.1 * y ^ pq.2‖ = ‖(Jₚ pq: K)‖ * ‖x ^ pq.1 * y ^ pq.2‖)]
      refine mul_le_mul_of_nonneg_right ?_ (by apply norm_nonneg)
      norm_cast
      apply Jₚ_bound
    refine Summable.of_norm_bounded ?_ raise
    apply Summable.mul_norm
    all_goals
    · simp only [norm_pow, norm_mul, RCLike.norm_ofNat, summable_geometric_iff_norm_lt_one,
        norm_norm]
      apply (lt_inv_mul_iff₀ ?_).mp
      · simp only [mul_one]
        try apply xbound
        try apply ybound
      · norm_num
