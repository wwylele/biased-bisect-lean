import BiasedBisect.CrossSection
import BiasedBisect.Integer
import BiasedBisect.MathlibTopologyOrderIsLUB
import BiasedBisect.MathlibMeasureTheoryIntegralAsymptotics

/-!
# Asymptotics

We show that `E` and `wₗᵢ`, the solution to the original biased bisect problem,
are asymptotically equivalent to `Eℝ` and `wℝ`, the solution to the continuous biased bisect problem.

## Main statements
 - `E_Asymptotic` states the asymptotic behavior of `E`.
 - `w_Asymtotic` states the asymptotic behavior of `wₗᵢ`.
-/

open Asymptotics Filter

lemma δₖ_infinity (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (δₖ s t) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro ceil
  by_contra! allunder
  have allunder' (k): δₖ s t k < ceil := by
    obtain ⟨k', k'range, k'under⟩ := allunder k
    refine lt_of_le_of_lt ?_ k'under
    exact (δₖ_mono s t).le_iff_le.mpr k'range
  have δmem: Nat.ceil (ceil / s) * s ∈ Δ s t := by
    use Nat.ceil (ceil / s), 0
    ring
  obtain ⟨k, keq⟩ := δₖ_surjΔ s t _ δmem
  obtain what := allunder' k
  rw [keq] at what
  obtain what' := lt_of_le_of_lt (Nat.le_ceil _) ((lt_div_iff₀ PosReal.pos).mpr what)
  simp at what'

lemma φ_Asymptotic (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (fun x ↦ x * (ρ s t) / Real.log (φ s t x)) atTop (nhds 1) := by
  have logφpos (x: ℝ) (h: 0 ≤ x): 0 < Real.log (φ s t x) := by
    apply Real.log_pos
    unfold φ
    norm_cast
    simp only [lt_add_iff_pos_right]
    exact Jceiled_pos s t x h

  have maxst: 0 < max s t := lt_max_of_lt_left PosReal.pos

  have left (x: ℝ) (h: 0 ≤ x): x / (x + max s t) ≤ x * (ρ s t) / Real.log (φ s t x) := by
    apply (le_div_iff₀ (logφpos x h)).mpr
    rw [← mul_div_right_comm]
    apply (div_le_iff₀ (add_pos_of_nonneg_of_pos h maxst)).mpr
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ h
    apply (Real.log_le_iff_le_exp (by unfold φ; norm_cast; simp)).mpr
    exact (φ_bound s t x (le_trans (Left.neg_nonpos_iff.mpr (le_of_lt maxst)) h)).2

  have right (x: ℝ) (h: 0 ≤ x): x * (ρ s t) / Real.log (φ s t x) ≤ 1 := by
    apply (div_le_one₀ (logφpos x h)).mpr
    apply (Real.le_log_iff_exp_le (by unfold φ; norm_cast; simp)).mpr
    rw [mul_comm]
    exact (φ_bound s t x (le_trans (Left.neg_nonpos_iff.mpr (le_of_lt maxst)) h)).1

  have left': ∀ᶠ x in atTop, x / (x + max s t) ≤ x * (ρ s t) / Real.log (φ s t x) := by
    apply eventually_atTop.mpr
    use 0
  have right': ∀ᶠ x in atTop, x * (ρ s t) / Real.log (φ s t x) ≤ 1 := by
    apply eventually_atTop.mpr
    use 0

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds left' right'
  conv in fun x ↦ _ =>
    ext x
    rw [← inv_div]
    rw [add_div]
  rw [(by simp: (1:ℝ) = (1 + 0)⁻¹)]
  refine Tendsto.inv₀ (Tendsto.add (tendsto_const_nhds.congr' ?_) ?_) (by simp)
  · apply eventually_atTop.mpr
    use 1
    intro x x1
    simp only
    rw [div_self (ne_of_gt (lt_of_lt_of_le (by simp) x1))]
  · exact Tendsto.const_div_atTop (fun ⦃U⦄ a ↦ a) _

lemma δₖ_Asymptotic (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (fun k ↦ δₖ s t k * (ρ s t) / Real.log (nₖ s t (k + 1))) atTop (nhds 1) := by
  simp_rw [← φδₖ]
  exact Tendsto.comp (φ_Asymptotic s t) (δₖ_infinity s t)

lemma δₖ_slowGrow (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (fun k ↦ δₖ s t (k + 1) / δₖ s t k) atTop (nhds 1) := by
  have smallgap (k: ℕ): δₖ s t (k + 1) ≤ δₖ s t k + s := by
    rw [δₖ]
    apply Set.IsWF.min_le
    unfold Δfloored
    simp only [gt_iff_lt, Set.mem_inter_iff, Set.mem_setOf_eq, lt_add_iff_pos_right]
    constructor
    · obtain ⟨p, q, pqeq⟩ := δₖ_in_Δ s t k
      use p + 1, q
      rw [← pqeq]
      push_cast
      ring
    · exact PosReal.pos

  have right (k: ℕ): δₖ s t (k + 1) / δₖ s t k ≤ (δₖ s t k + s) / δₖ s t k := by
    apply div_le_div_of_nonneg_right
    · apply smallgap
    · rw [← δ₀ s t]
      apply (δₖ_mono s t).le_iff_le.mpr
      simp
  have right': ∀ᶠ k in atTop, δₖ s t (k + 1) / δₖ s t k ≤ (δₖ s t k + s) / δₖ s t k := by
    apply eventually_atTop.mpr
    use 0
    intro k k0
    exact right k

  have left (k: ℕ) (k1: 1 ≤ k): 1 ≤ δₖ s t (k + 1) / δₖ s t k := by
    refine (one_le_div₀ ?_).mpr ?_
    · rw [← δ₀ s t]
      apply (δₖ_mono s t).lt_iff_lt.mpr
      exact k1
    · apply (δₖ_mono s t).le_iff_le.mpr
      simp

  have left': ∀ᶠ k in atTop, 1 ≤ δₖ s t (k + 1) / δₖ s t k := by
    apply eventually_atTop.mpr
    use 1

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_ left' right'
  rw [(by simp: (1:ℝ) = (1 + (s * 0)))]
  conv in fun k ↦ _ =>
    ext k
    rw [add_div]
  apply Tendsto.add
  · apply tendsto_const_nhds.congr'
    apply eventually_atTop.mpr
    use 1
    intro k k1
    simp only
    refine (div_self ?_).symm
    apply ne_of_gt
    rw [← δ₀ s t]
    exact δₖ_mono s t k1
  · apply Tendsto.const_mul
    exact Tendsto.comp tendsto_inv_atTop_zero (δₖ_infinity s t)


lemma dE_Asymptotic' (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (fun n ↦ (dE s t n) * (ρ s t) / Real.log n) atTop (nhds 1) := by
  let kₙ'proof (n: ℝ): (max n 1) ≥ 1 := by simp
  let kₙ' (n: ℝ) := (kₙ_exist s t _ (kₙ'proof n))
  let left := fun n ↦ δₖ s t ((kₙ' n).choose) * (ρ s t) / Real.log (nₖ s t ((kₙ' n).choose + 1))
  let right := fun n ↦ δₖ s t ((kₙ' n).choose) * (ρ s t) / Real.log (nₖ s t (kₙ' n).choose)

  have kₙ'inv (n: ℝ) (n1: 1 ≤ n): nₖ s t (kₙ' n).choose ≤ n ∧ n < nₖ s t ((kₙ' n).choose + 1) := by
    obtain kₙ'spec := (kₙ' n).choose_spec
    convert nₖ_inv _ _ _ _ kₙ'spec
    all_goals
      symm
      exact max_eq_left n1

  have nₖleft (n: ℝ) (n1: 1 ≤ n) := (kₙ'inv n n1).1
  have nₖright (n: ℝ) (n1: 1 ≤ n) := (kₙ'inv n n1).2
  have δₖeq (n: ℝ) (n1: 1 ≤ n): δₖ s t ((kₙ' n).choose) = dE s t n := by
    obtain kₙ'spec := (kₙ' n).choose_spec
    rw [← max_eq_left n1]
    unfold dE
    rw [kₙ'spec]
    simp

  have dEρnonneg (n: ℝ) (n1: 1 ≤ n): 0 ≤ (dE s t n) * (ρ s t) := by
    refine mul_nonneg ?_ (le_of_lt (ρ_range s t))
    rw [← dE₁ s t]
    exact (dE_mono s t) n1

  have leftle (n: ℝ) (n1: 1 < n): left n ≤ (dE s t n) * (ρ s t) / Real.log n := by
    unfold left

    rw [δₖeq n (le_of_lt n1)]
    apply div_le_div_of_nonneg_left (dEρnonneg n (le_of_lt n1)) (Real.log_pos n1)
    apply Real.log_le_log (lt_trans (by simp) n1)
    exact le_of_lt (nₖright n (le_of_lt n1))

  have rightle (n: ℝ) (n2: 2 ≤ n): (dE s t n) * (ρ s t) / Real.log n ≤ right n := by
    have n1: 1 < n := lt_of_lt_of_le (by simp) n2
    have k1: (kₙ' n).choose ≥ 1 := by
      have mem: 1 ∈ (kceiled s t (max n 1)).toFinset := by
        simp only [Set.mem_toFinset]
        unfold kceiled
        simp only [Set.mem_setOf_eq]
        rw [n₁]
        simp only [Nat.cast_ofNat, le_sup_iff, Nat.not_ofNat_le_one, or_false]
        exact n2
      exact Finset.le_max_of_eq mem (kₙ' n).choose_spec
    unfold right
    rw [δₖeq n (le_of_lt n1)]
    have onele: 1 < nₖ s t ((kₙ' n).choose) := by
      apply Nat.lt_of_succ_le
      norm_num
      rw [← n₁ s t]
      exact (nₖ_mono s t).le_iff_le.mpr k1
    apply div_le_div_of_nonneg_left (dEρnonneg n (le_of_lt n1))
    · apply Real.log_pos
      exact Nat.one_lt_cast.mpr onele
    · apply Real.log_le_log
      · exact lt_trans (by simp: (0:ℝ) < 1) (Nat.one_lt_cast.mpr onele)
      · exact nₖleft n (le_of_lt n1)

  have leftle': ∀ᶠ n in atTop, left n ≤ (dE s t n) * (ρ s t) / Real.log n := by
    apply eventually_atTop.mpr
    use 2
    intro n n2
    exact leftle n (lt_of_lt_of_le (by simp) n2)

  have rightle': ∀ᶠ n in atTop, (dE s t n) * (ρ s t) / Real.log n ≤ right n := by
    apply eventually_atTop.mpr
    use 2

  have ktends: Tendsto (fun n ↦ (kₙ' n).choose) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro k
    use nₖ s t (k + 1)
    intro n nbound
    apply le_of_add_le_add_right (a := 1)
    apply (nₖ_mono s t).le_iff_le.mp
    rify
    refine le_trans nbound (le_of_lt (nₖright _ ?_))
    refine le_trans ?_ nbound
    norm_cast
    nth_rw 1 [← n₀ s t]
    apply (nₖ_mono s t).le_iff_le.mpr
    simp

  have righttends: Tendsto (fun k ↦ δₖ s t (k + 1 + 1) * (ρ s t) / Real.log (nₖ s t (k + 1 + 1)))
    atTop (nhds 1) := by

    conv in fun k ↦ _ =>
      ext k
      rw [(by
        refine (div_mul_cancel₀ _ ?_).symm
        apply ne_of_gt
        rw [← δ₀ s t]
        apply δₖ_mono
        simp
        :δₖ s t (k + 1 + 1) = δₖ s t (k + 1 + 1) / δₖ s t (k + 1) * δₖ s t (k + 1))]
      rw [(by ring:
         δₖ s t (k + 1 + 1) / δₖ s t (k + 1) * δₖ s t (k + 1) * (ρ s t) / Real.log (nₖ s t (k + 1 + 1))
        = δₖ s t (k + 1 + 1) / δₖ s t (k + 1) * (δₖ s t (k + 1) * (ρ s t) / Real.log (nₖ s t (k + 1 + 1))))]
    rw [(by simp: (1:ℝ) = 1 * 1)]
    refine Tendsto.mul ?_ ?_
    · exact Tendsto.comp (δₖ_slowGrow s t) (tendsto_add_atTop_nat 1)
    · exact Tendsto.comp (δₖ_Asymptotic s t) (tendsto_add_atTop_nat 1)

  have righttends': Tendsto (fun k ↦ δₖ s t k * (ρ s t) / Real.log (nₖ s t k))
    atTop (nhds 1) := by
    apply (righttends.comp (tendsto_sub_atTop_nat 2)).congr'
    apply eventually_atTop.mpr
    use 2
    intro k k2
    simp only [Function.comp_apply]
    congr
    all_goals
    zify [k2]
    ring

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ leftle' rightle'
  · exact Tendsto.comp (δₖ_Asymptotic s t) ktends
  · exact Tendsto.comp righttends' ktends

lemma dE_Asymptotic (s t: ℝ) [PosReal s] [PosReal t]:
dE s t ~[atTop] (Real.log · / ρ s t) := by
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · apply eventually_atTop.mpr
    use 2
    intro n n2
    simp only [ne_eq, div_eq_zero_iff, Real.log_eq_zero, not_or]
    constructor
    · constructor
      · contrapose! n2
        rw [n2]
        norm_num
      · constructor
        all_goals
        · contrapose! n2
          rw [n2]
          norm_num
    · exact ne_of_gt (ρ_range _ _)
  · apply (dE_Asymptotic' s t).congr
    intro n
    simp only [Pi.div_apply]
    rw [← div_mul]
    rw [mul_div_right_comm]

theorem E_Asymptotic (s t: ℝ) [PosReal s] [PosReal t]:
E s t ~[atTop] Eℝ s t := by
  have congr_left: E s t =ᶠ[atTop] fun n ↦ ∫ x in Set.Ioc 1 n, dE s t x + s + t := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    simp only
    rw [← intervalIntegral.integral_of_le hn]
    convert E_integral s t n hn
  have congr_right: Eℝ s t =ᶠ[atTop] fun n ↦ ∫ x in Set.Ioc 1 n, (Real.log x + 1) / ρ s t := by
    unfold Eℝ
    apply eventually_atTop.mpr
    use 1
    intro n hn
    let f := (fun n ↦ n * Real.log n / ρ s t)
    have: (fun n ↦ n * Real.log n / ρ s t) n =
      f n - f 1 := by
      unfold f
      simp
    rw [this]
    simp only
    rw [← intervalIntegral.integral_of_le hn]
    apply (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_).symm
    · intro x hx
      rw [Set.uIcc_of_le hn] at hx
      have x0: x ≠ 0 := ne_of_gt <| lt_of_lt_of_le (by simp) hx.1
      unfold f
      apply HasDerivAt.div_const
      have: Real.log x + 1 = 1 * Real.log x + x * x⁻¹ := by
        simp [x0]
      rw [this]
      apply HasDerivAt.mul
      · exact hasDerivAt_id' x
      · refine Real.hasDerivAt_log x0
    · apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.div_const (ContinuousOn.add ?_ continuousOn_const) _
      exact Real.continuousOn_log.mono (by simp [hn])
  refine IsEquivalent.congr_left ?_ congr_left.symm
  refine IsEquivalent.congr_right ?_ congr_right.symm
  refine IsEquivalent.integral ?_ ?_ ?_ ?_
  · refine (IsEquivalent.trans ?_ (dE_Asymptotic s t)).trans ?_
    · simp_rw [add_assoc]
      apply IsEquivalent.add_isLittleO IsEquivalent.refl
      refine IsLittleO.trans_isEquivalent ?_ (dE_Asymptotic s t).symm
      refine isLittleO_const_left.mpr (Or.inr ?_)
      have: (norm ∘ fun x ↦ Real.log x / ρ s t) =ᶠ[atTop] fun x ↦ Real.log x / ρ s t := by
        apply eventually_atTop.mpr
        use 1
        intro x hx
        simp only [Function.comp_apply, norm_div, Real.norm_eq_abs]
        rw [abs_eq_self.mpr (Real.log_nonneg hx), abs_eq_self.mpr (ρ_range s t).le]
      apply Filter.Tendsto.congr' this.symm
      exact (Real.tendsto_log_atTop).atTop_div_const (ρ_range s t)
    · refine IsEquivalent.div ?_ IsEquivalent.refl
      refine (IsEquivalent.add_isLittleO IsEquivalent.refl ?_).symm
      refine isLittleO_const_left.mpr (Or.inr ?_)
      have: (norm ∘ fun x ↦ Real.log x ) =ᶠ[atTop] fun x ↦ Real.log x := by
        apply eventually_atTop.mpr
        use 1
        intro x hx
        simp only [Function.comp_apply, Real.norm_eq_abs, abs_eq_self]
        exact Real.log_nonneg hx
      exact Filter.Tendsto.congr' this.symm Real.tendsto_log_atTop
  · exact (Real.tendsto_log_atTop.atTop_add tendsto_const_nhds).atTop_div_const (ρ_range s t)
  · intro n hn
    apply (dE_integrable' s t 1 n).def'.congr_set_ae
    apply Eventually.of_forall
    unfold Set.uIoc
    intro y
    congr
    · exact left_eq_inf.mpr hn
    · exact Eq.symm (max_eq_right hn)
  · intro n hn
    refine integrableOn_Icc_iff_integrableOn_Ioc.mp <| ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.div_const (ContinuousOn.add ?_ continuousOn_const) _
    exact Real.continuousOn_log.mono (by simp)

/-
g agrees with ξ₀ that we defined in Integer.lean
-/
lemma g_eq (s t: ℕ+): (ξ₀ s t ^ (t: ℕ)) = g s t := by
  apply g_unique s t
  · obtain left := ξ₀min s t
    obtain right := ξ₀max s t
    constructor
    · exact le_of_lt (pow_pos left t)
    · exact pow_le_one₀ (le_of_lt left) (le_of_lt right)
  · obtain val := ξ₀eval s t
    unfold ξPolynomialℝ at val
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
      Polynomial.eval_one] at val
    obtain val' := eq_sub_of_add_eq (eq_of_sub_eq_zero val)
    rw [← val']
    simp only [Real.rpow_natCast]
    rw [← pow_mul, ← pow_mul, mul_comm]


/-
A corollary of w_Asymtotic_int: the limit holds for rational s / t
-/
lemma w_Asymtotic_rat (s t: ℝ) [PosReal s] [PosReal t] (rational: s / t ∈ Set.range Rat.cast):
Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) atTop (nhds (g s t)) := by
  obtain ⟨ST, STeq⟩ := Set.mem_range.mpr rational
  let T := Rat.pnatDen ST
  let S' := Rat.num ST
  have eq1: (S' / T: ℚ) = s / t := by
    unfold S' T
    rw [Rat.coe_pnatDen, Rat.num_div_den, STeq]
  push_cast at eq1
  have eq2: S' = s / t * T := by
    exact mul_invOf_eq_iff_eq_mul_right.mp eq1
  have S'pos: 0 < (S': ℝ) := by
    rw [eq2]
    exact mul_pos (div_pos PosReal.pos PosReal.pos) (by norm_cast; exact PNat.pos T)
  norm_cast at S'pos
  let S: PNat := ⟨Int.toNat S', by
    simp only [Int.lt_toNat, CharP.cast_eq_zero]
    exact S'pos
  ⟩
  have S'eq : S' = S := by
    unfold S
    simp only [PNat.mk_coe, Int.ofNat_toNat, left_eq_sup]
    exact le_of_lt S'pos
  rw [S'eq] at eq1
  push_cast at eq1
  let l := s / S
  have seq: s = l * S := by
    unfold l
    simp
  have teq: t = l * T := by
    unfold l
    rw [div_mul, eq1, ← div_mul]
    rw [div_self (ne_of_gt PosReal.pos)]
    simp only [one_mul]

  simp_rw [seq, teq]
  conv in (fun n ↦ _) =>
    ext n
    rw [← wₗᵢ_homo S T n l]
  rw [← g_homo, ← g_eq]
  apply w_Asymtotic_int

/-
To generalize the limit to all real s and t, we will utilize the following facts:
 - g is antitone and continuous
 - w is monotone w.r.t s and t
-/

/-
To help with the proof, we define the inverse function of g w.r.t t, fixing s = 1
-/
noncomputable
def ginv (g) := Real.log g / Real.log (1 - g)

/-
ginv is antitone
-/
lemma ginv_anti: StrictAntiOn ginv (Set.Ioo 0 1) := by
  unfold ginv
  intro g1 g1mem g2 g2mem lt
  simp only
  nth_rw 1 [← neg_div_neg_eq]
  nth_rw 2 [← neg_div_neg_eq]
  apply div_lt_div₀
  · simp only [neg_lt_neg_iff]
    exact Real.log_lt_log g1mem.1 lt
  · simp only [neg_le_neg_iff]
    apply le_of_lt
    apply Real.log_lt_log
    · simp only [sub_pos]
      apply g2mem.2
    · simp only [sub_lt_sub_iff_left]
      exact lt
  · simp only [Left.nonneg_neg_iff]
    exact le_of_lt (Real.log_neg g1mem.1 g1mem.2)
  · simp only [Left.neg_pos_iff]
    apply Real.log_neg
    · simp only [sub_pos]
      exact g1mem.2
    · simp only [sub_lt_self_iff]
      exact g1mem.1

/-
And as expected, ginv inverts g
-/
lemma ginv_comp (r: ℝ) [PosReal r]: ginv (g 1 r) = r := by
  unfold ginv
  apply div_eq_of_eq_mul
  · simp only [ne_eq, Real.log_eq_zero, sub_eq_self, not_or]
    constructor
    · exact ne_of_gt (sub_pos.mpr (g_range _ _).2)
    · constructor
      · exact ne_of_gt (g_range _ _).1
      · apply ne_of_gt
        apply lt_sub_left_of_add_lt
        apply add_lt_of_lt_sub_right
        norm_num
        apply lt_trans (g_range _ _).2 (by norm_num)
  · symm
    apply (Real.mul_log_eq_log_iff (sub_pos_of_lt (g_range _ _).2) (g_range _ _).1).mpr
    rw [← g_satisfies 1 r]
    simp

/-
We generalize w's asymtotic behavior to all positive s and t
-/
lemma w_Asymtotic' (s t: ℝ) [PosReal s] [PosReal t]:
Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) atTop (nhds (g s t)) := by
  -- We first normalize to s = 1 and only consider varying t, which is now renamed to r
  let r := t / s
  have s_cancel: 1 / s * s = 1 := one_div_mul_cancel (ne_of_gt PosReal.pos)
  have t_cancel: 1 / s * t = r := one_div_mul_eq_div s t
  have funrw (n): wₗᵢ s t n = wₗᵢ 1 r n := by
    rw [wₗᵢ_homo s t n (1 / s)]
    congr 1
  have limrw: g s t = g 1 r := by
    rw [g_homo s t (1 / s)]
    congr 1
  conv in fun n ↦ _ =>
    ext n
    rw [funrw n]
  rw [limrw]

  -- We can find two rational sequences approaching r, from below and above
  obtain ⟨below, belowMono, belowLt, belowLim⟩ := Rat.exists_seq_strictMono_tendsto_real r
  obtain ⟨above, aboveMono, aboveLt, aboveLim⟩ := Rat.exists_seq_strictAnti_tendsto_real r

  -- We will use the two rational sequences to squeeze the limit.
  -- However, these are double limit (r' -> r and N -> ∞), so we can't use squeeze theorem directly
  -- We will do a manual ε-δ style proof here

  apply tendsto_atTop_nhds.mpr
  intro U gmem Uopen
  obtain ⟨low, high, ⟨glow, ghigh⟩, substU⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Uopen.mem_nhds gmem)
  -- We unfold the limit definition to an appropriate ε to use
  -- Note we divided the allowed deviation by two. We'd like to have two parts of ε
  -- which we will distribute to both of the double limit
  let ε := (min (g 1 r - low) (high - g 1 r)) / 2
  have εpos: 0 < ε := by
    unfold ε
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff, sub_pos]
    exact ⟨glow, ghigh⟩
  have εsubst: Set.Ioo (g 1 r - ε * 2) (g 1 r + ε * 2) ⊆ U := by
    refine subset_trans ?_ substU
    unfold ε
    rw [div_mul_cancel₀ _ (by simp)]
    apply Set.Ioo_subset_Ioo
    · apply le_sub_comm.mpr
      simp only [inf_le_left]
    · apply add_le_of_le_sub_left
      simp

  -- An adhoc theorem that g is continuous
  have g_continuous: ∃dr > 0, ∀ r', (h: r' ∈ Set.Ioo (max (r - dr) 0) (r + dr)) →
    have: PosReal r' := { pos := (max_lt_iff.mp h.1).2 }
    g 1 r' ∈ Set.Ioo (g 1 r - ε) (g 1 r + ε) := by

    have leftSet: g 1 r < min (g 1 r + ε) 1 := by
      simp only [lt_inf_iff, lt_add_iff_pos_right]
      exact ⟨εpos, (g_range _ _).2⟩
    have ⟨gleft, ⟨gleftRange, gleftValid⟩⟩ := Set.nonempty_Ioo.mpr leftSet
    obtain ⟨gleftε, gleftValid⟩ := lt_min_iff.mp gleftValid

    have rightSet: max (g 1 r - ε) 0 < g 1 r := by
      simp only [sup_lt_iff, sub_lt_self_iff]
      exact ⟨εpos, (g_range _ _).1⟩
    have ⟨gright, ⟨grightValid, grightRange⟩⟩ := Set.nonempty_Ioo.mpr rightSet
    obtain ⟨grightε, grightValid⟩ := max_lt_iff.mp grightValid

    have leftmem: gleft ∈ Set.Ioo 0 1 := ⟨lt_trans (g_range _ _).1 gleftRange, gleftValid⟩
    have rightmem: gright ∈ Set.Ioo 0 1 := ⟨grightValid, lt_trans grightRange (g_range _ _).2⟩

    let rleft := ginv gleft
    let rright := ginv gright
    use min (r - rleft) (rright - r)
    constructor
    · simp only [gt_iff_lt, lt_inf_iff, sub_pos]
      rw [← ginv_comp r]
      constructor
      · exact ginv_anti (g_range _ _) leftmem gleftRange
      · exact ginv_anti rightmem (g_range _ _) grightRange
    · intro r' r'range
      simp only [sub_inf, sub_sub_cancel, add_inf, add_sub_cancel, Set.mem_Ioo, sup_lt_iff,
        lt_inf_iff] at r'range
      obtain ⟨⟨⟨r'left, _⟩, r'pos⟩, ⟨_, r'right⟩⟩ := r'range
      have: PosReal r' := { pos := r'pos }

      suffices g 1 r' ∈ Set.Ioo gright gleft by
        refine Set.mem_of_mem_of_subset this (Set.Ioo_subset_Ioo ?_ ?_)
        · exact le_of_lt grightε
        · exact le_of_lt gleftε
      simp only [Set.mem_Ioo]
      constructor
      · apply (ginv_anti.lt_iff_lt (g_range _ _) rightmem).mp
        rw [ginv_comp]
        exact r'right
      · apply (ginv_anti.lt_iff_lt leftmem (g_range _ _)).mp
        rw [ginv_comp]
        exact r'left
  obtain ⟨dr, drpos, drspec⟩ := g_continuous

  have rmem: r ∈ Set.Ioo (max (r - dr) 0) (r + dr) := by
    constructor
    · simp only [sup_lt_iff, sub_lt_self_iff]
      constructor
      · exact drpos
      · exact PosReal.pos
    · exact lt_add_of_pos_right r drpos

  -- We use one of ε to find close enough r' on the rational sequences
  -- where g 1 r' is close enough to g 1 r on the continous g
  obtain ⟨belowLimN, belowSpec⟩ := tendsto_atTop_nhds.mp belowLim (Set.Ioo (max (r - dr) 0) (r + dr))
    rmem isOpen_Ioo
  obtain belowSpecN := belowSpec belowLimN le_rfl
  obtain belowDr := drspec (below belowLimN) belowSpecN
  simp only at belowDr

  obtain ⟨aboveLimN, aboveSpec⟩ := tendsto_atTop_nhds.mp aboveLim (Set.Ioo (max (r - dr) 0) (r + dr))
    rmem isOpen_Ioo
  obtain aboveSpecN := aboveSpec aboveLimN le_rfl
  obtain aboveDr := drspec (above aboveLimN) aboveSpecN
  simp only at aboveDr

  -- Then we use the other ε to find a large enough n such that for the rational r'
  -- w 1 r' / n is close enough to g 1 r'
  have: PosReal (below belowLimN) := {
    pos := (max_lt_iff.mp belowSpecN.1).2
  }
  have belowRat: (1 / (below belowLimN) :ℝ) ∈ Set.range Rat.cast := by
    use 1 / (below belowLimN)
    simp
  obtain ⟨belowWN, belowW⟩ := tendsto_atTop_nhds.mp (w_Asymtotic_rat 1 (below belowLimN) belowRat)
    (Set.Ioo (g 1 (below belowLimN) - ε) (g 1 (below belowLimN) + ε)) (by simpa using εpos)
    isOpen_Ioo

  have: PosReal (above aboveLimN) := {
    pos := (max_lt_iff.mp aboveSpecN.1).2
  }
  have aboveRat: (1 / (above aboveLimN) :ℝ) ∈ Set.range Rat.cast := by
    use 1 / (above aboveLimN)
    simp
  obtain ⟨aboveWN, aboveW⟩:= tendsto_atTop_nhds.mp (w_Asymtotic_rat 1 (above aboveLimN) aboveRat)
    (Set.Ioo (g 1 (above aboveLimN) - ε) (g 1 (above aboveLimN) + ε)) (by simpa using εpos)
    isOpen_Ioo

  -- We combine the bound from both sequence
  use max 2 (max belowWN aboveWN)
  intro n nrange
  obtain ⟨n2, nr⟩ := max_le_iff.mp nrange
  obtain ⟨nbelow, nabove⟩ := max_le_iff.mp nr
  obtain belowW := belowW n nbelow
  obtain aboveW := aboveW n nabove

  -- Because of monotone, we are able to bound w 1 r / n by rational r'
  apply Set.mem_of_mem_of_subset
  · show wₗᵢ 1 r n / n ∈ Set.Icc  (wₗᵢ 1 (above aboveLimN) n / n) (wₗᵢ 1 (below belowLimN) n / n)
    constructor
    · refine div_le_div_of_nonneg_right ?_ (le_trans (by norm_num) n2)
      apply wₗᵢMono _ _ _ _ _ n2
      simp only [one_div]
      apply (inv_le_inv₀ (by exact PosReal.pos) (by exact PosReal.pos)).mpr
      exact le_of_lt (aboveLt aboveLimN)
    · refine div_le_div_of_nonneg_right ?_ (le_trans (by norm_num) n2)
      apply wₗᵢMono _ _ _ _ _ n2
      simp only [one_div]
      apply (inv_le_inv₀ (by exact PosReal.pos) (by exact PosReal.pos)).mpr
      exact le_of_lt (belowLt belowLimN)
  · refine subset_trans ?_ εsubst
    apply Set.Icc_subset_Ioo
    · refine lt_trans ?_ aboveW.1
      rw [mul_two, ← sub_sub]
      simp only [sub_lt_sub_iff_right]
      exact aboveDr.1
    · refine lt_trans belowW.2 ?_
      rw [mul_two, ← add_assoc]
      simp only [add_lt_add_iff_right]
      exact belowDr.2

theorem w_Asymtotic (s t: ℝ) [PosReal s] [PosReal t]: wₗᵢ s t ~[atTop] wℝ s t := by
  unfold wℝ
  have g0: g s t ≠ 0 := ne_of_gt (g_range s t).1
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · apply eventually_atTop.mpr
    use 1
    intro n n1
    simp only [ne_eq, mul_eq_zero, not_or]
    constructor
    · exact g0
    · exact ne_of_gt (lt_of_lt_of_le (by simp) n1)
  · rw [← div_self g0]
    have fun_rw: (wₗᵢ s t · : ℝ → ℝ) / (g s t * ·) = (fun n ↦ wₗᵢ s t n / n / g s t) := by
      ext n
      simp only [Pi.div_apply]
      rw [mul_comm, div_div]
    rw [fun_rw]
    apply Tendsto.div (w_Asymtotic' s t) tendsto_const_nhds g0
