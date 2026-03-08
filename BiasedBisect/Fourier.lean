import BiasedBisect.Inv
import BiasedBisect.Multigeometric
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegrableOn


open Real
open FourierTransform
open Complex
open MeasureTheory


lemma ne_zero_of_re_neg {s : ℂ} (hs : 0 > s.re) : s ≠ 0 :=
  fun h ↦ (Complex.zero_re ▸ h ▸ hs).false

lemma φ_grossBound (s t x: ℝ) (h: x ≥ - max s t) [PosReal s] [PosReal t]:
φ s t x ≤ rexp ((Real.log 2 / (min s t)) * x) * rexp (Real.log 2 / (min s t) * max s t) := by
  apply le_trans (φ_bound s t x h).2
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_monotone
  refine mul_le_mul_of_nonneg_right ?_ (neg_le_iff_add_nonneg.mp h)
  apply (ρf_anti s t).le_iff_ge.mp
  rw [ρ_satisfies]
  unfold ρf
  rw [(by norm_num: (1:ℝ) = 2⁻¹ + 2⁻¹)]
  apply add_le_add
  all_goals
  · apply (le_inv_comm₀ (by simp) (Real.exp_pos _)).mp
    rw [← Real.exp_neg, neg_mul, neg_neg, ← mul_div_assoc, mul_comm, mul_div_assoc,
      Real.exp_mul, Real.exp_log (by simp)]
    apply self_le_rpow_of_one_le (by simp)
    apply (one_le_div₀ (lt_min PosReal.pos PosReal.pos)).mpr
    simp

noncomputable
def smStep (μ x: ℝ): ℝ := if x ≤ 0 then 0 else if x ≤ μ then x / μ else 1

lemma smStepContinuous (μ: ℝ) [PosReal μ]: Continuous (smStep μ) := by
  apply Continuous.if
  · intro x xmem
    rw [← Set.Iic, frontier_Iic] at xmem
    simp only [Set.mem_singleton_iff] at xmem
    have cond: x ≤ μ := by
      rw [xmem]
      exact le_of_lt PosReal.pos
    simp only [cond, ↓reduceIte]
    rw [xmem]
    simp only [zero_div]
  · continuity
  · apply Continuous.if
    · intro x xmem
      rw [← Set.Iic, frontier_Iic] at xmem
      simp only [Set.mem_singleton_iff] at xmem
      rw [xmem]
      exact div_self (ne_of_gt PosReal.pos)
    · continuity
    · continuity

lemma smStepLe1 (μ x: ℝ) [PosReal μ]: smStep μ x ≤ 1 := by
  unfold smStep
  split_ifs with x0 x1
  · norm_num
  · exact (div_le_one PosReal.pos).mpr x1
  · exact le_rfl

lemma smStepNonneg (μ x: ℝ) [PosReal μ]: 0 ≤ smStep μ x := by
  unfold smStep
  split_ifs with x0 x1
  · norm_num
  · simp only [not_le] at x0
    exact div_nonneg (le_of_lt x0) (le_of_lt PosReal.pos)
  · norm_num

noncomputable
def φReg (s t μ σ x: ℝ) := rexp (- σ * x) * (Set.indicator (Set.Ici 0) (fun _ ↦ 1) x + ∑' pq,  Jₚ pq * (smStep μ (x - (pq.1 * s + pq.2 * t))))

lemma φRegLe (s t μ σ x: ℝ) [PosReal s] [PosReal t] [PosReal μ]:
φReg s t μ σ x ≤ rexp (- σ * x) * φ s t x := by
  unfold φReg
  refine mul_le_mul_of_nonneg_left ?_ (by apply exp_nonneg)
  unfold φ Jceiled
  push_cast
  apply add_le_add
  · apply Set.indicator_le' (by simp only [Set.mem_Ici, le_refl, implies_true])
      (by simp only [Set.mem_Ici, not_le, zero_le_one, implies_true])
  · have shut: ∀pq ∉ ((Λceiled s t x).toFinset), ((Jₚ pq) * smStep μ (x - (↑pq.1 * s + ↑pq.2 * t)): ℝ) = 0 := by
      intro pq pqnotmem
      unfold Λceiled at pqnotmem
      simp only [Set.mem_toFinset, Set.mem_setOf_eq, not_le] at pqnotmem
      obtain range := sub_nonpos_of_le (le_of_lt pqnotmem)
      apply mul_eq_zero_of_right
      unfold smStep
      simp only [range, ↓reduceIte]
    rw [tsum_eq_sum shut]
    gcongr with pq pqmem
    refine (mul_le_iff_le_one_right ?_).mpr (by apply smStepLe1)
    · norm_cast
      apply Jₚ_nonzero


lemma φReg_neg (s t μ σ x: ℝ) (h: x < 0) [PosReal s] [PosReal t] : φReg s t μ σ x = 0 := by
  unfold φReg
  apply mul_eq_zero_of_right
  simp only [Set.mem_Ici, not_le, h, Set.indicator_of_notMem, zero_add]
  convert tsum_zero with pq
  apply mul_eq_zero_of_right
  unfold smStep
  have cond: x - (pq.1 * s + pq.2 * t) ≤ 0 := by
    apply sub_nonpos_of_le
    apply le_of_lt
    apply lt_of_lt_of_le h
    apply add_nonneg
    all_goals
    · apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · exact le_of_lt PosReal.pos
  simp only [cond, ↓reduceIte]


lemma φRegBound (s t μ σ x: ℝ) [PosReal s] [PosReal t] [PosReal μ]:
φReg s t μ σ x ≤ rexp ((Real.log 2 / (min s t) - σ) * x) * rexp (Real.log 2 / (min s t) * max s t) := by
  obtain xneg|xpos := lt_or_ge x 0
  · rw [φReg_neg _ _ _ _ _ xneg]
    exact mul_nonneg (by apply exp_nonneg) (by apply exp_nonneg)
  · rw [sub_eq_neg_add, add_mul, Real.exp_add, mul_assoc]
    apply le_trans (φRegLe s t μ σ x)
    refine mul_le_mul_of_nonneg_left ?_ (by apply exp_nonneg)
    apply φ_grossBound
    apply le_of_lt
    refine lt_of_lt_of_le ?_ xpos
    simp only [Left.neg_neg_iff, lt_sup_iff]
    left; exact PosReal.pos

lemma φRegNonneg (s t μ σ x: ℝ) [PosReal s] [PosReal t] [PosReal μ]:
0 ≤ φReg s t μ σ x := by
  unfold φReg
  apply mul_nonneg (by apply exp_nonneg)
  apply add_nonneg
  · apply Set.indicator_nonneg
    simp only [Set.mem_Ici, zero_le_one, implies_true]
  · apply tsum_nonneg
    intro pq
    apply mul_nonneg (by apply Nat.cast_nonneg')
    apply smStepNonneg

lemma JceiledContinuous (s t μ : ℝ) [PosReal s] [PosReal t] [PosReal μ]:
Continuous (fun x ↦ ∑' (pq : ℕ × ℕ), Jₚ pq * smStep μ (x - (pq.1 * s + pq.2 * t)))  := by
  let coverSet := fun (x:ℝ) ↦ Set.Iio (x + 1)
  have converSetMap: ∀ (x:ℝ), ∃ (i:ℝ), coverSet i ∈ nhds x := by
    intro x
    use x
    unfold coverSet
    refine Iio_mem_nhds ?_
    exact lt_add_one x
  apply continuous_of_cover_nhds converSetMap
  intro S
  have funcongr: Set.EqOn
    (fun x ↦ ∑' (pq : ℕ × ℕ), ↑(Jₚ pq) * smStep μ (x - (pq.1 * s + pq.2 * t)))
    (fun x ↦ ∑ pq ∈ Λceiled s t (S + 1), ↑(Jₚ pq) * smStep μ (x - (pq.1 * s + pq.2 * t)))
    (coverSet S) := by
    intro x xmem
    unfold coverSet at xmem
    simp only [Set.mem_Iio] at xmem
    simp only
    apply tsum_eq_sum
    intro pq pqnotmem
    unfold Λceiled at pqnotmem
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, not_le] at pqnotmem
    apply mul_eq_zero_of_right
    unfold smStep
    have cond: x - (pq.1 * s + pq.2 * t) ≤ 0 := sub_nonpos_of_le (le_of_lt (lt_trans xmem pqnotmem))
    simp only [cond, ↓reduceIte]
  refine ContinuousOn.congr ?_ funcongr
  apply Continuous.continuousOn
  apply continuous_finset_sum
  intro pq pqmem
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.comp (smStepContinuous μ)
    fun_prop

lemma φRegContinuousAt (s t μ σ x: ℝ) (hx: x ≠ 0) [PosReal s] [PosReal t] [PosReal μ]:
ContinuousAt (φReg s t μ σ) x := by
  obtain neg|pos := lt_or_gt_of_ne hx
  · apply Filter.EventuallyEq.continuousAt (y := 0)
    apply eventually_nhds_iff.mpr
    use Set.Iio 0
    constructor
    · intro y ymem
      simp only [Set.mem_Iio] at ymem
      rw [φReg_neg _ _ _ _ _ ymem]
    · exact ⟨isOpen_Iio, neg⟩
  · apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.add
    · apply Filter.EventuallyEq.continuousAt (y := 1)
      apply eventually_nhds_iff.mpr
      use Set.Ioi 0
      constructor
      · intro y ymem
        simp only [Set.mem_Ioi] at ymem
        obtain ymem' := le_of_lt ymem
        simp only [Set.mem_Ici, ymem', Set.indicator_of_mem]
      · exact ⟨isOpen_Ioi, pos⟩
    · refine ContinuousOn.continuousAt (s := Set.Ioo 0 (x + 1)) ?_ (Ioo_mem_nhds pos (lt_add_one x))
      apply Continuous.continuousOn
      apply JceiledContinuous


lemma φRegMeasurable (s t μ σ: ℝ) [PosReal s] [PosReal t] [PosReal μ]:
Measurable (φReg s t μ σ) := by
  apply Measurable.mul
  · apply Continuous.measurable
    continuity
  · apply Measurable.add
    · apply Measurable.indicator
      · measurability
      · exact measurableSet_Ici
    · apply Continuous.measurable
      apply JceiledContinuous

noncomputable
def φRegFourierIntegrant (s t μ σ f x: ℝ): ℂ :=
  cexp ((-2 * π * f * x: ℝ) * I) * (rexp (- σ * x) * (Set.indicator (Set.Ici 0) (fun _ ↦ 1) x + ∑' pq, Jₚ pq * (smStep μ (x - (pq.1 * s + pq.2 * t)))): ℝ)

set_option backward.isDefEq.respectTransparency false in
lemma φReg_Fourier1 (s t μ σ f: ℝ):
𝓕 (fun x ↦ (φReg s t μ σ x:ℂ)) f =
∫ (x:ℝ), φRegFourierIntegrant s t μ σ f x := by
  unfold φReg φRegFourierIntegrant
  rw [fourier_eq']
  congr
  ext x
  congr 1
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

lemma φReg_FourierIntegrable (s t μ σ f: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) [PosReal s] [PosReal t] [PosReal μ]:
Integrable (φRegFourierIntegrant s t μ σ f) := by
  have expIntegrable: IntegrableOn (fun x ↦ rexp ((Real.log 2 / (min s t) - σ) * x) * rexp (Real.log 2 / (min s t) * max s t)) (Set.Ioi 0) volume := by
    apply Integrable.mul_const
    rw [(by ring: (Real.log 2 / (s ⊓ t) - σ) = -(σ - Real.log 2 / (s ⊓ t)))]
    apply exp_neg_integrableOn_Ioi
    exact sub_pos_of_lt σBound
  have integrableOn: IntegrableOn (φRegFourierIntegrant s t μ σ f) (Set.Ioi 0) := by
    unfold φRegFourierIntegrant
    apply MeasureTheory.Integrable.mono' expIntegrable
    · apply MeasureTheory.AEStronglyMeasurable.mul
      · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
        apply Continuous.stronglyMeasurable
        continuity
      · rw [(by rfl: (fun x ↦((
          (rexp (-σ * x) * ((Set.Ici 0).indicator (fun x ↦ 1) x + ∑' (pq : ℕ × ℕ), (Jₚ pq) * smStep μ (x - (pq.1 * s + pq.2 * t)))):ℝ):ℂ)) =
          Complex.ofReal ∘ φReg s t μ σ)]
        apply AEStronglyMeasurable.comp_measurable
        · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
          exact Continuous.stronglyMeasurable continuous_ofReal
        · apply φRegMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      rw [norm_mul]
      rw [(by apply norm_exp_ofReal_mul_I: ‖cexp ((-2 * π * f * x: ℝ) * I)‖ = 1), one_mul]
      rw [Complex.norm_real, norm_eq_abs]
      rw [← φReg]
      rw [abs_of_nonneg (by apply φRegNonneg)]
      apply φRegBound
  apply MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero integrableOn
  simp only [Set.mem_Ioi, not_lt]
  suffices ∀ᵐ (x : ℝ), x ∈ Set.Iic 0 → φRegFourierIntegrant s t μ σ f x = 0 by exact this
  rw [← MeasureTheory.ae_restrict_iff' measurableSet_Iic,
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Iio_ae_eq_Iic.symm,
    MeasureTheory.ae_restrict_iff' measurableSet_Iio]
  apply Filter.Eventually.of_forall
  intro x xmem
  simp only [Set.mem_Iio] at xmem
  unfold φRegFourierIntegrant
  apply mul_eq_zero_of_right
  norm_cast
  rw [← φReg]
  exact φReg_neg _ _ _ _ _ xmem

noncomputable
def φRegFourierIntegrantLeft (σ f x: ℝ) :=
  Set.indicator (Set.Ici 0) (fun (x:ℝ) ↦ cexp (-(2 * π * f * I + σ) * x)) x

noncomputable
def φRegFourierIntegrantRight (s t μ σ f x: ℝ) :=
  ∑' pq, Jₚ pq * cexp (-(2 * π * f * I + σ) * x) * (smStep μ (x - (pq.1 * s + pq.2 * t)))

lemma indicator_cast {s: Set α} {f : α → ℝ} {x: α}:
  ((s.indicator f x: ℝ): ℂ) = s.indicator (fun a ↦ ((f a): ℂ)) x := by
  obtain k := map_indicator Complex.ofRealHom.toAddMonoidHom s f x
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ofRealHom_eq_coe] at k
  exact k


lemma φRegFourierIntegrantRw1 (s t μ σ f x: ℝ):
φRegFourierIntegrant s t μ σ f x =
φRegFourierIntegrantLeft σ f x + φRegFourierIntegrantRight s t μ σ f x := by
  unfold φRegFourierIntegrant
  push_cast
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  rw [(by ring: -2 * π * f * x * I + -σ * x = -(2 * π * f * I + σ) * x)]
  rw [mul_add]
  congr 1
  · unfold φRegFourierIntegrantLeft
    rw [indicator_cast]
    rw [← Set.indicator_mul_right _ (fun (x: ℝ) ↦ cexp (-(2 * π * f * I + σ) * x))]
    simp only [ofReal_one, mul_one]
  · unfold φRegFourierIntegrantRight
    rw [← tsum_mul_left]
    congr
    ext pq
    ring

lemma integrable_exp_mul_complex_Ioi {a: ℝ} {c : ℂ} (hc : c.re < 0):
IntegrableOn (fun (x: ℝ) ↦ Complex.exp (c * x)) (Set.Ioi a) := by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simp_rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    set b := -c.re
    rw [(by unfold b; simp only [neg_neg]: c.re = -b)]
    apply exp_neg_integrableOn_Ioi
    unfold b
    exact Left.neg_pos_iff.mpr hc

lemma rexp_mul_n (x: ℝ) (n: ℕ): rexp (x * n) = (rexp x) ^ n := by
  rw [Real.exp_mul]
  simp only [rpow_natCast]

lemma φReg_Fourier2 (s t μ σ f: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) [PosReal s] [PosReal t] [PosReal μ]:
𝓕 (fun x ↦ (φReg s t μ σ x:ℂ)) f =
(2 * π * f * I + σ)⁻¹ + ∫ (x:ℝ), φRegFourierIntegrantRight s t μ σ f x := by
  have σpos: 0 < σ:= by
    refine lt_trans ?_ σBound
    apply div_pos (log_pos (by norm_num))
    simp only [lt_inf_iff]
    exact ⟨PosReal.pos, PosReal.pos⟩
  have leftIntegrable: MeasureTheory.Integrable (φRegFourierIntegrantLeft σ f) := by
    unfold φRegFourierIntegrantLeft
    apply (MeasureTheory.integrable_indicator_iff measurableSet_Ici).mpr
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr
    apply (MeasureTheory.integrable_norm_iff (by apply Continuous.aestronglyMeasurable; fun_prop)).mp
    have exprw: (fun (x:ℝ) ↦ ‖cexp (-(2 * π * f * I + σ) * x)‖) = fun (x:ℝ) ↦ rexp (-σ * x) := by
      ext x
      rw [neg_add, add_mul, Complex.exp_add, norm_mul]
      rw [(by push_cast; ring: (-(2 * π * f * I) * x: ℂ) = (-2 * π * f * x: ℝ) * I)]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
      norm_cast
      exact norm_of_nonneg (exp_nonneg _)
    rw [exprw]
    exact exp_neg_integrableOn_Ioi 0 σpos

  have rightIntegrable: MeasureTheory.Integrable (φRegFourierIntegrantRight s t μ σ f) := by
    have subeq: φRegFourierIntegrantRight s t μ σ f = φRegFourierIntegrant s t μ σ f - φRegFourierIntegrantLeft σ f := by
      ext x
      simp only [Pi.sub_apply]
      rw [φRegFourierIntegrantRw1]
      ring
    rw [subeq]
    apply MeasureTheory.Integrable.sub (φReg_FourierIntegrable s t μ σ f σBound) leftIntegrable
  rw [φReg_Fourier1]
  simp_rw [φRegFourierIntegrantRw1]
  rw [integral_add leftIntegrable rightIntegrable]
  apply add_right_cancel_iff.mpr
  unfold φRegFourierIntegrantLeft
  rw [MeasureTheory.integral_indicator measurableSet_Ici]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [integral_exp_mul_complex_Ioi ?_ _]
  · simp only [neg_add_rev, ofReal_zero, mul_zero, Complex.exp_zero]
    rw [neg_div, ← div_neg]
    rw [one_div]
    congr
    simp only [neg_add_rev, neg_neg]
  · simp only [neg_add_rev, add_re, neg_re, ofReal_re, mul_re, re_ofNat, im_ofNat, ofReal_im,
    mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one, sub_self, neg_zero,
    Left.neg_neg_iff]
    exact σpos



noncomputable
def φRegFourierIntegrantRightSummand (δ μ: ℝ) (l: ℂ) :=
  ∫ (x:ℝ), cexp (l * x) * (smStep μ (x - δ))

set_option backward.isDefEq.respectTransparency false in
lemma φRegFourierIntegrantRightExchange (s t μ σ f: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) [PosReal s] [PosReal t] [PosReal μ]:
∫ (x:ℝ), φRegFourierIntegrantRight s t μ σ f x = ∑' pq, Jₚ pq * φRegFourierIntegrantRightSummand (pq.1 * s + pq.2 * t) μ (-(2 * π * f * I + σ)) := by
  have σpos: 0 < σ:= by
    refine lt_trans ?_ σBound
    apply div_pos (log_pos (by norm_num))
    simp only [lt_inf_iff]
    exact ⟨PosReal.pos, PosReal.pos⟩
  have σBound': Real.log 2 < σ * (s ⊓ t) := by
    refine (div_lt_iff₀ ?_).mp σBound;
    simp only [lt_inf_iff]
    exact ⟨PosReal.pos, PosReal.pos⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt σpos)] at σBound'
  obtain ⟨sBound, tBound⟩ := lt_inf_iff.mp σBound'
  unfold φRegFourierIntegrantRight φRegFourierIntegrantRightSummand
  simp_rw [← integral_const_mul, ← mul_assoc]
  symm
  apply MeasureTheory.integral_tsum_of_summable_integral_norm
  · rintro ⟨p, q⟩
    conv in (fun x ↦ _) =>
      intro x
      rw [mul_assoc]
    apply Integrable.const_mul
    have cexpIntegrable: IntegrableOn (fun (x: ℝ) ↦ cexp (-(2 * π * f * I + σ) * x)) (Set.Ioi 0) := by
      apply integrable_exp_mul_complex_Ioi
      simp only [neg_add_rev, add_re, neg_re, ofReal_re, mul_re, re_ofNat, im_ofNat, ofReal_im,
        mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one, sub_self, neg_zero,
        Left.neg_neg_iff]
      exact σpos
    obtain cexpIntegrable' := Integrable.norm cexpIntegrable
    refine MeasureTheory.IntegrableOn.integrable_of_ae_notMem_eq_zero (s := (Set.Ioi 0)) ?_ ?_
    · apply Integrable.mono' cexpIntegrable'
      · apply Continuous.aestronglyMeasurable
        apply Continuous.mul (by fun_prop)
        exact Continuous.comp' continuous_ofReal (Continuous.comp' (smStepContinuous μ) (by fun_prop))
      · apply Filter.Eventually.of_forall
        intro x
        rw [norm_mul]
        apply (mul_le_of_le_one_right (by apply norm_nonneg))
        norm_cast
        rw [norm_eq_abs]
        rw [abs_eq_self.mpr (by apply smStepNonneg)]
        apply smStepLe1
    · apply Filter.Eventually.of_forall
      intro x xmem
      simp only [Set.mem_Ioi, not_lt] at xmem
      apply mul_eq_zero_of_right
      norm_cast
      have cond: x - (p * s + q * t) ≤ 0 := by
        apply sub_nonpos_of_le
        apply le_trans xmem
        apply add_nonneg
        all_goals exact mul_nonneg (by apply Nat.cast_nonneg) (le_of_lt PosReal.pos)
      unfold smStep
      simp only [cond, ↓reduceIte]
  · have normBound: ∀ (pq:ℕ×ℕ), norm (∫ (x : ℝ), ‖(Jₚ pq) * cexp (-(2 * π * f * I + σ) * x) * (smStep μ (x - (pq.1 * s + pq.2 * t)))‖)
      ≤ 2 ^ pq.1 * 2 ^ pq.2 * (rexp (-σ * (pq.1 * s + pq.2 * t)) / σ) := by
      intro pq
      conv in (fun x ↦ _) =>
        intro x
        rw [mul_assoc, norm_mul]
      rw [integral_const_mul]
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (by apply norm_nonneg) ?_
      · norm_cast
        apply Jₚ_bound
      · rw [norm_eq_abs]
        rw [abs_eq_self.mpr (by apply integral_nonneg; intro x; simp only [Pi.zero_apply]; apply norm_nonneg)]
        simp_rw [norm_mul, norm_exp]
        have union: (Set.univ: Set ℝ) = Set.Ioi (pq.1 * s + pq.2 * t)∪ Set.Iic (pq.1 * s + pq.2 * t) := by
          rw [Set.union_comm]; simp only [Set.Iic_union_Ioi]
        rw [← MeasureTheory.setIntegral_univ, union]
        rw [MeasureTheory.integral_union_eq_left_of_forall measurableSet_Iic ?_]
        · have rightrw: rexp (-σ * (pq.1 * s + pq.2 * t)) / σ = ∫ (x : ℝ) in Set.Ioi (pq.1 * s + pq.2 * t), Real.exp (-σ * x) := by
            symm
            apply Complex.ofReal_inj.mp
            convert integral_exp_mul_complex_Ioi (a := -σ) ?_ (pq.1 * s + pq.2 * t)
            · norm_cast
            · norm_cast
              simp only [neg_mul, neg_div_neg_eq]
            · simp only [neg_re, ofReal_re, Left.neg_neg_iff]
              exact σpos
          rw [rightrw]
          gcongr with x hx
          · refine Integrable.mono' (g := fun x ↦ Real.exp (-σ * x)) (exp_neg_integrableOn_Ioi _ σpos) ?_ ?_
            · apply Continuous.aestronglyMeasurable
              apply Continuous.mul (by fun_prop)
              exact Continuous.comp' continuous_norm (
                Continuous.comp' continuous_ofReal (Continuous.comp' (smStepContinuous μ) (by fun_prop)))
            · apply Filter.Eventually.of_forall
              intro x
              simp only [neg_add_rev, mul_re, add_re, neg_re, ofReal_re, re_ofNat, im_ofNat,
                ofReal_im, mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one,
                sub_self, neg_zero, neg_mul, add_im, neg_im, zero_add, norm_real, norm_eq_abs,
                norm_mul, Real.abs_exp, abs_abs]
              apply (mul_le_of_le_one_right (by apply exp_nonneg))
              rw [abs_eq_self.mpr (by apply smStepNonneg)]
              apply smStepLe1
          · exact exp_neg_integrableOn_Ioi _ σpos
          · exact measurableSet_Ioi.nullMeasurableSet
          · simp only [neg_add_rev, mul_re, add_re, neg_re, ofReal_re, re_ofNat, im_ofNat,
              ofReal_im, mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one,
              sub_self, neg_zero, neg_mul, add_im, neg_im, zero_add, norm_real, norm_eq_abs]
            apply (mul_le_of_le_one_right (by apply exp_nonneg))
            rw [abs_eq_self.mpr (by apply smStepNonneg)]
            apply smStepLe1
        · intro x xmem
          simp only [Set.mem_Iic] at xmem
          apply mul_eq_zero_of_right
          simp only [norm_real, norm_eq_abs, abs_eq_zero]
          unfold smStep
          obtain cond := sub_nonpos_of_le xmem
          simp only [cond, ↓reduceIte]
      · apply mul_nonneg
        all_goals
        · apply pow_nonneg
          · norm_num
    refine Summable.of_norm_bounded ?_ normBound

    have summandRw: (fun (pq: ℕ × ℕ) ↦ 2 ^ pq.1 * 2 ^ pq.2 * (rexp (-σ * (pq.1 * s + pq.2 * t)) / σ))
     = fun (pq: ℕ × ℕ) ↦ ((2 * rexp (-σ * s)) ^ pq.1 * (2 * rexp (-σ * t)) ^ pq.2) / σ := by
      ext pq
      rw [mul_pow, mul_pow]
      rw [← rexp_mul_n, ← rexp_mul_n]
      rw [mul_add, Real.exp_add]
      field_simp

    rw [summandRw]
    apply Summable.div_const
    apply Summable.mul_of_nonneg
    · simp only [neg_mul, summable_geometric_iff_norm_lt_one, norm_mul, Real.norm_ofNat,
        norm_eq_abs, Real.abs_exp]
      rw [Real.exp_neg]
      apply (mul_inv_lt_iff₀ (by apply exp_pos)).mpr
      simp only [one_mul]
      apply (log_lt_iff_lt_exp (by norm_num)).mp
      exact sBound
    · simp only [neg_mul, summable_geometric_iff_norm_lt_one, norm_mul, Real.norm_ofNat,
        norm_eq_abs, Real.abs_exp]
      rw [Real.exp_neg]
      apply (mul_inv_lt_iff₀ (by apply exp_pos)).mpr
      simp only [one_mul]
      apply (log_lt_iff_lt_exp (by norm_num)).mp
      exact tBound
    · intro p
      simp only [Pi.zero_apply]
      apply pow_nonneg
      apply mul_nonneg
      · norm_num
      · apply exp_nonneg
    · intro p
      simp only [Pi.zero_apply]
      apply pow_nonneg
      apply mul_nonneg
      · norm_num
      · apply exp_nonneg

set_option backward.isDefEq.respectTransparency false in
lemma φRegFourierIntegrantRightSummandEq (δ μ: ℝ) (l: ℂ) (hl: l.re < 0) [PosReal μ]:
φRegFourierIntegrantRightSummand δ μ l = cexp (l * δ) * (1 - cexp (l * μ)) / (l ^ 2 * μ) := by
  rw [mul_sub, ← Complex.exp_add, ← mul_add]

  unfold φRegFourierIntegrantRightSummand
  have union: (Set.univ: Set ℝ) = (Set.Ioc δ (δ + μ) ∪ Set.Ioi (δ + μ)) ∪ Set.Iic δ := by
    rw [Set.union_comm];
    rw [Set.Ioc_union_Ioi_eq_Ioi ((le_add_iff_nonneg_right δ).mpr (le_of_lt PosReal.pos))]
    simp only [Set.Iic_union_Ioi]
  rw [← MeasureTheory.setIntegral_univ, union]
  have leftZero: ∀ x ∈ Set.Iic δ, cexp (l * ↑x) * smStep μ (x - δ) = 0 := by
    intro x xmem
    simp only [Set.mem_Iic] at xmem
    apply mul_eq_zero_of_right
    norm_cast
    unfold smStep
    obtain cond := sub_nonpos_of_le xmem
    simp only [cond, ↓reduceIte]

  rw [MeasureTheory.integral_union_eq_left_of_forall measurableSet_Iic leftZero]

  have μ0: (μ : ℂ) ≠ 0 := by norm_cast; exact ne_of_gt PosReal.pos
  have l0: l ≠ 0 := ne_zero_of_re_neg hl
  have l2μ0: l ^ 2 * μ ≠ 0 := by
    refine mul_ne_zero ?_ μ0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact l0


  have Leftfcongr: (fun (x: ℝ) ↦ (cexp (l * x) * smStep μ (x - δ): ℂ)) =ᵐ[volume.restrict (Set.Ioc δ (δ + μ))]
    (fun (x: ℝ) ↦ (cexp (l * x) * ((x - δ) / μ): ℂ)) := by
    apply (MeasureTheory.ae_restrict_iff' (by exact measurableSet_Ioc)).mpr
    apply Filter.Eventually.of_forall
    intro x xmem
    obtain ⟨c1, c2⟩ := xmem
    simp only [mul_eq_mul_left_iff, Complex.exp_ne_zero, or_false]
    unfold smStep
    have cond1: ¬ x - δ ≤ 0 := by simp only [tsub_le_iff_right, zero_add, not_le]; exact c1
    have cond2: x - δ ≤ μ := by exact tsub_le_iff_left.mpr c2
    simp only [cond1, cond2, ↓reduceIte]
    norm_cast

  have leftIntegral: ∫ (x : ℝ) in Set.Ioc δ (δ + μ), cexp (l * x) * smStep μ (x - δ) =
      (cexp (l * (δ + μ)) * (l * μ - 1) + cexp (l * δ)) / (l ^ 2 * μ) := by
    rw [MeasureTheory.integral_congr_ae Leftfcongr]
    have der (x: ℝ): HasDerivAt (fun (x: ℝ) ↦ cexp (l * x) * ((l * x - l * δ - 1) / (l ^ 2 * μ): ℂ)) (cexp (l * x) * ((x - δ) / μ): ℂ) x := by
      rw [(by field_simp [μ0, l2μ0]; ring:
        (cexp (l * x) * ((x - δ) / μ): ℂ) =
        ((l * 1) * cexp (l * x) * ((l * x - l * δ - 1) / (l ^ 2 * μ)): ℂ) + (cexp (l * x) * ((l * 1) / (l^2 * μ)): ℂ))]
      apply HasDerivAt.mul
      · rw [mul_comm]
        apply (Complex.hasDerivAt_exp _).comp x _
        exact ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
      · apply HasDerivAt.div_const
        simp only [hasDerivAt_sub_const_iff]
        exact ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
    rw [← intervalIntegral.integral_of_le ((le_add_iff_nonneg_right δ).mpr (le_of_lt PosReal.pos))]
    rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (der x).deriv) (fun x _ => (der x).differentiableAt) (by fun_prop)]
    field_simp [l2μ0]
    push_cast
    ring


  have Rightfcongr: (fun (x: ℝ) ↦ (cexp (l * x) * smStep μ (x - δ): ℂ)) =ᵐ[volume.restrict (Set.Ioi (δ + μ))]
    (fun (x: ℝ) ↦ cexp (l * x)) := by
    apply (MeasureTheory.ae_restrict_iff' (by exact measurableSet_Ioi)).mpr
    apply Filter.Eventually.of_forall
    intro x xmem
    simp only [Set.mem_Ioi] at xmem
    have cond2: ¬ x - δ ≤ μ := by rw [not_le]; exact lt_tsub_iff_left.mpr xmem
    have cond1: ¬ x - δ ≤ 0 := by
      rw [not_le]
      obtain c2 := not_le.mp cond2
      exact lt_trans PosReal.pos c2
    unfold smStep
    simp only [cond1, cond2, ↓reduceIte, ofReal_one, mul_one]

  have rightIntegral: ∫ (x : ℝ) in Set.Ioi (δ + μ), cexp (l * x) * smStep μ (x - δ) =
      -cexp (l * (δ + μ)) / l := by
    rw [MeasureTheory.integral_congr_ae Rightfcongr]
    rw [integral_exp_mul_complex_Ioi hl _]
    norm_cast

  rw [(by field_simp [l0, l2μ0]; ring:
    (cexp (l * δ) * 1 - cexp (l * (δ + μ))) / (l ^ 2 * μ) =
    (cexp (l * (δ + μ)) * (l * μ - 1: ℂ) + cexp (l * δ)) / (l ^ 2 * μ) + (-cexp (l * (δ + μ)) / l))]

  rw [← leftIntegral, ← rightIntegral]
  apply MeasureTheory.setIntegral_union
  · simp only [le_refl, Set.Ioc_disjoint_Ioi]
  · exact measurableSet_Ioi
  · refine MeasureTheory.IntegrableOn.congr_fun_ae ?_ Leftfcongr.symm
    apply Continuous.integrableOn_Ioc
    fun_prop
  · refine MeasureTheory.IntegrableOn.congr_fun_ae ?_ Rightfcongr.symm
    apply integrable_exp_mul_complex_Ioi
    exact hl

noncomputable
def φRegFourierResult (s t μ σ f: ℝ) := (2 * π * f * I + σ)⁻¹ +
  (1 - (cexp (-(2 * π * f * I + σ) * s) + cexp (-(2 * π * f * I + σ) * t)))⁻¹ *
  ((1 - cexp (-(2 * π * f * I + σ) * μ)) / ((2 * π * f * I + σ) ^ 2 * μ))

lemma φReg_Fourier (s t μ σ: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) [PosReal s] [PosReal t] [PosReal μ]:
𝓕 (fun x ↦ (φReg s t μ σ x:ℂ)) = φRegFourierResult s t μ σ := by
  ext f
  have σpos: 0 < σ:= by
    refine lt_trans ?_ σBound
    apply div_pos (log_pos (by norm_num))
    simp only [lt_inf_iff]
    exact ⟨PosReal.pos, PosReal.pos⟩
  have σBound': Real.log 2 < σ * (s ⊓ t) := by
    refine (div_lt_iff₀ ?_).mp σBound;
    simp only [lt_inf_iff]
    exact ⟨PosReal.pos, PosReal.pos⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt σpos)] at σBound'
  obtain ⟨sBound, tBound⟩ := lt_inf_iff.mp σBound'
  rw [φReg_Fourier2 _ _ _ _ _ σBound]
  rw [φRegFourierIntegrantRightExchange _ _ _ _ _ σBound]
  have h: (-(2 * π * f * I + σ)).re < 0 := by
    simp only [neg_add_rev, add_re, neg_re, ofReal_re, mul_re, re_ofNat, im_ofNat, ofReal_im,
      mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one, sub_self, neg_zero,
      Left.neg_neg_iff]
    exact σpos
  conv in (fun pq ↦ _) =>
    ext pq
    rw [φRegFourierIntegrantRightSummandEq _ _ _ h]
    rw [Complex.ofReal_add, mul_comm _ s, mul_comm _ t, Complex.ofReal_mul, Complex.ofReal_mul,
       mul_add, Complex.exp_add, ← mul_assoc _ (s:ℂ) _, ← mul_assoc _ (t:ℂ) _, ]
    simp only [ofReal_natCast]
    rw [mul_comm _ (pq.1:ℂ), mul_comm _ (pq.2:ℂ), Complex.exp_nat_mul, Complex.exp_nat_mul]
    rw [← mul_div, ← mul_assoc, ← mul_assoc]
  rw [tsum_mul_right]
  rw [neg_pow_two]
  congr
  refine (bigeometric_series (cexp (-(2 * π * f * I + σ) * s)) (cexp (-(2 * π * f * I + σ) * t)) ?_ ?_).tsum_eq
  all_goals
  · rw [Complex.norm_exp]
    simp only [neg_add_rev, mul_re, add_re, neg_re, ofReal_re, re_ofNat, im_ofNat, ofReal_im,
      mul_zero, sub_zero, mul_im, zero_mul, add_zero, I_re, I_im, mul_one, sub_self, neg_zero,
      neg_mul, add_im, neg_im, zero_add]
    rw [Real.exp_neg]
    refine (inv_lt_inv₀ (by apply exp_pos) (by norm_num)).mpr ?_
    refine (log_lt_iff_lt_exp (by norm_num)).mp ?_
    try exact sBound
    try exact tBound

/-
lemma φReg_FourierInv (s t μ σ x: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) (xBound: 0 < x)
[PosReal s] [PosReal t] [PosReal μ]:
𝓕⁻ (φRegFourierResult s t μ σ) x = φReg s t μ σ x := by
  rw [← φReg_Fourier _ _ _ _ σBound]
  apply MeasureTheory.Integrable.fourier_inversion
  · obtain finteg := φReg_FourierIntegrable s t μ σ 0 σBound
    unfold φRegFourierIntegrant at finteg
    conv at finteg in (fun x ↦ _) =>
      ext x
      rw [(by simp only [neg_mul, mul_zero, zero_mul, ofReal_zero, Complex.exp_zero]:
        cexp ((-2 * π * 0 * x: ℝ) * I) = 1)]
      rw [one_mul]
    exact finteg
  · rw [φReg_Fourier _ _ _ _ σBound]
    unfold φRegFourierResult
    sorry
  · apply ContinuousAt.comp continuous_ofReal.continuousAt
    apply φRegContinuousAt
    exact ne_of_gt xBound


def rootSet (s t: ℝ): Set ℂ := sorry

noncomputable
def φRegFourierDecompTerm (s t μ: ℝ) (z r: ℂ) :=
  (1 - cexp (-μ * r)) / (μ * r ^ 2 * (z - r) * (s * cexp (-s * r) + t * cexp (-t * r)))

lemma φRegFourierDecomp (s t μ σ f: ℝ):
φRegFourierResult s t μ σ f = ∑' r: rootSet s t, φRegFourierDecompTerm s t μ (2 * π * f * I + σ) r := by
  sorry
-/
