import BiasedBisect.Inv
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Integral.ExpDecay


open Real
open FourierTransform
open Complex
open MeasureTheory




/-Some culculus-/

lemma ne_zero_of_re_neg {s : ℂ} (hs : 0 > s.re) : s ≠ 0 :=
  fun h ↦ (Complex.zero_re ▸ h ▸ hs).false

lemma exp_dir (f σ: ℝ) (x c: ℂ) (σ0: σ > 0):
HasDerivAt (fun x ↦ Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c)) / (-2 * π * f * Complex.I - σ) )
(Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c))) x
:= by
  have muldiv: Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c)) =
    Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c)) * (-2 * π * f * Complex.I - σ) / (-2 * π * f * Complex.I - σ) := by
    rw [mul_div_cancel_right₀]
    apply ne_zero_of_re_neg
    simp only [neg_mul, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
      Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im,
      zero_mul, add_zero, Complex.I_re, Complex.I_im, mul_one, sub_self, neg_zero, zero_sub,
      gt_iff_lt, Left.neg_neg_iff]
    exact σ0
  rw [muldiv]
  apply HasDerivAt.div_const
  apply HasDerivAt.cexp
  have right: (-2 * π * f * Complex.I - σ) = (-2 * π * f * Complex.I - σ) * 1 := by
    rw [MulOneClass.mul_one]
  nth_rw 2 [right]
  apply HasDerivAt.const_mul
  apply HasDerivAt.sub_const c
  exact hasDerivAt_id' x

lemma exp_integ(f σ c a b: ℝ) (σ0: σ > 0):
∫ x in a..b, Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c)) =
Complex.exp ((-2 * π * f * Complex.I - σ) * (b - c)) / (-2 * π * f * Complex.I - σ) - Complex.exp ((-2 * π * f * Complex.I - σ) * (a - c)) / (-2 * π * f * Complex.I - σ) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x xmem
    apply HasDerivAt.comp_ofReal (exp_dir f σ x c σ0)
  · apply intervalIntegrable_iff.mpr
    apply Continuous.integrableOn_uIoc
    continuity

def MeasureTheory.HasIntegral [NormedAddCommGroup G] [NormedSpace ℝ G] {_ : MeasurableSpace α}
(f : α → G) (μ : MeasureTheory.Measure α) (s : Set α) (result : G) :=
MeasureTheory.IntegrableOn f s μ ∧ ∫ x in s, f x ∂μ = result

lemma MeasureTheory.HasIntegral_union [NormedAddCommGroup G] [NormedSpace ℝ G] {_ : MeasurableSpace α}
{f: α → G} {μ : MeasureTheory.Measure α} {s t : Set α} {a b : G}
(hst : Disjoint s t) (ht : MeasurableSet t)
(hfs : MeasureTheory.HasIntegral f μ s a) (hft : MeasureTheory.HasIntegral f μ t b):
MeasureTheory.HasIntegral f μ (s ∪ t) (a + b) := by
  constructor
  · exact MeasureTheory.IntegrableOn.union (hfs.left) (hft.left)
  · rw [MeasureTheory.setIntegral_union hst ht hfs.left hft.left, hfs.right, hft.right]

lemma MeasureTheory.HasIntegral_congr_ae [NormedAddCommGroup G] [NormedSpace ℝ G] {_ : MeasurableSpace α}
{f g: α → G} {μ : MeasureTheory.Measure α} {s : Set α} {a : G}
(h : f =ᵐ[μ.restrict s] g) (hfs : MeasureTheory.HasIntegral f μ s a):
MeasureTheory.HasIntegral g μ s a := by
  constructor
  · exact MeasureTheory.Integrable.congr hfs.left h
  · rw [← MeasureTheory.integral_congr_ae h]
    exact hfs.right

lemma MeasureTheory.HasIntegralHasSum [NormedAddCommGroup G] [NormedSpace ℝ G] {_ : MeasurableSpace α}
[Countable ι]
{f: ι → α → G} {g: α → G} {μ : MeasureTheory.Measure α} {s : Set α} {a : ι → G} {asum: G}
(hf : ∀ (i : ι), MeasureTheory.HasIntegral (f i) μ s (a i)) (hsum: HasSum a asum) (hfsum: HasSum f g)
(habs: Summable fun (i : ι) => ∫a in s, ‖f i a‖ ∂μ):
MeasureTheory.HasIntegral g μ s asum := by
  constructor
  · sorry
  · rw [← hfsum.tsum_eq]
    have intrw: ∫ (x : α) in s, (∑' (i : ι), f i) x ∂μ = ∫ (x : α) in s, (∑' (i : ι), f i x) ∂μ := by
      congr
      ext x
      apply tsum_apply
      exact hfsum.summable
    rw [intrw]
    rw [← hsum.tsum_eq]
    rw [← MeasureTheory.integral_tsum_of_summable_integral_norm (fun i ↦ (hf i).left) habs]
    congr
    ext i
    exact (hf i).right



noncomputable
def U (μ x: ℝ): ℂ := if x ≤ 0 then 0 else if x ≤ μ then x / μ else 1

noncomputable
def Uexp (μ σ a f x: ℝ): ℂ := Complex.exp (((-2 * π * (f * x)) * Complex.I)) * (U μ (x - a) * Complex.exp (- σ * x))

lemma Uexp_integral (μ σ a f: ℝ):
MeasureTheory.HasIntegral (Uexp μ σ a f) MeasureTheory.volume Set.univ 0 := by
  have left: MeasureTheory.HasIntegral (Uexp μ σ a f) MeasureTheory.volume (Set.Iic a) 0 := by
    have left': MeasureTheory.HasIntegral (fun (x:ℝ) ↦ (0:ℂ)) MeasureTheory.volume (Set.Iic a) 0 := by sorry
    refine MeasureTheory.HasIntegral_congr_ae ?_ left'
    apply (MeasureTheory.ae_restrict_iff' (by exact measurableSet_Iic)).mpr
    apply Filter.Eventually.of_forall
    unfold Uexp U
    simp only [Set.mem_Iic]
    intro x xmem
    have cond: x - a ≤ 0 := by exact sub_nonpos_of_le xmem
    simp only [cond, ↓reduceIte, zero_mul, mul_zero]

  have mid: MeasureTheory.HasIntegral (Uexp μ σ a f) MeasureTheory.volume (Set.Ioc a (a + μ))
    (((((2 * π * f * Complex.I + σ) * μ + 1)) * Complex.exp (-(a + μ) * (2 * π * f * Complex.I + σ))
        - Complex.exp (-a * (2 * π * f * Complex.I + σ)))
        / (-μ * (2 * π * f * Complex.I + σ) ^ 2) :ℂ) := by
    have mid': MeasureTheory.HasIntegral (fun (x:ℝ) ↦ Complex.exp (((-2 * π * (f * x)) * Complex.I)) * ((x - a) / μ * Complex.exp (- σ * x)))
      MeasureTheory.volume (Set.Ioc a (a + μ))
      (((((2 * π * f * Complex.I + σ) * μ + 1)) * Complex.exp (-(a + μ) * (2 * π * f * Complex.I + σ))
        - Complex.exp (-a * (2 * π * f * Complex.I + σ)))
        / (-μ * (2 * π * f * Complex.I + σ) ^ 2) :ℂ) := by sorry
    refine MeasureTheory.HasIntegral_congr_ae ?_ mid'
    apply (MeasureTheory.ae_restrict_iff' (by exact measurableSet_Ioc)).mpr
    apply Filter.Eventually.of_forall
    unfold Uexp U
    simp only [Set.mem_Ioc]
    rintro x ⟨xleft, xright⟩
    have cond1: ¬ x - a ≤ 0 := by simp only [not_le]; exact sub_pos_of_lt xleft
    have cond2: x - a ≤ μ := by exact sub_left_le_of_le_add xright
    simp only [cond1, cond2, ↓reduceIte]
    push_cast
    rfl

  have right: MeasureTheory.HasIntegral (Uexp μ σ a f) MeasureTheory.volume (Set.Ioi (a + μ)) 0 := by sorry

  have leftmid_disjoint: Disjoint (Set.Iic a) (Set.Ioc a (a + μ)) := by sorry
  have leftmid_union: Set.Iic a ∪ Set.Ioc a (a + μ) = Set.Iic (a + μ) := by sorry
  obtain leftmid := MeasureTheory.HasIntegral_union leftmid_disjoint measurableSet_Ioc left mid
  rw [leftmid_union] at leftmid


  have all_disjoint: Disjoint (Set.Iic (a + μ)) (Set.Ioi (a + μ)) := by sorry
  have all_union: (Set.Iic (a + μ)) ∪ (Set.Ioi (a + μ)) = Set.univ := by sorry
  obtain all := MeasureTheory.HasIntegral_union all_disjoint measurableSet_Ioi leftmid right
  rw [all_union] at all
  sorry

lemma UexpSum_integral (μ σ a f: ℝ):
MeasureTheory.HasIntegral (fun x ↦ ∑' pq, Jₚ pq * Uexp μ σ a f x) MeasureTheory.volume Set.univ 0 := by
  sorry

/-End-/

noncomputable
def Uinteg (μ σ a f: ℝ) := ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ (x - a) * Complex.exp (- σ * x))

/-
noncomputable
def φTerm (s t μ σ: ℝ) (pq: ℕ × ℕ) (x: ℝ): ℂ := Jₚ pq * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x))

noncomputable
def φReg (s t μ σ x: ℝ) := U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x

lemma φReg_Fourier (s t μ σ f: ℝ):
𝓕 (φReg s t μ σ) f = 0 := calc
  𝓕 (φReg s t μ σ) f = 𝓕 (fun x ↦ U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x) f := by
    unfold φReg; rfl
  _ = ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x) := by
    rw [fourierIntegral_eq']
    simp only [neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat, smul_eq_mul]
  _ = ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x)) + Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * ∑' pq, φTerm s t μ σ pq x := by
    congr 1
    ext x
    apply left_distrib
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * ∑' pq, φTerm s t μ σ pq x := by
    refine MeasureTheory.integral_add ?_ ?_
    sorry
    sorry
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∫ x, ∑' pq, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * φTerm s t μ σ pq x := by
    congr 2
    ext x
    exact Eq.symm tsum_mul_left
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * φTerm s t μ σ pq x := by
    congr 1
    refine MeasureTheory.integral_tsum ?_ ?_
    sorry
    sorry
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, ∫ x, Jₚ pq * (Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x))) := by
    congr 2
    ext pq
    congr 1
    ext x
    unfold φTerm
    ring_nf
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, Jₚ pq * ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x)) := by
    congr 2
    ext pq
    apply MeasureTheory.integral_mul_left
  _ = (∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ (x - 0) * Complex.exp (- σ * x))) + ∑' pq, Jₚ pq * ∫ x, Complex.exp ((↑(-2 * π * (f * x)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x)) := by
    congr 2
    ext x
    simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_zero]
  _ = (Uinteg μ σ 0 f) + ∑' pq, Jₚ pq * Uinteg μ σ (pq.1 * s + pq.2 * t) f := by
    rfl

  _ = 0 := by sorry
-/


lemma φReg_Fourier_sum_exchange (s t μ σ f: ℝ) :
∫ x:ℝ, ∑' pq, Jₚ pq * Complex.exp ((-(2 * π * f * Complex.I + σ) * x)) * (U μ (x - (pq.1 * s + pq.2 * t))) =
∑' pq, ∫ x:ℝ, Jₚ pq * Complex.exp ((-(2 * π * f * Complex.I + σ) * x)) * (U μ (x - (pq.1 * s + pq.2 * t))) := by
  apply MeasureTheory.integral_tsum
  · intro pq
    apply Continuous.aestronglyMeasurable
    sorry
  · have le: ∑' (pq : ℕ × ℕ), ∫⁻ (x : ℝ), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ ≤
      ∑' (pq : ℕ × ℕ), ∫⁻ x in Set.Ici (pq.1 * s + pq.2 * t), ‖(2 ^ pq.1 * 2 ^ pq.2 * Real.exp (- σ * x))‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro pq
      have split: ∫⁻ (x : ℝ), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ =
        ∫⁻ (x : ℝ) in (Set.Iio (pq.1 * s + pq.2 * t) ∪ Set.Ici (pq.1 * s + pq.2 * t)), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ  := by
        rw [← MeasureTheory.setLIntegral_univ]
        congr
        simp only [Set.Iio_union_Ici]
      rw [split]
      have union: ∫⁻ (x : ℝ) in (Set.Iio (pq.1 * s + pq.2 * t) ∪ Set.Ici (pq.1 * s + pq.2 * t)), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ ≤
        (∫⁻ (x : ℝ) in Set.Iio (pq.1 * s + pq.2 * t), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ) +
        (∫⁻ (x : ℝ) in Set.Ici (pq.1 * s + pq.2 * t), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ) := by apply MeasureTheory.lintegral_union_le
      refine le_trans union ?_
      have leftzero: (∫⁻ (x : ℝ) in Set.Iio (pq.1 * s + pq.2 * t), ‖Jₚ pq * Complex.exp (-(2 * π * f * Complex.I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖ₑ) = 0 := by
        sorry
      rw [leftzero, zero_add]
      gcongr with x

      sorry

    refine ne_top_of_le_ne_top ?_ le

    have eq: ∑' (pq : ℕ × ℕ), ∫⁻ x in Set.Ici (pq.1 * s + pq.2 * t), ‖(2 ^ pq.1 * 2 ^ pq.2 * Real.exp (- σ * x))‖ₑ =
      ∑' (pq : ℕ × ℕ), (‖2 ^ pq.1 * 2 ^ pq.2 * Real.exp (pq.1 * s + pq.2 * t) * σ⁻¹‖₊: ENNReal)  := by
      congr
      ext pq


      sorry

    rw [eq]
    apply ENNReal.tsum_coe_ne_top_iff_summable.mpr


    sorry


lemma φReg_Fourier_sum_exchange' (s t μ σ f: ℝ) :
∑' pq, ∫ x:ℝ, Jₚ pq * cexp ((-(2 * π * f * I + σ) * x)) * (U μ (x - (pq.1 * s + pq.2 * t))) =
∫ x:ℝ, ∑' pq, Jₚ pq * cexp ((-(2 * π * f * I + σ) * x)) * (U μ (x - (pq.1 * s + pq.2 * t))) := by
  apply MeasureTheory.integral_tsum_of_summable_integral_norm
  · rintro ⟨p, q⟩
    sorry
  · have normBound: ∀ (pq:ℕ×ℕ), norm (∫ (x : ℝ), ‖Jₚ pq * cexp (-(2 * π * f * I + σ) * x) * U μ (x - (pq.1 * s + pq.2 * t))‖)
      ≤ 2 ^ pq.1 * 2 ^ pq.2 * rexp (-σ * (pq.1 * s + pq.2 * t)) / σ := by sorry
    refine Summable.of_norm_bounded _ ?_ normBound
    sorry

lemma φReg_Fourier_sum_exchange_integrable (s t μ σ f: ℝ) :
MeasureTheory.Integrable (fun (x: ℝ) ↦ ∑' pq, Jₚ pq * cexp ((-(2 * π * f * I + σ) * x)) * (U μ (x - (pq.1 * s + pq.2 * t)))) := by sorry


lemma φBound (s t x: ℝ) (h: x ≥ - max s t) [PosReal s] [PosReal t]:
φ s t x ≤ rexp ((Real.log 2 / (min s t)) * x) * rexp (Real.log 2 / (min s t) * max s t) := by
  have inductor (n: ℕ): ∀ x ∈ Set.Ico (- max s t) (n * min s t), φ s t x ≤ rexp ((Real.log 2 / (min s t)) * x) * rexp (Real.log 2 / (min s t) * max s t)  := by
    induction n with
    | zero =>
      rintro x ⟨xleft, xright⟩
      simp only [CharP.cast_eq_zero, zero_mul] at xright
      unfold φ
      rw [Jceiled_neg _ _ _ xright]
      rw [← Real.exp_add]
      rw [← mul_add]
      simp only [add_zero, Nat.cast_one, one_le_exp_iff]
      apply mul_nonneg
      · apply le_of_lt
        apply div_pos
        · exact log_pos (by norm_num)
        · simp only [lt_inf_iff]
          exact ⟨PosReal.pos, PosReal.pos⟩
      · exact neg_le_iff_add_nonneg.mp xleft
    | succ n prev =>
      rintro x ⟨xleft, xright⟩
      by_cases xInPrev: x < n * (s ⊓ t)
      · have inprev: x ∈ Set.Ico (-(s ⊔ t)) (n * (s ⊓ t)) := by
          simp only [Set.mem_Ico]
          exact ⟨xleft, xInPrev⟩
        exact prev x inprev
      · simp only [not_lt] at xInPrev
        have x0: 0 ≤ x := by
          refine le_trans ?_ xInPrev
          apply mul_nonneg
          · exact Nat.cast_nonneg' n
          · simp only [le_inf_iff]
            exact ⟨le_of_lt PosReal.pos, le_of_lt PosReal.pos⟩
        rw [φ_rec s t x x0]
        push_cast
        have sInPrev: x - s ∈ Set.Ico (-(s ⊔ t)) (n * (s ⊓ t)) := by
          simp only [Set.mem_Ico]
          constructor
          · simp only [neg_le_sub_iff_le_add]
            exact le_trans (by apply le_max_left: s ≤ max s t) (le_add_of_nonneg_left x0)
          · apply sub_lt_iff_lt_add.mpr
            apply lt_of_lt_of_le xright
            push_cast
            rw [add_one_mul]
            apply add_le_add_left
            exact min_le_left s t
        have tInPrev: x - t ∈ Set.Ico (-(s ⊔ t)) (n * (s ⊓ t)) := by
          simp only [Set.mem_Ico]
          constructor
          · simp only [neg_le_sub_iff_le_add]
            exact le_trans (by apply le_max_right: t ≤ max s t) (le_add_of_nonneg_left x0)
          · apply sub_lt_iff_lt_add.mpr
            apply lt_of_lt_of_le xright
            push_cast
            rw [add_one_mul]
            apply add_le_add_left
            exact min_le_right s t
        obtain leLeft := add_le_add (prev _ sInPrev) (prev _ tInPrev)
        apply le_trans leLeft
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by apply exp_nonneg)
        have split: rexp (Real.log 2 / (min s t) * x) =
          rexp (Real.log 2 / (min s t) * (x - min s t)) + rexp (Real.log 2 / (min s t) * (x - min s t)) := by
          rw [← mul_two]
          nth_rw 3 [(by refine Eq.symm (Real.exp_log ?_); norm_num: 2 = rexp (Real.log 2))]
          rw [← Real.exp_add]
          congr
          apply sub_eq_iff_eq_add'.mp
          rw [← mul_sub]
          simp only [sub_sub_cancel]
          rw [div_mul_cancel₀ _ (by apply ne_of_gt; simp only [lt_inf_iff]; exact ⟨PosReal.pos, PosReal.pos⟩)]
        rw [split]
        apply add_le_add
        all_goals
        · gcongr
          · apply le_of_lt
            apply div_pos
            · exact log_pos (by norm_num)
            · simp only [lt_inf_iff]
              exact ⟨PosReal.pos, PosReal.pos⟩
          · simp only [inf_le_left, inf_le_right]

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
      refine lt_of_lt_of_le ?_ toNatRaise
      apply lt_of_le_of_lt
      · show x / (s ⊓ t) ≤ ↑⌈x / (s ⊓ t)⌉
        apply Int.le_ceil
      · apply lt_add_of_pos_right
        norm_num

  exact inductor n x bound

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
  simp only [Set.mem_Ici, not_le, h, Set.indicator_of_not_mem, zero_add]
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
    apply φBound
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


noncomputable
def φRegFourierIntegrant (s t μ σ f x: ℝ): ℂ :=
  cexp ((((-2 * π * f * x: ℝ) * I))) * (rexp (- σ * x) * (Set.indicator (Set.Ici 0) (fun _ ↦ 1) x + ∑' pq, Jₚ pq * (smStep μ (x - (pq.1 * s + pq.2 * t)))): ℝ)

lemma φReg_Fourier1 (s t μ σ f: ℝ):
𝓕 (fun x ↦ (φReg s t μ σ x:ℂ)) f =
∫ (x:ℝ), φRegFourierIntegrant s t μ σ f x := by
  unfold φReg φRegFourierIntegrant
  rw [fourierIntegral_eq']
  congr
  ext x
  congr 1
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

lemma φReg_Fourier1Integrable (s t μ σ f: ℝ) (σBound: Real.log 2 / (s ⊓ t) < σ) [PosReal s] [PosReal t] [PosReal μ]:
Integrable (φRegFourierIntegrant s t μ σ f) volume := by
  have expIntegrable: IntegrableOn (fun x ↦ rexp ((Real.log 2 / (min s t) - σ) * x) * rexp (Real.log 2 / (min s t) * max s t)) (Set.Ioi 0) volume := by
    apply Integrable.mul_const
    rw [(by ring: (Real.log 2 / (s ⊓ t) - σ) = -(σ - Real.log 2 / (s ⊓ t)))]
    apply exp_neg_integrableOn_Ioi
    exact sub_pos_of_lt σBound
  have integrableOn: IntegrableOn (φRegFourierIntegrant s t μ σ f) (Set.Ioi 0) volume := by
    unfold φRegFourierIntegrant
    apply MeasureTheory.Integrable.mono' expIntegrable
    · apply MeasureTheory.AEStronglyMeasurable.mul
      · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
        apply Continuous.stronglyMeasurable
        continuity
      · rw [(by rfl: (fun x ↦((
          (rexp (-σ * x) * ((Set.Ici 0).indicator (fun x ↦ 1) x + ∑' (pq : ℕ × ℕ), (Jₚ pq) * smStep μ (x - (pq.1 * s + pq.2 * t)))):ℝ):ℂ)) =
          Complex.ofReal ∘ (fun x ↦ rexp (-σ * x) * ((Set.Ici 0).indicator (fun x ↦ 1) x + ∑' (pq : ℕ × ℕ), (Jₚ pq) * smStep μ (x - (pq.1 * s + pq.2 * t)))))]
        apply AEStronglyMeasurable.comp_measurable
        · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
          exact Continuous.stronglyMeasurable continuous_ofReal
        · apply Measurable.mul
          · apply Continuous.measurable
            continuity
          · apply Measurable.add
            · apply Measurable.indicator
              · measurability
              · exact measurableSet_Ici
            · apply Continuous.measurable
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
                continuity
    · apply Filter.Eventually.of_forall
      intro x
      rw [norm_mul]
      rw [(by apply norm_exp_ofReal_mul_I: ‖cexp ((-2 * π * f * x: ℝ) * I)‖ = 1), one_mul]
      rw [Complex.norm_real, norm_eq_abs]
      rw [← φReg]
      rw [abs_of_nonneg (by apply φRegNonneg)]
      apply φRegBound
  apply MeasureTheory.IntegrableOn.integrable_of_ae_not_mem_eq_zero integrableOn
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
