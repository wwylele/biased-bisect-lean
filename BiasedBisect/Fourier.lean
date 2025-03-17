import BiasedBisect.Inv
import Mathlib.Analysis.Fourier.FourierTransform

open Real
open FourierTransform




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
