import BiasedBisect.Basic
import Mathlib.Analysis.Fourier.FourierTransform

open Real
open FourierTransform

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

theorem φ_inv (s t n: ℝ) (n1: n ≥ 1) [PosReal s] [PosReal t]:
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



/-Some culculus-/

lemma ne_zero_of_re_neg {s : ℂ} (hs : 0 > s.re) : s ≠ 0 :=
  fun h ↦ (Complex.zero_re ▸ h ▸ hs).false

lemma exp_dir (f σ: ℝ) (x: ℂ) (σ0: σ > 0):
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
  have right: (-2 * ↑π * ↑f * Complex.I - ↑σ) = (-2 * ↑π * ↑f * Complex.I - ↑σ) * 1 := by
    rw [MulOneClass.mul_one]
  nth_rw 2 [right]
  apply HasDerivAt.const_mul
  apply HasDerivAt.sub_const c
  exact hasDerivAt_id' x

lemma exp_integ(f σ a b: ℝ) (σ0: σ > 0):
∫ x in a..b, Complex.exp ((-2 * π * f * Complex.I - σ) * (x - c)) =
Complex.exp ((-2 * π * f * Complex.I - σ) * (b - c)) / (-2 * π * f * Complex.I - σ) - Complex.exp ((-2 * π * f * Complex.I - σ) * (a - c)) / (-2 * π * f * Complex.I - σ) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x xmem
    apply HasDerivAt.comp_ofReal (exp_dir f σ x σ0)
  · sorry

/-End-/

noncomputable
def U (μ x: ℝ): ℂ := if x ≤ 0 then 0 else if x < μ then x / μ else 1

noncomputable
def Uinteg (μ σ a f: ℝ) := ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ (x - a) * Complex.exp (- σ * x))

noncomputable
def φTerm (s t μ σ: ℝ) (pq: ℕ × ℕ) (x: ℝ): ℂ := Jₚ pq * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x))

noncomputable
def φReg (s t μ σ x: ℝ) := U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x

lemma φReg_Fourier (s t μ σ f: ℝ):
𝓕 (φReg s t μ σ) f = 0 := calc
  𝓕 (φReg s t μ σ) f = 𝓕 (fun x ↦ U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x) f := by
    unfold φReg; rfl
  _ = ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x) + ∑' pq, φTerm s t μ σ pq x) := by
    rw [fourierIntegral_eq']
    simp only [neg_mul, RCLike.inner_apply, conj_trivial, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_ofNat, smul_eq_mul]
  _ = ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x)) + Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * ∑' pq, φTerm s t μ σ pq x := by
    congr 1
    ext x
    apply left_distrib
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * ∑' pq, φTerm s t μ σ pq x := by
    refine MeasureTheory.integral_add ?_ ?_
    sorry
    sorry
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∫ x, ∑' pq, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * φTerm s t μ σ pq x := by
    congr 2
    ext x
    exact Eq.symm tsum_mul_left
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * φTerm s t μ σ pq x := by
    congr 1
    refine MeasureTheory.integral_tsum ?_ ?_
    sorry
    sorry
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, ∫ x, Jₚ pq * (Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x))) := by
    congr 2
    ext pq
    congr 1
    ext x
    unfold φTerm
    ring
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ x * Complex.exp (- σ * x))) + ∑' pq, Jₚ pq * ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x)) := by
    congr 2
    ext pq
    apply MeasureTheory.integral_mul_left
  _ = (∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ (x - 0) * Complex.exp (- σ * x))) + ∑' pq, Jₚ pq * ∫ x, Complex.exp ((↑(-2 * π * (x * f)) * Complex.I)) * (U μ (x - (pq.1 * s + pq.2 * t)) * Complex.exp (- σ * x)) := by
    congr 2
    ext x
    simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_zero]
  _ = (Uinteg μ σ 0 f) + ∑' pq, Jₚ pq * Uinteg μ σ (pq.1 * s + pq.2 * t) f := by
    rfl

  _ = 0 := by sorry
