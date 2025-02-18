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
  simp
  unfold kₙ at keq
  unfold φ
  ext δ
  constructor
  · simp
    intro JceiledLe
    contrapose JceiledLe with δGe
    simp
    simp at δGe
    have JceiledLe: (1: ℝ) + Jceiled s t (δₖ s t k) ≤ 1 + Jceiled s t δ := by
      simp
      apply Jceiled_mono
      exact δGe
    apply gt_of_ge_of_gt JceiledLe
    have pull_cast: (1: ℝ) + (Jceiled s t (δₖ s t k)) = ((1 + Jceiled s t (δₖ s t k): ℕ): ℝ) := by
      simp
    have n_accum: 1 + Jceiled s t (δₖ s t k) = nₖ s t (k + 1) := by
      rw [nₖ_accum]
      simp
    rw [pull_cast]
    rw [n_accum]
    by_contra nle
    simp at nle
    have kp1mem: k + 1 ∈ (kceiled s t n).toFinset := by
      unfold kceiled
      simp
      exact nle
    have what: k + 1 ≤ k := by exact Finset.le_max_of_eq kp1mem keq
    simp at what
  · simp
    intro δlt
    by_cases k0: k = 0
    · rw [k0] at δlt
      rw [δ₀] at δlt
      rw [Jceiled_neg s t δ δlt]
      simp
      exact n1
    · have kmem: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
      unfold kceiled at kmem
      simp at kmem
      rw [nₖ_accum] at kmem
      simp [k0] at kmem
      apply le_trans ?_ kmem
      simp
      apply Jceiled_gap'
      rw [← δₖ]
      have h: (k - 1).succ = k := by exact Nat.succ_pred_eq_of_ne_zero k0
      rw [h]
      exact δlt

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
    simp
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
    simp
  _ = (Uinteg μ σ 0 f) + ∑' pq, Jₚ pq * Uinteg μ σ (pq.1 * s + pq.2 * t) f := by
    rfl

  _ = 0 := by sorry
