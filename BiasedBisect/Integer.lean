import BiasedBisect.Basic
import BiasedBisect.Inv

import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Int.Basic

/-

This file discusses when s and t are positive integers.

Most statements here can be generalized to when s/t are rationals,
but the generalization will be deferred to homogeneity.

-/

instance PNat_is_pos (s: ℕ+): PosReal s where
  pos := by
    have nat: (s: ℕ) > 0 := by exact PNat.pos s
    exact Nat.cast_pos'.mpr nat

/-
When s and t are positive integers, Δ collaps to a subset of l * gcd(s, t)
-/
theorem Δ_int (s t: ℕ+):
Δ s t ⊆ {δ: ℝ | ∃l: ℕ, δ = l * PNat.gcd s t} := by
  simp
  intro δ mem
  unfold Δ at mem
  unfold is_δ at mem
  simp at mem
  rcases mem with ⟨p, ⟨q, pq⟩⟩
  simp
  use p * (s / (PNat.gcd s t)) + q * (t / (PNat.gcd s t))
  push_cast
  rw [add_mul]
  rw [← pq]
  rw [mul_assoc]
  rw [mul_assoc]
  congr 2
  · rw [← Nat.cast_mul]
    apply Nat.cast_inj.mpr
    refine (Nat.div_eq_iff_eq_mul_left ?_ ?_).mp rfl
    · refine Nat.gcd_pos_of_pos_left t ?_
      exact PNat.pos s
    · apply Nat.gcd_dvd_left
  · rw [← Nat.cast_mul]
    apply Nat.cast_inj.mpr
    refine (Nat.div_eq_iff_eq_mul_left ?_ ?_).mp rfl
    · refine Nat.gcd_pos_of_pos_left t ?_
      exact PNat.pos s
    · apply Nat.gcd_dvd_right

/-
And obviously, all δ are integers (natural numbers to be precise,
but keeping it in ℤ simplifies some reasoning later)
We will also start
-/
theorem δlift (s t: ℕ+) (δ: ℝ) (mem: δ ∈ Δ s t): ∃d: ℤ, d = δ := by
  unfold Δ at mem
  unfold is_δ at mem
  simp at mem
  rcases mem with ⟨p, ⟨q, pq⟩⟩
  use p * s + q * t
  push_cast
  exact pq

theorem δnext_int (s t: ℕ+) (δ: ℤ): ∃d': ℤ, d' = δnext s t δ := by
  rcases δlift s t (δnext s t δ) (δnext_in_Δ s t δ) with ⟨d', eq⟩
  use d'

/-
Since δ are all integers, their gaps is at least 1
-/
lemma δnext_int_larger (s t: ℕ+) (δ: ℤ): δnext s t δ >= δ + 1 := by
  rcases δnext_int s t δ with ⟨d', eq⟩
  rw [← eq]
  rcases δnext_larger s t δ with larger
  rw [← eq] at larger
  apply Int.cast_lt.mp at larger
  apply Int.add_one_le_of_lt at larger
  have h: ((δ + 1): ℤ) ≤ (d': ℝ) := by
    exact Int.cast_le.mpr larger
  rw [Int.cast_add] at h
  simp at h
  exact h

/-
We can now define integer versions of δₖ
-/
noncomputable
def δₖ_int (s t: ℕ+): ℕ → ℤ
| 0 => 0
| Nat.succ k => Classical.choose (δnext_int s t (δₖ_int s t k))

lemma δₖ_int_agree (s t: ℕ+) (k: ℕ): δₖ_int s t k = δₖ s t k := by
  induction k with
  | zero =>
    unfold δₖ_int
    unfold δₖ
    simp
  | succ k prev =>
    unfold δₖ_int
    unfold δₖ
    rw [← prev]
    exact Classical.choose_spec (δnext_int s t (δₖ_int s t k))


/-
... and integer versions for Jline and Jceiled
-/
noncomputable
def Jline_int (s t: ℕ+) (δ: ℤ) := Jline s t δ

lemma Jline_int_rec (s t: ℕ+) (δ: ℤ) (d0: δ ≠ 0):
Jline_int s t δ = Jline_int s t (δ - s) + Jline_int s t (δ - t) := by
  unfold Jline_int
  push_cast
  apply Jline_rec
  exact Int.cast_ne_zero.mpr d0

noncomputable
def Jceiled_int (s t: ℕ+) (δ: ℤ) := Jceiled s t δ

lemma Jceiled_int_accum (s t: ℕ+) (δ: ℤ):
Jceiled_int s t δ + Jline_int s t (δ + 1) = Jceiled_int s t (δ + 1) := by
  unfold Jceiled_int
  unfold Jline_int
  rcases eq_or_lt_of_le (δnext_int_larger s t δ) with eq|lt
  · have eq': ((δ + 1): ℤ) = δnext s t δ := by
      rw [← eq]
      push_cast
      simp
    rw [eq']
    apply Jceiled_accum
  · have ceiled_nogrow: Jceiled s t δ = Jceiled s t (δ + 1) := by
      apply Jceiled_gap
      · simp
      · exact lt
    have line_empty: (Λline s t (δ + 1)).toFinset = ∅ := by
      simp
      unfold Λline
      refine Set.preimage_eq_empty ?_
      apply Set.disjoint_of_subset
      · show {(δ:ℝ) + 1} ⊆ {(δ:ℝ) + 1}
        simp
      · show Set.range (δₚ s t) ⊆ Δ s t
        refine Set.range_subset_iff.mpr ?_
        intro ⟨p, q⟩
        unfold δₚ; unfold Δ; unfold is_δ
        simp
      · simp
        contrapose lt with isOnΛ
        simp; simp at isOnΛ
        unfold δnext
        apply le_of_not_gt
        apply Set.IsWF.not_lt_min
        unfold Δfloored
        constructor
        · exact isOnΛ
        · simp
    have line_empty': Jline s t (δ + 1) = 0 := by
      unfold Jline
      rw [line_empty]
      apply Finset.sum_empty
    rw [ceiled_nogrow]
    simp
    exact line_empty'

/-
And the integer version of dE
-/
noncomputable
def dE_int (s t: ℕ+): ℝ → ℤ := fun n ↦
  match kₙ s t n with
  | some k => δₖ_int s t k
  | none => 0

lemma dE_int_agree (s t: ℕ+) (n: ℝ): dE_int s t n = dE s t n := by
  unfold dE_int dE
  by_cases n1: n ≥ 1
  · rcases kₙ_exist s t n n1 with ⟨k, keq⟩
    rw [keq]
    simp
    exact δₖ_int_agree s t k
  · simp at n1
    rcases kₙ_not_exist s t n n1 with keq
    rw [keq]
    simp


/-
Let's introduce a new sequence Φ(δ) that's simply Jceiled_int shifted by 1.

We will soon see that this is the sequence that uniquely satisfies the following conditions:
 - Φ(< 0) = 1
 - Φ(δ ≥ 0) = Φ(δ - s) + Φ(δ - t)
As an example, for s = 1 and t = 2, this is the Fibonacci sequence (shifted in index)
-/
noncomputable
def Φ (s t: ℕ+) (δ: ℤ) := 1 + Jceiled_int s t δ

lemma Φ_agree (s t: ℕ+) (δ: ℤ): Φ s t δ = φ s t δ := by
  unfold Φ
  unfold Jceiled_int
  unfold φ
  rfl

theorem Φ_neg (s t: ℕ+) (δ: ℤ) (dpos: δ < 0): Φ s t δ = 1 := by
  unfold Φ
  simp
  unfold Jceiled_int
  unfold Jceiled
  have line_empty: (Λceiled s t δ).toFinset = ∅ := by
    simp
    unfold Λceiled
    simp
    apply Set.eq_empty_iff_forall_not_mem.mpr
    rintro ⟨p, q⟩
    simp
    apply lt_of_lt_of_le
    · show (δ:ℝ) < 0
      exact Int.cast_lt_zero.mpr dpos
    · apply Left.add_nonneg
      · apply mul_nonneg
        · apply Nat.cast_nonneg'
        · apply Nat.cast_nonneg'
      · apply mul_nonneg
        · apply Nat.cast_nonneg'
        · apply Nat.cast_nonneg'
  rw [line_empty]
  apply Finset.sum_empty

theorem Φ_rec (s t: ℕ+) (δ: ℤ) (dpos: δ ≥ 0):
Φ s t δ = Φ s t (δ - s) + Φ s t (δ - t) := by
  have alt: 0 ≤ δ → Φ s t δ = Φ s t (δ - s) + Φ s t (δ - t) := by
    apply Int.le_induction
    · simp
      have sneg: -(s:ℤ) < 0 := by simp
      have tneg: -(t:ℤ) < 0 := by simp
      rw [Φ_neg s t (-(s:ℤ)) sneg]
      rw [Φ_neg s t (-(t:ℤ)) tneg]
      unfold Φ
      have zero: 0 = (-1) + 1 := by simp
      rw [zero]
      rw [← (Jceiled_int_accum s t (-1))]
      unfold Jline_int
      simp
      rw [Jline₀]
      nth_rw 2 [add_comm]
      rw [← Φ]
      rw [Φ_neg]
      simp
    · unfold Φ
      intro δ dpos prev
      rw [add_sub_right_comm]
      rw [add_sub_right_comm]
      rw [← Jceiled_int_accum]
      rw [← Jceiled_int_accum]
      rw [← Jceiled_int_accum]
      rw [Jline_int_rec]
      · rw [← add_assoc]
        rw [prev]
        ring_nf
      · apply ne_of_gt
        exact Int.lt_add_one_iff.mpr dpos
  exact alt dpos

/-
Φ is the discrete analog of the continuous function φ
-/
def ΔceiledByΦ (s t: ℕ+) (n: ℝ) := {δ: ℤ | Φ s t δ ≤ n}

lemma ΔceiledByΦ_agree (s t: ℕ+) (n: ℝ):
Int.cast '' (ΔceiledByΦ s t n) = δceiledByφ s t n ∩ (Int.cast '' Set.univ) := by
  ext δ
  unfold ΔceiledByΦ δceiledByφ
  simp
  constructor
  · rintro ⟨d, ⟨h1, h2⟩⟩
    constructor
    · rw [Φ_agree] at h1
      rw [h2] at h1
      exact h1
    · use d
  · rintro ⟨h1, ⟨d, h2⟩⟩
    use d
    constructor
    · rw [Φ_agree]
      rw [h2]
      exact h1
    · exact h2

lemma dE_int_range_agree (s t: ℕ+) (n: ℝ):
Int.cast '' Set.Iic (dE_int s t n - 1) = Set.Iio (dE s t n) ∩ (Int.cast '' Set.univ) := by
  ext m
  simp
  constructor
  · rintro ⟨x, ⟨h1, h2⟩⟩
    constructor
    · rw [← dE_int_agree]
      rw [← h2]
      simp
      exact Int.lt_of_le_sub_one h1
    · use x
  · rintro ⟨h1, ⟨x, h2⟩⟩
    use x
    constructor
    · rw [← dE_int_agree] at h1
      rw [← h2] at h1
      simp at h1
      exact Int.le_sub_one_of_lt h1
    · exact h2

/-
And finally, we show that Φ is the inverse function of dE in some sense
-/
theorem Φ_inv (s t: ℕ+) (n: ℝ) (n1: n ≥ 1):
ΔceiledByΦ s t n = Set.Iic (dE_int s t n - 1) := by
  have lifted: ((Int.cast '' (ΔceiledByΦ s t n)): Set ℝ) = Int.cast '' Set.Iic (dE_int s t n - 1) := by
    rw [ΔceiledByΦ_agree]
    rw [dE_int_range_agree]
    congr
    exact φ_inv s t n n1
  exact (Set.image_eq_image Int.cast_injective).mp lifted

/-
We will investigate the generator function Z{Φ}(x) = ∑i:ℕ, Φ(i) * x^i and
and show that it converges to a nice function.

We start with a few lemma that will help us to reason about the summation
-/

/-
Λexchange: the bijection between (i, (p, q) ∈ (Λceiled i)) ↔ ((p, q), (i - δₚ(p ,q)))
-/
lemma ΛexchangeMem (s t: ℕ+) (pq :(ℕ × ℕ)) (i: ℕ):
pq ∈ (Λceiled s t (i + pq.1 * s + pq.2 * t: ℕ)).toFinset := by
  unfold Λceiled
  simp

def Λexchange (s t: ℕ+): ((ℕ × ℕ) × ℕ) ≃ ((i: ℕ) × (Λceiled s t i).toFinset) where
  toFun | ⟨pq, i⟩ => ⟨i + pq.1 * s + pq.2 * t, ⟨pq, ΛexchangeMem s t pq i⟩⟩
  invFun | ⟨i, ⟨pq, le⟩ ⟩ => ⟨pq, i - (pq.1 * s + pq.2 * t)⟩
  left_inv := by
    unfold Function.LeftInverse
    simp
    intro p q i
    zify
    simp
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    simp
    rintro ⟨i, ⟨pq, le⟩⟩
    simp
    unfold Λceiled at le
    simp at le
    constructor
    · rw [add_assoc]
      refine Nat.sub_add_cancel ?_
      rify
      exact le
    · refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
      rintro ⟨p, q⟩
      unfold Λceiled
      simp
      have cast: ((i - (pq.1 * ↑s + pq.2 * ↑t)): ℕ) = ((i:ℝ) - (pq.1 * ↑s + pq.2 * ↑t:ℕ)) := by
        refine Nat.cast_sub ?_
        rify
        exact le
      rw [cast]
      push_cast
      rw [add_assoc]
      rw [sub_add_cancel]

/-
Λdecomp: the bijection to domcompose ℕ × ℕ lattice to slices of 45°
-/
lemma ΛdecompMem (p q: ℕ): p ∈ Finset.range (p + q + 1) := by
  simp
  linarith

def Λdecomp: ((j:ℕ) × Finset.range (j + 1)) ≃ (ℕ × ℕ) where
  toFun | ⟨j, n⟩ => (n, j - n)
  invFun | ⟨p, q⟩ => ⟨p + q, ⟨p, ΛdecompMem p q⟩⟩
  left_inv := by
    unfold Function.LeftInverse
    simp
    rintro ⟨j, ⟨n, nmem⟩⟩
    simp at nmem
    simp
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
    simp

/-
A gross bound for Jₚ to dompose it to a product of f(p) and g(q)
-/
lemma Jₚ_bound: ∀p, ∀q, Jₚ (p, q) ≤ 2^p * 2^q := by
  intro p
  induction p with
  | zero =>
    intro q
    unfold Jₚ
    simp
    exact Nat.one_le_two_pow
  | succ p prev =>
    intro q
    induction q with
    | zero =>
      unfold Jₚ
      simp
      exact Nat.one_le_two_pow
    | succ q prev' =>
      rw [Jₚ_rec]
      have right: 2 ^ (p + 1) * 2 ^ (q + 1) = 2 ^ (p + 1) * 2 ^ q + 2 ^ p * 2 ^ (q + 1) := by
        ring
      rw [right]
      exact add_le_add prev' (prev (q + 1))

/-
An analog to geometric series over ℕ × ℕ
The radius bound here is not sharp
-/
lemma pqx_sum [RCLike K]
(s t: ℕ+) (x: K) (bound: ‖x‖ < 2⁻¹):
HasSum (fun pq ↦ ↑(Jₚ pq) * x ^ (pq.1 * (s:ℕ) + pq.2 * (t:ℕ))) (1 - (x ^ (s:ℕ) + x ^ (t:ℕ)))⁻¹ := by
  apply (Equiv.hasSum_iff Λdecomp).mp
  unfold Λdecomp Function.comp
  simp

  let term := fun (⟨j, c⟩:(j:ℕ) × Finset.range (j + 1)) ↦ ((Jₚ (c, j - c)) * x ^ (c * s + (j - c) * t: ℕ ))
  have binom: ∀(j:ℕ), HasSum (fun (c:Finset.range (j + 1)) ↦ term ⟨j, c⟩ ) ((x ^ (s:ℕ) + x ^ (t:ℕ))^j) := by
    intro j
    rw [add_pow]
    let f(c: ℕ) := (x ^ (s:ℕ)) ^ c * (x ^ (t:ℕ)) ^ (j - c) * (j.choose c)
    have left: (fun c ↦ term ⟨j, c⟩) = (fun (c:Finset.range (j + 1)) ↦ f c) ∘ (↑) := by
      unfold term f Jₚ
      ext c
      rcases c with ⟨c, mem⟩
      simp at mem
      simp
      rw [← pow_mul, ← pow_mul]
      rw [← pow_add]
      nth_rw 4 [mul_comm]
      congr 2
      · congr
        rw [← Nat.add_sub_assoc]
        · simp
        · exact Nat.le_of_lt_succ mem
      · ring
    have left': ∀ c, (fun c ↦ term ⟨j, c⟩) c = ((fun (c:Finset.range (j + 1)) ↦ f c) ∘ (↑)) c := by
      intro c
      rw [left]
    apply HasSum.congr_fun ?_ left'
    apply Finset.hasSum

  apply HasSum.sigma_of_hasSum ?_ binom
  · apply (Equiv.summable_iff Λdecomp.symm).mp
    unfold term Λdecomp Function.comp
    simp
    show Summable fun (pq: ℕ × ℕ) ↦ Jₚ pq * x ^ (pq.1 * (s:ℕ) + pq.2 * (t:ℕ))
    let termBound := fun (pq: ℕ × ℕ) ↦ ‖(2 * x ^ (s:ℕ)) ^ pq.1 * (2 * x ^ (t:ℕ)) ^ pq.2‖
    have raise(pq: ℕ × ℕ): ‖Jₚ pq * x ^ (pq.1 * s + pq.2 * t)‖ ≤ termBound pq := by
      unfold termBound
      rw [mul_pow, mul_pow]
      rw [mul_mul_mul_comm]
      rw [← pow_mul, ← pow_mul]
      rw [mul_comm (s:ℕ), mul_comm (t:ℕ)]
      rw [← pow_add x]
      rw [norm_mul, norm_mul]
      apply mul_le_mul
      · have left: ‖(Jₚ pq: K)‖ = Jₚ pq := by
          simp
        have right: ‖(2: K) ^ pq.1 * (2: K) ^ pq.2‖ = (2 ^ pq.1 * 2 ^ pq.2: ℕ) := by
          simp
        rw [left, right]
        apply Nat.cast_le.mpr
        apply Jₚ_bound
      · simp
      · apply norm_nonneg
      · apply norm_nonneg
    apply Summable.of_norm_bounded termBound ?_ raise
    · show Summable termBound
      apply Summable.mul_norm
      repeat
        simp
        apply (lt_inv_mul_iff₀ ?_).mp
        · simp
          apply lt_of_le_of_lt ?_ bound
          apply pow_le_of_le_one
          · simp
          · apply le_of_lt; apply lt_trans bound; norm_num
          · simp
        · simp
  · apply hasSum_geometric_of_norm_lt_one
    apply lt_of_le_of_lt (norm_add_le _ _)
    have half: (1:ℝ) = 2⁻¹ + 2⁻¹ := by norm_num
    rw [half]
    apply add_lt_add
    repeat
      simp
      apply lt_of_le_of_lt ?_ bound
      apply pow_le_of_le_one
      · simp
      · apply le_of_lt; apply lt_trans bound; norm_num
      · simp

noncomputable
def ξPolynomial(s t: ℕ+) :=
  Polynomial.monomial s (1:ℂ) + Polynomial.monomial t (1:ℂ) - Polynomial.C 1

lemma ξPolynomialDerivative(s t: ℕ+):
(ξPolynomial s t).derivative = Polynomial.monomial (s - 1) (s:ℂ) + Polynomial.monomial (t - 1) (t:ℂ) := by
  unfold ξPolynomial
  simp
  rw [Polynomial.derivative_monomial, Polynomial.derivative_monomial]
  simp


lemma ξPolynomialFactorizeMulti(s t: ℕ+):
ξPolynomial s t = Polynomial.C (ξPolynomial s t).leadingCoeff * ((ξPolynomial s t).roots.map (Polynomial.X - Polynomial.C ·)).prod := by
  exact Polynomial.eq_prod_roots_of_splits_id (Complex.isAlgClosed.splits (ξPolynomial s t))

noncomputable
def ξSet(s t: ℕ+) := (ξPolynomial s t).roots.toFinset

lemma ξNonMult(s t: ℕ+) (r: ℂ) (rmem: r ∈ ξSet s t):
s * r ^ (s - 1: ℕ) + t * r ^ (↑t - 1: ℕ) ≠ 0 := by
  obtain rmem' := Multiset.mem_dedup.mp rmem
  obtain req_of_pol := Polynomial.isRoot_of_mem_roots rmem'
  unfold ξPolynomial at req_of_pol
  simp at req_of_pol
  obtain req_of_pol' := eq_of_sub_eq_zero req_of_pol
  by_contra req_of_der
  have req_of_der': (s * r ^ (s - 1:ℕ) + t * r ^ (t - 1:ℕ)) * r = 0 := by
    apply mul_eq_zero.mpr; left; exact req_of_der
  rw [add_mul] at req_of_der'
  rw [mul_assoc, mul_assoc] at req_of_der'
  rw [← pow_succ, ← pow_succ] at req_of_der'
  have s1: (1:ℕ) ≤ s := by exact NeZero.one_le
  have t1: (1:ℕ) ≤ t := by exact NeZero.one_le
  have rs: r ^ (s:ℕ) = 1 - r ^ (t:ℕ) := eq_sub_of_add_eq req_of_pol'
  have rt: r ^ (t:ℕ) = 1 - r ^ (s:ℕ) := eq_sub_of_add_eq' req_of_pol'
  rw [Nat.sub_add_cancel s1, Nat.sub_add_cancel t1] at req_of_der'
  have req_of_der'' := req_of_der'
  rw [rs] at req_of_der'
  rw [rt] at req_of_der''
  have rs': s = (s - t) * r ^ (t:ℕ) := by
    apply eq_of_sub_eq_zero
    rw [sub_mul]
    rw [← sub_add]
    nth_rw 1 [← mul_one (s:ℂ)]
    rw [← mul_sub]
    exact req_of_der'
  have rt': t = (t - s) * r ^ (s:ℕ) := by
    apply eq_of_sub_eq_zero
    rw [sub_mul]
    rw [← sub_add]
    nth_rw 1 [← mul_one (t:ℂ)]
    rw [← mul_sub]
    rw [add_comm]
    exact req_of_der''
  by_cases seqt: (s:ℂ) = t
  · rw [seqt] at rs'
    simp at rs'
  · have snet: (s - t: ℂ) ≠ 0 := sub_ne_zero_of_ne seqt
    have tnes: (t - s: ℂ) ≠ 0 := by
      refine sub_ne_zero_of_ne ?_
      symm
      exact seqt
    rw [mul_comm] at rs'
    rw [mul_comm] at rt'
    obtain rs'' := (div_eq_iff snet).mpr rs'
    obtain rt'' := (div_eq_iff tnes).mpr rt'
    have sside: (s / (s - t)) ^(s:ℕ) = r ^(s * t: ℕ) := by
      rw [mul_comm]
      rw [pow_mul]
      rw [rs'']
    have tside: (t / (t - s)) ^(t:ℕ) = r ^(s * t: ℕ) := by
      rw [pow_mul]
      rw [rt'']
    obtain what: ((s:ℂ) / (s - t)) ^(s:ℕ) = (t / (t - s)) ^(t:ℕ) := by
      rw [sside, tside]
    rw [div_pow, div_pow] at what
    obtain ts0: (s - t: ℂ) ^ (s: ℕ) ≠ 0 := pow_ne_zero _ snet
    obtain st0: (t - s: ℂ) ^ (t: ℕ) ≠ 0 := pow_ne_zero _ tnes
    obtain what := mul_eq_mul_of_div_eq_div _ _ ts0 st0 what
    have whathalf(S T: ℕ) (Spos: 0 < S) (Tpos: 0 < T) (h: S < T)(what: (S ^ S * (T - S) ^ T: ℂ) = T ^ T * (S - T) ^ S): False := by
      norm_cast at what
      obtain what := abs_eq_abs.mpr (Or.inl what)
      rw [abs_mul, abs_mul] at what
      simp at what
      have tsubs: |Int.subNatNat T S| = (T - S:ℕ) := by
        rw [Int.subNatNat_of_le (le_of_lt h)]
        exact Int.abs_natCast (T - S)
      have ssubt: |Int.subNatNat S T| = (T - S:ℕ) := by
        rw [Int.subNatNat_eq_coe]
        push_cast [h]
        nth_rw 2 [← neg_sub]
        refine abs_of_neg ?_
        refine Int.sub_neg_of_lt ?_
        norm_cast
      rw [tsubs, ssubt] at what
      set D:ℕ := T - S
      have D0: D ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr h
      have Teq: T = D + S := by
        unfold D
        refine Eq.symm (Nat.sub_add_cancel ?_)
        exact Nat.le_of_succ_le h
      rw [Teq] at what
      rw [npow_add, npow_add] at what
      rw [← mul_assoc] at what
      rw [mul_eq_mul_right_iff] at what
      rw [mul_comm] at what
      have ds0: ¬ (D:ℤ)^S = 0 := by
        simp
        exact fun a ↦ False.elim (D0 a)
      rw [or_iff_left ds0] at what
      have conflict:  (D:ℤ) ^ D * S ^ S ≠ (D + S) ^ D * (D + S) ^ S := by
        apply ne_of_lt
        gcongr
        · show (D:ℤ) < D + S
          apply (lt_add_iff_pos_right (D:ℤ)).mpr
          exact Int.ofNat_pos.mpr Spos
        · show (S:ℤ) < D + S
          apply (lt_add_iff_pos_left (S:ℤ)).mpr
          refine Int.ofNat_pos.mpr ?_
          exact Nat.zero_lt_sub_of_lt h
      contradiction
    have snet': (s:ℕ) ≠ t := by
      norm_cast at seqt
      norm_cast
    rcases ne_iff_lt_or_gt.mp snet' with lt|gt
    · exact whathalf s t s1 t1 lt what
    · exact whathalf t s t1 s1 gt what.symm

lemma ξPolynomialFactorize(s t: ℕ+):
ξPolynomial s t = Polynomial.C (ξPolynomial s t).leadingCoeff * Lagrange.nodal (ξSet s t) id := by
  unfold Lagrange.nodal
  nth_rw 1 [ξPolynomialFactorizeMulti]
  apply mul_eq_mul_left_iff.mpr
  left
  unfold ξSet
  simp
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_congr rfl
  intro r rmem
  obtain rmem' := Multiset.mem_dedup.mp rmem
  have root1: Multiset.count r (ξPolynomial s t).roots = 1 := by
    apply le_antisymm
    · unfold Polynomial.roots
      have n0: ξPolynomial s t ≠ 0 := by
        exact Polynomial.ne_zero_of_mem_roots rmem'
      simp [n0]
      obtain ⟨_,multiEq⟩ := Exists.choose_spec (Polynomial.exists_multiset_roots n0)
      rw [multiEq r]
      by_contra ge2
      simp at ge2
      apply Nat.succ_le_iff.mpr at ge2
      apply (Polynomial.le_rootMultiplicity_iff n0).mp at ge2
      simp at ge2
      obtain ⟨factor, feq⟩ := dvd_iff_exists_eq_mul_left.mp ge2
      obtain der := ξPolynomialDerivative s t
      rw [feq] at der
      simp at der
      rw [Polynomial.derivative_pow] at der
      have square: (Polynomial.X - Polynomial.C r) ^ 2 = (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C r) := by
        ring
      rw [square] at der
      simp at der
      rw [← mul_assoc, ← mul_assoc, ← add_mul] at der
      have dvd: Polynomial.X - Polynomial.C r ∣ Polynomial.monomial (s - 1) (s:ℂ) + Polynomial.monomial (t - 1) (t:ℂ) := by
        exact
          Dvd.intro_left
            (Polynomial.derivative factor * (Polynomial.X - Polynomial.C r) +
              factor * Polynomial.C 2)
            der
      obtain req_of_der := Polynomial.eval_dvd dvd (x := r)
      simp at req_of_der
      obtain req_of_pol := Polynomial.isRoot_of_mem_roots rmem'
      unfold ξPolynomial at req_of_pol
      simp at req_of_pol
      obtain noneq := ξNonMult s t r rmem
      contradiction
    · exact Multiset.one_le_count_iff_mem.mpr rmem'
  rw [root1]
  simp

/-
A main theorem: the generating function Z{Φ}(x) converges to a rational function
The bound here is not sharp, but it should be sufficient for future reasoning over complex plane
-/
theorem ZΦ_sum (s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
HasSum (fun i:ℕ ↦ x ^ i * Φ s t i) ((((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹):= by
  unfold ξPolynomial
  simp
  rw [← neg_sub 1 _]
  rw [← neg_inv]
  rw [sub_neg_eq_add]
  rw [add_mul]
  rw [one_mul]
  have bound2: ‖x‖ < 1 := by
    apply lt_trans bound
    norm_num

  unfold Φ Jceiled_int Jceiled
  push_cast

  have h: (fun i:ℕ ↦ x ^ i * (1 + ∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p)))
   = fun i:ℕ ↦ (x ^ i + (∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p)) * x ^ i) := by
     ext i
     rw [mul_comm]
     rw [add_mul]
     simp
  rw [h]
  apply HasSum.add
  · apply hasSum_geometric_of_norm_lt_one
    · exact bound2
  · have h: (fun i:ℕ ↦ (∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p)) * x ^ i)
          = fun i:ℕ ↦ (∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p) * x ^ i) := by
      ext i
      apply Finset.sum_mul
    rw [h]

    have totalSum: HasSum (fun (⟨i, p⟩ : (i: ℕ) × (Λceiled s t i).toFinset) ↦ (Jₚ p) * x ^ i) ((1 - (x ^ (s:ℕ) + x ^ (t:ℕ)))⁻¹ * (1 - x)⁻¹) := by
      apply (Equiv.hasSum_iff (Λexchange s t)).mp
      unfold Λexchange
      unfold Function.comp
      simp
      let f (pq: ℕ × ℕ) := (Jₚ pq) * x ^ (pq.1 * s + pq.2 * t)
      let g (i: ℕ) := x ^ i
      have eqInside: (fun pqi: ((ℕ × ℕ) × ℕ) ↦ ↑(Jₚ pqi.1) * x ^ (pqi.2 + pqi.1.1 * s + pqi.1.2 * t))
       = (fun pqi: ((ℕ × ℕ) × ℕ) ↦  (f pqi.1) * (g pqi.2)) := by
        ext pqi
        rw [mul_assoc]
        rw [← pow_add]
        congr 2
        ring
      rw [eqInside]
      apply HasSum.mul
      · unfold f
        apply pqx_sum _ _ _ bound
      · unfold g
        apply hasSum_geometric_of_norm_lt_one
        exact bound2
      · apply summable_mul_of_summable_norm
        · unfold f
          simp
          unfold Summable
          use (1 - (‖x‖ ^ (s: ℕ) + ‖x‖ ^ (t: ℕ)))⁻¹
          apply pqx_sum s t ‖x‖
          simp
          exact bound
        · unfold g
          simp
          exact bound2

    apply HasSum.sigma totalSum
    intro i
    simp
    apply Finset.hasSum

lemma PartialFractionDecompostion [Field F] [DecidableEq F]
(x: F) (roots: Finset F) (hasroots: roots.Nonempty) (notroot: x ∉ roots):
((Lagrange.nodal roots id).eval x)⁻¹ = ∑ r ∈ roots, (x - r)⁻¹ * ((Polynomial.derivative (Lagrange.nodal roots id)).eval r)⁻¹ := by
  apply DivisionMonoid.inv_eq_of_mul
  rw [Finset.mul_sum]
  have h0 (r: F) (h: r ∈ roots): (Polynomial.derivative (Lagrange.nodal roots id)).eval r
    = Polynomial.eval r (∏ r' ∈ roots.erase r, (Polynomial.X - Polynomial.C r')) := by
    rw [Lagrange.derivative_nodal]
    rw [Polynomial.eval_finset_sum]
    unfold Lagrange.nodal
    simp
    apply Finset.sum_eq_single r
    · intro r' r'mem r'ne
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero_iff.mpr
      use r
      constructor
      · exact Finset.mem_erase_of_ne_of_mem (id (Ne.symm r'ne)) h
      · simp
    · exact fun a ↦ False.elim (a h)

  have h1 :
     ∑ r ∈ roots, ((Lagrange.nodal roots id).eval x) * ((x - r)⁻¹ * ((Polynomial.derivative (Lagrange.nodal roots id)).eval r)⁻¹)
   = ∑ r ∈ roots, (Lagrange.basis roots id r).eval x := by
    apply Finset.sum_congr rfl
    intro r rmem
    rw [h0 r rmem]
    unfold Lagrange.nodal
    rw [Polynomial.eval_prod]
    simp
    have notroot': x - r ≠ 0 := by
      refine sub_ne_zero_of_ne ?_
      exact Ne.symm (ne_of_mem_of_not_mem rmem notroot)
    rw [← mul_assoc]
    rw [← Finset.mul_prod_erase roots _ rmem]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]
    rw [inv_mul_cancel₀ notroot']
    rw [one_mul]
    unfold Lagrange.basis
    rw [Polynomial.eval_prod]
    rw [Polynomial.eval_prod]
    unfold Lagrange.basisDivisor
    rw [← Finset.prod_inv_distrib]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r' r'mem
    simp
    rw [mul_comm]
  rw [h1]
  rw [← Polynomial.eval_finset_sum]
  rw [Lagrange.sum_basis (Set.injOn_id _) hasroots]
  simp

lemma PartialFractionDecompostion2 [Field F] [DecidableEq F]
(x: F) (roots: Finset F) (coef: F)
(hasroots: roots.Nonempty) (notroot: x ∉ roots) (not1: x ≠ 1) (onenotroot: 1 ∉ roots):
(((Polynomial.C coef * Lagrange.nodal roots id).eval 1)⁻¹ - ((Polynomial.C coef * Lagrange.nodal roots id).eval x)⁻¹) * (1 - x)⁻¹
 = ∑ r ∈ roots, (x - r)⁻¹ * (r - 1)⁻¹ * ((Polynomial.derivative (Polynomial.C coef * Lagrange.nodal roots id)).eval r)⁻¹ := by
  rw [Polynomial.derivative_C_mul]
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  simp
  rw [← sub_mul]
  nth_rw 2 [mul_comm]
  rw [mul_assoc]

  rw [PartialFractionDecompostion x roots hasroots notroot]
  rw [PartialFractionDecompostion 1 roots hasroots onenotroot]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r rmem
  rw [← sub_mul]
  rw [mul_right_comm]
  rw [mul_comm]
  rw [mul_assoc]
  apply mul_eq_mul_right_iff.mpr
  left
  have x1: 1 - x ≠ 0 := sub_ne_zero_of_ne (id (Ne.symm not1))
  have xr: x - r ≠ 0 := sub_ne_zero_of_ne (Ne.symm (ne_of_mem_of_not_mem rmem notroot))
  have r1: r - 1 ≠ 0 := sub_ne_zero_of_ne (ne_of_mem_of_not_mem rmem onenotroot)
  apply (mul_inv_eq_iff_eq_mul₀ x1).mpr
  rw [mul_assoc]
  apply (eq_inv_mul_iff_mul_eq₀ xr).mpr
  apply (eq_inv_mul_iff_mul_eq₀ r1).mpr
  rw [mul_sub]
  rw [Field.mul_inv_cancel _ xr]
  rw [← neg_sub r 1]
  rw [← neg_inv]
  rw [mul_neg]
  rw [mul_sub]
  rw [mul_neg]
  rw [mul_comm (x - r)]
  rw [← mul_assoc]
  rw [Field.mul_inv_cancel _ r1]
  simp


lemma ΦX_sum_eq(s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
(((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹ =
∑ ξ ∈ ξSet s t, (x - ξ)⁻¹ * (ξ - 1)⁻¹*(s * ξ^(s - 1:ℕ) + t * ξ^(t - 1:ℕ))⁻¹ := by
  rw [ξPolynomialFactorize]
  have nonempty: (ξSet s t).Nonempty := by
    by_contra empty
    simp at empty
    obtain factorize := ξPolynomialFactorize s t
    rw [empty] at factorize
    simp at factorize
    obtain eval: (ξPolynomial s t).eval 0 = (ξPolynomial s t).eval 1 := by
      rw [factorize]
      simp
    unfold ξPolynomial at eval
    simp at eval
    norm_num at eval
  have xnotroot: x ∉ ξSet s t := by
    unfold ξSet
    simp
    rw [imp_iff_not_or]
    right
    unfold ξPolynomial
    simp
    apply sub_ne_zero.mpr
    have h: ‖x ^ (s:ℕ) + x ^ (t:ℕ)‖ ≠ ‖(1:ℂ)‖ := by
      apply ne_of_lt
      apply lt_of_le_of_lt (norm_add_le _ _)
      have right: ‖(1:ℂ)‖ = 2⁻¹ + 2⁻¹ := by norm_num
      rw [right]
      gcongr
      repeat
      · simp
        refine lt_of_le_of_lt ?_ bound
        refine pow_le_of_le_one ?_ ?_ ?_
        · simp
        · apply le_trans (le_of_lt bound)
          norm_num
        · simp
    exact fun a ↦ h (congrArg norm a)
  have xnotone: x ≠ 1 := by
    contrapose bound with one
    simp at one
    rw [one]
    norm_num
  have onenotroot: 1 ∉ ξSet s t := by
    by_contra isroot
    unfold ξSet at isroot
    simp at isroot
    rcases isroot with ⟨_, eval⟩
    unfold ξPolynomial at eval
    simp at eval
  rw [PartialFractionDecompostion2 _ _ _ nonempty xnotroot xnotone onenotroot]
  rw [← ξPolynomialFactorize]
  rw [ξPolynomialDerivative]
  simp


lemma ZΦ_sum2 (s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
HasSum (fun i:ℕ ↦ x ^ i * (∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ ))
((((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹):= by
  rw [ΦX_sum_eq s t x bound]
  have rw_fun: (fun i:ℕ ↦ x ^ i *(∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ ) )
   = fun i:ℕ ↦ (∑ξ ∈ ξSet s t, (x * ξ⁻¹)^i * (1 - ξ)⁻¹ * ξ⁻¹*(s * ξ^(s - 1:ℕ) + t * ξ^(t - 1:ℕ))⁻¹ ) := by
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext ξ
    rw [← mul_assoc, ← mul_assoc]
    rw [← mul_pow]
    rw [mul_assoc _ ξ⁻¹]
    congr
    rw [← mul_inv]
    rw [mul_add]
    congr 2
    repeat
      rw [mul_comm ξ]
      rw [mul_assoc]
      nth_rw 3 [← pow_one ξ]
      rw [← pow_add]
      congr
      exact Eq.symm (PNat.natPred_add_one _)

  rw [rw_fun]
  apply hasSum_sum
  intro ξ mem
  unfold ξSet ξPolynomial at mem
  simp at mem
  obtain ⟨_, polyeq⟩ := mem
  have ξ0: ξ ≠ 0 := by
    by_contra zero
    rw [zero] at polyeq
    simp at polyeq
  apply HasSum.mul_right
  have rw_sum: (x - ξ)⁻¹ * (ξ - 1)⁻¹ = (1 - x * ξ⁻¹)⁻¹ * (1 - ξ)⁻¹ * ξ⁻¹ := by
    rw [← neg_sub ξ , ← neg_inv]
    rw [← neg_sub 1 , ← neg_inv]
    rw [neg_mul_neg]
    rw [mul_right_comm]
    rw [← mul_inv _ ξ]
    congr
    rw [sub_mul]
    rw [mul_assoc]
    rw [inv_mul_cancel₀ ξ0]
    simp

  rw [rw_sum]
  apply HasSum.mul_right
  apply HasSum.mul_right
  apply hasSum_geometric_of_norm_lt_one
  show ‖x * ξ⁻¹‖ < 1
  rw [norm_mul]
  rw [norm_inv]
  have ξgt0: 0 < ‖ξ‖ := by
    simp
    exact ξ0
  apply (mul_inv_lt_iff₀ ξgt0).mpr
  simp
  apply lt_of_lt_of_le bound
  contrapose polyeq
  simp at polyeq
  apply sub_ne_zero_of_ne
  have nomr_ne: ‖ξ ^ (s:ℕ) + ξ ^ (t:ℕ)‖ ≠ ‖(1:ℂ)‖ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (norm_add_le _ _)
    have right: ‖(1:ℂ)‖ = 2⁻¹ + 2⁻¹ := by norm_num
    rw [right]
    gcongr
    repeat
    · simp
      refine lt_of_le_of_lt ?_ polyeq
      refine pow_le_of_le_one ?_ ?_ ?_
      · simp
      · apply le_trans (le_of_lt polyeq)
        norm_num
      · simp
  exact fun a ↦ nomr_ne (congrArg norm a)


theorem ΦFormula (s t: ℕ+) (i: ℕ):
Φ s t i = ∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ := by
  let fmsL: FormalMultilinearSeries ℂ ℂ ℂ :=
    fun i ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin i) (Φ s t i)
  have hasFmsL: HasFPowerSeriesAt (fun x ↦ (((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹) fmsL 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    unfold fmsL FormalMultilinearSeries.coeff
    simp
    unfold Filter.Eventually
    apply mem_nhds_iff.mpr
    use {x:ℂ | ‖x‖ <2⁻¹}
    simp
    constructor
    · apply ZΦ_sum
    · exact isOpen_lt continuous_norm continuous_const
  let fmsR: FormalMultilinearSeries ℂ ℂ ℂ :=
    fun i ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin i) (∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹)
  have hasFmsR: HasFPowerSeriesAt (fun x ↦ (((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹) fmsR 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    unfold fmsR FormalMultilinearSeries.coeff
    simp
    unfold Filter.Eventually
    apply mem_nhds_iff.mpr
    use {x:ℂ | ‖x‖ <2⁻¹}
    simp
    constructor
    · obtain ZΦ_sum2 := ZΦ_sum2
      simp at ZΦ_sum2
      apply ZΦ_sum2
    · exact isOpen_lt continuous_norm continuous_const
  obtain fmsEq := HasFPowerSeriesAt.eq_formalMultilinearSeries hasFmsL hasFmsR
  have coeffL: Φ s t i = fmsL.coeff i := by
    unfold fmsL FormalMultilinearSeries.coeff
    simp
  have coeffR: ∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ = fmsR.coeff i := by
    unfold fmsR FormalMultilinearSeries.coeff
    simp
  rw [coeffL, coeffR]
  rw [fmsEq]


noncomputable
def ξPolynomialℝ(s t: ℕ+) :=
  Polynomial.monomial s (1:ℝ) + Polynomial.monomial t (1:ℝ) - Polynomial.C 1

lemma PowMono (a: ℕ+): StrictMonoOn (fun (x:ℝ) ↦ x ^ (a: ℕ)) (Set.Ici 0) := by
  have rwfun: (fun (x:ℝ) ↦ x ^ (a: ℕ)) = fun (x:ℝ) ↦ x ^ (a: ℝ) := by
    ext
    symm
    apply Real.rpow_natCast
  rw [rwfun]
  refine Real.strictMonoOn_rpow_Ici_of_exponent_pos ?_
  simp

lemma ξPolynomialℝ_mono(s t: ℕ+): StrictMonoOn ((ξPolynomialℝ s t).eval ·) (Set.Ici 0) := by
  unfold ξPolynomialℝ
  simp
  apply StrictMonoOn.add_const
  apply StrictMonoOn.add
  repeat apply PowMono

lemma ξPolynomialℝUniqueRoot(s t: ℕ+):
∃!ξ > 0, (ξPolynomialℝ s t).eval ξ = 0 := by
  apply existsUnique_of_exists_of_unique
  · apply (Set.mem_image _ _ _).mp
    set f := ((ξPolynomialℝ s t).eval ·)
    apply Set.mem_of_mem_of_subset
    · show 0 ∈ Set.Ioo (f 0) (f 1)
      unfold f
      unfold ξPolynomialℝ
      simp
    · apply subset_trans
      · show Set.Ioo (f 0) (f 1) ⊆ f '' Set.Ioo 0 1
        have zeroOne: (0:ℝ) ≤ 1 := by norm_num
        apply intermediate_value_Ioo zeroOne
        unfold f
        apply Polynomial.continuousOn_aeval
      · apply Set.image_mono
        intro x xmem
        rcases xmem with ⟨zero, one⟩
        exact zero
  · rintro x y ⟨xmem, xzero⟩ ⟨ymem, yzero⟩
    refine ((ξPolynomialℝ_mono s t).eq_iff_eq ?_ ?_).mp ?_
    · exact Set.mem_Ici_of_Ioi xmem
    · exact Set.mem_Ici_of_Ioi ymem
    · rw [xzero, yzero]

noncomputable
def ξ₀ (s t: ℕ+) := (ξPolynomialℝUniqueRoot s t).choose

theorem Complex.arg_pow_coe_angle {x : ℂ} {n: ℕ} : ((x ^ n).arg : Real.Angle) = n • (x.arg : Real.Angle) := by
  by_cases x0: x = 0
  · rw [x0]
    by_cases n0: n = 0
    repeat simp [n0]
  · induction n with
    | zero => simp [x0]
    | succ n prev =>
      have xn0: x ^ n ≠ 0 := pow_ne_zero n x0
      rw [pow_succ]
      rw [Complex.arg_mul_coe_angle xn0 x0]
      rw [prev]
      rfl

lemma ξ₀Smallest (s t: ℕ+) (coprime: s.Coprime t):
∀ξ ∈ ξSet s t, ξ ≠ ξ₀ s t → ξ₀ s t < ‖ξ‖ := by
  obtain ⟨⟨ξ₀pos, ξ₀eq⟩, ξ₀unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  unfold ξPolynomialℝ at ξ₀eq
  simp at ξ₀eq
  intro ξ mem' ne
  unfold ξSet ξPolynomial at mem'
  simp at mem'
  rcases mem' with ⟨_, mem'⟩
  obtain mem := eq_of_sub_eq_zero mem'
  obtain memnorm := congrArg norm mem
  have normle: 1 ≤ ‖ξ‖ ^ (s:ℕ) + ‖ξ‖ ^ (t:ℕ)  := by
    rw [← norm_pow, ← norm_pow]
    convert norm_add_le (ξ ^ (s:ℕ)) (ξ ^ (t:ℕ))
    rw [memnorm]
    simp
  let ξPoly' := Polynomial.monomial s (1:ℝ) + Polynomial.monomial t (1:ℝ)
  let ξPoly'F := (ξPoly'.eval ·)
  have normle': ξPoly'F (ξ₀ s t) ≤ ξPoly'F ‖ξ‖  := by
    unfold ξPoly'F ξPoly' ξ₀ ξPolynomialℝ
    simp
    convert normle
    obtain ξ₀eq := eq_of_sub_eq_zero ξ₀eq
    rw [ξ₀eq]
  have mono: StrictMonoOn ξPoly'F (Set.Ici 0) := by
    unfold ξPoly'F ξPoly'
    simp
    apply StrictMonoOn.add
    repeat apply PowMono
  have normleFromMono: ξ₀ s t ≤ ‖ξ‖ := by
    refine (mono.le_iff_le ?_ ?_).mp normle'
    · simp
      apply le_of_lt
      apply gt_iff_lt.mp
      exact ξ₀pos
    · simp
  apply lt_of_le_of_ne normleFromMono
  contrapose ne with eq
  simp;
  unfold ξ₀ ξPolynomialℝ at eq
  simp at eq
  rw [eq] at ξ₀eq
  simp at memnorm
  rw [← memnorm] at ξ₀eq
  rw [← norm_pow, ← norm_pow] at ξ₀eq
  obtain ξ₀eq := eq_of_sub_eq_zero ξ₀eq
  obtain arg_eq := Complex.norm_add_eq_iff.mp ξ₀eq.symm
  have ξnon0: ξ ≠ 0 := by
    by_contra ξ0
    rw [ξ0] at mem
    simp at mem
  have s0: ¬ ξ ^ (s:ℕ) = 0 := by simp; exact ξnon0
  have t0: ¬ ξ ^ (t:ℕ) = 0 := by simp; exact ξnon0
  simp [s0, t0] at arg_eq
  obtain same_ray: SameRay ℝ (ξ ^ (s:ℕ)) (ξ ^ (t:ℕ)) := by
    apply Complex.sameRay_iff.mpr
    right; right; exact arg_eq
  obtain same_ray1: SameRay ℝ (ξ ^ (s:ℕ)) 1 := by
    rw [← mem]
    apply SameRay.add_right
    · rfl
    · exact same_ray
  obtain arg0s := Complex.sameRay_iff.mp same_ray1
  simp [s0] at arg0s
  obtain arg0t := (Complex.sameRay_iff.mp same_ray)
  simp [s0, t0] at arg0t
  rw [arg0s] at arg0t
  obtain angles := congrArg (fun (a:ℝ) ↦ (a:Real.Angle)) arg0s
  obtain anglet := congrArg (fun (a:ℝ) ↦ (a:Real.Angle)) arg0t.symm
  rw [Complex.arg_pow_coe_angle, ← Real.Angle.natCast_mul_eq_nsmul] at angles
  rw [Complex.arg_pow_coe_angle, ← Real.Angle.natCast_mul_eq_nsmul] at anglet
  obtain ⟨ks, kseq⟩ := Real.Angle.coe_eq_zero_iff.mp angles
  obtain ⟨kt, kteq⟩ := Real.Angle.coe_eq_zero_iff.mp anglet
  simp at kseq
  simp at kteq
  rw [mul_comm _ ξ.arg] at kseq
  rw [mul_comm _ ξ.arg] at kteq
  have twopi0 : (2 * Real.pi) ≠ 0 := by exact ne_of_gt (Real.two_pi_pos)
  have s0r: (s:ℝ) ≠ 0 := by exact Ne.symm (NeZero.ne' (s:ℝ))
  have t0r: (t:ℝ) ≠ 0 := by exact Ne.symm (NeZero.ne' (t:ℝ))
  obtain kseq' := (div_eq_div_iff s0r twopi0).mpr kseq
  obtain kteq' := (div_eq_div_iff t0r twopi0).mpr kteq
  have keq: (ks / s: ℝ) = kt / t := by
    rw [kseq', kteq']
  apply (div_eq_div_iff s0r t0r).mp at keq
  norm_cast at keq
  have sdvd: (s:ℤ) ∣ (ks * t) := by
    exact Dvd.intro_left kt (id (Eq.symm keq))
  have dvd: (s:ℤ) ∣ ks := by
    refine IsCoprime.dvd_of_dvd_mul_right ?_ sdvd
    apply Int.isCoprime_iff_nat_coprime.mpr
    simp
    exact coprime
  obtain ⟨factor, feq⟩ := dvd
  rw [feq] at kseq'
  simp at kseq'
  obtain ktwopi: factor * (2 * Real.pi) = ξ.arg := (eq_div_iff twopi0).mp kseq'
  have factor0: factor = 0 := by
    apply le_antisymm
    · by_contra pos
      simp at pos
      have : 2 * Real.pi ≤ ξ.arg := by
        rw [← one_mul (2 * Real.pi)]
        rw [← ktwopi]
        rw [mul_le_mul_right]
        · exact Int.cast_one_le_of_pos pos
        · exact Real.two_pi_pos
      obtain what := le_trans this (Complex.arg_le_pi ξ)
      nth_rw 2 [← one_mul Real.pi] at what
      apply (mul_le_mul_right Real.pi_pos).mp at what
      simp at what
    · by_contra neg
      simp at neg
      have : ξ.arg ≤ -(2 * Real.pi) := by
        rw [neg_eq_neg_one_mul]
        rw [← ktwopi]
        rw [mul_le_mul_right]
        · exact Int.cast_le_neg_one_of_neg neg
        · exact Real.two_pi_pos
      obtain what := lt_of_lt_of_le (Complex.neg_pi_lt_arg ξ) this
      apply neg_lt_neg_iff.mp at what
      nth_rw 2 [← one_mul Real.pi] at what
      apply (mul_lt_mul_right Real.pi_pos).mp at what
      simp at what
  rw [factor0] at ktwopi
  simp at ktwopi
  obtain ⟨ξre, ξim⟩ := Complex.arg_eq_zero_iff.mp ktwopi.symm
  obtain ⟨ξℝ, ξeq⟩ := Complex.canLift.prf ξ ξim
  have ξℝpos: 0 ≤ ξℝ := by
    convert ξre
    rw [← ξeq]
    simp
  have ξℝeval: (ξPolynomialℝ s t).eval ξℝ = 0 := by
    unfold ξPolynomialℝ
    simp
    rw [← ξeq] at mem'
    norm_cast at mem'
  have ξℝpos': 0 < ξℝ  := by
    apply lt_of_le_of_ne ξℝpos
    by_contra eq0
    rw [← eq0] at ξℝeval
    unfold ξPolynomialℝ at ξℝeval
    simp at ξℝeval
  have ξℝuniqueCond: (fun ξ ↦ ξ > 0 ∧ Polynomial.eval ξ (ξPolynomialℝ s t) = 0) ξℝ := by
    simp
    constructor
    · exact ξℝpos'
    · exact ξℝeval
  rw [← ξeq]
  norm_cast
  obtain unique := ξ₀unique ξℝ ξℝuniqueCond
  exact unique


theorem ΦAsymptotic (s t: ℕ+) (coprime: s.Coprime t):
Filter.Tendsto (fun (i:ℕ) ↦ (Φ s t i:ℂ) * ((ξ₀ s t)^i * (1 - (ξ₀ s t)) * (s * (ξ₀ s t)^(s:ℕ) + t * (ξ₀ s t)^(t:ℕ)))) Filter.atTop (nhds 1) := by
  obtain ⟨⟨ξ₀pos, ξ₀eq⟩, ξ₀unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  have funrw:
    (fun (i:ℕ) ↦ (Φ s t i:ℂ) * ((ξ₀ s t)^i * (1 - (ξ₀ s t)) * (s * (ξ₀ s t)^(s:ℕ) + t * (ξ₀ s t)^(t:ℕ)))) =
    (fun (i:ℕ) ↦ 1 +
    ∑ ξ ∈ (ξSet s t).erase ↑(ξ₀ s t),
      (↑(ξ₀ s t) / ξ) ^ i *
        ((1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ)))) := by
    ext i
    rw [ΦFormula]
    rw [Finset.sum_mul]
    have mem: (ξ₀ s t: ℂ) ∈ ξSet s t := by
      unfold ξSet
      simp
      constructor
      · by_contra poly0
        have ev1: (ξPolynomial s t).eval 1 = 1 := by
          unfold ξPolynomial
          simp
        rw [poly0] at ev1
        simp at ev1
      · unfold ξPolynomial
        simp
        norm_cast
        unfold ξ₀ ξPolynomialℝ
        simp
        unfold ξPolynomialℝ at ξ₀eq
        simp at ξ₀eq
        exact ξ₀eq
    rw [← Finset.add_sum_erase _ _ mem]
    have left: ((ξ₀ s t: ℂ))⁻¹ ^ i * (1 - (ξ₀ s t: ℂ))⁻¹ * (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ))⁻¹ *
      ((ξ₀ s t: ℂ) ^ i * (1 - (ξ₀ s t: ℂ)) * (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ))) = 1 := by
      simp
      field_simp
      apply div_self
      simp
      constructor
      · constructor
        · rw [imp_iff_not_or]
          left
          show ξ₀ s t ≠ 0
          by_contra ξ0
          rw [ξ0] at mem
          unfold ξSet ξPolynomial at mem
          simp at mem
        · show 1 - (ξ₀ s t : ℂ) ≠ 0
          by_contra ξ1
          apply eq_of_sub_eq_zero at ξ1
          rw [← ξ1] at mem
          unfold ξSet ξPolynomial at mem
          simp at mem
      · show (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ)) ≠ 0
        obtain noneq := ξNonMult s t (ξ₀ s t:ℂ) mem
        contrapose noneq with eq0
        simp at eq0; simp
        have h: s * (ξ₀ s t:ℂ) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ) =
          (s * (ξ₀ s t) ^ (s - 1:ℕ) + t * (ξ₀ s t) ^ (t - 1:ℕ)) * (ξ₀ s t) := by
          rw [add_mul]
          rw [mul_assoc, mul_assoc]
          rw [← pow_succ, ← pow_succ]
          congr
          repeat exact Eq.symm (PNat.natPred_add_one _)
        rw [h] at eq0
        apply mul_eq_zero.mp at eq0
        have h2: (ξ₀ s t:ℂ) ≠ 0 := by
          by_contra ξ0
          rw [ξ0] at mem
          unfold ξSet ξPolynomial at mem
          simp at mem
        simp [h2] at eq0
        exact eq0
    rw [left]
    have right:
      ∑ ξ ∈ (ξSet s t).erase ↑(ξ₀ s t), ξ⁻¹ ^ i * (1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ *
      ((ξ₀ s t) ^ i * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ))) =
      ∑ ξ ∈ (ξSet s t).erase ↑(ξ₀ s t), (ξ₀ s t / ξ)^ i * ((1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ))) := by
      congr 1
      ext ξ
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      rw [mul_right_comm _ _ ((ξ₀ s t: ℂ) ^ i)]
      rw [mul_right_comm _ _ ((ξ₀ s t: ℂ) ^ i)]
      congr
      rw [← mul_pow]
      congr 1
      exact inv_mul_eq_div ξ ↑(ξ₀ s t)
    rw [right]

  rw [funrw]

  have limrw: nhds (1:ℂ) = nhds (1 + 0) := by simp
  rw [limrw]
  apply Filter.Tendsto.add (by simp)

  have limrw2: nhds (0:ℂ) = nhds (∑ ξ ∈ (ξSet s t).erase (ξ₀ s t), 0) := by simp
  rw [limrw2]
  apply tendsto_finset_sum
  intro ξ mem
  simp at mem
  rcases mem with ⟨ne, mem⟩

  have limrw3: nhds (0:ℂ) = nhds (0 * ((1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ)))) := by simp
  rw [limrw3]
  apply Filter.Tendsto.mul_const
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [norm_div]
  refine (div_lt_one ?_).mpr ?_
  · simp
    by_contra ξ0
    rw [ξ0] at mem
    unfold ξSet ξPolynomial at mem
    simp at mem
  · have rwl: ‖(ξ₀ s t: ℂ)‖ = ξ₀ s t := by
      simp
      apply le_of_lt
      unfold ξ₀
      exact ξ₀pos
    rw [rwl]
    apply ξ₀Smallest s t coprime
    · exact mem
    · exact ne
