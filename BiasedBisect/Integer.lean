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

/-
When s and t are positive integers, Δ collaps to a subset of l * gcd(s, t)
-/
theorem Δ_int (s t: ℕ+):
Δ s t ⊆ {δ: ℝ | ∃l: ℕ, δ = l * PNat.gcd s t} := by
  simp only [PNat.gcd_coe]
  intro δ mem
  unfold Δ at mem
  simp only [Set.mem_setOf_eq] at mem
  rcases mem with ⟨p, ⟨q, pq⟩⟩
  simp only [Set.mem_setOf_eq]
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
  simp only [Set.mem_setOf_eq] at mem
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
  simp only [Int.cast_one] at h
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
    simp only [Int.cast_zero]
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
      simp only
    rw [eq']
    apply Jceiled_accum
  · have ceiled_nogrow: Jceiled s t δ = Jceiled s t (δ + 1) := by
      apply Jceiled_gap
      · simp only [le_add_iff_nonneg_right, zero_le_one]
      · exact lt
    have line_empty: (Λline s t (δ + 1)).toFinset = ∅ := by
      simp only [Set.toFinset_eq_empty]
      unfold Λline
      refine Set.preimage_eq_empty ?_
      apply Set.disjoint_of_subset
      · show {(δ:ℝ) + 1} ⊆ {(δ:ℝ) + 1}
        simp only [subset_refl]
      · show Set.range (δₚ s t) ⊆ Δ s t
        refine Set.range_subset_iff.mpr ?_
        intro ⟨p, q⟩
        unfold δₚ; unfold Δ
        simp only [Set.mem_setOf_eq, exists_apply_eq_apply2]
      · simp only [Set.disjoint_singleton_left]
        contrapose lt with isOnΛ
        simp only [not_lt]; simp only [not_not] at isOnΛ
        unfold δnext
        apply le_of_not_gt
        apply Set.IsWF.not_lt_min
        unfold Δfloored
        constructor
        · exact isOnΛ
        · simp only [gt_iff_lt, Set.mem_setOf_eq, lt_add_iff_pos_right, zero_lt_one]
    have line_empty': Jline s t (δ + 1) = 0 := by
      unfold Jline
      rw [line_empty]
      apply Finset.sum_empty
    rw [ceiled_nogrow]
    simp only [Int.cast_add, Int.cast_one, add_eq_left]
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
    simp only
    exact δₖ_int_agree s t k
  · simp only [ge_iff_le, not_le] at n1
    rcases kₙ_not_exist s t n n1 with keq
    rw [keq]
    simp only [Int.cast_zero]

lemma dE_int_homo (s t l: ℕ+) (n: ℝ): l * (dE_int s t n) = dE_int (l * s) (l * t) n := by
  rify
  rw [dE_int_agree, dE_int_agree]
  push_cast
  apply dE_homo s t n l


/-
Let's introduce a new sequence Φ(δ) that's simply Jceiled_int shifted by 1.
-/
noncomputable
def Φ (s t: ℕ+) (δ: ℤ) := 1 + Jceiled_int s t δ

lemma Φ_agree (s t: ℕ+) (δ: ℤ): Φ s t δ = φ s t δ := by
  unfold Φ
  unfold Jceiled_int
  unfold φ
  rfl

/-
Φ(δ) is the unique sequence that satisfies the following conditions:
 - Φ(< 0) = 1
 - Φ(δ ≥ 0) = Φ(δ - s) + Φ(δ - t)
As an example, for s = 1 and t = 2, this is the Fibonacci sequence (shifted in index)
-/
theorem Φ_neg (s t: ℕ+) (δ: ℤ) (dpos: δ < 0): Φ s t δ = 1 := by
  unfold Φ
  simp only [add_eq_left]
  unfold Jceiled_int
  unfold Jceiled
  have line_empty: (Λceiled s t δ).toFinset = ∅ := by
    simp only [Set.toFinset_eq_empty]
    unfold Λceiled
    simp only
    apply Set.eq_empty_iff_forall_not_mem.mpr
    rintro ⟨p, q⟩
    simp only [Set.mem_setOf_eq, not_le]
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
    · simp only [zero_sub]
      have sneg: -(s:ℤ) < 0 := by simp only [Left.neg_neg_iff, Nat.cast_pos, PNat.pos]
      have tneg: -(t:ℤ) < 0 := by simp only [Left.neg_neg_iff, Nat.cast_pos, PNat.pos]
      rw [Φ_neg s t (-(s:ℤ)) sneg]
      rw [Φ_neg s t (-(t:ℤ)) tneg]
      unfold Φ
      have zero: 0 = (-1) + 1 := by simp only [Int.reduceNeg, neg_add_cancel]
      rw [zero]
      rw [← (Jceiled_int_accum s t (-1))]
      unfold Jline_int
      simp only [Int.reduceNeg, neg_add_cancel, Int.cast_zero, Nat.reduceAdd]
      rw [Jline₀]
      nth_rw 2 [add_comm]
      rw [← Φ]
      rw [Φ_neg]
      simp only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one]
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
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.image_univ, Set.mem_inter_iff, Set.mem_range]
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
  simp only [Set.mem_image, Set.mem_Iic, Set.image_univ, Set.mem_inter_iff, Set.mem_Iio,
    Set.mem_range]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩⟩
    constructor
    · rw [← dE_int_agree]
      rw [← h2]
      simp only [Int.cast_lt]
      exact Int.lt_of_le_sub_one h1
    · use x
  · rintro ⟨h1, ⟨x, h2⟩⟩
    use x
    constructor
    · rw [← dE_int_agree] at h1
      rw [← h2] at h1
      simp only [Int.cast_lt] at h1
      exact Int.le_sub_one_of_lt h1
    · exact h2

/-
And finally, we show that Φ is the inverse function of dE in some sense
-/
lemma Φ_inv (s t: ℕ+) (n: ℝ) (n1: n ≥ 1):
ΔceiledByΦ s t n = Set.Iic (dE_int s t n - 1) := by
  have lifted: ((Int.cast '' (ΔceiledByΦ s t n)): Set ℝ) = Int.cast '' Set.Iic (dE_int s t n - 1) := by
    rw [ΔceiledByΦ_agree]
    rw [dE_int_range_agree]
    congr
    exact φ_inv s t n n1
  exact (Set.image_eq_image Int.cast_injective).mp lifted

lemma Φδₖ (s t: ℕ+) (k: ℕ):
Φ s t (δₖ_int s t k) = nₖ s t (k + 1) := by
  rw [Φ_agree]
  rw [δₖ_int_agree]
  apply φδₖ

lemma Φδₖt (s t: ℕ+) (k: ℕ) (kh: k ≥ 1):
Φ s t (δₖ_int s t k - t) = wₖ s t (k + 1) := by
  rw [Φ_agree]
  push_cast
  rw [δₖ_int_agree]
  exact φδₖt _ _ _ kh


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
  simp only [Nat.cast_add, Nat.cast_mul, Set.mem_toFinset, Set.mem_setOf_eq, add_le_add_iff_right,
    le_add_iff_nonneg_left, Nat.cast_nonneg]

def Λexchange (s t: ℕ+): ((ℕ × ℕ) × ℕ) ≃ ((i: ℕ) × (Λceiled s t i).toFinset) where
  toFun | ⟨pq, i⟩ => ⟨i + pq.1 * s + pq.2 * t, ⟨pq, ΛexchangeMem s t pq i⟩⟩
  invFun | ⟨i, ⟨pq, le⟩ ⟩ => ⟨pq, i - (pq.1 * s + pq.2 * t)⟩
  left_inv := by
    unfold Function.LeftInverse
    simp only [Prod.forall, Prod.mk.injEq, true_and]
    intro p q i
    zify
    simp only [add_le_add_iff_right, le_add_iff_nonneg_left, zero_le, Nat.cast_sub, Nat.cast_add,
      Nat.cast_mul, add_sub_add_right_eq_sub, add_sub_cancel_right]
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    simp only
    rintro ⟨i, ⟨pq, le⟩⟩
    simp only [Sigma.mk.injEq]
    unfold Λceiled at le
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at le
    constructor
    · rw [add_assoc]
      refine Nat.sub_add_cancel ?_
      rify
      exact le
    · refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
      rintro ⟨p, q⟩
      unfold Λceiled
      simp only [Nat.cast_add, Nat.cast_mul, Set.mem_toFinset, Set.mem_setOf_eq]
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
  simp only [Finset.mem_range]
  linarith

def Λdecomp: ((j:ℕ) × Finset.range (j + 1)) ≃ (ℕ × ℕ) where
  toFun | ⟨j, n⟩ => (n, j - n)
  invFun | ⟨p, q⟩ => ⟨p + q, ⟨p, ΛdecompMem p q⟩⟩
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

/-
A gross bound for Jₚ to dompose it to a product of f(p) and g(q)
-/
lemma Jₚ_bound: ∀p, ∀q, Jₚ (p, q) ≤ 2^p * 2^q := by
  intro p
  induction p with
  | zero =>
    intro q
    unfold Jₚ
    simp only [zero_add, Nat.choose_zero_right, pow_zero, one_mul]
    exact Nat.one_le_two_pow
  | succ p prev =>
    intro q
    induction q with
    | zero =>
      unfold Jₚ
      simp only [add_zero, Nat.choose_self, pow_zero, mul_one]
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
  simp only [Equiv.coe_fn_mk]

  let term := fun (⟨j, c⟩:(j:ℕ) × Finset.range (j + 1)) ↦ ((Jₚ (c, j - c)) * x ^ (c * s + (j - c) * t: ℕ ))
  have binom: ∀(j:ℕ), HasSum (fun (c:Finset.range (j + 1)) ↦ term ⟨j, c⟩ ) ((x ^ (s:ℕ) + x ^ (t:ℕ))^j) := by
    intro j
    rw [add_pow]
    let f(c: ℕ) := (x ^ (s:ℕ)) ^ c * (x ^ (t:ℕ)) ^ (j - c) * (j.choose c)
    have left: (fun c ↦ term ⟨j, c⟩) = (fun (c:Finset.range (j + 1)) ↦ f c) ∘ (↑) := by
      unfold term f Jₚ
      ext c
      rcases c with ⟨c, mem⟩
      simp only [Finset.mem_range] at mem
      simp only [Function.comp_apply]
      rw [← pow_mul, ← pow_mul]
      rw [← pow_add]
      nth_rw 4 [mul_comm]
      congr 2
      · congr
        rw [← Nat.add_sub_assoc]
        · simp only [add_tsub_cancel_left]
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
    simp only [Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk, add_tsub_cancel_left, Prod.mk.eta]
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
          simp only [RCLike.norm_natCast]
        have right: ‖(2: K) ^ pq.1 * (2: K) ^ pq.2‖ = (2 ^ pq.1 * 2 ^ pq.2: ℕ) := by
          simp only [norm_mul, norm_pow, RCLike.norm_ofNat, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_ofNat]
        rw [left, right]
        apply Nat.cast_le.mpr
        apply Jₚ_bound
      · simp only [norm_pow, le_refl]
      · apply norm_nonneg
      · apply norm_nonneg
    apply Summable.of_norm_bounded termBound ?_ raise
    · show Summable termBound
      apply Summable.mul_norm
      repeat
        simp only [norm_pow, norm_mul, RCLike.norm_ofNat, summable_geometric_iff_norm_lt_one,
          Real.norm_ofNat, norm_norm]
        apply (lt_inv_mul_iff₀ ?_).mp
        · simp only [mul_one]
          apply lt_of_le_of_lt ?_ bound
          apply pow_le_of_le_one
          · simp only [norm_nonneg]
          · apply le_of_lt; apply lt_trans bound; norm_num
          · simp only [ne_eq, PNat.ne_zero, not_false_eq_true]
        · simp only [Nat.ofNat_pos]
  · apply hasSum_geometric_of_norm_lt_one
    apply lt_of_le_of_lt (norm_add_le _ _)
    have half: (1:ℝ) = 2⁻¹ + 2⁻¹ := by norm_num
    rw [half]
    apply add_lt_add
    repeat
      simp only [norm_pow]
      apply lt_of_le_of_lt ?_ bound
      apply pow_le_of_le_one
      · simp only [norm_nonneg]
      · apply le_of_lt; apply lt_trans bound; norm_num
      · simp only [ne_eq, PNat.ne_zero, not_false_eq_true]

noncomputable
def ξPolynomial(s t: ℕ+) :=
  Polynomial.monomial s (1:ℂ) + Polynomial.monomial t (1:ℂ) - Polynomial.C 1

lemma ξPolynomialDerivative(s t: ℕ+):
(ξPolynomial s t).derivative = Polynomial.monomial (s - 1) (s:ℂ) + Polynomial.monomial (t - 1) (t:ℂ) := by
  unfold ξPolynomial
  simp only [map_one, Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_one, sub_zero]
  rw [Polynomial.derivative_monomial, Polynomial.derivative_monomial]
  simp only [one_mul]


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
  simp only [map_one, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_monomial, one_mul, Polynomial.eval_one] at req_of_pol
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
    simp only [sub_self, zero_mul, Nat.cast_eq_zero, PNat.ne_zero] at rs'
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
      simp only [Nat.cast_pow, abs_pow, Nat.abs_cast] at what
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
        simp only [pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq, not_and, Decidable.not_not]
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
  simp only [id_eq]
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_congr rfl
  intro r rmem
  obtain rmem' := Multiset.mem_dedup.mp rmem
  have root1: Multiset.count r (ξPolynomial s t).roots = 1 := by
    apply le_antisymm
    · unfold Polynomial.roots
      have n0: ξPolynomial s t ≠ 0 := by
        exact Polynomial.ne_zero_of_mem_roots rmem'
      simp only [n0, ↓reduceDIte, ge_iff_le]
      obtain ⟨_,multiEq⟩ := Exists.choose_spec (Polynomial.exists_multiset_roots n0)
      rw [multiEq r]
      by_contra ge2
      simp only [not_le] at ge2
      apply Nat.succ_le_iff.mpr at ge2
      apply (Polynomial.le_rootMultiplicity_iff n0).mp at ge2
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at ge2
      obtain ⟨factor, feq⟩ := dvd_iff_exists_eq_mul_left.mp ge2
      obtain der := ξPolynomialDerivative s t
      rw [feq] at der
      simp only [Polynomial.derivative_mul] at der
      rw [Polynomial.derivative_pow] at der
      have square: (Polynomial.X - Polynomial.C r) ^ 2 = (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C r) := by
        ring
      rw [square] at der
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one] at der
      rw [← mul_assoc, ← mul_assoc, ← add_mul] at der
      have dvd: Polynomial.X - Polynomial.C r ∣ Polynomial.monomial (s - 1) (s:ℂ) + Polynomial.monomial (t - 1) (t:ℂ) := by
        exact
          Dvd.intro_left
            (Polynomial.derivative factor * (Polynomial.X - Polynomial.C r) +
              factor * Polynomial.C 2)
            der
      obtain req_of_der := Polynomial.eval_dvd dvd (x := r)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
        Polynomial.eval_add, Polynomial.eval_monomial, GroupWithZero.dvd_iff,
        forall_const] at req_of_der
      obtain req_of_pol := Polynomial.isRoot_of_mem_roots rmem'
      unfold ξPolynomial at req_of_pol
      simp only [map_one, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_monomial, one_mul, Polynomial.eval_one] at req_of_pol
      obtain noneq := ξNonMult s t r rmem
      contradiction
    · exact Multiset.one_le_count_iff_mem.mpr rmem'
  rw [root1]
  simp only [pow_one]

/-
A main theorem: the generating function Z{Φ}(x) converges to a rational function
The bound here is not sharp, but it should be sufficient for future reasoning over complex plane
-/
theorem ZΦ_sum (s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
HasSum (fun i:ℕ ↦ x ^ i * Φ s t i) ((((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹):= by
  unfold ξPolynomial
  simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_pow,
    mul_one, Polynomial.eval_one, add_sub_cancel_right, inv_one, one_mul]
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
     simp only [one_mul]
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
      simp only
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
          simp only [Complex.norm_mul, Complex.norm_natCast, norm_pow]
          unfold Summable
          use (1 - (‖x‖ ^ (s: ℕ) + ‖x‖ ^ (t: ℕ)))⁻¹
          apply pqx_sum s t ‖x‖
          simp only [norm_norm]
          exact bound
        · unfold g
          simp only [norm_pow, summable_geometric_iff_norm_lt_one, norm_norm]
          exact bound2

    apply HasSum.sigma totalSum
    intro i
    simp only
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
    simp only [id_eq]
    apply Finset.sum_eq_single r
    · intro r' r'mem r'ne
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero_iff.mpr
      use r
      constructor
      · exact Finset.mem_erase_of_ne_of_mem (id (Ne.symm r'ne)) h
      · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    · exact fun a ↦ False.elim (a h)

  have h1 :
     ∑ r ∈ roots, ((Lagrange.nodal roots id).eval x) * ((x - r)⁻¹ * ((Polynomial.derivative (Lagrange.nodal roots id)).eval r)⁻¹)
   = ∑ r ∈ roots, (Lagrange.basis roots id r).eval x := by
    apply Finset.sum_congr rfl
    intro r rmem
    rw [h0 r rmem]
    unfold Lagrange.nodal
    rw [Polynomial.eval_prod]
    simp only [id_eq, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
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
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, id_eq,
      Polynomial.eval_mul]
    rw [mul_comm]
  rw [h1]
  rw [← Polynomial.eval_finset_sum]
  rw [Lagrange.sum_basis (Set.injOn_id _) hasroots]
  simp only [Polynomial.eval_one]

lemma PartialFractionDecompostion2 [Field F] [DecidableEq F]
(x: F) (roots: Finset F) (coef: F)
(hasroots: roots.Nonempty) (notroot: x ∉ roots) (not1: x ≠ 1) (onenotroot: 1 ∉ roots):
(((Polynomial.C coef * Lagrange.nodal roots id).eval 1)⁻¹ - ((Polynomial.C coef * Lagrange.nodal roots id).eval x)⁻¹) * (1 - x)⁻¹
 = ∑ r ∈ roots, (x - r)⁻¹ * (r - 1)⁻¹ * ((Polynomial.derivative (Polynomial.C coef * Lagrange.nodal roots id)).eval r)⁻¹ := by
  rw [Polynomial.derivative_C_mul]
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  simp only [Polynomial.eval_C, mul_inv_rev, Polynomial.eval_mul]
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
  simp only [one_mul, neg_sub, mul_one, sub_sub_sub_cancel_left]


lemma ΦX_sum_eq(s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
(((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹ =
∑ ξ ∈ ξSet s t, (x - ξ)⁻¹ * (ξ - 1)⁻¹*(s * ξ^(s - 1:ℕ) + t * ξ^(t - 1:ℕ))⁻¹ := by
  rw [ξPolynomialFactorize]
  have nonempty: (ξSet s t).Nonempty := by
    by_contra empty
    simp only [Finset.not_nonempty_iff_eq_empty] at empty
    obtain factorize := ξPolynomialFactorize s t
    rw [empty] at factorize
    simp only [Lagrange.nodal_empty, mul_one] at factorize
    obtain eval: (ξPolynomial s t).eval 0 = (ξPolynomial s t).eval 1 := by
      rw [factorize]
      simp only [Polynomial.eval_C]
    unfold ξPolynomial at eval
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, ne_eq,
      PNat.ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, Polynomial.eval_one, zero_sub,
      one_pow, mul_one, add_sub_cancel_right] at eval
    norm_num at eval
  have xnotroot: x ∉ ξSet s t := by
    unfold ξSet
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def, not_and]
    rw [imp_iff_not_or]
    right
    unfold ξPolynomial
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
      Polynomial.eval_one]
    apply sub_ne_zero.mpr
    have h: ‖x ^ (s:ℕ) + x ^ (t:ℕ)‖ ≠ ‖(1:ℂ)‖ := by
      apply ne_of_lt
      apply lt_of_le_of_lt (norm_add_le _ _)
      have right: ‖(1:ℂ)‖ = 2⁻¹ + 2⁻¹ := by norm_num
      rw [right]
      gcongr
      repeat
      · simp only [norm_pow]
        refine lt_of_le_of_lt ?_ bound
        refine pow_le_of_le_one ?_ ?_ ?_
        · simp only [norm_nonneg]
        · apply le_trans (le_of_lt bound)
          norm_num
        · simp only [ne_eq, PNat.ne_zero, not_false_eq_true]
    exact fun a ↦ h (congrArg norm a)
  have xnotone: x ≠ 1 := by
    contrapose bound with one
    simp only [ne_eq, Decidable.not_not] at one
    rw [one]
    norm_num
  have onenotroot: 1 ∉ ξSet s t := by
    by_contra isroot
    unfold ξSet at isroot
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def] at isroot
    rcases isroot with ⟨_, eval⟩
    unfold ξPolynomial at eval
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_pow,
      mul_one, Polynomial.eval_one, add_sub_cancel_right, one_ne_zero] at eval
  rw [PartialFractionDecompostion2 _ _ _ nonempty xnotroot xnotone onenotroot]
  rw [← ξPolynomialFactorize]
  rw [ξPolynomialDerivative]
  simp only [Polynomial.eval_add, Polynomial.eval_monomial]


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
  simp only [map_one, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
    Polynomial.eval_one] at mem
  obtain ⟨_, polyeq⟩ := mem
  have ξ0: ξ ≠ 0 := by
    by_contra zero
    rw [zero] at polyeq
    simp only [ne_eq, PNat.ne_zero, not_false_eq_true, zero_pow, add_zero, zero_sub, neg_eq_zero,
      one_ne_zero] at polyeq
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
    simp only [one_mul, mul_one]

  rw [rw_sum]
  apply HasSum.mul_right
  apply HasSum.mul_right
  apply hasSum_geometric_of_norm_lt_one
  show ‖x * ξ⁻¹‖ < 1
  rw [norm_mul]
  rw [norm_inv]
  have ξgt0: 0 < ‖ξ‖ := by
    simp only [norm_pos_iff, ne_eq]
    exact ξ0
  apply (mul_inv_lt_iff₀ ξgt0).mpr
  simp only [one_mul]
  apply lt_of_lt_of_le bound
  contrapose polyeq
  simp only [not_le] at polyeq
  apply sub_ne_zero_of_ne
  have nomr_ne: ‖ξ ^ (s:ℕ) + ξ ^ (t:ℕ)‖ ≠ ‖(1:ℂ)‖ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (norm_add_le _ _)
    have right: ‖(1:ℂ)‖ = 2⁻¹ + 2⁻¹ := by norm_num
    rw [right]
    gcongr
    repeat
    · simp only [norm_pow]
      refine lt_of_le_of_lt ?_ polyeq
      refine pow_le_of_le_one ?_ ?_ ?_
      · simp only [norm_nonneg]
      · apply le_trans (le_of_lt polyeq)
        norm_num
      · simp only [ne_eq, PNat.ne_zero, not_false_eq_true]
  exact fun a ↦ nomr_ne (congrArg norm a)


theorem ΦFormula (s t: ℕ+) (i: ℕ):
Φ s t i = ∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ := by
  let fmsL: FormalMultilinearSeries ℂ ℂ ℂ :=
    fun i ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin i) (Φ s t i)
  have hasFmsL: HasFPowerSeriesAt (fun x ↦ (((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹) fmsL 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    unfold fmsL FormalMultilinearSeries.coeff
    simp only [ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply, Finset.prod_const_one,
      smul_eq_mul, one_mul, zero_add]
    unfold Filter.Eventually
    apply mem_nhds_iff.mpr
    use {x:ℂ | ‖x‖ <2⁻¹}
    simp only [Set.setOf_subset_setOf, Set.mem_setOf_eq, norm_zero, inv_pos, Nat.ofNat_pos,
      and_true]
    constructor
    · apply ZΦ_sum
    · exact isOpen_lt continuous_norm continuous_const
  let fmsR: FormalMultilinearSeries ℂ ℂ ℂ :=
    fun i ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin i) (∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹)
  have hasFmsR: HasFPowerSeriesAt (fun x ↦ (((ξPolynomial s t).eval 1)⁻¹ - ((ξPolynomial s t).eval x)⁻¹) * (1 - x)⁻¹) fmsR 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    unfold fmsR FormalMultilinearSeries.coeff
    simp only [inv_pow, ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply,
      Finset.prod_const_one, smul_eq_mul, one_mul, zero_add]
    unfold Filter.Eventually
    apply mem_nhds_iff.mpr
    use {x:ℂ | ‖x‖ <2⁻¹}
    simp only [Set.setOf_subset_setOf, Set.mem_setOf_eq, norm_zero, inv_pos, Nat.ofNat_pos,
      and_true]
    constructor
    · obtain ZΦ_sum2 := ZΦ_sum2
      simp only [inv_pow] at ZΦ_sum2
      apply ZΦ_sum2
    · exact isOpen_lt continuous_norm continuous_const
  obtain fmsEq := HasFPowerSeriesAt.eq_formalMultilinearSeries hasFmsL hasFmsR
  have coeffL: Φ s t i = fmsL.coeff i := by
    unfold fmsL FormalMultilinearSeries.coeff
    simp only [ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply, Finset.prod_const_one,
      smul_eq_mul, one_mul]
  have coeffR: ∑ξ ∈ ξSet s t, (ξ⁻¹)^i * (1 - ξ)⁻¹ * (s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹ = fmsR.coeff i := by
    unfold fmsR FormalMultilinearSeries.coeff
    simp only [inv_pow, ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply,
      Finset.prod_const_one, smul_eq_mul, one_mul]
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
  simp only [Nat.cast_pos, PNat.pos]

lemma ξPolynomialℝ_mono(s t: ℕ+): StrictMonoOn ((ξPolynomialℝ s t).eval ·) (Set.Ici 0) := by
  unfold ξPolynomialℝ
  simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
    Polynomial.eval_one]
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
      simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, ne_eq,
        PNat.ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, Polynomial.eval_one,
        zero_sub, one_pow, mul_one, add_sub_cancel_right, Set.mem_Ioo, Left.neg_neg_iff,
        zero_lt_one, and_self]
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

lemma ξ₀min (s t: ℕ+): ξ₀ s t > 0 := by
  obtain ⟨⟨range, ev⟩, unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  exact range

lemma ξ₀max (s t: ℕ+): ξ₀ s t < 1 := by
  obtain ⟨⟨range, ev⟩, unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  have leftmem: ξ₀ s t ∈ (Set.Ici 0) := by exact Set.mem_Ici_of_Ioi range
  have rightmem: (1:ℝ) ∈ (Set.Ici 0) := by simp only [Set.mem_Ici, zero_le_one]
  have leftrw: Polynomial.eval (ξ₀ s t) (ξPolynomialℝ s t) = 0 := by
    unfold ξ₀ ξPolynomialℝ
    exact ev
  apply ((ξPolynomialℝ_mono s t).lt_iff_lt leftmem rightmem).mp
  rw [leftrw]
  unfold ξPolynomialℝ
  simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_pow,
    mul_one, Polynomial.eval_one, add_sub_cancel_right, zero_lt_one]

lemma ξ₀eval (s t: ℕ+): (ξPolynomialℝ s t).eval (ξ₀ s t) = 0 := by
  obtain ⟨⟨range, ev⟩, unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  exact ev

lemma ξ₀homo (s t l: ℕ+): (ξ₀ s t) = (ξ₀ (l * s) (l * t)) ^ (l:ℕ) := by
  apply (ξPolynomialℝUniqueRoot s t).unique
  · constructor
    · apply ξ₀min
    · apply ξ₀eval
  · constructor
    · apply pow_pos; apply ξ₀min
    · unfold ξPolynomialℝ
      simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial,
        one_mul, Polynomial.eval_one]
      rw [← pow_mul, ← pow_mul]
      norm_cast
      obtain eval := ξ₀eval (l * s) (l * t)
      unfold ξPolynomialℝ at eval
      simp only [PNat.mul_coe, map_one, Polynomial.eval_sub, Polynomial.eval_add,
        Polynomial.eval_monomial, one_mul, Polynomial.eval_one] at eval
      exact eval

lemma ξ₀Smallest (s t: ℕ+) (coprime: s.Coprime t):
∀ξ ∈ ξSet s t, ξ ≠ ξ₀ s t → ξ₀ s t < ‖ξ‖ := by
  obtain ⟨⟨ξ₀pos, ξ₀eq⟩, ξ₀unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  unfold ξPolynomialℝ at ξ₀eq
  simp only [gt_iff_lt, map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial,
    one_mul, Polynomial.eval_one, and_imp] at ξ₀eq
  intro ξ mem' ne
  unfold ξSet ξPolynomial at mem'
  simp only [map_one, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
    Polynomial.eval_one] at mem'
  rcases mem' with ⟨_, mem'⟩
  obtain mem := eq_of_sub_eq_zero mem'
  obtain memnorm := congrArg norm mem
  have normle: 1 ≤ ‖ξ‖ ^ (s:ℕ) + ‖ξ‖ ^ (t:ℕ)  := by
    rw [← norm_pow, ← norm_pow]
    convert norm_add_le (ξ ^ (s:ℕ)) (ξ ^ (t:ℕ))
    rw [memnorm]
    simp only [norm_one]
  let ξPoly' := Polynomial.monomial s (1:ℝ) + Polynomial.monomial t (1:ℝ)
  let ξPoly'F := (ξPoly'.eval ·)
  have normle': ξPoly'F (ξ₀ s t) ≤ ξPoly'F ‖ξ‖  := by
    unfold ξPoly'F ξPoly' ξ₀ ξPolynomialℝ
    simp only [gt_iff_lt, map_one, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_monomial, one_mul, Polynomial.eval_one, and_imp]
    convert normle
    obtain ξ₀eq := eq_of_sub_eq_zero ξ₀eq
    rw [ξ₀eq]
  have mono: StrictMonoOn ξPoly'F (Set.Ici 0) := by
    unfold ξPoly'F ξPoly'
    simp only [Polynomial.eval_add, Polynomial.eval_monomial, one_mul]
    apply StrictMonoOn.add
    repeat apply PowMono
  have normleFromMono: ξ₀ s t ≤ ‖ξ‖ := by
    refine (mono.le_iff_le ?_ ?_).mp normle'
    · simp only [Set.mem_Ici]
      apply le_of_lt
      apply gt_iff_lt.mp
      exact ξ₀pos
    · simp only [Set.mem_Ici, norm_nonneg]
  apply lt_of_le_of_ne normleFromMono
  contrapose ne with eq
  simp only [ne_eq, Decidable.not_not];
  unfold ξ₀ ξPolynomialℝ at eq
  simp only [gt_iff_lt, map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial,
    one_mul, Polynomial.eval_one, and_imp, ne_eq, Decidable.not_not] at eq
  rw [eq] at ξ₀eq
  simp only [norm_one] at memnorm
  rw [← memnorm] at ξ₀eq
  rw [← norm_pow, ← norm_pow] at ξ₀eq
  obtain ξ₀eq := eq_of_sub_eq_zero ξ₀eq
  obtain arg_eq := Complex.norm_add_eq_iff.mp ξ₀eq.symm
  have ξnon0: ξ ≠ 0 := by
    by_contra ξ0
    rw [ξ0] at mem
    simp only [ne_eq, PNat.ne_zero, not_false_eq_true, zero_pow, add_zero, zero_ne_one] at mem
  have s0: ¬ ξ ^ (s:ℕ) = 0 := by
    simp only [ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact ξnon0
  have t0: ¬ ξ ^ (t:ℕ) = 0 := by
    simp only [ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact ξnon0
  simp only [s0, t0, false_or] at arg_eq
  obtain same_ray: SameRay ℝ (ξ ^ (s:ℕ)) (ξ ^ (t:ℕ)) := by
    apply Complex.sameRay_iff.mpr
    right; right; exact arg_eq
  obtain same_ray1: SameRay ℝ (ξ ^ (s:ℕ)) 1 := by
    rw [← mem]
    apply SameRay.add_right
    · rfl
    · exact same_ray
  obtain arg0s := Complex.sameRay_iff.mp same_ray1
  simp only [s0, one_ne_zero, Complex.arg_one, false_or] at arg0s
  obtain arg0t := (Complex.sameRay_iff.mp same_ray)
  simp only [s0, t0, false_or] at arg0t
  rw [arg0s] at arg0t
  obtain angles := congrArg (fun (a:ℝ) ↦ (a:Real.Angle)) arg0s
  obtain anglet := congrArg (fun (a:ℝ) ↦ (a:Real.Angle)) arg0t.symm
  rw [Complex.arg_pow_coe_angle, ← Real.Angle.natCast_mul_eq_nsmul] at angles
  rw [Complex.arg_pow_coe_angle, ← Real.Angle.natCast_mul_eq_nsmul] at anglet
  obtain ⟨ks, kseq⟩ := Real.Angle.coe_eq_zero_iff.mp angles
  obtain ⟨kt, kteq⟩ := Real.Angle.coe_eq_zero_iff.mp anglet
  simp only [zsmul_eq_mul] at kseq
  simp only [zsmul_eq_mul] at kteq
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
    simp only [Int.natAbs_ofNat, PNat.coprime_coe]
    exact coprime
  obtain ⟨factor, feq⟩ := dvd
  rw [feq] at kseq'
  simp only [Int.cast_mul, Int.cast_natCast, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
    not_false_eq_true, mul_div_cancel_left₀] at kseq'
  obtain ktwopi: factor * (2 * Real.pi) = ξ.arg := (eq_div_iff twopi0).mp kseq'
  have factor0: factor = 0 := by
    apply le_antisymm
    · by_contra pos
      simp only [not_le] at pos
      have : 2 * Real.pi ≤ ξ.arg := by
        rw [← one_mul (2 * Real.pi)]
        rw [← ktwopi]
        rw [mul_le_mul_right]
        · exact Int.cast_one_le_of_pos pos
        · exact Real.two_pi_pos
      obtain what := le_trans this (Complex.arg_le_pi ξ)
      nth_rw 2 [← one_mul Real.pi] at what
      apply (mul_le_mul_right Real.pi_pos).mp at what
      simp only [Nat.not_ofNat_le_one] at what
    · by_contra neg
      simp only [not_le] at neg
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
      simp only [Nat.not_ofNat_lt_one] at what
  rw [factor0] at ktwopi
  simp only [Int.cast_zero, zero_mul] at ktwopi
  obtain ⟨ξre, ξim⟩ := Complex.arg_eq_zero_iff.mp ktwopi.symm
  obtain ⟨ξℝ, ξeq⟩ := Complex.canLift.prf ξ ξim
  have ξℝpos: 0 ≤ ξℝ := by
    convert ξre
    rw [← ξeq]
    simp only [Complex.ofReal_re]
  have ξℝeval: (ξPolynomialℝ s t).eval ξℝ = 0 := by
    unfold ξPolynomialℝ
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
      Polynomial.eval_one]
    rw [← ξeq] at mem'
    norm_cast at mem'
  have ξℝpos': 0 < ξℝ  := by
    apply lt_of_le_of_ne ξℝpos
    by_contra eq0
    rw [← eq0] at ξℝeval
    unfold ξPolynomialℝ at ξℝeval
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, ne_eq,
      PNat.ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, Polynomial.eval_one, zero_sub,
      neg_eq_zero, one_ne_zero] at ξℝeval
  have ξℝuniqueCond: (fun ξ ↦ ξ > 0 ∧ Polynomial.eval ξ (ξPolynomialℝ s t) = 0) ξℝ := by
    simp only [gt_iff_lt]
    constructor
    · exact ξℝpos'
    · exact ξℝeval
  rw [← ξeq]
  norm_cast
  obtain unique := ξ₀unique ξℝ ξℝuniqueCond
  exact unique

noncomputable
def Res₀ (s t: ℕ+): ℝ := (1 - (ξ₀ s t)) * (s * (ξ₀ s t)^(s:ℕ) + t * (ξ₀ s t)^(t:ℕ))

lemma Res₀pos (s t: ℕ+): Res₀ s t > 0 := by
  unfold Res₀
  apply mul_pos
  · apply sub_pos_of_lt
    exact ξ₀max s t
  · apply add_pos
    all_goals
      apply mul_pos
      · simp only [Nat.cast_pos, PNat.pos]
      · apply pow_pos
        exact ξ₀min s t

lemma ΦAsymptotic (s t: ℕ+) (coprime: s.Coprime t):
Filter.Tendsto (fun (i:ℕ) ↦ (Φ s t i:ℂ) * ((ξ₀ s t)^i * Res₀ s t)) Filter.atTop (nhds 1) := by
  obtain ⟨⟨ξ₀pos, ξ₀eq⟩, ξ₀unique⟩ := (ξPolynomialℝUniqueRoot s t).choose_spec
  have funrw:
    (fun (i:ℕ) ↦ (Φ s t i:ℂ) * ((ξ₀ s t)^i * Res₀ s t)) =
    (fun (i:ℕ) ↦ 1 +
    ∑ ξ ∈ (ξSet s t).erase ↑(ξ₀ s t),
      (↑(ξ₀ s t) / ξ) ^ i *
        ((1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ)))) := by
    ext i
    unfold Res₀
    push_cast
    nth_rw 2 [← mul_assoc]
    rw [ΦFormula]
    rw [Finset.sum_mul]
    have mem: (ξ₀ s t: ℂ) ∈ ξSet s t := by
      unfold ξSet
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def]
      constructor
      · by_contra poly0
        have ev1: (ξPolynomial s t).eval 1 = 1 := by
          unfold ξPolynomial
          simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial,
            one_pow, mul_one, Polynomial.eval_one, add_sub_cancel_right]
        rw [poly0] at ev1
        simp only [Polynomial.eval_zero, zero_ne_one] at ev1
      · unfold ξPolynomial
        simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial,
          one_mul, Polynomial.eval_one]
        norm_cast
        unfold ξ₀ ξPolynomialℝ
        simp only [gt_iff_lt, map_one, Polynomial.eval_sub, Polynomial.eval_add,
          Polynomial.eval_monomial, one_mul, Polynomial.eval_one, and_imp]
        unfold ξPolynomialℝ at ξ₀eq
        simp only [gt_iff_lt, map_one, Polynomial.eval_sub, Polynomial.eval_add,
          Polynomial.eval_monomial, one_mul, Polynomial.eval_one, and_imp] at ξ₀eq
        exact ξ₀eq
    rw [← Finset.add_sum_erase _ _ mem]
    have left: ((ξ₀ s t: ℂ))⁻¹ ^ i * (1 - (ξ₀ s t: ℂ))⁻¹ * (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ))⁻¹ *
      ((ξ₀ s t: ℂ) ^ i * (1 - (ξ₀ s t: ℂ)) * (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ))) = 1 := by
      simp only [inv_pow]
      field_simp
      apply div_self
      simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', Complex.ofReal_eq_zero, not_or, not_and,
        Decidable.not_not]
      constructor
      · constructor
        · rw [imp_iff_not_or]
          left
          show ξ₀ s t ≠ 0
          by_contra ξ0
          rw [ξ0] at mem
          unfold ξSet ξPolynomial at mem
          simp only [map_one, Complex.ofReal_zero, Multiset.mem_toFinset, Polynomial.mem_roots',
            ne_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
            Polynomial.eval_monomial, PNat.ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
            Polynomial.eval_one, zero_sub, neg_eq_zero, one_ne_zero, and_false] at mem
        · show 1 - (ξ₀ s t : ℂ) ≠ 0
          by_contra ξ1
          apply eq_of_sub_eq_zero at ξ1
          rw [← ξ1] at mem
          unfold ξSet ξPolynomial at mem
          simp only [map_one, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
            Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
            Polynomial.eval_monomial, one_pow, mul_one, Polynomial.eval_one, add_sub_cancel_right,
            one_ne_zero, and_false] at mem
      · show (s * (ξ₀ s t: ℂ) ^ (s:ℕ) + t * (ξ₀ s t: ℂ) ^ (t:ℕ)) ≠ 0
        obtain noneq := ξNonMult s t (ξ₀ s t:ℂ) mem
        contrapose noneq with eq0
        simp only [ne_eq, Decidable.not_not] at eq0;
        simp only [ne_eq, Decidable.not_not]
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
          simp only [map_one, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
            Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
            Polynomial.eval_monomial, PNat.ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
            Polynomial.eval_one, zero_sub, neg_eq_zero, one_ne_zero, and_false] at mem
        simp only [h2, or_false] at eq0
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

  have limrw: nhds (1:ℂ) = nhds (1 + 0) := by simp only [add_zero]
  rw [limrw]
  apply Filter.Tendsto.add (by simp only [tendsto_const_nhds_iff])

  have limrw2: nhds (0:ℂ) = nhds (∑ ξ ∈ (ξSet s t).erase (ξ₀ s t), 0) := by simp only [Finset.sum_const_zero]
  rw [limrw2]
  apply tendsto_finset_sum
  intro ξ mem
  simp only [Finset.mem_erase, ne_eq] at mem
  rcases mem with ⟨ne, mem⟩

  have limrw3: nhds (0:ℂ) = nhds (0 * ((1 - ξ)⁻¹ * (s * ξ ^ (s:ℕ) + t * ξ ^ (t:ℕ))⁻¹ * (1 - (ξ₀ s t)) * (s * (ξ₀ s t) ^ (s:ℕ) + t * (ξ₀ s t) ^ (t:ℕ)))) := by simp only [zero_mul]
  rw [limrw3]
  apply Filter.Tendsto.mul_const
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [norm_div]
  refine (div_lt_one ?_).mpr ?_
  · simp only [norm_pos_iff, ne_eq]
    by_contra ξ0
    rw [ξ0] at mem
    unfold ξSet ξPolynomial at mem
    simp only [map_one, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, PNat.ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, Polynomial.eval_one, zero_sub, neg_eq_zero,
      one_ne_zero, and_false] at mem
  · have rwl: ‖(ξ₀ s t: ℂ)‖ = ξ₀ s t := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_eq_self]
      apply le_of_lt
      unfold ξ₀
      exact ξ₀pos
    rw [rwl]
    apply ξ₀Smallest s t coprime
    · exact mem
    · exact ne

lemma ΦAsymptoticℝ (s t: ℕ+) (coprime: s.Coprime t):
Filter.Tendsto (fun (i:ℕ) ↦ (Φ s t i:ℝ) * ((ξ₀ s t)^i * Res₀ s t)) Filter.atTop (nhds 1) := by
  obtain complex := ΦAsymptotic s t coprime
  norm_cast at complex
  have one: (1:ℂ) = (1:ℝ) := by simp only [Complex.ofReal_one]
  rw [one] at complex
  exact Filter.tendsto_ofReal_iff.mp complex

lemma ΦAsymptoticℝ' (s t: ℕ+) (coprime: s.Coprime t):
Filter.Tendsto (fun (i:ℤ) ↦ (Φ s t i:ℝ) * ((ξ₀ s t)^i * Res₀ s t)) Filter.atTop (nhds 1) := by
  have funrw: (fun (i:ℕ) ↦ (Φ s t i:ℝ) * ((ξ₀ s t)^i * Res₀ s t)) = (fun (i:ℤ) ↦ (Φ s t i:ℝ) * ((ξ₀ s t)^i * Res₀ s t)) ∘ (fun (i:ℕ) ↦ (i:ℤ)) := by
    rfl
  obtain asymp := ΦAsymptoticℝ s t coprime
  rw [funrw] at asymp
  apply Filter.tendsto_map' at asymp
  convert asymp
  exact Eq.symm Nat.map_cast_int_atTop

lemma dE_int_Asymptotic_coprime (s t: ℕ+) (coprime: s.Coprime t):
Filter.Tendsto (fun n ↦ (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n) Filter.atTop (nhds (-1:ℝ)) := by
  have leftSide (n: ℝ) (n1: n > 1): Φ s t (dE_int s t n - 1) ≤ n := by
    have mem: dE_int s t n - 1 ∈ Set.Iic (dE_int s t n - 1) := by simp only [Set.mem_Iic, le_refl]
    rw [← Φ_inv s t n (le_of_lt n1)] at mem
    unfold ΔceiledByΦ at mem
    simp only [Set.mem_setOf_eq] at mem
    exact mem
  have rightSide (n: ℝ) (n1: n > 1): n < Φ s t (dE_int s t n) := by
    have mem: dE_int s t n ∉ Set.Iic (dE_int s t n - 1) := by simp only [Set.mem_Iic,
      le_sub_self_iff, Int.reduceLE, not_false_eq_true]
    rw [← Φ_inv s t n (le_of_lt n1)] at mem
    unfold ΔceiledByΦ at mem
    simp only [Set.mem_setOf_eq, not_le] at mem
    exact mem
  have Φ0 {d: ℤ}: Φ s t d > (0:ℝ) := by
    norm_cast
    unfold Φ
    simp only [gt_iff_lt, add_pos_iff, Nat.lt_one_iff, pos_of_gt, true_or]
  have ξ0 (n: ℝ): ξ₀ s t ^ (dE_int s t n - 1) > 0 := by apply zpow_pos (ξ₀min s t)
  have ξ0' (n: ℝ): ξ₀ s t ^ (dE_int s t n) > 0 := by apply zpow_pos (ξ₀min s t)
  have ξRes₀0 (n: ℝ): ξ₀ s t ^ dE_int s t n * Res₀ s t > 0 := mul_pos (ξ0' n) (Res₀pos s t)
  have leftSide0 (n: ℝ): (Φ s t (dE_int s t n - 1)) * (ξ₀ s t ^ (dE_int s t n - 1) * Res₀ s t) > 0 :=
    mul_pos Φ0 (mul_pos (ξ0 n) (Res₀pos s t))
  have leftSide1 (n: ℝ) : (Φ s t (dE_int s t n - 1)) * (ξ₀ s t ^ (dE_int s t n - 1) * Res₀ s t) * ξ₀ s t > 0 :=
    mul_pos (leftSide0 n) (ξ₀min s t)

  have rightSide0 (n: ℝ) : (Φ s t (dE_int s t n)) * (ξ₀ s t ^ (dE_int s t n) * Res₀ s t) > 0 :=
    mul_pos Φ0 (mul_pos (ξ0' n) (Res₀pos s t))

  have nξ0' (n: ℝ) (n1: n > 1): n * ξ₀ s t ^ (dE_int s t n) > 0 :=
    mul_pos (lt_trans Real.zero_lt_one n1) (ξ0' n)

  have mid (n: ℝ) (n1: n > 1): n * ξ₀ s t ^ dE_int s t n * Res₀ s t > 0 :=
    mul_pos (nξ0' n n1) (Res₀pos s t)
  have logngt0 (n: ℝ) (n1: n > 1): 0 < Real.log n := Real.log_pos n1
  have logn0 (n: ℝ) (n1: n > 1): Real.log n ≠ 0 := Ne.symm (ne_of_lt (logngt0 n n1))
  have n0 (n: ℝ) (n1: n > 1): n ≠ 0 := ne_of_gt (lt_trans Real.zero_lt_one n1)

  have leftSide' (n: ℝ) (n1: n > 1):
    (Real.log (Φ s t (dE_int s t n - 1) * ((ξ₀ s t)^(dE_int s t n - 1) * Res₀ s t)) + Real.log (ξ₀ s t)) * (Real.log n)⁻¹ ≤
    1 + (dE_int s t n) * Real.log ((ξ₀ s t)) / Real.log n + Real.log (Res₀ s t) / Real.log n := by

    rw [← Real.log_mul (ne_of_gt (leftSide0 n)) (ne_of_gt (ξ₀min s t))]
    rw [← div_self (logn0 n n1)]
    rw [← add_div, ← add_div]
    rw [← Real.log_zpow]
    rw [← Real.log_mul (n0 n n1) (ne_of_gt (ξ0' n))]
    rw [← Real.log_mul (ne_of_gt (nξ0' n n1)) (ne_of_gt (Res₀pos s t))]
    apply (div_le_div_iff_of_pos_right (logngt0 n n1)).mpr
    apply (Real.strictMonoOn_log.le_iff_le (leftSide1 n) (mid n n1)).mpr
    rw [mul_assoc, mul_right_comm, ← zpow_add_one₀ (ne_of_gt (ξ₀min s t)), sub_add_cancel, mul_assoc]
    apply (mul_le_mul_iff_of_pos_right (ξRes₀0 n)).mpr
    exact leftSide n n1

  have rightSide' (n: ℝ) (n1: n > 1):
    1 + (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n + Real.log (Res₀ s t) / Real.log n <
    (Real.log (Φ s t (dE_int s t n) * ((ξ₀ s t)^(dE_int s t n) * Res₀ s t))) * (Real.log n)⁻¹ := by
    rw [← div_self (logn0 n n1)]
    rw [← add_div, ← add_div]
    rw [← Real.log_zpow]
    rw [← Real.log_mul (n0 n n1) (ne_of_gt (ξ0' n))]
    rw [← Real.log_mul (ne_of_gt (nξ0' n n1)) (ne_of_gt (Res₀pos s t))]
    apply (div_lt_div_iff_of_pos_right (logngt0 n n1)).mpr
    apply (Real.strictMonoOn_log.lt_iff_lt (mid n n1) (rightSide0 n)).mpr
    rw [mul_assoc]
    apply (mul_lt_mul_iff_of_pos_right (ξRes₀0 n)).mpr
    exact rightSide n n1

  have loginv: Filter.Tendsto ((Real.log ·)⁻¹) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.inv_tendsto_atTop
    exact Real.tendsto_log_atTop
  have log1: Filter.Tendsto Real.log (nhds 1) (nhds 0) := by
    rw [← Real.log_one]
    apply ContinuousAt.tendsto
    apply Real.continuousAt_log
    norm_num
  have dElim: Filter.Tendsto (dE_int s t) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro d
    use Φ s t d
    intro n dlen
    obtain dEdlen:= dE_mono s t dlen
    rw [← dE_int_agree, ← dE_int_agree] at dEdlen
    norm_cast at dEdlen
    refine le_trans ?_ dEdlen
    apply le_of_lt
    have mem: d ∈ ΔceiledByΦ s t (Φ s t d) := by
      unfold ΔceiledByΦ
      simp only [Nat.cast_le, Set.mem_setOf_eq, le_refl]
    have g1: Φ s t d ≥ (1:ℝ) := by
      norm_cast
      unfold Φ
      simp only [le_add_iff_nonneg_right, zero_le]
    rw [Φ_inv _ _ _ g1] at mem
    exact Int.lt_of_le_sub_one mem


  have leftLimit:
    Filter.Tendsto (fun n ↦ (Real.log (Φ s t (dE_int s t n - 1) * ((ξ₀ s t)^(dE_int s t n - 1) * Res₀ s t)) + Real.log (ξ₀ s t)) * (Real.log n)⁻¹) Filter.atTop (nhds 0) := by
    rw [(by norm_num: (0:ℝ) = (0 + Real.log (ξ₀ s t)) * 0)]
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.add_const
      rw [(by rfl: (fun n ↦ Real.log (↑(Φ s t (dE_int s t n - 1)) * (ξ₀ s t ^ (dE_int s t n - 1) * Res₀ s t))) = Real.log ∘ (fun d ↦ ↑(Φ s t d) * (ξ₀ s t ^ d * Res₀ s t)) ∘ (fun n ↦ dE_int s t n - 1))]
      apply Filter.Tendsto.comp log1
      apply Filter.Tendsto.comp
      · apply ΦAsymptoticℝ' s t coprime
      · apply Filter.tendsto_atTop_add_const_right
        exact dElim
    · exact loginv

  have rightLimit:
    Filter.Tendsto (fun n ↦ (Real.log (Φ s t (dE_int s t n) * ((ξ₀ s t)^(dE_int s t n) * Res₀ s t)))  * (Real.log n)⁻¹) Filter.atTop (nhds 0) := by
    rw [(by norm_num: (0:ℝ) = 0 * 0)]
    apply Filter.Tendsto.mul
    rw [(by rfl: (fun n ↦ Real.log (↑(Φ s t (dE_int s t n)) * (ξ₀ s t ^ (dE_int s t n) * Res₀ s t))) = Real.log ∘ (fun d ↦ ↑(Φ s t d) * (ξ₀ s t ^ d * Res₀ s t)) ∘ (fun n ↦ dE_int s t n))]
    · apply Filter.Tendsto.comp log1
      apply Filter.Tendsto.comp
      · apply ΦAsymptoticℝ' s t coprime
      · exact dElim
    · exact loginv

  have midLimit:
    Filter.Tendsto (fun n ↦ 1 + (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n + Real.log (Res₀ s t) / Real.log n) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' leftLimit rightLimit
    all_goals
      unfold Filter.Eventually
      apply Filter.mem_atTop_sets.mpr
      use 2
      intro n n2
      have n1 : n > 1 := lt_of_lt_of_le (by norm_num) n2
      simp only [Set.mem_setOf_eq]
    · apply leftSide' n n1
    · apply le_of_lt
      apply rightSide' n n1

  have funrw: (fun n ↦ (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n) =
    (fun n ↦ 1 + (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n + Real.log (Res₀ s t) / Real.log n - (1 + Real.log (Res₀ s t) / Real.log n)) := by
    ext n
    ring

  rw [funrw]
  rw [(by norm_num: (-1:ℝ) = 0 - (1 + Real.log (Res₀ s t) * 0))]
  apply Filter.Tendsto.sub midLimit
  apply Filter.Tendsto.const_add
  apply Filter.Tendsto.const_mul
  exact loginv

lemma reduce_coprime (s t: ℕ+): ∃ (l S T: ℕ+), s = l * S ∧ t = l * T ∧ S.Coprime T := by
  obtain ⟨S, seq⟩ := PNat.gcd_dvd_left s t
  obtain ⟨T, teq⟩ := PNat.gcd_dvd_right s t
  have coprime: S.Coprime T := by
    obtain gcd_left := Nat.gcd_mul_left (s.gcd t) S T
    norm_cast at gcd_left
    rw [← seq, ← teq] at gcd_left
    exact mul_eq_left.mp (id (Eq.symm gcd_left))
  use s.gcd t, S, T


lemma dE_int_Asymptotic (s t: ℕ+):
Filter.Tendsto (fun n ↦ (dE_int s t n:ℝ) * Real.log ((ξ₀ s t)) / Real.log n) Filter.atTop (nhds (-1:ℝ)) := by
  obtain ⟨l, S, T, seq, teq, coprime⟩ := reduce_coprime s t

  obtain base := dE_int_Asymptotic_coprime S T coprime
  refine Filter.Tendsto.congr ?_ base
  intro n
  rw [seq, teq, ← dE_int_homo]
  rw [mul_comm _ (dE_int S T n)]
  push_cast
  rw [mul_assoc, ← Real.log_pow, ← ξ₀homo]

lemma wₖ_Asymtotic (s t: ℕ+):
Filter.Tendsto (fun k ↦ (wₖ s t k: ℝ) / nₖ s t k) Filter.atTop (nhds (ξ₀ s t ^ (t: ℕ))) := by

  have funrw: (fun k ↦ (wₖ s t k: ℝ) / nₖ s t k) =ᶠ[Filter.atTop] (fun k ↦ (wₖ s t (k - 2 + 2): ℝ) / nₖ s t (k - 2 + 2)) := by
    apply Filter.eventually_atTop.mpr
    use 2
    intro k k2
    congr
    exact (Nat.sub_eq_iff_eq_add k2).mp rfl

  apply Filter.Tendsto.congr' funrw.symm

  obtain ⟨l, S, T, seq, teq, coprime⟩ := reduce_coprime s t

  have factor0(k: ℕ): (ξ₀ S T)^(δₖ_int S T (k - 2 + 1)) * Res₀ S T ≠ 0 := by
    apply ne_of_gt
    refine mul_pos ?_ (Res₀pos S T)
    apply zpow_pos
    exact ξ₀min S T

  rw [seq, teq]
  conv in (fun k ↦ _) =>
    ext k
    simp only [PNat.mul_coe, Nat.cast_mul]
    rw [← nₖ_homo, ← wₖ_homo]
    rw [(by rfl: k - 2 + 2 = k - 2 + 1 + 1)]
    rw [← Φδₖ, ← Φδₖt _ _ _ (by exact Nat.le_add_left 1 (k - 2))]
    rw [← mul_div_mul_right _ _ (factor0 k)]
    conv in ((Φ S T (δₖ_int S T (k - 2 + 1) - T):ℝ) * _) =>
      conv in ξ₀ S T ^ δₖ_int S T (k - 2 + 1) * Res₀ S T  =>
        rw [← sub_add_cancel (δₖ_int S T (k - 2 + 1)) T]
      rw [zpow_add₀ (ne_of_gt (ξ₀min S T))]
      rw [mul_right_comm, ← mul_assoc]

  push_cast
  rw [pow_mul]
  rw [← ξ₀homo]
  norm_cast
  conv in (nhds _) =>
    rw [← mul_div_cancel_left₀ (ξ₀ S T ^ (T:ℕ)) (by norm_num: (1:ℝ) ≠ 0)]
  have inner: Filter.Tendsto (fun k ↦ δₖ_int S T (k - 2 + 1)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro j
    use j.toNat + 1
    intro k le
    zify at le
    apply Int.le_sub_right_of_add_le at le
    have jk: j ≤ k - 1 := le_trans (Int.self_le_toNat j) le
    apply le_trans jk
    have kle: (k:ℤ) - 1 ≤ (k - 2 + 1: ℕ) := by omega
    apply le_trans kle
    have δₖ_int_growth (k: ℕ): k ≤ δₖ_int S T k := by
      induction k with
      | zero =>
        rify
        rw [δₖ_int_agree]
        rw [δ₀]
      | succ k prev =>
        apply (add_le_add_iff_right 1).mpr at prev
        push_cast
        apply le_trans prev
        apply Int.add_one_le_of_lt
        rify
        rw [δₖ_int_agree, δₖ_int_agree]
        apply δₖ_mono
        exact lt_add_one k
    exact δₖ_int_growth (k - 2 + 1)


  apply Filter.Tendsto.div _ _ (by norm_num)
  · apply Filter.Tendsto.mul
    · have inner': Filter.Tendsto (fun k ↦ δₖ_int S T (k - 2 + 1) - T) Filter.atTop Filter.atTop := by
        have shift: Filter.Tendsto (fun (x:ℤ) ↦ x - T) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_atTop.mpr
          intro j
          use j + T
          exact fun a b ↦ Int.le_sub_right_of_add_le b
        exact Filter.Tendsto.comp shift inner
      exact Filter.Tendsto.comp (ΦAsymptoticℝ' S T coprime) inner'
    · simp only [tendsto_const_nhds_iff]
  · exact Filter.Tendsto.comp (ΦAsymptoticℝ' S T coprime) inner

lemma lerp_dist (a u v g: ℝ) (arange: a ∈ Set.Icc 0 1):
dist ((1 - a) * u + a * v) g ≤ max (dist u g) (dist v g) := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.mp arange
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  rw [(by ring: (1 - a) * u + a * v - g = (1 - a) * (u - g) + a * (v - g))]
  apply le_trans (by apply norm_add_le)
  rw [norm_mul, norm_mul]
  obtain norma: ‖a‖ = a := Real.norm_of_nonneg h0
  obtain norm1a: ‖1 - a‖ = 1 - a:= Real.norm_of_nonneg (sub_nonneg_of_le h1)
  rw [(by rw [norma, norm1a]; ring: max ‖u - g‖ ‖v - g‖ = ‖1 - a‖ * max ‖u - g‖ ‖v - g‖ + ‖a‖ * max ‖u - g‖ ‖v - g‖)]
  gcongr
  · apply le_max_left
  · apply le_max_right


lemma w_Asymtotic_of_wₖ (s t limit: ℝ) [PosReal s] [PosReal t]
(wₖas: Filter.Tendsto (fun k ↦ (wₖ s t k: ℝ) / nₖ s t k) Filter.atTop (nhds limit)):
Filter.Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) Filter.atTop (nhds limit) := by
  let kₙ'proof (n: ℝ): (max n 1) ≥ 1 := by simp only [ge_iff_le, le_sup_right]
  let kₙ' (n: ℝ) := (kₙ_exist s t _ (kₙ'proof n))
  let f (n: ℝ): ℕ × ℝ :=
    let k := (kₙ' n).choose
    (k, (nₖ s t (k + 1) / nₖ s t k - nₖ s t (k + 1) / n) / (nₖ s t (k + 1) / nₖ s t k - 1))
  let g (k: ℕ) (a: ℝ): ℝ :=
    (1 - a) * (wₖ s t k / nₖ s t k) + a * (wₖ s t (k + 1) / nₖ s t (k + 1))

  have funrw: (fun n ↦ (wₗᵢ s t n: ℝ) / n) =ᶠ[Filter.atTop] ↿g ∘ f := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro n n1
    simp only [Function.comp_apply]
    unfold f
    simp only
    unfold Function.HasUncurry.uncurry Function.hasUncurryInduction Function.HasUncurry.uncurry Function.hasUncurryBase
    simp only [id_eq]
    unfold wₗᵢ g
    obtain ⟨k, keq⟩ := kₙ_exist s t n n1
    rw [keq]
    simp only
    have keq': (kₙ' n).choose = k := by
      obtain k' := (kₙ' n).choose_spec
      apply WithBot.coe_eq_coe.mp
      rw [WithBot.some_eq_coe] at k'
      rw [← k', (max_eq_left n1: max n 1 = n), keq]
      rfl
    rw [keq']
    have nkk0: (nₖ s t (k + 1) - nₖ s t k: ℝ) ≠ 0 := by
      apply ne_of_gt
      apply sub_pos_of_lt
      norm_num
      apply nₖ_mono
      exact lt_add_one k
    have nk0: (nₖ (↑↑s) (↑↑t) k: ℝ) ≠ 0 := by norm_cast; apply nₖ_pos
    have nk0': (nₖ (↑↑s) (↑↑t) (k + 1): ℝ) ≠ 0 := by norm_cast; apply nₖ_pos
    have n0: n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) n1)
    field_simp [nkk0, nk0, nk0', n0]
    ring

  apply Filter.Tendsto.congr' funrw.symm

  have flim: Filter.Tendsto f Filter.atTop (Filter.atTop ×ˢ Filter.principal (Set.Icc 0 1)) := by
    unfold f
    apply Filter.Tendsto.prod_mk
    · apply Filter.tendsto_atTop_atTop.mpr
      intro k
      use nₖ s t k
      intro n le
      obtain k' := (kₙ' n).choose_spec
      unfold kₙ at k'

      have mem: k ∈ (kceiled s t (max n 1)).toFinset := by
        unfold kceiled
        simp only [le_sup_iff, Nat.cast_le_one, Set.mem_toFinset, Set.mem_setOf_eq]
        left
        exact le

      obtain lemax := Finset.le_max mem
      rw [k'] at lemax
      exact WithBot.coe_le_coe.mp lemax

    · refine Filter.tendsto_atTop'.mpr ?_
      intro nhds01 nhds01mem
      use 1
      intro n n1
      simp only [Filter.mem_principal] at nhds01mem
      apply Set.mem_of_subset_of_mem nhds01mem
      simp only [Set.mem_Icc]
      have nₖpos: (0:ℝ) < nₖ s t (kₙ' n).choose := by
        norm_num
        apply Nat.zero_lt_of_ne_zero
        apply nₖ_pos
      obtain k' := (kₙ' n).choose_spec
      unfold kₙ at k'

      constructor
      · apply div_nonneg_iff.mpr
        left
        constructor
        · apply sub_nonneg_of_le
          apply div_le_div_of_nonneg_left
          · apply Nat.cast_nonneg'
          · exact nₖpos
          · obtain nₖmem := Finset.mem_of_max k'
            unfold kceiled at nₖmem
            simp only [le_sup_iff, Nat.cast_le_one, Set.mem_toFinset, Set.mem_setOf_eq] at nₖmem
            obtain l|r := nₖmem
            · exact l
            · rify at r
              exact le_trans r n1
        · apply sub_nonneg_of_le
          refine (one_le_div₀ ?_).mpr ?_
          · exact nₖpos
          · simp only [Nat.cast_le]
            apply (nₖ_mono s t).le_iff_le.mpr
            apply Nat.le_add_right
      · refine (div_le_one₀ ?_).mpr ?_
        · apply sub_pos_of_lt
          refine (one_lt_div ?_).mpr ?_
          · exact nₖpos
          · norm_cast
            apply nₖ_mono
            apply lt_add_one
        · apply sub_le_sub_left
          refine (one_le_div ?_).mpr ?_
          · exact lt_of_lt_of_le (by norm_num) n1
          · by_contra lt
            simp only [not_le] at lt
            have mem: (kₙ' n).choose + 1 ∈ (kceiled (↑↑s) (↑↑t) (max n 1)).toFinset := by
              unfold kceiled
              simp only [le_sup_iff, Nat.cast_le_one, Set.mem_toFinset, Set.mem_setOf_eq]
              left
              exact le_of_lt lt
            obtain le_max := Finset.le_max mem
            rw [k'] at le_max
            obtain what := WithBot.coe_le_coe.mp le_max
            simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at what

  have limkk: Filter.Tendsto (· + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro j
    use j
    intro n le
    exact Nat.le_add_right_of_le le
  let limLeft := wₖas
  obtain limRight := Filter.Tendsto.comp limLeft limkk
  obtain limLeft' := Metric.tendsto_atTop.mp limLeft
  obtain limRight' := Metric.tendsto_atTop.mp limRight
  simp only [Function.comp_apply] at limRight'

  have glim: Filter.Tendsto ↿g (Filter.atTop ×ˢ Filter.principal (Set.Icc 0 1)) (nhds (limit)) := by
    apply tendsto_prod_principal_iff.mpr
    refine Metric.tendstoUniformlyOn_iff.mpr ?_
    intro ε εpos
    apply Filter.eventually_atTop.mpr
    obtain ⟨nLeft, nLeftSpec⟩ := limLeft' ε εpos
    obtain ⟨nRight, nRightSpec⟩ := limRight' ε εpos

    use (max nLeft nRight)
    intro k kbound
    simp only [ge_iff_le, sup_le_iff] at kbound
    obtain ⟨leftBound, rightBound⟩ := kbound
    obtain leftLt := nLeftSpec k leftBound
    obtain rightLt := nRightSpec k rightBound
    intro a arange
    obtain maxLt := max_lt leftLt rightLt
    refine lt_of_le_of_lt ?_ maxLt
    unfold g
    rw [dist_comm]
    apply lerp_dist _ _ _ _ arange

  exact Filter.Tendsto.comp glim flim


theorem w_Asymtotic_int (s t: ℕ+):
Filter.Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) Filter.atTop (nhds (ξ₀ s t ^ (t: ℕ))) :=
  w_Asymtotic_of_wₖ s t _ (wₖ_Asymtotic s t)
