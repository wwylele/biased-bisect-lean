import BiasedBisect.Basic
import BiasedBisect.Inv

import Mathlib.Data.Complex.ExponentialBounds

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

/-
A main theorem: the generating function Z{Φ}(x) converges to a rational function
The bound here is not sharp, but it should be sufficient for future reasoning over complex plane
-/
theorem ZΦ_sum (s t: ℕ+) (x: ℂ) (bound: ‖x‖ < 2⁻¹):
HasSum (fun i:ℕ ↦ Φ s t i * x ^ i) ((1 - x)⁻¹ + (1 - (x ^ (s:ℕ) + x ^ (t:ℕ)))⁻¹ * (1 - x)⁻¹) := by
  have bound2: ‖x‖ < 1 := by
    apply lt_trans bound
    norm_num

  unfold Φ Jceiled_int Jceiled
  push_cast

  have h: (fun i:ℕ ↦ (1 + ∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p)) * x ^ i)
   = fun i:ℕ ↦ (x ^ i + (∑ p ∈ (Λceiled s t i).toFinset, ↑(Jₚ p)) * x ^ i) := by
     ext i
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



noncomputable
def ξPolynomial(s t: ℕ+) :=
  Polynomial.monomial s (1:ℂ) + Polynomial.monomial t (1:ℂ) + Polynomial.monomial 0 (-1:ℂ)

noncomputable
def ξSet(s t: ℕ+) := (ξPolynomial s t).roots

lemma ΦX_sum_eq(s t: ℕ+) (x: ℂ):
((1 - x)⁻¹ + (1 - (x ^ (s:ℕ) + x ^ (t:ℕ)))⁻¹ * (1 - x)⁻¹) =
(Multiset.map (fun ξ ↦ (1 - x * ξ⁻¹)⁻¹*(1 - ξ)⁻¹*(s * ξ^(s:ℕ) + t * ξ^(t:ℕ))⁻¹) (ξSet s t)).sum := by sorry


lemma unique_pq' (s t: ℕ+) (pq pq': ℕ × ℕ)
(coprime: PNat.Coprime s t) (eq: δₚ s t pq = δₚ s t pq') (bound: δₚ s t pq < s * t): pq = pq' := by
  unfold δₚ at eq
  simp at eq
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul] at eq
  rw [← Nat.cast_add, ← Nat.cast_add] at eq
  apply Nat.cast_inj.mp at eq
  unfold δₚ at bound
  simp at bound
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul] at bound
  rw [← Nat.cast_add] at bound
  apply Nat.cast_lt.mp at bound
  zify at eq
  let p: ℤ := pq.1
  let q: ℤ := pq.2
  let p': ℤ := pq'.1
  let q': ℤ := pq'.2
  let S: ℤ := s
  let T: ℤ := t
  have eq: (p - p') * S = (q' - q) * T := by
    linarith
  have bound: p * S + q * T < S * T := by
    linarith
  have bound': p' * S + q' * T < S * T := by
    linarith
  have qbound: q * T < S * T := by
    apply lt_of_le_of_lt ?_ bound
    apply le_add_of_nonneg_left
    apply mul_nonneg
    · exact Int.ofNat_zero_le pq.1
    · exact Int.ofNat_zero_le s
  have qbound': q' * T < S * T := by
    apply lt_of_le_of_lt ?_ bound'
    apply le_add_of_nonneg_left
    apply mul_nonneg
    · exact Int.ofNat_zero_le pq'.1
    · exact Int.ofNat_zero_le s
  have qboundred: q < S := by
    apply lt_of_mul_lt_mul_right qbound
    exact Int.ofNat_zero_le t
  have qboundred': q' < S := by
    apply lt_of_mul_lt_mul_right qbound'
    exact Int.ofNat_zero_le t
  have cop: IsCoprime S T := by
    apply Nat.isCoprime_iff_coprime.mpr
    exact PNat.coprime_coe.mpr coprime
  have qfactor: S ∣ (q' - q) * T := by
    exact Dvd.intro_left (p - p') eq
  have qfactor2: S ∣ (q' - q) := by
    exact IsCoprime.dvd_of_dvd_mul_right cop qfactor
  rcases exists_eq_mul_left_of_dvd qfactor2 with ⟨k, keq⟩
  have q'eq: q' = k * S + q := by exact Eq.symm (add_eq_of_eq_sub (id (Eq.symm keq)))
  rw [q'eq] at qboundred'
  have kup: k * S < S := by linarith
  have kup': k < 1 := by
    nth_rw 2 [← one_mul S] at kup
    apply lt_of_mul_lt_mul_right kup
    exact Int.ofNat_zero_le s
  have qeq: q = q' - k * S := by exact eq_sub_of_add_eq' (id (Eq.symm q'eq))
  rw [qeq] at qboundred
  have kdown: k * S > -S := by linarith
  have kdown': k > -1 := by
    rw [← neg_one_mul] at kdown
    apply lt_of_mul_lt_mul_right kdown
    exact Int.ofNat_zero_le s
  have k0: k = 0 := by
    apply le_antisymm
    · exact Int.lt_add_one_iff.mp kup'
    · exact kdown'
  rw [k0] at qeq
  simp at qeq
  rw [qeq] at eq
  simp at eq
  have s0: S ≠ 0 := by exact Ne.symm (NeZero.ne' S)
  simp [s0] at eq
  have pp: p = p' := by exact Int.eq_of_sub_eq_zero eq
  refine Prod.ext_iff.mpr ?_
  constructor
  · exact Int.ofNat_inj.mp pp
  · exact Int.ofNat_inj.mp qeq

lemma δₖ_unique_pq (s t: ℕ+) (k: ℕ)
(coprime: PNat.Coprime s t) (kbound: 2 * (k + 1) < (s + 1) * (t + 1)):
∃! pq: ℕ × ℕ, δₖ s t k = δₚ s t pq := by sorry


lemma slopeBound (a b c d s t: ℕ+) (det: a * d = b * c + 1) (left: c * t < d * s) (right: b * s < a * t):
t ≥ b + d := by
  have left': c * t + 1 ≤ d * s := by exact left
  have left'': (c * t + 1) * b ≤ d * s * b := by exact (mul_le_mul_iff_right b).mpr left'
  have left''': (c * t + 1) * b + d ≤ d * s * b + d := by exact add_le_add_right left'' d
  rw [mul_assoc] at left'''
  rw [← mul_add_one] at left'''
  rw [mul_comm s b] at left'''
  have right': b * s + 1 ≤ a * t := by exact right
  have right'': d * (b * s + 1) ≤ d * (a * t) := by exact mul_le_mul_left' right' d
  have all: (c * t + 1) * b + d ≤ d * (a * t) := le_trans left''' right''
  rw [← mul_assoc] at all
  rw [mul_comm d a] at all
  rw [det] at all
  rw [add_mul, add_mul] at all
  have eq: c * t * b = b * c * t := by ring
  rw [eq] at all
  rw [add_assoc] at all
  apply (add_le_add_iff_left (b * c * t)).mp at all
  simp at all
  exact all

theorem Δceiled_inert_half (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ) [PosReal s1] [PosReal t1]
[PosReal s2] [PosReal t2] (det: a * d = b * c + 1)
(left: a * t1 > b * s1) (mid: s1 * t2 > s2 * t1) (right: d * s2 > c * t2)
(pBound: p < b + d)
(p' q': ℕ) (qless: q < q') (pmore: p' < p):
p' * s1 + q' * t1 ≤ p * s1 + q * t1 ↔ p' * s2 + q' * t2 ≤ p * s2 + q * t2 := by
  have rewr (s t: ℝ): p' * s + q' * t ≤ p * s + q * t ↔ (q' - q: ℕ) * t ≤ (p - p': ℕ) * s := by
    rw [Nat.cast_sub (le_of_lt qless)]
    rw [Nat.cast_sub (le_of_lt pmore)]
    rw [sub_mul, sub_mul]
    constructor
    repeat
      intro h
      linarith
  rw [rewr s1 t1]
  rw [rewr s2 t2]
  set dp := p - p'
  set dq := q' -q
  have dpBound: dp < b + d := by
    unfold dp
    exact tsub_lt_of_lt pBound
  have dp0: dp > 0 := by
    unfold dp
    simp
    exact pmore
  have dq0: dq > 0 := by
    unfold dq
    simp
    exact qless
  have dp0': (dp:ℝ) > 0 := by
    exact Nat.cast_pos'.mpr dp0
  have bpos: (b:ℝ) > 0 := by simp
  have dpos: (d:ℝ) > 0 := by simp
  constructor
  · intro le1
    by_contra ge2
    simp at ge2
    nth_rw 2 [mul_comm] at le1
    apply (div_le_div_iff₀ dp0' PosReal.pos).mpr at le1
    nth_rw 1 [mul_comm] at ge2
    apply (div_lt_div_iff₀ PosReal.pos dp0').mpr at ge2
    nth_rw 2 [mul_comm] at left
    apply (div_lt_div_iff₀ PosReal.pos bpos).mpr at left
    nth_rw 1 [mul_comm] at right
    apply (div_lt_div_iff₀ dpos PosReal.pos).mpr at right
    obtain Left: (dq:ℝ) / dp < a / b := lt_of_le_of_lt le1 left
    obtain Right: (c:ℝ) / d < dq / dp := lt_trans right ge2
    apply (div_lt_div_iff₀ dp0' bpos).mp at Left
    apply (div_lt_div_iff₀ dpos dp0').mp at Right
    let S: ℕ+ := ⟨dq, dq0⟩
    let T: ℕ+ := ⟨dp, dp0⟩
    have dqS: dq = S := by trivial
    have dpT: dp = T := by trivial
    rw [dqS, dpT] at Left
    rw [dqS, dpT] at Right
    norm_cast at Left
    norm_cast at Right
    rw [mul_comm] at Left
    nth_rw 2 [mul_comm] at Right
    have anotherBound := slopeBound a b c d S T det Right Left
    rw [dpT] at dpBound
    norm_cast at dpBound
    obtain what := lt_of_lt_of_le dpBound anotherBound
    simp at what
  · intro le2
    nth_rw 2 [mul_comm]
    apply (div_le_div_iff₀ dp0' PosReal.pos).mp
    nth_rw 2 [mul_comm] at le2
    apply (div_le_div_iff₀ dp0' PosReal.pos).mpr at le2
    apply (div_lt_div_iff₀ PosReal.pos PosReal.pos).mpr at mid
    apply le_of_lt
    exact lt_of_le_of_lt le2 mid



lemma Δceiled_inert (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left: a * t1 > b * s1) (mid: s1 * t2 > s2 * t1) (right: d * s2 > c * t2)
(pBound: p < b + d) (qBound: q < a + c):
Λceiled s1 t1 (p * s1 + q * t1) = Λceiled s2 t2 (p * s2 + q * t2) := by
  unfold Λceiled
  ext ⟨p', q'⟩
  simp
  by_cases pless: p' ≤ p
  · by_cases qless: q' ≤ q
    · apply iff_of_true
      repeat
        apply add_le_add
        repeat
          apply (mul_le_mul_right ?_).mpr
          · simp
            trivial
          · exact PosReal.pos
    · simp at qless
      rcases lt_or_eq_of_le pless with pmore|peq
      · exact Δceiled_inert_half a b c d s1 t1 s2 t2 p q det left mid right pBound p' q' qless pmore
      · rw [peq]
        simp
        apply iff_of_false
        repeat
          simp
          apply (mul_lt_mul_right ?_).mpr
          · simp
            trivial
          · exact PosReal.pos
  · simp at pless
    by_cases qmore: q' ≥ q
    · apply iff_of_false
      repeat
        simp
        apply add_lt_add_of_lt_of_le
        · apply (mul_lt_mul_right ?_).mpr
          · simp
            trivial
          · exact PosReal.pos
        · apply (mul_le_mul_right ?_).mpr
          · simp
            trivial
          · exact PosReal.pos
    · simp at qmore
      have det': d * a = c * b + 1 := by
        nth_rw 1 [mul_comm]
        nth_rw 2 [mul_comm]
        exact det
      have mid': t2 * s1 > t1 * s2 := by
        nth_rw 1 [mul_comm]
        nth_rw 2 [mul_comm]
        exact mid
      rw [add_comm] at qBound
      nth_rw 1 [add_comm]
      nth_rw 2 [add_comm]
      nth_rw 3 [add_comm]
      nth_rw 4 [add_comm]
      symm
      exact Δceiled_inert_half d c b a t2 s2 t1 s1 q p det' right mid' left qBound q' p' pless qmore

lemma Δceiled_inert' (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(pBound: p < b + d) (qBound: q < a + c):
Λceiled s1 t1 (p * s1 + q * t1) = Λceiled s2 t2 (p * s2 + q * t2) := by
  rcases lt_trichotomy (s1 * t2) (s2 * t1) with t|eq|gt
  · exact Eq.symm (Δceiled_inert a b c d s2 t2 s1 t1 p q det left2 t right1 pBound qBound)
  · let l := s2 / s1
    have sl: s2 = l * s1 := by
      unfold l
      rw [div_mul_cancel₀]
      apply ne_of_gt
      exact PosReal.pos
    have tl: t2 = l * t1 := by
      unfold l
      rw [← mul_div_right_comm]
      rw [← eq]
      rw [mul_div_right_comm]
      rw [div_self (ne_of_gt PosReal.pos)]
      simp
    let lpos: PosReal l := {
      pos := by
        unfold l
        apply (div_pos_iff_of_pos_left PosReal.pos).mpr
        exact PosReal.pos
    }
    rw [sl, tl]
    rw [← mul_assoc, ← mul_assoc]
    rw [mul_comm _ l, mul_comm _ l]
    rw [mul_assoc, mul_assoc]
    rw [← mul_add]
    apply Λceiled_homo s1 t1 (↑p * s1 + ↑q * t1) l
  · exact Δceiled_inert a b c d s1 t1 s2 t2 p q det left1 gt right2 pBound qBound

lemma Δceiled_lt_inert(a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p1 q1 p2 q2: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(p1Bound: p1 < b + d) (q1Bound: q1 < a + c)
(p2Bound: p2 < b + d) (q2Bound: q2 < a + c):
δₚ s1 t1 (p1, q1) < δₚ s1 t1 (p2, q2) → δₚ s2 t2 (p1, q1) < δₚ s2 t2 (p2, q2) := by
  by_contra rel
  simp at rel
  rcases rel with ⟨r1, r2⟩
  have c1: Λceiled s1 t1 (δₚ s1 t1 (p1, q1)) ⊆ Λceiled s1 t1 (δₚ s1 t1 (p2, q2)) := by
    unfold Λceiled
    simp
    intro p q mem
    apply le_of_lt
    apply lt_of_le_of_lt mem r1
  have c2: Λceiled s2 t2 (δₚ s2 t2 (p1, q1)) ⊇ Λceiled s2 t2 (δₚ s2 t2 (p2, q2)) := by
    unfold Λceiled
    simp
    intro p q mem
    apply le_trans mem r2
  have left: Λceiled s1 t1 (δₚ s1 t1 (p1, q1)) = Λceiled s2 t2 (δₚ s2 t2 (p1, q1)) := by
    unfold δₚ
    refine Δceiled_inert' a b c d s1 t1 s2 t2 p1 q1 det left1 right1 left2 right2 p1Bound q1Bound
  have right: Λceiled s1 t1 (δₚ s1 t1 (p2, q2)) = Λceiled s2 t2 (δₚ s2 t2 (p2, q2)) := by
    unfold δₚ
    refine Δceiled_inert' a b c d s1 t1 s2 t2 p2 q2 det left1 right1 left2 right2 p2Bound q2Bound
  rw [← left, ← right] at c2
  have eq: Λceiled s1 t1 (δₚ s1 t1 (p1, q1)) = Λceiled s1 t1 (δₚ s1 t1 (p2, q2)) := by
    exact Set.Subset.antisymm c1 c2
  have pq2: (p2, q2) ∈ Λceiled s1 t1 (δₚ s1 t1 (p2, q2)) := by
    unfold Λceiled δₚ
    simp
  rw [← eq] at pq2
  unfold Λceiled at pq2
  simp at pq2
  rw [← δₚ] at pq2
  obtain what := lt_of_le_of_lt pq2 r1
  simp at what

lemma unique_pq (a b c d: ℕ+) (s t: ℝ) (pq pq': ℕ × ℕ)
[PosReal s] [PosReal t]
(det: a * d = b * c + 1)
(left: a * t > b * s) (right: d * s > c * t)
(eq: δₚ s t pq = δₚ s t pq') (bound: δₚ s t pq < (a + c) * (b + d)): pq = pq' := by sorry

lemma δₖ_inert (a b c d: ℕ+) (s1 t1 s2 t2: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(kbound: ℕ) (pqₖ: ℕ → ℕ × ℕ)
(pqMatch1: ∀ k ≤ kbound, δₖ s1 t1 k = δₚ s1 t1 (pqₖ k))
(pqBound: ∀ k ≤ kbound, (pqₖ k).1 * (a + c) + (pqₖ k).2 * (b + d) < (a + c) * (b + d))
: ∀ k ≤ kbound, δₖ s2 t2 k = δₚ s2 t2 (pqₖ k) := by
  intro k kle
  induction k with
  | zero =>
    rw [δ₀]
    obtain at1 := pqMatch1 0 kle
    rw [δ₀] at at1
    unfold δₚ at at1
    simp at at1
    obtain at1 := ge_of_eq at1
    have left: (pqₖ 0).1 * s1 ≥ 0 := by
      apply mul_nonneg
      · simp
      · exact le_of_lt (PosReal.pos)
    have right: (pqₖ 0).2 * t1 ≥ 0 := by
      apply mul_nonneg
      · simp
      · exact le_of_lt (PosReal.pos)
    obtain ⟨shuts, shutt⟩ := sum_to_zero _ _ left right at1
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero (ne_of_gt PosReal.pos) at shuts
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero (ne_of_gt PosReal.pos) at shutt
    unfold δₚ
    simp
    rw [shuts, shutt]
    simp
  | succ k prev =>
    have kleprev: k ≤ kbound := by exact Nat.le_of_succ_le kle
    obtain prev := prev kleprev
    obtain pqBoundk := pqBound k kleprev
    have pBound: (pqₖ k).1 < b + d := by
      have pqac: (pqₖ k).2 * (b + d) ≥ 0 := by
        apply mul_nonneg
        · simp
        · simp
      obtain pqBoundk' := lt_of_add_lt_of_nonneg_left pqBoundk pqac
      rw [mul_comm] at pqBoundk'
      apply lt_of_mul_lt_mul_left pqBoundk'
      simp
    have qBound: (pqₖ k).2 < a + c := by
      have pqac: (pqₖ k).1 * (a + c) ≥ 0 := by
        apply mul_nonneg
        · simp
        · simp
      obtain pqBoundk' := lt_of_add_lt_of_nonneg_right pqBoundk pqac
      apply lt_of_mul_lt_mul_right pqBoundk'
      simp
    obtain pqBoundkp := pqBound (k + 1) kle
    have pBound': (pqₖ (k + 1)).1 < b + d := by
      have pqac: (pqₖ (k + 1)).2 * (b + d) ≥ 0 := by
        apply mul_nonneg
        · simp
        · simp
      obtain pqBoundk' := lt_of_add_lt_of_nonneg_left pqBoundkp pqac
      rw [mul_comm] at pqBoundk'
      apply lt_of_mul_lt_mul_left pqBoundk'
      simp
    have qBound': (pqₖ (k + 1)).2 < a + c := by
      have pqac: (pqₖ (k + 1)).1 * (a + c) ≥ 0 := by
        apply mul_nonneg
        · simp
        · simp
      obtain pqBoundk' := lt_of_add_lt_of_nonneg_right pqBoundkp pqac
      apply lt_of_mul_lt_mul_right pqBoundk'
      simp
    let acpos: PosReal (a + c) := {
      pos := by apply add_pos_of_nonneg_of_pos; simp; simp
    }
    let bdpos: PosReal (b + d) := {
      pos := by apply add_pos_of_nonneg_of_pos; simp; simp
    }
    have abcd1: (a: ℝ) * (b + d) > b * (a + c) := by
      norm_cast
      rw [mul_add, mul_add]
      rw [det]
      rw [mul_comm]
      rw [← add_assoc]
      exact PNat.lt_add_right (a * b + b * c) 1
    have abcd2: (d: ℝ) * (a + c) > c * (b + d) := by
      norm_cast
      rw [mul_add, mul_add]
      rw [mul_comm d a]
      rw [det]
      rw [mul_comm c b]
      rw [mul_comm c d]
      rw [add_assoc]
      rw [add_comm 1]
      rw [← add_assoc]
      exact PNat.lt_add_right (b * c + d * c) 1
    have pqBound's2: δₚ s2 t2 (pqₖ (k + 1)) < s2 * (b + d) := by
      by_contra ge
      simp at ge
      have mem: ((b + d: ℕ), 0) ∈ Λceiled s2 t2 ((pqₖ (k + 1)).1 * s2 + (pqₖ (k + 1)).2 * t2) := by
        unfold Λceiled
        simp
        rw [mul_comm]
        exact ge
      rw [Δceiled_inert' a b c d s2 t2 (a + c) (b + d) (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
        det left2 right2 abcd1 abcd2 pBound' qBound' ] at mem
      unfold Λceiled at mem
      simp at mem
      obtain another := pqBound (k + 1) kle
      rify at another
      obtain what := lt_of_le_of_lt mem another
      rw [mul_comm] at what
      simp at what
    have pqBound't2: δₚ s2 t2 (pqₖ (k + 1)) < t2 * (a + c) := by
      by_contra ge
      simp at ge
      have mem: (0, (a + c: ℕ)) ∈ Λceiled s2 t2 ((pqₖ (k + 1)).1 * s2 + (pqₖ (k + 1)).2 * t2) := by
        unfold Λceiled
        simp
        rw [mul_comm]
        exact ge
      rw [Δceiled_inert' a b c d s2 t2 (a + c) (b + d) (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
        det left2 right2 abcd1 abcd2 pBound' qBound' ] at mem
      unfold Λceiled at mem
      simp at mem
      obtain another := pqBound (k + 1) kle
      rify at another
      obtain what := lt_of_le_of_lt mem another
      rw [mul_comm] at what
      simp at what
    apply le_antisymm
    · have next: δₚ s1 t1 (pqₖ (k + 1)) > δₚ s1 t1 (pqₖ k) := by
        rw [← pqMatch1 (k + 1) kle]
        rw [← pqMatch1 k kleprev]
        rw [δₖ]
        apply δnext_larger
      have preserveNext: δₚ s2 t2 (pqₖ (k + 1)) > δₚ s2 t2 (pqₖ k) := by
        apply (Δceiled_lt_inert a b c d s1 t1 s2 t2 (pqₖ k).1 (pqₖ k).2 (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
          det left1 right1 left2 right2 pBound qBound pBound' qBound' next)

      have preserveNext': δₚ s2 t2 (pqₖ (k + 1)) ∈ Δfloored s2 t2 (δₖ s2 t2 k) := by
        rw [prev]
        unfold Δfloored
        simp
        constructor
        · unfold δₚ Δ is_δ
          simp
        · exact preserveNext
      unfold δₖ δnext
      exact
        Set.IsWF.min_le (Δfloored_WF s2 t2 (δₖ s2 t2 k)) (Δfloored_nonempty s2 t2 (δₖ s2 t2 k))
          preserveNext'
    · by_contra lt
      simp at lt
      obtain δₖ2FromPq := δₖ_in_Δ s2 t2 (k + 1)
      unfold Δ is_δ at δₖ2FromPq
      simp at δₖ2FromPq
      rcases δₖ2FromPq with ⟨p', ⟨q', δₖ2eq⟩⟩
      rw [← δₖ2eq] at lt
      obtain gt := δnext_larger s2 t2 (δₖ s2 t2 k)
      rw [← δₖ] at gt
      rw [← δₖ2eq] at gt
      rw [prev] at gt
      obtain pq's2 := lt_trans lt pqBound's2
      obtain pq't2 := lt_trans lt pqBound't2
      have p's2: (p':ℝ) * s2 < s2 * (↑↑b + ↑↑d) := by
        apply lt_of_add_lt_of_nonneg_left pq's2
        apply mul_nonneg
        · simp
        · exact le_of_lt (PosReal.pos)
      have q't2: (q':ℝ) * t2 < t2 * (↑↑a + ↑↑c) := by
        apply lt_of_add_lt_of_nonneg_right pq't2
        apply mul_nonneg
        · simp
        · exact le_of_lt (PosReal.pos)
      have p'bd: p' < b + d := by
        rw [mul_comm] at p's2
        rify
        apply lt_of_mul_lt_mul_left p's2 (le_of_lt (PosReal.pos))
      have q'ac: q' < a + c := by
        rw [mul_comm] at q't2
        rify
        apply lt_of_mul_lt_mul_left q't2 (le_of_lt (PosReal.pos))
      have preserveLt: p' * s1 + q' * t1 < δₚ s1 t1 (pqₖ (k + 1)) := by
        have eq: p' * s1 + q' * t1 = δₚ s1 t1 (p', q') := by unfold δₚ; simp
        have eq2: p' * s2 + q' * t2 = δₚ s2 t2 (p', q') := by unfold δₚ; simp
        rw [eq]
        apply (Δceiled_lt_inert a b c d s2 t2 s1 t1 p' q' (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
          det left2 right2 left1 right1 p'bd q'ac pBound' qBound' ?_)
        rw [eq2] at lt
        exact lt
      have preserveGt: p' * s1 + q' * t1 > δₚ s1 t1 (pqₖ k) := by
        have eq: p' * s1 + q' * t1 = δₚ s1 t1 (p', q') := by unfold δₚ; simp
        have eq2: p' * s2 + q' * t2 = δₚ s2 t2 (p', q') := by unfold δₚ; simp
        rw [eq]
        apply (Δceiled_lt_inert a b c d s2 t2 s1 t1 (pqₖ k).1 (pqₖ k).2 p' q'
          det left2 right2 left1 right1 pBound qBound p'bd q'ac ?_)
        rw [eq2] at gt
        exact gt
      rw [← pqMatch1 (k + 1) kle] at preserveLt
      unfold δₖ at preserveLt
      rw [← pqMatch1 k kleprev] at preserveGt
      have inFloor: p' * s1 + q' * t1 ∈ Δfloored s1 t1 (δₖ s1 t1 k) := by
        unfold Δfloored Δ is_δ
        simp
        exact preserveGt
      have inFloor': p' * s1 + q' * t1 ≥ δnext s1 t1 (δₖ s1 t1 k) := by
        unfold δnext
        exact
          Set.IsWF.min_le (Δfloored_WF s1 t1 (δₖ s1 t1 k)) (Δfloored_nonempty s1 t1 (δₖ s1 t1 k))
            inFloor
      have what := gt_of_ge_of_gt inFloor' preserveLt
      simp at what

def FintypeIcc (L: ℕ): Type := Set.Icc 0 L


def Λrectangle (a b c d: ℕ+) :=
  (Finset.range (b + d + 1)) ×ˢ (Finset.range (a + c + 1))

instance Λrectangle_fintype (a b c d: ℕ+): Fintype (Λrectangle a b c d) := by
  unfold Λrectangle
  apply Finset.fintypeCoeSort

lemma Λrectangle_card (a b c d: ℕ+): Fintype.card (Λrectangle a b c d) = (b + d + 1) * (a + c + 1) := by
  unfold Λrectangle
  simp

def Λtriangle (a b c d: ℕ+) := {pq: ℕ × ℕ | pq.1 * (a + c) + pq.2 * (b + d) < (a + c) * (b + d)}

lemma ΛtriangleSubset (a b c d: ℕ+): Λtriangle a b c d ⊆ Λrectangle a b c d := by
  unfold Λtriangle Λrectangle
  simp
  rintro ⟨p, q⟩
  intro mem
  simp at mem
  constructor
  · simp
    refine lt_add_of_lt_of_pos ?_ Nat.one_pos
    have lt: p * (a + c) < (a + c) * (b + d) := by
      apply lt_of_add_lt_of_nonneg_left mem (mul_nonneg ?_ ?_)
      · simp
      · simp
    rw [mul_comm] at lt
    apply Nat.lt_of_mul_lt_mul_left lt
  · refine lt_add_of_lt_of_pos ?_ Nat.one_pos
    have lt: q * (b + d) < (a + c) * (b + d) := by
      apply lt_of_add_lt_of_nonneg_right mem (mul_nonneg ?_ ?_)
      · simp
      · simp
    apply Nat.lt_of_mul_lt_mul_right lt

noncomputable
instance ΛtriangleDecidable (a b c d: ℕ+): DecidablePred fun x ↦ x ∈ Λtriangle a b c d := by
  apply Classical.decPred

noncomputable
instance ΛtriangleFintype (a b c d: ℕ+): Fintype (Λtriangle a b c d) := by
  refine Set.fintypeSubset _ (ΛtriangleSubset a b c d)

def ΛtriangleUpper (a b c d: ℕ+) := {pq: ℕ × ℕ | pq.1 * (a + c) + pq.2 * (b + d) > (a + c) * (b + d)} ∩ (Λrectangle a b c d)

def ΛtriangleUpperSubset (a b c d: ℕ+): ΛtriangleUpper a b c d ⊆ Λrectangle a b c d := by
  unfold ΛtriangleUpper
  exact Set.inter_subset_right

noncomputable
instance ΛtriangleUpperDecidable (a b c d: ℕ+): DecidablePred fun x ↦ x ∈ ΛtriangleUpper a b c d := by
  apply Classical.decPred

noncomputable
instance ΛtriangleUpperFintype (a b c d: ℕ+): Fintype (ΛtriangleUpper a b c d) := by
  refine Set.fintypeSubset _ (ΛtriangleUpperSubset a b c d)

lemma ΛtriangeEquivToFun (a b c d: ℕ+) (h: (p, q) ∈ Λtriangle a b c d):
  (b + d - p, a + c - q) ∈ ΛtriangleUpper a b c d := by sorry

lemma ΛtriangeEquivInvFun (a b c d: ℕ+) (h: (p, q) ∈ ΛtriangleUpper a b c d):
  (b + d - p, a + c - q) ∈ Λtriangle a b c d := by sorry


lemma ΛtriangleCardEq (a b c d: ℕ+): (Λtriangle a b c d).toFinset.card = (ΛtriangleUpper a b c d).toFinset.card := by
  apply Finset.card_bijective (fun ⟨p, q⟩ ↦ ⟨b + d - p, a + c - q⟩ )
  · sorry
  · rintro ⟨p, q⟩
    unfold Λtriangle ΛtriangleUpper Λrectangle
    simp
    sorry
  /-use fun ⟨⟨p, q⟩, h⟩ ↦ ⟨⟨b + d - p, a + c - q ⟩ , ΛtriangeEquivToFun a b c d h⟩
  use fun ⟨⟨p, q⟩, h⟩ ↦ ⟨⟨b + d - p, a + c - q ⟩ , ΛtriangeEquivInvFun a b c d h⟩
  · unfold Function.LeftInverse Λtriangle
    simp
    intro p q mem
    constructor
    · sorry
    · sorry
  · unfold Function.RightInverse Function.LeftInverse ΛtriangleUpper Λrectangle
    simp
    intro p q mem pbound qbound
    constructor
    · sorry
    · sorry-/

def ΛrectangleCut (a b c d: ℕ+) := (Λrectangle a b c d \ {((b:ℕ) + d, 0)}) \ {(0, (a:ℕ) + c)}

instance ΛrectangleCutFintype (a b c d: ℕ+): Fintype (ΛrectangleCut a b c d) := by
  unfold ΛrectangleCut
  apply Finset.fintypeCoeSort

lemma ΛrectangleCutCard (a b c d: ℕ+): Fintype.card (ΛrectangleCut a b c d) = (b + d + 1) * (a + c + 1) - 2 := by
  have two: 2 = 1 + 1 := by simp
  rw [two]
  rw [← Nat.sub_sub]
  unfold ΛrectangleCut
  simp
  rw [Finset.card_sdiff]
  · rw [Finset.card_sdiff]
    · congr
      rw [← Λrectangle_card]
      exact Eq.symm (Fintype.card_coe (Λrectangle a b c d))
    · unfold Λrectangle
      simp
  · unfold Λrectangle
    simp

lemma ΛrectangleDecompose (a b c d: ℕ+) (det: a * d = b * c + 1):
ΛrectangleCut a b c d = (Λtriangle a b c d).toFinset ∪ (ΛtriangleUpper a b c d).toFinset := by
  unfold ΛrectangleCut Λtriangle ΛtriangleUpper Λrectangle
  ext ⟨p, q⟩
  simp
  constructor
  · rintro ⟨⟨⟨pbound,qbound⟩, pcut⟩, qcut⟩
    rw [or_iff_not_imp_left]
    intro notlower
    simp at notlower
    constructor
    · apply lt_of_le_of_ne notlower
      sorry
    · constructor
      · exact pbound
      · exact qbound
  · rintro h
    rcases h with lower|upper
    · constructor
      · constructor
        · constructor
          · refine lt_add_of_lt_of_pos ?_ Nat.one_pos
            have lt: p * (a + c) < (a + c) * (b + d) := by
              apply lt_of_add_lt_of_nonneg_left lower (mul_nonneg ?_ ?_)
              · simp
              · simp
            rw [mul_comm] at lt
            apply Nat.lt_of_mul_lt_mul_left lt
          · refine lt_add_of_lt_of_pos ?_ Nat.one_pos
            have lt: q * (b + d) < (a + c) * (b + d) := by
              apply lt_of_add_lt_of_nonneg_right lower (mul_nonneg ?_ ?_)
              · simp
              · simp
            apply Nat.lt_of_mul_lt_mul_right lt
        · intro pcut
          by_contra q0
          rw [pcut, q0] at lower
          rw [mul_comm] at lower
          simp at lower
      · intro qcut
        by_contra p0
        rw [qcut, p0] at lower
        simp at lower
    · rcases upper with ⟨upper, ⟨pbound, qbound⟩⟩
      constructor
      · constructor
        · constructor
          · exact pbound
          · exact qbound
        · intro pcut
          by_contra q0
          rw [pcut, q0] at upper
          rw [mul_comm] at upper
          simp at upper
      · intro qcut
        by_contra p0
        rw [qcut, p0] at upper
        simp at upper

lemma ΛrectangleDisjoint (a b c d: ℕ+): (Λtriangle a b c d).toFinset ∩ (ΛtriangleUpper a b c d).toFinset = ∅ := by
  unfold Λtriangle ΛtriangleUpper
  ext pq
  simp
  intro mem
  rw [imp_iff_not_or]
  left
  simp
  apply le_of_lt mem

lemma ΛtriangleCard (a b c d: ℕ+) (det: a * d = b * c + 1):
(Λtriangle a b c d).toFinset.card = (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) := by
  obtain reccard := ΛrectangleCutCard a b c d
  simp at reccard
  rw [ΛrectangleDecompose a b c d det] at reccard
  rw [Finset.card_union] at reccard
  rw [ΛrectangleDisjoint] at reccard
  rw [← ΛtriangleCardEq] at reccard
  rw [← two_mul] at reccard
  rw [mul_comm]
  rw [← reccard]
  simp


lemma nₖ_inert(a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (k: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t1 > b * s1) (right2: d * s1 > c * t1)
(kbound: 2 * (k + 1) < (a + c + 1) * (b + d + 1)):
nₖ s1 t1 k = nₖ s2 t2 k := by
  sorry

/-

def Λtriangle (a b c d: ℕ+) (det: a * d = b * c + 1) :=
{pq: ℕ × ℕ // pq.1 * (a + b) + pq.2 * (c + d) ≤ (a + b) * (c + d)}

instance Λtriangle_Finite (a b c d: ℕ+) (det: a * d = b * c + 1):
Finite (Λtriangle a b c d det) := by
  sorry

instance Λtriangle_Fintype (a b c d: ℕ+) (det: a * d = b * c + 1):
Fintype (Λtriangle a b c d det) := by
  sorry

def ΛLEbyST (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t)
(pq: Λtriangle a b c d det) (pq': Λtriangle a b c d det)
:= (δₚ s t pq.val) ≤ (δₚ s t pq'.val)

noncomputable
instance ΛLEbyST_DecidableRel (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t):
DecidableRel (ΛLEbyST a b c d det s t left right) := by
  exact Classical.decRel (ΛLEbyST a b c d det s t left right)

instance ΛLEbyST_IsTrans (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t):
IsTrans (Λtriangle a b c d det) (ΛLEbyST a b c d det s t left right) where
  trans := by
    unfold ΛLEbyST
    intro a b c ab bc
    apply le_trans ab bc

instance ΛLEbyST_IsAntisymm (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t):
IsAntisymm (Λtriangle a b c d det) (ΛLEbyST a b c d det s t left right) where
  antisymm := by
    unfold ΛLEbyST
    intro a b ab ba
    sorry

instance ΛLEbyST_IsTotal (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t):
IsTotal (Λtriangle a b c d det) (ΛLEbyST a b c d det s t left right) where
  total := by sorry

noncomputable
def ΛList (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t) :=
Finset.sort (ΛLEbyST a b c d det s t left right) Finset.univ

lemma ΛListLenth (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t):
(ΛList a b c d det s t left right).length = (a + c + 1) * (b + d + 1) / 2 - 1 := by sorry


lemma δₖFromList (a b c d: ℕ+) (det: a * d = b * c + 1)
(s t: ℝ) (left: a * t > b * s) (right: d * s > c * t)
[PosReal s] [PosReal t]:
List.map (δₖ s t) (List.range ((a + c + 1) * (b + d + 1) / 2 - 2)) = List.map (fun pq ↦ δₚ s t pq.val) (ΛList a b c d det s t left right)  := by
  refine List.map_eq_iff.mpr ?_


lemma ΛList_inert (a b c d: ℕ+) (det: a * d = b * c + 1)
(s1 t1: ℝ) (left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(s2 t2: ℝ) (left2: a * t2 > b * s2) (right2: d * s2 > c * t2):
ΛList a b c d det s1 t1 left1 right1 = ΛList a b c d det s2 t2 left2 right2 := by sorry
-/
