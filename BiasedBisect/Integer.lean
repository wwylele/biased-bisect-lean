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
