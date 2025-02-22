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

--lemma δₖ_int (s t: ℕ+) (k: ℕ): ∃δ: ℤ, δ = δₖ s t k

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
We can now provide integer versions for Jline and Jceiled
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


theorem Φ_inv (s t: ℕ+) (n: ℝ) (n1: n ≥ 1):
ΔceiledByΦ s t n = Set.Iic (dE_int s t n - 1) := by
  have lifted: ((Int.cast '' (ΔceiledByΦ s t n)): Set ℝ) = Int.cast '' Set.Iic (dE_int s t n - 1) := by
    rw [ΔceiledByΦ_agree]
    rw [dE_int_range_agree]
    congr
    exact φ_inv s t n n1
  exact (Set.image_eq_image Int.cast_injective).mp lifted


lemma ΔceiledByΦ_empty (s t: ℕ+) (n1: n < 1): ΔceiledByΦ s t n = ∅ := by
  apply Set.eq_empty_of_forall_not_mem
  intro δ
  unfold ΔceiledByΦ
  simp
  apply lt_of_lt_of_le n1
  unfold Φ
  simp

lemma ΔceiledByΦ_nonempty (s t: ℕ+) (n1: n ≥ 1): (ΔceiledByΦ s t n).Nonempty := by
  apply Set.nonempty_of_mem
  show -1 ∈ ΔceiledByΦ s t n
  unfold ΔceiledByΦ
  simp
  unfold Φ
  unfold Jceiled_int
  unfold Jceiled
  simp
  have setEq: (Λceiled s t (-1)).toFinset = ∅ := by
    simp
    apply Λceiled_neg
    simp
  rw [setEq]
  unfold Jₚ
  simp
  exact n1

lemma Φ_grossBound (s t: ℕ+) (δ: ℤ) (h: δ ≥ -(max s t)):
Φ s t δ ≤ (Real.exp ((max s t) / (min s t))) * (Real.exp ((1: ℝ) / (min s t))) ^ δ := by
  have variant(n: ℤ): n ≥ -(max s t) → ∀δ:ℤ, δ ≥ -(max s t) → δ ≤ n →
  Φ s t δ ≤ (Real.exp ((max s t) / (min s t))) * (Real.exp ((1: ℝ) / (min s t))) ^ δ := by
    apply Int.le_induction
    · intro δ ge le
      have eq: δ = -(max s t) := by exact Int.le_antisymm le ge
      have one: Φ s t δ = 1 := by
        apply Φ_neg
        rw [eq]
        apply neg_neg_of_pos
        simp
      rw [one, eq]
      rw [← Real.rpow_intCast]
      rw [← Real.exp_mul]
      push_cast
      rw [← Real.exp_add]
      simp
      rw [inv_mul_eq_div]
    · intro m mbound prev
      intro δ δlow δhigh
      by_cases δm: δ ≤ m
      · exact prev δ δlow δm
      · simp at δm
        have δeq: δ = m + 1 := by exact Int.le_antisymm δhigh δm
        by_cases δ0: δ < 0
        · have one: Φ s t δ = 1 := by
            apply Φ_neg
            exact δ0
          rw [one]
          obtain prevBound := prev m mbound (le_refl m)
          have mone: Φ s t m = 1 := by
            apply Φ_neg
            exact Int.lt_trans δm δ0
          rw [mone] at prevBound
          rw [δeq]
          apply le_trans prevBound
          apply (mul_le_mul_left ?_).mpr
          · rw [zpow_add₀]
            · nth_rw 1 [← mul_one (Real.exp (1 / min s t) ^ m)]
              apply (mul_le_mul_left ?_).mpr
              · simp
              · refine zpow_pos ?_ m
                apply Real.exp_pos
            · apply Real.exp_ne_zero
          · apply Real.exp_pos
        · simp at δ0
          rw [Φ_rec s t δ δ0]
          push_cast
          have left: (Φ s t (δ - s)) + ↑(Φ s t (δ - t)) ≤ Real.exp ((max s t) / (min s t)) * Real.exp (1 / min s t) ^ (δ - s) + Real.exp ((max s t) / (min s t)) * Real.exp (1 / min s t) ^ (δ - t) := by
            apply add_le_add
            · apply prev (δ - s)
              · apply ge_trans
                · show δ - s ≥ -s
                  simp
                  exact δ0
                · simp
              · rw [δeq]
                simp
                exact NeZero.one_le
            · apply prev (δ - t)
              · apply ge_trans
                · show δ - t ≥ -t
                  simp
                  exact δ0
                · simp
              · rw [δeq]
                simp
                exact NeZero.one_le
          apply le_trans left
          rw [← mul_add]
          apply mul_le_mul
          · simp
          · rw [sub_eq_add_neg, sub_eq_add_neg]
            rw [zpow_add₀, zpow_add₀]
            · rw [← mul_add]
              nth_rw 2 [← mul_one (Real.exp (1 / min s t) ^ δ)]
              apply mul_le_mul
              · apply le_refl
              · rw [← Real.rpow_intCast, ← Real.rpow_intCast]
                rw [← Real.exp_mul, ← Real.exp_mul]
                apply le_trans
                · show _ ≤ Real.exp (-1) + Real.exp (-1)
                  push_cast
                  have bound (x y: ℕ+): Real.exp (1 / min x y * -x) ≤ Real.exp (-1) := by
                    simp
                    refine (one_le_inv_mul₀ ?_).mpr ?_
                    . simp
                    · simp
                  apply add_le_add
                  · apply bound
                  · rw [min_comm]
                    apply bound
                · rw [← two_mul]
                  rw [mul_comm]
                  apply mul_le_of_le_div₀
                  · simp
                  · simp
                  apply le_of_lt
                  apply lt_trans Real.exp_neg_one_lt_d9
                  norm_num
              · apply add_nonneg
                · apply le_of_lt
                  apply zpow_pos
                  apply Real.exp_pos
                · apply le_of_lt
                  apply zpow_pos
                  apply Real.exp_pos
              · apply zpow_nonneg
                apply Real.exp_nonneg
            · apply Real.exp_ne_zero
            · apply Real.exp_ne_zero
          · apply add_nonneg
            · apply le_of_lt
              apply zpow_pos
              apply Real.exp_pos
            · apply le_of_lt
              apply zpow_pos
              apply Real.exp_pos
          · apply Real.exp_nonneg


  apply variant δ h δ h
  exact Int.le_refl δ


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
    · sorry
    · sorry

  right_inv := sorry

lemma pqx_sum [NormedField K] (s t: ℕ) (x: K) (bound: ‖x‖ < Real.exp (min s t)⁻¹) (bound2: ‖x‖ < 1):
HasSum (fun pq ↦ ↑(Jₚ pq) * x ^ (pq.1 * s + pq.2 * t)) (1 - (x ^ s + x ^ t))⁻¹ := by
  apply (Equiv.hasSum_iff Λdecomp).mp
  unfold Λdecomp Function.comp
  simp

  let term := fun (⟨j, c⟩:(j:ℕ) × Finset.range (j + 1)) ↦ ((Jₚ (c, j - c)) * x ^ (c * s + (j - c) * t: ℕ ))
  have binom: ∀(j:ℕ), HasSum (fun (c:Finset.range (j + 1)) ↦ term ⟨j, c⟩ ) ((x ^ s + x ^ t)^j) := by
    intro j
    rw [add_pow]
    let f(c: ℕ) := (x ^ s) ^ c * (x ^ t) ^ (j - c) * (j.choose c)
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

  apply HasSum.of_sigma binom
  · apply hasSum_geometric_of_norm_lt_one
    sorry
  · sorry


lemma ΦX_sum (s t: ℕ+) (x: ℂ) (bound: ‖x‖ < Real.exp (min s t)⁻¹) (bound2: ‖x‖ < 1):
HasSum (fun i:ℕ ↦ Φ s t i * x ^ i) ((1 - x)⁻¹ + (1 - (x ^ (s:ℕ) + x ^ (t:ℕ)))⁻¹ * (1 - x)⁻¹) := by
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
        apply pqx_sum _ _ _ bound bound2
      · unfold g
        apply hasSum_geometric_of_norm_lt_one
        exact bound2
      · apply summable_mul_of_summable_norm
        · unfold f
          simp
          unfold Summable
          use (1 - (‖x‖ ^ (s: ℕ) + ‖x‖ ^ (t: ℕ)))⁻¹
          apply pqx_sum s t ‖x‖
          · simp
            exact bound
          · simp
            exact bound2
        · unfold g
          simp
          exact bound2

    apply HasSum.sigma totalSum
    intro i
    simp
    apply Finset.hasSum



lemma unique_pq (s t: ℕ+) (pq pq': ℕ × ℕ)
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


lemma slopeBound (a b c d s t: ℕ+) (det: a * d = b * c + 1) (left: b * t < d * s) (right: c * s < a * t):
t ≥ c + d := by sorry

lemma Δceiled_inert (a b c d s t: ℕ+) (p q: ℕ)
(det: a * d = b * c + 1) (left: b * t < d * s) (right: c * s < a * t)
(bound: p * (a + b) + q * (c + d) < (a + b) * (c + d)):
Λceiled s t (p * s + q * t) = Λceiled (a + b) (c + d) (p * (a + b) + q * (c + d)) := by
  unfold Λceiled
  ext ⟨p', q'⟩
  simp
  constructor
  · intro h1
    by_contra h2
    simp at h2
    sorry
  · intro h1
    by_contra h2
    sorry
