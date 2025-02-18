import BiasedBisect.Basic
import BiasedBisect.Inv

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

--noncomputable
--def δₖ_int (s t: ℕ+): ℕ → ℤ
--| 0 => 0
--| Nat.succ n =>
--  let ⟨δ, p⟩ := δnext_int s t (δₖ_int s t n)
--  δ

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

--noncomputable
--def dE_int (s t: ℕ+): ℝ → ℤ := fun n ↦
--  match kₙ s t n with
--  | some k => δₖ s t k
--  | none => 0

/-
Let's introduce a new sequence φ(δ) that's simply Jceiled_int shifted by 1.

We will soon see that this is the sequence that uniquely satisfies the following conditions:
 - φ(< 0) = 1
 - φ(δ ≥ 0) = φ(δ - s) + φ(δ - t)
As an example, for s = 1 and t = 2, this is the Fibonacci sequence (shifted in index)
-/
noncomputable
def φ (s t: ℕ+) (δ: ℤ) := 1 + Jceiled_int s t δ

lemma φ_agree (s t: ℕ+) (δ: ℤ): φ s t δ = φ s t δ := by
  unfold φ
  unfold Jceiled_int
  unfold φ
  rfl

theorem φ_neg (s t: ℕ+) (δ: ℤ) (dpos: δ < 0): φ s t δ = 1 := by
  unfold φ
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

theorem φ_rec (s t: ℕ+) (δ: ℤ) (dpos: δ ≥ 0):
φ s t δ = φ s t (δ - s) + φ s t (δ - t) := by
  have alt: 0 ≤ δ → φ s t δ = φ s t (δ - s) + φ s t (δ - t) := by
    apply Int.le_induction
    · simp
      have sneg: -(s:ℤ) < 0 := by simp
      have tneg: -(t:ℤ) < 0 := by simp
      rw [φ_neg s t (-(s:ℤ)) sneg]
      rw [φ_neg s t (-(t:ℤ)) tneg]
      unfold φ
      have zero: 0 = (-1) + 1 := by simp
      rw [zero]
      rw [← (Jceiled_int_accum s t (-1))]
      unfold Jline_int
      simp
      rw [Jline₀]
      nth_rw 2 [add_comm]
      rw [← φ]
      rw [φ_neg]
      simp
    · unfold φ
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

def ΔceiledByφ (s t: ℕ+) (n: ℝ) := {δ: ℤ | φ s t δ ≤ n}

--theorem φ_inv (s t: ℕ+) (n: ℝ) (n1: n ≥ 1):
--ΔceiledByφ s t n = Set.Iic (dE s t n - 1) := by

lemma ΔceiledByφ_empty (s t: ℕ+) (n1: n < 1): ΔceiledByφ s t n = ∅ := by
  apply Set.eq_empty_of_forall_not_mem
  intro δ
  unfold ΔceiledByφ
  simp
  apply lt_of_lt_of_le n1
  unfold φ
  simp

lemma ΔceiledByφ_nonempty (s t: ℕ+) (n1: n ≥ 1): (ΔceiledByφ s t n).Nonempty := by
  apply Set.nonempty_of_mem
  show -1 ∈ ΔceiledByφ s t n
  unfold ΔceiledByφ
  simp
  unfold φ
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


/-
noncomputable
def dE_int (s t: ℕ+) := fun n ↦
  match (ΔceiledByφ s t (n + 1)).toFinset.max with
  | some δ => δ
  | none => 0

theorem dE_int_agree (s t: ℕ+) (n: ℝ): dE s t n = dE_int s t n := by sorry
-/
