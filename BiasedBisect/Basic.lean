import Mathlib.Tactic
import Mathlib.Util.Delaborators

/-

In this file, we will try to construct a solution to the following problem:

A software has (n+1) versions v_0,v_1,...,v_n, and n changes in between.
It is discovered one of the change broke a feature of the software, but we don't know
which one did. We only know v_0 is fine and v_n is broken. How do we quickly find the broken
change?

Well, the answer to this classic question is to do binary search. But what if the cost of
performing a software test depends on the outcome? For example, a broken software will result
in a system crash and requires much longer time to reboot. Which version should we test first,
and next?

Let s and t be the cost of a successful and a failed test. The expected cost F(n) is

F(1) = 0
F(n) = min (1 ≤ w ≤ n - 1) {(w / n) * (F(w) + t) + ((n - w) / n) * (F(n - w) + s)}

where w is the first version to test. To simplify a little bit, we normalize F(n) with

E(n) = n * F(n)

where E(n) satisfies

E(1) = 0
E(n) = min (1 ≤ w ≤ n - 1) {F(w) + F(n - w) + w * t + (n - w) * s}

-/



/- some random util theorems -/
theorem sum_to_zero (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (h : a + b ≤ 0) : a = 0 ∧ b = 0 := by
  constructor
  · -- Prove `a = 0`
    apply le_antisymm
    · -- Show `a ≤ 0`
      calc
        a ≤ a + b := by exact le_add_of_nonneg_right hb
        _ ≤ 0 := h
    · -- Show `0 ≤ a`
      exact ha
  · -- Prove `b = 0`
    apply le_antisymm
    · -- Show `b ≤ 0`
      calc
        b ≤ a + b := by exact le_add_of_nonneg_left ha
        _ ≤ 0 := h
    · -- Show `0 ≤ b`
      exact hb

theorem finset_max_eq [LinearOrder α] (s: Finset α) {m : α} (mem: m ∈ s) (other: ∀n ∈ s, n ≤ m)
  : s.max = WithBot.some m :=
by
  apply le_antisymm
  · simpa using other
  · exact Finset.le_max mem



class PosReal (x : ℝ) : Prop where
  pos : x > 0

/-
Throughout the file, we will use a pair of real positive parameters s and t.

We start with the lattic Λ = ℕ × ℕ and assign each lattice point (p, q) a value
δ = ps + qt. Visually, this is drawing a line passing the point with a
fixed slope (namely -s/t) and measures how far away it is from the origin.

All possible δ makes up the set Δ. One can notice that the "shape" of this set
is different depending on whether s/t is rational or not:
 - For irrational s/t, each lattice point will get a assigned a unique δ, and
   Δ get more dense when we are futher away from the origin
 - For rational s/t, a line of slope -s/t can pass multiple lattice points,
   and eventually the gap between δ is stabilized at a fixed value gcd(s, t)
-/

def is_δ(s t: ℝ) (δ: ℝ): Prop :=
  ∃ p q: ℕ, p * s + q * t = δ

def Δ(s t: ℝ) :=
  {δ | is_δ s t δ}

/-
The set Δ is symmetric for s and t. We will exploit this symmetry a lot later on.
-/
theorem Δ_symm(s t: ℝ): Δ s t = Δ t s := by
  ext
  have oneway(δ s t:ℝ)(h: δ ∈ Δ s t):  δ ∈ Δ t s := by
    rcases h with ⟨p, q, pq⟩
    use q, p
    rw [add_comm]
    exact pq
  constructor
  · apply oneway
  · apply oneway

/-
For each lattice point, we can assign a δ. As previously mentioned,
this is injective only when s/t is irrational
-/
def δₚ(s t: ℝ) (pq: ℕ × ℕ): ℝ :=
  match pq with
  | (p, q) => p * s + q * t

/-
Similarly, δₚ is also symmetric, but one needs to swap the coordinates of the input
-/
lemma δₚ_symm (s t: ℝ) (p q: ℕ): δₚ s t (p, q) = δₚ t s (q, p) := by
  unfold δₚ
  simp
  apply add_comm

example : 27 ∈ Δ 10 7 := by
  use 2, 1
  norm_num

/-
We can draw a line with slope -s/t and only consider lattice points enveloped by the line,
including those on the line. Equalently, this is considering only points whose assigned
δ is less or equal to a given value. We call these subsets as "ceiled"
-/

def Δceiled(s t ceil: ℝ) :=
  (Δ s t) ∩ {δ | δ ≤ ceil}

def Λceiled(s t ceil: ℝ) :=
  {(p, q): ℕ × ℕ | p * s + q * t ≤ ceil}


lemma Λceiled_symm (s t δ: ℝ) (p q: ℕ) (h: (p, q) ∈ Λceiled s t δ):
(q, p) ∈ Λceiled t s δ := by
  unfold Λceiled
  unfold Λceiled at h
  simp at h
  simp
  rw [add_comm]
  exact h

/-
As an important example, the subset ceiled by 0 only includes the point (0, 0)
-/
lemma Λceiled₀ (s t: ℝ) [PosReal s] [PosReal t]: Λceiled s t 0 = {(0, 0)} := by
  unfold Λceiled
  ext ⟨p,q⟩
  constructor
  · rintro sum_le_zero
    simp at sum_le_zero
    apply sum_to_zero at sum_le_zero
    · rcases sum_le_zero with ⟨p1, q1⟩
      simp
      constructor
      · have h: (p:ℝ) = 0 := by
          apply eq_zero_of_ne_zero_of_mul_right_eq_zero
          · show s ≠ 0
            apply ne_of_gt PosReal.pos
          · exact p1
        apply Nat.cast_eq_zero.mp h
      · have h: (q:ℝ) = 0 := by
          apply eq_zero_of_ne_zero_of_mul_right_eq_zero
          · show t ≠ 0
            apply ne_of_gt PosReal.pos
          · exact q1
        apply Nat.cast_eq_zero.mp h
    · apply mul_nonneg
      · apply Nat.cast_nonneg
      · apply le_of_lt PosReal.pos
    · apply mul_nonneg
      · apply Nat.cast_nonneg
      · apply le_of_lt PosReal.pos
  · rintro zero
    simp at zero
    rcases zero with ⟨p0, q0⟩
    rw [p0]
    rw [q0]
    simp

/-
And if the ceiling is negative, Λceiled is the empty set.
-/
lemma Λceiled_neg (s t δ: ℝ) (neg: δ < 0) [PosReal s] [PosReal t]:
Λceiled s t δ = ∅ := by
  unfold Λceiled
  ext pq
  simp
  apply lt_of_lt_of_le neg
  apply add_nonneg
  · apply mul_nonneg
    · simp
    · apply le_of_lt PosReal.pos
  · apply mul_nonneg
    · simp
    · apply le_of_lt PosReal.pos

/-
Obviously, the δₚ maps all ceiled lattice points to all ceiled δ
-/
lemma Λ_map_ceiled: δₚ s t '' (Λceiled s t ceil) = Δceiled s t ceil := by
  ext y; constructor
  · rintro ⟨⟨p, q⟩, pqunderbound , deltaEFromDot⟩
    constructor
    · use p, q
      exact deltaEFromDot
    · rw [← deltaEFromDot]
      exact pqunderbound
  · rintro ⟨⟨p, q, deltaEFromDot⟩, bounded⟩
    use (p, q)
    constructor
    · unfold Λceiled
      simp at bounded
      rw [← deltaEFromDot] at bounded
      exact bounded
    · exact deltaEFromDot

/-
We would like to prove that Δceiled is finite.
We first introduce bounded natural numbers, and their products
and show their finiteness.
-/
def ℕceiled (ceil: ℝ) := {p: ℕ | p ≤ ceil}

instance ℕceiled_finite (ceil: ℝ): Finite (ℕceiled ceil) := by
  by_cases h: ceil < 0
  · have empty: ℕceiled ceil = ∅ := by
      rw [ℕceiled]
      apply Set.eq_empty_of_forall_not_mem
      intro s
      simp
      apply lt_of_lt_of_le h
      exact Nat.cast_nonneg' s
    simp [empty]
    exact Finite.of_subsingleton
  · let N := Nat.floor ceil
    rw [ℕceiled]
    apply Set.Finite.subset (Set.finite_le_nat N)
    intro s hs
    simp
    rw [Set.mem_setOf_eq] at hs
    apply (Nat.le_floor_iff (le_of_not_lt h)).mpr
    exact hs

def ΛRec (pbound qbound: ℝ) := Set.prod (ℕceiled pbound) (ℕceiled qbound)

instance ΛRec_finite (pbound qbound: ℝ): Finite (ΛRec pbound qbound) := by
  apply Set.finite_prod.mpr
  constructor
  · left; apply ℕceiled_finite
  · left; apply ℕceiled_finite

/-
We can show Λceiled is always inside a rectangle region, hence finite
-/
lemma Λceiled_in_rec (s t ceil: ℝ) [PosReal s] [PosReal t]:
  Λceiled s t ceil ⊆ ΛRec (ceil / s) (ceil / t) := by
  rintro ⟨p, q⟩ pqInBound
  constructor
  · rw [ℕceiled]
    simp
    apply (le_div_iff₀' PosReal.pos).mpr
    calc
      s * p = p * s := by apply mul_comm
      _ = p * s + 0 := by rw [add_zero]
      _ ≤ p * s + q * t := by
        apply add_le_add
        · apply le_refl
        · rw [← zero_mul 0]
          apply mul_le_mul
          · exact Nat.cast_nonneg' q
          · exact le_of_lt PosReal.pos
          · apply le_refl
          · exact Nat.cast_nonneg' q
      _ ≤ ceil := by exact pqInBound
  · rw [ℕceiled]
    simp
    apply (le_div_iff₀' PosReal.pos).mpr
    calc
      t * q = q * t := by apply mul_comm
      _ = 0 + q * t:= by rw [zero_add]
      _ ≤ p * s + q * t := by
        apply add_le_add
        · rw [← zero_mul 0]
          apply mul_le_mul
          · exact Nat.cast_nonneg' p
          · exact le_of_lt PosReal.pos
          · apply le_refl
          · exact Nat.cast_nonneg' p
        · apply le_refl
      _ ≤ ceil := by exact pqInBound

instance Λceiled_finite(s t ceil: ℝ) [PosReal s] [PosReal t]: Finite (Λceiled s t ceil) := by
  apply Finite.Set.subset (ΛRec (ceil / s) (ceil / t)) (Λceiled_in_rec s t ceil)

noncomputable instance (s t ceil: ℝ) [PosReal s] [PosReal t]:
Fintype (Λceiled s t ceil) := by apply Fintype.ofFinite

/-
As the image of δₚ, Δ is therefore also finite, and consequently well-ordered
-/
instance Δceiled_finite(s t ceil: ℝ) [PosReal s] [PosReal t]: Finite (Δceiled s t ceil) := by
  rw [← Λ_map_ceiled]
  apply Set.Finite.image (δₚ s t) (Λceiled_finite s t ceil)

lemma Δceiled_WF (s t ceil: ℝ) [PosReal s] [PosReal t]: (Δceiled s t ceil).IsWF := by
  apply Set.Finite.isWF
  apply Δceiled_finite s t ceil

/-
We now can show the whole set Δ is also well-ordered.
Although Δ is an infinite set and can become arbitrarily dense for larger elements,
its base, as indicated by the ceiled variation, behaves friendly for the order
-/
lemma Δ_WF (s t: ℝ) [PosReal s] [PosReal t]: Set.IsWF (Δ s t) := by
  have Δceiled_has_no_chain (ceil: ℝ):
    ∀ (f : ℕ → ℝ), StrictAnti f → ¬∀(n: ℕ), f (OrderDual.toDual n) ∈ Δceiled s t ceil := by
      apply Set.isWF_iff_no_descending_seq.mp
      apply Δceiled_WF s t ceil

  apply Set.isWF_iff_no_descending_seq.mpr
  rintro f fStrictAnti

  rintro assume_Δ_has_chain
  have Δ_chain_is_in_Δceiled:
    ∀n: ℕ, f (OrderDual.toDual n) ∈ Δceiled s t (f (OrderDual.toDual 0)) := by
      intro n
      rw [Δceiled]
      constructor
      · exact assume_Δ_has_chain n
      · simp
        by_cases nIsZero: n = 0
        · rw [nIsZero]
          simp
        · apply le_of_lt
          apply fStrictAnti
          exact Nat.zero_lt_of_ne_zero nIsZero
  exact Δceiled_has_no_chain (f (OrderDual.toDual 0)) f fStrictAnti Δ_chain_is_in_Δceiled

/-
Δ always has the smallest element 0
-/
lemma δ0 (s t: ℝ): 0 ∈ Δ s t := by
  use 0, 0
  norm_num

lemma Δ_nonempty (s t: ℝ): (Δ s t).Nonempty := by
  use 0
  apply δ0

lemma Δ_min_element (s t: ℝ) (δin: δ ∈ Δ s t) [PosReal s] [PosReal t]: 0 ≤ δ := by
  rcases δin with ⟨ p, ⟨ q, depq  ⟩ ⟩
  rw [← depq]
  apply add_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg' p
    · apply le_of_lt
      exact PosReal.pos
  · apply mul_nonneg
    · exact Nat.cast_nonneg' q
    · apply le_of_lt
      exact PosReal.pos

lemma Δ_min (s t: ℝ) [PosReal s] [PosReal t]:
  Set.IsWF.min (Δ_WF s t) (Δ_nonempty s t) = 0 := by
  apply Set.IsWF.min_eq_of_lt
  · apply δ0
  · intro δ δin δNotFirst
    apply lt_of_le_of_ne (Δ_min_element s t δin) (Ne.symm δNotFirst)

/-
We also introduce "floored" subsets, the complement of ceiled ones.
These subsets contain elements where δ is larger than a certain threshold.
-/
def Δfloored (s t floor: ℝ) :=
  Δ s t ∩ {δ: ℝ | δ > floor}

/-
Obviously, floored sets are also symmetric.
-/
lemma Δfloored_symm (s t floor: ℝ):
Δfloored s t floor = Δfloored t s floor := by
  unfold Δfloored
  congr
  apply Δ_symm

/-
Floored sets are still infinite, but are well-ordered as subsets
-/
lemma Δfloored_WF (s t floor: ℝ) [PosReal s] [PosReal t]:
  Set.IsWF (Δfloored s t floor) := by
  apply Set.WellFoundedOn.subset (Δ_WF s t )
  rintro _ ⟨δin, _⟩
  exact δin

/-
Floored sets are always non-empty due to the unboundness of Δ
-/
lemma Δfloored_nonempty (s t floor: ℝ) [PosReal s] [PosReal t]:
  (Δfloored s t floor).Nonempty := by
  use (Nat.ceil (floor / s) + 1) * s + t
  constructor
  · use (Nat.ceil (floor / s) + 1), 1
    norm_num
  · simp
    nth_rewrite 1 [← add_zero floor]
    apply add_lt_add
    · apply (div_lt_iff₀ PosReal.pos).mp
      calc
        floor / s ≤ Nat.ceil (floor / s) := by apply Nat.le_ceil
        _ < Nat.ceil (floor / s) + 1 := by apply lt_add_one
    · exact PosReal.pos

/-
Since Δ is well-ordered, it is possible to sort all elements
and enumerate them starting from the smallest one (0).

We first define the find the next δ' given an element δ using floored subsets.
Note that this function also accepts input outside of Δ. It simply finds the
smallest δ that's larger than the input
-/
noncomputable
def δnext (s t floor: ℝ) [PosReal s] [PosReal t]: ℝ :=
  Set.IsWF.min (Δfloored_WF s t floor) (Δfloored_nonempty s t floor)

/-
Again the symmetry is passed on to δnext
-/
lemma δnext_symm (s t floor: ℝ) [PosReal s] [PosReal t]:
δnext s t floor = δnext t s floor := by
  unfold δnext
  congr
  apply Δfloored_symm

/-
δnext will always output an element in Δ
-/
lemma δnext_in_Δ (s t floor: ℝ) [PosReal s] [PosReal t]: δnext s t floor ∈ Δ s t := by
  have: δnext s t floor ∈ Δfloored s t floor := by
    apply Set.IsWF.min_mem
  exact Set.mem_of_mem_inter_left this

/-
δnext will always output an element larger than the input
-/
lemma δnext_larger (s t floor: ℝ)  [PosReal s] [PosReal t]: δnext s t floor > floor := by
  unfold δnext
  have h (δ: ℝ) (mem: δ ∈ Δfloored s t floor): δ > floor := by
    unfold Δfloored at mem
    apply Set.mem_of_mem_inter_right at mem
    simp at mem
    trivial
  apply h (δnext s t floor) (Set.IsWF.min_mem (Δfloored_WF s t floor) (Δfloored_nonempty s t floor))

/-
δnext also effectively gives the "gap" between the input δ and the next δ'.
There is no additional lattice point between this gap,
which means Λceiled is inert for any bound given between the gap
-/
lemma Λceiled_gap (s t δ β: ℝ) [PosReal s] [PosReal t] (leftBound: δ ≤ β) (rightBound: β < δnext s t δ):
Λceiled s t δ = Λceiled s t β := by
  unfold Λceiled
  ext ⟨p, q⟩
  simp
  constructor
  · intro ltδ
    apply le_trans ltδ leftBound
  · intro gtβ
    contrapose gtβ with gtδ
    simp; simp at gtδ
    have inFloored: p * s + q * t ∈ Δfloored s t δ := by
      unfold Δfloored
      simp
      constructor
      · unfold Δ; unfold is_δ
        simp
      · exact gtδ
    apply Set.IsWF.not_lt_min (Δfloored_WF s t δ) (Δfloored_nonempty s t δ) at inFloored
    simp at inFloored
    apply lt_of_lt_of_le rightBound
    exact inFloored

/-
We can define the sequence δₖ by sorting all elements in Δ.
The index k will also be used a lot for other related sequences.
-/
noncomputable
def δₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℝ
| 0 => 0
| Nat.succ n => δnext s t (δₖ s t n)

/-
δₖ is obviously strictly increasing
-/
lemma δₖ_mono (s t: ℝ) [PosReal s] [PosReal t]: StrictMono (δₖ s t) := by
  have mono (s t: ℝ) (k a: ℕ) [PosReal s] [PosReal t]: δₖ s t k < δₖ s t (k + a + 1) := by
    induction a with
    | zero =>
      simp
      show δₖ s t k < δnext s t (δₖ s t k)
      exact δnext_larger s t (δₖ s t k)
    | succ a prev =>
      apply lt_trans prev
      rw [← add_assoc]
      show δₖ s t (k + a + 1) < δnext s t (δₖ s t (k + a + 1))
      exact δnext_larger s t (δₖ s t (k + a + 1))
  unfold StrictMono
  intro k l k_lt_l
  apply Nat.exists_eq_add_of_lt at k_lt_l
  rcases k_lt_l with ⟨a, a_is_diff⟩
  rw [a_is_diff]
  apply mono

/-
δₖ covers all elements in Δ. In fact, δₖ is a bijection between Δ and ℕ
-/
def δₖ_surjΔ (s t δ: ℝ) (mem: δ ∈ Δ s t) [PosReal s] [PosReal t]: ∃k, δₖ s t k = δ := by
  apply Set.WellFoundedOn.induction (Δ_WF s t) mem
  intro this thismem prev
  let underThis := (Δceiled s t this) \ {this}
  have underThisFinite: Set.Finite underThis := by
    unfold underThis
    exact Set.toFinite (Δceiled s t this \ {this})
  have underThisFintype: Fintype underThis := by exact underThisFinite.fintype
  by_cases nonEmpty: Set.Nonempty underThis
  · have nonEmpty': Finset.Nonempty underThis.toFinset := by
      exact Set.Aesop.toFinset_nonempty_of_nonempty nonEmpty
    rcases Finset.max_of_nonempty nonEmpty' with ⟨max: ℝ, maxEq⟩
    have maxmem: max ∈ underThis.toFinset := by exact Finset.mem_of_max maxEq
    have maxmem': max ∈ underThis := by exact Set.mem_toFinset.mp maxmem
    have maxmem: max ∈ Δ s t := by
      apply Set.mem_of_mem_of_subset maxmem'
      unfold underThis
      apply subset_trans (Set.diff_subset)
      unfold Δceiled
      exact Set.inter_subset_left
    have maxlt: max < this := by
      unfold underThis at maxmem'
      apply (Set.mem_diff max).mp at maxmem'
      rcases maxmem' with ⟨maxInCeil, maxNe⟩
      simp at maxNe
      unfold Δceiled at maxInCeil
      rcases maxInCeil with ⟨maxOnGrid, maxLe⟩
      simp at maxLe
      exact lt_of_le_of_ne maxLe maxNe
    rcases (prev max maxmem maxlt) with ⟨prevk, preveq⟩
    use prevk + 1
    unfold δₖ
    rw [preveq]
    apply le_antisymm
    · apply Set.IsWF.min_le
      unfold Δfloored
      constructor
      · exact thismem
      · exact maxlt
    · refine (Set.IsWF.le_min_iff ?_ ?_).mpr ?_
      rintro b bmem
      unfold Δfloored at bmem
      rcases bmem with ⟨bOnGrid, bLtMax⟩
      simp at bLtMax
      contrapose bLtMax with bLeThis
      simp at bLeThis
      simp
      have bMemUnder: b ∈ underThis := by
        unfold underThis
        apply (Set.mem_diff b).mpr
        constructor
        · unfold Δceiled
          constructor
          · exact bOnGrid
          · simp
            apply le_of_lt
            exact bLeThis
        · simp
          apply ne_of_lt
          exact bLeThis
      have bMemUnder: b ∈ underThis.toFinset := by exact Set.mem_toFinset.mpr bMemUnder
      exact Finset.le_max_of_eq bMemUnder maxEq
  · use 0
    have empty: underThis = ∅ := by exact Set.not_nonempty_iff_eq_empty.mp nonEmpty
    unfold underThis at empty
    have single: Δceiled s t this = {this} := by
      apply (Set.Nonempty.subset_singleton_iff ?_).mp ?_
      · apply Set.nonempty_of_mem
        show this ∈ Δceiled s t this
        unfold Δceiled
        constructor
        · exact thismem
        · simp
      · exact Set.diff_eq_empty.mp empty
    have this_is_0: this = 0 := by
      have subsingle: (Δceiled s t this).Subsingleton := by
        rw [single]
        exact Set.subsingleton_singleton
      contrapose subsingle with notZero
      apply Set.not_subsingleton_iff.mpr
      use 0
      constructor
      · unfold Δceiled
        constructor
        · unfold Δ; unfold is_δ; simp
          use 0, 0; simp
        · simp
          unfold Δ at thismem; unfold is_δ at thismem
          simp at thismem
          rcases thismem with ⟨p, ⟨q, pqmem⟩⟩
          rw [← pqmem]
          apply add_nonneg
          · apply mul_nonneg
            · simp
            · apply le_of_lt PosReal.pos
          · apply mul_nonneg
            · simp
            · apply le_of_lt PosReal.pos
      · use this
        constructor
        · unfold Δceiled
          constructor
          · exact thismem
          · simp
        · exact fun a ↦ notZero (id (Eq.symm a))
    rw [this_is_0]
    exact rfl



/-
δₖ is also symmetric
-/
theorem δₖ_symm (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: δₖ s t k = δₖ t s k := by
  induction k with
  | zero => unfold δₖ; rfl
  | succ k prev =>
    unfold δₖ
    rw [prev]
    apply δnext_symm

/-
δₖ always starts with 0
-/
lemma δ₀ (s t: ℝ) [PosReal s] [PosReal t]: δₖ s t 0 = 0 := by
  rfl

/-
All δₖ are obviously elements in Δ
-/
lemma δₖ_in_Δ (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: δₖ s t k ∈ Δ s t := by
  cases k with
  | zero => apply δ0
  | succ n => apply δnext_in_Δ

/-
We introduce a new kind of subset of the lattice:
lattice points whose assigned δ is exactly a given constant.
It can be empty if the given constant is not in Δ

As one can notice, this subset is a sub-singleton when s/t is irrational,
but we won't expand on it here
-/
def Λline (s t δ: ℝ): Set (ℕ × ℕ) :=
  ((δₚ s t) ⁻¹' Set.singleton δ)

/-
This subset is again symmetric with lattice coordinates swapped.
-/
lemma Λline_symm (s t δ: ℝ) (p q: ℕ) (h: (p, q) ∈ Λline s t δ):
(q, p) ∈ Λline t s δ := by
  unfold Λline
  unfold Λline at h
  simp at h
  apply Set.mem_preimage.mpr
  apply Set.mem_singleton_of_eq
  rw [δₚ_symm t s q p]
  exact h

/-
If the line is negative, it won't cover any lattice points
-/
lemma Λline_neg (s t δ: ℝ) (neg: δ < 0) [PosReal s] [PosReal t]:
Λline s t δ = ∅ := by
  unfold Λline
  ext pq
  simp
  apply Set.not_mem_singleton_iff.mpr
  apply ne_of_gt
  apply lt_of_lt_of_le neg
  apply add_nonneg
  · apply mul_nonneg
    · simp
    · apply le_of_lt PosReal.pos
  · apply mul_nonneg
    · simp
    · apply le_of_lt PosReal.pos

/-
Elements in Λline is allowed to shift in coordinates and change their δ by s.

Note that this is not saying Λline of δ and of δ + s are one-to-one.
When shifting δ by s, it can potentially introduce a new element with p' = 0. This element
is ruled out by the p' = p + 1 ≥ 1 in the statement
-/
lemma Λline_s (s t δ: ℝ) [PosReal s] [PosReal t]:
∀(p q: ℕ), (p, q) ∈ Λline s t δ ↔ (p + 1, q) ∈ (Λline s t (δ + s)) := by
  intro p q
  constructor
  · intro onLine
    unfold Λline at onLine
    simp at onLine
    apply Set.eq_of_mem_singleton at onLine
    unfold δₚ at onLine
    simp at onLine
    unfold Λline
    simp
    apply Set.mem_singleton_of_eq
    unfold δₚ
    simp
    linarith
  · rintro onLine
    unfold Λline at onLine
    unfold Λline
    simp at onLine
    simp
    apply Set.mem_singleton_of_eq
    apply Set.eq_of_mem_singleton at onLine
    unfold δₚ
    unfold δₚ at onLine
    simp
    simp at onLine
    linarith

/-
By symmetry, we can state similarly for t and q
-/
lemma Λline_t (s t δ: ℝ) [PosReal s] [PosReal t]:
∀(p q: ℕ), (p, q) ∈ Λline s t δ ↔ (p, q + 1) ∈ (Λline s t (δ + t)) := by
  intro p q
  constructor
  · intro h
    apply Λline_symm at h
    apply Λline_symm
    apply (Λline_s t s δ q p).mp
    exact h
  · rintro h
    apply Λline_symm at h
    apply Λline_symm
    apply (Λline_s t s δ q p).mpr
    exact h

/-
The line subset at δ = 0 gives the singleton (0, 0)
-/
lemma Λline₀ (s t: ℝ) [PosReal s] [PosReal t]: Λline s t 0 = {(0, 0)} := by
  unfold Λline
  ext ⟨p,q⟩
  constructor
  · rintro inPreimage
    rw [Set.mem_preimage] at inPreimage
    apply Set.eq_of_mem_singleton at inPreimage
    apply Set.mem_singleton_of_eq
    unfold δₚ at inPreimage
    simp at inPreimage
    have sum: (p: ℝ) * s + (q: ℝ) * t = 0 := by linarith
    apply le_of_eq at sum
    apply sum_to_zero at sum
    · rcases sum with ⟨p1, q1⟩
      simp
      constructor
      · have h: (p:ℝ) = 0 := by
          apply eq_zero_of_ne_zero_of_mul_right_eq_zero
          · show s ≠ 0
            apply ne_of_gt PosReal.pos
          · exact p1
        apply Nat.cast_eq_zero.mp h
      · have h: (q:ℝ) = 0 := by
          apply eq_zero_of_ne_zero_of_mul_right_eq_zero
          · show t ≠ 0
            apply ne_of_gt PosReal.pos
          · exact q1
        apply Nat.cast_eq_zero.mp h
    · apply mul_nonneg
      · apply Nat.cast_nonneg
      · apply le_of_lt PosReal.pos
    · apply mul_nonneg
      · apply Nat.cast_nonneg
      · apply le_of_lt PosReal.pos
  · rintro pqIs11
    apply Set.eq_of_mem_singleton at pqIs11
    cases pqIs11
    simp
    apply Set.mem_singleton_of_eq
    unfold δₚ
    simp

/-
Λline is not empty when the input is from Δ
-/
lemma Λline_nonempty (s t δ: ℝ) (δinΩ: δ ∈ Δ s t): (Λline s t δ).Nonempty := by
  rcases δinΩ with ⟨p, q, pqOnLine ⟩
  use (p, q)
  exact pqOnLine

/-
Λline is a subset of the corresponding Λceiled, and therefore is also finite.
-/
lemma Λline_in_Λceiled (s t δ: ℝ): Λline s t δ ⊆ Λceiled s t δ := by
  rintro ⟨p, q⟩ pqOnLine
  unfold Λceiled
  simp
  apply le_of_eq
  exact pqOnLine

instance (s t δ: ℝ) [PosReal s] [PosReal t]:
Finite (Λline s t δ) := by
  apply Finite.Set.subset (Λceiled s t δ) (Λline_in_Λceiled s t δ)

noncomputable instance (s t δ: ℝ) [PosReal s] [PosReal t]:
Fintype (Λline s t δ) := by apply Fintype.ofFinite

/-
Now we assign each lattice point with another value J,
which is the Pascal triangle where p- and q-axies are the sides of the triangle
-/
def Jₚ: ℕ × ℕ → ℕ
| (p, q) => Nat.choose (p + q) (p)

/-
Just like the Pascal triangle, Jₚ follows the recurrence relation.

It should be noted that if we embed Λ in ℤ × ℤ and assign J = 0 to the rest of the points,
all points still follow this recurrence relation *except* at (0, 0).
This defect will show up again later.
-/
lemma Jₚ_rec (p q: ℕ):
Jₚ ((p + 1), (q + 1)) = (Jₚ ((p + 1), q)) + Jₚ (p, (q + 1)) := by
  unfold Jₚ
  simp
  rw [← add_assoc]
  rw [Nat.choose]
  rw [add_comm]
  congr 2
  linarith

/-
On Λ, J are all nonzero
-/
lemma Jₚ_nonzero: Jₚ pq > 0 := by
  rw [Jₚ]
  apply Nat.choose_pos
  apply Nat.le_add_right

/-
J itself is symmatrical for swapped coordinates.
-/
lemma Jₚ_symm (p q: ℕ): Jₚ (p, q) = Jₚ (q, p) := by
  unfold Jₚ
  by_cases pzero: p = 0
  · rw [pzero]
    by_cases qzero: q = 0
    · rw [qzero]
    · simp
  · by_cases qzero: q = 0
    · rw [qzero]
      simp
    · simp
      rw [← Nat.choose_symm]
      · rw [add_comm]
        congr 1
        exact Eq.symm (Nat.eq_sub_of_add_eq rfl)
      · exact Nat.le_add_right p q

/-
We can evaluate J for a given δ, by summing up J of all points passed by the line
-/
noncomputable
def Jline (s t δ: ℝ) [PosReal s] [PosReal t]: ℕ :=
  ∑pq ∈ (Λline s t δ).toFinset, Jₚ pq

/-
The evaluation on the line is symmetric for s and t
-/
lemma Jline_symm (s t δ: ℝ) [PosReal s] [PosReal t]: Jline s t δ = Jline t s δ := by
  let map: (ℕ × ℕ) → (ℕ × ℕ)
  | (p, q) => (q, p)
  apply Finset.sum_of_injOn map
  · unfold Set.InjOn
    intro a _ b _
    unfold map
    simp
    exact fun a_1 a_2 ↦ Prod.ext a_2 a_1
  · unfold Set.MapsTo
    rintro ⟨p, q⟩ mem
    simp at mem
    unfold map
    simp
    exact Λline_symm s t δ p q mem
  · rintro ⟨p, q⟩ mem nmem
    absurd nmem
    simp
    simp at mem
    use q,p
    constructor
    · exact Λline_symm t s δ p q mem
    · unfold map
      simp
  · unfold map
    simp
    intro a b mem
    exact Jₚ_symm a b

-- A helper function to zero the value if the input is zero
def shut(p: ℕ) (value: ℕ) := match p with
| Nat.zero => 0
| Nat.succ _ => value

/-
Jline can be shifted by s. The sum will however be affected by the potential point
on the p = 0 boundary, hence the equality needs to remove such point
-/
lemma Jline_s (s t δ: ℝ) [PosReal s] [PosReal t]:
Jline s t (δ - s) = ∑⟨p, q⟩ ∈ (Λline s t δ).toFinset, shut p (Jₚ (p - 1, q)) := by
  unfold Jline
  let map: (ℕ × ℕ) → (ℕ × ℕ)
  | (p, q) => (p + 1, q)
  apply Finset.sum_of_injOn map
  · unfold Set.InjOn
    simp
    intro a b abmem c d cdmem ab_eq_cd
    unfold map at ab_eq_cd
    simp at ab_eq_cd
    trivial
  · simp
    unfold Λline;
    unfold Set.MapsTo
    intro ⟨p, q⟩  pqmem
    simp; simp at pqmem
    apply Set.eq_of_mem_singleton at pqmem
    unfold δₚ at pqmem
    simp at pqmem
    apply Set.mem_singleton_of_eq
    unfold map
    unfold δₚ
    simp
    linarith
  · intro ⟨p, q⟩ pqmem pqnmem
    have p0: p = 0 := by
      unfold Λline at pqmem
      simp at pqmem
      apply Set.eq_of_mem_singleton at pqmem
      unfold Λline at pqnmem
      simp at pqnmem
      contrapose pqnmem
      simp
      use p - 1, q
      constructor
      · apply Set.mem_singleton_of_eq
        unfold δₚ
        unfold δₚ at pqmem
        simp
        simp at pqmem
        rw [← pqmem]
        apply Nat.exists_eq_succ_of_ne_zero at pqnmem
        rcases pqnmem with ⟨n, np⟩
        rw [np]
        simp
        ring
      · unfold map
        simp
        apply Nat.exists_eq_succ_of_ne_zero at pqnmem
        rcases pqnmem with ⟨n, np⟩
        rw [np]
        simp
    rw [p0]
    unfold shut
    simp
  · intro δ δmem
    unfold map; unfold shut
    simp

/-
A similar statement can be said for t
TODO: can we use symmetric lemmas to avoid copy-pasting the proof here?
-/
lemma Jline_t (s t δ: ℝ) [PosReal s] [PosReal t]:
Jline s t (δ - t) = ∑⟨p, q⟩ ∈ (Λline s t δ).toFinset, shut q (Jₚ (p, q - 1)) := by
  unfold Jline
  let map: (ℕ × ℕ) → (ℕ × ℕ)
  | (p, q) => (p, q + 1)
  apply Finset.sum_of_injOn map
  · unfold Set.InjOn
    simp
    intro a b abmem c d cdmem ab_eq_cd
    unfold map at ab_eq_cd
    simp at ab_eq_cd
    trivial
  · simp
    unfold Λline;
    unfold Set.MapsTo
    intro ⟨p, q⟩  pqmem
    simp; simp at pqmem
    apply Set.eq_of_mem_singleton at pqmem
    unfold δₚ at pqmem
    simp at pqmem
    apply Set.mem_singleton_of_eq
    unfold map
    unfold δₚ
    simp
    linarith
  · intro ⟨p, q⟩ pqmem pqnmem
    have p0: q = 0 := by
      unfold Λline at pqmem
      simp at pqmem
      apply Set.eq_of_mem_singleton at pqmem
      unfold Λline at pqnmem
      simp at pqnmem
      contrapose pqnmem
      simp
      use p, q - 1
      constructor
      · apply Set.mem_singleton_of_eq
        unfold δₚ
        unfold δₚ at pqmem
        simp
        simp at pqmem
        rw [← pqmem]
        apply Nat.exists_eq_succ_of_ne_zero at pqnmem
        rcases pqnmem with ⟨n, np⟩
        rw [np]
        simp
        ring
      · unfold map
        simp
        apply Nat.exists_eq_succ_of_ne_zero at pqnmem
        rcases pqnmem with ⟨n, np⟩
        rw [np]
        simp
    rw [p0]
    unfold shut
    simp
  · intro δ δmem
    unfold map; unfold shut
    simp

/-
Derived from the recurrence of binomial coefficents,
Jline is also recurrent, except for at δ = 0
-/
lemma Jline_rec (s t δ: ℝ) (δ0: δ ≠ 0) [PosReal s] [PosReal t]:
Jline s t δ = Jline s t (δ - s) + Jline s t (δ - t) := by
  rw [Jline_s]
  rw [Jline_t]
  unfold Jline
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr
  congr
  rintro ⟨p, q⟩ pqOnLine
  by_cases p0: p = 0
  · by_cases q0: q = 0
    · unfold Λline at pqOnLine
      simp at pqOnLine
      apply Set.eq_of_mem_singleton at pqOnLine
      unfold δₚ at pqOnLine
      rw [p0, q0] at pqOnLine
      simp at pqOnLine
      absurd δ0
      rw [pqOnLine]
    · simp
      unfold shut
      apply Nat.exists_eq_succ_of_ne_zero at q0
      rcases q0 with ⟨q1, q10⟩
      rw [p0]
      rw [q10]
      simp
      unfold Jₚ
      simp
  · by_cases q0: q = 0
    · simp
      unfold shut
      apply Nat.exists_eq_succ_of_ne_zero at p0
      rcases p0 with ⟨p1, p10⟩
      rw [q0]
      rw [p10]
      simp
      unfold Jₚ
      simp
    · apply Nat.exists_eq_succ_of_ne_zero at p0
      rcases p0 with ⟨p1, p10⟩
      apply Nat.exists_eq_succ_of_ne_zero at q0
      rcases q0 with ⟨q1, q10⟩
      simp
      unfold shut
      rw [q10]
      rw [p10]
      simp
      nth_rw 3 [add_comm]
      apply Jₚ_rec

/-
At δ = 0, Jline gives the "seed" 1 that induces all other values
-/
lemma Jline₀ (s t: ℝ) [PosReal s] [PosReal t]: Jline s t 0 = 1 := by
  unfold Jline
  let zerozero: ℕ × ℕ := (0, 0)
  have h: (Λline s t 0).toFinset = {zerozero} := by
    apply Finset.coe_injective
    simp
    rw [Λline₀ s t]
  rw [Finset.sum_congr h]
  · show ∑pq ∈ {zerozero}, Jₚ pq = 1
    rfl
  · show ∀ x ∈ {(0, 0)}, Jₚ x = Jₚ x
    rintro x x1
    rfl

/-
For all elements of Δ, Jline is nonzero
-/
lemma Jline_nonzero (s t δ: ℝ) [PosReal s] [PosReal t] (δinΩ: δ ∈ Δ s t):
Jline s t δ > 0 := by
  apply Nat.lt_of_succ_le
  simp
  rcases Λline_nonempty s t δ δinΩ with ⟨pq, pqOnLine⟩
  have nonneg: ∀ pq ∈ (Λline s t δ).toFinset, 0 ≤ Jₚ pq := by
    simp
  calc
    1 ≤ Jₚ pq := by
      apply Nat.succ_le_of_lt
      apply Jₚ_nonzero
    _ ≤ Jline s t δ := by
      apply Finset.single_le_sum nonneg
      apply Set.mem_toFinset.mpr pqOnLine

/-
Since we have defined the sequence δₖ for all elements in Δ,
we can map them to a sequence Jₖ by Jline
-/
noncomputable
def Jₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ :=
  fun k ↦ Jline s t (δₖ s t k)

/-
The sequence Jₖ is also symmetric and non-zero
-/
lemma Jₖ_symm (s t: ℝ) [PosReal s] [PosReal t]: Jₖ s t = Jₖ t s := by
  ext
  unfold Jₖ
  rw [δₖ_symm]
  rw [Jline_symm]

lemma Jₖ_nonzero (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: Jₖ s t k > 0 := by
  apply Jline_nonzero
  apply δₖ_in_Δ

example (s t: ℝ) [PosReal s] [PosReal t]: Jₖ s t 0 = 1 := by
  unfold Jₖ
  unfold δₖ
  apply Jline₀

/-
We also define a pair of sequence Jsₖ and Jtₖ similar to Jₖ,
but the line is shifted by s or t.
The shifting can make some line no longer pass any lattice points,
so some Jsₖ and Jtₖ are zero
-/
noncomputable
def Jsₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ :=
  fun k ↦ Jline s t ((δₖ s t k) - s)

noncomputable
def Jtₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ :=
  fun k ↦ Jline s t ((δₖ s t k) - t)

/-
Jsₖ and Jtₖ are symmetric to each other
-/
def Jstₖ_symm (s t: ℝ) (k: ℕ)[PosReal s] [PosReal t]:
Jsₖ s t k = Jtₖ t s k := by
  unfold Jsₖ
  unfold Jtₖ
  rw [Jline_symm]
  congr 2
  exact δₖ_symm s t k

/-
Derived from Jline recurrence formula, Jₖ can be decomposed into Jsₖ and Jtₖ
-/
lemma Jstₖ_rec (s t: ℝ) (k: ℕ) (k0: k ≥ 1) [PosReal s] [PosReal t]:
Jₖ s t k = Jsₖ s t k + Jtₖ s t k := by
  unfold Jₖ
  unfold Jsₖ
  unfold Jtₖ
  apply Jline_rec s t (δₖ s t k)
  apply ne_of_gt
  rw [← δ₀ s t]
  apply (StrictMono.lt_iff_lt (δₖ_mono s t)).mpr
  exact k0

/-
Just like Jline for Λline, we can define Jceiled for Λceiled
which sums over all lattices bounded by δ.
-/
noncomputable
def Jceiled (s t: ℝ) [PosReal s] [PosReal t] (δ: ℝ): ℕ :=
  ∑pq ∈ (Λceiled s t δ).toFinset, Jₚ pq

/-
Jceiled is symmetric
-/
lemma Jceiled_symm (s t δ: ℝ) [PosReal s] [PosReal t]:
Jceiled s t δ = Jceiled t s δ := by
  let map: (ℕ × ℕ) → (ℕ × ℕ)
  | (p, q) => (q, p)
  apply Finset.sum_of_injOn map
  · unfold Set.InjOn
    intro a _ b _
    unfold map
    simp
    exact fun a_1 a_2 ↦ Prod.ext a_2 a_1
  · unfold Set.MapsTo
    rintro ⟨p, q⟩ mem
    simp at mem
    unfold map
    simp
    exact Λceiled_symm s t δ p q mem
  · rintro ⟨p, q⟩ mem nmem
    absurd nmem
    simp
    simp at mem
    use q,p
    constructor
    · exact Λceiled_symm t s δ p q mem
    · unfold map
      simp
  · unfold map
    simp
    intro a b mem
    exact Jₚ_symm a b

/-
Jceiled is weakly increasing with regards to δ.
As δ grows, Λceiled can either remain unchanged for include new points.
-/
lemma Jceiled_mono (s t: ℝ) [PosReal s] [PosReal t]: Monotone (Jceiled s t) := by
  unfold Monotone
  intro a b ab
  unfold Jceiled
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · simp
    unfold Λceiled
    simp
    intro p q pq
    exact Preorder.le_trans (↑p * s + ↑q * t) a b pq ab
  · intro _ _ _
    apply Nat.zero_le

/-
The growth of Jceiled is precisely described by Jline.
One way to view this is to say Jceiled = ΣJline for all lines in the bound
-/
lemma Jceiled_accum (s t δ: ℝ) [PosReal s] [PosReal t]:
Jceiled s t δ + Jline s t (δnext s t δ) = Jceiled s t (δnext s t δ) := by
  unfold Jceiled; unfold Jline
  have disjoint: Disjoint (Λceiled s t δ).toFinset
                          (Λline s t (δnext s t δ)).toFinset := by
    simp
    apply Set.disjoint_iff_forall_ne.mpr
    rintro ⟨p, q⟩ peCeiled ⟨p2, q2⟩ pqLine
    unfold Λceiled at peCeiled
    simp at peCeiled
    unfold Λline at pqLine
    apply Set.mem_preimage.mp at pqLine
    apply Set.eq_of_mem_singleton at pqLine
    unfold δₚ at pqLine
    simp at pqLine
    contrapose peCeiled with pqEq
    simp at pqEq
    rcases pqEq with ⟨pEq, qEq⟩
    rw [pEq]
    rw [qEq]
    rw [pqLine]
    simp
    exact δnext_larger s t δ

  have union: (Λceiled s t δ).toFinset.disjUnion
          (Λline s t (δnext s t δ)).toFinset disjoint =
          (Λceiled s t (δnext s t δ)).toFinset := by
    refine Finset.ext_iff.mpr ?_
    simp
    intro p q
    constructor
    · rintro pqIn
      rcases pqIn with pqCeled | pqLine
      · unfold Λceiled at pqCeled; simp at pqCeled
        unfold Λceiled; simp
        apply le_trans pqCeled
        apply le_of_lt
        exact δnext_larger s t δ
      · unfold Λline at pqLine
        apply Set.eq_of_mem_singleton at pqLine
        unfold Λceiled; simp
        rw [← pqLine]
        unfold δₚ
        trivial
    · rintro pqCeiled
      by_cases pqCeiledSmaller: (p, q) ∈ Λceiled s t δ
      · left; exact pqCeiledSmaller
      · right
        unfold Λceiled at pqCeiled; simp at pqCeiled
        unfold Λceiled at pqCeiledSmaller; simp at pqCeiledSmaller
        unfold Λline
        apply Set.mem_singleton_of_eq
        unfold δₚ; simp
        have pqFloored: p * s + q * t ∈ Δfloored s t δ := by
          unfold Δfloored
          constructor
          · unfold Δ; simp; unfold is_δ; use p, q;
          · simp; exact pqCeiledSmaller
        have pqUp: p * s + q * t ≥ δnext s t δ := by
          unfold δnext
          exact Set.IsWF.min_le (Δfloored_WF s t δ) (Δfloored_nonempty s t δ) pqFloored
        apply not_lt_of_ge at pqUp
        apply eq_of_le_of_not_lt pqCeiled pqUp
  rw [← union]
  rw [Finset.sum_disjUnion]

/-
Since there are gaps between δ, Jceiled stops growing when inside these gaps
We can also derive a few variants of this lemma:
 - As long as β is less than δnext(δ), Jceiled(β) is no larger than Jceiled(δ)
 - or the contrapose: if Jceiled(β) is larger than Jceiled(δ), β must have passed δnext(δ)
-/
lemma Jceiled_gap (s t δ β: ℝ) [PosReal s] [PosReal t] (leftBound: δ ≤ β) (rightBound: β < δnext s t δ):
Jceiled s t δ = Jceiled s t β := by
  unfold Jceiled
  congr 1
  simp
  apply Λceiled_gap s t δ β leftBound rightBound

lemma Jceiled_gap' (s t δ β: ℝ) [PosReal s] [PosReal t] (rightBound: β < δnext s t δ):
Jceiled s t δ ≥ Jceiled s t β := by
  by_cases inBetween: δ ≤ β
  · apply ge_of_eq
    exact Jceiled_gap s t δ β inBetween rightBound
  · simp at inBetween
    apply Jceiled_mono
    exact le_of_lt inBetween

lemma Jceiled_gap'' (s t δ β: ℝ) [PosReal s] [PosReal t] (jump: Jceiled s t δ < Jceiled s t β):
δnext s t δ ≤ β := by
  contrapose jump with le
  simp; simp at le
  apply Jceiled_gap'
  exact le

lemma Jceiled_neg (s t δ: ℝ) (neg: δ < 0) [PosReal s] [PosReal t]:
Jceiled s t δ = 0 := by
  unfold Jceiled
  have empty: (Λceiled s t δ).toFinset = ∅ := by
    simp
    exact Λceiled_neg s t δ neg
  rw [empty]
  exact rfl

/-
Now we can define the sequence nₖ as partial sums of Jₖ.

The first element n₀ starts at 1 for reasons we will see later.
This essentially comes from the defect of binomial coefficient at (0, 0).

nₖ will be the n-coordinate of the vertices of several piecewise functions we will introduce
-/
noncomputable
def nₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ
| 0 => 1
| Nat.succ k => (nₖ s t k) + (Jₖ s t k)

/-
Since nₖ is the partial sum, we can alternatively express it using Jceiled
-/
lemma nₖ_accum (s t: ℝ) (k: ℕ)  [PosReal s] [PosReal t]:
nₖ s t k = if k = 0 then 1 else 1 + Jceiled s t (δₖ s t (k - 1)) := by
  induction k with
  | zero => unfold nₖ; simp
  | succ k prev =>
    simp
    unfold nₖ
    by_cases k0: k = 0
    · rw [k0] at prev; simp at prev
      rw [k0]
      unfold nₖ
      apply add_left_cancel_iff.mpr
      unfold Jₖ
      rw [δ₀]
      unfold Jline
      unfold Jceiled
      congr 1
      simp
      rw [Λceiled₀]
      apply Λline₀
    · simp [k0] at prev
      rw [prev]
      unfold Jₖ
      let δ := δₖ s t (k - 1)
      have next: δₖ s t k = δnext s t δ := by
        unfold δₖ
        apply Nat.exists_eq_succ_of_ne_zero at k0
        rcases k0 with ⟨k1, k1succ⟩
        rw [k1succ]
        simp
        unfold δ
        congr
        exact Nat.eq_sub_of_add_eq (id (Eq.symm k1succ))
      rw [next]
      rw [add_assoc]
      apply add_left_cancel_iff.mpr
      apply Jceiled_accum

/-
nₖ is also symmetric
-/
lemma nₖ_symm (s t: ℝ) [PosReal s] [PosReal t]: nₖ s t = nₖ t s := by
  ext n
  induction n with
  | zero => unfold nₖ; trivial
  | succ n prev =>
    unfold nₖ
    rw [prev]
    simp
    rw [Jₖ_symm]

/-
The first two elements of nₖ are always 1 and 2
-/
lemma n₀ (s t: ℝ) [PosReal s] [PosReal t]: nₖ s t 0 = 1 := by
  unfold nₖ
  rfl

lemma n₁ (s t: ℝ) [PosReal s] [PosReal t]: nₖ s t 1 = 2 := by
  unfold nₖ
  unfold nₖ
  unfold Jₖ
  rw [δₖ]
  rw [Jline₀]

/-
nₖ grows faster than k it self
-/
lemma nₖ_grow (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: nₖ s t k > k := by
  induction k with
  | zero =>
    unfold nₖ
    norm_num
  | succ n prev =>
    unfold nₖ
    apply add_lt_add_of_lt_of_le
    · exact prev
    · exact Jₖ_nonzero s t n

/-
And obviously, nₖ is strictly increasing
-/
lemma nₖ_mono (s t: ℝ) [PosReal s] [PosReal t]: StrictMono (nₖ s t) := by
  have v1 (k a: ℕ): nₖ s t k < nₖ s t (a + 1 + k) := by
    induction a with
    | zero =>
      simp
      rw [Nat.add_comm]
      rw [Nat.add_one]
      nth_rewrite 1 [nₖ]
      apply (lt_add_iff_pos_right (nₖ s t k)).mpr
      apply Jₖ_nonzero
    | succ a prev =>
      apply lt_trans
      · apply prev
      · nth_rewrite 2 [Nat.add_assoc]
        nth_rewrite 1 [Nat.add_comm 1 k]
        rw [← Nat.add_assoc]
        nth_rewrite 2 [Nat.add_one]
        nth_rewrite 1 [nₖ]
        apply (lt_add_iff_pos_right (nₖ s t (a + 1 + k))).mpr
        apply Jₖ_nonzero
  have v2 (k l: ℕ) (kl: k < l): nₖ s t k < nₖ s t l := by
    let a := l - k - 1
    have lrw: l = a + 1 + k := by
      apply Nat.succ_le_of_lt at kl
      norm_num at kl
      apply (Nat.sub_eq_iff_eq_add ?_).mp
      · apply (Nat.sub_eq_iff_eq_add ?_).mp
        · rfl
        · exact Nat.le_sub_of_add_le' kl
      · apply le_of_add_le_left
        exact kl
    rw [lrw]
    exact v1 k a
  intro k l kl
  exact v2 k l kl

/-
Just as we used Jₖ to define nₖ, we also use Jsₖ and Jtₖ to define
partial sum sequences wₖ' and wₖ, respectively.
(The reason wₖ corresponds to t is mostly historical)

The starting point w₀ = 1 is an artifact, as we will see it doesn't follow
nice properties we will soon see.
The real starting point of this sequence is w₁ = 1.
-/
noncomputable
def wₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ
| 0 => 1
| Nat.succ k => (wₖ s t k) + (Jtₖ s t k)

noncomputable
def wₖ' (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℕ
| 0 => 1
| Nat.succ k => (wₖ' s t k) + (Jsₖ s t k)

/-
wₖ and wₖ' are symmetric to each other
-/
lemma wₖ_symm (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
wₖ s t k = wₖ' t s k := by
  induction k with
  | zero =>
    unfold wₖ
    unfold wₖ'
    rfl
  | succ k prev =>
    unfold wₖ
    unfold wₖ'
    congr 1
    symm
    apply Jstₖ_symm

/-
Similarly, wₖ and wₖ' can be alternatively expressed using Jceiled.
However, this proof is much less trivial than the one for nₖ,
because some Jsₖ and Jtₖ can be 0 as they don't pass any lattice points.
-/
lemma wₖ_accum (s t: ℝ) (k: ℕ)  [PosReal s] [PosReal t]:
wₖ s t k = if k = 0 then 1 else 1 + Jceiled s t (δₖ s t (k - 1) - t) := by
 induction k with
  | zero => unfold wₖ; simp
  | succ k prev =>
    simp
    unfold wₖ
    -- Because w₀ = 1 is an artifact, the induction to w₁ needs special care
    by_cases k0: k = 0
    · rw [k0] at prev; simp at prev
      rw [k0]
      unfold wₖ
      apply add_left_cancel_iff.mpr
      unfold Jtₖ
      rw [δ₀]
      unfold Jline
      unfold Jceiled
      congr 1
      simp
      have empty: Λceiled s t (-t) = ∅ := by
        unfold Λceiled
        ext ⟨p, q⟩ ;
        simp
        apply lt_of_lt_of_le
        · show -t < 0
          apply neg_lt.mpr
          simp
          exact PosReal.pos
        · apply add_nonneg
          · apply mul_nonneg
            · exact Nat.cast_nonneg' p
            · apply le_of_lt
              exact PosReal.pos
          · apply mul_nonneg
            · exact Nat.cast_nonneg' q
            · apply le_of_lt
              exact PosReal.pos
      rw [empty]
      unfold Λline
      refine Set.preimage_eq_empty ?_
      apply Set.disjoint_iff_forall_ne.mpr
      intro a am b bm
      apply Set.eq_of_mem_singleton at am
      contrapose bm with eq
      simp at eq
      rw [am] at eq
      rw [← eq]
      unfold δₚ
      simp
      intro p q
      apply ne_of_gt
      apply lt_of_lt_of_le
      · show -t < 0
        apply neg_lt.mpr
        simp
        exact PosReal.pos
      · apply add_nonneg
        · apply mul_nonneg
          · exact Nat.cast_nonneg' p
          · apply le_of_lt
            exact PosReal.pos
        · apply mul_nonneg
          · exact Nat.cast_nonneg' q
          · apply le_of_lt
            exact PosReal.pos
    · simp [k0] at prev
      rw [prev]
      unfold Jtₖ
      rw [add_assoc]
      apply add_left_cancel_iff.mpr
      -- we need to discuss based on whether next Jtₖ passed new points
      rcases lt_trichotomy (δₖ s t k - t) (δnext s t (δₖ s t (k - 1) - t)) with lt|eq|gt
      -- case 1: Jtₖ contains no new points. We argue by showing the gap in δ
      · rw [← Jceiled_gap s t (δₖ s t (k - 1) - t) (δₖ s t k - t)]
        · simp
          unfold Jline
          have empty: (Λline s t (δₖ s t k - t)).toFinset = ∅ := by
            simp
            unfold Λline
            refine Set.preimage_eq_empty ?_
            apply Set.disjoint_of_subset
            · show {(δₖ s t k - t)} ⊆ {(δₖ s t k - t)}
              simp
            · show Set.range (δₚ s t) ⊆ Δ s t
              refine Set.range_subset_iff.mpr ?_
              intro ⟨p, q⟩
              unfold δₚ; unfold Δ; unfold is_δ
              simp
            · simp
              contrapose lt with isOnΛ
              simp
              simp at isOnΛ
              unfold δnext
              apply le_of_not_gt
              apply Set.IsWF.not_lt_min
              unfold Δfloored
              constructor
              · exact isOnΛ
              · simp
                apply (StrictMono.lt_iff_lt (δₖ_mono s t)).mpr
                simp
                exact Nat.zero_lt_of_ne_zero k0
          rw [empty]
          apply Finset.sum_empty
        · simp
          apply (StrictMono.le_iff_le (δₖ_mono s t)).mpr
          simp
        · exact lt
      -- case 2: Jtₖ contains new points, we can do simple accumulation
      · rw [eq]
        exact Jceiled_accum s t (δₖ s t (k - 1) - t)
      -- case 3: we somehow skipped over a valid δ. This is impossible
      · absurd gt
        simp
        set right := δnext s t (δₖ s t (k - 1) - t) + t with right_eq
        unfold δₖ
        set kprev := k - 1 with kprev_eq
        have k_is_succ: k = kprev + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero k0)
        rw [k_is_succ]
        simp
        unfold δnext
        rw [right_eq]
        apply le_of_not_gt
        apply Set.IsWF.not_lt_min
        unfold Δfloored
        constructor
        · have mem: δnext s t (δₖ s t kprev - t) ∈ Δ s t := by apply δnext_in_Δ
          unfold Δ at mem; unfold is_δ at mem
          simp at mem
          rcases mem with ⟨p, ⟨q, pq⟩⟩
          rw [← pq]
          unfold Δ; unfold is_δ
          simp
          use p, q+1
          push_cast
          ring
        · simp
          apply lt_add_of_sub_right_lt
          apply δnext_larger

lemma wₖ'_accum (s t: ℝ) (k: ℕ)  [PosReal s] [PosReal t]:
wₖ' s t k = if k = 0 then 1 else 1 + Jceiled s t (δₖ s t (k - 1) - s) := by
  rw [← wₖ_symm]
  rw [Jceiled_symm]
  rw [δₖ_symm]
  exact wₖ_accum t s k

/-
w₁ = w₁' = 1 is the real starting point of this sequence
-/
lemma w₁ (s t: ℝ) [PosReal s] [PosReal t]: wₖ s t 1 = 1 := by
  unfold wₖ
  unfold wₖ
  unfold Jtₖ
  rw [δ₀]
  simp
  unfold Jline
  have empty: Λline s t (-t) = ∅ := by
    unfold Λline
    apply Set.preimage_eq_empty
    apply Set.disjoint_iff_forall_ne.mpr
    intro a am b bm
    apply Set.eq_of_mem_singleton at am
    unfold Set.range at bm
    simp at bm
    rcases bm with ⟨p, q, cm⟩
    unfold δₚ at cm
    simp at cm
    have an: a < 0 := by
      apply neg_eq_iff_eq_neg.mpr at am
      have tp: t > 0 := by apply PosReal.pos
      rw [← am] at tp
      exact Left.neg_pos_iff.mp tp
    have bp: b >= 0 := by
      rw [← cm]
      apply add_nonneg
      · apply mul_nonneg
        · exact Nat.cast_nonneg' p
        · apply le_of_lt PosReal.pos
      · apply mul_nonneg
        · exact Nat.cast_nonneg' q
        · apply le_of_lt PosReal.pos
    linarith
  have empty': (Λline s t (-t)).toFinset = ∅ := by
    exact Set.toFinset_eq_empty.mpr empty
  rw [empty']
  exact rfl

lemma w₁' (s t: ℝ) [PosReal s] [PosReal t]: wₖ' s t 1 = 1 := by
  rw [← wₖ_symm]
  exact w₁ t s

/-
Recurrence formula of wₖ: by swapping s and t, w becomes n - w
This is the first property that shows w₀ doesn't follow the pattern.
A more sensible definition of w₀ that follows the Symmetry can be
 - w₀ = 1/2 when s = t
 - w₀ = c if s > t else 1 - c
But these definitions doesn't add much value to our further arguments,
so we will just leave w₀ semantically undefined.

(The equivalent formula "wₖ s t k + wₖ' s t k = nₖ s t k" might be more
suitable to be *the* recurrence formula. This is stated this way for
historical reasons)
-/
lemma wₖ_rec (s t: ℝ) (k: ℕ) (kh: k ≥ 1) [PosReal s] [PosReal t]:
wₖ s t k + wₖ t s k = nₖ s t k := by
  have symm(l: ℕ): wₖ s t (l + 1) + wₖ t s (l + 1) = nₖ s t (l + 1) := by
    induction l with
    | zero =>
      simp
      rw [w₁]; rw [w₁]
      unfold nₖ
      simp
      unfold nₖ; unfold Jₖ; unfold δₖ
      rw [Jline₀]
    | succ l lm =>
      unfold wₖ
      unfold nₖ
      rw [← add_assoc]; nth_rw 2 [add_assoc]; nth_rw 4 [add_comm]; rw [← add_assoc]
      rw [lm]
      rw [add_assoc]
      rw [add_left_cancel_iff.mpr]
      unfold Jₖ; unfold Jtₖ
      nth_rw 3 [Jline_rec]
      · nth_rw 2 [Jline_symm]
        nth_rw 2 [δₖ_symm]
        apply add_comm
      · rw [← δ₀ s t]
        apply ne_of_gt
        apply δₖ_mono
        exact Nat.zero_lt_succ l
  apply Nat.exists_eq_add_of_le' at kh
  rcases kh with ⟨l, lm⟩
  let s := symm l
  rw [← lm] at s
  exact s

/-
wₖ is always bounded between [1, nₖ - 1]. Because w₀ is undefined, we require k ≥ 1
-/
lemma wₖ_min' (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: wₖ s t k ≥ 1 := by
  induction k with
  | zero => unfold wₖ; trivial
  | succ l h =>
    unfold wₖ
    exact Nat.le_add_right_of_le h

lemma wₖ_min (s t: ℝ) (k: ℕ) (_: k ≥ 1) [PosReal s] [PosReal t]: wₖ s t k ≥ 1 := by
  apply wₖ_min' s t k

lemma wₖ_max (s t: ℝ) (k: ℕ) (kh: k ≥ 1) [PosReal s] [PosReal t]: wₖ s t k ≤ nₖ s t k - 1 := by
  rw [← wₖ_rec s t k kh]
  apply Nat.le_sub_one_of_lt
  apply Nat.lt_add_of_pos_right
  apply lt_of_le_of_lt' (wₖ_min t s k kh)
  trivial

/-
wₖ is also increasing but only weakly.
(The same is true for wₖ' but we omit the proof)
-/
lemma wₖ_mono (s t: ℝ) [PosReal s] [PosReal t]: Monotone (wₖ s t) := by
  have version1 (k a: ℕ): wₖ s t k ≤ wₖ s t (a + k) := by
    induction a with
    | zero =>
      simp
    | succ a prev =>
      apply le_trans
      · apply prev
      · rw [Nat.add_assoc]
        rw [Nat.add_comm 1 k]
        rw [← Nat.add_assoc]
        rw [Nat.add_one]
        rw [wₖ]
        apply Nat.le_add_right
  have version2 (k l: ℕ) (kl: k ≤ l): wₖ s t k ≤ wₖ s t l := by
    let a := l - k
    have lrw: l = a + k := by
      exact (Nat.sub_eq_iff_eq_add kl).mp rfl
    rw [lrw]
    exact version1 k a
  intro k l
  apply version2

/-
Here is a pretty important property of wₖ and wₖ':
Elements of wₖ and wₖ' sequence all come from nₖ.
This means wₖ and wₖ' effectively sets up mapping from nₖ to itself.
It can be showed that this mapping is weakly monotone and contracting,
and we will prove a weaker version of this later
-/
lemma wₖ_is_nₖ (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: ∃k', wₖ s t k = nₖ s t k' := by
  by_cases k0 : k = 0
  · use 0
    rw [k0]
    unfold wₖ
    unfold nₖ
    rfl
  · let K := k - 1
    have km1e: k = K + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero k0)
    rw [km1e]
    rw [wₖ_accum]
    simp
    have Δceiled_fintype: Fintype (Δceiled s t (δₖ s t K - t)) := by
      exact Fintype.ofFinite (Δceiled s t (δₖ s t K - t))
    by_cases ge0: δₖ s t K - t ≥ 0
    · have zeroIn: 0 ∈ Δceiled s t (δₖ s t K - t) := by
        unfold Δceiled
        constructor
        · exact δ0 s t
        · exact ge0
      have nonEmpty: Set.Nonempty (Δceiled s t (δₖ s t K - t)) := by
        refine Set.nonempty_of_mem zeroIn
      have nonEmpty': Finset.Nonempty (Δceiled s t (δₖ s t K - t)).toFinset := by
        exact Set.Aesop.toFinset_nonempty_of_nonempty nonEmpty
      rcases Finset.max_of_nonempty nonEmpty' with ⟨max: ℝ, maxEq⟩
      have mem: max ∈ (Δceiled s t (δₖ s t K - t)).toFinset := by
        exact Finset.mem_of_max maxEq
      have mem': max ∈ (Δceiled s t (δₖ s t K - t)) := by
        exact Set.mem_toFinset.mp mem
      have mem'': max ∈ Δ s t := by
        apply Set.mem_of_mem_of_subset mem'
        unfold Δceiled
        exact Set.inter_subset_left
      rcases δₖ_surjΔ s t max mem'' with ⟨k', k'eq⟩
      use k' + 1
      rw [nₖ_accum]
      simp
      rw [k'eq]
      unfold Jceiled
      congr 1
      simp
      apply subset_antisymm_iff.mpr
      constructor
      · unfold Λceiled
        simp
        intro p q mem
        apply Finset.le_max_of_eq ?_ maxEq
        simp
        unfold Δceiled
        constructor
        · unfold Δ; unfold is_δ
          simp
        · simp
          exact mem
      · unfold Λceiled
        simp
        intro p q mem
        unfold Δceiled at mem'
        have memle: max ∈ {δ | δ ≤ δₖ s t K - t} := by exact Set.mem_of_mem_inter_right mem'
        simp at memle
        apply le_trans mem memle
    · use 0
      unfold nₖ
      simp
      apply Jceiled_neg
      exact lt_of_not_ge ge0

lemma wₖ'_is_nₖ (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: ∃k', wₖ' s t k = nₖ s t k' := by
  rw [← wₖ_symm]
  rw [nₖ_symm]
  exact wₖ_is_nₖ t s k

/-
With sequence δₖ, nₖ, and wₖ introduced, we will construct the following functions:

First, the "cost differential" function dE(n): [1, ∞) → ℝ

    ↑ dE(n)
    |
    |     |-J₀-|-J₁--|---J₂---|-------J₃------|
    |
    |                                         |
δ₃--|--                       *===============∘
    |                         |
δ₂--|--              *========∘
    |                |
    |                |
δ₁--|--        *=====∘
    |          |
    |          |
δ₀--+-----*====∘-----|--------|---------------|--------→ n
    0     n₀   n₁    n₂       n₃              n₄
          (=1)

The function is defined like a stair case.
By convension, each interval is defined with left point closed:
dE( [nₖ, nₖ₊₁) ) = δₖ

Second, the "strategy" function w(n): [2, ∞) → P(ℝ).

    ↑ w(n)
    |
    |     |-J₀-|-J₁--|---J₂---|-------J₃------|
    |                                          /
w₄--|--                            *----------*-  --|--
    |                             /##########/      |
    |                            /##########/       |
    |                           /##########/        | Jt₃
    |                          /##########/         |
w₃--|--                *------*----------*        --|--
    |                 /######/                      | Jt₂
w₂--|--          *---*------*                     --|--
    |           /###/                               | Jt₁
w₁--|--        *---*                              --|--
    +----------|-----|--------|---------------|--------→ n
    0     n₀   n₁    n₂       n₃              n₄
          (=1) (=2)

We first anchor all points (n₁, w₁), (n₂, w₂), ...
and then connect them with parallelogram with an angle of 45°
The parallelogram can be degenerated if Jt = 0 or Jt = J.
Then all points enveloped, including the boundary, are in w(n)

Again, because w₀ is semantically undefined,
w(n) is only defined starting from n₁ = 2.

We also write w(n) = [wₘᵢₙ(n), wₘₐₓ(n)]

But before we can define these functions, we need to define
how to find k for a given real input n.

We define kceiled as the set of natural numbers k for which nₖ ≤ n.
-/

noncomputable
def kceiled (s t n: ℝ) [PosReal s] [PosReal t] :=
  {k: ℕ | nₖ s t k ≤ n}

/-
kceiled is also obviously symmetric and finite
-/
lemma kceiled_symm (s t n: ℝ) [PosReal s] [PosReal t]: kceiled s t n = kceiled t s n := by
  unfold kceiled
  rw [nₖ_symm]

instance kceiled_finite (s t n: ℝ) [PosReal s] [PosReal t]: Finite (kceiled s t n) := by
  by_cases npos: n ≥ 0
  · have sub: kceiled s t n ⊆ ℕceiled (Nat.ceil n) := by
      apply Set.subset_setOf.mpr
      rintro k kmem
      unfold kceiled at kmem
      simp at kmem
      contrapose kmem
      simp at kmem
      simp
      apply nₖ_mono s t at kmem
      apply lt_of_le_of_lt
      · show n ≤ nₖ s t (Nat.ceil n)
        apply le_trans
        · apply Nat.le_ceil
        · apply Nat.cast_le.mpr
          apply le_of_lt
          apply nₖ_grow
      · show (nₖ s t (Nat.ceil n) :ℝ) < nₖ s t k
        apply Nat.cast_lt.mpr
        exact kmem
    apply Finite.Set.subset (ℕceiled (Nat.ceil n)) sub
  · simp at npos
    have empty: (kceiled s t n) = ∅ := by
      apply Set.eq_empty_of_forall_not_mem
      intro x
      unfold kceiled
      simp
      apply lt_of_lt_of_le
      · apply npos
      · apply Nat.cast_nonneg'
    rw [empty]
    exact Finite.of_subsingleton

noncomputable instance (s t n: ℝ) [PosReal s] [PosReal t]:
Fintype (kceiled s t n) := by apply Fintype.ofFinite

/-
We can now find kₙ, the closest k for which nₖ ≤ n.
We can always find such k for n ≥ 1.
-/
noncomputable
def kₙ (s t n: ℝ) [PosReal s] [PosReal t] := (kceiled s t n).toFinset.max

/-
And obviously, it is also symmetrical
-/
lemma kₙ_symm (s t n: ℝ) [PosReal s] [PosReal t]: kₙ s t n = kₙ t s n := by
  unfold kₙ
  congr 1
  simp
  rw [kceiled_symm]

/-
kₙ and nₖ are basically inverse functions to each other.
One can recover the k by composing kₙ and nₖ .
-/
lemma kₙ_inv (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
kₙ s t (nₖ s t k) = some k := by
  unfold kₙ
  unfold kceiled
  apply finset_max_eq
  · simp
  · simp
    intro k'
    apply (StrictMono.le_iff_le (nₖ_mono s t)).mp

lemma kₙ_inv' (s t n: ℝ) (k: ℕ) [PosReal s] [PosReal t] (low: n ≥ nₖ s t k) (high: n < nₖ s t (k + 1)):
kₙ s t n = some k := by
  apply finset_max_eq
  · simp
    exact low
  · simp
    intro n n_le
    have nlt: nₖ s t n < nₖ s t (k + 1) := by
      rify
      apply lt_of_le_of_lt n_le
      exact high
    apply Nat.le_of_lt_add_one
    apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp
    exact nlt

/-
k₁ = 0 is the first non-empty kₙ. This corresponds to the fact n₀ = 1
-/
lemma k₁ (s t: ℝ) [PosReal s] [PosReal t]:
kₙ s t 1 = some 0 := by
  have n0: nₖ s t 0 = 1 := by rfl
  have k1: kₙ s t (nₖ s t 0) = some 0 := by exact kₙ_inv s t 0
  rw [n0] at k1
  rw [← k1]
  simp

/-
Any n ≥ 1 should give a valid k
-/
lemma kₙ_exist (s t n: ℝ) (np: n ≥ 1) [PosReal s] [PosReal t]:
∃k, kₙ s t n = some k := by
  unfold kₙ
  apply Finset.max_of_nonempty
  apply Set.Aesop.toFinset_nonempty_of_nonempty
  use 0
  unfold kceiled
  simp
  unfold nₖ
  rify
  exact np

/-
Mean while, n < 1 never gives a valid k
-/
lemma kₙ_not_exist (s t n: ℝ) (np: n < 1) [PosReal s] [PosReal t]: kₙ s t n = none := by
  unfold kₙ
  have empty: (kceiled s t n).toFinset = ∅ := by
    unfold kceiled
    simp
    apply Set.eq_empty_of_forall_not_mem
    intro k
    simp
    apply lt_of_lt_of_le np
    simp
    have n0: 1 = nₖ s t 0 := by exact rfl
    rw [n0]
    apply (StrictMono.le_iff_le (nₖ_mono s t)).mpr
    exact Nat.zero_le k
  rw [empty]
  rfl

/-
Now the cost differential function is defined by clamping to the nearest k and find δₖ
-/
noncomputable
def dE (s t: ℝ) [PosReal s] [PosReal t]: ℝ → ℝ := fun n ↦
  match kₙ s t n with
  | some k => δₖ s t k
  | none => 0

/-
... which is symmetric
-/
lemma dE_symm (s t n: ℝ) [PosReal s] [PosReal t]: dE s t n = dE t s n := by
  unfold dE
  rw [kₙ_symm]
  congr
  ext
  rw [δₖ_symm]

/-
... and weakly increasing
-/
lemma dE_mono (s t: ℝ) [PosReal s] [PosReal t]: Monotone (dE s t) := by
  unfold Monotone
  intro m n mnle
  unfold dE
  by_cases m1: m < 1
  · rw [kₙ_not_exist s t m m1]
    simp
    by_cases n1: n < 1
    · rw [kₙ_not_exist s t n n1]
    · simp at n1
      rcases kₙ_exist s t n n1 with ⟨k, keq⟩
      rw [keq]
      simp
      rw [← δ₀ s t]
      apply (StrictMono.le_iff_le (δₖ_mono s t)).mpr
      simp
  · simp at m1;
    rcases kₙ_exist s t m m1 with ⟨k, keq⟩
    have n1: n ≥ 1 := by apply ge_trans mnle m1
    rcases kₙ_exist s t n n1 with ⟨k', k'eq⟩
    rw [keq]
    rw [k'eq]
    simp
    apply (StrictMono.le_iff_le (δₖ_mono s t)).mpr
    unfold kₙ at keq
    unfold kₙ at k'eq
    have kne: Finset.Nonempty (kceiled s t m).toFinset := by
      unfold Finset.Nonempty
      use k
      exact Finset.mem_of_max keq
    have k'ne: Finset.Nonempty (kceiled s t n).toFinset := by
      unfold Finset.Nonempty
      use k'
      exact Finset.mem_of_max k'eq
    rw [← Finset.coe_max' kne] at keq
    rw [← Finset.coe_max' k'ne] at k'eq
    have keq: (kceiled s t m).toFinset.max' kne = k := by exact ENat.coe_inj.mp keq
    have k'eq: (kceiled s t n).toFinset.max' k'ne = k' := by exact ENat.coe_inj.mp k'eq
    rw [← keq]
    rw [← k'eq]
    apply Finset.max'_subset
    unfold kceiled
    simp
    intro k km
    apply le_trans km mnle

/-
The following three lemma show the nice property of wₖ when applied to dE:
The domain n ∈ [1, ∞) is divided by (wₖ k) and (wₖ (k + 1)) into three regions:
 - dE( [1,          wₖ k      ) ) < δₖ - t
 - dE( [wₖ k,       wₖ (k + 1)) ) = δₖ - t
 - dE( [wₖ (k + 1), ∞         ) ) > δₖ - t

In other words, wₖ captures exactly where dE = δₖ - t (while nₖ captures where dE = δₖ)

Note that because 1 ≤ wₖ k ≤ wₖ (k + 1) are week inequalities,
the intervals listed above can degenerate

There are similar properties with wₖ' and δₖ - s, but the proof is omitted
-/
lemma w_eq (s t w: ℝ) (k: ℕ) (kh: k ≥ 1) [PosReal s] [PosReal t]
(low: w ≥ wₖ s t k) (r: w < wₖ s t (k + 1)):
dE s t w = δₖ s t k - t := by
  have no_δ_between (k': ℕ) (δ: ℝ) (lower: δ > δₖ s t k' - t) (upper: δ < δₖ s t (k' + 1) - t):
  δ ∉ Δ s t := by
    by_contra mem
    have δtmem: δ + t ∈ Δ s t := by
      unfold Δ at mem; unfold is_δ at mem; simp at mem
      rcases mem with ⟨p, ⟨q, pq⟩⟩
      unfold Δ; unfold is_δ; simp
      use p, q+1
      rw [← pq]
      simp
      ring
    have δtmemfloor: δ + t ∈ Δfloored s t (δₖ s t k') := by
      unfold Δfloored; constructor
      · exact δtmem
      · simp
        exact lt_add_of_tsub_lt_right lower
    have δnext_smaller: δₖ s t (k' + 1) ≤ δ + t := by
      unfold δₖ; unfold δnext
      exact Set.IsWF.min_le _ _ δtmemfloor
    have δnext_smaller': δₖ s t (k' + 1) - t ≤ δ := by exact
      (OrderedSub.tsub_le_iff_right (δₖ s t (k' + 1)) t δ).mpr δnext_smaller
    have what: δₖ s t (k' + 1) - t < δₖ s t (k' + 1) - t := by apply lt_of_le_of_lt δnext_smaller' upper
    simp at what
  have δ_shift_mem: δₖ s t k - t ∈ Δ s t := by
    by_contra notmem
    have empty: (Λline s t (δₖ s t k - t)).toFinset = ∅ := by
      simp
      unfold Λline
      refine Set.preimage_eq_empty ?_
      apply Set.disjoint_iff_forall_ne.mpr
      intro a am b bm
      apply Set.eq_of_mem_singleton at am
      rw [← am] at notmem
      apply Set.mem_range.mp at bm
      rcases bm with ⟨pq, pqm⟩
      have bmm: b ∈ Δ s t := by
        rw [← pqm]
        unfold δₚ
        unfold Δ; unfold is_δ
        simp
      exact Ne.symm (ne_of_mem_of_not_mem bmm notmem)
    have zero: Jtₖ s t k = 0 := by
      unfold Jtₖ
      unfold Jline
      rw [empty]
      apply Finset.sum_empty
    have inter: wₖ s t k < wₖ s t (k + 1) := by
      rify
      exact lt_of_le_of_lt low r
    nth_rw 2 [wₖ.eq_def] at inter
    simp at inter
    rw [zero] at inter
    simp at inter
  rcases (δₖ_surjΔ s t (δₖ s t k - t) δ_shift_mem) with ⟨l, Leq⟩

  rw [wₖ_accum] at r
  simp at r
  rw [← Leq] at r
  have nₖ_accum_rw: (1:ℝ) + Jceiled s t (δₖ s t l) = nₖ s t (l + 1) := by
    rw [nₖ_accum]
    simp
  rw [nₖ_accum_rw] at r

  have left_eq: wₖ s t k = nₖ s t l := by
    let K := k - 1
    have km1e: k = K + 1 := by exact (Nat.sub_eq_iff_eq_add kh).mp rfl
    rw [wₖ_accum]
    rw [km1e]
    simp
    by_cases Leq0: l = 0
    · rw [Leq0]
      rw [nₖ_accum]
      simp
      rw [Leq0] at Leq
      rw [δ₀] at Leq
      apply Jceiled_neg
      rw [km1e] at Leq
      unfold δₖ at Leq
      rw [Leq]
      simp
      exact δnext_larger s t (δₖ s t K)
    · let L := l - 1
      have Lm1e: l = L + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero Leq0)
      rw [nₖ_accum]
      rw [Lm1e]
      simp
      rw [km1e] at Leq
      rw [Lm1e] at Leq
      unfold δₖ at Leq
      symm
      apply Jceiled_gap
      · by_contra Lgreater
        simp at Lgreater
        have h: δₖ s t K < δₖ s t L + t := by exact lt_add_of_tsub_lt_right Lgreater
        have Ltmem: δₖ s t L + t ∈ Δ s t := by
          rcases δₖ_in_Δ s t L with Lmem
          unfold Δ at Lmem; unfold is_δ at Lmem
          rcases Lmem with ⟨p, ⟨q, pq⟩⟩
          rw [← pq]
          unfold Δ; unfold is_δ; simp
          use p, q+1
          simp
          ring
        have LtinFloor: δₖ s t L + t ∈ Δfloored s t (δₖ s t K) := by
          unfold Δfloored; constructor
          · exact Ltmem
          · simp; exact h
        have Ltltnext: δₖ s t L + t ≥ δnext s t (δₖ s t K) := by
          unfold δnext
          exact Set.IsWF.min_le _ _ LtinFloor
        have Ltltnext': δₖ s t L ≥ δnext s t (δₖ s t K) - t := by exact
          (OrderedSub.tsub_le_iff_right (δnext s t (δₖ s t K)) t (δₖ s t L)).mpr Ltltnext
        rw [← Leq] at Ltltnext'
        have what: δₖ s t L < δₖ s t L := by
          apply lt_of_lt_of_le (δnext_larger s t (δₖ s t L)) Ltltnext'
        exact (lt_self_iff_false (δₖ s t L)).mp what
      · rw [Leq]
        simp
        exact δnext_larger s t (δₖ s t K)
  rw [left_eq] at low
  have gotk: kₙ s t w = some l := by
    unfold kₙ
    unfold kceiled
    apply finset_max_eq
    · simp
      exact low
    · simp
      intro n n_le
      have nlt: nₖ s t n < nₖ s t (l + 1) := by
        rify
        apply lt_of_le_of_lt n_le
        exact r
      apply Nat.le_of_lt_add_one
      apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp
      exact nlt

  unfold dE
  rw [gotk]
  simp
  exact Leq

lemma w_lt (s t w: ℝ) (k: ℕ) (kh: k ≥ 1) [PosReal s] [PosReal t]
(low: w ≥ 1) (high: w < wₖ s t k):
dE s t w < δₖ s t k - t := by
  let K := k - 1
  have km1e: k = K + 1 := by exact (Nat.sub_eq_iff_eq_add kh).mp rfl
  rw [wₖ_accum] at high
  rw [km1e] at high
  simp at high
  rw [km1e]

  unfold dE
  rcases kₙ_exist s t w low with ⟨l, leq⟩
  rw [leq]
  simp
  unfold kₙ at leq
  unfold kceiled at leq
  apply Finset.mem_of_max at leq
  simp at leq
  by_cases Leq0: l = 0
  · rw [Leq0]
    rw [δ₀]
    have low': w ≥ (1:ℝ) := by exact low
    have Jceiled_lt: 1 + (Jceiled s t (δₖ s t K - t)) > (1:ℝ) := by
      apply gt_of_gt_of_ge
      · exact high
      · exact low'
    simp at Jceiled_lt
    have nonneg: (δₖ s t K - t) ≥ 0 := by
      contrapose Jceiled_lt with Jceiled_zero
      simp
      apply Jceiled_neg
      exact lt_of_not_ge Jceiled_zero
    apply lt_of_le_of_lt nonneg
    simp
    rw [δₖ]
    exact δnext_larger s t (δₖ s t K)
  · let L := l - 1
    have lm1e: l = L + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero Leq0)
    rw [nₖ_accum] at leq
    rw [lm1e] at leq
    simp at leq
    have Jceiled_lt: (1:ℝ) + Jceiled s t (δₖ s t L) < 1 + Jceiled s t (δₖ s t K - t) := by
      apply lt_of_le_of_lt leq high
    simp at Jceiled_lt
    apply Jceiled_gap'' at Jceiled_lt
    rw [lm1e]
    rw [δₖ]
    apply lt_of_le_of_lt Jceiled_lt
    simp
    rw [δₖ]
    exact δnext_larger s t (δₖ s t K)


lemma w_gt (s t w: ℝ) (k: ℕ) [PosReal s] [PosReal t]
(low: w ≥ wₖ s t (k + 1)):
dE s t w > δₖ s t k - t := by
  have w1: w ≥ 1 := by
    apply ge_trans low
    simp
    apply wₖ_min s t (k + 1)
    simp
  unfold dE
  rcases kₙ_exist s t w w1 with ⟨l, leq⟩
  rw [leq]
  simp
  unfold kₙ at leq
  unfold kceiled at leq
  have l_greater: nₖ s t (l + 1) > w := by
    by_contra le
    simp at le
    have what: l + 1 ≤ l := by
      apply Finset.le_max_of_eq ?_ leq
      simp
      exact le
    simp at what

  have tr: nₖ s t (l + 1) > wₖ s t (k + 1)  := by
    rify
    apply gt_of_gt_of_ge
    · exact l_greater
    · exact low

  rw [wₖ_accum] at tr
  rw [nₖ_accum] at tr
  simp at tr
  exact Monotone.reflect_lt (Jceiled_mono s t) tr

/-
As a corollary, we show that wₖ is not only a monotone mapping from nₖ to itself,
but also under the mapping, wₖ(k) and wₖ(k + 1) are either same, or two nₖ(k') next to each other.
-/
lemma wₖ_is_nₖ_p1 (s t: ℝ) (k k': ℕ) [PosReal s] [PosReal t]
(keq: wₖ s t k = nₖ s t k') (wne: wₖ s t k ≠ wₖ s t (k + 1)): wₖ s t (k + 1) = nₖ s t (k' + 1) := by
  by_cases k0: k = 0
  · rw [k0] at wne
    simp at wne
    rw [w₁] at wne
    unfold wₖ at wne
    simp at wne
  · have kh: k ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr k0
    rcases wₖ_is_nₖ s t (k + 1) with ⟨k'p1, k'p1eq⟩
    rw [k'p1eq]
    congr
    have w_mono: wₖ s t k < wₖ s t (k + 1) := by
      apply lt_of_le_of_ne ?_ wne
      exact Nat.le.intro rfl
    have k_mono: k' < k'p1 := by
      apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp
      rw [← keq]
      rw [← k'p1eq]
      exact w_mono
    have k'notp2: k'p1 < k' + 2 := by
      by_contra k'p1gt
      simp at k'p1gt
      let k'mid := k' + 1
      have k'left: k' < k'mid := by exact lt_add_one k'
      have k'right: k'mid < k'p1 := by exact k'p1gt
      have nleft: nₖ s t k' < nₖ s t k'mid := by apply (nₖ_mono s t) k'left
      have nright: nₖ s t k'mid < nₖ s t k'p1 := by apply (nₖ_mono s t) k'right
      have deLeft: dE s t (nₖ s t k') < dE s t (nₖ s t k'mid) := by
        unfold dE
        rw [kₙ_inv]
        rw [kₙ_inv]
        simp
        unfold k'mid
        rw [δₖ]
        exact δnext_larger s t (δₖ s t k')
      have leftEq: dE s t (nₖ s t k') = δₖ s t k - t := by
        apply w_eq s t (nₖ s t k') k kh
        · exact le_of_eq (congrArg Nat.cast keq)
        · rw [k'p1eq]
          simp
          exact Nat.lt_trans nleft nright
      have midEq: dE s t (nₖ s t k'mid) = δₖ s t k - t := by
        apply w_eq s t (nₖ s t k'mid) k kh
        · rw [keq]
          simp
          exact Nat.le_of_succ_le nleft
        · rw [k'p1eq]
          simp
          exact nright
      rw [leftEq] at deLeft
      rw [midEq] at deLeft
      simp at deLeft
    exact Nat.eq_of_le_of_lt_succ k_mono k'notp2

/-
By symmetry, the same holds for wₖ'
-/
lemma wₖ'_is_nₖ_p1 (s t: ℝ) (k k': ℕ) [PosReal s] [PosReal t]
(keq: wₖ' s t k = nₖ s t k') (wne: wₖ' s t k ≠ wₖ' s t (k + 1)): wₖ' s t (k + 1) = nₖ s t (k' + 1) := by
  rw [← wₖ_symm] at keq
  rw [← wₖ_symm] at wne
  rw [← wₖ_symm] at wne
  rw [← wₖ_symm]
  rw [nₖ_symm] at keq
  rw [nₖ_symm]
  exact wₖ_is_nₖ_p1 t s k k' keq wne


/-
The strategy function w is defined by finding wₖ after clamping to the nearest k
The parallelogram is formed by taking certain min and max
-/
noncomputable
def wₘᵢₙ (s t n: ℝ) [PosReal s] [PosReal t]: ℝ :=
  match kₙ s t n with
  | some k => max (wₖ s t k) ((wₖ s t (k + 1)) + n - (nₖ s t (k + 1)))
  | none => 0

noncomputable
def wₘₐₓ (s t n: ℝ) [PosReal s] [PosReal t]: ℝ :=
  match kₙ s t n with
  | some k => min (wₖ s t (k + 1)) ((wₖ s t k) + n - (nₖ s t k))
  | none => 0

/-
Derived from wₖ_rec, we have "recurrence formula" between wₘᵢₙ and wₘₐₓ.
-/
lemma wₘₘ_rec (s t n: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]:
wₘᵢₙ s t n + wₘₐₓ t s n = n := by
  unfold wₘᵢₙ wₘₐₓ
  rw [kₙ_symm t s]
  have n1: n ≥ 1 := by apply ge_trans n2; simp
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  have k1: k ≥ 1 := by
    have mem: 1 ∈ (kceiled s t n).toFinset := by
      simp
      unfold kceiled
      simp
      rw [n₁]
      exact n2
    apply Finset.le_max_of_eq mem keq
  rw [keq]
  simp
  have k1rec: (wₖ t s (k + 1): ℝ) = nₖ s t (k + 1) - wₖ s t (k + 1) := by
    rw [← wₖ_rec s t (k + 1)]
    · simp
    · simp
  have krec: (wₖ t s k: ℝ) = nₖ s t k - wₖ s t k := by
    rw [← wₖ_rec s t k]
    · simp
    · exact k1
  rw [krec, k1rec]
  rw [nₖ_symm t s]
  have h1: (nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) = - ((wₖ s t (k + 1)) + n - (nₖ s t (k + 1))) + n := by
    ring
  have h2: (nₖ s t k: ℝ) - (wₖ s t k) + n - (nₖ s t k) = -(wₖ s t k) + n := by
    ring
  rw [h1]
  rw [h2]
  rw [← min_add]
  rw [min_neg_neg]
  rw [max_comm]
  simp

/-
Just like wₖ, w(n) is bounded within [1, n - 1]
-/
lemma wₘᵢₙ_min (s t n: ℝ) (h: n ≥ 2) [PosReal s] [PosReal t]: wₘᵢₙ s t n ≥ 1 := by
  unfold wₘᵢₙ
  have h1: n ≥ 1 := by linarith
  rcases kₙ_exist s t n h1 with ⟨k, kexist⟩
  rw [kexist]
  simp
  unfold kₙ at kexist
  left
  apply wₖ_min s t k
  have mem: 1 ∈ (kceiled s t n).toFinset := by
    simp
    unfold kceiled
    simp
    rw [n₁]
    exact h
  apply Finset.le_max_of_eq mem kexist

lemma wₘₐₓ_max (s t n: ℝ) (h: n ≥ 2) [PosReal s] [PosReal t]: wₘₐₓ s t n ≤ n - 1 := by
  unfold wₘₐₓ
  have h1: n ≥ 1 := by linarith
  rcases kₙ_exist s t n h1 with ⟨k, kexist⟩
  have k1: k ≥ 1 := by
    have mem: 1 ∈ (kceiled s t n).toFinset := by
      simp
      unfold kceiled
      simp
      rw [n₁]
      exact h
    apply Finset.le_max_of_eq mem kexist
  rw [kexist]
  simp
  right
  rw [add_comm]
  rw [add_comm_sub]
  apply add_le_add
  · trivial
  · have h2: wₖ s t k ≤ nₖ s t k - 1 := by
      apply wₖ_max s t k
      exact k1
    have nh : nₖ s t k > 1 := by
      rw [← n₀ s t]
      have h: StrictMono (nₖ s t) := by exact nₖ_mono s t
      apply h
      exact k1
    have lift: nₖ s t k - (1: ℝ) = ↑(nₖ s t k - 1) := by
      refine Eq.symm (Nat.cast_pred ?_)
      exact Nat.zero_lt_of_lt nh
    rw [lift]
    exact Nat.cast_le.mpr h2

/-
We also define a third kind of w function wₗᵢ,
which is the diagonals of parallelograms formed by wₘᵢₙ and wₘₐₓ
-/
noncomputable
def wₗᵢ (s t n: ℝ) [PosReal s] [PosReal t]: ℝ :=
  match kₙ s t n with
  | some k =>
    let a := (n - nₖ s t k) / (nₖ s t (k + 1) - nₖ s t k)
    (1 - a) * (wₖ s t k) + a * (wₖ s t (k + 1))
  | none => 0

/-
We also define the dual version wₗᵢ'
We could have done the same for wₘᵢₙ and wₘₐₓ,
but we omitted them as they don't add much value
-/
noncomputable
def wₗᵢ' (s t n: ℝ) [PosReal s] [PosReal t]: ℝ :=
  match kₙ s t n with
  | some k =>
    let a := (n - nₖ s t k) / (nₖ s t (k + 1) - nₖ s t k)
    (1 - a) * (wₖ' s t k) + a * (wₖ' s t (k + 1))
  | none => 0

/-
wₗᵢ as the diagnonal, is always between wₘᵢₙ and wₘₐₓ.
With this, we have the complete ordering:
1 ≤ wₘᵢₙ ≤ wₗᵢ ≤ wₘₐₓ ≤ n - 1
-/
def wₗᵢ_range (s t n: ℝ) [PosReal s] [PosReal t]:
wₘᵢₙ s t n ≤ wₗᵢ s t n ∧ wₗᵢ s t n ≤ wₘₐₓ s t n := by
  unfold wₘᵢₙ wₗᵢ wₘₐₓ
  by_cases n1: n ≥ 1
  · have n0: (n: ℝ) ≥ 0 := by apply ge_trans n1; simp
    rcases kₙ_exist s t n n1 with ⟨k, keq⟩
    have nle: nₖ s t k ≤ n := by
      unfold kₙ at keq
      have maxle: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
      unfold kceiled at maxle
      simp at maxle
      exact maxle
    have nge: nₖ s t (k + 1) ≥ n := by
      by_contra le
      simp at le
      apply le_of_lt at le
      have mem: k + 1 ∈ (kceiled s t n).toFinset := by
        unfold kceiled
        simp
        exact le
      unfold kₙ at keq
      have what: k + 1 ≤ k := by apply Finset.le_max_of_eq mem keq
      simp at what
    have wge: wₖ s t (k + 1) ≥ wₖ s t k := by exact Nat.le.intro rfl
    have wge': (wₖ s t (k + 1): ℝ) ≥ wₖ s t k := by exact Nat.cast_le.mpr wge
    have w'ge': (nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) - nₖ s t k + wₖ s t k ≥ 0 := by
      by_cases k0: k = 0
      · rw [k0]
        simp
        rw [w₁]
        unfold wₖ
        unfold nₖ
        simp
        unfold nₖ
        unfold Jₖ
        rw [δ₀]; rw [Jline₀]; simp
      · have k1: k ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr k0
        have k2: k + 1 ≥ 1 := by exact Nat.le_add_right_of_le k1
        rw [← wₖ_rec s t k k1]; rw [← wₖ_rec s t (k + 1) k2]
        simp
        rw [← sub_sub]
        rw [sub_right_comm]
        rw [sub_add]
        simp
        exact Nat.le.intro rfl
    have wnle: nₖ s t k * ((wₖ s t (k + 1): ℝ) - wₖ s t k) ≤ n * ((wₖ s t (k + 1): ℝ) - wₖ s t k) := by
      apply mul_le_mul nle
      · simp
      · exact sub_nonneg_of_le wge'
      · exact n0
    have wnle': nₖ s t (k + 1) * ((nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) - nₖ s t k + wₖ s t k) ≥ n * ((nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) - nₖ s t k + wₖ s t k) := by
      apply mul_le_mul nge
      · simp
      · exact w'ge'
      · simp
    have wnle'': nₖ s t (k + 1) * ((wₖ s t (k + 1): ℝ) - wₖ s t k) ≥ n * ((wₖ s t (k + 1): ℝ) - wₖ s t k) := by
      apply mul_le_mul nge
      · simp
      · exact sub_nonneg_of_le wge'
      · simp
    have wnle''': nₖ s t k * ((nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) - nₖ s t k + wₖ s t k) ≤ n * ((nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) - nₖ s t k + wₖ s t k) := by
      apply mul_le_mul nle
      · simp
      · exact w'ge'
      · exact n0
    simp [keq]
    have denogt: (nₖ s t (k + 1): ℝ) - nₖ s t k > 0 := by
      simp
      apply nₖ_mono
      simp
    have deno0: (nₖ s t (k + 1): ℝ) - nₖ s t k ≠ 0 := by
      apply ne_of_gt denogt
    constructor
    · constructor
      · field_simp
        refine (le_div_iff₀ denogt).mpr ?_
        linarith
      · field_simp
        refine (le_div_iff₀ denogt).mpr ?_
        linarith
    · constructor
      · field_simp
        refine (div_le_iff₀ denogt).mpr ?_
        linarith
      · field_simp
        refine (div_le_iff₀ denogt).mpr ?_
        linarith
  · simp at n1
    rcases kₙ_not_exist s t n n1 with knone
    simp [knone]

lemma wₘₘ_order (s t n: ℝ) [PosReal s] [PosReal t]:
wₘᵢₙ s t n ≤ wₘₐₓ s t n := by
  rcases wₗᵢ_range s t n with ⟨left, right⟩
  exact le_trans left right

/-
As usual, wₗᵢ is symmetric
-/
lemma wₗᵢ_symm (s t n: ℝ) [PosReal s] [PosReal t]:
wₗᵢ s t n = wₗᵢ' t s n := by
  unfold wₗᵢ wₗᵢ'
  rw [kₙ_symm s t]
  rw [nₖ_symm s t]
  congr
  ext k
  simp
  congr
  · exact wₖ_symm s t k
  · exact wₖ_symm s t (k + 1)

/-
... and has recurrence formula
-/
lemma wₗᵢ_rec (s t n: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]:
wₗᵢ s t n + wₗᵢ t s n = n := by
  have n1: n ≥ 1 := by
    apply ge_trans n2
    simp
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  have k1: k ≥ 1 := by
    have mem: 1 ∈ (kceiled s t n).toFinset := by
      simp
      unfold kceiled
      simp
      rw [n₁]
      exact n2
    apply Finset.le_max_of_eq mem keq
  have k0: k ≠ 0 := by exact Nat.not_eq_zero_of_lt k1
  have k2: k + 1 ≥ 1 := by exact Nat.le_add_right_of_le k1
  unfold wₗᵢ
  rw [kₙ_symm t s]
  rw [keq]
  simp
  rw [nₖ_symm t s]
  have wrec: wₖ t s k = nₖ s t k - wₖ s t k := by
    refine Nat.eq_sub_of_add_eq' ?_
    exact wₖ_rec s t k k1
  have wrec': wₖ t s (k + 1) = nₖ s t (k + 1) - wₖ s t (k + 1) := by
    refine Nat.eq_sub_of_add_eq' ?_
    exact wₖ_rec s t (k + 1) k2
  rw [wrec]
  rw [wrec']
  have denogt: (nₖ s t (k + 1): ℝ) - nₖ s t k > 0 := by
    simp
    apply nₖ_mono
    simp
  have deno0: (nₖ s t (k + 1): ℝ) - nₖ s t k ≠ 0 := by
    apply ne_of_gt denogt
  have cast1: ((nₖ s t k - wₖ s t k: ℕ) : ℝ) = (nₖ s t k: ℝ) - wₖ s t k := by
    refine Nat.cast_sub ?_
    rw [wₖ_accum, nₖ_accum]
    simp [k0]
    apply Jceiled_mono
    simp
    apply le_of_lt
    exact PosReal.pos
  have cast2: ((nₖ s t (k + 1) - wₖ s t (k + 1): ℕ) : ℝ) = (nₖ s t (k + 1): ℝ) - wₖ s t (k + 1) := by
    refine Nat.cast_sub ?_
    rw [wₖ_accum, nₖ_accum]
    simp
    apply Jceiled_mono
    simp
    apply le_of_lt
    exact PosReal.pos
  rw [cast1, cast2]
  field_simp
  ring


/-
We define the "strategy evaluation differential function"
dD(n, w) = dE(w) - dE(n - w) + t - s
-/
noncomputable
def dD (s t n: ℝ) [PosReal s] [PosReal t]: ℝ → ℝ := fun w ↦ dE s t w - dE s t (n - w) + t - s

/-
It is symmetric
-/
lemma dD_symm (s t n w: ℝ) [PosReal s] [PosReal t]:
dD s t n w = -dD t s n (n - w) := by
  unfold dD
  rw [dE_symm s t]
  rw [dE_symm s t]
  ring_nf

/-
... and weakly increasing w.r.t w
-/
lemma dD_mono (s t n: ℝ) [PosReal s] [PosReal t]: Monotone (dD s t n) := by
  unfold Monotone
  intro a b able
  unfold dD
  have h1: dE s t a ≤ dE s t b := by apply dE_mono s t able
  have h2: dE s t (n - a) ≥ dE s t (n - b) := by
    apply dE_mono s t
    exact tsub_le_tsub_left able n
  refine tsub_le_tsub ?_ (le_refl s)
  refine add_le_add  ?_ (le_refl t)
  apply tsub_le_tsub h1 h2

/-
We show that wₘᵢₙ and wₘₐₓ indicates where dD is negative, zero, or positive.

In these theorems, we conviniently ignored boundary points at w = wₘᵢₙ or w = wₘₐₓ.
dD value at those points can be found, but it doesn't add much value for our further arguments.
-/
theorem dD_zero (s t n: ℝ) (h: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w > wₘᵢₙ s t n) (rightBound: w < wₘₐₓ s t n):
dD s t n w = 0 := by
  have n1: n ≥ 1 := by
    refine le_trans ?_ h
    exact one_le_two
  have w1: w ≥ 1 := by
    apply le_trans (wₘᵢₙ_min s t n h)
    apply le_of_lt leftBound
  have wn: n - w ≥ 1 := by
    apply le_sub_comm.mp
    refine le_trans ?_ (wₘₐₓ_max s t n h)
    apply le_of_lt rightBound
  rcases kₙ_exist s t n n1 with ⟨kl, kltop⟩
  unfold wₘᵢₙ at leftBound
  rw [kltop] at leftBound
  simp at leftBound
  rcases leftBound with ⟨lw, lnw⟩
  unfold wₘₐₓ at rightBound
  rw [kltop] at rightBound
  simp at rightBound
  rcases rightBound with ⟨rw, rnw⟩
  have kl1: kl ≥ 1 := by
    unfold kₙ at kltop
    refine Finset.le_max_of_eq ?_ kltop
    simp
    unfold kceiled
    simp
    rw [n₁]
    exact h
  have k1rel: dE s t w = δₖ s t kl - t := by
    apply w_eq s t w
    · exact kl1
    · exact le_of_lt lw
    · exact rw
  have k2rel: dE s t (n - w) = δₖ s t kl - s := by
    rw [δₖ_symm]
    rw [dE_symm]
    apply w_eq t s (n - w)
    · exact kl1
    · rw [← wₖ_rec] at rnw
      simp at rnw
      apply le_of_lt at rnw
      exact le_sub_comm.mp rnw
      exact kl1
    · rw [← wₖ_rec] at lnw
      simp at lnw
      exact sub_lt_comm.mp lnw
      exact Nat.le_add_right_of_le kl1
  unfold dD
  rw [k1rel]
  rw [k2rel]
  simp

theorem dD_neg (s t n: ℝ) (h: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w > 1) (rightBound: w < wₘᵢₙ s t n):
dD s t n w < 0 := by
  have n1: n ≥ 1 := by
    refine le_trans ?_ h
    exact one_le_two
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  have k1: k ≥ 1 := by
    unfold kₙ at keq
    refine Finset.le_max_of_eq ?_ keq
    simp
    unfold kceiled
    simp
    rw [n₁]
    exact h

  unfold dD
  unfold wₘᵢₙ at rightBound
  rw [keq] at rightBound
  simp at rightBound

  unfold kₙ at keq
  have kmem: k ∈ (kceiled s t n).toFinset := by
    exact Finset.mem_of_max keq
  unfold kceiled at kmem
  simp at kmem

  have symm: nₖ s t k - wₖ s t k = (wₖ t s k: ℝ) := by
    apply sub_eq_of_eq_add
    rw [← wₖ_rec s t k k1]
    push_cast
    apply add_comm
  have symm': nₖ s t (k + 1) - wₖ t s (k + 1) = (wₖ s t (k + 1): ℝ) := by
    apply sub_eq_of_eq_add
    rw [← wₖ_rec s t (k + 1) (Nat.le_add_right_of_le k1)]
    push_cast
    simp

  rcases rightBound with right|right
  · have lt: dE s t w < δₖ s t k - t := by
      apply w_lt s t w k k1 (le_of_lt leftBound) right
    have symmBound: n - w > nₖ s t k - wₖ s t k := by
      apply lt_of_le_of_lt
      · show n - wₖ s t k ≥ nₖ s t k - wₖ s t k
        simp
        exact kmem
      · show n - w > n - wₖ s t k
        simp
        exact right
    rw [symm] at symmBound
    have lt2: dE s t (n - w) ≥ δₖ s t k - s := by
      rw [dE_symm]
      rw [δₖ_symm]
      by_cases thre: n - w < wₖ t s (k + 1)
      · apply ge_of_eq
        apply w_eq t s (n - w) k k1 (le_of_lt symmBound) thre
      · simp at thre
        apply le_of_lt
        apply w_gt t s (n - w) k thre
    linarith
  · have lt: dE s t (n - w) > δₖ s t k - s := by
      rw [dE_symm]
      rw [δₖ_symm]
      refine w_gt t s (n - w) k ?_
      rw [← symm'] at right
      linarith
    have lt2: dE s t w ≤ δₖ s t k - t := by
      by_cases thre: w < wₖ s t k
      · apply le_of_lt
        apply w_lt s t w k k1 (le_of_lt leftBound) thre
      · simp at thre
        apply le_of_eq
        refine w_eq s t w k k1 thre ?_
        apply lt_trans right
        have nlt: n < nₖ s t (k + 1) := by
          by_contra ge
          simp at ge
          have h: (k + 1) ∈ kceiled s t n := by
            unfold kceiled
            simp; exact ge
          have h': (k + 1) ∈ (kceiled s t n).toFinset := by
            simp
            exact h
          have what: k + 1 ≤ k := by exact Finset.le_max_of_eq h' keq
          simp at what
        linarith
    linarith


theorem dD_pos (s t n: ℝ) (h: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w > wₘₐₓ s t n) (rightBound: w < n - 1):
dD s t n w > 0 := by
  rw [dD_symm]
  simp
  apply dD_neg
  · exact h
  · exact lt_tsub_comm.mp rightBound
  · have wrec: wₘₐₓ s t n = n - wₘᵢₙ t s n := by
      nth_rw 2 [← wₘₘ_rec t s n h]
      simp
    rw [wrec] at leftBound
    exact sub_lt_comm.mp leftBound


/-
Let's also show that dE and dD are integrable, which will be soon used
-/
lemma dE_integrable (s t m n: ℝ) [PosReal s] [PosReal t]:
IntervalIntegrable (dE s t) MeasureTheory.volume m n := by
  apply Monotone.intervalIntegrable (dE_mono s t)

/-
Here is a more useful version with the correction term s + t
-/
lemma dE_integrable' (s t m n: ℝ) [PosReal s] [PosReal t]:
IntervalIntegrable (fun x ↦ (dE s t x) + s + t) MeasureTheory.volume m n := by
  have ti: IntervalIntegrable (fun x ↦ t)  MeasureTheory.volume m n := by
    apply intervalIntegrable_const
  have si: IntervalIntegrable (fun x ↦ s)  MeasureTheory.volume m n := by
    apply intervalIntegrable_const

  apply IntervalIntegrable.add ?_ ti
  apply IntervalIntegrable.add ?_ si
  apply dE_integrable

lemma dD_integrable (s t n w1 w2: ℝ) [PosReal s] [PosReal t]:
IntervalIntegrable (dD s t n) MeasureTheory.volume w1 w2 := by
  apply Monotone.intervalIntegrable (dD_mono s t n)

/-

Now we can construct our main function, the cost function E(n)

    ↑ E(n)
    |
    |     |-J₀-|-J₁--|---J₂---|-------J₃------|
    |
    |                                        ·*   --|--
    |                                      ··       |
    |                                     ·         |
    |                                    ·          |
    |                                  ··           |
    |                                 ·             |
    |                                ·              | (δ₃+s+t)*J₃
    |                              ··               |
    |     |    |     |        |   ·                 |
    |     |    |     |        |  ·                  |
    |     |    |     |        | ·                   |
E₃--|--   |    |     |      ··*·---               --|--
    |     |    |     |     ·                        |
    |     |    |     |   ··                         | (δ₂+s+t)*J₂
    |     |    |     | ··                           |
E₂--|--   |    |    ·*·------------               --|--
    |     |    |   ·                                |
    |     |    | ··                                 | (δ₁+s+t)*J₁
E₁--|--   |   ·*·------------------               --|--
    |     | ··                                      | (δ₀+s+t)*J₀
E₀--+-----*·---|-----|--------|---------------|-----|--→ n
    0     n₀   n₁    n₂       n₃              n₄
          (=1)

-/

/-
We first pin the vertices Eₖ on this function
-/
noncomputable
def Eₖ (s t: ℝ) [PosReal s] [PosReal t]: ℕ → ℝ
| 0 => 0
| Nat.succ k => (Eₖ s t k) + (Jₖ s t k) * (δₖ s t k + s + t)

/-
... which is symmetric
-/
lemma Eₖ_symm (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
Eₖ s t k = Eₖ t s k := by
  induction k with
  | zero => rfl
  | succ k prev =>
    unfold Eₖ
    rw [prev]
    rw [Jₖ_symm]
    rw [δₖ_symm]
    rw [add_right_comm]

/-
Eₖ can be alternatively expressed as integrating dE between vertices
-/
lemma Eₖ_integral (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
Eₖ s t k = ∫ x in (1: ℝ)..(nₖ s t k), dE s t x + s + t := by
 induction k with
 | zero =>
   unfold Eₖ
   unfold nₖ
   simp
 | succ k prev =>
    unfold Eₖ
    rw [prev]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (dE_integrable' s t 1 (nₖ s t k))
      (dE_integrable' s t (nₖ s t k) (nₖ s t (k + 1)))
    ]
    simp
    have const_integ: (Jₖ s t k) * (δₖ s t k + s + t) =
      ∫ n in (nₖ s t k: ℝ)..(nₖ s t (k + 1): ℝ), (δₖ s t k + s + t) := by
      rw [intervalIntegral.integral_const]
      rw [nₖ]
      push_cast
      simp
    rw [const_integ]
    apply intervalIntegral.integral_congr_ae
    have nle: (nₖ s t k: ℝ) ≤ (nₖ s t (k + 1): ℝ) := by
      simp
      exact Nat.le.intro rfl
    rw [Set.uIoc_of_le nle]

    have ico: ∀ (n : ℝ), n ∈ Set.Ico (nₖ s t k: ℝ) (nₖ s t (k + 1): ℝ)
    → δₖ s t k + s + t = dE s t n + s + t := by
      rintro n ⟨low, high⟩
      simp
      unfold dE
      rw [kₙ_inv' s t n k low high]

    rw [← MeasureTheory.ae_restrict_iff',
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc.symm,
      MeasureTheory.ae_restrict_iff']
    · exact .of_forall ico
    · simp
    · simp

/-
We then define E(n) as linear interpolation between Eₖ
-/
noncomputable
def E (s t: ℝ) [PosReal s] [PosReal t]: ℝ → ℝ := fun n ↦
  match kₙ s t n with
  | some k => Eₖ s t k + (n - nₖ s t k) * (δₖ s t k + s + t)
  | none => 0

/-
... which is symmetric
-/
lemma E_symm (s t n: ℝ) [PosReal s] [PosReal t]: E s t n = E t s n := by
  unfold E
  rw [kₙ_symm]
  congr
  ext
  rw [Eₖ_symm]
  rw [nₖ_symm]
  rw [δₖ_symm]
  rw [add_right_comm]

/-
... and can be expressed as an integral
-/
lemma E_integral (s t n: ℝ) (n1: n ≥ 1) [PosReal s] [PosReal t]:
E s t n = ∫ x in (1: ℝ)..n, dE s t x + s + t := by
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  unfold E
  rw [keq]
  simp
  rw [Eₖ_integral]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (dE_integrable' s t 1 (nₖ s t k))
    (dE_integrable' s t (nₖ s t k) n)
  ]
  simp
  have const_integ: (n - nₖ s t k) * (δₖ s t k + s + t) =
    ∫ n in (nₖ s t k: ℝ)..(n: ℝ), (δₖ s t k + s + t) := by
    rw [intervalIntegral.integral_const]
    simp
  rw [const_integ]
  apply intervalIntegral.integral_congr
  unfold Set.EqOn
  intro x xmem
  unfold kₙ at keq
  have kmem: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
  unfold kceiled at kmem
  simp at kmem
  rw [Set.uIcc_of_le kmem] at xmem
  rcases xmem with ⟨low, high⟩
  simp
  apply le_antisymm
  · have left: δₖ s t k = dE s t (nₖ s t k) := by
      unfold dE
      rw [kₙ_inv]
    rw [left]
    apply dE_mono s t
    exact low
  · have left: dE s t x ≤ dE s t n := by
      apply dE_mono s t
      exact high
    have right: δₖ s t k = dE s t n := by
      unfold dE
      unfold kₙ
      rw [keq]
    rw [right]
    exact left

/-
While E(n) itself is defined as partial sum of Jₖ * (δₖ + s + t),
we can also show the composed mapping E(w(n)) is the partial sum of Jtₖ * (δₖ + s)
-/
lemma Ew_accum (s t: ℝ) (k: ℕ) (k1: k ≥ 1) [PosReal s] [PosReal t]:
E s t (wₖ s t k) + (Jtₖ s t k) * (δₖ s t k + s) = E s t (wₖ s t (k + 1)) := by
  by_cases zero_interval: wₖ s t k = wₖ s t (k + 1)
  · rw [zero_interval]
    simp
    left
    rw [wₖ] at zero_interval
    unfold Jtₖ at zero_interval
    simp at zero_interval
    exact zero_interval
  · rcases wₖ_is_nₖ s t k with ⟨k', k'eq⟩
    rcases wₖ_is_nₖ_p1 s t k k' k'eq zero_interval with k'p1eq
    rw [k'eq]
    rw [k'p1eq]
    unfold E
    rw [kₙ_inv]
    rw [kₙ_inv]
    simp
    rw [Eₖ]
    simp
    have dEeq: dE s t (wₖ s t k) = δₖ s t k - t := by
      apply w_eq
      · exact k1
      · simp
      · simp
        apply lt_of_le_of_ne ?_ zero_interval
        apply (wₖ_mono s t)
        exact Nat.le_add_right k 1
    unfold dE at dEeq
    rw [k'eq] at dEeq
    rw [kₙ_inv] at dEeq
    simp at dEeq
    congr 1
    · simp
      unfold Jtₖ
      rw [← dEeq]
      rfl
    · rw [dEeq]
      ring

/-
Symmetrically E(w'(n)) is the partial sum of Jsₖ * (δₖ + t)
-/
lemma Ew'_accum (s t: ℝ) (k: ℕ) (k1: k ≥ 1) [PosReal s] [PosReal t]:
E s t (wₖ' s t k) + (Jsₖ s t k) * (δₖ s t k + t) = E s t (wₖ' s t (k + 1)) := by
  rw [E_symm]
  rw [← wₖ_symm]
  rw [Jstₖ_symm]
  rw [δₖ_symm]
  nth_rw 2 [E_symm]
  rw [← wₖ_symm]
  exact Ew_accum t s k k1

/-
And here is the strategy evaluation function
-/
noncomputable
def D (s t n w: ℝ) [PosReal s] [PosReal t] := E s t w + E s t (n - w) + t * w + s * (n - w)

/-
... which is symmetric
-/
lemma D_symm (s t n w: ℝ) [PosReal s] [PosReal t]:
D s t n w = D t s n (n - w) := by
  unfold D
  rw [E_symm s t]
  rw [E_symm s t]
  ring_nf

/-
... and is the integral of the strategy evaluation differential function
-/
lemma D_integral (s t n w1 w2: ℝ) (w1low: w1 ≥ 1) (w1high: w1 ≤ n - 1) (w2low: w2 ≥ 1) (w2high: w2 ≤ n - 1)
[PosReal s] [PosReal t]:
D s t n w2 - D s t n w1 = ∫ w in w1..w2, dD s t n w := by
  unfold D
  unfold dD
  have right: ∫ w in w1..w2, dE s t w - dE s t (n - w) + t - s =
    ∫ w in w1..w2, (dE s t w + s + t) - (dE s t (n - w) + s + t) + (t - s) := by
       apply intervalIntegral.integral_congr
       unfold Set.EqOn
       intro x xmem
       simp
       ring
  rw [right]
  have integ0: IntervalIntegrable (fun w ↦ dE s t (n - w) + s + t) MeasureTheory.volume w1 w2 := by
    apply Antitone.intervalIntegrable
    unfold Antitone
    intro a b able
    simp
    apply dE_mono
    linarith
  have integ1: IntervalIntegrable (fun w ↦ (dE s t w + s + t) - (dE s t (n - w) + s + t)) MeasureTheory.volume w1 w2 := by
    apply IntervalIntegrable.sub (dE_integrable' s t w1 w2) integ0
  have integ2: IntervalIntegrable (fun w ↦ (t - s)) MeasureTheory.volume w1 w2 := by
    apply intervalIntegrable_const
  rw [intervalIntegral.integral_add integ1 integ2]
  rw [intervalIntegral.integral_sub (dE_integrable' s t w1 w2) integ0]
  rw [intervalIntegral.integral_const]
  rw [E_integral s t w1 w1low]
  rw [E_integral s t w2 w2low]
  rw [E_integral s t (n - w1) (le_sub_comm.mp w1high)]
  rw [E_integral s t (n - w2) (le_sub_comm.mp w2high)]
  rw [← intervalIntegral.integral_interval_sub_left (dE_integrable' s t 1 w2) (dE_integrable' s t 1 w1)]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ dE s t x + s + t)]
  rw [← intervalIntegral.integral_interval_sub_left (dE_integrable' s t 1 (n - w1)) (dE_integrable' s t 1 (n - w2))]
  simp
  ring

/-
We will now prove several version of the recurrence formula on E
-/
lemma Eₖ_rec (s t: ℝ) [PosReal s] [PosReal t]:
∀k: ℕ, 1 ≤ k →
Eₖ s t k = E s t (wₖ s t k) + E s t (wₖ' s t k) +
           t *   (wₖ s t k) + s *   (wₖ' s t k) := by
  apply Nat.le_induction
  · rw [w₁]
    rw [w₁']
    unfold E
    simp
    rw [k₁]
    simp
    unfold nₖ
    simp
    unfold Eₖ
    unfold Eₖ
    unfold Jₖ
    rw [δ₀]
    rw [Jline₀]
    ring
  · intro k k1 prev
    unfold Eₖ
    rw [prev]
    rw [← Ew_accum _ _ _ k1]
    rw [← Ew'_accum _ _ _ k1]
    rw [wₖ]
    rw [wₖ']
    rw [Jstₖ_rec _ _ _ k1]
    push_cast
    ring

lemma Eₖ_lerp (s t: ℝ) (k: ℕ) (a: ℝ) (low: a ≥ 0) (high: a ≤ 1) [PosReal s] [PosReal t]:
E s t ((1 - a) * (nₖ s t k) + a * (nₖ s t (k + 1))) = (1 - a) * (Eₖ s t k) + a * (Eₖ s t (k + 1)) := by
  by_cases a1: a = 1
  · rw [a1]
    simp
    unfold E
    rw [kₙ_inv]
    simp
  · have keq: kₙ s t ((1 - a) * (nₖ s t k) + a * (nₖ s t (k + 1))) = some k := by
      unfold kₙ
      unfold kceiled
      apply finset_max_eq
      · simp
        apply le_add_of_sub_left_le
        have onem: nₖ s t k = (1:ℝ) * nₖ s t k := by exact Eq.symm (one_mul ((nₖ s t k):ℝ))
        nth_rw 1 [onem]
        rw [← sub_mul]
        simp
        refine mul_le_mul_of_nonneg ?_ ?_ low ?_
        · simp
        · simp
          exact Nat.le.intro rfl
        · simp
      · intro n mem
        simp at mem
        rw [sub_mul] at mem
        rw [sub_add] at mem
        rw [← mul_sub] at mem
        have lt: nₖ s t n < 1 * (nₖ s t k) - (((nₖ s t k): ℝ) - (nₖ s t (k + 1))) := by
          apply lt_of_le_of_lt mem
          apply sub_lt_sub_left
          rw [← neg_sub]
          rw [mul_neg]
          apply neg_lt_neg
          apply (mul_lt_iff_lt_one_left ?_).mpr
          · exact lt_of_le_of_ne high a1
          · simp
            apply nₖ_mono
            simp
        simp at lt
        apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp at lt
        exact Nat.le_of_lt_succ lt
    unfold E
    rw [keq]
    simp
    rw [Eₖ]
    rw [nₖ]
    push_cast
    ring

lemma Ewₖ_lerp (s t: ℝ) (k: ℕ) (a: ℝ) (low: a ≥ 0) (high: a ≤ 1) [PosReal s] [PosReal t]:
E s t ((1 - a) * (wₖ s t k) + a * (wₖ s t (k + 1))) = (1 - a) * (E s t (wₖ s t k)) + a * (E s t (wₖ s t (k + 1))) := by
  rcases wₖ_is_nₖ s t k with ⟨k', k'eq⟩
  by_cases wne: wₖ s t k ≠ wₖ s t (k + 1)
  · rcases wₖ_is_nₖ_p1 s t k k' k'eq wne with k'p1eq
    rw [k'eq]
    rw [k'p1eq]
    nth_rw 2 [E]
    nth_rw 2 [E]
    rw [kₙ_inv]
    rw [kₙ_inv]
    simp
    exact Eₖ_lerp s t k' a low high
  · simp at wne
    rw [← wne]
    ring_nf

lemma Ewₖ'_lerp (s t: ℝ) (k: ℕ) (a: ℝ) (low: a ≥ 0) (high: a ≤ 1) [PosReal s] [PosReal t]:
E s t ((1 - a) * (wₖ' s t k) + a * (wₖ' s t (k + 1))) = (1 - a) * (E s t (wₖ' s t k)) + a * (E s t (wₖ' s t (k + 1))) := by
  rw [← wₖ_symm]; rw [← wₖ_symm];
  rw [E_symm]; nth_rw 2 [E_symm]; nth_rw 3 [E_symm]
  exact Ewₖ_lerp t s k a low high


lemma Eₖ_rec_lerp (s t: ℝ) (k: ℕ) (a: ℝ) (k1: k ≥ 1) (low: a ≥ 0) (high: a ≤ 1) [PosReal s] [PosReal t]:
E s t ((1 - a) * (nₖ s t k) + a * (nₖ s t (k + 1))) =
E s t ((1 - a) * (wₖ s t k) + a * (wₖ s t (k + 1))) + E s t ((1 - a) * (wₖ' s t k) + a * (wₖ' s t (k + 1))) +
t *   ((1 - a) * (wₖ s t k) + a * (wₖ s t (k + 1))) + s *   ((1 - a) * (wₖ' s t k) + a * (wₖ' s t (k + 1))) := by
  rw [Eₖ_lerp s t k a low high]
  rw [Ewₖ_lerp s t k a low high]
  rw [Ewₖ'_lerp s t k a low high]
  rw [Eₖ_rec s t k k1]
  rw [Eₖ_rec]
  ring
  exact Nat.le_add_right_of_le k1

/-
Eventually, we reached the major conclusion:
The cost equals the strategy evaluation at the optimal strategy wₗᵢ
-/
lemma E_wₗᵢ (s t n: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]:
E s t n = D s t n (wₗᵢ s t n) := by
  have rec: n - wₗᵢ s t n = wₗᵢ' s t n := by
    nth_rw 1 [← wₗᵢ_rec s t n n2]
    rw [wₗᵢ_symm t s]
    simp
  unfold D
  rw [rec]
  have n1: n ≥ 1 := by
    apply ge_trans n2
    simp
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  unfold wₗᵢ
  unfold wₗᵢ'
  rw [keq]
  simp
  have denogt: (nₖ s t (k + 1): ℝ) - nₖ s t k > 0 := by
    simp
    apply nₖ_mono
    simp
  have deno0: (nₖ s t (k + 1): ℝ) - nₖ s t k ≠ 0 := by
    apply ne_of_gt denogt
  have neq: n = (1 - (n - nₖ s t k) / (nₖ s t (k + 1) - nₖ s t k)) * (nₖ s t k)
    + ((n - nₖ s t k) / (nₖ s t (k + 1) - nₖ s t k)) * (nₖ s t (k + 1)) := by
    rw [← div_self deno0 ]
    rw [← sub_div]
    rw [div_mul_eq_mul_div]
    rw [div_mul_eq_mul_div]
    rw [← add_div]
    apply (eq_div_iff deno0).mpr
    ring
  nth_rw 1 [neq]
  apply Eₖ_rec_lerp
  · unfold kₙ at keq
    refine Finset.le_max_of_eq ?_ keq
    simp
    unfold kceiled
    simp
    rw [n₁]
    exact n2
  · apply div_nonneg ?_ (le_of_lt denogt)
    simp
    rcases Finset.mem_of_max keq with mem
    unfold kceiled at mem
    simp at mem
    exact mem
  · apply (div_le_one denogt).mpr
    simp
    by_contra gt
    simp at gt
    apply le_of_lt at gt
    unfold kₙ at keq
    have k1: k + 1 ∈ (kceiled s t n).toFinset := by exact Set.mem_toFinset.mpr gt
    have k1lmax : k + 1 ≤ k := by exact Finset.le_max_of_eq k1 keq
    simp at k1lmax

/-
But because D has flat derivative dD between wₘᵢₙ and wₘₐₓ
all w in between gives cost = strategy evaluation
-/
lemma E_w (s t n w: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w ≥ wₘᵢₙ s t n) (rightBound: w ≤ wₘₐₓ s t n):
E s t n = D s t n w := by
  rw [E_wₗᵢ s t n n2]
  apply eq_of_sub_eq_zero
  rcases wₗᵢ_range s t n with ⟨wₗᵢleftBound, wₗᵢrightBound⟩
  have w1: w ≥ 1 := by apply ge_trans leftBound (wₘᵢₙ_min s t n n2)
  have wn1: w ≤ n - 1 := by apply le_trans rightBound (wₘₐₓ_max s t n n2)
  have wli1: wₗᵢ s t n ≥ 1 := by apply ge_trans wₗᵢleftBound (wₘᵢₙ_min s t n n2)
  have wlin1: wₗᵢ s t n ≤ n -1 := by apply le_trans wₗᵢrightBound (wₘₐₓ_max s t n n2)
  rw [D_integral _ _ _ _ _ w1 wn1 wli1 wlin1]
  apply intervalIntegral.integral_zero_ae
  unfold Set.uIoc
  rw [← MeasureTheory.ae_restrict_iff',
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm,
    MeasureTheory.ae_restrict_iff']
  · refine .of_forall ?_
    rintro x ⟨low, high⟩
    have xlow: wₘᵢₙ s t n < x := by
      simp at low
      rcases low with h|h
      · apply lt_of_le_of_lt leftBound h
      · apply lt_of_le_of_lt wₗᵢleftBound h
    have xhigh: x < wₘₐₓ s t n := by
      simp at high
      rcases high with h|h
      · apply lt_of_lt_of_le h rightBound
      · apply lt_of_lt_of_le h wₗᵢrightBound
    exact dD_zero s t n n2 xlow xhigh
  · simp
  · simp

/-
And using the fact that the derivative dD is negative/positive outside the range,
we conclude that the strategy evaluation is larger than the cost everywhere else.
-/
lemma E_wₘᵢₙ (s t n w: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w ≥ 1) (rightBound: w < wₘᵢₙ s t n):
E s t n < D s t n w := by
  have minrefl: wₘᵢₙ s t n ≥ wₘᵢₙ s t n := by apply le_refl
  have minmax: wₘᵢₙ s t n ≤ wₘₐₓ s t n := by
    rcases wₗᵢ_range s t n with ⟨wₗᵢleftBound, wₗᵢrightBound⟩
    apply le_trans wₗᵢleftBound wₗᵢrightBound
  have minup: wₘᵢₙ s t n ≤ n - 1 := by
    apply le_trans minmax
    apply wₘₐₓ_max s t n n2
  have wn1: w < n - 1 := by apply lt_of_lt_of_le rightBound minup
  have wn1': w ≤ n - 1 := by apply le_of_lt wn1
  rw [E_w s t n (wₘᵢₙ s t n) n2 minrefl minmax]
  apply lt_of_sub_neg
  rw [D_integral _ _ _ _ _ leftBound wn1' (wₘᵢₙ_min s t n n2) minup]
  apply neg_of_neg_pos
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply IntervalIntegrable.neg
    apply dD_integrable
  · rintro x ⟨xleft, xright⟩
    simp
    apply dD_neg s t n n2
    · apply gt_of_gt_of_ge xleft leftBound
    · exact xright
  · exact rightBound

lemma E_wₘₐₓ (s t n w: ℝ) (n2: n ≥ 2) [PosReal s] [PosReal t]
(leftBound: w > wₘₐₓ s t n) (rightBound: w ≤ n - 1):
E s t n < D s t n w := by
  have w_rec: wₘₐₓ s t n = n - wₘᵢₙ t s n := by
    nth_rw 2 [← wₘₘ_rec t s n n2]
    simp
  rw [E_symm]
  rw [D_symm]
  have leftBound': n - w ≥ 1 := by exact le_sub_comm.mp rightBound
  have rightBound': n - w < wₘᵢₙ t s n := by
    rw [w_rec] at leftBound
    exact sub_lt_comm.mp leftBound
  exact E_wₘᵢₙ t s n (n - w) n2 leftBound' rightBound'

/-
Therefore, the interval bounded by wₘᵢₙ and wₘₐₓ idicates where E = D.
Let's make it its own function
-/
def wₛₑₜ (s t: ℝ) [PosReal s] [PosReal t]: ℝ → Set ℝ :=
  fun n ↦ Set.Icc (wₘᵢₙ s t n) (wₘₐₓ s t n)

/-
Let's summarize our result in a high level

For any possible cost function E(n): [1, ∞) → ℝ
We can define a strategy evaluation function StratEval{E}(n, w)

A cost function E is called optimal if the min value of StratEval is E itself,
and a strategy function w is called optimal if it is the set for StratEval to reach E.
-/

def StratEval (Efun: ℝ → ℝ) (s t n w: ℝ) :=
  Efun w + Efun (n - w) + t * w + s * (n - w)

def HasMin (s: Set ℝ) (m: ℝ): Prop := m ∈ s ∧ ∀ a ∈ s, a ≥ m

def IsOptimalCost (Efun: ℝ → ℝ) (s t: ℝ): Prop :=
  ∀ n ≥ 2, HasMin ((StratEval Efun s t n) '' (Set.Icc 1 (n - 1))) (Efun n)

def IsOptimalStrat (Efun: ℝ → ℝ) (wfun: ℝ → Set ℝ) (s t: ℝ): Prop :=
  ∀ n ≥ 2, ∀ w ∈ (Set.Icc 1 (n - 1)), StratEval Efun s t n w = Efun n ↔ w ∈ wfun n

/-
Then obviously the E and w function we have constructed are optimal
-/
theorem E_IsOptimalCost (s t: ℝ) [PosReal s] [PosReal t]:
IsOptimalCost (E s t) s t := by
  unfold IsOptimalCost
  intro n n2
  unfold HasMin
  unfold StratEval
  constructor
  · simp
    use wₘᵢₙ s t n
    constructor
    · constructor
      · exact wₘᵢₙ_min s t n n2
      · exact le_trans (wₘₘ_order s t n) (wₘₐₓ_max s t n n2)
    · have refl: wₘᵢₙ s t n ≥ wₘᵢₙ s t n := by simp
      obtain ew := E_w s t n (wₘᵢₙ s t n) n2 refl (wₘₘ_order s t n)
      unfold D at ew
      exact ew.symm
  · simp
    intro d w low high eq
    have deq: d = D s t n w := by exact id (Eq.symm eq)
    rw [deq]
    by_cases wlow: w < wₘᵢₙ s t n
    · apply le_of_lt
      apply E_wₘᵢₙ s t n w n2 low wlow
    · by_cases whigh: w ≤ wₘₐₓ s t n
      · simp at wlow
        apply le_of_eq
        apply E_w s t n w n2 wlow whigh
      · simp at whigh
        apply le_of_lt
        apply E_wₘₐₓ s t n w n2 whigh high

theorem W_IsOptimalStrat (s t: ℝ) [PosReal s] [PosReal t]:
IsOptimalStrat (E s t) (wₛₑₜ s t) s t := by
  unfold IsOptimalStrat
  unfold StratEval
  simp
  intro n n2 w wlow whigh
  have deq: E s t w + E s t (n - w) + t * w + s * (n - w) = D s t n w := by rfl
  rw [deq]
  constructor
  · contrapose
    rintro range
    rcases (Decidable.not_and_iff_or_not.mp range) with h|h
    · simp at h;
      apply ne_of_gt
      exact E_wₘᵢₙ s t n w n2 wlow h
    · simp at h;
      apply ne_of_gt
      exact E_wₘₐₓ s t n w n2 h whigh
  · rintro ⟨low, high⟩
    exact Eq.symm (E_w s t n w n2 low high)

/-
Finally, we want to lift our E and w to integers,
which is the domain of the original question.
-/

noncomputable
def Eℤ (s t: ℝ) [PosReal s] [PosReal t]: ℤ → ℝ :=
fun n ↦ E s t n

noncomputable
def wₘᵢₙℤ (s t: ℝ) [PosReal s] [PosReal t]: ℤ → ℤ :=
fun n ↦ match kₙ s t n with
  | some k => max (wₖ s t k) ((wₖ s t (k + 1)) + n - (nₖ s t (k + 1)))
  | none => 0

noncomputable
def wₘₐₓℤ (s t: ℝ) [PosReal s] [PosReal t]: ℤ → ℤ :=
fun n ↦ match kₙ s t n with
  | some k => min (wₖ s t (k + 1)) ((wₖ s t k) + n - (nₖ s t k))
  | none => 0

/-
While Eℤ is easy to understand, we need to show that
wₘᵢₙℤ and wₘₐₓℤ remains the same value when lifted
-/
lemma wₘᵢₙℤeq (s t: ℝ) (n: ℤ) [PosReal s] [PosReal t]:
wₘᵢₙℤ s t n = wₘᵢₙ s t n := by
  unfold wₘᵢₙℤ wₘᵢₙ
  by_cases n1: (n: ℝ) < 1
  · rw [kₙ_not_exist s t n n1]
    simp
  · have n1: (n: ℝ) ≥ 1 := by exact le_of_not_lt n1
    rcases kₙ_exist s t n n1 with ⟨k, keq⟩
    rw [keq]
    simp

lemma wₘₐₓℤeq (s t: ℝ) (n: ℤ) [PosReal s] [PosReal t]:
wₘₐₓℤ s t n = wₘₐₓ s t n := by
  unfold wₘₐₓℤ wₘₐₓ
  by_cases n1: (n: ℝ) < 1
  · rw [kₙ_not_exist s t n n1]
    simp
  · have n1: (n: ℝ) ≥ 1 := by exact le_of_not_lt n1
    rcases kₙ_exist s t n n1 with ⟨k, keq⟩
    rw [keq]
    simp

noncomputable
def wℤ (s t: ℝ) [PosReal s] [PosReal t]: ℤ → Set ℤ :=
fun n ↦ Set.Icc (wₘᵢₙℤ s t n) (wₘₐₓℤ s t n)

/-
We can then define the integer version of the optimal criteria,
and proof the optimality of Eℤ and Wℤ
-/
def StratEvalℤ (Efun: ℤ → ℝ) (s t: ℝ) (n w: ℤ) :=
  Efun w + Efun (n - w) + t * w + s * (n - w)

def IsOptimalCostℤ (Efun: ℤ → ℝ) (s t: ℝ): Prop :=
  ∀ n ≥ 2, HasMin ((StratEvalℤ Efun s t n) '' (Set.Icc 1 (n - 1))) (Efun n)

def IsOptimalStratℤ (Efun: ℤ → ℝ) (wfun: ℤ → Set ℤ) (s t: ℝ): Prop :=
  ∀ n ≥ 2, ∀ w ∈ (Set.Icc 1 (n - 1)), StratEvalℤ Efun s t n w = Efun n ↔ w ∈ wfun n

theorem Eℤ_IsOptimalCost (s t: ℝ) [PosReal s] [PosReal t]:
IsOptimalCostℤ (Eℤ s t) s t := by
  unfold IsOptimalCostℤ
  intro n n2
  rify at n2
  unfold HasMin
  unfold StratEvalℤ
  constructor
  · simp
    use wₘᵢₙℤ s t n
    constructor
    · constructor
      · rify
        rw [wₘᵢₙℤeq]
        exact wₘᵢₙ_min s t n n2
      · rify
        rw [wₘᵢₙℤeq]
        exact le_trans (wₘₘ_order s t n) (wₘₐₓ_max s t n n2)
    · have refl: wₘᵢₙ s t n ≥ wₘᵢₙ s t n := by simp
      obtain ew := E_w s t n (wₘᵢₙ s t n) n2 refl (wₘₘ_order s t n)
      unfold D at ew
      unfold Eℤ
      push_cast
      rw [wₘᵢₙℤeq]
      exact ew.symm
  · simp
    intro d w low high eq
    rify at low
    rify at high
    have deq: d = D s t n w := by
      unfold Eℤ at eq
      push_cast at eq
      exact id (Eq.symm eq)
    rw [deq]
    by_cases wlow: w < wₘᵢₙ s t n
    · apply le_of_lt
      apply E_wₘᵢₙ s t n w n2 low wlow
    · by_cases whigh: w ≤ wₘₐₓ s t n
      · simp at wlow
        apply le_of_eq
        apply E_w s t n w n2 wlow whigh
      · simp at whigh
        apply le_of_lt
        apply E_wₘₐₓ s t n w n2 whigh high

theorem Wℤ_IsOptimalStrat (s t: ℝ) [PosReal s] [PosReal t]:
IsOptimalStratℤ (Eℤ s t) (wℤ s t) s t := by
  unfold IsOptimalStratℤ
  unfold StratEvalℤ
  simp
  intro n n2 w wlow whigh
  rify at n2
  rify at wlow
  rify at whigh
  unfold Eℤ
  push_cast
  have deq: E s t w + E s t (n - w) + t * w + s * (n - w) = D s t n w := by rfl
  rw [deq]
  constructor
  · contrapose
    rintro range
    rcases (Decidable.not_and_iff_or_not.mp range) with h|h
    · simp at h;
      rify at h
      rw [wₘᵢₙℤeq] at h
      apply ne_of_gt
      exact E_wₘᵢₙ s t n w n2 wlow h
    · simp at h;
      rify at h
      rw [wₘₐₓℤeq] at h
      apply ne_of_gt
      exact E_wₘₐₓ s t n w n2 h whigh
  · rintro ⟨low, high⟩
    rify at low
    rw [wₘᵢₙℤeq] at low
    rify at high
    rw [wₘₐₓℤeq] at high
    exact Eq.symm (E_w s t n w n2 low high)

/-
And finally, Eℤ is the unique optimal function with starting point of Eℤ(1) = 0
-/
theorem Eℤ₁ (s t: ℝ) [PosReal s] [PosReal t]: Eℤ s t 1 = 0 := by
  unfold Eℤ
  unfold E
  simp
  rw [k₁]
  simp
  unfold Eₖ
  rw [n₀]
  rw [δ₀]
  simp

lemma HasMinEq (s: Set ℝ) (m n: ℝ) (mMin: HasMin s m) (nMin: HasMin s n): m = n := by
  unfold HasMin at mMin
  unfold HasMin at nMin
  rcases mMin with ⟨mmem, mle⟩
  rcases nMin with ⟨nmem, nle⟩
  apply le_antisymm
  · apply mle n nmem
  · apply nle m mmem

theorem Eℤ_Unique (s t: ℝ) (Efun: ℤ → ℝ) [PosReal s] [PosReal t]
(E1: Efun 1 = 0) (opt: IsOptimalCostℤ Efun s t):
∀n ≥ 1, Efun n = Eℤ s t n := by
  have alt: ∀n ≥ 1, ∀m, m ≥ 1 → m ≤ n → Efun m = Eℤ s t m := by
    apply Int.le_induction
    · intro m m1 m1'
      have meq: m = 1 := by exact Eq.symm (Int.le_antisymm m1 m1')
      rw [meq]
      rw [E1, Eℤ₁]
    · intro n n1 prev
      intro m m1 mlenp1
      by_cases mlen: m ≤ n
      · exact prev m m1 mlen
      · have n12: n + 1 ≥ 2 := by exact Int.le_add_of_neg_add_le_right n1
        simp at mlen
        have meq: m = n + 1 := by exact Int.le_antisymm mlenp1 mlen
        rw [meq]
        obtain EFunOpt := opt (n + 1) n12
        simp at EFunOpt
        obtain Eℤopt := Eℤ_IsOptimalCost s t (n + 1) n12
        simp at Eℤopt
        have StratEq: StratEvalℤ Efun s t (n + 1) '' Set.Icc 1 n = StratEvalℤ (Eℤ s t) s t (n + 1) '' Set.Icc 1 n := by
          refine Set.image_congr ?_
          simp
          intro w wlow whigh
          unfold StratEvalℤ
          simp
          congr
          · apply prev w wlow whigh
          · apply prev (n + 1 - w)
            · refine Int.le_sub_left_of_add_le ?_
              simp
              apply whigh
            · simp
              apply wlow
        rw [StratEq] at EFunOpt
        apply HasMinEq _ _ _ EFunOpt Eℤopt

  intro n n1
  apply alt n n1 n n1
  exact Int.le_refl n
