import BiasedBisect.Basic

/-
In this file, we prove a family of "inert" theorems.
The w function, along with many underlying structures, demonstrate a behavior
where for a fixed n, the function value doesn't change along s/t line within a small interval
Such interval is always between a pair of Farey neighbours.

To be specific, for positive integers a, b, c, and d such that ad - bc = 1,
and for all s and t usch that c/d < s/t < a/b,
the w function is a constant as long as n isn't too large (we will find the bound for n soon)

We will use such tuple (a, b, c, d) a lot in the following theorems, which we call an inert interval.

Intuitively, changing s/t slightly is to rotate the scanning line over Λ a little bit.
When such rotation doesn't hit any lattice points, a lot of functions we have constructed stay constant.
-/

/-
We start with a simple lemma: for rational s/t, the scanning line can pass multiple points,
but this can only happen after the (s * t) threshold.
-/
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

/- The property of Farey neighbors: a new fraction between a Farey neighbor must have a large denominator -/
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

/-
Some inert theorems on Λceiled:
below the threshold, one can slightly rotate the ceiling without changing the set members.

We divide the proof into three parts:
 - Λceiled_inert_half: only look at one side of the delta area
 - Λceiled_inert: prove for the full set, but requires an ordering between two ceilings
 - Λceiled_inert': remove the requirement on the ordering
-/
theorem Λceiled_inert_half (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ) [PosReal s1] [PosReal t1]
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

lemma Λceiled_inert (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ)
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
      · exact Λceiled_inert_half a b c d s1 t1 s2 t2 p q det left mid right pBound p' q' qless pmore
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
      exact Λceiled_inert_half d c b a t2 s2 t1 s1 q p det' right mid' left qBound q' p' pless qmore

lemma Λceiled_inert' (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p q: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(pBound: p < b + d) (qBound: q < a + c):
Λceiled s1 t1 (p * s1 + q * t1) = Λceiled s2 t2 (p * s2 + q * t2) := by
  rcases lt_trichotomy (s1 * t2) (s2 * t1) with lt|eq|gt
  · exact Eq.symm (Λceiled_inert a b c d s2 t2 s1 t1 p q det left2 lt right1 pBound qBound)
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
    apply Λceiled_homo s1 t1 (p * s1 + q * t1) l
  · exact Λceiled_inert a b c d s1 t1 s2 t2 p q det left1 gt right2 pBound qBound

/-
The δₚ evaluation is inert within the threshold,
as in the ordering doesn't change for changing s/t
-/
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
    refine Λceiled_inert' a b c d s1 t1 s2 t2 p1 q1 det left1 right1 left2 right2 p1Bound q1Bound
  have right: Λceiled s1 t1 (δₚ s1 t1 (p2, q2)) = Λceiled s2 t2 (δₚ s2 t2 (p2, q2)) := by
    unfold δₚ
    refine Λceiled_inert' a b c d s1 t1 s2 t2 p2 q2 det left1 right1 left2 right2 p2Bound q2Bound
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

/-
A variation of Λceiled_inert, concering about a ceiling created by lattice point below ℕ
This will be used for w related theories
-/
lemma Λceiled_inert_t (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left: a * t1 > b * s1) (mid: s1 * t2 > s2 * t1) (right: d * s2 > c * t2)
(pBound: p < b + d):
Λceiled s1 t1 (p * s1 - t1) = Λceiled s2 t2 (p * s2 - t2) := by
  unfold Λceiled
  ext ⟨p', q'⟩
  simp
  by_cases pless: p' < p
  · have rewr (s t: ℝ): p' * s + q' * t ≤ p * s - t ↔ (q' + 1: ℕ) * t ≤ (p - p': ℕ) * s := by
      rw [Nat.cast_sub (le_of_lt pless)]
      push_cast
      constructor
      repeat
        intro h
        linarith
    rw [rewr s1 t1]
    rw [rewr s2 t2]
    set dp := p - p'
    set dq := q' + 1
    have dpBound: dp < b + d := by
      unfold dp
      exact tsub_lt_of_lt pBound
    have dp0: dp > 0 := by
      unfold dp
      simp
      exact pless
    have dq0: dq > 0 := by
      unfold dq
      simp
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
  · simp at pless
    apply iff_of_false
    repeat
      simp
      rw [sub_eq_add_neg]
      apply add_lt_add_of_le_of_lt
      · apply (mul_le_mul_right PosReal.pos).mpr
        simp; exact pless
      · apply lt_of_lt_of_le
        · apply neg_neg_of_pos
          exact PosReal.pos
        · apply mul_nonneg
          · simp
          · apply le_of_lt PosReal.pos

/- again Λceiled_inert_t' removes the ordering requirement -/
lemma Λceiled_inert_t' (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (p: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(pBound: p < b + d):
Λceiled s1 t1 (p * s1 - t1) = Λceiled s2 t2 (p * s2 - t2) := by
  rcases lt_trichotomy (s1 * t2) (s2 * t1) with lt|eq|gt
  · exact Eq.symm (Λceiled_inert_t a b c d s2 t2 s1 t1 p det left2 lt right1 pBound)
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
    rw [← mul_assoc]
    rw [mul_comm _ l]
    rw [mul_assoc]
    rw [← mul_sub]
    apply Λceiled_homo s1 t1 (p * s1 - t1) l
  · exact Λceiled_inert_t a b c d s1 t1 s2 t2 p det left1 gt right2 pBound

/-
The mediant of Farey neighbors is within the inert interval
-/
lemma abcdLeftRight (a b c d: ℕ+) (det: a * d = b * c + 1):
(a: ℝ) * (b + d) > b * (a + c) ∧ (d: ℝ) * (a + c) > c * (b + d) := by
  constructor
  · norm_cast
    rw [mul_add, mul_add]
    rw [det]
    rw [mul_comm]
    rw [← add_assoc]
    exact PNat.lt_add_right (a * b + b * c) 1
  · norm_cast
    rw [mul_add, mul_add]
    rw [mul_comm d a]
    rw [det]
    rw [mul_comm c b]
    rw [mul_comm c d]
    rw [add_assoc]
    rw [add_comm 1]
    rw [← add_assoc]
    exact PNat.lt_add_right (b * c + d * c) 1

/-
δₖ sequence is inert within an inert interval.
This version is a bit primitive, where it requires a sequence of lattice points
that generates δₖ to exist first, and we don't have an explicit bound yet
-/
lemma δₖ_inert (a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (kbound: ℕ) (pqₖ: ℕ → ℕ × ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
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
    obtain ⟨abcd1, abcd2⟩ := abcdLeftRight a b c d det
    have pqBound's2: δₚ s2 t2 (pqₖ (k + 1)) < s2 * (b + d) := by
      by_contra ge
      simp at ge
      have mem: ((b + d: ℕ), 0) ∈ Λceiled s2 t2 ((pqₖ (k + 1)).1 * s2 + (pqₖ (k + 1)).2 * t2) := by
        unfold Λceiled
        simp
        rw [mul_comm]
        exact ge
      rw [Λceiled_inert' a b c d s2 t2 (a + c) (b + d) (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
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
      rw [Λceiled_inert' a b c d s2 t2 (a + c) (b + d) (pqₖ (k + 1)).1 (pqₖ (k + 1)).2
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
      have p's2: (p':ℝ) * s2 < s2 * (b + d) := by
        apply lt_of_add_lt_of_nonneg_left pq's2
        apply mul_nonneg
        · simp
        · exact le_of_lt (PosReal.pos)
      have q't2: (q':ℝ) * t2 < t2 * (a + c) := by
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

/-
Here we have series of little lemma to eventually prove the cardinality of
all lattice points in an inert interval
-/

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

def ΛtriangleFinset (a b c d: ℕ+) :=
  Finset.biUnion (Finset.range (b + d)) (fun p ↦ {p} ×ˢ Finset.range ((((a + c) * (b + d - p) + (b + d - 1))) / (b + d)))

/- We could have just use the finiteness, but having a computable one is useful -/
instance ΛtriangleFintype (a b c d: ℕ+): Fintype (Λtriangle a b c d) := by
  apply Fintype.ofFinset (ΛtriangleFinset a b c d)
  intro pq
  unfold Λtriangle ΛtriangleFinset
  simp
  constructor
  · rintro ⟨p', p'b, q', ⟨q'b, eq⟩⟩
    rw [← eq]
    simp
    have qb: q' * (b + d) < (a + c) * (b + d - p') + (b + d - 1) - (b + d - 1) := by
      apply (Nat.lt_div_iff_mul_lt ?_).mp q'b
      simp
    have qb2: q' * (b + d) < (a + c) * (b + d - p') := by
      convert qb using 1
      symm
      apply Nat.add_sub_self_right
    have h: p' * (a + c) + q' * (b + d) < p' * (a + c) + (a + c) * (b + d - p') := by
      exact Nat.add_lt_add_left qb2 (p' * (a + c))
    nth_rw 3 [mul_comm] at h
    rw [← mul_add] at h
    convert h using 2
    zify [p'b]
    ring
  · intro mem
    use pq.1
    constructor
    · apply Nat.lt_of_add_right_lt at mem
      rw [mul_comm] at mem
      exact Nat.lt_of_mul_lt_mul_left mem
    · use pq.2
      constructor
      · rw [mul_comm] at mem
        rw [add_comm] at mem
        apply Nat.lt_sub_of_add_lt at mem
        rw [← Nat.mul_sub] at mem
        have h: ((a + c) * (b + d - pq.1): ℕ) = (a + c) * (b + d - pq.1) + (b + d - 1) - (b + d - 1) := by
          symm
          apply Nat.add_sub_self_right
        rw [h] at mem
        apply (Nat.lt_div_iff_mul_lt ?_).mpr ?_
        · simp
        · exact mem
      · simp

noncomputable
instance ΛtriangleDecidable (a b c d: ℕ+): DecidablePred fun x ↦ x ∈ Λtriangle a b c d := by
  apply Classical.decPred


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

def BoundDecomposite (p q: ℕ) (h: p * (a + c) + q * (b + d) < (a + c) * (b + d)):
    p < b + d ∧ q < a + c := by
    constructor
    · obtain h' := lt_of_add_lt_of_nonneg_left h (Nat.zero_le _)
      rw [mul_comm] at h'
      apply lt_of_mul_lt_mul_left h' (Nat.zero_le _)
    · obtain h' := lt_of_add_lt_of_nonneg_right h (Nat.zero_le _)
      apply lt_of_mul_lt_mul_right h' (Nat.zero_le _)

lemma ΛtriangleCardEq (a b c d: ℕ+): (Λtriangle a b c d).toFinset.card = (ΛtriangleUpper a b c d).toFinset.card := by
  apply Finset.card_nbij (fun ⟨p, q⟩ ↦ ⟨b + d - p, a + c - q⟩ )
  · unfold Λtriangle ΛtriangleUpper Λrectangle
    rintro ⟨p, q⟩
    simp
    intro mem
    constructor
    · obtain ⟨pb, qb⟩ := BoundDecomposite p q mem
      rw [Nat.sub_mul, Nat.sub_mul]
      rw [← Nat.add_sub_assoc]
      · rw [← Nat.sub_add_comm]
        · rw [Nat.sub_sub]
          apply Nat.lt_sub_iff_add_lt.mpr
          rw [mul_comm]
          apply Nat.add_lt_add_left
          nth_rw 3 [mul_comm]
          exact mem
        · refine Nat.mul_le_mul_right (a + c) ?_
          exact Nat.le_of_lt pb
      · refine Nat.mul_le_mul_right (b + d) ?_
        exact Nat.le_of_lt qb
    · constructor
      · exact lt_of_le_of_lt (Nat.sub_le (b + d) p) (Nat.lt_add_one (b + d))
      · exact lt_of_le_of_lt (Nat.sub_le (a + c) q) (Nat.lt_add_one (a + c))
  · unfold Set.InjOn Λtriangle
    simp
    intro p q mem p2 q2 mem2 pp qq
    obtain ⟨pb, qb⟩ := BoundDecomposite p q mem
    obtain ⟨p2b, q2b⟩ := BoundDecomposite p2 q2 mem2
    constructor
    · zify at pp
      rw [Nat.cast_sub (le_of_lt pb)] at pp
      rw [Nat.cast_sub (le_of_lt p2b)] at pp
      simp at pp
      exact pp
    · zify at qq
      rw [Nat.cast_sub (le_of_lt qb)] at qq
      rw [Nat.cast_sub (le_of_lt q2b)] at qq
      simp at qq
      exact qq
  · unfold Set.SurjOn Λtriangle ΛtriangleUpper Λrectangle
    rintro ⟨p, q⟩
    simp
    intro mem pb qb
    use (b + d - p), (a + c - q)
    constructor
    · rw [Nat.sub_mul, Nat.sub_mul]
      rw [← Nat.add_sub_assoc]
      · rw [← Nat.sub_add_comm]
        · rw [Nat.sub_sub]
          apply Nat.sub_lt_right_of_lt_add
          · apply add_le_add
            · refine Nat.mul_le_mul_right (a + c) ?_
              exact Nat.le_of_lt_succ pb
            · refine Nat.mul_le_mul_right (b + d) ?_
              exact Nat.le_of_lt_succ qb
          · rw [mul_comm]
            apply Nat.add_lt_add_left
            exact mem
        · refine Nat.mul_le_mul_right (a + c) ?_
          exact Nat.le_of_lt_succ pb
      · refine Nat.mul_le_mul_right (b + d) ?_
        exact Nat.le_of_lt_succ qb
    · constructor
      · refine Eq.symm (Nat.eq_sub_of_add_eq' ?_)
        refine Nat.sub_add_cancel ?_
        exact Nat.le_of_lt_succ pb
      · refine Eq.symm (Nat.eq_sub_of_add_eq' ?_)
        refine Nat.sub_add_cancel ?_
        exact Nat.le_of_lt_succ qb

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

lemma abcdCoprime (a b c d: ℕ+) (det: a * d = b * c + 1):
(a + c: ℕ).gcd (b + d) = 1 := by
  let k := (a + c: ℕ).gcd (b + d)
  have kac: k ∣ a + c := by apply Nat.gcd_dvd_left
  have kbd: k ∣ b + d := by apply Nat.gcd_dvd_right
  obtain ⟨u, ueq⟩ := kac
  obtain ⟨v, veq⟩ := kbd
  zify at ueq
  zify at veq
  have aeq: (a: ℤ) = k * u - c := by exact eq_sub_of_add_eq ueq
  have beq: (b: ℤ) = k * v - d := by exact eq_sub_of_add_eq veq
  have det': a * d - b * c = (1: ℤ) := by
    rw [sub_eq_of_eq_add']
    norm_cast
  rw [aeq, beq] at det'
  ring_nf at det'
  rw [mul_assoc, mul_assoc] at det'
  rw [← mul_sub] at det'
  have k1: k = (1:ℤ) := by
    refine Int.eq_one_of_dvd_one ?_ ?_
    · simp
    · exact Dvd.intro (u * d - c * v) det'
  simp at k1
  exact k1

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
      by_contra eq
      by_cases p0: p = 0
      · obtain q0 := qcut p0
        rw [p0] at eq
        simp at eq
        rw [eq] at q0
        contradiction
      · by_cases q0: q = 0
        · obtain p0 := imp_not_comm.mp pcut q0
          rw [q0] at eq
          simp at eq
          rw [mul_comm] at eq
          simp at eq
          rw [eq] at p0
          contradiction
        · have eq': (a + c) * (b + d - p) = q * (b + d) := by
            rw [Nat.mul_sub]
            apply (Nat.sub_eq_iff_eq_add' ?_).mpr
            · rw [mul_comm _ p]
              exact eq
            · apply (mul_le_mul_left ?_).mpr
              · exact Nat.le_of_lt_succ pbound
              · simp
          have dvd: (a + c: ℕ) ∣ q * (b + d) := by
            exact Dvd.intro _ eq'
          have dvd_q: (a + c: ℕ) ∣ q := by
            rw [← mul_one q]
            rw [← abcdCoprime a b c d det]
            apply Nat.dvd_mul_gcd_iff_dvd_mul.mpr
            exact dvd
          rcases dvd_q with ⟨k, keq⟩
          match k with
          | 0 =>
            simp at keq
            rw [keq] at q0
            contradiction
          | 1 =>
            simp at keq
            rw [keq] at eq
            simp at eq
            rw [eq] at p0
            contradiction
          | k' + 2 =>
            rw [keq] at qbound
            apply Nat.le_of_lt_add_one at qbound
            simp at qbound

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

/-
Here we finally get the value of the cardinality, which we will use to character rise the bound of n
-/
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

instance abPos(a b: ℕ+): PosReal (a + b) where
  pos := by norm_cast; simp


/- We define the the sequence of lattice points that will generate δₖ -/
lemma pqOfδₖ_abcd_exist(a b c d: ℕ+) (k: ℕ):
∃ (pq: ℕ × ℕ), δₚ (a + c) (b + d) pq = δₖ (a + c) (b + d) k := by
  obtain h := δₖ_in_Δ (a + c) (b + d) k
  unfold Δ is_δ at h
  simp at h
  unfold δₚ
  simp
  exact h

noncomputable
def pqOfδₖ_abcd (a b c d: ℕ+) (k: ℕ) := (pqOfδₖ_abcd_exist a b c d k).choose

lemma pqOfδₖ_abcd_bound (a b c d: ℕ+) (k: ℕ) (det: a * d = b * c + 1)
(h: k < (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ)):
(pqOfδₖ_abcd a b c d k).1 * (a + c) + (pqOfδₖ_abcd a b c d k).2 * (b + d) < (a + c) * (b + d) := by
  by_contra oob
  simp at oob
  let Δtriangle := δₚ (a + c) (b + d) '' Λtriangle a b c d
  have ΔtriangleCard: Δtriangle.toFinset.card = (Λtriangle a b c d).toFinset.card := by
    unfold Δtriangle
    let prot := (Λtriangle a b c d).toFinset.card
    have h: prot = (Λtriangle a b c d).toFinset.card := by rfl
    rw [← h]
    simp
    rw [h]
    apply Finset.card_image_iff.mpr
    unfold Set.InjOn
    simp
    intro p q mem p2 q2 mem2 eq
    norm_cast at eq
    obtain coprime := abcdCoprime a b c d det
    norm_cast at coprime
    unfold Λtriangle at mem
    simp at mem
    have mem': δₚ ↑↑(a + c) ↑↑(b + d) (p, q) < ↑↑(a + c) * ↑↑(b + d) := by
      unfold δₚ
      simp
      norm_cast
    obtain pqeq := unique_pq (a + c) (b + d) (p, q) (p2, q2) coprime eq mem'
    exact Prod.mk.inj_iff.mp pqeq

  let kTriangle := (δₖ (a + c) (b + d)) ⁻¹' Δtriangle
  have kTriangleFintype: Fintype kTriangle := by
    refine Set.Finite.fintype ?_
    refine Set.Finite.preimage ?_ ?_
    · intro k1 m1 k2 m2 eq
      apply (StrictMonoOn.eq_iff_eq (strictMonoOn_univ.mpr (δₖ_mono (a+c) (b+d))) ?_ ?_).mp eq
      · simp
      · simp
    · exact Set.toFinite Δtriangle

  have kTriangleCard: kTriangle.toFinset.card = Δtriangle.toFinset.card := by
    unfold kTriangle
    apply Finset.card_nbij (δₖ (a + c) (b + d))
    · intro k mem
      simp at mem
      simp
      exact mem
    · intro d1 mem1 d2 mem2 eq
      apply (StrictMonoOn.eq_iff_eq (strictMonoOn_univ.mpr (δₖ_mono (a+c) (b+d))) ?_ ?_).mp eq
      · simp
      · simp
    · intro δ mem
      simp at mem
      simp
      have δinΔ: δ ∈ Δ (a+c) (b+d) := by
        unfold Δtriangle at mem
        simp at mem
        rcases mem with ⟨p, q, mem, mem2⟩
        unfold Δ is_δ
        simp
        use p, q
        unfold δₚ at mem2
        simp at mem2
        exact mem2
      obtain ⟨k, keq⟩ := δₖ_surjΔ (a+c) (b+d) δ δinΔ
      use k
      constructor
      · rw [keq]
        exact mem
      · exact keq

  have kTriangleBound (kt: ℕ) (mem: kt ∈ kTriangle): kt < k := by
    have δrel: δₖ (a+c) (b+d) kt < δₖ (a+c) (b+d) k := by
      unfold kTriangle Δtriangle Λtriangle at mem
      simp at mem
      obtain ⟨p, q, pqBound, pqEq⟩ := mem
      unfold δₚ at pqEq
      simp at pqEq
      rify at pqBound
      rw [pqEq] at pqBound
      apply lt_of_lt_of_le pqBound
      rify at oob
      convert oob
      obtain kspec := Exists.choose_spec (pqOfδₖ_abcd_exist a b c d k)
      unfold δₚ at kspec
      simp at kspec
      unfold pqOfδₖ_abcd
      exact id (Eq.symm kspec)

    apply (StrictMono.lt_iff_lt (δₖ_mono (a+c) (b+d))).mp δrel

  have kTriangleCardBound: kTriangle.toFinset.card = (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) := by
    rw [kTriangleCard]
    rw [ΔtriangleCard]
    exact ΛtriangleCard a b c d det

  have kTriangleMaxBound (kt: ℕ) (mem: kt ∈ kTriangle): kt ≤ (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) - 2 := by
    obtain le1: kt ≤ k - 1 := by exact Nat.le_sub_one_of_lt (kTriangleBound kt mem)
    apply le_trans le1
    obtain le2: k ≤ ((a + c + 1) * (b + d + 1) - 2) / 2 - 1 := by exact Nat.le_sub_one_of_lt h
    exact Nat.sub_le_sub_right le2 1

  have notSaturated: (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) ≥ 2 := by
    apply Nat.le_div_two_iff_mul_two_le.mpr
    norm_num
    apply Nat.le_sub_of_add_le
    norm_num
    have sixNine: 6 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
    apply le_trans sixNine
    gcongr
    repeat exact NeZero.one_le

  set N := (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) - 2
  have n2: (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) = N + 2 := by
    unfold N
    rw [Nat.sub_add_cancel]
    exact notSaturated

  rw [n2] at kTriangleCardBound

  have kTriangleCardBoundFromMax: kTriangle.toFinset.card ≤ N + 1 := by
    let boundSet := Finset.range (N + 1)
    have sub: kTriangle.toFinset ⊆ boundSet := by
      unfold boundSet
      simp
      intro k mem
      simp
      apply Nat.lt_add_one_of_le
      exact kTriangleMaxBound k mem
    have boundCard: boundSet.card = N + 1 := by exact Finset.card_range (N + 1)
    rw [← boundCard]
    apply Finset.card_le_card sub

  rw [kTriangleCardBound] at kTriangleCardBoundFromMax
  simp at kTriangleCardBoundFromMax

/-
Now we can prove a stronger version of δₖ_inert, because we know the sequence of lattice points
always exists, and we have the explicit bound
-/
lemma δₖ_inert_fixed (a b c d: ℕ+) (s t: ℝ) (k: ℕ)
[PosReal s] [PosReal t]
(det: a * d = b * c + 1)
(left: a * t > b * s) (right: d * s > c * t)
(kbound: k < (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ)):
δₖ s t k = δₚ s t (pqOfδₖ_abcd a b c d k) := by
  have bound1: 1 ≤ (((a + c + 1) * (b + d + 1) - 2) / 2: ℕ) := by
    exact Nat.one_le_of_lt kbound
  apply δₖ_inert a b c d (a + c) (b + d) s t (((a + c + 1) * (b + d + 1) - 2) / 2 - 1) (pqOfδₖ_abcd a b c d) det
  · rw [mul_add, mul_add]
    rw [mul_comm]
    apply (add_lt_add_iff_left _).mpr
    norm_cast
    rw [det]
    apply PNat.lt_add_right
  · rw [mul_add, mul_add]
    nth_rw 2 [mul_comm]
    apply (add_lt_add_iff_right _).mpr
    norm_cast
    rw [mul_comm c b, mul_comm d a]
    rw [det]
    apply PNat.lt_add_right
  · exact left
  · exact right
  · intro k' mem
    obtain eq := Exists.choose_spec (pqOfδₖ_abcd_exist a b c d k')
    rw [← eq]
    rfl
  · intro k' mem
    apply pqOfδₖ_abcd_bound a b c d k' det
    exact Nat.lt_of_le_pred bound1 mem
  · exact Nat.le_sub_one_of_lt kbound

/-
From δₖ, we can prove nₖ is inert
-/
lemma nₖ_inert(a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (k: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(kbound: k < (((a + c + 1) * (b + d + 1)) / 2: ℕ)):
nₖ s1 t1 k = nₖ s2 t2 k := by
  rw [nₖ_accum, nₖ_accum]
  by_cases k0: k = 0
  · rw [k0]
    simp
  · simp [k0]
    have k1: 1 ≤ k := by exact Nat.one_le_iff_ne_zero.mpr k0
    have k1bound: k - 1 < ((a + c + 1) * (b + d + 1) - 2) / 2 := by
      apply (Nat.sub_lt_sub_iff_right k1).mpr at kbound
      convert kbound using 1
      apply Nat.eq_sub_of_add_eq
      rw [← Nat.div_eq_sub_div]
      · simp
      · have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
        apply le_trans twoNine
        gcongr
        repeat exact NeZero.one_le
    rw [δₖ_inert_fixed a b c d s1 t1 (k - 1) det left1 right1 k1bound]
    rw [δₖ_inert_fixed a b c d s2 t2 (k - 1) det left2 right2 k1bound]
    unfold Jceiled
    congr 1
    unfold δₚ
    simp
    obtain pqBound := pqOfδₖ_abcd_bound a b c d (k - 1) det k1bound
    obtain ⟨pb, qb⟩ := BoundDecomposite _ _ pqBound
    apply Λceiled_inert' a b c d s1 t1 s2 t2 _ _ det left1 right1 left2 right2 pb qb

/-
...and wₖ is inert. This prove is longer because one need to consider
some wₖ might corresponds to a ceiling generated by a lattice point below ℕ
-/
lemma wₖ_inert(a b c d: ℕ+) (s1 t1 s2 t2: ℝ) (k: ℕ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(kbound: k < (((a + c + 1) * (b + d + 1)) / 2: ℕ)):
wₖ s1 t1 k = wₖ s2 t2 k := by
  rw [wₖ_accum, wₖ_accum]
  by_cases k0: k = 0
  · rw [k0]
    simp
  · simp [k0]
    have k1: 1 ≤ k := by exact Nat.one_le_iff_ne_zero.mpr k0
    have k1bound: k - 1 < ((a + c + 1) * (b + d + 1) - 2) / 2 := by
      apply (Nat.sub_lt_sub_iff_right k1).mpr at kbound
      convert kbound using 1
      apply Nat.eq_sub_of_add_eq
      rw [← Nat.div_eq_sub_div]
      · simp
      · have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
        apply le_trans twoNine
        gcongr
        repeat exact NeZero.one_le
    rw [δₖ_inert_fixed a b c d s1 t1 (k - 1) det left1 right1 k1bound]
    rw [δₖ_inert_fixed a b c d s2 t2 (k - 1) det left2 right2 k1bound]
    unfold Jceiled
    congr 1
    unfold δₚ
    simp
    obtain pqBound := pqOfδₖ_abcd_bound a b c d (k - 1) det k1bound
    obtain ⟨pb, qb⟩ := BoundDecomposite _ _ pqBound
    set q := (pqOfδₖ_abcd a b c d (k - 1)).2
    by_cases q0: q = 0
    · simp [q0]
      apply Λceiled_inert_t' a b c d s1 t1 s2 t2 _ det left1 right1 left2 right2 pb
    · have q1: 1 ≤ q := by exact Nat.one_le_iff_ne_zero.mpr q0
      have shift1: q * t1 - t1 = (q - 1: ℕ) * t1 := by
        push_cast [q1]
        rw [sub_mul]
        simp
      have shift2: q * t2 - t2 = (q - 1: ℕ) * t2 := by
        push_cast [q1]
        rw [sub_mul]
        simp
      have qb': q - 1 < a + c := by exact tsub_lt_of_lt qb
      rw [add_sub_assoc, add_sub_assoc, shift1, shift2]
      apply Λceiled_inert' a b c d s1 t1 s2 t2 _ _ det left1 right1 left2 right2 pb qb'

/-
We define the bound for n
The first definition explicit for computation, but we also immediately prove a formula that's
more useful for theorem proving
-/
def nBranching (a b c d: ℕ+) := 1 + ∑pq ∈ (Λtriangle a b c d).toFinset, Jₚ pq

theorem nBranchingFormula (a b c d: ℕ+) (det: a * d = b * c + 1):
nBranching a b c d = nₖ (a + c) (b + d) (((a + c + 1) * (b + d + 1)) / 2 - 1) := by
  symm
  have twoBound: (2:ℕ)  ≤ (a + c + 1) * (b + d + 1) := by
    have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
    apply le_trans twoNine
    gcongr
    repeat exact NeZero.one_le
  have fourBound: (4:ℕ)  ≤ (a + c + 1) * (b + d + 1) := by
    have fourNine: 4 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
    apply le_trans fourNine
    gcongr
    repeat exact NeZero.one_le
  unfold nBranching
  have nonzero: (a + c + 1: ℕ) * (b + d + 1) / 2 - 1 ≠ 0 := by
    refine Nat.sub_ne_zero_iff_lt.mpr ?_
    refine (Nat.le_div_iff_mul_le ?_).mpr ?_
    · simp
    · norm_num
      have fourNine: 4 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
      apply le_trans fourNine
      gcongr
      repeat exact NeZero.one_le
  rw [nₖ_accum]
  simp [nonzero]
  unfold Jceiled
  congr 1
  simp
  apply subset_antisymm
  · unfold Λceiled
    intro pq mem
    simp at mem
    have inΔ: (pq.1: ℝ) * (a + c) + pq.2 * (b + d) ∈ Δ (a + c) (b + d) := by
      unfold Δ is_δ
      simp
    obtain ⟨k, keq⟩ := δₖ_surjΔ (a + c) (b + d)  _ inΔ
    rw [← keq] at mem
    obtain kmono := (StrictMono.le_iff_le (δₖ_mono (a + c) (b + d))).mp mem
    have klt: k < ((a + c + 1) * (b + d + 1) - 2) / 2 := by
      apply Nat.lt_of_le_sub_one (Nat.zero_lt_of_ne_zero nonzero) at kmono
      convert kmono using 1
      apply Nat.eq_sub_of_add_eq
      symm
      apply Nat.div_eq_sub_div
      · simp
      · exact twoBound
    let pq' := pqOfδₖ_abcd a b c d k
    obtain pq'eq := Exists.choose_spec (pqOfδₖ_abcd_exist a b c d k)
    obtain bound := pqOfδₖ_abcd_bound a b c d k det klt
    rify at bound
    unfold pqOfδₖ_abcd at bound
    unfold δₚ at pq'eq
    simp at pq'eq
    rw [pq'eq] at bound
    rw [keq] at bound
    unfold Λtriangle
    simp
    rify
    exact bound
  · let Δtriangle := δₚ (a + c) (b + d) '' Λtriangle a b c d
    have ΔtriangleCard: Δtriangle.toFinset.card ≤ (Λtriangle a b c d).toFinset.card := by
      unfold Δtriangle
      set protect := (Λtriangle a b c d).toFinset.card
      simp
      unfold protect
      exact Finset.card_image_le
    by_contra exception
    obtain ⟨pq, inTriangle, outCeiled⟩ := Set.not_subset_iff_exists_mem_not_mem.mp exception
    unfold Λceiled at outCeiled
    simp at outCeiled
    have inΔ: (pq.1: ℝ) * (a + c) + pq.2 * (b + d) ∈ Δ (a + c) (b + d) := by
      unfold Δ is_δ
      simp
    obtain ⟨k', keq⟩ := δₖ_surjΔ (a + c) (b + d) _ inΔ
    rw [← keq] at outCeiled
    rw [Nat.sub_sub] at outCeiled
    norm_num at outCeiled
    obtain k'floor := (StrictMono.lt_iff_lt (δₖ_mono (a + c) (b + d))).mp outCeiled
    have k'mem: δₖ (a + c) (b + d) k' ∈ Δtriangle := by
      rw [keq]
      unfold Δtriangle
      exact Set.mem_image_of_mem (δₚ (a + c) (b + d)) inTriangle
    rw [ΛtriangleCard a b c d det] at ΔtriangleCard
    have hole: ∃(l: ℕ), l ≤ (a + c + 1) * (b + d + 1) / 2 - 2 ∧ δₖ (a + c) (b + d) l ∉ Δtriangle := by
      by_contra full
      simp at full
      have subset: Finset.image (δₖ (↑↑a + ↑↑c) (↑↑b + ↑↑d)) (Finset.Icc 0 ((a + c + 1) * (b + d + 1) / 2 - 2))
        ⊆ Δtriangle.toFinset := by
        refine Finset.subset_iff.mpr ?_
        simp
        exact full
      have subset': Finset.image (δₖ (↑↑a + ↑↑c) (↑↑b + ↑↑d)) ({k'}) ⊆ Δtriangle.toFinset := by
        refine Finset.subset_iff.mpr ?_
        simp
        exact k'mem
      let uni := (Finset.Icc (0: ℕ) ((a + c + 1) * (b + d + 1) / 2 - 2)) ∪ {k'}
      have subset_uni: Finset.image (δₖ (↑↑a + ↑↑c) (↑↑b + ↑↑d)) uni ⊆ Δtriangle.toFinset := by
        unfold uni
        rw [Finset.image_union]
        apply Finset.union_subset subset subset'
      have disj: (Finset.Icc (0: ℕ) ((a + c + 1) * (b + d + 1) / 2 - 2)) ∩ {k'} = ∅ := by
        apply Finset.disjoint_iff_inter_eq_empty.mp
        simp
        exact k'floor
      have uniCard: uni.card = (a + c + 1) * (b + d + 1) / 2 - 2 + 1 + 1 - 0 := by
        unfold uni
        rw [Finset.card_union]
        rw [disj]
        simp
      have imageCard: (Finset.image (δₖ (↑↑a + ↑↑c) (↑↑b + ↑↑d)) uni).card = (a + c + 1) * (b + d + 1) / 2 - 2 + 1 + 1 - 0 := by
        rw [← uniCard]
        apply Finset.card_image_iff.mpr
        apply Set.injOn_of_injective
        apply StrictMono.injective (δₖ_mono _ _)
      obtain cardBound := Finset.card_le_card subset_uni
      rw [imageCard] at cardBound
      obtain chain := le_trans cardBound ΔtriangleCard
      have zero2: 0 < 2 := by simp
      rw [Nat.div_eq_sub_div zero2 twoBound] at chain
      simp at chain
      have subAddCanCancel: (1: ℕ) ≤ ((a + c + 1) * (b + d + 1) - 2) / 2 := by
        exact Nat.one_le_of_lt chain
      rw [Nat.sub_add_cancel subAddCanCancel] at chain
      simp at chain
    obtain ⟨l, lrange, lnotmem⟩ := hole
    obtain lrange := lt_of_le_of_lt lrange k'floor
    obtain lkrel := δₖ_mono (a + c) (b + d) lrange
    obtain lpq := δₖ_in_Δ (a + c) (b + d) l
    unfold Δ is_δ at lpq
    rcases lpq with ⟨lp, lq, lpqeq⟩
    rw [← lpqeq] at lkrel
    rw [← lpqeq] at lnotmem
    unfold Δtriangle Λtriangle at lnotmem
    simp at lnotmem
    obtain lnotmem := lnotmem lp lq
    rw [imp_not_comm] at lnotmem
    unfold δₚ at lnotmem
    simp at lnotmem
    unfold Δtriangle Λtriangle at k'mem
    simp at k'mem
    rcases k'mem with ⟨kp, kq, kb, keq⟩
    unfold δₚ at keq
    simp at keq
    rify at kb
    rw [keq] at kb
    rify at lnotmem
    obtain chain := lt_of_lt_of_le kb lnotmem
    obtain chain := lt_trans chain lkrel
    simp at chain

/-
kceiled is inert within the bound of n
-/
lemma kceiled_inert(a b c d: ℕ+) (s1 t1 s2 t2 n: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(nbound: n ≤ nBranching a b c d):
kceiled s1 t1 n = kceiled s2 t2 n := by
  rw [nBranchingFormula a b c d det] at nbound
  unfold kceiled
  ext k
  simp
  let nbound1 := nbound
  let nbound2 := nbound
  let kbound := ((a + c + 1) * (b + d + 1): ℕ) / 2 - 1
  have kboundOne: 1 ≤ ((a + c + 1) * (b + d + 1): ℕ) / 2 := by
    refine (Nat.one_le_div_iff ?_).mpr ?_
    · simp
    · have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
      apply le_trans twoNine
      gcongr
      repeat exact NeZero.one_le
  have kboundBound: kbound < (a + c + 1) * (b + d + 1) / 2 := by
     exact Nat.sub_one_lt_of_lt kboundOne
  obtain ⟨abcd1, abcd2⟩ := abcdLeftRight a b c d det
  rw [← nₖ_inert a b c d s1 t1 (a+c) (b+d) kbound det left1 right1 abcd1 abcd2 kboundBound] at nbound1
  rw [← nₖ_inert a b c d s2 t2 (a+c) (b+d) kbound det left2 right2 abcd1 abcd2 kboundBound] at nbound2
  constructor
  · intro h
    obtain inBound := le_trans h nbound1
    norm_cast at inBound
    have kInBound: k ≤ kbound := by exact (StrictMono.le_iff_le (nₖ_mono s1 t1)).mp inBound
    unfold kbound at kInBound
    have kInBound': k < ((a + c + 1) * (b + d + 1): ℕ) / 2 := by
      exact Nat.lt_of_le_of_lt kInBound kboundBound
    rw [← nₖ_inert a b c d s1 t1 s2 t2 k det left1 right1 left2 right2 kInBound']
    exact h
  · intro h
    obtain inBound := le_trans h nbound2
    norm_cast at inBound
    have kInBound: k ≤ kbound := by exact (StrictMono.le_iff_le (nₖ_mono s2 t2)).mp inBound
    unfold kbound at kInBound
    have kInBound': k < ((a + c + 1) * (b + d + 1): ℕ) / 2 := by
      exact Nat.lt_of_le_of_lt kInBound kboundBound
    rw [nₖ_inert a b c d s1 t1 s2 t2 k det left1 right1 left2 right2 kInBound']
    exact h

/-
... so is kₙ
-/
lemma kₙ_inert(a b c d: ℕ+) (s1 t1 s2 t2 n: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(nbound: n ≤ nBranching a b c d):
kₙ s1 t1 n = kₙ s2 t2 n := by
  unfold kₙ
  congr 1
  simp
  apply kceiled_inert a b c d s1 t1 s2 t2 n det left1 right1 left2 right2 nbound

/-
Here come our main theorems: wₘᵢₙ, wₘₐₓ, and wₗᵢ are all inert
-/
theorem wₘᵢₙ_inert (a b c d: ℕ+) (s1 t1 s2 t2 n: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(h: n ≥ 2) (nbound: n ≤ nBranching a b c d):
wₘᵢₙ s1 t1 n = wₘᵢₙ s2 t2 n := by
  obtain ⟨abcd1, abcd2⟩ := abcdLeftRight a b c d det
  unfold wₘᵢₙ
  have n1: n ≥ 1 := by apply ge_trans h; simp
  rcases kₙ_exist s1 t1 n n1 with ⟨k1, k1eq⟩
  rcases kₙ_exist s2 t2 n n1 with ⟨k2, k2eq⟩
  rw [k1eq, k2eq]
  simp
  have keq: kₙ s1 t1 n = kₙ s2 t2 n := by
    apply  kₙ_inert a b c d s1 t1 s2 t2 n det left1 right1 left2 right2 nbound
  have keq': k1 = k2 := by
    rw [← keq] at k2eq
    rw [k1eq] at k2eq
    exact ENat.coe_inj.mp k2eq
  rw [← keq']
  have boundlt: ((a + c + 1: ℕ) * (b + d + 1)) / 2 - 1 < ((a + c + 1) * (b + d + 1)) / 2 := by
    refine Nat.sub_one_lt ?_
    apply Nat.div_ne_zero_iff.mpr
    constructor
    · simp
    · have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
      apply le_trans twoNine
      gcongr
      repeat exact NeZero.one_le
  by_cases nlt: n < nₖ (a + c) (b + d) (((a + c + 1) * (b + d + 1)) / 2 - 1)
  · have k1bound: k1 + 1 < (a + c + 1) * (b + d + 1) / 2 := by
      unfold kₙ at k1eq
      have kmem: k1 ∈ (kceiled s1 t1 n).toFinset := by exact Finset.mem_of_max k1eq
      unfold kceiled at kmem
      simp at kmem
      obtain klt := lt_of_le_of_lt kmem nlt
      simp at klt
      rw [← nₖ_inert a b c d s1 t1 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
        det left1 right1 abcd1 abcd2 boundlt] at klt
      apply (StrictMono.lt_iff_lt (nₖ_mono s1 t1)).mp at klt
      exact Nat.add_lt_of_lt_sub klt
    congr 2
    · show wₖ s1 t1 k1 = wₖ s2 t2 k1
      apply wₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2
      exact Nat.lt_of_succ_lt k1bound
    · congr 2
      show wₖ s1 t1 (k1 + 1) = wₖ s2 t2 (k1 + 1)
      apply wₖ_inert a b c d s1 t1 s2 t2 (k1 + 1) det left1 right1 left2 right2
      exact k1bound
    · simp
      show nₖ s1 t1 (k1 + 1) = nₖ s2 t2 (k1 + 1)
      apply nₖ_inert a b c d s1 t1 s2 t2 (k1 + 1) det left1 right1 left2 right2
      exact k1bound
  · simp at nlt
    have neq: n = nₖ (a + c) (b + d) (((a + c + 1) * (b + d + 1)) / 2 - 1) := by
      rw [nBranchingFormula a b c d det] at nbound
      apply le_antisymm nbound nlt
    let neq2 := neq
    rw [← nₖ_inert a b c d s1 t1 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
      det left1 right1 abcd1 abcd2 boundlt] at neq
    rw [← nₖ_inert a b c d s2 t2 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
      det left2 right2 abcd1 abcd2 boundlt] at neq2
    have keq: k1 = (a + c + 1: ℕ) * (b + d + 1) / 2 - 1 := by
      unfold kₙ at k1eq
      have kmem: k1 ∈ (kceiled s1 t1 n).toFinset := by exact Finset.mem_of_max k1eq
      unfold kceiled at kmem
      rw [neq] at kmem
      simp at kmem
      have k11: k1 + 1 ∉ (kceiled s1 t1 n).toFinset := by
        by_contra k11mem
        obtain k11le := Finset.le_max k11mem
        rw [k1eq] at k11le
        have what: k1 + 1 ≤ k1 := by exact WithBot.coe_le_coe.mp k11le
        simp at what
      unfold kceiled at k11
      rw [neq] at k11
      simp at k11
      apply (StrictMono.le_iff_le (nₖ_mono s1 t1)).mp at kmem
      apply (StrictMono.lt_iff_lt (nₖ_mono s1 t1)).mp at k11
      exact Eq.symm (Nat.eq_of_le_of_lt_succ kmem k11)
    have kbound: k1 < (a + c + 1: ℕ) * (b + d + 1) / 2 := by exact lt_of_eq_of_lt keq boundlt
    rw [← keq] at neq
    rw [neq]
    have min_left(s t: ℝ)[PosReal s] [PosReal t]: (wₖ s t k1 : ℝ) ⊔ ((wₖ s t (k1 + 1)) + (nₖ s t k1) - (nₖ s t (k1 + 1))) = wₖ s t k1 := by
      apply max_eq_left
      apply sub_left_le_of_le_add
      have k1ge1 : k1 ≥ 1 := by
        rw [keq]
        apply Nat.le_sub_of_add_le
        apply (Nat.le_div_iff_mul_le ?_).mpr ?_
        · simp
        · norm_num
          have fourNine: 4 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
          apply le_trans fourNine
          gcongr
          repeat exact NeZero.one_le
      have k11ge1 : k1 + 1 ≥ 1 := by exact Nat.le_add_right_of_le k1ge1
      rw [← wₖ_rec s t k1 k1ge1]
      rw [← wₖ_rec s t (k1 + 1) k11ge1]
      push_cast
      have mono: (wₖ t s k1: ℝ) ≤ wₖ t s (k1 + 1) := by
        norm_cast
        apply wₖ_mono t s
        simp
      linarith
    obtain ninert := nₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound
    nth_rw 2 [ninert]
    rw [min_left s1 t1]
    rw [min_left s2 t2]
    simp
    apply wₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound


theorem wₘₐₓ_inert (a b c d: ℕ+) (s1 t1 s2 t2 n: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(h: n ≥ 2) (nbound: n ≤ nBranching a b c d):
wₘₐₓ s1 t1 n = wₘₐₓ s2 t2 n := by
  rw [nBranchingFormula a b c d det] at nbound
  obtain rec1 := eq_sub_of_add_eq' (wₘₘ_rec t1 s1 n h)
  obtain rec2 := eq_sub_of_add_eq' (wₘₘ_rec t2 s2 n h)
  rw [rec1, rec2]
  congr 1
  rw [nₖ_symm] at nbound
  have nboundeq: nₖ (b + d) (a + c) ((a + c + 1) * (b + d + 1) / 2 - 1)
    = nₖ (d + b) (c + a) ((d + b + 1) * (c + a + 1) / 2 - 1) := by
    congr 1
    · apply add_comm
    · apply add_comm
    · rw [mul_comm]
      congr 4
      · apply add_comm
      · apply add_comm
  rw [nboundeq] at nbound
  rw [mul_comm a d] at det
  rw [mul_comm b c] at det
  rw [← nBranchingFormula d c b a det] at nbound
  apply wₘᵢₙ_inert d c b a t1 s1 t2 s2 n det right1 left1 right2 left2 h nbound

theorem wₗᵢ_inert (a b c d: ℕ+) (s1 t1 s2 t2 n: ℝ)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(det: a * d = b * c + 1)
(left1: a * t1 > b * s1) (right1: d * s1 > c * t1)
(left2: a * t2 > b * s2) (right2: d * s2 > c * t2)
(_h: n ≥ 2) (nbound: n ≤ nBranching a b c d):
wₗᵢ s1 t1 n = wₗᵢ s2 t2 n := by
  obtain ⟨abcd1, abcd2⟩ := abcdLeftRight a b c d det
  unfold wₗᵢ
  by_cases n1: n ≥ 1
  · rcases kₙ_exist s1 t1 n n1 with ⟨k1, k1eq⟩
    rcases kₙ_exist s2 t2 n n1 with ⟨k2, k2eq⟩
    rw [k1eq, k2eq]
    simp
    have keq: kₙ s1 t1 n = kₙ s2 t2 n := by
      apply  kₙ_inert a b c d s1 t1 s2 t2 n det left1 right1 left2 right2 nbound
    have keq': k1 = k2 := by
      rw [← keq] at k2eq
      rw [k1eq] at k2eq
      exact ENat.coe_inj.mp k2eq
    rw [← keq']
    have boundlt: ((a + c + 1: ℕ) * (b + d + 1)) / 2 - 1 < ((a + c + 1) * (b + d + 1)) / 2 := by
      refine Nat.sub_one_lt ?_
      apply Nat.div_ne_zero_iff.mpr
      constructor
      · simp
      · have twoNine: 2 ≤ (1 + 1 + 1) * (1 + 1 + 1) := by simp
        apply le_trans twoNine
        gcongr
        repeat exact NeZero.one_le
    by_cases nlt: n < nₖ (a + c) (b + d) (((a + c + 1) * (b + d + 1)) / 2 - 1)
    · have k1bound: k1 + 1 < (a + c + 1) * (b + d + 1) / 2 := by
        unfold kₙ at k1eq
        have kmem: k1 ∈ (kceiled s1 t1 n).toFinset := by exact Finset.mem_of_max k1eq
        unfold kceiled at kmem
        simp at kmem
        obtain klt := lt_of_le_of_lt kmem nlt
        simp at klt
        rw [← nₖ_inert a b c d s1 t1 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
          det left1 right1 abcd1 abcd2 boundlt] at klt
        apply (StrictMono.lt_iff_lt (nₖ_mono s1 t1)).mp at klt
        exact Nat.add_lt_of_lt_sub klt
      have kbound: k1 < (a + c + 1: ℕ) * (b + d + 1) / 2 := by exact Nat.lt_of_succ_lt k1bound
      have nkeq: nₖ s1 t1 k1 = nₖ s2 t2 k1 := by
        apply nₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound
      have nkeq': nₖ s1 t1 (k1 + 1) = nₖ s2 t2 (k1 + 1) := by
        apply nₖ_inert a b c d s1 t1 s2 t2 (k1 + 1) det left1 right1 left2 right2 k1bound
      have wkeq: wₖ s1 t1 k1 = wₖ s2 t2 k1 := by
        apply wₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound
      have wkeq': wₖ s1 t1 (k1 + 1) = wₖ s2 t2 (k1 + 1) := by
        apply wₖ_inert a b c d s1 t1 s2 t2 (k1 + 1) det left1 right1 left2 right2 k1bound
      congr
    · simp at nlt
      have neq: n = nₖ (a + c) (b + d) (((a + c + 1) * (b + d + 1)) / 2 - 1) := by
        rw [nBranchingFormula a b c d det] at nbound
        apply le_antisymm nbound nlt
      let neq2 := neq
      rw [← nₖ_inert a b c d s1 t1 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
        det left1 right1 abcd1 abcd2 boundlt] at neq
      rw [← nₖ_inert a b c d s2 t2 (a + c) (b + d) ((a + c + 1) * (b + d + 1) / 2 - 1)
        det left2 right2 abcd1 abcd2 boundlt] at neq2
      have keq: k1 = (a + c + 1: ℕ) * (b + d + 1) / 2 - 1 := by
        unfold kₙ at k1eq
        have kmem: k1 ∈ (kceiled s1 t1 n).toFinset := by exact Finset.mem_of_max k1eq
        unfold kceiled at kmem
        rw [neq] at kmem
        simp at kmem
        have k11: k1 + 1 ∉ (kceiled s1 t1 n).toFinset := by
          by_contra k11mem
          obtain k11le := Finset.le_max k11mem
          rw [k1eq] at k11le
          have what: k1 + 1 ≤ k1 := by exact WithBot.coe_le_coe.mp k11le
          simp at what
        unfold kceiled at k11
        rw [neq] at k11
        simp at k11
        apply (StrictMono.le_iff_le (nₖ_mono s1 t1)).mp at kmem
        apply (StrictMono.lt_iff_lt (nₖ_mono s1 t1)).mp at k11
        exact Eq.symm (Nat.eq_of_le_of_lt_succ kmem k11)
      have kbound: k1 < (a + c + 1: ℕ) * (b + d + 1) / 2 := by exact lt_of_eq_of_lt keq boundlt
      rw [← keq] at neq
      rw [neq]
      obtain ninert := nₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound
      rw [ninert]
      simp
      apply wₖ_inert a b c d s1 t1 s2 t2 k1 det left1 right1 left2 right2 kbound
  · simp at n1
    obtain knot1 := kₙ_not_exist s1 t1 n n1
    obtain knot2 := kₙ_not_exist s2 t2 n n1
    rw [knot1, knot2]

/-
We start proving another family ot theorems: inert at edge
These are essentially saying w functions are inert for (a=1,b=N,c=0,d=1) and for (a=1,b=0,c=N,d=1)
But as we have been developing our theory for positive inters only, these need special treatment.

We will also prove stronger theorems where we find the value of w explicity.
In fact, they are at the edge 1 or n - 1, hence the name.
-/

lemma δₖ_inert_edge (N: ℕ+) (s t: ℝ) (k: ℕ)
[PosReal s] [PosReal t]
(left: t > N * s)
(kbound: k < ((N + 1): ℕ)):
δₖ s t k = k * s := by
  induction k with
  | zero => rw [δ₀]; simp
  | succ k prev =>
    have kprevbound: k < N + 1 := by exact Nat.lt_of_succ_lt kbound
    obtain prev := prev kprevbound
    unfold δₖ
    rw [prev]
    unfold δnext
    apply Set.IsWF.min_eq_of_le
    · unfold Δfloored
      constructor
      · unfold Δ is_δ
        simp
        use k + 1, 0
        simp
      · simp
        apply (mul_lt_mul_right PosReal.pos).mpr ?_
        · apply lt_add_one
    · unfold Δfloored Δ is_δ
      simp
      intro δ p q eq mem
      rw [← eq]
      rw [← eq] at mem
      by_cases q0: q = 0
      · rw [q0] at mem; simp at mem
        rw [q0]; simp
        apply (mul_lt_mul_right PosReal.pos).mp at mem
        simp at mem
        apply (mul_le_mul_right PosReal.pos).mpr
        norm_cast
      · have kbound': k + 1 ≤ N := by exact Nat.le_of_lt_succ kbound
        have h: (k + 1) * s ≤ N * s := by
          apply (mul_le_mul_right PosReal.pos).mpr
          norm_cast
        apply le_trans h
        apply le_trans (le_of_lt left)
        have q1: 1 ≤ q := by exact Nat.one_le_iff_ne_zero.mpr q0
        have tle: t ≤ q * t := by
          nth_rw 1 [← one_mul t]
          gcongr
          · apply le_of_lt PosReal.pos
          · norm_cast
        apply le_trans tle
        nth_rw 1 [← zero_add (q * t)]
        gcongr
        apply mul_nonneg
        · simp
        · apply le_of_lt PosReal.pos

lemma nₖ_inert_edge (N: ℕ+) (s t: ℝ) (k: ℕ)
[PosReal s] [PosReal t]
(left: t > N * s)
(kbound: k < ((N + 2): ℕ)):
nₖ s t k = k + 1 := by
  rw [nₖ_accum]
  by_cases k0: k = 0
  · rw [k0]
    simp
  · simp [k0]
    rw [add_comm]
    congr 1
    have k1: k - 1 < N + 1 := by
      refine Nat.sub_one_lt_of_le ?_ ?_
      · exact Nat.zero_lt_of_ne_zero k0
      · exact Nat.le_of_lt_succ kbound
    rw [δₖ_inert_edge N s t (k - 1) left k1]
    unfold Jceiled
    have Λeq: (Λceiled s t (↑(k - 1) * s)).toFinset = (Finset.Icc 0 (k - 1)).product {0} := by
      ext pq
      unfold Λceiled
      simp
      constructor
      · intro mem
        use pq.1
        have q0: pq.2 = 0 := by
          have h: 0 ≤ pq.1 * s := by
            apply mul_nonneg
            · simp
            · exact (le_of_lt PosReal.pos)
          obtain bound := le_of_add_le_of_nonneg_right mem h
          have right: (k - 1: ℕ) * s ≤ N * s := by
            apply mul_le_mul_of_nonneg_right
            · norm_cast
              exact Nat.le_of_lt_succ k1
            · exact le_of_lt PosReal.pos
          obtain bound' := le_trans bound right
          obtain bound'' := lt_of_le_of_lt bound' left
          nth_rw 2 [← one_mul t] at bound''
          obtain qb := lt_of_mul_lt_mul_of_nonneg_right bound'' (le_of_lt PosReal.pos)
          simp at qb
          exact qb
        rw [q0] at mem
        simp at mem
        constructor
        · rify
          exact le_of_mul_le_mul_of_pos_right mem PosReal.pos
        · rw [← q0]
      · simp
        intro p pb eq
        rw [← eq]
        simp
        rify at pb
        exact mul_le_mul_of_nonneg_right pb (le_of_lt PosReal.pos)
    rw [Λeq]
    unfold Jₚ
    simp
    exact Nat.succ_pred_eq_of_ne_zero k0

lemma wₖ_inert_edge (N: ℕ+) (s t: ℝ) (k: ℕ)
[PosReal s] [PosReal t]
(left: t > N * s)
(kbound: k < ((N + 2): ℕ)):
wₖ s t k = 1 := by
  rw [wₖ_accum]
  by_cases k0: k = 0
  · rw [k0]
    simp
  · simp [k0]
    unfold Jceiled
    convert Finset.sum_empty
    have k1: k - 1 < N + 1 := by
      refine Nat.sub_one_lt_of_le ?_ ?_
      · exact Nat.zero_lt_of_ne_zero k0
      · exact Nat.le_of_lt_succ kbound
    rw [δₖ_inert_edge N s t (k - 1) left k1]
    unfold Λceiled
    simp
    ext pq
    simp
    have right: 0 ≤ pq.1 * s + pq.2 * t := by
      apply add_nonneg
      repeat
        apply mul_nonneg
        · simp
        · exact le_of_lt PosReal.pos
    refine lt_of_lt_of_le ?_ right
    apply sub_lt_zero.mpr
    apply lt_of_le_of_lt ?_ left
    apply mul_le_mul_of_nonneg_right
    · norm_cast
      exact Nat.le_of_lt_succ k1
    · exact le_of_lt PosReal.pos

theorem wₘᵢₙ_inert_edge (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: t > N * s)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₘᵢₙ s t n = 1 := by
  have hN: N + (2:ℕ) = N + 1 + 1 := by ring
  unfold wₘᵢₙ
  have n1: n ≥ 1 := by apply ge_trans h; simp
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  rw [keq]
  simp
  by_cases nbound': n < N + 2
  · unfold kₙ at keq
    have kmem: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
    unfold kceiled at kmem
    simp at kmem
    obtain nₖrel := lt_of_le_of_lt kmem nbound'
    norm_cast at nₖrel
    push_cast at nₖrel
    have kbound: k + 1 < N + 2 := by
      rw [hN]
      rw [hN] at nₖrel
      rw [← nₖ_inert_edge N s t (N + 1) left (Nat.lt_add_one _)] at nₖrel
      apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp at nₖrel
      exact Nat.add_lt_add_right nₖrel 1
    have kbound': k < N + 2 := by
      exact Nat.lt_of_succ_lt kbound
    rw [wₖ_inert_edge N s t k left kbound']
    rw [wₖ_inert_edge N s t (k + 1) left kbound]
    rw [nₖ_inert_edge N s t (k + 1) left kbound]
    simp
    show n ≤ k + 1 + 1
    apply le_of_lt
    by_contra ntoolarge
    simp at ntoolarge
    have anothermem: k + 1 ∈ (kceiled s t n).toFinset := by
      unfold kceiled
      simp
      rw [nₖ_inert_edge N s t (k + 1) left kbound]
      push_cast
      exact ntoolarge
    have what: k + 1 ≤ k := by exact Finset.le_max_of_eq anothermem keq
    simp at what
  · simp at nbound'
    have nN: n = N + 2 := by apply le_antisymm nbound nbound'
    have bound: (N + 1: ℕ) < N + 2 := by simp
    have kv: k = N + 1 := by
      unfold kₙ at keq
      rw [nN] at keq
      apply le_antisymm
      · obtain memmax := Finset.mem_of_max keq
        unfold kceiled at memmax
        simp at memmax
        norm_cast at memmax
        push_cast at memmax
        rw [hN] at memmax
        rw [← nₖ_inert_edge N s t (N + 1) left bound] at memmax
        exact (StrictMono.le_iff_le (nₖ_mono s t)).mp memmax
      · by_contra ntoolarge
        simp at ntoolarge
        have anothermem: k + 1 ∈ (kceiled s t (N + 2)).toFinset := by
          unfold kceiled
          simp
          norm_cast
          push_cast
          rw [hN]
          rw [← nₖ_inert_edge N s t (N + 1) left bound]
          apply (StrictMono.le_iff_le (nₖ_mono s t)).mpr
          exact ntoolarge
        have what: k + 1 ≤ k := by exact Finset.le_max_of_eq anothermem keq
        simp at what
    rw [kv]
    have neq: n = (nₖ s t (N + 1)) := by
      rw [nN]
      rw [nₖ_inert_edge N s t (N + 1) left bound]
      norm_cast
    rw [neq]
    have max_left: (wₖ s t (N + 1) : ℝ) ⊔ ((wₖ s t ((N + 1) + 1)) + (nₖ s t (N + 1)) - (nₖ s t ((N + 1) + 1))) = wₖ s t (N + 1) := by
      apply max_eq_left
      apply sub_left_le_of_le_add
      have k1ge1 : (N + 1) ≥ 1 := by exact PNat.one_le (N + 1)
      have k11ge1 : (N + 1) + 1 ≥ 1 := by exact PNat.one_le (N + 1 + 1)
      rw [← wₖ_rec s t (N + 1) k1ge1]
      rw [← wₖ_rec s t ((N + 1) + 1) k11ge1]
      push_cast
      have mono: (wₖ t s (N + 1): ℝ) ≤ wₖ t s ((N + 1) + 1) := by
        norm_cast
        apply wₖ_mono t s
        simp
      linarith
    rw [max_left]
    rw [wₖ_inert_edge N s t (N + 1) left bound]
    simp

theorem wₘₐₓ_inert_edge (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: t > N * s)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₘₐₓ s t n = 1 := by
  have hN: N + (2:ℕ) = N + 1 + 1 := by ring
  unfold wₘₐₓ
  have n1: n ≥ 1 := by apply ge_trans h; simp
  rcases kₙ_exist s t n n1 with ⟨k, keq⟩
  rw [keq]
  simp
  by_cases nbound': n < N + 2
  · unfold kₙ at keq
    have kmem: k ∈ (kceiled s t n).toFinset := by exact Finset.mem_of_max keq
    unfold kceiled at kmem
    simp at kmem
    obtain nₖrel := lt_of_le_of_lt kmem nbound'
    norm_cast at nₖrel
    push_cast at nₖrel
    have kbound: k + 1 < N + 2 := by
      rw [hN]
      rw [hN] at nₖrel
      rw [← nₖ_inert_edge N s t (N + 1) left (Nat.lt_add_one _)] at nₖrel
      apply (StrictMono.lt_iff_lt (nₖ_mono s t)).mp at nₖrel
      exact Nat.add_lt_add_right nₖrel 1
    have kbound': k < N + 2 := by
      exact Nat.lt_of_succ_lt kbound
    rw [wₖ_inert_edge N s t k left kbound']
    rw [wₖ_inert_edge N s t (k + 1) left kbound]
    rw [nₖ_inert_edge N s t k left kbound']
    simp
    show 1 ≤ 1 + n - (k + 1)
    apply le_sub_right_of_add_le
    apply add_le_add_left
    by_contra ntoosmall
    simp at ntoosmall
    have notmem: k ∉ (kceiled s t n).toFinset := by
      unfold kceiled
      simp
      rw [nₖ_inert_edge N s t k left kbound']
      push_cast
      exact ntoosmall
    have mem: k ∈ (kceiled s t n).toFinset := by exact Set.mem_toFinset.mpr kmem
    contradiction
  · simp at nbound'
    have nN: n = N + 2 := by apply le_antisymm nbound nbound'
    have bound: (N + 1: ℕ) < N + 2 := by simp
    have kv: k = N + 1 := by
      unfold kₙ at keq
      rw [nN] at keq
      apply le_antisymm
      · obtain memmax := Finset.mem_of_max keq
        unfold kceiled at memmax
        simp at memmax
        norm_cast at memmax
        push_cast at memmax
        rw [hN] at memmax
        rw [← nₖ_inert_edge N s t (N + 1) left bound] at memmax
        exact (StrictMono.le_iff_le (nₖ_mono s t)).mp memmax
      · by_contra ntoolarge
        simp at ntoolarge
        have anothermem: k + 1 ∈ (kceiled s t (N + 2)).toFinset := by
          unfold kceiled
          simp
          norm_cast
          push_cast
          rw [hN]
          rw [← nₖ_inert_edge N s t (N + 1) left bound]
          apply (StrictMono.le_iff_le (nₖ_mono s t)).mpr
          exact ntoolarge
        have what: k + 1 ≤ k := by exact Finset.le_max_of_eq anothermem keq
        simp at what
    rw [kv]
    have neq: n = (nₖ s t (N + 1)) := by
      rw [nN]
      rw [nₖ_inert_edge N s t (N + 1) left bound]
      norm_cast
    rw [neq]
    simp
    have min_right: (wₖ s t (N + 1 + 1): ℝ) ⊓ ((wₖ s t (N + 1))) = wₖ s t (N + 1) := by
      simp
      apply wₖ_mono s t
      simp
    rw [min_right]
    rw [wₖ_inert_edge N s t (N + 1) left bound]
    simp

theorem wₗᵢ_inert_edge (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: t > N * s)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₗᵢ s t n = 1 := by
  obtain ⟨l, r⟩ := wₗᵢ_range s t n
  apply le_antisymm
  · rw [← wₘₐₓ_inert_edge N s t n left h nbound]
    exact r
  · rw [← wₘᵢₙ_inert_edge N s t n left h nbound]
    exact l

theorem wₘᵢₙ_inert_edge' (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: s > N * t)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₘᵢₙ s t n = n - 1 := by
  nth_rw 2 [← wₘₘ_rec s t n h]
  rw [wₘₐₓ_inert_edge N t s n left h nbound]
  simp

theorem wₘₐₓ_inert_edge' (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: s > N * t)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₘₐₓ s t n = n - 1 := by
  nth_rw 2 [← wₘₘ_rec t s n h]
  rw [wₘᵢₙ_inert_edge N t s n left h nbound]
  simp

theorem wₗᵢ_inert_edge' (N: ℕ+) (s t n: ℝ)
[PosReal s] [PosReal t]
(left: s > N * t)
(h: n ≥ 2) (nbound: n ≤ N + 2):
wₗᵢ s t n = n - 1 := by
  nth_rw 2 [← wₗᵢ_rec t s n h]
  rw [wₗᵢ_inert_edge N t s n left h nbound]
  simp

def genNode(n: ℕ+) (input: List (ℕ+ × ℕ+)): List (ℕ+ × ℕ+) := match input with
| .nil => .nil
| .cons head tail => match genNode n tail with
  | .nil => [head]
  | .cons prevhead prevtail =>
    if nBranching head.1 head.2 prevhead.1 prevhead.2 < n then
      [head, (head.1 + prevhead.1, head.2 + prevhead.2), prevhead] ++ prevtail
    else
      [head, prevhead] ++ prevtail

def nodeList(n: ℕ+): List (ℕ+ × ℕ+) :=
PNat.recOn n [] (fun prevn prev ↦
  if prevn < 2 then [] else if prevn = 2 then [(1, 1)] else
  genNode (prevn + 1) ([((prevn - 1), 1)] ++ prev ++ [(1, (prevn - 1))])
)

#eval nodeList 30
