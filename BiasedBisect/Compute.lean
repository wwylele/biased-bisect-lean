import BiasedBisect.Integer

theorem Vector.get_eq_getElem (v : Vector α n) (i : Fin n) : v.get i = v[(i: ℕ)] := rfl

theorem Vector.get_replicate (a : α) (i : Fin n): (Vector.replicate n a).get i = a := by
  rw [Vector.get_eq_getElem]
  rw [Vector.getElem_replicate]

instance (s t: ℕ+): NeZero (max s t: ℕ) := {
  out := by simp
}

structure ΦComputer (s t: ℕ+) where
  hst: s < t
  buffer : Vector ℕ t
  next_δ : ℕ
  next_pos : Fin t
  eqΦ : ∀ i: Fin t, buffer.get (next_pos - (Fin.ofNat' t 1) - i) = Φ s t (next_δ - 1 - i)

def ΦComputer.init (s t: ℕ+) (hst: s < t): ΦComputer s t := {
  hst
  buffer := Vector.replicate _ 1
  next_δ := 0
  next_pos := ⟨0, by simp⟩
  eqΦ := by
    intro i
    simp only [Fin.mk_zero', Fin.ofNat'_eq_cast, Nat.cast_one, zero_sub, CharP.cast_eq_zero,
      Int.reduceNeg]
    have neg: (-1 -i: ℤ) < 0 := by
      simp only [Int.reduceNeg, sub_neg]
      refine Int.neg_lt_of_neg_lt ?_
      apply Int.add_one_le_iff.mp
      simp
    rw [Φ_neg s t _ neg]
    rw [Vector.get_replicate]
}

structure ΦOutput (s t: ℕ+) where
  δ : ℕ
  Φδ : ℕ
  Φs : ℕ
  Φt : ℕ
  Φeq: Φ s t δ = Φδ
  Φseq: Φ s t (δ - s) = Φs
  Φteq: Φ s t (δ - t) = Φt

def ΦComputer.next {s t: ℕ+} (input: ΦComputer s t): (ΦComputer s t) × ΦOutput s t :=
  have t_ndvd_s: ¬ (t:ℕ) ∣ ↑s := Nat.not_dvd_of_pos_of_lt s.prop input.hst
  have onet: ((1: Fin t):ℕ) = (1:ℕ) := by
    simp only [Fin.val_one']
    apply Nat.mod_eq_of_lt
    exact lt_of_le_of_lt s.prop input.hst

  let pos_s := input.next_pos - Fin.ofNat' t s

  let Φs := input.buffer.get pos_s
  have Φseq: Φs = Φ s t (input.next_δ - s) := by
    convert input.eqΦ (Fin.ofNat' t s - 1) using 2
    · unfold pos_s
      simp
    · simp only [Fin.ofNat'_eq_cast]
      rw [sub_sub]
      rw [Fin.val_sub_one_of_ne_zero (by simpa using t_ndvd_s)]
      rw [Nat.cast_sub (by
        simp only [Fin.val_natCast]
        refine Nat.one_le_iff_ne_zero.mpr ?_
        contrapose! t_ndvd_s with mod0
        exact Nat.dvd_of_mod_eq_zero mod0
      )]
      simp only [Fin.val_natCast, Int.ofNat_emod, Nat.cast_one, add_sub_cancel, sub_right_inj]
      refine (Int.emod_eq_of_lt (by simp) (by simpa using input.hst)).symm

  let Φt := input.buffer.get input.next_pos
  have Φteq: Φt = Φ s t (input.next_δ - t) := by
    convert input.eqΦ (Fin.ofNat' t 0 - 1) using 2
    · simp
    · simp only [Fin.ofNat'_eq_cast, Nat.cast_zero, zero_sub]
      rw [sub_sub]
      simp only [sub_right_inj]
      rw [Fin.coe_neg, Nat.mod_eq_of_lt ?_]
      all_goals
      · rw [onet]
        simp

  let Φst := Φs + Φt
  have Φsteq: Φst = Φ s t input.next_δ := by
    unfold Φst
    rw [Φ_rec s t _ (by simp), Φseq, Φteq]

  let buffer' := input.buffer.set input.next_pos Φst input.next_pos.prop
  let next_δ' := input.next_δ + 1
  let next_pos' := input.next_pos + 1
  have eqΦ': ∀ i: Fin t, buffer'.get (next_pos' - 1 - i) = Φ s t (next_δ' - 1 - i) := by
    unfold buffer' next_pos' next_δ'
    intro i
    rw [Vector.get_eq_getElem, Vector.getElem_set]
    split_ifs with new
    · rw [add_sub_cancel_right] at new
      obtain new' := sub_eq_self.mp (Fin.eq_of_val_eq new).symm
      rw [Φsteq, new']
      simp
    · rw [← Vector.get_eq_getElem]
      convert input.eqΦ (i - 1) using 2
      · simp
      · have i0: i ≠ 0 := by
          contrapose! new with i0
          rw [i0]
          simp
        simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        rw [Fin.coe_sub_iff_le.mpr (Fin.one_le_of_ne_zero i0)]
        rw [onet]
        rw [Nat.cast_sub (by
          refine Nat.one_le_iff_ne_zero.mpr ?_
          simpa using i0
        )]
        simp

  ⟨⟨input.hst, buffer', next_δ', next_pos', eqΦ'⟩,
    ⟨input.next_δ, Φst, Φs, Φt, Φsteq.symm, Φseq.symm, Φteq.symm⟩⟩

lemma ΦComputer.next_succδ {s t: ℕ+} (input: ΦComputer s t):
input.next.1.next.2.δ = input.next.2.δ + 1 := by rfl

lemma ΦComputer.next_init {s t: ℕ+} (hst: s < t):
(ΦComputer.init s t hst).next.2.δ = 0 := by rfl

structure ΦOutputK (s t: ℕ+) (k: ℕ) where
  Φcomp: ΦComputer s t
  Φout : ΦOutput s t
  hk: Φout.Φδ = nₖ s t (k + 1)
  hδ: Φcomp.next.2.δ = Φout.δ + 1
  hδₖ: Φout.δ = δₖ_int s t k

def ΦComputer.next_after {s t: ℕ+} (input: ΦComputer s t) (δ: ℤ) (Φδ: ℕ) (k: ℕ)
(hΦ: Φδ = Φ s t δ) (hnext: input.next.2.δ = δ + 1) (hnₖ: Φδ = nₖ s t k)
: ΦOutputK s t k :=
  let next := input.next
  if h: next.2.Φδ ≤ Φδ then
    have hΦ': Φδ = Φ s t (δ + 1) := by
      rw [← next.2.Φeq] at h
      rw [← hnext]
      refine le_antisymm ?_ h
      rw [hΦ, hnext]
      exact Φ_mono _ _ (by simp)
    next.1.next_after (δ + 1) Φδ k hΦ' (by
      rw [ΦComputer.next_succδ]
      push_cast
      rw [hnext]
    ) hnₖ
  else
    have h': nₖ s t k < Φ s t (δ + 1) := by
      rw [hnₖ, ← next.2.Φeq, hnext] at h
      exact not_le.mp h
    have Φk: Φ s t δ = nₖ s t k := by
      rw [← hΦ]
      exact hnₖ
    have Φk1: Φ s t (δ + 1) = nₖ s t (k + 1) := by
      apply Φjump _ _ _ _ Φk
      rw [Φk]
      exact h'
    have hk: next.2.Φδ = nₖ s t (k + 1) := by
      rw [← next.2.Φeq, hnext]
      exact Φk1
    have hδₖ: next.2.δ = δₖ_int s t k := by
      rw [hnext]
      apply le_antisymm
      · apply Int.add_one_le_of_lt
        by_contra! le
        obtain what := Φ_mono s t le
        rw [Φδₖ, Φk] at what
        obtain what' := (nₖ_mono s t).le_iff_le.mp what
        simp at what'
      · unfold Φ Jceiled_int at Φk1
        rw [nₖ_accum] at Φk1
        simp at Φk1
        rify
        rw [δₖ_int_agree]
        exact Jceiled_mono' _ _ _ _ Φk1
    {
      Φcomp := next.1
      Φout := next.2
      hk := hk
      hδ := by apply ΦComputer.next_succδ
      hδₖ := hδₖ
    }
termination_by t * Φδ + 1 - ∑ i ∈ Finset.range t, Φ s t (input.next.2.δ - i)
decreasing_by
  apply Nat.sub_lt_sub_left
  · apply Nat.lt_succ.mpr
    have: (t * Φδ: ℕ) = ∑ _ ∈ Finset.range t, Φδ := by simp
    rw [this]
    apply Finset.sum_le_sum
    intro i _
    trans Φ s t input.next.2.δ
    · apply Φ_mono
      simp
    · rw [input.next.2.Φeq]
      exact h
  · rw [ΦComputer.next_succδ]
    let t': ℕ := t - 1
    have: t = t' + 1 := by
      unfold t'
      refine (Nat.sub_add_cancel ?_).symm
      exact NeZero.one_le
    rw [this]
    nth_rw 1 [Finset.range_succ]
    rw [Finset.sum_insert (by simp)]
    have: Finset.range (t' + 1) = insert 0 (Finset.Ioo 0 (t' + 1)) := by
      simp
    rw [this]
    rw [Finset.sum_insert (by simp)]
    have: ∑ i ∈ Finset.range t', Φ s t (input.next.2.δ - i) =
      ∑ i ∈ Finset.Ioo 0 (t' + 1), Φ s t (input.next.2.δ + 1 - i) := by
      apply Finset.sum_nbij (· + 1)
      · intro i h
        simpa using Finset.mem_range.mp h
      · intro i _ j _ ij
        exact Nat.succ_inj'.mp ij
      · intro i imem
        obtain ⟨ileft, iright⟩ := Finset.mem_Ioo.mp imem
        simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio]
        use i - 1
        constructor
        · exact Nat.sub_lt_right_of_lt_add ileft iright
        · exact Nat.sub_add_cancel ileft
      · intro i _
        simp
    rw [this]
    apply add_lt_add_right
    unfold t'
    simp only [PNat.pos, Nat.cast_pred, CharP.cast_eq_zero, sub_zero]
    rw [← sub_add, ← add_sub_right_comm]
    rw [Φ_rec s t (input.next.2.δ + 1: ℕ) (Int.ofNat_zero_le _)]
    exact (lt_add_iff_pos_left _).mpr (Φ_pos _ _ _)

structure nwComputer (s t: ℕ+) where
  Φcomp : ΦComputer s t
  next_k : ℕ
  prev_nₖ : ℕ
  prev_δ : ℤ
  δ_agree : Φcomp.next.2.δ = prev_δ + 1
  nₖ_δ_agree: prev_nₖ = Φ s t prev_δ
  nₖ_eq : prev_nₖ = nₖ s t next_k

def nwComputer.init (s t: ℕ+) (hst: s < t): nwComputer s t := {
  Φcomp := ΦComputer.init s t hst
  next_k := 0
  prev_nₖ := 1
  prev_δ := -1
  δ_agree := by rw [ΦComputer.next_init hst]; simp
  nₖ_δ_agree := by rw [Φ_neg s t (-1) (by simp)]
  nₖ_eq := by rw [n₀]
}

structure nwOutput (s t: ℕ+) where
  k : ℕ
  δₖ_val : ℕ
  nₖ₁_val : ℕ
  δₖ_eq : δₖ_val = δₖ_int s t k
  nₖ_eq : nₖ₁_val = nₖ s t (k + 1)

def nwComputer.next {s t: ℕ+} (input: nwComputer s t): (nwComputer s t) × nwOutput s t :=
  let Φcomp'output := input.Φcomp.next_after input.prev_δ input.prev_nₖ input.next_k
    input.nₖ_δ_agree input.δ_agree input.nₖ_eq
  let Φcomp' := Φcomp'output.Φcomp
  let output := Φcomp'output.Φout
  let δₖ_val := output.δ
  let nₖ₁_val := output.Φδ
  let k := input.next_k
  ⟨{
    Φcomp := Φcomp'
    next_k := k + 1
    prev_nₖ := nₖ₁_val
    prev_δ := δₖ_val
    δ_agree := by
      obtain h := Φcomp'output.hδ
      zify at h
      exact h
    nₖ_δ_agree := output.Φeq.symm
    nₖ_eq := Φcomp'output.hk
  }, {
    k
    δₖ_val
    nₖ₁_val
    δₖ_eq := Φcomp'output.hδₖ
    nₖ_eq := Φcomp'output.hk
  }⟩
