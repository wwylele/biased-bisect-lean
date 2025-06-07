import BiasedBisect.Integer

theorem Vector.get_eq_getElem (v : Vector α n) (i : Fin n) : v.get i = v[(i: ℕ)] := rfl

theorem Vector.get_replicate (a : α) (i : Fin n): (Vector.replicate n a).get i = a := by
  rw [Vector.get_eq_getElem]
  rw [Vector.getElem_replicate]

instance (s t: ℕ+): NeZero (max s t: ℕ) := {
  out := by simp
}

structure ΦComputer (s t: ℕ+) where
  hst: s ≤ t
  buffer : Vector ℕ t
  next_δ : ℕ
  next_pos : Fin t
  eqΦ : ∀ i: Fin t, buffer.get (next_pos - (Fin.ofNat t 1) - i) = Φ s t (next_δ - 1 - i)

def ΦComputer.init (s t: ℕ+) (hst: s ≤ t): ΦComputer s t := {
  hst
  buffer := Vector.replicate _ 1
  next_δ := 0
  next_pos := ⟨0, by simp⟩
  eqΦ := by
    intro i
    simp only [Fin.mk_zero', Fin.ofNat_eq_cast, Nat.cast_one, zero_sub, CharP.cast_eq_zero,
      Int.reduceNeg]
    have neg: (-1 -i: ℤ) < 0 := by
      simp only [Int.reduceNeg, sub_neg]
      refine Int.neg_lt_of_neg_lt ?_
      apply Int.add_one_le_iff.mp
      simp
    rw [Φ_neg s t _ neg]
    rw [Vector.get_replicate]
}

theorem Fin.coe_sub_one' {n : ℕ+} {a : ℕ+}:
    Fin.ofNat n a - 1 = Fin.ofNat n (a - 1) := by
  rw [Fin.ofNat_sub]

  trans Fin.ofNat n (a - 1 + n)
  · obtain rfl | hn := eq_or_ne n 1
    · ext
      simp
    · congr 1
      have : ((1 : Fin n) : ℕ) = 1 := by
        rw [val_one', Nat.mod_eq]
        simp only [PNat.pos, true_and, ite_eq_right_iff]
        intro h
        exfalso
        obtain what := lt_of_le_of_ne h (by simpa using hn)
        simp at what
      rw [this]
      rw [← Nat.sub_add_comm (by apply PNat.one_le)]
      rw [add_comm]
      rw [Nat.sub_add_comm (by apply PNat.one_le)]
  · refine eq_of_val_eq ?_
    rw [ofNat_eq_cast, ofNat_eq_cast, val_natCast, val_natCast]
    apply Nat.add_mod_right


theorem Fin.coe_neg_one' {n : ℕ+}:
    ((-1 : Fin n): ℕ) = n - 1 := by
  obtain n1|n1 := eq_or_lt_of_le (PNat.one_le n)
  · rw [← n1]
    simp
  · rw [Fin.coe_neg, val_one']
    nth_rw 2 [Nat.mod_eq_of_lt (by simpa using n1)]
    rw [Nat.mod_eq_of_lt (by simp)]


structure ΦOutput (s t: ℕ+) where
  δ : ℕ
  Φδ : ℕ
  Φs : ℕ
  Φt : ℕ
  Φeq : Φ s t δ = Φδ
  Φseq : Φ s t (δ - s) = Φs
  Φteq : Φ s t (δ - t) = Φt

def ΦComputer.next {s t: ℕ+} (input: ΦComputer s t): (ΦComputer s t) × ΦOutput s t :=
  let pos_s := input.next_pos - Fin.ofNat t s

  let Φs := input.buffer.get pos_s
  have Φseq: Φs = Φ s t (input.next_δ - s) := by
    convert input.eqΦ (Fin.ofNat t s - 1) using 2
    · unfold pos_s
      rw [sub_sub]
      congr 1
      rw [add_comm]
      exact (sub_add_cancel _ _).symm
    · rw [Fin.coe_sub_one', Fin.ofNat_eq_cast, Fin.val_natCast]
      rw [Nat.mod_eq_of_lt (Nat.sub_one_lt_of_le (by simp) (by norm_cast; exact input.hst))]
      simp

  let Φt := input.buffer.get input.next_pos
  have Φteq: Φt = Φ s t (input.next_δ - t) := by
    convert input.eqΦ (Fin.ofNat t 0 - 1) using 2
    · rw [sub_sub]
      convert (sub_zero _).symm
      rw [add_comm]
      exact (sub_add_cancel (Fin.ofNat t 0) 1)
    · rw [sub_sub]
      congr 1
      apply eq_add_of_sub_eq'
      trans ((t - 1 : ℕ) : ℤ)
      · simp
      · congr 1
        rw [← Fin.coe_neg_one']
        rfl

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
      · rw [← sub_add]
        rw [add_sub_right_comm, add_sub_right_comm]
        rfl
      · have i0: i ≠ 0 := by
          contrapose! new with i0
          rw [i0]
          simp
        have t1: 1 < t := by
          contrapose! i0 with t1
          simp only [PNat.le_one_iff] at t1
          apply subsingleton_iff.mp
          convert Fin.subsingleton_one
          simpa using t1
        have onet: ((1: Fin t):ℕ) = (1:ℕ) := by
          simp only [Fin.val_one']
          apply Nat.mod_eq_of_lt
          simpa using t1

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

lemma ΦComputer.next_init {s t: ℕ+} (hst: s ≤ t):
(ΦComputer.init s t hst).next.2.δ = 0 := by rfl

inductive ΦComputer' (s t: ℕ+) where
| st: ΦComputer s t -> ΦComputer' s t
| ts: ΦComputer t s -> ΦComputer' s t

def ΦComputer'.init (s t: ℕ+): ΦComputer' s t :=
  if hst: s ≤ t then
    ΦComputer'.st (ΦComputer.init s t hst)
  else
    ΦComputer'.ts (ΦComputer.init t s (le_of_lt (lt_of_not_ge hst)))

def ΦComputer'.next {s t: ℕ+} (input: ΦComputer' s t): (ΦComputer' s t) × ΦOutput s t :=
  match input with
  | ΦComputer'.st cst =>
    let next := cst.next
    ⟨ΦComputer'.st next.1, next.2⟩
  | ΦComputer'.ts cts =>
    let next := cts.next
    ⟨ΦComputer'.ts next.1, {
      δ := next.2.δ
      Φδ := next.2.Φδ
      Φs := next.2.Φt
      Φt := next.2.Φs
      Φeq := Φ_symm t s _ ▸ next.2.Φeq
      Φseq := Φ_symm t s _ ▸ next.2.Φteq
      Φteq := Φ_symm t s _ ▸ next.2.Φseq
    }⟩

lemma ΦComputer'.next_succδ {s t: ℕ+} (input: ΦComputer' s t):
input.next.1.next.2.δ = input.next.2.δ + 1 := by
  unfold ΦComputer'.next
  match input with
  | ΦComputer'.st cst => rw [ΦComputer.next_succδ]
  | ΦComputer'.ts cts => rw [ΦComputer.next_succδ]

lemma ΦComputer'.next_init (s t: ℕ+):
(ΦComputer'.init s t).next.2.δ = 0 := by
  unfold ΦComputer'.init
  unfold ΦComputer'.next
  split_ifs with hst
  · rw [ΦComputer.next_init hst]
  · rw [ΦComputer.next_init (le_of_lt (lt_of_not_ge hst))]

structure ΦOutputK (s t: ℕ+) (k: ℕ) where
  Φcomp: ΦComputer' s t
  Φout : ΦOutput s t
  hk: Φout.Φδ = nₖ s t (k + 1)
  hδ: Φcomp.next.2.δ = Φout.δ + 1
  hδₖ: Φout.δ = δₖ_int s t k

def ΦComputer'.next_after {s t: ℕ+} (input: ΦComputer' s t) (δ: ℤ) (Φδ: ℕ) (k: ℕ)
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
      rw [ΦComputer'.next_succδ]
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
        simp only [Int.cast_add, Int.cast_one, Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
          add_tsub_cancel_right, Nat.add_right_inj] at Φk1
        rify
        rw [δₖ_int_agree]
        exact Jceiled_mono' _ _ _ _ Φk1
    {
      Φcomp := next.1
      Φout := next.2
      hk := hk
      hδ := by apply ΦComputer'.next_succδ
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
  · rw [ΦComputer'.next_succδ]
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
        exact Nat.succ_inj.mp ij
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
  Φcomp : ΦComputer' s t
  next_k : ℕ
  prev_nₖ : ℕ
  prev_δ : ℤ
  δ_agree : Φcomp.next.2.δ = prev_δ + 1
  nₖ_δ_agree: prev_nₖ = Φ s t prev_δ
  nₖ_eq : prev_nₖ = nₖ s t next_k

def nwComputer.init (s t: ℕ+): nwComputer s t := {
  Φcomp := ΦComputer'.init s t
  next_k := 0
  prev_nₖ := 1
  prev_δ := -1
  δ_agree := by rw [ΦComputer'.next_init]; simp
  nₖ_δ_agree := by rw [Φ_neg s t (-1) (by simp)]
  nₖ_eq := by rw [n₀]
}

structure nwOutput (s t: ℕ+) where
  k : ℕ
  δₖ_val : ℕ
  nₖ₁_val : ℕ
  wₖ₁_val : ℕ
  δₖ_eq : δₖ_val = δₖ_int s t k
  nₖ_eq : nₖ₁_val = nₖ s t (k + 1)
  wₖ_eq : wₖ₁_val = wₖ s t (k + 1)

def nwComputer.next {s t: ℕ+} (input: nwComputer s t): (nwComputer s t) × nwOutput s t :=
  let Φcomp'output := input.Φcomp.next_after input.prev_δ input.prev_nₖ input.next_k
    input.nₖ_δ_agree input.δ_agree input.nₖ_eq
  let Φcomp' := Φcomp'output.Φcomp
  let output := Φcomp'output.Φout
  let δₖ_val := output.δ
  let nₖ₁_val := output.Φδ
  let wₖ₁_val := output.Φt
  let k := input.next_k
  have wₖ_eq: wₖ₁_val = wₖ s t (k + 1) := by
    unfold wₖ₁_val
    rw [← output.Φteq]
    rw [Φcomp'output.hδₖ]
    rw [Φδₖt]
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
    wₖ₁_val
    δₖ_eq := Φcomp'output.hδₖ
    nₖ_eq := Φcomp'output.hk
    wₖ_eq
  }⟩

lemma nwComputer.next_succ {s t: ℕ+} (input: nwComputer s t):
input.next.1.next.2.k = input.next.2.k + 1 := by rfl

lemma nwComputer.next_init (s t: ℕ+):
(nwComputer.init s t).next.2.k = 0 := by rfl

structure bbComputer (s t: ℕ+) where
  nwComp: nwComputer s t
  next_n : ℕ
  next_En : ℕ
  k : ℕ
  left_nₖ : ℕ
  right_nₖ : ℕ
  left_wₖ : ℕ
  right_wₖ : ℕ
  curr_δₖ : ℕ
  En_eq : next_En = E s t next_n
  next_k : nwComp.next.2.k = k + 1
  n_left : left_nₖ ≤ next_n
  n_right : next_n < right_nₖ
  left_nₖ_eq : left_nₖ = nₖ s t k
  right_nₖ_eq : right_nₖ = nₖ s t (k + 1)
  left_wₖ_eq : left_wₖ = wₖ s t k
  right_wₖ_eq : right_wₖ = wₖ s t (k + 1)
  δₖ_eq : curr_δₖ = δₖ_int s t k

def bbComputer.init (s t: ℕ+): bbComputer s t :=
  let nwCompInit := nwComputer.init s t
  let nwNext := nwCompInit.next
  {
    nwComp := nwNext.1
    next_n := 1
    next_En := 0
    k := 0
    left_nₖ := 1
    right_nₖ := nwNext.2.nₖ₁_val
    left_wₖ := 1
    right_wₖ := nwNext.2.wₖ₁_val
    curr_δₖ := nwNext.2.δₖ_val
    En_eq := by
      obtain E1 := Eℤ₁ s t
      unfold Eℤ at E1
      norm_cast at ⊢ E1
      exact E1.symm
    next_k := by rw [nwComputer.next_succ, nwComputer.next_init]
    n_left := by simp
    n_right := by
      rw [nwNext.2.nₖ_eq, nwComputer.next_init]
      norm_num
      rw [n₁]
      simp
    left_nₖ_eq := by rw [n₀]
    right_nₖ_eq := by rw [nwNext.2.nₖ_eq, nwComputer.next_init]
    left_wₖ_eq := by unfold wₖ; rfl
    right_wₖ_eq := by rw [nwNext.2.wₖ_eq, nwComputer.next_init]
    δₖ_eq := by rw [nwNext.2.δₖ_eq, nwComputer.next_init]
  }

structure bbOutput (s t: ℕ+) where
  n : ℕ
  En : ℕ
  wₘᵢₙn : ℤ
  wₘₐₓn : ℤ
  wₗᵢn : ℚ
  En_eq : En = Eℤ s t n
  wₘᵢₙn_eq : wₘᵢₙn = wₘᵢₙℤ s t n
  wₘₐₓn_eq : wₘₐₓn = wₘₐₓℤ s t n
  wₗᵢn_eq : wₗᵢn = wₗᵢ s t n
deriving Repr

def bbComputer.next {s t: ℕ+} (input: bbComputer s t): (bbComputer s t) × (bbOutput s t) :=
  let next_n' := input.next_n + 1
  let next_En' := input.next_En + (input.curr_δₖ + s + t)
  have keq: kₙ s t input.next_n = some input.k := by
    apply kₙ_inv'
    · norm_cast
      rw [← input.left_nₖ_eq]
      exact input.n_left
    · norm_cast
      rw [← input.right_nₖ_eq]
      exact input.n_right

  let wₘᵢₙn: ℤ := max input.left_wₖ (input.right_wₖ + input.next_n - input.right_nₖ)
  have wₘᵢₙn_eq : wₘᵢₙn = wₘᵢₙℤ s t input.next_n := by
    unfold wₘᵢₙn wₘᵢₙℤ
    rw [input.left_wₖ_eq, input.right_wₖ_eq, input.right_nₖ_eq]
    rw [(by norm_cast: ((input.next_n: ℤ): ℝ) = input.next_n)]
    rw [keq]

  let wₘₐₓn: ℤ := min input.right_wₖ (input.left_wₖ + input.next_n - input.left_nₖ)
  have wₘₐₓn_eq : wₘₐₓn = wₘₐₓℤ s t input.next_n := by
    unfold wₘₐₓn wₘₐₓℤ
    rw [input.left_wₖ_eq, input.right_wₖ_eq, input.left_nₖ_eq]
    rw [(by norm_cast: ((input.next_n: ℤ): ℝ) = input.next_n)]
    rw [keq]

  let a: ℚ := (input.next_n - input.left_nₖ) / (input.right_nₖ - input.left_nₖ)
  let wₗᵢn :=  (1 - a) * input.left_wₖ + a * input.right_wₖ
  have wₗᵢn_eq : wₗᵢn = wₗᵢ s t input.next_n := by
    unfold wₗᵢn a wₗᵢ
    rw [input.left_wₖ_eq, input.right_wₖ_eq, input.left_nₖ_eq, input.right_nₖ_eq]
    rw [keq]
    simp

  if h: next_n' = input.right_nₖ then
    let nwComp' := input.nwComp.next
    have right_nₖ_eq: nwComp'.2.nₖ₁_val = nₖ s t (input.k + 1 + 1) := by rw [nwComp'.2.nₖ_eq, input.next_k]
    have n_right: next_n' < nwComp'.2.nₖ₁_val := by
        rw [h, input.right_nₖ_eq, nwComp'.2.nₖ_eq, input.next_k]
        exact nₖ_mono s t (by simp)
    have keq': kₙ s t (input.next_n + 1) = some (input.k + 1) := by
      apply kₙ_inv'
      · norm_cast
        rw [← input.right_nₖ_eq]
        exact le_of_eq h.symm
      · norm_cast
        rw [← right_nₖ_eq]
        exact n_right
    have δeq: nwComp'.2.δₖ_val = δₖ_int s t (input.k + 1) := by rw [nwComp'.2.δₖ_eq, input.next_k]
    ⟨{
      nwComp := nwComp'.1
      next_n := next_n'
      next_En := next_En'
      k := input.k + 1
      left_nₖ := input.right_nₖ
      right_nₖ := nwComp'.2.nₖ₁_val
      left_wₖ := input.right_wₖ
      right_wₖ := nwComp'.2.wₖ₁_val
      curr_δₖ := nwComp'.2.δₖ_val
      En_eq := by
        unfold next_n' next_En'
        push_cast
        rw [input.En_eq]
        unfold E
        obtain δeq := input.δₖ_eq
        rify at δeq h
        unfold next_n' at h
        push_cast at h
        obtain h' := eq_sub_of_add_eq h
        rw [keq, keq', δeq, δₖ_int_agree, h, h', input.right_nₖ_eq]
        simp only [sub_self, zero_mul, add_zero]
        rw [Eₖ, nₖ]
        push_cast
        ring
      next_k := by rw [nwComputer.next_succ, input.next_k]
      n_left := le_of_eq h.symm
      n_right := n_right
      left_nₖ_eq := input.right_nₖ_eq
      right_nₖ_eq := right_nₖ_eq
      left_wₖ_eq := input.right_wₖ_eq
      right_wₖ_eq := by rw [nwComp'.2.wₖ_eq, input.next_k]
      δₖ_eq := δeq
    }, {
      n := input.next_n
      En := input.next_En
      wₘᵢₙn
      wₘₐₓn
      wₗᵢn
      En_eq := input.En_eq
      wₘᵢₙn_eq
      wₘₐₓn_eq
      wₗᵢn_eq
    }⟩
  else
    have n_left: input.left_nₖ ≤ next_n' := le_trans input.n_left (by unfold next_n'; simp)
    have n_right: next_n' < input.right_nₖ := lt_of_le_of_ne (Nat.add_one_le_of_lt input.n_right) h
    have keq': kₙ s t (input.next_n + 1) = some input.k := by
      apply kₙ_inv'
      · norm_cast
        rw [← input.left_nₖ_eq]
        exact n_left
      · norm_cast
        rw [← input.right_nₖ_eq]
        exact n_right
    ⟨{
      nwComp := input.nwComp
      next_n := next_n'
      next_En := next_En'
      k := input.k
      left_nₖ := input.left_nₖ
      right_nₖ := input.right_nₖ
      left_wₖ := input.left_wₖ
      right_wₖ := input.right_wₖ
      curr_δₖ := input.curr_δₖ
      En_eq := by
        unfold next_n' next_En'
        push_cast
        rw [input.En_eq]
        unfold E
        obtain δeq := input.δₖ_eq
        rify at δeq
        rw [keq, keq', δeq, δₖ_int_agree]
        simp only
        ring
      next_k := input.next_k
      n_left := n_left
      n_right := n_right
      left_nₖ_eq := input.left_nₖ_eq
      right_nₖ_eq := input.right_nₖ_eq
      left_wₖ_eq := input.left_wₖ_eq
      right_wₖ_eq := input.right_wₖ_eq
      δₖ_eq := input.δₖ_eq
    }, {
      n := input.next_n
      En := input.next_En
      wₘᵢₙn
      wₘₐₓn
      wₗᵢn
      En_eq := input.En_eq
      wₘᵢₙn_eq
      wₘₐₓn_eq
      wₗᵢn_eq
    }⟩


lemma bbComputer.next_succ {s t: ℕ+} (input: bbComputer s t):
input.next.1.next.2.n = input.next.2.n + 1 := by
  rw [bbComputer.next]
  split
  all_goals
  · simp only
    rw [bbComputer.next]
    split
    all_goals rfl

lemma bbComputer.next_init (s t: ℕ+):
(bbComputer.init s t).next.2.n = 1 := by
  rw [bbComputer.next]
  split
  all_goals rfl

def calculateBbList' (s t: ℕ+) (n: ℕ) (prev: Array (bbOutput s t)) (comp: bbComputer s t) :=
  if n = 0 then
    prev
  else
    let next := comp.next
    calculateBbList' s t (n - 1) (prev ++ [next.2]) next.1

def calculateBbList (s t: ℕ+) (n: ℕ) :=
  calculateBbList' s t n (Array.emptyWithCapacity n) (bbComputer.init s t)
