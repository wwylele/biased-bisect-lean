import BiasedBisect.Basic

def Λₖ (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t] := Λline s t (δₖ s t k)

lemma ΛₖNonempty (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]: (Λₖ s t k).Nonempty := by
  unfold Λₖ Λline
  refine Set.Nonempty.preimage' ?_ ?_
  · apply Set.singleton_nonempty
  · apply Set.singleton_subset_iff.mpr
    simp only [Set.mem_range, Prod.exists]
    apply δₖ_in_Δ

lemma Λ₀ (s t: ℝ) [PosReal s] [PosReal t]: Λₖ s t 0 = {(0, 0)} := by
  unfold Λₖ Λline δₚ
  rw [δ₀]
  simp only
  ext pq
  constructor
  · intro pqmem
    simp only [Set.mem_preimage] at pqmem
    apply Set.mem_singleton_iff.mp at pqmem
    obtain ⟨ps, qt⟩ := sum_to_zero _ _ (mul_nonneg (by apply Nat.cast_nonneg') (le_of_lt PosReal.pos))
      (mul_nonneg (by apply Nat.cast_nonneg') (le_of_lt PosReal.pos))  (le_of_eq pqmem)
    obtain p := (mul_eq_zero_iff_right (ne_of_gt PosReal.pos: s ≠ 0)).mp ps
    obtain q := (mul_eq_zero_iff_right (ne_of_gt PosReal.pos: t ≠ 0)).mp qt
    norm_cast at p q
    exact Set.mem_singleton_of_eq (Prod.ext_iff.mpr ⟨p, q⟩)
  · intro pqmem
    apply Set.mem_singleton_iff.mp at pqmem
    simp only [Set.mem_preimage]
    rw [pqmem]
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact Set.mem_singleton_of_eq rfl

noncomputable instance (s t: ℝ) (k: ℕ) [PosReal s] [PosReal t]:
Fintype (Λₖ s t k) := by unfold Λₖ; infer_instance


def Λfloored (s t: ℝ) (K: ℕ) [PosReal s] [PosReal t] := {pq: ℕ × ℕ | δₚ s t pq > δₖ s t K}

noncomputable
def minGap (s t: ℝ) (K: ℕ) [PosReal s] [PosReal t] :=
  ((Finset.range (K + 1)).image (fun k ↦ δₖ s t (k + 1) - δₖ s t k)).min' (by
  simp only [Finset.image_nonempty, Finset.nonempty_range_iff]
  exact Ne.symm (Nat.zero_ne_add_one K)
)

noncomputable
def εBound (s t: ℝ) (K: ℕ) [PosReal s] [PosReal t] := minGap s t K / (δₖ s t (K + 1))

lemma εBoundPos (s t: ℝ) (K: ℕ) [PosReal s] [PosReal t]: 0 < εBound s t K := by
  apply div_pos
  · unfold minGap
    simp only [Finset.lt_min'_iff, Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, sub_pos]
    intro k kmem
    apply δₖ_mono
    exact lt_add_one k
  · rw [← δ₀ s t]
    apply δₖ_mono
    exact Nat.zero_lt_succ K

lemma ΛₖIsolated (s t ε: ℝ) (k K: ℕ) (kbound: k < K) [PosReal s] [PosReal t]
(εpos: 0 ≤ ε) (εbound: ε < t * εBound s t K):
∀ pq ∈ Λₖ s t k, ∀ pq' ∈ Λₖ s t (k + 1), δₚ s (t + ε) pq < δₚ s (t + ε) pq' := by
  intro pq pqmem pq' pq'mem
  unfold δₚ
  simp only
  have right: pq'.1 * s + pq'.2 * t ≤ pq'.1 * s + pq'.2 * (t + ε) := by
    apply le_of_sub_nonneg
    ring_nf
    exact mul_nonneg (Nat.cast_nonneg' pq'.2) εpos
  refine lt_of_lt_of_le ?_ right
  rw [(by ring: pq.1 * s + pq.2 * (t + ε) = pq.1 * s + pq.2 * t + pq.2 * ε)]
  unfold Λₖ Λline at pqmem pq'mem
  simp only [Set.mem_preimage] at pqmem pq'mem
  obtain pqeq := Set.eq_of_mem_singleton pqmem
  obtain pq'eq := Set.eq_of_mem_singleton pq'mem
  unfold δₚ at pqeq pq'eq
  simp only at pqeq pq'eq
  rw [pqeq, pq'eq]
  apply add_lt_of_lt_sub_left
  have left: pq.2 * ε ≤ pq.2 * t * εBound s t K := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_of_lt εbound) (by exact Nat.cast_nonneg' pq.2)
  apply lt_of_le_of_lt left
  have left: pq.2 * t * εBound s t K < δₖ s t (K + 1) * εBound s t K := by
    refine mul_lt_mul_of_pos_right ?_ (by apply εBoundPos)
    obtain left := le_of_add_le_of_nonneg_right (le_of_eq pqeq)
      (mul_nonneg (Nat.cast_nonneg' pq.1) (le_of_lt PosReal.pos))
    apply lt_of_le_of_lt left
    apply δₖ_mono
    exact Nat.lt_add_right 1 kbound
  apply lt_of_lt_of_le left
  unfold εBound
  rw [mul_div_cancel₀ _ (by apply ne_of_gt; rw [← δ₀ s t]; apply δₖ_mono; exact Nat.zero_lt_succ K)]
  unfold minGap
  apply Finset.min'_le
  simp only [Finset.mem_image, Finset.mem_range]
  use k
  exact ⟨Nat.lt_add_right 1 kbound, rfl⟩

lemma ΛflooredIsolated (s t ε: ℝ) (K: ℕ)  [PosReal s] [PosReal t]
(εpos: 0 ≤ ε) (εbound: ε < t * εBound s t K):
∀ pq ∈ Λₖ s t K, ∀ pq' ∈ Λfloored s t K, δₚ s (t + ε) pq < δₚ s (t + ε) pq' := by
  intro pq pqmem pq' pq'mem
  unfold δₚ
  simp only
  have right: pq'.1 * s + pq'.2 * t ≤ pq'.1 * s + pq'.2 * (t + ε) := by
    apply le_of_sub_nonneg
    ring_nf
    exact mul_nonneg (Nat.cast_nonneg' pq'.2) εpos
  refine lt_of_lt_of_le ?_ right
  rw [(by ring: pq.1 * s + pq.2 * (t + ε) = pq.1 * s + pq.2 * t + pq.2 * ε)]
  unfold Λₖ Λline at pqmem
  unfold Λfloored at pq'mem
  simp only [Set.mem_preimage] at pqmem
  simp only [gt_iff_lt, Set.mem_setOf_eq] at pq'mem
  obtain pqeq := Set.eq_of_mem_singleton pqmem
  unfold δₚ at pqeq
  simp only at pqeq
  rw [pqeq]
  have memnext: δₚ s t pq' ∈ Δfloored s t (δₖ s t K):= by
    unfold Δfloored
    constructor
    · unfold δₚ Δ
      simp only [Set.mem_setOf_eq, exists_apply_eq_apply2]
    · simp only [gt_iff_lt, Set.mem_setOf_eq]
      exact pq'mem
  have nextle: δₖ s t (K + 1) ≤ δₚ s t pq' := by
    unfold δₖ δnext
    exact Set.IsWF.min_le _ _ memnext
  unfold δₚ at nextle
  simp only at nextle
  refine lt_of_lt_of_le ?_ nextle
  apply add_lt_of_lt_sub_left
  have left: pq.2 * ε ≤ pq.2 * t * εBound s t K := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_of_lt εbound) (by exact Nat.cast_nonneg' pq.2)
  apply lt_of_le_of_lt left
  have left: pq.2 * t * εBound s t K < δₖ s t (K + 1) * εBound s t K := by
    refine mul_lt_mul_of_pos_right ?_ (by apply εBoundPos)
    obtain left := le_of_add_le_of_nonneg_right (le_of_eq pqeq)
      (mul_nonneg (Nat.cast_nonneg' pq.1) (le_of_lt PosReal.pos))
    apply lt_of_le_of_lt left
    apply δₖ_mono
    exact lt_add_one K
  apply lt_of_lt_of_le left
  unfold εBound
  rw [mul_div_cancel₀ _ (by apply ne_of_gt; rw [← δ₀ s t]; apply δₖ_mono; exact Nat.zero_lt_succ K)]
  unfold minGap
  apply Finset.min'_le
  simp only [Finset.mem_image, Finset.mem_range]
  use K
  exact ⟨lt_add_one K, rfl⟩

lemma ΛₖMono (s t ε: ℝ) (k1 k2 K: ℕ) (kh: k1 < k2) (kbound: k1 ≤ K) [PosReal s] [PosReal t]
(εpos: 0 ≤ ε) (εbound: ε < t * εBound s t K):
∀ pq ∈ Λₖ s t k1, ∀ pq' ∈ Λₖ s t k2, δₚ s (t + ε) pq < δₚ s (t + ε) pq' := by
  obtain k2leK|k2gtK := le_or_gt k2 K
  · obtain k1succlek2 := Nat.succ_le_of_lt kh
    induction k2, k1succlek2 using Nat.le_induction with
    | base =>
      intro pq1 pq1mem pq2 pq2mem
      apply ΛₖIsolated s t ε k1 K k2leK εpos εbound pq1 pq1mem pq2 pq2mem
    | succ k2 hak hk =>
      intro pq1 pq1mem pq2 pq2mem
      obtain ⟨mid, midmem⟩ := ΛₖNonempty s t k2
      obtain prev := hk hak (Nat.le_of_succ_le k2leK) pq1 pq1mem mid midmem
      apply lt_trans prev
      apply ΛₖIsolated s t ε k2 K k2leK εpos εbound mid midmem pq2 pq2mem
  · intro pq1 pq1mem pq2 pq2mem
    have k2InFloored: pq2 ∈ Λfloored s t K := by
      unfold Λₖ Λline at pq2mem
      simp only [Set.mem_preimage] at pq2mem
      obtain pq2eq := Set.eq_of_mem_singleton pq2mem
      unfold Λfloored
      simp only [gt_iff_lt, Set.mem_setOf_eq]
      rw [pq2eq]
      exact δₖ_mono _ _ k2gtK
    revert pq1
    induction kbound using Nat.decreasingInduction with
    | of_succ k1 hk1 ih =>
      intro pq1 pq1mem
      have k1succltk2: k1 + 1 < k2 := lt_of_le_of_lt hk1 k2gtK
      obtain ⟨mid, midmem⟩ := ΛₖNonempty s t (k1 + 1)
      obtain prev := ih k1succltk2 mid midmem
      refine lt_trans ?_ prev
      eapply ΛₖIsolated s t ε k1 K hk1 εpos εbound pq1 pq1mem mid midmem
    | self =>
      intro pq1 pq1mem
      exact ΛflooredIsolated _ _ _ _ εpos εbound pq1 pq1mem pq2 k2InFloored

lemma ΛₖSplit (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε]:
∀ pq ∈ Λₖ s t k, ∀ pq' ∈ Λₖ s t k, pq = pq' ↔ δₚ s (t + ε) pq = δₚ s (t + ε) pq' := by
  intro pq pqmem pq' pq'mem
  constructor
  · intro pqeq
    rw [pqeq]
  · intro δeq
    unfold Λₖ Λline at pqmem pq'mem
    simp only [Set.mem_preimage] at pqmem pq'mem
    obtain pqeq := Set.eq_of_mem_singleton pqmem
    obtain pq'eq := Set.eq_of_mem_singleton pq'mem
    unfold δₚ at pqeq pq'eq δeq
    simp only at pqeq pq'eq δeq
    rw [← pq'eq] at pqeq
    rw [mul_add, mul_add, ← add_assoc, ← add_assoc] at δeq
    rw [← pqeq] at δeq
    apply add_left_cancel at δeq
    apply mul_right_cancel₀ (ne_of_gt PosReal.pos) at δeq
    rw [← δeq] at pqeq
    apply add_right_cancel at pqeq
    apply mul_right_cancel₀ (ne_of_gt PosReal.pos) at pqeq
    norm_cast at δeq pqeq
    exact Prod.ext pqeq δeq

lemma ΛₖSplit' (s t ε: ℝ) (k K: ℕ) (kbound: k ≤ K) [PosReal s] [PosReal t] [PosReal ε]
(εbound: ε < t * εBound s t K):
∀ pq ∈ Λₖ s t k, ∀ pq', pq = pq' ↔ δₚ s (t + ε) pq = δₚ s (t + ε) pq' := by
  intro pq pqmem pq'
  constructor
  · intro pqeq
    rw [pqeq]
  · intro pqeq
    obtain ⟨k', k'eq⟩ := δₖ_surjΔ s t (δₚ s t pq') (by unfold Δ δₚ; simp only [Set.mem_setOf_eq,
      exists_apply_eq_apply2])
    have pq'mem: pq' ∈ Λₖ s t k' := Eq.symm k'eq
    refine (ΛₖSplit s t ε k pq pqmem pq' ?_).mpr pqeq
    convert pq'mem
    apply le_antisymm
    · by_contra lt
      simp only [not_le] at lt
      obtain mono := ΛₖMono s t ε k' k K lt (le_of_lt (lt_of_lt_of_le lt kbound))
        (le_of_lt PosReal.pos) εbound pq' pq'mem pq pqmem
      rw [pqeq] at mono
      simp only [lt_self_iff_false] at mono
    · by_contra lt
      simp only [not_le] at lt
      obtain mono := ΛₖMono s t ε k k' K lt (kbound)
        (le_of_lt PosReal.pos) εbound pq pqmem pq' pq'mem
      rw [pqeq] at mono
      simp only [lt_self_iff_false] at mono



lemma ΛₖtoδNonempty (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] :
((Λₖ s t k).toFinset.image (δₚ s (t + ε))).Nonempty := by
  simp only [Finset.image_nonempty, Set.toFinset_nonempty]
  apply ΛₖNonempty

noncomputable
def δₚSplitMax (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε] :=
  ((Λₖ s t k).toFinset.image (δₚ s (t + ε))).max' (ΛₖtoδNonempty s t ε k)

lemma δₚSplitMaxInΔ (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε]:
δₚSplitMax s t ε k ∈ Δ s (t + ε) := by
  unfold δₚSplitMax
  obtain ⟨max, ⟨maxmem, maxspec⟩⟩ := Finset.mem_image.mp (Finset.max'_mem _ (ΛₖtoδNonempty s t ε k))
  rw [← maxspec]
  unfold δₚ Δ
  simp only [Set.mem_setOf_eq, exists_apply_eq_apply2]

lemma δₚSplitMaxSpec (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε]:
∀ pq ∈ (Λₖ s t k), δₚ s (t + ε) pq ≤ δₚSplitMax s t ε k := by
  intro pq pqmem
  have mem: δₚ s (t + ε) pq ∈ (Λₖ s t k).toFinset.image (δₚ s (t + ε)) := by
    simp only [Finset.mem_image, Set.mem_toFinset]
    use pq
  obtain le_max := Finset.le_max' _ _ mem
  exact le_max

noncomputable
def kSplitMax (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε] :=
(δₖ_surjΔ _ _ _ (δₚSplitMaxInΔ s t ε k)).choose

def kSplitMaxSpec (s t ε: ℝ) (k: ℕ) [PosReal s] [PosReal t] [PosReal ε]:
∀ pq ∈ (Λₖ s t k), δₚ s (t + ε) pq ≤ δₖ s (t + ε) (kSplitMax s t ε k) := by
  obtain spec := (δₖ_surjΔ _ _ _ (δₚSplitMaxInΔ s t ε k)).choose_spec
  unfold kSplitMax
  rw [spec]
  apply δₚSplitMaxSpec

lemma ΛceiledSplit (s t ε: ℝ) (k K: ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k ≤ K) (εbound: ε < t * εBound s t K):
Λceiled s t (δₖ s t k) = Λceiled s (t + ε) (δₖ s (t + ε) (kSplitMax s t ε k)) := by
  unfold Λceiled
  ext pq
  simp only [Set.mem_setOf_eq]
  have pqmem: pq.1 * s + pq.2 * t ∈ Δ s t := by unfold Δ; simp only [Set.mem_setOf_eq,
    exists_apply_eq_apply2]
  obtain ⟨k', k'eq⟩ := δₖ_surjΔ _ _ _ pqmem
  rw [← k'eq]
  rw [(δₖ_mono s t).le_iff_le]
  have pqmemSplit: pq ∈ Λₖ s t k' := by
    unfold Λₖ Λline δₚ
    simp only [Set.mem_preimage]
    apply Set.mem_singleton_of_eq
    rw [k'eq]
  rw [← δₚ]
  simp only [Prod.mk.eta]
  obtain spec := (δₖ_surjΔ _ _ _ (δₚSplitMaxInΔ s t ε k)).choose_spec
  constructor
  · intro k'lek
    obtain lt|eq := lt_or_eq_of_le k'lek
    · apply le_of_lt
      unfold kSplitMax
      rw [spec]
      obtain maxmem := Finset.max'_mem _ (ΛₖtoδNonempty s t ε k)
      simp only [Finset.mem_image, Set.mem_toFinset] at maxmem
      obtain ⟨pq', ⟨pq'mem, pq'eq⟩⟩ := maxmem
      unfold δₚSplitMax
      rw [← pq'eq]
      apply ΛₖMono s t ε k' k K lt (le_of_lt (lt_of_lt_of_le lt kBound))
        (le_of_lt PosReal.pos) εbound _ pqmemSplit _ pq'mem
    · apply kSplitMaxSpec
      rw[← eq]
      exact pqmemSplit
  · contrapose
    simp only [not_le]
    intro kltk'
    unfold kSplitMax
    rw [spec]
    unfold δₚSplitMax
    apply (Finset.max'_lt_iff _ (ΛₖtoδNonempty s t ε k)).mpr
    intro δ δeq
    simp only [Finset.mem_image, Set.mem_toFinset] at δeq
    obtain ⟨pq', ⟨pq'mem, pq'eq⟩⟩ := δeq
    rw [← pq'eq]
    apply ΛₖMono s t ε k k' K kltk' kBound (le_of_lt PosReal.pos) εbound _ pq'mem _ pqmemSplit

lemma ΛceiledSplit_s (s t ε: ℝ) (k K: ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k ≤ K) (εbound: ε < t * εBound s t K):
Λceiled s t (δₖ s t k - s) = Λceiled s (t + ε) (δₖ s (t + ε) (kSplitMax s t ε k) - s) := by
  unfold Λceiled
  ext pq
  simp only [Set.mem_setOf_eq]
  have left: pq.1 * s + pq.2 * t ≤ δₖ s t k - s ↔
        (pq.1 + 1: ℕ) * s + pq.2 * t ≤ δₖ s t k := by
    push_cast
    rw [add_one_mul, add_right_comm]
    exact le_sub_iff_add_le
  have right: pq.1 * s + pq.2 * (t + ε) ≤ δₖ s (t + ε) (kSplitMax s t ε k) - s  ↔
        (pq.1 + 1: ℕ) * s + pq.2 * (t + ε) ≤ δₖ s (t + ε) (kSplitMax s t ε k) := by
    push_cast
    rw [add_one_mul, add_right_comm]
    exact le_sub_iff_add_le
  rw [left, right]

  obtain Λsplit := ΛceiledSplit s t ε k K kBound εbound
  have ΛsplitExt : ∀ (pq: ℕ × ℕ), pq ∈ Λceiled s t (δₖ s t k) ↔ pq ∈ Λceiled s (t + ε) (δₖ s (t + ε) (kSplitMax s t ε k)) := by
    exact fun pq ↦ Eq.to_iff (congrFun Λsplit pq)
  unfold Λceiled at ΛsplitExt
  simp only [Set.mem_setOf_eq] at ΛsplitExt
  exact ΛsplitExt (pq.1 + 1, pq.2)


lemma nₖSplit (s t ε: ℝ) (k K: ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k ≤ K) (εbound: ε < t * εBound s t K):
nₖ s t (k + 1) = nₖ s (t + ε) (kSplitMax s t ε k + 1) := by
  rw [nₖ_accum, nₖ_accum]
  simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, add_right_inj]
  unfold Jceiled
  refine Finset.sum_congr ?_ (by simp only [Set.mem_toFinset, implies_true])
  simp only [Set.toFinset_inj]
  apply ΛceiledSplit s t ε k K kBound εbound

lemma wₖ'Split (s t ε: ℝ) (k K: ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k ≤ K) (εbound: ε < t * εBound s t K):
wₖ' s t (k + 1) = wₖ' s (t + ε) (kSplitMax s t ε k + 1) := by
  rw [wₖ'_accum, wₖ'_accum]
  simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, add_right_inj]
  unfold Jceiled
  refine Finset.sum_congr ?_ (by simp only [Set.mem_toFinset, implies_true])
  simp only [Set.toFinset_inj]
  apply ΛceiledSplit_s s t ε k K kBound εbound

lemma wₖSplit (s t ε: ℝ) (k K: ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k ≤ K) (εbound: ε < t * εBound s t K):
wₖ s t (k + 1) = wₖ s (t + ε) (kSplitMax s t ε k + 1) := by
  obtain n := nₖSplit s t ε k K kBound εbound
  obtain w' := wₖ'Split s t ε k K kBound εbound
  rw [← wₖ_rec _ _ _ (by apply Nat.le_add_left), ← wₖ_rec _ _ _ (by apply Nat.le_add_left)] at n
  rw [← wₖ_symm, ← wₖ_symm] at w'
  rw [← w'] at n
  exact Nat.add_right_cancel n

lemma δₖSplitBetween (s t ε: ℝ) (k K k': ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k < K) (εbound: ε < t * εBound s t K)
(k'left: kSplitMax s t ε k < k') (k'right: k' ≤ kSplitMax s t ε (k + 1)):
∃pq ∈ Λₖ s t (k + 1), δₖ s (t + ε) k' = δₚ s (t + ε) pq := by
  obtain ⟨p, q, pqeq⟩ := δₖ_in_Δ s (t + ε) k'
  rw [← pqeq]
  use (p, q)
  constructor
  · unfold kSplitMax at k'left k'right
    obtain δk'left := (δₖ_mono s (t + ε)).lt_iff_lt.mpr k'left
    obtain δk'right := (δₖ_mono s (t + ε)).le_iff_le.mpr k'right
    obtain k'leftspec := (δₖ_surjΔ _ _ _ (δₚSplitMaxInΔ s t ε k)).choose_spec
    obtain k'rightspec := (δₖ_surjΔ _ _ _ (δₚSplitMaxInΔ s t ε (k + 1))).choose_spec
    rw [k'leftspec] at δk'left
    rw [k'rightspec] at δk'right
    unfold δₚSplitMax at δk'left δk'right
    rw [← δₚ] at pqeq
    have leftLt: ∀pqk ∈ Λₖ s t k, δₚ s (t + ε) pqk < δₚ s (t + ε) (p, q) := by
      rw [pqeq]
      intro pqk pqkmem
      refine lt_of_le_of_lt ?_ δk'left
      apply Finset.le_max'
      simp only [Finset.mem_image, Set.mem_toFinset]
      use pqk
    have stpqmem: δₚ s t (p, q) ∈ Δ s t := by
      unfold δₚ Δ
      simp only [Set.mem_setOf_eq, exists_apply_eq_apply2]
    obtain ⟨k1, k1eq⟩ := δₖ_surjΔ s t _ stpqmem
    unfold Λₖ Λline
    simp only [Set.mem_preimage]
    rw [← k1eq]
    apply Set.mem_singleton_of_eq
    apply le_antisymm
    · apply (δₖ_mono s t).le_iff_le.mpr
      by_contra lt
      simp only [not_le] at lt
      obtain max := (Finset.image (δₚ s (t + ε)) (Λₖ s t (k + 1)).toFinset).max' (ΛₖtoδNonempty s t ε (k + 1))
      obtain maxmem := Finset.max'_mem _ (ΛₖtoδNonempty s t ε (k + 1))
      simp only [Finset.mem_image, Set.mem_toFinset] at maxmem
      obtain ⟨Λkpq, ⟨Λkpqmem, Λkpqeq⟩⟩ := maxmem
      obtain mono := ΛₖMono s t ε (k + 1) k1 K lt kBound (le_of_lt PosReal.pos) εbound
        Λkpq Λkpqmem (p, q) (Eq.symm k1eq)
      rw [pqeq] at mono
      obtain what := lt_of_lt_of_le mono δk'right
      rw [Λkpqeq] at what
      simp only [lt_self_iff_false] at what
    · apply (δₖ_mono s t).le_iff_le.mpr
      by_contra lt
      simp only [not_le] at lt
      obtain lt'|eq := lt_or_eq_of_le (Nat.le_of_lt_succ lt)
      · obtain ⟨Λkpq, Λkpqmem⟩ := ΛₖNonempty s t k
        obtain mono := ΛₖMono s t ε k1 k K lt' (le_of_lt (lt_trans lt' kBound)) (le_of_lt PosReal.pos)
          εbound (p, q) ((Eq.symm k1eq)) Λkpq Λkpqmem
        obtain leftLt' := leftLt Λkpq Λkpqmem
        obtain what := lt_trans leftLt' mono
        simp only [lt_self_iff_false] at what
      · rw [eq] at k1eq
        have pqmem: (p, q) ∈ Λₖ s t k := (Eq.symm k1eq)
        obtain what := leftLt (p, q) pqmem
        simp only [lt_self_iff_false] at what
  · rfl

/-
lemma δₖSplitBetweenUnique (s t ε: ℝ) (k K k': ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k < K) (εbound: ε < t * εBound s t K)
(k'left: kSplitMax s t ε k < k') (k'right: k' ≤ kSplitMax s t ε (k + 1)):
∃!pq, pq ∈ Λₖ s t (k + 1) ∧ δₖ s (t + ε) k' = δₚ s (t + ε) pq := by
  obtain ⟨pq, pqeq⟩ := δₖSplitBetween s t ε k K k' kBound εbound k'left k'right
  use pq
  simp only [and_imp]
  constructor
  · exact pqeq
  · intro pq' pq'eq δeq
    obtain ⟨pqmem, pqeq⟩ := pqeq
    rw [δeq] at pqeq
    exact (ΛₖSplit s t ε (k + 1) _ pq'eq _ pqmem).mpr pqeq
    -/

noncomputable
def pqOfδₖSplit (s t ε: ℝ) (k K k': ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k < K) (εbound: ε < t * εBound s t K)
(k'left: kSplitMax s t ε k < k') (k'right: k' ≤ kSplitMax s t ε (k + 1)) :=
(δₖSplitBetween s t ε k K k' kBound εbound k'left k'right).choose

noncomputable
def pqslot (pq: ℕ × ℕ) := (pq.2 / (pq.1 + pq.2): ℝ)

lemma Jslope (pq: ℕ × ℕ) (h: pq.2 ≠ 0):
(Jₚ (pq.1, pq.2 - 1) / Jₚ pq: ℝ) = pqslot pq := by
  unfold pqslot
  refine (div_eq_div_iff ?_ ?_).mpr ?_
  · norm_cast
    apply ne_of_gt
    apply Jₚ_nonzero
  · norm_cast
    omega
  · norm_cast
    unfold Jₚ
    simp only
    rw [mul_comm pq.2]
    rw [(by omega: pq.1 + pq.2 = pq.1 + (pq.2 - 1) + 1)]
    convert Nat.choose_mul_succ_eq (pq.1 + (pq.2 - 1)) pq.1
    omega


lemma wslope (s t ε: ℝ) (k K k': ℕ) [PosReal s] [PosReal t] [PosReal ε]
(kBound: k < K) (εbound: ε < t * εBound s t K)
(k'left: kSplitMax s t ε k < k') (k'right: k' ≤ kSplitMax s t ε (k + 1)):
((Jtₖ s (t + ε) k') / (Jₖ s (t + ε) k'): ℝ) = pqslot (pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right) := by

  unfold Jtₖ Jₖ Jline
  obtain ⟨exist, eq⟩ := (δₖSplitBetween s t ε k K k' kBound εbound k'left k'right).choose_spec
  unfold Λₖ at exist
  have rwJ: (Λline s (t + ε) (δₖ s (t + ε) k')).toFinset = {pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right} := by
    unfold pqOfδₖSplit
    refine Finset.eq_singleton_iff_unique_mem.mpr ?_
    simp only [Set.mem_toFinset]
    constructor
    · unfold Λline
      simp only [Set.mem_preimage]
      exact Set.mem_singleton_of_eq eq.symm
    · intro pq pqmem
      unfold Λline at pqmem
      simp only [Set.mem_preimage] at pqmem
      apply Set.mem_singleton_iff.mp at pqmem
      symm
      exact (ΛₖSplit' s t ε (k + 1) K kBound εbound _ exist _).mpr (Eq.trans pqmem eq).symm

  rw [rwJ]

  have memTranslate: ∀ pq ∈ (Λline s (t + ε) (δₖ s (t + ε) k' - (t + ε))),
    (pq.1, pq.2 + 1) ∈ (Λline s (t + ε) (δₖ s (t + ε) k')).toFinset := by
    intro pq pqmem
    unfold Λline δₚ at pqmem ⊢
    simp only [Set.mem_preimage] at pqmem
    simp only [Set.mem_toFinset, Set.mem_preimage]
    apply Set.mem_singleton_iff.mp at pqmem
    apply Set.mem_singleton_of_eq
    apply add_eq_of_eq_sub at pqmem
    rw [← pqmem]
    push_cast
    ring

  by_cases q0: (pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right).2 = 0
  · have rwJt: (Λline s (t + ε) (δₖ s (t + ε) k' - (t + ε))).toFinset = ∅ := by
      simp only [Set.toFinset_eq_empty]
      apply Set.eq_empty_of_forall_not_mem
      intro pq
      by_contra pqmem
      obtain what := memTranslate pq pqmem
      rw [rwJ] at what
      simp only [Finset.mem_singleton] at what
      obtain ⟨peq, qeq⟩ := Prod.eq_iff_fst_eq_snd_eq.mp what
      rw [q0] at qeq
      simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false] at qeq
    rw [rwJt]
    simp only [Finset.sum_empty, CharP.cast_eq_zero, Finset.sum_singleton, zero_div]
    unfold pqslot
    rw [q0]
    simp only [CharP.cast_eq_zero, add_zero, zero_div]
  · have q1: 1 ≤ (pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right).2 := by
      exact Nat.one_le_iff_ne_zero.mpr q0
    have rwJt: (Λline s (t + ε) (δₖ s (t + ε) k' - (t + ε))).toFinset = {(
      (pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right).1,
      (pqOfδₖSplit s t ε k K k' kBound εbound k'left k'right).2 - 1
    )} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ?_
      simp only [Set.mem_toFinset]
      obtain ⟨rwj, unique⟩ := Finset.eq_singleton_iff_unique_mem.mp rwJ
      unfold Λline δₚ at rwj
      simp only [Set.mem_toFinset, Set.mem_preimage] at rwj
      constructor
      · unfold Λline
        simp only [Set.mem_preimage]
        apply Set.mem_singleton_of_eq
        unfold δₚ
        apply eq_sub_of_add_eq
        simp only
        rw [add_assoc, ← add_one_mul]
        push_cast [q1]
        simp only [sub_add_cancel]
        exact rwj
      · intro pq pqmem
        obtain translate := memTranslate pq pqmem
        obtain ⟨peq, qeq⟩ := Prod.eq_iff_fst_eq_snd_eq.mp (unique _ translate)
        ext
        · exact peq
        · simp only
          simp only at qeq
          rw [← qeq]
          rw [Nat.add_sub_cancel]
    rw [rwJt]
    simp only [Finset.sum_singleton]
    apply Jslope _ q0
