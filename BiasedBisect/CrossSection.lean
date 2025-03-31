import BiasedBisect.Inert
import BiasedBisect.Split

@[ext]
structure InertSeg where
  a: ℕ+
  b: ℕ+
  c: ℕ+
  d: ℕ+
deriving Repr

def InertSeg.det1 (seg: InertSeg) := seg.a * seg.d = seg.b * seg.c + 1

lemma InertSeg.det1.le {seg: InertSeg} (h: seg.det1):
(seg.b / seg.a: ℝ) < seg.d / seg.c := by
  apply (div_lt_div_iff₀ (by simp only [Nat.cast_pos, PNat.pos]) (by simp only [Nat.cast_pos, PNat.pos])).mpr
  norm_cast
  rw [mul_comm seg.d seg.a]
  unfold InertSeg.det1 at h
  rw [h]
  exact PNat.lt_add_right (seg.b * seg.c) 1

def InertSeg.inert (n: ℕ+) (seg: InertSeg) := n ≤ nBranching seg.a seg.b seg.c seg.d

def genSeg (n: ℕ+) (input: List InertSeg): List InertSeg := match input with
| .nil => .nil
| .cons head tail =>
  if nBranching head.a head.b head.c head.d < n then
    [⟨head.a, head.b, head.a + head.c, head.b + head.d⟩,
     ⟨head.a + head.c, head.b + head.d, head.c, head.d⟩] ++ genSeg n tail
  else
    [head] ++ genSeg n tail

lemma genSegDet (n: ℕ+) (input: List InertSeg) (h: input.Forall InertSeg.det1):
(genSeg n input).Forall InertSeg.det1 := by
  unfold genSeg
  match input with
  | .nil => simp only [List.Forall]
  | .cons head tail =>
    simp only [List.cons_append, List.nil_append]
    simp only [List.forall_cons] at h
    obtain ⟨headh, tailh⟩ := h
    split
    · simp only [List.Forall, List.forall_cons]
      unfold InertSeg.det1 at headh
      constructor
      · unfold InertSeg.det1
        simp only
        rw [mul_add, mul_add]
        rw [headh]
        ring
      · constructor
        · unfold InertSeg.det1
          simp only
          rw [add_mul, add_mul]
          rw [headh]
          ring
        · apply genSegDet
          exact tailh
    · simp only [List.forall_cons]
      constructor
      · exact headh
      · apply genSegDet
        exact tailh

lemma genSegInert (n: ℕ+) (input: List InertSeg) (h: input.Forall (InertSeg.inert n)):
  (genSeg (n + 1) input).Forall (InertSeg.inert (n + 1)) := by
  unfold genSeg
  match input with
  | .nil => simp only [List.Forall]
  | .cons head tail =>
    simp only [List.cons_append, List.nil_append]
    simp only [List.forall_cons] at h
    obtain ⟨headh, tailh⟩ := h
    split_ifs with branching
    · simp only [List.Forall, List.forall_cons]
      unfold InertSeg.inert at headh
      constructor
      · unfold InertSeg.inert
        simp only [PNat.add_coe, PNat.val_ofNat]
        apply Nat.succ_le_of_lt
        apply lt_of_le_of_lt headh
        unfold nBranching
        simp only [add_lt_add_iff_left]
        refine Finset.sum_lt_sum_of_subset ?_ (i := (0, (head.a + (head.a + head.c) - 1))) ?_ ?_ (by apply Jₚ_nonzero) ?_
        · unfold Λtriangle
          simp only [PNat.add_coe, Set.subset_toFinset, Set.coe_toFinset, Set.setOf_subset_setOf,
            Prod.forall]
          intro p q pqmem
          obtain pqmemp := Nat.lt_of_add_right_lt pqmem
          rw [mul_comm] at pqmemp
          simp only [add_pos_iff, PNat.pos, or_self, mul_lt_mul_left] at pqmemp
          obtain pqmemq := Nat.lt_of_le_of_lt (Nat.le_add_left ..) pqmem
          simp only [add_pos_iff, PNat.pos, or_self, mul_lt_mul_right] at pqmemq

          rw [(by ring: p * (head.a + (head.a + head.c)) + q * (head.b + (head.b + head.d)) =
            p * (head.a + head.c) + q * (head.b + head.d) + p * head.a + q * head.b)]
          rw [(by ring: ((head.a + (head.a + head.c)) * (head.b + (head.b + head.d)): ℕ) =
            (head.a + head.c) * (head.b + head.d) + (head.b + head.d) * head.a + (head.a + head.c) * head.b + head.a * head.b)]
          refine lt_trans ?_ (lt_add_of_pos_right _ (by apply Nat.pos_of_neZero))
          refine add_lt_add (add_lt_add pqmem ?_) ?_
          · simp only [PNat.pos, mul_lt_mul_right]
            exact pqmemp
          · simp only [PNat.pos, mul_lt_mul_right]
            exact pqmemq
        · unfold Λtriangle
          simp only [PNat.add_coe, Set.mem_toFinset, Set.mem_setOf_eq, zero_mul, zero_add,
            add_pos_iff, PNat.pos, or_self, mul_lt_mul_right, tsub_lt_self_iff, Nat.lt_one_iff,
            pos_of_gt, and_self]
        · unfold Λtriangle
          simp only [Set.mem_toFinset, Set.mem_setOf_eq, zero_mul, zero_add, add_pos_iff, PNat.pos,
            or_self, mul_lt_mul_right, not_lt]
          rw [(by ring_nf: (head.a + (head.a + head.c) - 1:ℕ) = head.a + head.c + head.a - 1)]
          apply Nat.le_sub_of_add_le
          simp only [add_le_add_iff_left]
          exact NeZero.one_le
        · intro _ _ _
          apply Nat.zero_le
      · constructor
        · unfold InertSeg.inert
          simp only [PNat.add_coe, PNat.val_ofNat]
          apply Nat.succ_le_of_lt
          apply lt_of_le_of_lt headh
          unfold nBranching
          simp only [add_lt_add_iff_left]
          refine Finset.sum_lt_sum_of_subset ?_ (i := ((head.b + head.d +head.d - 1), 0)) ?_ ?_ (by apply Jₚ_nonzero) ?_
          · unfold Λtriangle
            simp only [PNat.add_coe, Set.subset_toFinset, Set.coe_toFinset, Set.setOf_subset_setOf,
              Prod.forall]
            intro p q pqmem
            obtain pqmemp := Nat.lt_of_add_right_lt pqmem
            rw [mul_comm] at pqmemp
            simp only [add_pos_iff, PNat.pos, or_self, mul_lt_mul_left] at pqmemp
            obtain pqmemq := Nat.lt_of_le_of_lt (Nat.le_add_left ..) pqmem
            simp only [add_pos_iff, PNat.pos, or_self, mul_lt_mul_right] at pqmemq
            rw [(by ring: p * (head.a + head.c + head.c) + q * (head.b + head.d + head.d) =
              p * (head.a + head.c) + q * (head.b + head.d) + p * head.c + q * head.d)]
            rw [(by ring: ((head.a + head.c + head.c) * (head.b + head.d + head.d): ℕ) =
              (head.a + head.c) * (head.b + head.d) + (head.b + head.d) * head.c + (head.a + head.c) * head.d + head.c * head.d)]
            refine lt_trans ?_ (lt_add_of_pos_right _ (by apply Nat.pos_of_neZero))
            refine add_lt_add (add_lt_add pqmem ?_) ?_
            · simp only [PNat.pos, mul_lt_mul_right]
              exact pqmemp
            · simp only [PNat.pos, mul_lt_mul_right]
              exact pqmemq
          · unfold Λtriangle
            simp only [PNat.add_coe, Set.mem_toFinset, Set.mem_setOf_eq, zero_mul, add_zero]
            rw [mul_comm]
            simp only [add_pos_iff, PNat.pos, or_self, mul_lt_mul_left, tsub_lt_self_iff,
              Nat.lt_one_iff, pos_of_gt, and_self]
          · unfold Λtriangle
            simp only [Set.mem_toFinset, Set.mem_setOf_eq, zero_mul, add_zero, not_lt]
            rw [mul_comm]
            simp only [add_pos_iff, PNat.pos, or_self, mul_le_mul_right]
            apply Nat.le_sub_of_add_le
            simp only [add_le_add_iff_left]
            exact NeZero.one_le
          · intro _ _ _
            apply Nat.zero_le
        · apply genSegInert
          exact tailh
    · simp only [List.forall_cons]
      constructor
      · unfold InertSeg.inert
        exact Nat.le_of_not_lt branching
      · apply genSegInert
        exact tailh

def segList (n: ℕ+): List InertSeg :=
PNat.recOn n [] (fun prevn prev ↦
  if prevn < 3 then [] else
  genSeg (prevn + 1) ([⟨prevn - 1, 1, prevn - 2, 1⟩] ++ prev ++ [⟨1, prevn - 2, 1, prevn - 1⟩])
)

#eval segList 4

lemma segListSucc (n: ℕ+) (h: ¬ n < 3):
segList (n + 1) = genSeg (n + 1) ([⟨n - 1, 1, n - 2, 1⟩] ++ (segList n) ++ [⟨1, n - 2, 1, n - 1⟩]) := by
  rw [segList]
  simp only [PNat.recOn_succ, h, ↓reduceIte]
  rfl

lemma List.forall_append (p : α → Prop) (xs ys : List α) :
    Forall p (xs ++ ys) ↔ Forall p xs ∧ Forall p ys := by
  match xs with
  | .nil => simp
  | .cons x xtail =>
    rw [cons_append, forall_cons, forall_cons, List.forall_append, and_assoc]

lemma segListDet (n: ℕ+): (segList n).Forall InertSeg.det1 := by
  induction n with
  | one =>
    unfold segList
    simp only [List.cons_append, List.nil_append, PNat.recOn_one, List.Forall.eq_1]
  | succ prevn prev =>
    by_cases h3: prevn < 3
    · unfold segList
      simp only [List.cons_append, List.nil_append, PNat.recOn_succ, h3, ↓reduceIte,
        List.Forall.eq_1]
    · rw [segListSucc prevn h3]
      simp only [not_lt] at h3
      have h1: 1 < prevn := lt_of_lt_of_le (by norm_num) h3
      have h2: 2 < prevn := lt_of_lt_of_le (by norm_num) h3
      apply genSegDet
      rw [List.forall_append, List.forall_append]
      constructor
      · constructor
        · unfold InertSeg.det1
          simp only [List.Forall, mul_one, one_mul]
          refine PNat.eq ?_
          rw [PNat.add_coe]
          rw [PNat.sub_coe, PNat.sub_coe]
          simp only [h1, ↓reduceIte, PNat.val_ofNat, h2, Nat.pred_eq_succ_iff]
          exact (Nat.sub_eq_iff_eq_add h1).mp rfl
        · exact prev
      · unfold InertSeg.det1
        simp only [List.Forall, mul_one, one_mul]
        refine PNat.eq ?_
        rw [PNat.add_coe]
        rw [PNat.sub_coe, PNat.sub_coe]
        simp only [h1, ↓reduceIte, PNat.val_ofNat, h2, Nat.pred_eq_succ_iff]
        exact (Nat.sub_eq_iff_eq_add h1).mp rfl

lemma segListInert (n: ℕ+): (segList n).Forall (InertSeg.inert n) := by
  induction n with
  | one =>
    unfold segList
    simp only [List.cons_append, List.nil_append, PNat.recOn_one, List.Forall]
  | succ prevn prev =>
    by_cases h3: prevn < 3
    · unfold segList
      simp only [List.cons_append, List.nil_append, PNat.recOn_succ, h3, ↓reduceIte,
        List.Forall.eq_1]
    · rw [segListSucc prevn h3]
      simp only [not_lt] at h3
      let a := prevn - 2
      have a2: prevn = a + 2 := by unfold a; refine Eq.symm (PNat.sub_add_of_lt ?_); exact h3
      have a1: prevn - 1 = a + 1 := by rw [a2]; exact rfl
      have arw: prevn - 2 = a := by rfl
      apply genSegInert
      rw [List.forall_append, List.forall_append]
      constructor
      · constructor
        · simp only [List.Forall]
          unfold InertSeg.inert
          unfold nBranching
          simp only
          rw [arw, a1, a2]
          push_cast
          rw [(by ring: (a + 2:ℕ) = 1 + (a + 1))]
          simp only [add_le_add_iff_left]
          apply le_trans
          · show a + 1 ≤ ∑ pq ∈ {0} ×ˢ (Finset.range (2 * a + 1)) , Jₚ pq
            unfold Jₚ
            simp only [Finset.singleton_product, Finset.sum_map, Function.Embedding.coeFn_mk,
              zero_add, Nat.choose_zero_right, Finset.sum_const, Finset.card_range, smul_eq_mul,
              mul_one, add_le_add_iff_right, PNat.pos, le_mul_iff_one_le_left, Nat.one_le_ofNat]
          · gcongr
            unfold Λtriangle
            simp only [Finset.singleton_product, PNat.add_coe, PNat.val_ofNat, Nat.reduceAdd,
              Set.subset_toFinset, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range,
              Set.image_subset_iff, Set.preimage_setOf_eq, zero_mul, zero_add, Nat.ofNat_pos,
              mul_lt_mul_right]
            intro p pmem
            simp only [Set.mem_Iio] at pmem
            simp only [Set.mem_setOf_eq]
            rw [(by ring: (a + 1 + a: ℕ) = 2 * a + 1)]
            exact pmem
        · exact prev
      · simp only [List.Forall]
        unfold InertSeg.inert
        unfold nBranching
        simp only
        rw [arw, a1, a2]
        push_cast
        rw [(by ring: (a + 2:ℕ) = 1 + (a + 1))]
        simp only [add_le_add_iff_left]
        apply le_trans
        · show a + 1 ≤ ∑ pq ∈ (Finset.range (2 * a + 1)) ×ˢ {0} , Jₚ pq
          unfold Jₚ
          simp only [Finset.product_singleton, Finset.sum_map, Function.Embedding.coeFn_mk,
            add_zero, Nat.choose_self, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
            add_le_add_iff_right, PNat.pos, le_mul_iff_one_le_left, Nat.one_le_ofNat]
        · gcongr
          unfold Λtriangle
          simp only [Finset.product_singleton, PNat.val_ofNat, Nat.reduceAdd, PNat.add_coe,
            Set.subset_toFinset, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_range,
            Set.image_subset_iff, Set.preimage_setOf_eq, zero_mul, add_zero]
          intro p pmem
          simp only [Set.mem_Iio] at pmem
          simp only [Set.mem_setOf_eq]
          rw [(by ring: 2 * (a + (a + 1): ℕ) = (2 * a + 1) * 2)]
          simp only [Nat.ofNat_pos, mul_lt_mul_right]
          exact pmem

def intervalList (n: ℕ+) := (segList n).map (fun seg ↦ Set.Icc (seg.b / seg.a: ℝ) (seg.d / seg.c))

lemma intervalPositive (n: ℕ+): (intervalList n).Forall (· ⊆ Set.Ioi 0) := by
  unfold intervalList
  simp only [List.forall_map_iff]
  refine List.forall_iff_forall_mem.mpr ?_
  intro seg segmem
  simp only [Function.comp_apply]
  refine (Set.Icc_subset_Ioi_iff ?_).mpr ?_
  · obtain det1 := List.forall_iff_forall_mem.mp (segListDet n) _ segmem
    exact le_of_lt det1.le
  · simp only [Nat.cast_pos, PNat.pos, div_pos_iff_of_pos_left]

noncomputable
def wₗᵢex (s t n: ℝ) :=
  if hs: s > 0 then
    if ht: t > 0 then
      have: PosReal s := {pos := hs}
      have: PosReal t := {pos := ht}
      wₗᵢ s t n
    else
      0
  else
    0

lemma wₗᵢAntiOnInterval (N: ℕ+) (n: ℝ) (hn: n ≤ N) (n2: 2 ≤ n):
(intervalList N).Forall (AntitoneOn (fun t ↦ wₗᵢex 1 t n)) := by
  unfold intervalList
  refine List.forall_iff_forall_mem.mpr ?_
  intro interval intervalmem
  obtain intervalsub := List.forall_iff_forall_mem.mp (intervalPositive N) _ intervalmem
  intro x xmem y ymem xley
  have xpos: x > 0 := intervalsub xmem
  have ypos: y > 0 := intervalsub ymem
  have: PosReal x := {pos := xpos}
  have: PosReal y := {pos := ypos}
  have: PosReal 1 := {pos := by norm_num}
  unfold wₗᵢex
  simp only [xpos, ypos, gt_iff_lt, zero_lt_one, ↓reduceDIte]
  simp at intervalmem
  obtain ⟨seg, ⟨segmem, segis⟩⟩ := intervalmem
  obtain det := List.forall_iff_forall_mem.mp (segListDet N) _ segmem
  obtain inert := List.forall_iff_forall_mem.mp (segListInert N) _ segmem
  rw [← segis] at xmem ymem
  obtain ⟨xleft, xright⟩ := xmem
  obtain ⟨yleft, yright⟩ := ymem

  obtain ⟨leftlimit, ⟨leftlimitpos, leftlimitspec⟩⟩ := wₗᵢtSplit 1 (seg.b / seg.a) n n2
  have leftset: (Set.Ioo 0 (min leftlimit (seg.d / seg.c - seg.b / seg.a))).Nonempty := by
    simp only [Set.nonempty_Ioo, lt_inf_iff, sub_pos]
    exact ⟨leftlimitpos, det.le⟩
  obtain ⟨lε, lεspec⟩ := leftset
  simp only [Set.mem_Ioo, lt_inf_iff] at lεspec
  obtain ⟨lεpos, lεsmall, lεinert⟩ := lεspec
  obtain leftle := leftlimitspec lε lεpos lεsmall
  simp only at leftle
  have: PosReal lε := {pos := by exact lεpos}
  have lεleft: seg.a * (seg.b / seg.a + lε) > seg.b * 1 := by
    simp only [mul_one, gt_iff_lt]
    rw [mul_add]
    rw [mul_div_cancel₀ _ (by simp)]
    exact lt_add_of_pos_right _ (mul_pos (by simp) lεpos)
  have lεright: seg.d * 1 > seg.c * (seg.b / seg.a + lε) := by
    simp only [mul_one, gt_iff_lt]
    apply (lt_div_iff₀' (by simp)).mp
    exact lt_tsub_iff_left.mp lεinert

  obtain ⟨rightlimit, ⟨rightlimitpos, rightlimitspec⟩⟩ := wₗᵢsSplit 1 (seg.d / seg.c) n n2
  have rightset: (Set.Ioo 0 (min rightlimit (seg.a * seg.d / (seg.b * seg.c) - 1))).Nonempty := by
    simp only [Set.nonempty_Ioo, lt_inf_iff, sub_pos]
    constructor
    · exact rightlimitpos
    · apply (one_lt_div (by simp only [Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left])).mpr
      norm_cast
      rw [det]
      exact PNat.lt_add_right (seg.b * seg.c) 1
  obtain ⟨rε, rεspec⟩ := rightset
  simp only [Set.mem_Ioo, lt_inf_iff] at rεspec
  obtain ⟨rεpos, rεsmall, rεinert⟩ := rεspec
  obtain rightle := rightlimitspec rε rεpos rεsmall
  simp only at rightle
  have: PosReal rε := {pos := by exact rεpos}
  have rεleft: seg.a * (seg.d / seg.c) > seg.b * (1 + rε) := by
    simp only [gt_iff_lt]
    rw [mul_div_assoc']
    apply (lt_div_iff₀' (by simp)).mp
    rw [div_div, mul_comm (seg.c:ℝ) seg.b]
    exact add_lt_of_lt_sub_left rεinert
  have rεright: seg.d * (1 + rε) > seg.c * (seg.d / seg.c) := by
    simp only [gt_iff_lt]
    rw [mul_div_cancel₀ _ (by simp), mul_one_add]
    simp only [lt_add_iff_pos_right, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left]
    exact rεpos

  have xleft' (h: seg.b / seg.a < x): seg.a * x > seg.b * 1 := by
    simp only [mul_one, gt_iff_lt]
    exact (div_lt_iff₀' (by simp only [Nat.cast_pos, PNat.pos])).mp h
  have xright' (h: x < seg.d / seg.c): ↑↑seg.d * 1 > ↑↑seg.c * x := by
    simp only [mul_one, gt_iff_lt]
    exact (lt_div_iff₀' (by simp only [Nat.cast_pos, PNat.pos])).mp h
  have yleft' (h: seg.b / seg.a < y): seg.a * y > seg.b * 1 := by
    simp only [mul_one, gt_iff_lt]
    exact (div_lt_iff₀' (by simp only [Nat.cast_pos, PNat.pos])).mp h
  have yright' (h: y < seg.d / seg.c): seg.d * 1 > seg.c * y := by
    simp only [mul_one, gt_iff_lt]
    exact (lt_div_iff₀' (by simp only [Nat.cast_pos, PNat.pos])).mp h

  have hBranching: n ≤ nBranching seg.a seg.b seg.c seg.d := le_trans hn (Nat.cast_le.mpr inert)
  obtain xeqleft|xgtleft := eq_or_lt_of_le xleft
  · obtain yeqleft|ygtleft := eq_or_lt_of_le yleft
    · simp_rw [← xeqleft, ← yeqleft]
      rfl
    · obtain yeqright|yltright := eq_or_lt_of_le yright
      · -- case: two edges
        simp_rw [yeqright, ← xeqleft]
        refine le_trans rightle (le_trans (le_of_eq ?_) leftle)
        exact wₗᵢ_inert seg.a seg.b seg.c seg.d _ _ _ _ _
          det rεleft rεright lεleft lεright n2 hBranching
      · -- case: left edge and interior
        simp_rw [← xeqleft]
        refine le_trans (le_of_eq ?_) leftle
        exact wₗᵢ_inert seg.a seg.b seg.c seg.d _ _ _ _ _
          det (yleft' ygtleft) (yright' yltright) lεleft lεright n2 hBranching
  · obtain xeqright|xltright := eq_or_lt_of_le xright
    · rw [xeqright] at xley
      obtain yeqright := le_antisymm xley yright
      simp_rw [xeqright, ← yeqright]
      rfl
    · obtain yeqright|yltright := eq_or_lt_of_le yright
      · -- case: interior and right edge
        simp_rw [yeqright]
        refine le_trans rightle (le_of_eq ?_)
        exact wₗᵢ_inert seg.a seg.b seg.c seg.d _ _ _ _ _
          det rεleft rεright (xleft' xgtleft) (xright' xltright) n2 hBranching
      · -- case: both interior
        apply le_of_eq
        exact wₗᵢ_inert seg.a seg.b seg.c seg.d 1 y 1 x n
          det (yleft' (lt_of_lt_of_le xgtleft xley)) (yright' yltright)
          (xleft' xgtleft) (xright' xltright) n2 hBranching
