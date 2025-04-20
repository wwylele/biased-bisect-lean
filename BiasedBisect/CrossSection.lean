import BiasedBisect.Inert
import BiasedBisect.Split
import Mathlib.Order.Monotone.Union

/-!
# Behavior of $E_{s,t}(n)$ and $w_{s,t}(n)$ for fixed $n$ and varying $s,t$

We will see that $w$ consists of a bunch of "blocks", whose interior displays Inert behavior,
while edges display Split behavior. We will explicitly construct this block list,
where each block is represented by inert tuples $(a, b, c, d)$.

## Main statements
 - `wₗᵢMono`: `wₗᵢ` is weakly monotone w.r.t. $s/t$.
-/

/-!
This encodes an inert tuple $(a, b, c, d)$, though on its own it is not necessarily one.
-/
@[ext]
structure InertSeg where
  a: ℕ+
  b: ℕ+
  c: ℕ+
  d: ℕ+
deriving Repr

/-!
An inert tuple must satisfy $ad - bc = 1$
-/
def InertSeg.det1 (seg: InertSeg) := seg.a * seg.d = seg.b * seg.c + 1

/-!
An inert tuple always creates a non-empty interval $[b/a, d/c]$.
-/
lemma InertSeg.det1.lt {seg: InertSeg} (h: seg.det1):
(seg.b / seg.a: ℝ) < seg.d / seg.c := by
  apply (div_lt_div_iff₀ (by simp only [Nat.cast_pos, PNat.pos])
    (by simp only [Nat.cast_pos, PNat.pos])).mpr
  norm_cast
  rw [mul_comm seg.d seg.a]
  unfold InertSeg.det1 at h
  rw [h]
  exact PNat.lt_add_right (seg.b * seg.c) 1

/-!
An inert tuple is actually inert if n is below the branching point.
-/
def InertSeg.inert (n: ℕ+) (seg: InertSeg) := n ≤ nBranching seg.a seg.b seg.c seg.d

/-!
Given a list of potentially inert tuple list,
the function `genSeg` divides those whose branching point is too small
to hopefully make the entire list actually inert.
-/
def genSeg (n: ℕ+) (input: List InertSeg): List InertSeg := match input with
| .nil => .nil
| .cons head tail =>
  if nBranching head.a head.b head.c head.d < n then
    [⟨head.a, head.b, head.a + head.c, head.b + head.d⟩,
     ⟨head.a + head.c, head.b + head.d, head.c, head.d⟩] ++ genSeg n tail
  else
    [head] ++ genSeg n tail

/-!
`genSeg` preserves $ad - bc = 1$.
-/
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

/-!
If the input list is inert for $n$, then the output is inert for $n + 1$.
-/
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

/-!
The explict inert tuple list is constructed as follows:
 - $n < 3$ is special cased and we will skip them here.
   - $n = 1$ is undefined for w.
   - $n = 2$ gives a constant function w.
 - $n = 3$ gives an empty list. This is also a special case but also serves as the base case.
 - starting from $n = 4$, we append $(n - 2, 1, n - 3, 1)$ and $(1, n - 3, 1, n - 2)$ to the two ends of the list
   and divide tuples to keep them inert.
-/
def segList (n: ℕ+): List InertSeg :=
PNat.recOn n [] (fun prevn prev ↦
  if prevn < 3 then [] else
  genSeg (prevn + 1) ([⟨prevn - 1, 1, prevn - 2, 1⟩] ++ prev ++ [⟨1, prevn - 2, 1, prevn - 1⟩])
)

/-!
The first non-empty list is at $n = 4$
-/
lemma segList4: segList 4 =
[{ a := 2, b := 1, c := 1, d := 1 }, { a := 1, b := 1, c := 1, d := 2 }] := by
  rfl

/-!
Restating the recursive definition of `segList` as a themorem.
-/
lemma segListSucc (n: ℕ+) (h: ¬ n < 3):
segList (n + 1) = genSeg (n + 1) ([⟨n - 1, 1, n - 2, 1⟩] ++ (segList n) ++ [⟨1, n - 2, 1, n - 1⟩]) := by
  rw [segList]
  simp only [PNat.recOn_succ, h, ↓reduceIte]
  rfl

/-!
`segList` always has $ad - bc = 1$ for all elements.
-/
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

/-!
`segList`'s elements are all inert.
-/
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

/-!
We will specialize $w$ function with $s = 1$ and varying $t$.

`segToInterval` converts inert tuple to intervals of $t$.
-/
def segToInterval (seg: InertSeg) := Set.Icc (seg.b / seg.a: ℝ) (seg.d / seg.c)

def intervalList (n: ℕ+) := (segList n).map segToInterval

/-!
All these intervals are positive numbers.
-/
lemma intervalPositive (n: ℕ+): (intervalList n).Forall (· ⊆ Set.Ioi 0) := by
  unfold intervalList
  simp only [List.forall_map_iff]
  refine List.forall_iff_forall_mem.mpr ?_
  intro seg segmem
  simp only [Function.comp_apply]
  refine (Set.Icc_subset_Ioi_iff ?_).mpr ?_
  · obtain det1 := List.forall_iff_forall_mem.mp (segListDet n) _ segmem
    exact le_of_lt det1.lt
  · simp only [Nat.cast_pos, PNat.pos, div_pos_iff_of_pos_left]

/-!
Define a `wₗᵢ` function without PosReal to help formulating theorems later
-/
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

/-!
`wₗᵢ` is antitonic w.r.t $t$ in each closed interval. This comes from the following two facts:
 - in the open interior, `wₗᵢ` is a constant, from Inert lemmas.
 - The left and right boundary Splits into the interior, inducing inequialities.
-/
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
  unfold wₗᵢex
  simp only [xpos, ypos, gt_iff_lt, zero_lt_one, ↓reduceDIte]
  simp only [List.mem_map] at intervalmem
  obtain ⟨seg, ⟨segmem, segis⟩⟩ := intervalmem
  obtain det := List.forall_iff_forall_mem.mp (segListDet N) _ segmem
  obtain inert := List.forall_iff_forall_mem.mp (segListInert N) _ segmem
  rw [← segis] at xmem ymem
  obtain ⟨xleft, xright⟩ := xmem
  obtain ⟨yleft, yright⟩ := ymem

  obtain ⟨leftlimit, ⟨leftlimitpos, leftlimitspec⟩⟩ := wₗᵢtSplit 1 (seg.b / seg.a) n n2
  have leftset: (Set.Ioo 0 (min leftlimit (seg.d / seg.c - seg.b / seg.a))).Nonempty := by
    simp only [Set.nonempty_Ioo, lt_inf_iff, sub_pos]
    exact ⟨leftlimitpos, det.lt⟩
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

/-!
Now that we have `AntitoneOn` in each interval, we'd like to glue them together.

The core theorem we want to use is `AntitoneOn.union_right`,
but we need to apply it repeatedly on the list.
To do so, we will need to formalize some properties about the list.
-/

/-!
A list of sets is called `SetsCover` iff
 - all the sets are non-empty Icc intervals, and
 - they connect to each other at boundaries.
-/
def SetsCover (list: List (Set ℝ)) (a b: ℝ): Prop := match list with
| [] => False
| [single] => single = Set.Icc a b ∧ a ≤ b
| head::tail => ∃c, head = Set.Icc a c ∧ a ≤ c ∧ SetsCover tail c b

/-!
A `SetsCover` list covers a large non-empty `Set.Icc` interval.
-/
lemma LeOfSetsCover (list: List (Set ℝ)) (a b: ℝ) (cover: SetsCover list a b):
a ≤ b := by match list with
| [] =>
  unfold SetsCover at cover
  exact False.elim cover
| [single] =>
  unfold SetsCover at cover
  obtain ⟨singleeq, aleb⟩ := cover
  exact aleb
| head::head2::tail =>
  unfold SetsCover at cover
  obtain ⟨c, ⟨headeq, alec, tailcover⟩⟩ := cover
  obtain cleb := LeOfSetsCover (head2::tail) c b tailcover
  exact le_trans alec cleb

/-!
Two `SetsCover` lists can be glued together.
-/
def SetsCoverAppend {l1 l2: List (Set ℝ)} {a b c: ℝ}
(h1: SetsCover l1 a b) (h2: SetsCover l2 b c):
SetsCover (l1 ++ l2) a c := by
  have l2long: ¬ l2 = [] := by
    by_contra l2empty
    rw [l2empty] at h2
    unfold SetsCover at h2
    exact h2
  match l1 with
  | [] =>
    unfold SetsCover at h1
    exact False.elim h1
  | [single] =>
    unfold SetsCover at h1
    obtain ⟨h1Icc, h1le⟩ := h1
    unfold SetsCover
    simp only [List.cons_append, List.nil_append, l2long]
    use b
  | head::head2::tail =>
    unfold SetsCover at h1
    obtain ⟨a', headIcc, aleb, tailcover⟩ := h1
    set tail' := head2 :: tail
    simp only [List.cons_append]
    use a'
    constructor
    · exact headIcc
    · constructor
      · exact aleb
      · exact SetsCoverAppend tailcover h2

/-!
The list version of `AntitoneOn.union_right`.
-/
lemma antitoneListUnion (f: ℝ → ℝ) (list: List (Set ℝ)) (a b: ℝ)
(cover: SetsCover list a b) (antitone: list.Forall (AntitoneOn f)):
AntitoneOn f (Set.Icc a b) := by match list with
| [] =>
  unfold SetsCover at cover
  exact False.elim cover
| [single] =>
  unfold SetsCover at cover
  obtain ⟨singleeq, aleb⟩ := cover
  rw [List.Forall, singleeq] at antitone
  exact antitone
| head::head2::tail =>
  unfold SetsCover at cover
  obtain ⟨c, ⟨headeq, alec, tailcover⟩⟩ := cover
  unfold List.Forall at antitone
  rw [headeq] at antitone
  obtain ⟨headanti, tailanti⟩ := antitone
  obtain cleb := LeOfSetsCover (head2::tail) c b tailcover
  rw [(Eq.symm (Set.Icc_union_Icc_eq_Icc alec cleb):
    Set.Icc a b = Set.Icc a c ∪ Set.Icc c b)]
  obtain tailanti' := antitoneListUnion f (head2::tail) c b tailcover tailanti
  obtain greatest: IsGreatest (Set.Icc a c) c := isGreatest_Icc alec
  obtain least: IsLeast (Set.Icc c b) c := isLeast_Icc cleb
  exact AntitoneOn.union_right headanti tailanti' greatest least

lemma IccEq {a b a' b': ℝ} (h: Set.Icc a b = Set.Icc a' b') (le: a ≤ b):
a = a' ∧ b = b' := by
  obtain nonempty := Set.nonempty_Icc.mpr le
  rw [h] at nonempty
  obtain le' := Set.nonempty_Icc.mp nonempty
  obtain least := isLeast_Icc le
  obtain least' := isLeast_Icc le'
  obtain greatest := isGreatest_Icc le
  obtain greatest' := isGreatest_Icc le'
  rw [h] at least greatest
  constructor
  · exact IsLeast.unique least least'
  · exact IsGreatest.unique greatest greatest'

/-!
`genSeg` preserves the `SetsCover` property.
-/
lemma genSegPreserveCovers (n: ℕ+) (list: List InertSeg) (a b: ℝ)
(hdet: list.Forall InertSeg.det1)
(hcover: SetsCover (list.map segToInterval) a b):
SetsCover ((genSeg n list).map segToInterval) a b := by match list with
| [] =>
  unfold SetsCover at hcover
  simp only [List.map_nil] at hcover
| [head] =>
  simp only [List.Forall] at hdet
  simp only [List.map_cons, List.map_nil] at hcover
  unfold genSeg
  split
  · unfold SetsCover segToInterval at hcover
    obtain ⟨abeq, aleb⟩ := hcover
    unfold SetsCover segToInterval
    simp only [List.cons_append, List.nil_append, List.map_cons, PNat.add_coe, Nat.cast_add]
    use ((head.b + head.d) / (head.a + head.c))
    obtain ⟨aeq, beq⟩ := IccEq abeq.symm aleb
    rw [aeq, beq]
    simp only [true_and]
    constructor
    · apply (div_le_div_iff₀ (by simp) (add_pos (by simp) (by simp))).mpr
      norm_cast
      rw [(by ring: head.b * (head.a + head.c) = head.a * head.b + head.b * head.c)]
      rw [(by ring: (head.b + head.d) * head.a = head.a * head.b + head.a * head.d)]
      simp only [add_le_add_iff_left]
      rw [hdet]
      exact le_of_lt (PNat.lt_add_right (head.b * head.c) 1)
    · unfold genSeg SetsCover
      simp only [List.map_nil, true_and]
      apply (div_le_div_iff₀ (add_pos (by simp) (by simp)) (by simp)).mpr
      norm_cast
      rw [(by ring: (head.b + head.d) * head.c = head.b * head.c + head.d * head.c)]
      rw [(by ring: head.d * (head.a + head.c) = head.a * head.d + head.d * head.c)]
      simp only [add_le_add_iff_right]
      rw [hdet]
      exact le_of_lt (PNat.lt_add_right (head.b * head.c) 1)
  · unfold genSeg
    simp only [List.append_nil, List.map_cons, List.map_nil]
    exact hcover
| head::head2::tail =>
  have longtail: ¬ List.map segToInterval (genSeg n (head2 :: tail)) = [] := by
    unfold genSeg
    split
    · simp
    · simp
  unfold List.Forall at hdet
  obtain ⟨headdet, taildet⟩ := hdet
  unfold SetsCover at hcover
  simp only [List.map_cons] at hcover
  obtain ⟨c, headIsIcc, alec, tailcover⟩ := hcover
  obtain tailcover' := genSegPreserveCovers n (head2::tail) _ _ taildet tailcover
  unfold genSeg
  split
  · simp only [List.cons_append, List.nil_append, List.map_cons]
    unfold SetsCover
    use ((head.b + head.d) / (head.a + head.c))
    unfold segToInterval at headIsIcc
    obtain ⟨aeq, ceq⟩ := IccEq headIsIcc.symm alec
    rw [aeq]
    constructor
    · unfold segToInterval
      simp only [PNat.add_coe, Nat.cast_add]
    · constructor
      · apply (div_le_div_iff₀ (by simp) (add_pos (by simp) (by simp))).mpr
        norm_cast
        rw [(by ring: head.b * (head.a + head.c) = head.a * head.b + head.b * head.c)]
        rw [(by ring: (head.b + head.d) * head.a = head.a * head.b + head.a * head.d)]
        simp only [add_le_add_iff_left]
        rw [headdet]
        exact le_of_lt (PNat.lt_add_right (head.b * head.c) 1)
      · unfold SetsCover
        simp only [longtail]
        use c
        constructor
        · unfold segToInterval
          rw [ceq]
          simp only [PNat.add_coe, Nat.cast_add]
        · constructor
          · rw [ceq]
            apply (div_le_div_iff₀ (add_pos (by simp) (by simp)) (by simp)).mpr
            norm_cast
            rw [(by ring: (head.b + head.d) * head.c = head.b * head.c + head.d * head.c)]
            rw [(by ring: head.d * (head.a + head.c) = head.a * head.d + head.d * head.c)]
            simp only [add_le_add_iff_right]
            rw [headdet]
            exact le_of_lt (PNat.lt_add_right (head.b * head.c) 1)
          · exact tailcover'
  · simp only [List.cons_append, List.nil_append, List.map_cons]
    unfold SetsCover
    simp only [longtail]
    use c

/-!
Our interval list is indeed `SetsCover`.
-/
lemma intervalListCover (n: ℕ+):
SetsCover (intervalList (n + 3)) (1 / (n + 1)) (n + 1) := by
  induction n with
  | one =>
    unfold intervalList
    rw [(by rfl: (1 + 3: ℕ+) = 4)]
    rw [segList4]
    unfold segToInterval
    simp only [List.map_cons, PNat.val_ofNat, Nat.cast_one, Nat.cast_ofNat, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, div_one, List.map_nil]
    norm_num
    unfold SetsCover
    use 1
    constructor
    · rfl
    · constructor
      · norm_num
      · unfold SetsCover
        exact ⟨rfl, by norm_num⟩
  | succ prev ih =>
    rw [(by rfl: prev + 1 + 3 = prev + 3 + 1)]
    unfold intervalList
    have cond: ¬ prev + 3 < 3 := by exact of_decide_eq_false rfl
    rw [segListSucc _ cond]
    apply genSegPreserveCovers _ _ _ _
    · rw [List.forall_append]
      constructor
      · rw [List.forall_append]
        constructor
        · unfold InertSeg.det1
          simp only [List.Forall, mul_one, one_mul]
          rfl
        · exact segListDet (prev + 3)
      · unfold InertSeg.det1
        simp only [List.Forall, mul_one, one_mul]
        rfl
    · simp only [List.map_append]
      refine SetsCoverAppend (SetsCoverAppend ?_ ih) ?_
      · unfold segToInterval SetsCover
        simp only [List.map_cons, PNat.val_ofNat, Nat.cast_one, one_div, List.map_nil, PNat.add_coe,
          Nat.cast_add]
        constructor
        · apply congr
          · apply congr rfl
            simp only [inv_inj]
            norm_cast
          · simp only [inv_inj]
            norm_cast
        · apply (inv_le_inv₀ (by linarith) (by linarith)).mpr
          simp only [le_add_iff_nonneg_right, zero_le_one]
      · unfold segToInterval SetsCover
        simp only [List.map_cons, PNat.val_ofNat, Nat.cast_one, div_one, List.map_nil, PNat.add_coe,
          Nat.cast_add, le_add_iff_nonneg_right, zero_le_one, and_true]
        apply congr
        · apply congr rfl
          norm_cast
        · norm_cast

/-!
Combining everything above, we show that `wₗᵢ 1 t n` is antitone on $[1 / (n - 2), n - 2]$ for integer $n$
(for non integer $n$, we just need to take a larger interger).
-/
lemma wₗᵢAntiOnMiddle (N: ℕ+) (n: ℝ) (hn: n ≤ N + 3) (n2: 2 ≤ n):
AntitoneOn (fun t ↦ wₗᵢex 1 t n) (Set.Icc (1 / (N + 1)) (N + 1)) := by
  apply antitoneListUnion
  · apply intervalListCover
  · apply wₗᵢAntiOnInterval
    · push_cast
      exact hn
    · exact n2

/-!
With Inert edge theories, we can show `wₗᵢ 1 t n` is antitone on $(0, 1 / (n -  2)]$ and on $[n - 2, ∞)$.
-/
lemma wₗᵢAntiOnLeft (N: ℕ+) (n: ℝ) (hn: n ≤ N + 3) (n2: 2 ≤ n):
AntitoneOn (fun t ↦ wₗᵢex 1 t n) (Set.Ioc 0 (1 / (N + 1))) := by
  have nN: n ≤ (N + 1: ℕ+) + 2 := by
    push_cast
    rw [add_assoc]
    norm_num
    exact hn
  intro x xmem y ymem xley
  simp only [one_div, Set.mem_Ioc] at xmem
  obtain ⟨xpos, xle⟩ := xmem
  simp only [one_div, Set.mem_Ioc] at ymem
  obtain ⟨ypos, yle⟩ := ymem
  have: PosReal x := {pos := xpos}
  have: PosReal y := {pos := ypos}
  unfold wₗᵢex
  simp only [gt_iff_lt, zero_lt_one, ↓reduceDIte, ypos, xpos, ge_iff_le]
  obtain ylt|yeq := lt_or_eq_of_le yle
  · obtain xlt := lt_of_le_of_lt xley ylt
    apply le_of_eq
    obtain ylt':= (inv_mul_lt_one₀
      (by simp only [inv_pos]; norm_cast; exact PNat.pos (N + 1))).mpr ylt
    simp only [inv_inv] at ylt'
    obtain xlt':= (inv_mul_lt_one₀
      (by simp only [inv_pos]; norm_cast; exact PNat.pos (N + 1))).mpr xlt
    simp only [inv_inv] at xlt'
    rw [wₗᵢ_inert_edge' (N + 1) 1 y n (by push_cast; exact ylt') n2 nN]
    rw [wₗᵢ_inert_edge' (N + 1) 1 x n (by push_cast; exact xlt') n2 nN]
  · obtain xlt|xeq := lt_or_eq_of_le xle
    · obtain ⟨εb, εbpos, εspec⟩ := wₗᵢsSplit 1 y n n2
      obtain ⟨ε, ⟨εpos, εlt⟩⟩: (Set.Ioo 0 εb).Nonempty := by
        simp only [Set.nonempty_Ioo]
        exact εbpos
      have: PosReal ε := {pos := by exact εpos}
      obtain split := εspec ε εpos εlt
      simp only at split
      apply le_trans split
      apply le_of_eq
      obtain xlt':= (inv_mul_lt_one₀
        (by simp only [inv_pos]; norm_cast; exact PNat.pos (N + 1))).mpr xlt
      simp only [inv_inv] at xlt'
      rw [wₗᵢ_inert_edge' (N + 1) 1 x n (by push_cast; exact xlt') n2 nN]
      rw [wₗᵢ_inert_edge' (N + 1) (1 + ε) y n (by
        rw [yeq];
        norm_cast
        rw [(mul_inv_eq_one₀ (by symm; apply NeZero.ne')).mpr rfl]
        exact lt_add_of_pos_right 1 εpos
      ) n2 nN]
    · simp_rw [xeq, yeq]
      rfl

lemma wₗᵢAntiOnRight (N: ℕ+) (n: ℝ) (hn: n ≤ N + 3) (n2: 2 ≤ n):
AntitoneOn (fun t ↦ wₗᵢex 1 t n) (Set.Ici (N + 1)) := by
  have nN: n ≤ (N + 1: ℕ+) + 2 := by
    push_cast
    rw [add_assoc]
    norm_num
    exact hn
  intro x xle y yle xley
  simp only [Set.mem_Ici] at xle
  simp only [Set.mem_Ici] at yle
  have xpos: 0 < x := lt_of_lt_of_le (by apply Nat.cast_add_one_pos) xle
  have ypos: 0 < y := lt_of_lt_of_le (by apply Nat.cast_add_one_pos) yle
  have: PosReal x := {pos := xpos}
  have: PosReal y := {pos := ypos}
  unfold wₗᵢex
  simp only [gt_iff_lt, zero_lt_one, ↓reduceDIte, ypos, xpos, ge_iff_le]
  obtain xlt|xeq := lt_or_eq_of_le xle
  · have ylt: N + 1 < y := lt_of_lt_of_le xlt xley
    rw [wₗᵢ_inert_edge (N + 1) 1 x n (by simpa using xlt) n2 nN]
    rw [wₗᵢ_inert_edge (N + 1) 1 y n (by simpa using ylt) n2 nN]
  · obtain ylt|yeq := lt_or_eq_of_le yle
    · obtain ⟨εb, εbpos, εspec⟩ := wₗᵢtSplit 1 x n n2
      obtain ⟨ε, ⟨εpos, εlt⟩⟩: (Set.Ioo 0 εb).Nonempty := by
        simp only [Set.nonempty_Ioo]
        exact εbpos
      have: PosReal ε := {pos := by exact εpos}
      obtain split := εspec ε εpos εlt
      simp only at split
      refine le_trans ?_ split
      apply le_of_eq
      rw [wₗᵢ_inert_edge (N + 1) 1 y n (by simpa using ylt) n2 nN]
      rw [wₗᵢ_inert_edge (N + 1) 1 (x + ε) n (by
        simp only [PNat.add_coe, PNat.val_ofNat, Nat.cast_add, Nat.cast_one, mul_one, gt_iff_lt]
        apply lt_of_le_of_lt xle
        exact lt_add_of_pos_right x εpos
      )  n2 nN]

    · simp_rw [← xeq, ← yeq]
      rfl

/-!
Gluing all them together, `wₗᵢ 1 t n` is antitone on all positive $t$.
We also drops the bounding `N` here as it is no longer in the result.
-/
lemma wₗᵢAnti (n: ℝ) (n2: 2 ≤ n):
AntitoneOn (fun t ↦ wₗᵢex 1 t n) (Set.Ioi 0) := by
  let N' := max 4 (Nat.ceil n) - 3
  let N: ℕ+ := ⟨N', (by unfold N'; simp)⟩
  have hn: n ≤ N + 3 := by
    unfold N N'
    simp only [PNat.mk_coe, le_sup_iff, Nat.reduceLeDiff, true_or, Nat.cast_sub, Nat.cast_max,
      Nat.cast_ofNat, sub_add_cancel]
    right
    exact Nat.le_ceil n
  obtain left := wₗᵢAntiOnLeft N n hn n2
  obtain mid := wₗᵢAntiOnMiddle N n hn n2
  obtain right := wₗᵢAntiOnRight N n hn n2

  have midinv: (1:ℝ) / (↑↑N + 1) ≤ ↑↑N + 1 := by
    simp only [one_div]
    refine le_trans ?_ (by simp: (1:ℝ) ≤ N + 1)
    apply inv_le_one_of_one_le₀
    simp

  have setrwleft: Set.Ioc 0 (1 / (N + 1):ℝ) ∪ Set.Icc (1 / (N + 1):ℝ) (N + 1) = Set.Ioc 0 (N + 1:ℝ) := by
    refine Set.Ioc_union_Icc_eq_Ioc ?_ midinv
    simp only [one_div, inv_pos]
    exact Nat.cast_add_one_pos N
  have setrw: Set.Ioi (0:ℝ) = Set.Ioc 0 (1 / (N + 1):ℝ)
    ∪ Set.Icc (1 / (N + 1):ℝ) (N + 1)
    ∪ Set.Ici (N + 1:ℝ) := by
    rw [setrwleft]
    symm
    apply Set.Ioc_union_Ici_eq_Ioi
    exact Nat.cast_add_one_pos ↑N

  have leftGreatest: IsGreatest (Set.Ioc 0 (1 / (N + 1):ℝ)) (1 / (N + 1):ℝ) := by
    exact isGreatest_Ioc Nat.one_div_pos_of_nat
  have leftLeast: IsLeast (Set.Icc (1 / (N + 1):ℝ) (N + 1)) (1 / (N + 1):ℝ) := by
    exact isLeast_Icc midinv

  have rightGreatest: IsGreatest (Set.Ioc 0 (1 / (N + 1):ℝ) ∪ Set.Icc (1 / (N + 1):ℝ) (N + 1)) (N + 1:ℝ) := by
    rw [setrwleft]
    exact isGreatest_Ioc (Nat.cast_add_one_pos N)
  have rightLeast: IsLeast (Set.Ici (N + 1:ℝ)) (N + 1:ℝ) := by
    exact isLeast_Ici

  rw [setrw]
  exact (left.union_right mid leftGreatest leftLeast).union_right
    right rightGreatest rightLeast

/-!
Restating the previous theorem for general $s$ and $t$.
-/
lemma wₗᵢMono (s1 t1 s2 t2 n: ℝ) (n2: 2 ≤ n)
[PosReal s1] [PosReal t1] [PosReal s2] [PosReal t2]
(h: s1 / t1 ≤ s2 / t2):
wₗᵢ s1 t1 n ≤ wₗᵢ s2 t2 n := by
  have rw1: wₗᵢ s1 t1 n = wₗᵢ 1 (t1 / s1) n := by
    simp_rw [(by ring: t1 / s1 = s1⁻¹ * t1)]
    simp_rw [((inv_mul_cancel₀ (ne_of_gt PosReal.pos)).symm: 1 = s1⁻¹ * s1)]
    apply wₗᵢ_homo
  have rw2: wₗᵢ s2 t2 n = wₗᵢ 1 (t2 / s2) n := by
    simp_rw [(by ring: t2 / s2 = s2⁻¹ * t2)]
    simp_rw [((inv_mul_cancel₀ (ne_of_gt PosReal.pos)).symm: 1 = s2⁻¹ * s2)]
    apply wₗᵢ_homo
  rw [rw1, rw2]
  have pos1: t1 / s1 > 0 := div_pos PosReal.pos PosReal.pos
  have pos2: t2 / s2 > 0 := div_pos PosReal.pos PosReal.pos
  have le: t2 / s2 ≤ t1 / s1 := by
    apply (div_le_div_iff₀ PosReal.pos PosReal.pos).mpr
    rw [mul_comm t2 s1, mul_comm t1 s2]
    exact (div_le_div_iff₀ PosReal.pos PosReal.pos).mp h
  have one: (1:ℝ) > 0 := by norm_num
  obtain anti := wₗᵢAnti n n2 pos2 pos1 le
  unfold wₗᵢex at anti
  simp only [pos1, pos2, one, ↓reduceDIte] at anti
  exact anti
