
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Instances.Rat


open Set Filter TopologicalSpace Topology Function
variable {α γ : Type*}
variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

protected theorem Set.Subset.isLUB_congr {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsLUB s x ↔ IsLUB t x :=
  isLUB_congr <| (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm <|
    upperBounds_mono_set hst

protected theorem Set.Subset.isGLB_congr {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsGLB s x ↔ IsGLB t x :=
  Set.Subset.isLUB_congr (α := αᵒᵈ) hst hts

theorem Dense.isLUB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsLUB (t ∩ s) x ↔ IsLUB t x :=
  Set.Subset.isLUB_congr (by simp) <| hs.open_subset_closure_inter ht

theorem Dense.isGLB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIciTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsGLB (t ∩ s) x ↔ IsGLB t x :=
  Dense.isLUB_inter_iff (α := αᵒᵈ) hs ht

theorem Dense.exists_seq_strictMono_tendsto' [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : y < x) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Ioo y x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  have hnonempty : (Ioo y x ∩ s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
  have hx : IsLUB (Ioo y x ∩ s) x := hs.isLUB_inter_iff isOpen_Ioo |>.mpr <| isLUB_Ioo hy
  obtain ⟨u, hu⟩ := hx.exists_seq_strictMono_tendsto_of_not_mem (by simp) hnonempty
  exact ⟨u, hu.1, hu.2.2.symm⟩

theorem Dense.exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Iio x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ : ∃ y, y < x := exists_lt x
  obtain ⟨u, hu_mono, hu_mem, hux⟩ := hs.exists_seq_strictMono_tendsto' hy
  have hu_mem' (n) : u n ∈ Iio x ∩ s :=
    Set.mem_of_mem_of_subset (hu_mem n) <| inter_subset_inter_left _ Ioo_subset_Iio_self
  exact ⟨u, hu_mono, hu_mem', hux⟩

theorem Dense.exists_seq_strictAnti_tendsto' [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : x < y) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioo x y ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using hs.exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

theorem Dense.exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioi x ∩ s)) ∧ Tendsto u atTop (𝓝 x) :=
  hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x

lemma StrictMono_coe {f: ℕ → ℚ} (h: StrictMono (((↑) : ℚ → ℝ) ∘ f)):
    StrictMono f := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  obtain h' := h (lt_add_one n: n < n + 1)
  simp at h'
  exact h'

theorem Rat.exists_seq_strictMono_tendsto_real (x : ℝ):
∃ (u : ℕ → ℚ), StrictMono u ∧ (∀ (n : ℕ), u n < x) ∧
Filter.Tendsto (fun n ↦ (u n: ℝ)) Filter.atTop (nhds x) := by
  obtain ⟨u, hu_mono, hu_mem, hux⟩ := Dense.exists_seq_strictMono_tendsto
    Rat.isDenseEmbedding_coe_real.dense x
  obtain hu_mem' := fun n => (Set.mem_inter_iff _ _ _).mp <| hu_mem n
  let v := fun n => (hu_mem' n).2.choose
  let hv_spec := fun n => (hu_mem' n).2.choose_spec
  have hu_comp: u = ((↑) : ℚ → ℝ) ∘ v := by
    ext n
    simp only [Function.comp_apply]
    rw [hv_spec n]
  rw [hu_comp] at hu_mono
  have hv_mono: StrictMono v := StrictMono_coe hu_mono
  use v
  constructor
  · exact hv_mono
  · constructor
    · intro n
      rw [hv_spec]
      exact (hu_mem' n).1
    · conv in fun n ↦ _ =>
        ext n
        rw [hv_spec]
      exact hux

theorem Rat.exists_seq_strictAnti_tendsto_real (x : ℝ):
∃ (u : ℕ → ℚ), StrictAnti u ∧ (∀ (n : ℕ), x < u n) ∧
Filter.Tendsto (fun n ↦ (u n: ℝ)) Filter.atTop (nhds x) := by
  obtain ⟨u, hu_mono, hu_mem, hux⟩ := Rat.exists_seq_strictMono_tendsto_real (-x)
  use fun n ↦ -(u n)
  constructor
  · exact StrictMono.neg hu_mono
  · constructor
    · intro n
      simp only [cast_neg]
      exact lt_neg_of_lt_neg (hu_mem n)
    · simp only [cast_neg]
      rw [(by simp: x = - - x)]
      exact Filter.Tendsto.comp (tendsto_neg _) hux
