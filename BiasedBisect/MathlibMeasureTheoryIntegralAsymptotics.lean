import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

open Asymptotics Filter MeasureTheory

section LinearOrder

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [LinearOrder α] [Nonempty α] [OrderClosedTopology α]
variable {f : α → E} {g : α → ℝ} {μ : Measure α}

theorem Asymptotics.IsBigOWith.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    {c : ℝ} (hfg: IsBigOWith c atTop f g)
    (hf: ∀ a, IntegrableOn f (Set.Iic a) μ)
    (hg: ∀ a, IntegrableOn g (Set.Iic a) μ)
    (h_nonneg: ∀ᶠ x in atTop, 0 ≤ g x)
    (h_tendsto: Tendsto (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) atTop atTop):
    ∀ c' > c, IsBigOWith c' atTop
      (fun a ↦ ∫ x in (Set.Iic a), f x ∂μ) (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) := by
  intro c' hc
  apply Asymptotics.isBigOWith_iff.mpr
  conv in _ ≤ _ => rw [← sub_nonneg]
  refine Filter.tendsto_atTop.mp ?_ 0

  obtain ⟨m_integral_nonneg, h_integral_nonneg⟩ := tendsto_atTop_atTop.mp h_tendsto 0
  obtain ⟨m_nonneg, h_nonneg'⟩ := eventually_atTop.mp h_nonneg
  obtain ⟨m_fg, hfg'⟩ := eventually_atTop.mp <| Asymptotics.isBigOWith_iff.mp hfg

  let m := max m_integral_nonneg (max m_nonneg m_fg)

  have hfm {b: α}: IntegrableOn f (Set.Ioc m b) μ := (hf b).mono_set Set.Ioc_subset_Iic_self
  have hgm {b: α}: IntegrableOn g (Set.Ioc m b) μ := (hg b).mono_set Set.Ioc_subset_Iic_self

  have : (fun a ↦
      c' * (∫ (x : α) in Set.Iic m, g x ∂μ)
      + c' * (∫ (x : α) in Set.Ioc m a, g x ∂μ)
      - ‖∫ (x : α) in Set.Iic a, f x ∂μ‖)
    =ᶠ[atTop] (fun a ↦ c' *
      ‖∫ (x : α) in Set.Iic a, g x ∂μ‖
      - ‖∫ (x : α) in Set.Iic a, f x ∂μ‖) := by
    apply Filter.eventually_atTop.mpr
    use m
    intro b hmb
    simp only [Real.norm_eq_abs, sub_left_inj]
    rw [← mul_add]
    refine mul_eq_mul_left_iff.mpr (Or.inl ?_)
    have h_integral_nonneg': 0 ≤ ∫ (x : α) in Set.Iic b, g x ∂μ := by
      apply h_integral_nonneg
      refine le_trans ?_ hmb
      unfold m
      exact le_sup_left

    rw [abs_eq_self.mpr h_integral_nonneg']
    rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioc (le_refl _))
      measurableSet_Ioc (hg m) hgm]
    rw [Set.Iic_union_Ioc_eq_Iic hmb]
  apply Filter.Tendsto.congr' this

  have : (fun a ↦
      c' * (∫ (x : α) in Set.Iic m, g x ∂μ)
      - ‖∫ (x : α) in Set.Iic m, f x ∂μ‖
      + (c' - c) * (∫ (x : α) in Set.Ioc m a, g x ∂μ))
    ≤ᶠ[atTop] (fun a ↦
      c' * (∫ (x : α) in Set.Iic m, g x ∂μ)
      + c' * (∫ (x : α) in Set.Ioc m a, g x ∂μ)
      - ‖∫ (x : α) in Set.Iic a, f x ∂μ‖) := by
    apply Filter.eventually_atTop.mpr
    use m
    intro b hmb
    simp only
    rw [sub_mul, add_sub, ← add_sub_right_comm, sub_sub]
    apply sub_le_sub_left
    have : Set.Iic b = Set.Iic m ∪ Set.Ioc m b := (Set.Iic_union_Ioc_eq_Iic hmb).symm
    rw [this]
    rw [MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioc (le_refl _))
      measurableSet_Ioc (hf m) hfm]
    apply le_trans (norm_add_le _ _)
    apply add_le_add_left
    apply le_trans (MeasureTheory.norm_integral_le_integral_norm _)
    rw [← integral_mul_left]
    apply MeasureTheory.integral_mono_ae hfm.norm (hgm.const_mul _)
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
    apply Eventually.of_forall
    intro x ⟨hx, _⟩
    have hx' : m_fg ≤ x := by
      refine le_of_lt <| lt_of_le_of_lt ?_ hx
      exact le_sup_of_le_right <| le_sup_right
    convert hfg' x hx'
    refine (abs_eq_self.mpr ?_).symm
    apply h_nonneg'
    refine le_of_lt <| lt_of_le_of_lt ?_ hx
    exact le_sup_of_le_right <| le_sup_left

  refine Filter.tendsto_atTop_mono' _ this ?_
  apply Filter.Tendsto.add_atTop tendsto_const_nhds
  apply Filter.Tendsto.const_mul_atTop (sub_pos.mpr hc)
  apply Filter.Tendsto.atTop_of_const_add (∫ (x : α) in Set.Iic m, g x ∂μ)

  have: (fun x ↦ ∫ (x : α) in Set.Iic x, g x ∂μ) =ᶠ[atTop]
    (fun x ↦ ∫ (x : α) in Set.Iic m, g x ∂μ + ∫ (x : α) in Set.Ioc m x, g x ∂μ) := by
    apply Filter.eventually_atTop.mpr
    use m
    intro b hmb
    simp only
    rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioc (le_refl _))
      measurableSet_Ioc (hg m) hgm]
    rw [Set.Iic_union_Ioc_eq_Iic hmb]
  exact h_tendsto.congr' this

theorem Asymptotics.IsBigO.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    (hfg: f =O[atTop] g)
    (hf: ∀ a, IntegrableOn f (Set.Iic a) μ)
    (hg: ∀ a, IntegrableOn g (Set.Iic a) μ)
    (h_nonneg: ∀ᶠ x in atTop, 0 ≤ g x)
    (h_tendsto: Tendsto (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) atTop atTop):
    (fun a ↦ ∫ x in (Set.Iic a), f x ∂μ) =O[atTop] (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) := by
  obtain ⟨c, hfg'⟩ := hfg.isBigOWith
  obtain ⟨c', hc⟩ := NoMaxOrder.exists_gt c
  exact (hfg'.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    hf hg h_nonneg h_tendsto c' hc).isBigO

theorem Asymptotics.IsLittleO.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    (hfg: f =o[atTop] g)
    (hf: ∀ a, IntegrableOn f (Set.Iic a) μ)
    (hg: ∀ a, IntegrableOn g (Set.Iic a) μ)
    (h_nonneg: ∀ᶠ x in atTop, 0 ≤ g x)
    (h_tendsto: Tendsto (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) atTop atTop):
    (fun a ↦ ∫ x in (Set.Iic a), f x ∂μ) =o[atTop] (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) := by
  apply Asymptotics.IsLittleO.of_isBigOWith
  intro c hc
  obtain ⟨c', hc'_pos, hc'c⟩ := exists_between hc
  exact (hfg.forall_isBigOWith hc'_pos).atTop_integral_Iic_of_nonneg_of_tendsto_integral
    hf hg h_nonneg h_tendsto c hc'c

theorem Asymptotics.IsEquivalent.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    {f : α → ℝ}
    (hfg: f ~[atTop] g)
    (hf: ∀ a, IntegrableOn f (Set.Iic a) μ)
    (hg: ∀ a, IntegrableOn g (Set.Iic a) μ)
    (h_nonneg: ∀ᶠ x in atTop, 0 ≤ g x)
    (h_tendsto: Tendsto (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) atTop atTop):
    (fun a ↦ ∫ x in (Set.Iic a), f x ∂μ) ~[atTop] (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) := by
  apply Asymptotics.IsLittleO.isEquivalent
  have: (fun a ↦ ∫ x in Set.Iic a, f x ∂μ) - (fun a ↦ ∫ x in Set.Iic a, g x ∂μ)
    = fun a ↦ ∫ x in Set.Iic a, f x - g x ∂μ := by
    ext a
    simp only [Pi.sub_apply]
    rw [← integral_sub (hf a) (hg a)]
  rw [this]
  exact hfg.isLittleO.atTop_integral_Iic_of_nonneg_of_tendsto_integral
    (fun a ↦ (hf a).sub (hg a)) hg h_nonneg h_tendsto

theorem Asymptotics.IsEquivalent.integral_real_Ioc {f g : ℝ → ℝ}
    (hfg : f ~[atTop] g)
    {a : ℝ}
    (hf : ∀ x ≥ a, IntegrableOn f (Set.Ioc a x))
    (hg : ∀ x ≥ a, IntegrableOn g (Set.Ioc a x))
    (h_tendsto : Tendsto g atTop atTop):
    (∫ t in Set.Ioc a ·, f t) ~[atTop] (∫ t in Set.Ioc a ·, g t) := by
  have hg_all (x : ℝ) : IntegrableOn g (Set.Ioc a x) := by
    by_cases h : a ≤ x
    · exact hg x h
    · rw [Set.Ioc_eq_empty (by
        simp only [not_lt]
        exact le_of_lt <| lt_of_not_ge h
      )]
      simp

  have h_nonneg: ∀ᶠ x in atTop, 0 ≤ g x := Tendsto.eventually_ge_atTop h_tendsto 0
  let μ := volume.restrict (Set.Ioi a)
  have h_tendsto': Tendsto (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) atTop atTop := by
    obtain ⟨z, hz⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 0
    have : (fun a ↦ ∫ x in (Set.Iic z), g x ∂μ) + (fun a ↦ ∫ x in (Set.Ioc z a), g x ∂μ) =ᶠ[atTop]
      (fun a ↦ ∫ x in (Set.Iic a), g x ∂μ) := by
      apply eventually_atTop.mpr
      use z
      intro b hb
      simp only [Pi.add_apply]
      have hza: IntegrableOn g (Set.Ioc z b) μ := by
        unfold μ IntegrableOn
        rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioi]
        exact (hg_all b).mono_set <| Set.Ioc_subset_Ioc_left (by simp)
      have hz: IntegrableOn g (Set.Iic z) μ := by
        unfold μ IntegrableOn
        rw [Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
        exact hg_all z
      rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioc (le_refl _))
        measurableSet_Ioc hz hza]
      rw [Set.Iic_union_Ioc_eq_Iic hb]
    apply Filter.Tendsto.congr' this
    apply Filter.Tendsto.add_atTop tendsto_const_nhds
    obtain ⟨c, hc⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 1
    apply Filter.tendsto_atTop_atTop.mpr
    intro v
    use (max (max z a) c) + (max 0 v)
    intro x hx
    unfold μ
    rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioi]
    have: Set.Ioc (max (max z a) c) x ≤ᶠ[ae volume] Set.Ioc (max z a) x := by
      exact Eventually.of_forall <| Set.Ioc_subset_Ioc_left <| le_max_left _ _
    refine le_trans ?_ (MeasureTheory.setIntegral_mono_set ?_ ?_ this)
    · have h_zac: IntegrableOn g (Set.Ioc (max (max z a) c) x) := by
        exact (hg_all x).mono_set <| Set.Ioc_subset_Ioc_left (by simp)
      have : 1 ≤ᵐ[volume.restrict (Set.Ioc (max (max z a) c) x)] g := by
        apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        apply Eventually.of_forall
        intro y ⟨hy, _⟩
        apply hc y <| le_of_lt <| (max_lt_iff.mp hy).2
      refine le_trans ?_ (MeasureTheory.integral_mono_ae
        (by apply MeasureTheory.integrable_const) h_zac this)
      simp only [Pi.one_apply, integral_const, MeasurableSet.univ, Measure.restrict_apply,
        Set.univ_inter, Real.volume_Ioc, smul_eq_mul, mul_one]
      rw [ENNReal.toReal_ofReal (le_trans (by simp) <| le_tsub_of_add_le_left hx)]
      exact le_trans (by simp) <| le_tsub_of_add_le_left hx
    · exact (hg_all x).mono_set <| Set.Ioc_subset_Ioc_left (by simp)
    · apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      apply Eventually.of_forall
      intro y ⟨hy, _⟩
      apply hz y <| le_of_lt (max_lt_iff.mp hy).1

  have hf': ∀ b, IntegrableOn f (Set.Iic b) μ := by
    intro b
    unfold μ IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Iic]
    apply (hf (max a b) (le_max_left a b)).mono_set
    rw [Set.Iic_inter_Ioi]
    exact Set.Ioc_subset_Ioc_right le_sup_right
  have hg': ∀ b, IntegrableOn g (Set.Iic b) μ := by
    intro b
    unfold μ IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Iic]
    apply (hg (max a b) (le_max_left a b)).mono_set
    rw [Set.Iic_inter_Ioi]
    exact Set.Ioc_subset_Ioc_right le_sup_right

  have (fn: ℝ → ℝ): (fun x ↦ ∫ (t : ℝ) in Set.Ioc a x, fn t) = fun x ↦ ∫ (t : ℝ) in Set.Iic x, fn t ∂μ := by
    ext x
    unfold μ
    congr 1
    rw [Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]

  rw [this f, this g]
  exact hfg.atTop_integral_Iic_of_nonneg_of_tendsto_integral hf' hg' h_nonneg h_tendsto'

end LinearOrder
