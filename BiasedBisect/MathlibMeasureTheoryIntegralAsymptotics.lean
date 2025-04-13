import Mathlib

open Asymptotics Filter MeasureTheory

theorem integral_equivalent (f g F G : ℝ → ℝ) (a : ℝ)
    (hf_tendsto : Tendsto f atTop atTop)
    (hfg : f ~[atTop] g)
    (hF : ∀ x ∈ Set.Ici a, F x = ∫ t in Set.Ioc a x, f t)
    (hG : ∀ x ∈ Set.Ici a, G x = ∫ t in Set.Ioc a x, G t):
    F ~[atTop] g := by

  have hf0 : ∀ᶠ x in atTop, f x ≠ 0 := Tendsto.eventually_ne_atTop hf_tendsto 0

  obtain hgdivf := tendsto_atTop_nhds.mp ((isEquivalent_iff_tendsto_one hf0).mp hfg.symm)

  have what (u v: ℝ) (h1: 1 ∈ Set.Ioo u v): False := by
    obtain ⟨X, hX⟩ := hgdivf (Set.Ioo u v) h1 isOpen_Ioo
    sorry


  sorry

theorem Asymptotics.IsLittleO.integral {f g : ℝ → ℝ}
    (hfg : f =o[atTop] g)
    (hg_tendsto : Tendsto g atTop atTop)
    {a : ℝ}
    (hf_integrable : ∀ x ≥ a, IntegrableOn f (Set.Ioc a x))
    (hg_integrable : ∀ x ≥ a, IntegrableOn g (Set.Ioc a x)):
    (∫ t in Set.Ioc a ·, f t) =o[atTop] (∫ t in Set.Ioc a ·, ‖g t‖) := by
  rw [Asymptotics.IsLittleO_def]
  intro c hc
  obtain ⟨c', ⟨hc'_pos, hc'c⟩⟩ := Set.nonempty_Ioo.mpr hc
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp (hfg.def hc'_pos)
  rw [Asymptotics.isBigOWith_iff]
  rw [Filter.eventually_atTop]
  obtain ⟨b', hb'⟩ := Filter.tendsto_atTop_atTop.mp hg_tendsto
    (((∫ t in Set.Ioc a b, ‖f t‖) - c * ∫ t in Set.Ioc a b, ‖g t‖) / (c - c'))
  use 1 + max a (max b b')

  intro x abb1_le_x
  have a_le_ab: a ≤ max a b := le_max_left a b
  have ab_le_abb: max a b ≤ max a (max b b') := max_le_max_left a <| le_max_left b b'
  have abb_le_abb1: max a (max b b') ≤ 1 + max a (max b b') := by simp
  have a_le_abb1: a ≤ 1 + max a (max b b') := a_le_ab.trans ab_le_abb |>.trans abb_le_abb1
  have a_le_x : a ≤ x := a_le_abb1.trans abb1_le_x
  have ab_le_abb1 := ab_le_abb.trans abb_le_abb1
  have b_le_abb1: b ≤ 1 + max a (max b b') := le_trans (by simp) ab_le_abb1

  obtain a_x_fi := (hf_integrable x a_le_x).norm
  obtain a_x_gi := (hg_integrable x a_le_x).norm

  have a_x_union: Set.Ioc a x =
    Set.Ioc a (1 + max a (max b b')) ∪ Set.Ioc (1 + max a (max b b')) x :=
    Set.Ioc_union_Ioc_eq_Ioc a_le_abb1 abb1_le_x |>.symm
  have a_x_disj: Disjoint
    (Set.Ioc a (1 + max a (max b b'))) (Set.Ioc (1 + max a (max b b')) x) :=
    Set.Ioc_disjoint_Ioc_of_le (le_refl _)
  obtain a_abb1_fi := IntegrableOn.mono_set a_x_fi (Set.union_subset_iff.mp (a_x_union.symm.le)).left
  obtain a_abb1_gi := IntegrableOn.mono_set a_x_gi (Set.union_subset_iff.mp (a_x_union.symm.le)).left
  obtain abb1_x_fi := IntegrableOn.mono_set a_x_fi (Set.union_subset_iff.mp (a_x_union.symm.le)).right
  obtain abb1_x_gi := IntegrableOn.mono_set a_x_gi (Set.union_subset_iff.mp (a_x_union.symm.le)).right

  have a_abb1_union: Set.Ioc a (1 + max a (max b b')) =
    Set.Ioc a (max a b) ∪ Set.Ioc (max a b) (1 + max a (max b b')) :=
    Set.Ioc_union_Ioc_eq_Ioc a_le_ab ab_le_abb1 |>.symm
  have a_abb1_disj: Disjoint
    (Set.Ioc a (max a b)) (Set.Ioc (max a b) (1 + max a (max b b'))) :=
    Set.Ioc_disjoint_Ioc_of_le (le_refl _)
  obtain a_ab_fi := IntegrableOn.mono_set a_abb1_fi (Set.union_subset_iff.mp (a_abb1_union.symm.le)).left
  obtain a_ab_gi := IntegrableOn.mono_set a_abb1_gi (Set.union_subset_iff.mp (a_abb1_union.symm.le)).left
  obtain ab_abb1_fi := IntegrableOn.mono_set a_abb1_fi (Set.union_subset_iff.mp (a_abb1_union.symm.le)).right
  obtain ab_abb1_gi := IntegrableOn.mono_set a_abb1_gi (Set.union_subset_iff.mp (a_abb1_union.symm.le)).right

  have ab_abb1_union: Set.Ioc (max a b) (1 + max a (max b b')) =
    Set.Ioc (max a b) (max a (max b b')) ∪ Set.Ioc (max a (max b b')) (1 + max a (max b b')) :=
    Set.Ioc_union_Ioc_eq_Ioc ab_le_abb abb_le_abb1 |> .symm
  have ab_abb1_disj: Disjoint
    (Set.Ioc (max a b) (max a (max b b')) ) (Set.Ioc (max a (max b b')) (1 + max a (max b b'))) :=
    Set.Ioc_disjoint_Ioc_of_le (le_refl _)
  obtain ab_abb_gi := IntegrableOn.mono_set ab_abb1_gi (Set.union_subset_iff.mp (ab_abb1_union.symm.le)).left
  obtain abb_abb1_gi := IntegrableOn.mono_set ab_abb1_gi (Set.union_subset_iff.mp (ab_abb1_union.symm.le)).right

  apply le_trans (norm_integral_le_integral_norm _)
  rw [Real.norm_eq_abs]
  rw [((abs_of_pos hc).symm: c = |c|), ← abs_mul]
  refine le_abs.mpr (Or.inl ?_)
  rw [a_x_union]
  rw [MeasureTheory.setIntegral_union a_x_disj measurableSet_Ioc a_abb1_fi abb1_x_fi]
  rw [MeasureTheory.setIntegral_union a_x_disj measurableSet_Ioc a_abb1_gi abb1_x_gi]
  rw [mul_add]
  apply add_le_add
  · rw [a_abb1_union]
    rw [setIntegral_union a_abb1_disj measurableSet_Ioc a_ab_fi ab_abb1_fi]
    rw [setIntegral_union a_abb1_disj measurableSet_Ioc a_ab_gi ab_abb1_gi]
    trans (∫ (x : ℝ) in Set.Ioc a (max a b), ‖f x‖) +
      c' * ∫ (x : ℝ) in Set.Ioc (max a b) (1 + (max a (max b b'))), ‖g x‖
    · apply add_le_add_left
      rw [← integral_mul_left]
      apply integral_mono_ae ab_abb1_fi (ab_abb1_gi.const_mul _)
      apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      apply Eventually.of_forall
      intro y ⟨hy, _⟩
      exact hb y (le_of_lt (max_lt_iff.mp hy).2)
    · rw [mul_add]
      rw [add_comm (c * _ ) (c * _)]
      apply sub_le_sub_iff.mp
      rw [← sub_mul]
      apply (div_le_iff₀' (sub_pos_of_lt hc'c)).mp
      obtain le0|gt0 := le_or_gt (((∫ (x : ℝ) in Set.Ioc a (max a b), ‖f x‖) -
        c * ∫ (x : ℝ) in Set.Ioc a (max a b), ‖g x‖ ∂volume) / (c - c')) 0
      · apply le_trans le0
        apply integral_nonneg
        intro x
        simp
      · trans ∫ (x' : ℝ) in Set.Ioc (max a (max b b')) (1 + (max a (max b b'))),
          (((∫ (x : ℝ) in Set.Ioc a (max a b), ‖f x‖) - c * ∫ (x : ℝ) in Set.Ioc a (max a b), ‖g x‖ ∂volume) / (c - c'))
        · rw [MeasureTheory.integral_const]
          apply le_mul_of_one_le_left gt0.le
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
          have length: 1 ≤ 1 + (max a (max b b')) - max a (max b b') := by
            rw [add_sub_cancel_right]
          rw [ENNReal.toReal_ofReal (le_trans (by simp) length)]
          exact length
        · rw [ab_abb1_union]
          rw [setIntegral_union ab_abb1_disj measurableSet_Ioc ab_abb_gi abb_abb1_gi]
          apply le_add_of_nonneg_of_le (integral_nonneg (by intro x; simp))
          apply MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const _) abb_abb1_gi
          apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          apply Eventually.of_forall
          intro y ⟨hy, _⟩
          have hby: b' < y := (max_lt_iff.mp (max_lt_iff.mp hy).2).2
          simp only
          rw [Real.norm_eq_abs]
          apply le_trans (le_trans ?_ (hb' y hby.le)) (le_abs_self _)
          apply le_of_eq
          have volume_eq: Set.Ioc a (max a b) = Set.Ioc a b := by
            ext x
            constructor
            · intro ⟨xleft, xright⟩
              obtain xlea | xleb := le_max_iff.mp xright
              · absurd xlea
                simp only [not_le]
                exact xleft
              · exact ⟨xleft, xleb⟩
            · intro ⟨xleft, xright⟩
              exact ⟨xleft, le_max_iff.mpr (Or.inr xright)⟩
          congr
  · rw [← integral_mul_left]
    apply MeasureTheory.integral_mono_ae abb1_x_fi (abb1_x_gi.const_mul _)
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
    apply Eventually.of_forall
    intro y ⟨hy, _⟩
    apply le_trans (hb y <| le_trans b_le_abb1 hy.le)
    apply mul_le_mul_of_nonneg_right hc'c.le (norm_nonneg _)
