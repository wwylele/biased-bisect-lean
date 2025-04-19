import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

open Asymptotics Filter MeasureTheory

theorem integral_norm_equivalent {f : ℝ → ℝ}
    (hf_tendsto : Tendsto f atTop atTop)
    {a : ℝ}
    (hf_integrable : ∀ x ≥ a, IntegrableOn f (Set.Ioc a x)):
    (∫ t in Set.Ioc a ·, f t) ~[atTop] (∫ t in Set.Ioc a ·, ‖f t‖) := by

  obtain ⟨b, hb⟩ := Filter.tendsto_atTop_atTop.mp hf_tendsto 1
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr ?_
  · apply Filter.eventually_atTop.mpr
    use 1 + max a b
    intro x hx
    apply ne_of_gt
    have a_lt_x: a < x := (lt_of_lt_of_le (by apply lt_of_le_of_lt (b := max a b); all_goals simp) hx)
    obtain integ := (hf_integrable x a_lt_x.le).norm
    apply (MeasureTheory.integral_pos_iff_support_of_nonneg (by intro x; simp) integ).mpr
    simp only [Real.norm_eq_abs, measurableSet_Ioc, Measure.restrict_apply']
    apply lt_of_lt_of_le (b := volume (Set.Ioc (max a b) x))
    · simp only [Real.volume_Ioc, ENNReal.ofReal_pos, sub_pos]
      exact lt_of_lt_of_le (by simp) hx
    · apply volume.mono
      intro y ⟨yleft, yright⟩
      simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, abs_eq_zero, Set.mem_Ioc]
      constructor
      · obtain hb' := hb y ((max_lt_iff.mp yleft).right).le
        exact ne_of_gt <| lt_of_lt_of_le (by simp) hb'
      · exact ⟨(max_lt_iff.mp yleft).left, yright⟩
  · rw [(by ring: (1:ℝ) = (0 + 1) / (0 + 1))]

    have fun_rw (x: ℝ) (ab_lt_x: max a b < x):
      ((∫ (t : ℝ) in Set.Ioc a x, f t) / ∫ (t : ℝ) in Set.Ioc a x, ‖f t‖) =
      ( (((∫ (t : ℝ) in Set.Ioc a (max a b), f t) / ∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖) + 1) /
        (((∫ (t : ℝ) in Set.Ioc a (max a b), ‖f t‖) / ∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖) + 1) ) := by

      have a_x_union: Set.Ioc a (a ⊔ b) ∪ Set.Ioc (a ⊔ b) x = Set.Ioc a x :=
        Set.Ioc_union_Ioc_eq_Ioc (by simp) ab_lt_x.le
      have a_x_disj: Disjoint (Set.Ioc a (a ⊔ b)) (Set.Ioc (a ⊔ b) x) :=
        Set.Ioc_disjoint_Ioc_of_le (le_refl _)
      obtain a_x_i := hf_integrable x (max_lt_iff.mp ab_lt_x).1.le
      obtain a_x_ni := a_x_i.norm
      obtain a_ab_i := IntegrableOn.mono_set a_x_i (Set.union_subset_iff.mp (a_x_union.le)).left
      obtain ab_x_i := IntegrableOn.mono_set a_x_i (Set.union_subset_iff.mp (a_x_union.le)).right
      obtain a_ab_ni := IntegrableOn.mono_set a_x_ni (Set.union_subset_iff.mp (a_x_union.le)).left
      obtain ab_x_ni := IntegrableOn.mono_set a_x_ni (Set.union_subset_iff.mp (a_x_union.le)).right

      have deno0: 0 < ∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖ := by
        apply (MeasureTheory.integral_pos_iff_support_of_nonneg (by intro x; simp) ab_x_ni).mpr
        simp only [Real.norm_eq_abs, measurableSet_Ioc, Measure.restrict_apply']
        rw [Set.inter_eq_right.mpr ?_]
        · simp [ab_lt_x]
        · intro y ⟨hy, _⟩
          obtain hb' := hb y (max_lt_iff.mp hy).2.le
          simp only [Function.mem_support, ne_eq, abs_eq_zero]
          exact ne_of_gt (lt_of_lt_of_le (by simp) hb')
      rw [div_add_one deno0.ne.symm, div_add_one deno0.ne.symm]
      rw [div_div_div_cancel_right₀ deno0.ne.symm]
      have: (∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖) = ∫ (t : ℝ) in Set.Ioc (max a b) x, f t := by
        apply integral_congr_ae
        apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        apply Eventually.of_forall
        intro y ⟨hy, _⟩
        simp only [Real.norm_eq_abs, abs_eq_self, ge_iff_le]
        obtain hb' := hb y (max_lt_iff.mp hy).2.le
        exact (lt_of_lt_of_le (by simp) hb').le
      nth_rw 1 [this]
      rw [← setIntegral_union a_x_disj measurableSet_Ioc a_ab_i ab_x_i]
      rw [← setIntegral_union a_x_disj measurableSet_Ioc a_ab_ni ab_x_ni]
      rw [a_x_union]
    have fun_rw': (fun x ↦ (∫ (t : ℝ) in Set.Ioc a x, f t) / ∫ (t : ℝ) in Set.Ioc a x, ‖f t‖)
      =ᶠ[atTop] (fun x ↦ (((∫ (t : ℝ) in Set.Ioc a (max a b), f t) / ∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖) + 1) /
        (((∫ (t : ℝ) in Set.Ioc a (max a b), ‖f t‖) / ∫ (t : ℝ) in Set.Ioc (max a b) x, ‖f t‖) + 1) ) := by
      apply Filter.eventually_atTop.mpr
      use (max a b + 1)
      intro x hx
      exact fun_rw x (lt_of_lt_of_le (by simp) hx)

    apply Filter.Tendsto.congr' fun_rw'.symm
    refine Filter.Tendsto.div ?_ ?_ (by simp)
    all_goals
    · refine Filter.Tendsto.add_const _ (Tendsto.const_div_atTop ?_ _)
      apply Filter.tendsto_atTop_atTop.mpr
      intro v
      use max 0 v + max a b
      intro y hy
      trans ∫ (t : ℝ) in Set.Ioc (a ⊔ b) y, 1
      · have yab: 0 ≤ y - max a b := by
          apply sub_nonneg_of_le
          refine le_trans ?_ hy
          simp
        simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
          Real.volume_Ioc, yab, ENNReal.toReal_ofReal, smul_eq_mul, mul_one, ge_iff_le]
        apply le_sub_right_of_add_le
        refine le_trans ?_ hy
        simp
      · have integ: IntegrableOn (fun a ↦ ‖f a‖) (Set.Ioc (a ⊔ b) y) := by
          apply (IntegrableOn.mono_set (hf_integrable y (
            by apply le_trans (by trans max a b; all_goals simp) hy)) ?_).norm
          apply Set.Ioc_subset_Ioc (by simp) (by simp)
        apply integral_mono_ae (by simp) integ
        apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        apply Eventually.of_forall
        intro z ⟨zleft, zright⟩
        simp only [Real.norm_eq_abs]
        obtain hb' := hb z (max_lt_iff.mp zleft).right.le
        exact le_abs.mpr (Or.inl hb')

theorem Asymptotics.IsLittleO.integral {f g : ℝ → ℝ}
    (hfg : f =o[atTop] g)
    (hg_tendsto : Tendsto g atTop atTop)
    {a : ℝ}
    (hf_integrable : ∀ x ≥ a, IntegrableOn f (Set.Ioc a x))
    (hg_integrable : ∀ x ≥ a, IntegrableOn g (Set.Ioc a x)):
    (∫ t in Set.Ioc a ·, f t) =o[atTop] (∫ t in Set.Ioc a ·, g t) := by
  refine Asymptotics.IsLittleO.trans_isBigO ?_ (integral_norm_equivalent hg_tendsto hg_integrable).isBigO_symm

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

theorem Asymptotics.IsEquivalent.integral {f g : ℝ → ℝ}
    (hfg : f ~[atTop] g)
    (hg_tendsto : Tendsto g atTop atTop)
    {a : ℝ}
    (hf_integrable : ∀ x ≥ a, IntegrableOn f (Set.Ioc a x))
    (hg_integrable : ∀ x ≥ a, IntegrableOn g (Set.Ioc a x)):
    (∫ t in Set.Ioc a ·, f t) ~[atTop] (∫ t in Set.Ioc a ·, g t) := by

  unfold Asymptotics.IsEquivalent
  have: (fun x ↦ ∫ (t : ℝ) in Set.Ioc a x, f t) - (fun x ↦ ∫ (t : ℝ) in Set.Ioc a x, g t)
    = fun x ↦ ∫ (t : ℝ) in Set.Ioc a x, f t - g t := by
    ext x
    simp only [Pi.sub_apply]
    have hf_integrable': IntegrableOn f (Set.Ioc a x) := by
      obtain lt|ge := lt_or_ge x a
      · rw [Set.Ioc_eq_empty (by simpa using lt.le)]
        simp
      · exact hf_integrable x ge
    have hg_integrable': IntegrableOn g (Set.Ioc a x) := by
      obtain lt|ge := lt_or_ge x a
      · rw [Set.Ioc_eq_empty (by simpa using lt.le)]
        simp
      · exact hg_integrable x ge
    rw [← integral_sub hf_integrable' hg_integrable']
  rw [this]
  have hfg_integrable: ∀ x ≥ a, IntegrableOn (f - g) (Set.Ioc a x) := by
    intro x hx
    exact (hf_integrable x hx).sub (hg_integrable x hx)
  exact Asymptotics.IsLittleO.integral hfg hg_tendsto hfg_integrable hg_integrable
