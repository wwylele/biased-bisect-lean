import BiasedBisect.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
ρ is the unique solution to the equation ρf = 1
-/
noncomputable
def ρf (s t: ℝ) [PosReal s] [PosReal t] (ρ: ℝ) := Real.exp (-s * ρ) + Real.exp (-t * ρ)

lemma ρf_anti (s t: ℝ) [PosReal s] [PosReal t]: StrictAnti (ρf s t) := by
  apply StrictAnti.add
  all_goals
  · apply StrictMono.comp_strictAnti (Real.exp_strictMono)
    exact strictAnti_mul_left (neg_lt_zero.mpr PosReal.pos)

lemma ρ_exist (s t: ℝ) [PosReal s] [PosReal t]:
∃! ρ ≥ 0, ρf s t ρ = 1 := by
  have tend: Filter.Tendsto (ρf s t) Filter.atTop (nhds 0) := by
    rw [(by simp: (0:ℝ) = 0 + 0)]
    apply Filter.Tendsto.add
    all_goals
    · apply Real.tendsto_exp_comp_nhds_zero.mpr
      apply Filter.Tendsto.neg_mul_atTop (neg_lt_zero.mpr PosReal.pos)
        tendsto_const_nhds
      exact fun ⦃U⦄ a ↦ a
  obtain ⟨ρbound, ρboundspec⟩ := tendsto_atTop_nhds.mp tend (Set.Iio 1) (by simp) isOpen_Iio
  obtain ρboundspec := Set.mem_Iio.mp (ρboundspec ρbound (le_refl _))

  have cont: ContinuousOn (ρf s t) (Set.Icc 0 ρbound) := by unfold ρf; fun_prop
  have ρ0: 0 < ρbound := by
    apply (ρf_anti s t).lt_iff_lt.mp
    apply lt_trans ρboundspec
    unfold ρf
    simp

  obtain ⟨ρs, ρssubset, ρsspec⟩ := Set.subset_image_iff.mp (
    intermediate_value_Icc' (le_of_lt ρ0) cont)

  have onemem: 1 ∈ ρf s t '' ρs := by
    rw [ρsspec]
    simp only [Set.mem_Icc]
    constructor
    · exact le_of_lt ρboundspec
    · unfold ρf
      simp
  obtain ⟨ρ, ρrange, ρspec⟩  := (Set.mem_image _ _ _).mp onemem
  use ρ
  constructor
  · constructor
    · refine Set.mem_of_mem_of_subset ρrange (ρssubset.trans ?_)
      exact (Set.Icc_subset_Ici_iff (le_of_lt ρ0)).mpr (le_refl _)
    · exact ρspec
  · intro q ⟨qrange, qeq⟩
    apply (((ρf_anti s t).strictAntiOn Set.univ).eq_iff_eq (by simp) (by simp)).mp
    rw [qeq]
    unfold ρf
    exact ρspec

noncomputable
def ρ (s t: ℝ) [PosReal s] [PosReal t] := (ρ_exist s t).choose

lemma ρ_satisfies (s t: ℝ) [PosReal s] [PosReal t]:
ρf s t (ρ s t) = 1 := by
  obtain ⟨⟨_, eq⟩, _⟩ := (ρ_exist s t).choose_spec
  exact eq

lemma ρ_range (s t: ℝ) [PosReal s] [PosReal t]: 0 < ρ s t := by
  obtain ⟨⟨range, eq⟩, _⟩ := (ρ_exist s t).choose_spec
  apply lt_of_le_of_ne range
  contrapose! eq
  rw [← eq]
  unfold ρf
  simp

lemma g_exist (s t: ℝ) [PosReal s] [PosReal t]:
∃! g ∈ Set.Icc (0:ℝ) 1, g ^ s = (1 - g) ^ t := by
  let f := (fun (g:ℝ) ↦ g ^ s - (1 - g) ^ t)
  have cont: ContinuousOn f (Set.Icc 0 1) := by
    apply ContinuousOn.sub
    all_goals
    · apply ContinuousOn.rpow_const
      · fun_prop
      · rintro _ _
        right
        exact le_of_lt PosReal.pos
  obtain ⟨gs, gssubset, gsspec⟩ := Set.subset_image_iff.mp (
    intermediate_value_Icc (by simp) cont)
  unfold f at gsspec
  norm_num at gsspec
  rw [Real.zero_rpow (ne_of_gt PosReal.pos)] at gsspec
  rw [Real.zero_rpow (ne_of_gt PosReal.pos)] at gsspec
  norm_num at gsspec
  have haszero: 0 ∈ f '' gs := by
    rw [gsspec]
    simp
  simp only [Set.mem_image] at haszero
  obtain ⟨g, grange, gspec⟩ := haszero
  use g
  obtain grange := gssubset grange
  simp only
  constructor
  · constructor
    · exact grange
    · exact eq_of_sub_eq_zero gspec
  · rintro g' ⟨g'range, g'spec⟩
    have eq: f g' = f g := by
      rw [gspec]
      unfold f
      exact sub_eq_zero_of_eq g'spec
    have mono: StrictMonoOn f (Set.Icc 0 1) := by
      have rpow_mono (p: ℝ) [PosReal p]: StrictMonoOn (fun (x:ℝ) ↦ x ^ p) (Set.Icc 0 1) := by
        intro x ⟨xleft, xright⟩ y ⟨yleft, yright⟩ xlty
        exact Real.strictMonoOn_rpow_Ici_of_exponent_pos PosReal.pos xleft yleft xlty
      unfold f
      apply StrictMonoOn.add
      · apply rpow_mono
      · apply StrictAntiOn.neg
        have onesub: StrictAntiOn (fun (x:ℝ) ↦ 1 - x) (Set.Icc 0 1) := by
          intro x _ y _ lt
          simpa using lt
        apply StrictMonoOn.comp_strictAntiOn (rpow_mono t) onesub
        unfold Set.MapsTo
        rintro x ⟨xleft, xright⟩
        simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right]
        exact ⟨xright, xleft⟩
    exact (StrictMonoOn.eq_iff_eq mono g'range grange).mp eq

noncomputable
def g (s t: ℝ) [PosReal s] [PosReal t] := (g_exist s t).choose

lemma g_satisfies (s t: ℝ) [PosReal s] [PosReal t]: (g s t) ^ s = (1 - (g s t)) ^ t := by
  obtain ⟨⟨range, satisfies⟩, unique⟩ := (g_exist s t).choose_spec
  exact satisfies

lemma g_range (s t: ℝ) [PosReal s] [PosReal t]: (g s t) ∈ Set.Ioo 0 1 := by
  obtain ⟨⟨⟨left, right⟩, satisfies⟩, unique⟩ := (g_exist s t).choose_spec
  constructor
  · apply lt_of_le_of_ne left
    contrapose! satisfies
    rw [← satisfies]
    simp only [sub_zero, Real.one_rpow]
    rw [Real.zero_rpow (ne_of_gt PosReal.pos)]
    norm_num
  · apply lt_of_le_of_ne right
    contrapose! satisfies
    rw [satisfies]
    simp only [Real.one_rpow, sub_self]
    rw [Real.zero_rpow (ne_of_gt PosReal.pos)]
    norm_num

lemma g_unique (s t: ℝ) [PosReal s] [PosReal t]
(g': ℝ) (grange: g' ∈ Set.Icc 0 1) (satisfies: g' ^ s = (1 - g') ^ t):
g' = g s t := by
  obtain ⟨_, unique⟩ := (g_exist s t).choose_spec
  exact unique g' ⟨grange, satisfies⟩

/-
g is homogeneous
-/
lemma g_homo (s t l: ℝ) [PosReal s] [PosReal t] [PosReal l]: g s t = g (l * s) (l * t) := by
  obtain range := g_range s t
  obtain satisfies := g_satisfies s t
  apply g_unique (l * s) (l * t)
  · exact Set.mem_Icc_of_Ioo range
  · obtain ⟨left, right⟩ := range
    rw [mul_comm l s, mul_comm l t]
    rw [Real.rpow_mul (le_of_lt left), Real.rpow_mul (sub_nonneg_of_le (le_of_lt right))]
    rw [satisfies]

def IsOptimalCostℝ (Efun: ℝ → ℝ) (s t: ℝ): Prop :=
  ∀ n > 0, IsLeast ((StratEval Efun s t n) '' (Set.Ioo 0 n)) (Efun n)

def IsOptimalStratℝ (Efun: ℝ → ℝ) (wfun: ℝ → Set ℝ) (s t: ℝ): Prop :=
  ∀ n > 0, ∀ w ∈ (Set.Ioo 0 n), StratEval Efun s t n w = Efun n ↔ w ∈ wfun n

noncomputable
def Eℝ (s t: ℝ) [PosReal s] [PosReal t]: ℝ → ℝ := fun n ↦ n * Real.log n / ρ s t

noncomputable
def wℝ (s t: ℝ) [PosReal s] [PosReal t]: ℝ → ℝ := (g s t * ·)

lemma wℝ_range (s t: ℝ) [PosReal s] [PosReal t] (n: ℝ) (npos: 0 < n):
wℝ s t n ∈ Set.Ioo 0 n := by
  unfold wℝ
  constructor
  · exact mul_pos (g_range s t).1 npos
  · exact mul_lt_of_lt_one_left npos (g_range s t).2


noncomputable
def Dℝ (s t: ℝ) [PosReal s] [PosReal t] (n w: ℝ) := Eℝ s t w + Eℝ s t (n - w) + t * w + s * (n - w)

noncomputable
def D'ℝ (s t: ℝ) [PosReal s] [PosReal t] (n w: ℝ) := (Real.log w - Real.log (n - w)) / ρ s t + t - s

lemma Dℝ_derive (s t: ℝ) [PosReal s] [PosReal t] (n w: ℝ) (wleft: 0 < w) (wright: w < n):
HasDerivAt (Dℝ s t n) (D'ℝ s t n w) w := by
  have nw0: n - w > 0 := by exact sub_pos.mpr wright
  unfold Dℝ Eℝ D'ℝ
  rw [(by ring: (Real.log w - Real.log (n - w)) / ρ s t + t - s =
    (Real.log w - Real.log (n - w)) / ρ s t + t * 1 + s * (-1))]
  apply HasDerivAt.add
  · apply HasDerivAt.add
    · simp_rw [← add_div]
      apply HasDerivAt.div_const
      rw [(by field_simp; ring: Real.log w - Real.log (n - w) =
        1 * Real.log w + w * w⁻¹ + (-1 * Real.log (n - w) + (n - w) * ((n - w)⁻¹ * (-1) )))]
      apply HasDerivAt.add
      · apply HasDerivAt.mul (hasDerivAt_id' w)
        exact (Real.hasStrictDerivAt_log_of_pos wleft).hasDerivAt
      · apply HasDerivAt.mul (HasDerivAt.const_sub _ (hasDerivAt_id' w))
        apply (Real.hasStrictDerivAt_log_of_pos nw0).hasDerivAt.comp
        exact (HasDerivAt.const_sub _ (hasDerivAt_id' w))
    · exact HasDerivAt.const_mul _ (hasDerivAt_id' w)
  · exact HasDerivAt.const_mul _ (HasDerivAt.const_sub _ (hasDerivAt_id' w))

lemma D'ℝ_mono (s t: ℝ) [PosReal s] [PosReal t] (n: ℝ):
StrictMonoOn (D'ℝ s t n) (Set.Ioo 0 n) := by
  unfold D'ℝ
  apply StrictMonoOn.add_const
  apply StrictMonoOn.add_const
  simp_rw [sub_div]
  apply StrictMonoOn.add
  · intro a amem b bmem altb
    refine div_lt_div_of_pos_right ?_ (ρ_range s t)
    exact Real.log_lt_log amem.1 altb
  · intro a amem b bmem altb
    apply neg_lt_neg
    refine div_lt_div_of_pos_right ?_ (ρ_range s t)
    apply Real.log_lt_log (sub_pos_of_lt bmem.2)
    linarith

lemma D'ℝ_continuous (s t: ℝ) [PosReal s] [PosReal t] (n: ℝ):
ContinuousOn (D'ℝ s t n) (Set.Ioo 0 n) := by
  unfold D'ℝ
  apply ContinuousOn.sub
  · apply ContinuousOn.add
    · refine ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) _
      · exact Real.continuousOn_log.mono (by aesop)
      · refine (Real.continuousOn_log.comp (s := {n}ᶜ) (by fun_prop) ?_).mono (by aesop)
        intro x xmem
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at xmem ⊢
        exact sub_ne_zero_of_ne fun a ↦ xmem (id (Eq.symm a))
    · fun_prop
  · fun_prop

lemma g_ρ_agree (s t: ℝ) [PosReal s] [PosReal t]: g s t = Real.exp (-t * ρ s t) := by
  symm
  apply g_unique s t
  · constructor
    · exact Real.exp_nonneg _
    · apply Real.exp_le_one_iff.mpr
      apply mul_nonpos_of_nonpos_of_nonneg (Left.neg_nonpos_iff.mpr <| le_of_lt PosReal.pos)
      apply le_of_lt <| ρ_range s t
  · rw [← eq_sub_of_add_eq (ρ_satisfies s t)]
    rw [← Real.exp_mul, ← Real.exp_mul]
    apply Real.exp_eq_exp.mpr
    ring

lemma D'ℝ_zero (s t: ℝ) [PosReal s] [PosReal t] (n: ℝ) (npos: 0 < n):
D'ℝ s t n (wℝ s t n) = 0 := by
  unfold D'ℝ
  apply sub_eq_zero_of_eq
  apply add_eq_of_eq_sub
  apply div_eq_of_eq_mul (ρ_range s t).ne.symm
  rw [sub_mul]
  apply sub_eq_sub_iff_add_eq_add.mpr
  apply_fun Real.exp using Real.exp_injective
  rw [Real.exp_add, Real.exp_add, Real.exp_log (wℝ_range s t n npos).1,
    Real.exp_log (by simpa using (wℝ_range s t n npos).2)]
  unfold wℝ
  rw [← one_sub_mul, ← mul_assoc, mul_right_comm]
  refine mul_eq_mul_right_iff.mpr (Or.inl ?_)
  apply mul_eq_mul_of_div_eq_div _ _ (ne_of_gt (sub_pos_of_lt (g_range s t).2)) (ne_of_gt (Real.exp_pos _))
  nth_rw 2 [← inv_div_inv]
  rw [← Real.exp_neg, ← Real.exp_neg, ← neg_mul, ← neg_mul]
  rw [eq_sub_of_add_eq (ρ_satisfies s t)]
  rw [g_ρ_agree s t]

lemma Dℝ_left (s t: ℝ) [PosReal s] [PosReal t] (n w: ℝ) (wleft: 0 < w) (wright: w < wℝ s t n):
Dℝ s t n (wℝ s t n) < Dℝ s t n w := by
  have npos: 0 < n := by
    obtain wlr := lt_trans wleft wright
    unfold wℝ at wlr
    have gpos: 0 < g s t := (g_range s t).left
    aesop
  have integrable: IntervalIntegrable (D'ℝ s t n) MeasureTheory.volume w (wℝ s t n) := by
    refine ((D'ℝ_continuous s t n).mono ?_).intervalIntegrable
    apply Set.Icc_subset_Ioo
    · simp only [lt_inf_iff]
      exact ⟨wleft, (wℝ_range s t n npos).left⟩
    · simp only [sup_lt_iff]
      refine ⟨lt_trans wright (wℝ_range s t n npos).2, (wℝ_range s t n npos).2⟩

  apply lt_of_sub_neg
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x xmem ↦ Dℝ_derive s t n x
    (by
      obtain le_w := xmem.1
      rw [min_eq_left <| le_of_lt wright] at le_w
      exact lt_of_lt_of_le wleft le_w
    )
    (by
      obtain le_w := xmem.2
      rw [max_eq_right <| le_of_lt wright] at le_w
      exact lt_of_le_of_lt le_w (wℝ_range s t n npos).2
    ))
    integrable]
  apply neg_of_neg_pos
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on integrable.neg ?_ wright
  intro x ⟨xleft, xright⟩
  simp only [Left.neg_pos_iff, gt_iff_lt]
  rw [← D'ℝ_zero s t n npos]
  refine (D'ℝ_mono s t n) ?_ (wℝ_range s t n npos) xright
  constructor
  · exact lt_trans wleft xleft
  · exact lt_trans xright (wℝ_range s t n npos).2

lemma Dℝ_right (s t: ℝ) [PosReal s] [PosReal t] (n w: ℝ) (wleft: wℝ s t n < w) (wright: w < n):
Dℝ s t n (wℝ s t n) < Dℝ s t n w := by
  have npos: 0 < n := by
    obtain wlr := lt_trans wleft wright
    unfold wℝ at wlr
    have gpos: g s t < 1 := (g_range s t).2
    nlinarith
  have integrable: IntervalIntegrable (D'ℝ s t n) MeasureTheory.volume (wℝ s t n) w := by
    refine ((D'ℝ_continuous s t n).mono ?_).intervalIntegrable
    apply Set.Icc_subset_Ioo
    · simp only [lt_inf_iff]
      exact ⟨(wℝ_range s t n npos).1, lt_trans (wℝ_range s t n npos).1 wleft⟩
    · simp only [sup_lt_iff]
      refine ⟨(wℝ_range s t n npos).2, wright⟩
  apply lt_of_sub_pos
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x xmem ↦ Dℝ_derive s t n x
    (by
      obtain le_w := xmem.1
      rw [min_eq_left <| le_of_lt wleft] at le_w
      exact lt_of_lt_of_le (wℝ_range s t n npos).1 le_w
    )
    (by
      obtain le_w := xmem.2
      rw [max_eq_right <| le_of_lt wleft] at le_w
      exact lt_of_le_of_lt le_w wright
    ))
    integrable]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on integrable ?_ wleft
  intro x ⟨xleft, xright⟩
  rw [← D'ℝ_zero s t n npos]
  refine (D'ℝ_mono s t n) (wℝ_range s t n npos) ?_ xleft
  constructor
  · exact lt_trans (wℝ_range s t n npos).1 xleft
  · exact lt_trans xright wright

lemma Dℝ_min (s t: ℝ) [PosReal s] [PosReal t] (n: ℝ) (npos: 0 < n):
Dℝ s t n (wℝ s t n) = Eℝ s t n := by
  obtain zero := D'ℝ_zero s t n npos
  unfold D'ℝ at zero
  have zero': Real.log (n - wℝ s t n) / ρ s t + s = Real.log (wℝ s t n) / ρ s t + t := by
    symm
    apply eq_of_sub_eq_zero
    rw [← zero]
    ring
  have: Dℝ s t n (wℝ s t n) =
    wℝ s t n * (Real.log (wℝ s t n) / ρ s t + t) +
    (n - wℝ s t n) * (Real.log (n - wℝ s t n) / ρ s t + s) := by
    unfold Dℝ Eℝ
    ring
  rw [this, zero', ← add_mul, add_sub_cancel]
  unfold Eℝ
  rw [mul_div_assoc]
  refine mul_eq_mul_left_iff.mpr (Or.inl ?_)
  apply add_eq_of_eq_sub'
  rw [← neg_sub]
  rw [← sub_div, ← Real.log_div (wℝ_range s t n npos).1.ne.symm npos.ne.symm]
  unfold wℝ
  rw [mul_div_cancel_right₀ _ npos.ne.symm, g_ρ_agree, Real.log_exp,
    mul_div_cancel_right₀ _ (ρ_range s t).ne.symm]
  simp

theorem Eℝ_IsOptimalCostℝ (s t: ℝ) [PosReal s] [PosReal t]: IsOptimalCostℝ (Eℝ s t) s t := by
  intro n npos
  unfold StratEval
  rw [← Dℝ_min s t n npos]
  constructor
  · simp only [Set.mem_image]
    use wℝ s t n
    constructor
    · exact wℝ_range s t n npos
    · unfold Dℝ
      simp only
  · intro E ⟨w, ⟨wmem, Eeq⟩⟩
    rw [← Eeq]
    obtain lt|eq|gt := lt_trichotomy w (wℝ s t n)
    · exact le_of_lt <| Dℝ_left s t n w wmem.1 lt
    · rw [eq]
      unfold Dℝ
      simp
    · exact le_of_lt <| Dℝ_right s t n w gt wmem.2

theorem Wℝ_IsOptimalStratℝ (s t: ℝ) [PosReal s] [PosReal t]:
IsOptimalStratℝ (Eℝ s t) (fun n ↦ {wℝ s t n}) s t := by
  intro n npos w wmem
  simp only [Set.mem_singleton_iff]
  constructor
  · intro eeq
    contrapose! eeq with wne
    rw [← Dℝ_min s t n npos]
    apply ne_of_gt
    obtain lt|gt := lt_or_gt_of_ne wne
    · exact Dℝ_left s t n w wmem.1 lt
    · exact Dℝ_right s t n w gt wmem.2
  · intro weq
    rw [weq]
    exact Dℝ_min s t n npos
