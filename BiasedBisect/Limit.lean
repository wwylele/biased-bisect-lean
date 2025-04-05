import BiasedBisect.CrossSection
import BiasedBisect.Integer
import BiasedBisect.MathlibTopologyOrderIsLUB

/-
In this file, we generalize asymtotic theorems for integer s and t to real numbers
-/

/-
The limit of (w / n) is called g. We first gives a formula of g in terms of a solution
to the equation g ^ s = (1 - g) ^ t. We will need to show there is such a unique solution
-/
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
g agrees with ξ₀ that we defined in Integer.lean
-/
lemma g_eq (s t: ℕ+): (ξ₀ s t ^ (t: ℕ)) = g s t := by
  apply g_unique s t
  · obtain left := ξ₀min s t
    obtain right := ξ₀max s t
    constructor
    · exact le_of_lt (pow_pos left t)
    · exact pow_le_one₀ (le_of_lt left) (le_of_lt right)
  · obtain val := ξ₀eval s t
    unfold ξPolynomialℝ at val
    simp only [map_one, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, one_mul,
      Polynomial.eval_one] at val
    obtain val' := eq_sub_of_add_eq (eq_of_sub_eq_zero val)
    rw [← val']
    simp only [Real.rpow_natCast]
    rw [← pow_mul, ← pow_mul, mul_comm]

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

/-
A corollary of w_Asymtotic_int: the limit holds for rational s / t
-/
lemma w_Asymtotic_rat (s t: ℝ) [PosReal s] [PosReal t] (rational: s / t ∈ Set.range Rat.cast):
Filter.Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) Filter.atTop (nhds (g s t)) := by
  obtain ⟨ST, STeq⟩ := Set.mem_range.mpr rational
  let T := Rat.pnatDen ST
  let S' := Rat.num ST
  have eq1: (S' / T: ℚ) = s / t := by
    unfold S' T
    rw [Rat.coe_pnatDen, Rat.num_div_den, STeq]
  push_cast at eq1
  have eq2: S' = s / t * T := by
    exact mul_invOf_eq_iff_eq_mul_right.mp eq1
  have S'pos: 0 < (S': ℝ) := by
    rw [eq2]
    exact mul_pos (div_pos PosReal.pos PosReal.pos) (by norm_cast; exact PNat.pos T)
  norm_cast at S'pos
  let S: PNat := ⟨Int.toNat S', by
    simp only [Int.lt_toNat, CharP.cast_eq_zero]
    exact S'pos
  ⟩
  have S'eq : S' = S := by
    unfold S
    simp only [PNat.mk_coe, Int.ofNat_toNat, left_eq_sup]
    exact le_of_lt S'pos
  rw [S'eq] at eq1
  push_cast at eq1
  let l := s / S
  have seq: s = l * S := by
    unfold l
    simp
  have teq: t = l * T := by
    unfold l
    rw [div_mul, eq1, ← div_mul]
    rw [div_self (ne_of_gt PosReal.pos)]
    simp only [one_mul]

  simp_rw [seq, teq]
  conv in (fun n ↦ _) =>
    ext n
    rw [← wₗᵢ_homo S T n l]
  rw [← g_homo, ← g_eq]
  apply w_Asymtotic_int

/-
To generalize the limit to all real s and t, we will utilize the following facts:
 - g is antitone and continuous
 - w is monotone w.r.t s and t
-/

/-
To help with the proof, we define the inverse function of g w.r.t t, fixing s = 1
-/
noncomputable
def ginv (g) := Real.log g / Real.log (1 - g)

/-
ginv is antitone
-/
lemma ginv_anti: StrictAntiOn ginv (Set.Ioo 0 1) := by
  unfold ginv
  intro g1 g1mem g2 g2mem lt
  simp only
  nth_rw 1 [← neg_div_neg_eq]
  nth_rw 2 [← neg_div_neg_eq]
  apply div_lt_div₀
  · simp only [neg_lt_neg_iff]
    exact Real.log_lt_log g1mem.1 lt
  · simp only [neg_le_neg_iff]
    apply le_of_lt
    apply Real.log_lt_log
    · simp only [sub_pos]
      apply g2mem.2
    · simp only [sub_lt_sub_iff_left]
      exact lt
  · simp only [Left.nonneg_neg_iff]
    exact le_of_lt (Real.log_neg g1mem.1 g1mem.2)
  · simp only [Left.neg_pos_iff]
    apply Real.log_neg
    · simp only [sub_pos]
      exact g1mem.2
    · simp only [sub_lt_self_iff]
      exact g1mem.1

/-
And as expected, ginv inverts g
-/
lemma ginv_comp (r: ℝ) [PosReal r]: ginv (g 1 r) = r := by
  unfold ginv
  apply div_eq_of_eq_mul
  · simp only [ne_eq, Real.log_eq_zero, sub_eq_self, not_or]
    constructor
    · exact ne_of_gt (sub_pos.mpr (g_range _ _).2)
    · constructor
      · exact ne_of_gt (g_range _ _).1
      · apply ne_of_gt
        apply lt_sub_left_of_add_lt
        apply add_lt_of_lt_sub_right
        norm_num
        apply lt_trans (g_range _ _).2 (by norm_num)
  · symm
    apply (Real.mul_log_eq_log_iff (sub_pos_of_lt (g_range _ _).2) (g_range _ _).1).mpr
    rw [← g_satisfies 1 r]
    simp

/-
We generalize w's asymtotic behavior to all positive s and t
-/
theorem w_Asymtotic (s t: ℝ) [PosReal s] [PosReal t]:
Filter.Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) Filter.atTop (nhds (g s t)) := by
  -- We first normalize to s = 1 and only consider varying t, which is now renamed to r
  let r := t / s
  have s_cancel: 1 / s * s = 1 := one_div_mul_cancel (ne_of_gt PosReal.pos)
  have t_cancel: 1 / s * t = r := one_div_mul_eq_div s t
  have funrw (n): wₗᵢ s t n = wₗᵢ 1 r n := by
    rw [wₗᵢ_homo s t n (1 / s)]
    congr 1
  have limrw: g s t = g 1 r := by
    rw [g_homo s t (1 / s)]
    congr 1
  conv in fun n ↦ _ =>
    ext n
    rw [funrw n]
  rw [limrw]

  -- We can find two rational sequences approaching r, from below and above
  obtain ⟨below, belowMono, belowLt, belowLim⟩ := Rat.exists_seq_strictMono_tendsto_real r
  obtain ⟨above, aboveMono, aboveLt, aboveLim⟩ := Rat.exists_seq_strictAnti_tendsto_real r

  -- We will use the two rational sequences to squeeze the limit.
  -- However, these are double limit (r' -> r and N -> ∞), so we can't use squeeze theorem directly
  -- We will do a manual ε-δ style proof here

  apply tendsto_atTop_nhds.mpr
  intro U gmem Uopen
  obtain ⟨low, high, ⟨glow, ghigh⟩, substU⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Uopen.mem_nhds gmem)
  -- We unfold the limit definition to an appropriate ε to use
  -- Note we divided the allowed deviation by two. We'd like to have two parts of ε
  -- which we will distribute to both of the double limit
  let ε := (min (g 1 r - low) (high - g 1 r)) / 2
  have εpos: 0 < ε := by
    unfold ε
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff, sub_pos]
    exact ⟨glow, ghigh⟩
  have εsubst: Set.Ioo (g 1 r - ε * 2) (g 1 r + ε * 2) ⊆ U := by
    refine subset_trans ?_ substU
    unfold ε
    rw [div_mul_cancel₀ _ (by simp)]
    apply Set.Ioo_subset_Ioo
    · apply le_sub_comm.mpr
      simp only [inf_le_left]
    · apply add_le_of_le_sub_left
      simp

  -- An adhoc theorem that g is continuous
  have g_continuous: ∃dr > 0, ∀ r', (h: r' ∈ Set.Ioo (max (r - dr) 0) (r + dr)) →
    have: PosReal r' := { pos := (max_lt_iff.mp h.1).2 }
    g 1 r' ∈ Set.Ioo (g 1 r - ε) (g 1 r + ε) := by

    have leftSet: g 1 r < min (g 1 r + ε) 1 := by
      simp only [lt_inf_iff, lt_add_iff_pos_right]
      exact ⟨εpos, (g_range _ _).2⟩
    have ⟨gleft, ⟨gleftRange, gleftValid⟩⟩ := Set.nonempty_Ioo.mpr leftSet
    obtain ⟨gleftε, gleftValid⟩ := lt_min_iff.mp gleftValid

    have rightSet: max (g 1 r - ε) 0 < g 1 r := by
      simp only [sup_lt_iff, sub_lt_self_iff]
      exact ⟨εpos, (g_range _ _).1⟩
    have ⟨gright, ⟨grightValid, grightRange⟩⟩ := Set.nonempty_Ioo.mpr rightSet
    obtain ⟨grightε, grightValid⟩ := max_lt_iff.mp grightValid

    have leftmem: gleft ∈ Set.Ioo 0 1 := ⟨lt_trans (g_range _ _).1 gleftRange, gleftValid⟩
    have rightmem: gright ∈ Set.Ioo 0 1 := ⟨grightValid, lt_trans grightRange (g_range _ _).2⟩

    let rleft := ginv gleft
    let rright := ginv gright
    use min (r - rleft) (rright - r)
    constructor
    · simp only [gt_iff_lt, lt_inf_iff, sub_pos]
      rw [← ginv_comp r]
      constructor
      · exact ginv_anti (g_range _ _) leftmem gleftRange
      · exact ginv_anti rightmem (g_range _ _) grightRange
    · intro r' r'range
      simp only [sub_inf, sub_sub_cancel, add_inf, add_sub_cancel, Set.mem_Ioo, sup_lt_iff,
        lt_inf_iff] at r'range
      obtain ⟨⟨⟨r'left, _⟩, r'pos⟩, ⟨_, r'right⟩⟩ := r'range
      have: PosReal r' := { pos := r'pos }

      suffices g 1 r' ∈ Set.Ioo gright gleft by
        refine Set.mem_of_mem_of_subset this (Set.Ioo_subset_Ioo ?_ ?_)
        · exact le_of_lt grightε
        · exact le_of_lt gleftε
      simp only [Set.mem_Ioo]
      constructor
      · apply (ginv_anti.lt_iff_lt (g_range _ _) rightmem).mp
        rw [ginv_comp]
        exact r'right
      · apply (ginv_anti.lt_iff_lt leftmem (g_range _ _)).mp
        rw [ginv_comp]
        exact r'left
  obtain ⟨dr, drpos, drspec⟩ := g_continuous

  have rmem: r ∈ Set.Ioo (max (r - dr) 0) (r + dr) := by
    constructor
    · simp only [sup_lt_iff, sub_lt_self_iff]
      constructor
      · exact drpos
      · exact PosReal.pos
    · exact lt_add_of_pos_right r drpos

  -- We use one of ε to find close enough r' on the rational sequences
  -- where g 1 r' is close enough to g 1 r on the continous g
  obtain ⟨belowLimN, belowSpec⟩ := tendsto_atTop_nhds.mp belowLim (Set.Ioo (max (r - dr) 0) (r + dr))
    rmem isOpen_Ioo
  obtain belowSpecN := belowSpec belowLimN le_rfl
  obtain belowDr := drspec (below belowLimN) belowSpecN
  simp only at belowDr

  obtain ⟨aboveLimN, aboveSpec⟩ := tendsto_atTop_nhds.mp aboveLim (Set.Ioo (max (r - dr) 0) (r + dr))
    rmem isOpen_Ioo
  obtain aboveSpecN := aboveSpec aboveLimN le_rfl
  obtain aboveDr := drspec (above aboveLimN) aboveSpecN
  simp only at aboveDr

  -- Then we use the other ε to find a large enough n such that for the rational r'
  -- w 1 r' / n is close enough to g 1 r'
  have: PosReal (below belowLimN) := {
    pos := (max_lt_iff.mp belowSpecN.1).2
  }
  have belowRat: (1 / (below belowLimN) :ℝ) ∈ Set.range Rat.cast := by
    use 1 / (below belowLimN)
    simp
  obtain ⟨belowWN, belowW⟩ := tendsto_atTop_nhds.mp (w_Asymtotic_rat 1 (below belowLimN) belowRat)
    (Set.Ioo (g 1 (below belowLimN) - ε) (g 1 (below belowLimN) + ε)) (by simpa using εpos)
    isOpen_Ioo

  have: PosReal (above aboveLimN) := {
    pos := (max_lt_iff.mp aboveSpecN.1).2
  }
  have aboveRat: (1 / (above aboveLimN) :ℝ) ∈ Set.range Rat.cast := by
    use 1 / (above aboveLimN)
    simp
  obtain ⟨aboveWN, aboveW⟩:= tendsto_atTop_nhds.mp (w_Asymtotic_rat 1 (above aboveLimN) aboveRat)
    (Set.Ioo (g 1 (above aboveLimN) - ε) (g 1 (above aboveLimN) + ε)) (by simpa using εpos)
    isOpen_Ioo

  -- We combine the bound from both sequence
  use max 2 (max belowWN aboveWN)
  intro n nrange
  obtain ⟨n2, nr⟩ := max_le_iff.mp nrange
  obtain ⟨nbelow, nabove⟩ := max_le_iff.mp nr
  obtain belowW := belowW n nbelow
  obtain aboveW := aboveW n nabove

  -- Because of monotone, we are able to bound w 1 r / n by rational r'
  apply Set.mem_of_mem_of_subset
  · show wₗᵢ 1 r n / n ∈ Set.Icc  (wₗᵢ 1 (above aboveLimN) n / n) (wₗᵢ 1 (below belowLimN) n / n)
    constructor
    · refine div_le_div_of_nonneg_right ?_ (le_trans (by norm_num) n2)
      apply wₗᵢMono _ _ _ _ _ n2
      simp only [one_div]
      apply (inv_le_inv₀ (by exact PosReal.pos) (by exact PosReal.pos)).mpr
      exact le_of_lt (aboveLt aboveLimN)
    · refine div_le_div_of_nonneg_right ?_ (le_trans (by norm_num) n2)
      apply wₗᵢMono _ _ _ _ _ n2
      simp only [one_div]
      apply (inv_le_inv₀ (by exact PosReal.pos) (by exact PosReal.pos)).mpr
      exact le_of_lt (belowLt belowLimN)
  · refine subset_trans ?_ εsubst
    apply Set.Icc_subset_Ioo
    · refine lt_trans ?_ aboveW.1
      rw [mul_two, ← sub_sub]
      simp only [sub_lt_sub_iff_right]
      exact aboveDr.1
    · refine lt_trans belowW.2 ?_
      rw [mul_two, ← add_assoc]
      simp only [add_lt_add_iff_right]
      exact belowDr.2
