import BiasedBisect.CrossSection
import BiasedBisect.Integer

/-
g ^ s = (1 - g) ^ t

-/

lemma gExist (s t: ℝ) [PosReal s] [PosReal t]:
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
def g (s t: ℝ) [PosReal s] [PosReal t] := (gExist s t).choose

lemma g_satisfies (s t: ℝ) [PosReal s] [PosReal t]: (g s t) ^ s = (1 - (g s t)) ^ t := by
  obtain ⟨⟨range, satisfies⟩, unique⟩ := (gExist s t).choose_spec
  exact satisfies

lemma g_range (s t: ℝ) [PosReal s] [PosReal t]: (g s t) ∈ Set.Ioo 0 1 := by
  obtain ⟨⟨⟨left, right⟩, satisfies⟩, unique⟩ := (gExist s t).choose_spec
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

lemma g_eq (s t: ℕ+): (ξ₀ s t ^ (t: ℕ)) = g s t := by
  obtain ⟨_, unique⟩ := (gExist s t).choose_spec
  apply unique
  constructor
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

lemma w_AsymtoticRational (s t: ℝ) [PosReal s] [PosReal t] (rational: s / t ∈ Set.range Rat.cast):
Filter.Tendsto (fun n ↦ (wₗᵢ s t n: ℝ) / n) Filter.atTop (nhds (g s t)) := by
  obtain ⟨ST, STeq⟩ := Set.mem_range.mpr rational
  let T := Rat.pnatDen ST
  let S' := Rat.num ST
  have eq1: (S' / T: ℚ) = s / t := by
    unfold S' T
    rw [Rat.coe_pnatDen, Rat.num_div_den, STeq]
  have eq2: S' = s / t * T := by
    sorry
  sorry
