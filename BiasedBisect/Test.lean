import BiasedBisect.Basic


lemma stuff(a b c: ℝ) (f: ℝ → ℝ) (h2: ∀ (x: ℝ), x ∈ Set.Ico a b → c = f x):
   ∀ᵐ (x : ℝ), x ∈ Set.Ioc a b → c = f x := by
  have h2': ∀ᵐ (x: ℝ), x ∈ Set.Ico a b → c = f x:= by sorry
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc h2'] with x hx using by
