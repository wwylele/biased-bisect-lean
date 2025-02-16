import BiasedBisect.Basic


lemma stuff (w1 w2 n: ℝ) (f: ℝ → ℝ):
∫ (x : ℝ) in w1..w2, f (n - x) = ∫ (x : ℝ) in (n - w2)..(n - w1), f x := by
  simp [intervalIntegral.integral_comp_sub_left]
