import Mathlib

lemma sum_cartesian (a b: ℝ) (f: α → ℝ) (g: β → ℝ) (h1: HasSum f a) (h2: HasSum g b):
  HasSum (fun (u, v) ↦ (f u) * (g v)) (a * b) := by sorry
