import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Asymptotics Filter

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
