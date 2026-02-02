import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod


open MeasureTheory ProbabilityTheory


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma norm_expectation_le_of_norm_le_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : Ω → E} {C : ℝ} (h : ∀ᵐ (x : Ω) ∂μ, ‖f x‖ ≤ C) :
  ‖μ[f]‖ ≤ C := by
  calc
    _ ≤ C * (μ Set.univ).toReal := by apply norm_integral_le_of_norm_le_const h
    _ = _ := by
      have : μ (Set.univ : Set Ω) = 1 := isProbabilityMeasure_iff.mp (by assumption)
      rw [this]
      simp

lemma abs_expectation_le_of_abs_le_const
  {f : Ω → ℝ} {C : ℝ} (h : ∀ᵐ (x : Ω) ∂μ, |f x| ≤ C) :
  |μ[f]| ≤ C := by
  exact @norm_expectation_le_of_norm_le_const Ω _ _ _ ℝ _ _ f C h
