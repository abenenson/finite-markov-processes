/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedDeletionDensity
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedHistoryExpectation
import FiniteMarkovProcesses.Probability.PoissonCountExponentialTail

/-!
# Exponential jump-count tails for finite-state Markov histories

The physical finite-state jump law is the exact pushforward of the common-clock uniformized law
under self-event deletion.  Deletion cannot increase event count, while the uniformized event
count is exactly Poisson.  This module composes those facts into an initial-law-uniform
exponential tail bound for the physical jump count.

## Main declarations

- `integrable_exp_mul_finiteStateMarkovJumpCount`: physical count exponential integrability.
- `integral_exp_mul_finiteStateMarkovJumpCount_le`: physical moment Poisson domination.
- `finiteStateMarkovJumpDensityMeasure_jumpCount_gt_le_poisson`: physical count domination.
- `finiteStateMarkovJumpDensityMeasure_jumpCount_gt_le_exponential`: explicit Chernoff bound.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Every nonnegative exponential moment of the physical jump count is integrable.  The proof
uses the exact uniformized source and the fact that self-event deletion cannot increase count. -/
theorem integrable_exp_mul_finiteStateMarkovJumpCount
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    Integrable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.jumpCount : ℝ) * exponent))
      (finiteStateMarkovJumpDensityMeasure initial generator duration) := by
  have hUniformized : Integrable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.jumpCount : ℝ) * exponent))
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
    have hPoisson := integrable_exp_mul_poissonCount
      (generator.uniformizationRate * duration) exponent
    rw [← map_jumpCount_finiteStateMarkovUniformizedDensityMeasure
      initial generator duration] at hPoisson
    exact (integrable_map_measure hPoisson.1
      FiniteJumpHistory.measurable_jumpCount.aemeasurable).mp hPoisson
  have hDeleted : Integrable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.deleteSelfEvents.jumpCount : ℝ) * exponent))
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
    refine hUniformized.mono' ?_ (Filter.Eventually.of_forall fun history => ?_)
    · have hDeletedCount : Measurable
          (fun history : FiniteJumpHistory State =>
            (history.deleteSelfEvents.jumpCount : ℝ)) :=
        (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
          (FiniteJumpHistory.measurable_jumpCount.comp
            FiniteJumpHistory.measurable_deleteSelfEvents)
      exact ((hDeletedCount.mul measurable_const).exp).aestronglyMeasurable
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hExponent
    exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
  rw [← map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator duration.coe_nonneg]
  have hHistoryExponential : Measurable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.jumpCount : ℝ) * exponent)) := by
    exact (((measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
      FiniteJumpHistory.measurable_jumpCount).mul measurable_const).exp
  exact (integrable_map_measure hHistoryExponential.aestronglyMeasurable
    FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable).mpr hDeleted

/-- At every nonnegative exponent, the physical jump-count exponential moment is bounded by the
exact common-clock Poisson moment, uniformly over the initial law. -/
theorem integral_exp_mul_finiteStateMarkovJumpCount_le
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    (∫ history : FiniteJumpHistory State,
        Real.exp ((history.jumpCount : ℝ) * exponent)
      ∂finiteStateMarkovJumpDensityMeasure initial generator duration) ≤
      Real.exp (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
        (Real.exp exponent - 1)) := by
  have hUniformized : Integrable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.jumpCount : ℝ) * exponent))
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
    have hPoisson := integrable_exp_mul_poissonCount
      (generator.uniformizationRate * duration) exponent
    rw [← map_jumpCount_finiteStateMarkovUniformizedDensityMeasure
      initial generator duration] at hPoisson
    exact (integrable_map_measure hPoisson.1
      FiniteJumpHistory.measurable_jumpCount.aemeasurable).mp hPoisson
  have hDeleted : Integrable
      (fun history : FiniteJumpHistory State =>
        Real.exp ((history.deleteSelfEvents.jumpCount : ℝ) * exponent))
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
    refine hUniformized.mono' ?_ (Filter.Eventually.of_forall fun history => ?_)
    · have hDeletedCount : Measurable
          (fun history : FiniteJumpHistory State =>
            (history.deleteSelfEvents.jumpCount : ℝ)) :=
        (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
          (FiniteJumpHistory.measurable_jumpCount.comp
            FiniteJumpHistory.measurable_deleteSelfEvents)
      exact ((hDeletedCount.mul measurable_const).exp).aestronglyMeasurable
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hExponent
    exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
  rw [← map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator duration.coe_nonneg]
  rw [integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable (by fun_prop)]
  calc
    (∫ history : FiniteJumpHistory State,
        Real.exp ((history.deleteSelfEvents.jumpCount : ℝ) * exponent)
      ∂finiteStateMarkovUniformizedDensityMeasure initial generator duration) ≤
        ∫ history : FiniteJumpHistory State,
          Real.exp ((history.jumpCount : ℝ) * exponent)
        ∂finiteStateMarkovUniformizedDensityMeasure initial generator duration := by
      apply integral_mono hDeleted hUniformized
      intro history
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ hExponent
      exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
    _ = ∫ count : ℕ, Real.exp ((count : ℝ) * exponent)
      ∂Measure.map FiniteJumpHistory.jumpCount
          (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
      exact (integral_map FiniteJumpHistory.measurable_jumpCount.aemeasurable
        ((((measurable_of_countable (fun count : ℕ => (count : ℝ))).mul
          measurable_const).exp).aestronglyMeasurable)).symm
    _ = Real.exp (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
        (Real.exp exponent - 1)) := by
      rw [map_jumpCount_finiteStateMarkovUniformizedDensityMeasure]
      exact integral_exp_mul_poissonCount
        (generator.uniformizationRate * duration) exponent

/-- The physical jump-count upper tail is bounded by the common-clock Poisson upper tail,
uniformly over the supplied initial law. -/
theorem finiteStateMarkovJumpDensityMeasure_jumpCount_gt_le_poisson
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (threshold : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator duration
        {history | threshold < history.jumpCount} ≤
      poissonMeasure
        (generator.uniformizationRate * duration)
        {count | threshold < count} := by
  let countEvent : Set ℕ := {count | threshold < count}
  have hCountEvent : MeasurableSet countEvent := MeasurableSet.of_discrete
  have hHistoryEvent : MeasurableSet
      {history : FiniteJumpHistory State | threshold < history.jumpCount} := by
    exact FiniteJumpHistory.measurable_jumpCount hCountEvent
  rw [← map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator duration.coe_nonneg]
  rw [Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents hHistoryEvent]
  calc
    finiteStateMarkovUniformizedDensityMeasure initial generator duration
        (FiniteJumpHistory.deleteSelfEvents ⁻¹'
          {history : FiniteJumpHistory State | threshold < history.jumpCount}) ≤
      finiteStateMarkovUniformizedDensityMeasure initial generator duration
        {history | threshold < history.jumpCount} := by
          apply measure_mono
          intro history hHistory
          change threshold < ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) at hHistory
          change threshold < ((history.jumpCount : ℕ) : ℝ)
          exact hHistory.trans_le (by
            exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history)
    _ = Measure.map FiniteJumpHistory.jumpCount
        (finiteStateMarkovUniformizedDensityMeasure initial generator duration)
          countEvent := by
      simpa [countEvent] using
        (Measure.map_apply FiniteJumpHistory.measurable_jumpCount hCountEvent).symm
    _ = poissonMeasure
        (generator.uniformizationRate * duration) countEvent := by
      exact congrArg (fun law : Measure ℕ => law countEvent)
        (map_jumpCount_finiteStateMarkovUniformizedDensityMeasure
          initial generator duration)

/-- Initial-law-uniform positive-exponent Chernoff bound for the physical jump count. -/
theorem finiteStateMarkovJumpDensityMeasure_jumpCount_gt_le_exponential
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0)
    {exponent : ℝ} (hExponent : 0 < exponent) (threshold : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator duration
        {history | threshold < history.jumpCount} ≤
      ENNReal.ofReal
        (Real.exp
          (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
              (Real.exp exponent - 1) - threshold * exponent)) := by
  exact (finiteStateMarkovJumpDensityMeasure_jumpCount_gt_le_poisson
    initial generator duration threshold).trans
      (poissonMeasure_gt_le_exponential
        (generator.uniformizationRate * duration)
        hExponent threshold)

end FiniteMarkovProcesses.Probability
