/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Moments.Variance
public import FiniteMarkovProcesses.Probability.PoissonCountExponentialTail

/-!
# A uniform second-moment bound for Poisson counts

The exponential moment at unit exponent gives a convenient finite bound for the second moment of
every Poisson count.  The bound is intentionally coarse: its role is uniform-integrability and
heterogeneous-replica concentration, not sharp Poisson variance evaluation.

## Main results

- `integrable_sq_poissonCount`.
- `integral_sq_poissonCount_le`.
- `variance_poissonCount_le`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The square of every Poisson count is integrable. -/
theorem integrable_sq_poissonCount (intensity : ℝ≥0) :
    Integrable (fun count : ℕ ↦ (count : ℝ) ^ 2) (poissonMeasure intensity) := by
  have hExponential :=
    (integrable_exp_mul_poissonCount intensity 1).const_mul 2
  apply hExponential.mono'
  · exact (measurable_of_countable _).aestronglyMeasurable
  · filter_upwards [] with count
    have hQuadratic := Real.quadratic_le_exp_of_nonneg (Nat.cast_nonneg count)
    norm_num at hQuadratic ⊢
    linarith

/-- The Poisson second moment is bounded by twice its unit-exponential moment. -/
theorem integral_sq_poissonCount_le (intensity : ℝ≥0) :
    (∫ count : ℕ, (count : ℝ) ^ 2 ∂poissonMeasure intensity) ≤
      2 * Real.exp ((intensity : ℝ) * (Real.exp 1 - 1)) := by
  calc
    (∫ count : ℕ, (count : ℝ) ^ 2 ∂poissonMeasure intensity) ≤
        ∫ count : ℕ, 2 * Real.exp ((count : ℝ) * 1)
          ∂poissonMeasure intensity := by
      apply integral_mono
      · exact integrable_sq_poissonCount intensity
      · exact (integrable_exp_mul_poissonCount intensity 1).const_mul 2
      · intro count
        have hQuadratic := Real.quadratic_le_exp_of_nonneg (Nat.cast_nonneg count)
        norm_num at hQuadratic ⊢
        linarith
    _ = 2 * Real.exp ((intensity : ℝ) * (Real.exp 1 - 1)) := by
      rw [integral_const_mul, integral_exp_mul_poissonCount]

/-- The variance of a real Poisson count obeys the same finite exponential bound. -/
theorem variance_poissonCount_le (intensity : ℝ≥0) :
    variance (fun count : ℕ ↦ (count : ℝ)) (poissonMeasure intensity) ≤
      2 * Real.exp ((intensity : ℝ) * (Real.exp 1 - 1)) := by
  calc
    variance (fun count : ℕ ↦ (count : ℝ)) (poissonMeasure intensity) ≤
        ∫ count : ℕ, (count : ℝ) ^ 2 ∂poissonMeasure intensity :=
      variance_le_expectation_sq (measurable_of_countable _).aestronglyMeasurable
    _ ≤ 2 * Real.exp ((intensity : ℝ) * (Real.exp 1 - 1)) :=
      integral_sq_poissonCount_le intensity

end FiniteMarkovProcesses.Probability
