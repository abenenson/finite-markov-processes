/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.PoissonCountExpectation
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Exponential moments and tails of Poisson counts

This module evaluates the exponential moment of a Poisson count at every real exponent and derives
the corresponding exponential Markov tail bound.  The result is source-neutral and retains the
free positive exponent needed for Chernoff optimization or a fixed-exponent coarse estimate.

## Main declarations

- `hasSum_exp_mul_poissonPMFReal`: exact mass-weighted exponential series.
- `integral_exp_mul_poissonCount`: exact exponential moment.
- `poissonMeasure_gt_le_exponential`: positive-exponent upper-tail bound.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The mass-weighted exponential Poisson series has the exact cumulant-generating value. -/
theorem hasSum_exp_mul_poissonPMFReal (intensity : ℝ≥0) (exponent : ℝ) :
    HasSum (fun count : ℕ =>
      Real.exp ((count : ℝ) * exponent) * poissonCountMassReal intensity count)
      (Real.exp ((intensity : ℝ) * (Real.exp exponent - 1))) := by
  have hSeries :=
    (NormedSpace.expSeries_div_hasSum_exp
      ((intensity : ℝ) * Real.exp exponent)).mul_left
        (Real.exp (-(intensity : ℝ)))
  convert hSeries using 1
  · ext count
    rw [poissonCountMassReal, Real.exp_nat_mul, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

/-- Every real exponential moment of a Poisson count is integrable. -/
theorem integrable_exp_mul_poissonCount (intensity : ℝ≥0) (exponent : ℝ) :
    Integrable (fun count : ℕ => Real.exp ((count : ℝ) * exponent))
      (poissonMeasure intensity) := by
  constructor
  · exact (measurable_of_countable _).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_norm, lintegral_countable']
    simp_rw [poissonMeasure_eq_poissonCountPMF_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), poissonCountPMF_apply]
    have hFinite :=
      (hasSum_exp_mul_poissonPMFReal intensity exponent).summable.tsum_ofReal_lt_top
    simp_rw [ENNReal.ofReal_mul (Real.exp_nonneg _)] at hFinite
    simpa [Real.norm_eq_abs, abs_of_pos] using hFinite

/-- The exponential moment of a Poisson count is the exponential of its cumulant. -/
theorem integral_exp_mul_poissonCount (intensity : ℝ≥0) (exponent : ℝ) :
    ∫ count : ℕ, Real.exp ((count : ℝ) * exponent) ∂poissonMeasure intensity =
      Real.exp ((intensity : ℝ) * (Real.exp exponent - 1)) := by
  have hIntegrable : Integrable (fun count : ℕ ↦ Real.exp ((count : ℝ) * exponent))
      (poissonCountPMF intensity).toMeasure := by
    rw [← poissonMeasure_eq_poissonCountPMF_toMeasure]
    exact integrable_exp_mul_poissonCount intensity exponent
  rw [poissonMeasure_eq_poissonCountPMF_toMeasure, PMF.integral_eq_tsum _ _ hIntegrable]
  have hApply (count : ℕ) :
      (poissonCountPMF intensity count).toReal = poissonCountMassReal intensity count := by
    change (ENNReal.ofReal (poissonCountMassReal intensity count)).toReal = _
    exact ENNReal.toReal_ofReal poissonCountMassReal_nonneg
  simp_rw [hApply]
  simpa [smul_eq_mul, mul_comm] using
    (hasSum_exp_mul_poissonPMFReal intensity exponent).tsum_eq

/-- Positive-exponent exponential Markov bound for the strict upper tail of a Poisson count. -/
theorem poissonMeasure_gt_le_exponential
    (intensity : ℝ≥0) {exponent : ℝ} (hExponent : 0 < exponent)
    (threshold : ℝ) :
    poissonMeasure intensity {count : ℕ | threshold < count} ≤
      ENNReal.ofReal
        (Real.exp ((intensity : ℝ) * (Real.exp exponent - 1) -
          threshold * exponent)) := by
  let exponentialCount : ℕ → ℝ≥0∞ :=
    fun count => ENNReal.ofReal (Real.exp ((count : ℝ) * exponent))
  let exponentialThreshold : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (threshold * exponent))
  have hThresholdPositive : exponentialThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hEventSubset :
      {count : ℕ | threshold < count} ⊆
        {count | exponentialThreshold ≤ exponentialCount count} := by
    intro count hCount
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hCount.le hExponent.le
  calc
    poissonMeasure intensity {count : ℕ | threshold < count} ≤
        poissonMeasure intensity
          {count | exponentialThreshold ≤ exponentialCount count} :=
      measure_mono hEventSubset
    _ ≤ (∫⁻ count, exponentialCount count ∂poissonMeasure intensity) /
        exponentialThreshold :=
      meas_ge_le_lintegral_div
        (measurable_of_countable exponentialCount).aemeasurable
        hThresholdPositive ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal
        (Real.exp ((intensity : ℝ) * (Real.exp exponent - 1))) /
          ENNReal.ofReal (Real.exp (threshold * exponent)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_exp_mul_poissonCount intensity exponent)
        (Filter.Eventually.of_forall fun count =>
          (Real.exp_pos ((count : ℝ) * exponent)).le)]
      rw [integral_exp_mul_poissonCount]
    _ = ENNReal.ofReal
        (Real.exp ((intensity : ℝ) * (Real.exp exponent - 1) -
          threshold * exponent)) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]

end FiniteMarkovProcesses.Probability
