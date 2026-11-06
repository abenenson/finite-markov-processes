/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Expectation of a Poisson count

This module proves directly from the Poisson mass recursion that the real-valued count is
integrable and has expectation equal to its intensity. The result belongs to the probability
layer and can be reused without importing a relative-entropy development.

## Main Results

- `integrable_poissonCount`: every Poisson count has a finite first moment.
- `integral_poissonCount`: the expected Poisson count equals its intensity.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The exact real mass used by the original Poisson PMF presentation. -/
noncomputable def poissonCountMassReal (intensity : ℝ≥0) (count : ℕ) : ℝ :=
  Real.exp (-(intensity : ℝ)) * (intensity : ℝ) ^ count / count.factorial

/-- The original real Poisson masses sum to one at every nonnegative intensity. -/
theorem hasSum_poissonCountMassReal (intensity : ℝ≥0) :
    HasSum (fun count : ℕ ↦ poissonCountMassReal intensity count) 1 := by
  simpa only [poissonCountMassReal] using
    ProbabilityTheory.hasSum_one_poissonMeasure intensity

/-- Every original Poisson mass is nonnegative, including at zero intensity. -/
theorem poissonCountMassReal_nonneg {intensity : ℝ≥0} {count : ℕ} :
    0 ≤ poissonCountMassReal intensity count := by
  unfold poissonCountMassReal
  positivity

/-- Every original Poisson mass is positive at a positive intensity. -/
theorem poissonCountMassReal_pos {intensity : ℝ≥0} {count : ℕ}
    (hIntensity : 0 < intensity) : 0 < poissonCountMassReal intensity count := by
  unfold poissonCountMassReal
  positivity

/-- The exact original count PMF, retained without Mathlib's deprecated Poisson PMF API. -/
noncomputable def poissonCountPMF (intensity : ℝ≥0) : PMF ℕ := by
  refine ⟨fun count ↦ ENNReal.ofReal (poissonCountMassReal intensity count), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact (hasSum_poissonCountMassReal intensity).toNNReal
    (fun count ↦ poissonCountMassReal_nonneg)

/-- The retained count PMF has exactly the original point mass formula. -/
@[simp]
theorem poissonCountPMF_apply (intensity : ℝ≥0) (count : ℕ) :
    poissonCountPMF intensity count = ENNReal.ofReal (poissonCountMassReal intensity count) := rfl

/-- Mathlib's weighted-Dirac law equals the entire original PMF measure, including
intensity zero. -/
theorem poissonMeasure_eq_poissonCountPMF_toMeasure (intensity : ℝ≥0) :
    poissonMeasure intensity = (poissonCountPMF intensity).toMeasure := by
  apply Measure.ext_of_singleton
  intro count
  rw [ProbabilityTheory.poissonMeasure_singleton,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  rfl

/-- Multiplication by the successor count shifts the Poisson mass recursion. -/
theorem succ_mul_poissonPMFReal (intensity : ℝ≥0) (count : ℕ) :
    ((count + 1 : ℕ) : ℝ) * poissonCountMassReal intensity (count + 1) =
      (intensity : ℝ) * poissonCountMassReal intensity count := by
  rw [poissonCountMassReal, poissonCountMassReal, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- The mass-weighted Poisson count series sums to the intensity. -/
theorem hasSum_count_mul_poissonPMFReal (intensity : ℝ≥0) :
    HasSum (fun count : ℕ ↦ (count : ℝ) * poissonCountMassReal intensity count)
      (intensity : ℝ) := by
  have hShifted : HasSum
      (fun count : ℕ ↦
        ((count + 1 : ℕ) : ℝ) * poissonCountMassReal intensity (count + 1))
      (intensity : ℝ) := by
    convert (hasSum_poissonCountMassReal intensity).mul_left (intensity : ℝ) using 1
    · ext count
      exact succ_mul_poissonPMFReal intensity count
    · simp
  apply (hasSum_nat_add_iff' 1).mp
  convert hShifted using 1
  simp

/-- The real-valued count is integrable under every Poisson count law. -/
theorem integrable_poissonCount (intensity : ℝ≥0) :
    Integrable (fun count : ℕ ↦ (count : ℝ)) (poissonMeasure intensity) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  simpa only [poissonCountMassReal, Real.norm_natCast, mul_comm] using
    (hasSum_count_mul_poissonPMFReal intensity).summable

/-- The expected count under a Poisson law is exactly its integrated intensity. -/
theorem integral_poissonCount (intensity : ℝ≥0) :
    ∫ count : ℕ, (count : ℝ) ∂poissonMeasure intensity = (intensity : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure' (integrable_poissonCount intensity)]
  simpa only [poissonCountMassReal, smul_eq_mul, mul_comm] using
    (hasSum_count_mul_poissonPMFReal intensity).tsum_eq

end FiniteMarkovProcesses.Probability
