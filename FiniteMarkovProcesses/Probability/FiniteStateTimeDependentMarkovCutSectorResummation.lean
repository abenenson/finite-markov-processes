/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCutSectorMarginal
import FiniteMarkovProcesses.Probability.PoissonCountExpectation
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Resummation of future cut sectors

For a fixed number of events before a physical cut, summing over every possible number of later
common-clock events cancels the future Poisson survival factor exactly.  The result is the
fixed-count endpoint mass at the cut, independent of the larger observation horizon.

This is the analytic projectivity identity.  Identifying it with the literal fixed-time
complete-history marginal additionally requires the null-boundary cut partition.

## Main result

- `tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The real common-clock factor on one before/after event-count sector factors into the
fixed-before-count clock mass at the cut and a Poisson mass for the remaining duration. -/
theorem finiteStateTimeDependentMarkovCutClockFactor_eq_endpoint_mul_poisson
    (rates : FiniteStateTimeDependentMarkovRate State)
    (duration cut : ℝ) (hCutDuration : cut ≤ duration)
    (earlierCount laterCount : ℕ) :
    ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        ENNReal.ofReal
          ((duration - cut) ^ laterCount / laterCount.factorial) =
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ earlierCount *
            Real.exp (-((rates.uniformizationRate : ℝ) * cut))) *
        poissonCountPMF
          (rates.uniformizationRate *
            ⟨duration - cut, sub_nonneg.mpr hCutDuration⟩) laterCount := by
  let remainingDuration : ℝ≥0 :=
    ⟨duration - cut, sub_nonneg.mpr hCutDuration⟩
  have hClockNonnegative :
      0 ≤ (rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration)) := by positivity
  have hVolumeNonnegative :
      0 ≤ (duration - cut) ^ laterCount / laterCount.factorial :=
    div_nonneg (pow_nonneg (sub_nonneg.mpr hCutDuration) laterCount)
      (Nat.cast_nonneg laterCount.factorial)
  have hEndpointClockNonnegative :
      0 ≤ (rates.uniformizationRate : ℝ) ^ earlierCount *
        Real.exp (-((rates.uniformizationRate : ℝ) * cut)) := by positivity
  rw [← ENNReal.ofReal_mul hClockNonnegative]
  rw [show poissonCountPMF (rates.uniformizationRate * remainingDuration) laterCount =
      ENNReal.ofReal
        (poissonCountMassReal
          (rates.uniformizationRate * remainingDuration) laterCount) by
    rfl]
  rw [← ENNReal.ofReal_mul hEndpointClockNonnegative]
  congr 1
  unfold poissonCountMassReal
  change
    (rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
        ((duration - cut) ^ laterCount / laterCount.factorial) =
      (rates.uniformizationRate : ℝ) ^ earlierCount *
          Real.exp (-((rates.uniformizationRate : ℝ) * cut)) *
        (Real.exp (-((rates.uniformizationRate : ℝ) * (duration - cut))) *
          ((rates.uniformizationRate : ℝ) * (duration - cut)) ^ laterCount /
            laterCount.factorial)
  rw [pow_add, mul_pow]
  rw [show -((rates.uniformizationRate : ℝ) * duration) =
      -((rates.uniformizationRate : ℝ) * cut) +
        -((rates.uniformizationRate : ℝ) * (duration - cut)) by ring]
  rw [Real.exp_add]
  ring

/-- Summing every later-event cut sector yields exactly the fixed-earlier-count endpoint mass at
the cut.  In particular, the result no longer depends on the larger horizon. -/
theorem tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration cut : ℝ) (hCutDuration : cut ≤ duration)
    (earlierCount : ℕ) (observed : State) :
    (∑' laterCount : ℕ,
      ∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
          orderedJumpTimesCutSector earlierCount laterCount 0 cut duration,
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + laterCount + 1) → State,
            if states (finiteStateTimeDependentMarkovCutStateIndex
                earlierCount laterCount) = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ earlierCount *
            Real.exp (-((rates.uniformizationRate : ℝ) * cut))) *
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates cut earlierCount observed := by
  let endpointCoefficient :=
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
      initial rates cut earlierCount observed
  let endpointClock := ENNReal.ofReal
    ((rates.uniformizationRate : ℝ) ^ earlierCount *
      Real.exp (-((rates.uniformizationRate : ℝ) * cut)))
  let remainingIntensity : ℝ≥0 := rates.uniformizationRate *
    ⟨duration - cut, sub_nonneg.mpr hCutDuration⟩
  calc
    _ = ∑' laterCount : ℕ,
        endpointCoefficient *
          (endpointClock * poissonCountPMF remainingIntensity laterCount) := by
      apply tsum_congr
      intro laterCount
      rw [lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector
        initial rates duration cut hCutDuration]
      rw [← finiteStateTimeDependentMarkovCutClockFactor_eq_endpoint_mul_poisson
        rates duration cut hCutDuration earlierCount laterCount]
      dsimp only [endpointCoefficient]
      ac_rfl
    _ = endpointCoefficient *
        ∑' laterCount : ℕ,
          endpointClock * poissonCountPMF remainingIntensity laterCount := by
      rw [ENNReal.tsum_mul_left]
    _ = endpointCoefficient *
        (endpointClock *
          ∑' laterCount : ℕ, poissonCountPMF remainingIntensity laterCount) := by
      rw [ENNReal.tsum_mul_left]
    _ = endpointClock * endpointCoefficient := by
      rw [(poissonCountPMF remainingIntensity).tsum_coe]
      simp
      ac_rfl
    _ = _ := rfl

end

end FiniteMarkovProcesses.Probability
