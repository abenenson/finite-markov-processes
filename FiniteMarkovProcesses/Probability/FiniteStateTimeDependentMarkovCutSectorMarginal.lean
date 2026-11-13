/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointCoefficient
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovFutureWordErasure
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesCutDisintegration

/-!
# Cut-sector marginals of time-dependent uniformized chains

On the sector with exactly `earlierCount` virtual events before a physical cut and
`laterCount` virtual events after it, summing every complete state word with a prescribed cut
state erases the future chain.  Integrating the sector then factors into the earlier endpoint
coefficient and the exact later ordered-simplex volume.

This is the fixed-count analytic core of intermediate-time projective consistency.  It does not
yet sum the two event-count sectors or identify a complete-history pushforward.

## Main results

- `sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutState`.
- `lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The prefix-time projection of a joined cut vector is its earlier block. -/
@[simp]
theorem finiteStateTimeDependentMarkovPrefixTimes_cutJoin
    (earlierCount laterCount : ℕ)
    (earlierTimes : Fin earlierCount → ℝ) (laterTimes : Fin laterCount → ℝ) :
    finiteStateTimeDependentMarkovPrefixTimes earlierCount laterCount
        (orderedJumpTimesCutJoin earlierCount laterCount
          (earlierTimes, laterTimes)) =
      earlierTimes := by
  funext index
  exact orderedJumpTimesCutJoin_apply_castAdd
    earlierCount laterCount earlierTimes laterTimes index

/-- At fixed virtual event times, summing complete words with a prescribed cut state leaves the
common clock factor times the endpoint word weight of the earlier block. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) (observed : State) :
    (∑ states : Fin (earlierCount + laterCount + 1) → State,
      if states (finiteStateTimeDependentMarkovCutStateIndex
          earlierCount laterCount) = observed then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
      ((rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates
            (finiteStateTimeDependentMarkovPrefixTimes
              earlierCount laterCount times) observed := by
  let clockFactor :=
    (rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
      Real.exp (-((rates.uniformizationRate : ℝ) * duration))
  calc
    (∑ states : Fin (earlierCount + laterCount + 1) → State,
      if states (finiteStateTimeDependentMarkovCutStateIndex
          earlierCount laterCount) = observed then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
      ∑ states : Fin (earlierCount + laterCount + 1) → State,
        clockFactor *
          (if states (finiteStateTimeDependentMarkovCutStateIndex
              earlierCount laterCount) = observed then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates times states
          else 0) := by
      apply Finset.sum_congr rfl
      intro states _hStates
      by_cases hObserved : states
          (finiteStateTimeDependentMarkovCutStateIndex
            earlierCount laterCount) = observed
      · simp only [hObserved, ite_true,
          finiteStateTimeDependentMarkovUniformizedSliceDensity, clockFactor]
      · simp only [hObserved, ite_false, mul_zero]
    _ = clockFactor *
        ∑ states : Fin (earlierCount + laterCount + 1) → State,
          (if states (finiteStateTimeDependentMarkovCutStateIndex
              earlierCount laterCount) = observed then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates times states
          else 0) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_cutState]

/-- The integrated mass of one cut sector factors into its earlier endpoint coefficient and the
exact volume of the later ordered simplex. -/
theorem lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration cut : ℝ) (hCutDuration : cut ≤ duration)
    (earlierCount laterCount : ℕ) (observed : State) :
    (∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
        orderedJumpTimesCutSector earlierCount laterCount 0 cut duration,
      ENNReal.ofReal
        (∑ states : Fin (earlierCount + laterCount + 1) → State,
          if states (finiteStateTimeDependentMarkovCutStateIndex
              earlierCount laterCount) = observed then
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times
          else 0)) =
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates cut earlierCount observed *
        ENNReal.ofReal
          ((duration - cut) ^ laterCount / laterCount.factorial) := by
  let clockFactor :=
    (rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
      Real.exp (-((rates.uniformizationRate : ℝ) * duration))
  have hClockNonnegative : 0 ≤ clockFactor := by
    dsimp [clockFactor]
    positivity
  have hIntegrand : Measurable fun
      times : Fin (earlierCount + laterCount) → ℝ ↦
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + laterCount + 1) → State,
            if states (finiteStateTimeDependentMarkovCutStateIndex
                earlierCount laterCount) = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_sum
    intro states _hStates
    by_cases hObserved : states
        (finiteStateTimeDependentMarkovCutStateIndex
          earlierCount laterCount) = observed
    · simpa only [hObserved, ite_true] using
        measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states
    · simp only [hObserved, ite_false]
      exact measurable_const
  rw [lintegral_orderedJumpTimesCutSector earlierCount laterCount 0 cut duration
    hIntegrand]
  simp_rw [sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutState]
  simp_rw [finiteStateTimeDependentMarkovPrefixTimes_cutJoin]
  have hClockFactor :
      (rates.uniformizationRate : ℝ) ^ (earlierCount + laterCount) *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration)) =
        clockFactor := rfl
  simp_rw [hClockFactor]
  simp_rw [ENNReal.ofReal_mul hClockNonnegative]
  rw [show (∫⁻ earlierTimes : Fin earlierCount → ℝ in
      orderedTimesInInterval earlierCount 0 cut,
      ∫⁻ _laterTimes : Fin laterCount → ℝ in
        orderedTimesInInterval laterCount cut duration,
        ENNReal.ofReal clockFactor *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes observed)) =
      ∫⁻ earlierTimes : Fin earlierCount → ℝ in
        orderedTimesInInterval earlierCount 0 cut,
        (ENNReal.ofReal clockFactor *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes observed)) *
          volume (orderedTimesInInterval laterCount cut duration) by
    apply lintegral_congr
    intro earlierTimes
    rw [lintegral_const]
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]]
  rw [volume_orderedTimesInInterval laterCount cut duration hCutDuration]
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
  rw [show orderedTimesInInterval earlierCount 0 cut =
      orderedJumpTimes earlierCount cut by
    rfl]
  have hReassociate (earlierTimes : Fin earlierCount → ℝ) :
      (ENNReal.ofReal clockFactor *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes observed)) *
          ENNReal.ofReal
            ((duration - cut) ^ laterCount / laterCount.factorial) =
        ENNReal.ofReal clockFactor *
          (ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes observed) *
            ENNReal.ofReal
              ((duration - cut) ^ laterCount / laterCount.factorial)) := by
    ac_rfl
  simp_rw [hReassociate]
  rw [lintegral_const_mul' (ENNReal.ofReal clockFactor) _ ENNReal.ofReal_ne_top]
  rw [lintegral_mul_const'
    (ENNReal.ofReal ((duration - cut) ^ laterCount / laterCount.factorial)) _
    ENNReal.ofReal_ne_top]
  ac_rfl

end

end FiniteMarkovProcesses.Probability
