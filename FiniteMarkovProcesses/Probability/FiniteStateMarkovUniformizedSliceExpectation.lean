/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedHistoryDensity
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedWordOccupation
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Fixed-count expectations of finite-state uniformized histories

This module combines the common-clock slice density, complete-word reward identities, and exact
ordered-time volume. For every fixed virtual-event count, summing over all state words and
integrating all ordered event times gives the literal Poisson count mass times the corresponding
stationary additive reward.

The carrier still includes virtual self-events. Physical deletion and the unbounded count-sum
transport remain separate.

## Main Results

- `finiteStateMarkovUniformizedSliceDensity_eq_clock_mul_stateWordWeight`: clock/state-word
  factorization of the common-clock density.
- `sum_uniformizedSliceDensity_mul_additiveSliceReward_stationary`: exact stationary state-word
  summation on every event-time vector.
- `finiteStateMarkovUniformizedCountAdditiveRewardIntegral_stationary`: exact ordered-time
  integral as a Poisson count coefficient.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Probability weight of one complete uniformized state word. -/
noncomputable def finiteStateUniformizedStateWordWeight
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State) : ℝ :=
  (initial (states 0)).toReal *
    finiteStateUniformizedContinuationWeight generator (states 0) (Fin.tail states)

/-- A word's event-intensity product is the common-clock power times its conditional weight. -/
theorem finiteStateMarkovUniformizedTransitionIntensityProduct_eq_rate_pow_mul_weight
    (generator : FiniteStateMarkovGenerator State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State) :
    finiteStateMarkovUniformizedTransitionIntensityProduct generator states =
      (generator.uniformizationRate : ℝ) ^ eventCount *
        finiteStateUniformizedContinuationWeight generator
          (states 0) (Fin.tail states) := by
  unfold finiteStateMarkovUniformizedTransitionIntensityProduct
    FiniteStateMarkovGenerator.uniformizedTransitionIntensity
    finiteStateUniformizedContinuationWeight
  rw [show Fin.cons (states 0) (Fin.tail states) = states by
    exact Fin.cons_self_tail states]
  rw [Finset.prod_mul_distrib]
  simp

/-- Uniformized slice density factors into clock, survival, and state-word weights. -/
theorem finiteStateMarkovUniformizedSliceDensity_eq_clock_mul_stateWordWeight
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    finiteStateMarkovUniformizedSliceDensity initial generator T states times =
      (generator.uniformizationRate : ℝ) ^ eventCount *
        Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
          finiteStateUniformizedStateWordWeight initial generator states := by
  unfold finiteStateMarkovUniformizedSliceDensity
    finiteStateUniformizedStateWordWeight
  rw [finiteStateMarkovUniformizedTransitionIntensityProduct_eq_rate_pow_mul_weight]
  ring

/-- Complete state-word probability weights sum to one. -/
theorem sum_finiteStateUniformizedStateWordWeight
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (eventCount : ℕ) :
    ∑ states : Fin (eventCount + 1) → State,
      finiteStateUniformizedStateWordWeight initial generator states = 1 := by
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ source : State, ∑ future : Fin eventCount → State,
    finiteStateUniformizedStateWordWeight initial generator (Fin.cons source future)) = 1
  unfold finiteStateUniformizedStateWordWeight
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [show (∑ source : State, ∑ future : Fin eventCount → State,
      (initial source).toReal *
        finiteStateUniformizedContinuationWeight generator source future) =
    ∑ source : State, (initial source).toReal *
      ∑ future : Fin eventCount → State,
        finiteStateUniformizedContinuationWeight generator source future by
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]]
  simp_rw [sum_finiteStateUniformizedContinuationWeight, mul_one]
  exact PMF.sum_toReal initial

/-- State-summed common-clock density is constant on each fixed-count time simplex. -/
theorem sum_finiteStateMarkovUniformizedSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (eventCount : ℕ) (times : Fin eventCount → ℝ) :
    (∑ states : Fin (eventCount + 1) → State,
      finiteStateMarkovUniformizedSliceDensity initial generator T states times) =
      (generator.uniformizationRate : ℝ) ^ eventCount *
        Real.exp (-((generator.uniformizationRate : ℝ) * T)) := by
  simp_rw [finiteStateMarkovUniformizedSliceDensity_eq_clock_mul_stateWordWeight]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [show (∑ states : Fin (eventCount + 1) → State,
      Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
        finiteStateUniformizedStateWordWeight initial generator states) =
      Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
        ∑ states : Fin (eventCount + 1) → State,
          finiteStateUniformizedStateWordWeight initial generator states by
    rw [Finset.mul_sum]]
  rw [sum_finiteStateUniformizedStateWordWeight, mul_one]

/-- The ordered-time integral of the state-summed fixed-count density is its Poisson mass. -/
theorem integral_sum_finiteStateMarkovUniformizedSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (eventCount : ℕ) :
    (∫ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
      ∑ states : Fin (eventCount + 1) → State,
        finiteStateMarkovUniformizedSliceDensity
          initial generator duration states times) =
      poissonCountMassReal (generator.uniformizationRate * duration) eventCount := by
  simp_rw [sum_finiteStateMarkovUniformizedSliceDensity]
  rw [integral_const]
  rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [smul_eq_mul]
  change (volume (orderedJumpTimes eventCount duration)).toReal * _ = _
  rw [volume_orderedJumpTimes eventCount duration duration.coe_nonneg]
  rw [ENNReal.toReal_ofReal]
  · unfold poissonCountMassReal
    rw [NNReal.coe_mul]
    ring
  · exact div_nonneg (pow_nonneg duration.coe_nonneg eventCount)
      (Nat.cast_nonneg eventCount.factorial)

/-- Reindex a full state-word transition reward as a source plus conditional future word. -/
theorem sum_stateWordWeight_mul_transitionRewardSum
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (reward : State → State → ℝ) (eventCount : ℕ) :
    (∑ states : Fin (eventCount + 1) → State,
      finiteStateUniformizedStateWordWeight initial generator states *
        ∑ index : Fin eventCount,
          reward (states index.castSucc) (states index.succ)) =
      finiteStateUniformizedWordTransitionRewardExpectation
        generator initial reward eventCount := by
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ source : State, ∑ future : Fin eventCount → State,
    finiteStateUniformizedStateWordWeight initial generator (Fin.cons source future) *
      finiteStateUniformizedTransitionRewardSum reward source future) = _
  unfold finiteStateUniformizedStateWordWeight
  simp only [Fin.cons_zero, Fin.tail_cons]
  unfold finiteStateUniformizedWordTransitionRewardExpectation
    finiteStateUniformizedConditionalTransitionRewardExpectation
  rw [show (∑ source : State, ∑ future : Fin eventCount → State,
      (initial source).toReal *
          finiteStateUniformizedContinuationWeight generator source future *
        finiteStateUniformizedTransitionRewardSum reward source future) =
    ∑ source : State,
      (initial source).toReal * ∑ future : Fin eventCount → State,
        finiteStateUniformizedContinuationWeight generator source future *
          finiteStateUniformizedTransitionRewardSum reward source future by
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro future _
    ring]

/-- Reindex a full state-word state reward as a source plus conditional future word. -/
theorem sum_stateWordWeight_mul_stateRewardSum
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 1) → ℝ) :
    (∑ states : Fin (eventCount + 1) → State,
      finiteStateUniformizedStateWordWeight initial generator states *
        ∑ index : Fin (eventCount + 1),
          coefficients index * reward (states index)) =
      finiteStateUniformizedWordStateRewardExpectation
        generator initial reward coefficients := by
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ source : State, ∑ future : Fin eventCount → State,
    finiteStateUniformizedStateWordWeight initial generator (Fin.cons source future) *
      finiteStateUniformizedStateRewardSum reward coefficients source future) = _
  unfold finiteStateUniformizedStateWordWeight
  simp only [Fin.cons_zero, Fin.tail_cons]
  unfold finiteStateUniformizedWordStateRewardExpectation
    finiteStateUniformizedConditionalStateRewardExpectation
  rw [show (∑ source : State, ∑ future : Fin eventCount → State,
      (initial source).toReal *
          finiteStateUniformizedContinuationWeight generator source future *
        finiteStateUniformizedStateRewardSum reward coefficients source future) =
    ∑ source : State,
      (initial source).toReal * ∑ future : Fin eventCount → State,
        finiteStateUniformizedContinuationWeight generator source future *
          finiteStateUniformizedStateRewardSum reward coefficients source future by
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro future _
    ring]

/-- Additive transition-plus-dwell reward on one timed state-word slice. -/
noncomputable def finiteStateMarkovAdditiveSliceReward
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  (∑ index : Fin eventCount,
    transitionReward (states index.castSucc) (states index.succ)) +
  ∑ index : Fin (eventCount + 1),
    FiniteJumpHistory.dwellTimeVector T times index * stateReward (states index)

/-- At stationarity, summing density-weighted additive rewards over all state words leaves
a constant fixed-count reward density on the ordered-time simplex. -/
theorem sum_uniformizedSliceDensity_mul_additiveSliceReward_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) (eventCount : ℕ) (times : Fin eventCount → ℝ) :
    (∑ states : Fin (eventCount + 1) → State,
      finiteStateMarkovUniformizedSliceDensity stationary.pmf generator T states times *
        finiteStateMarkovAdditiveSliceReward
          transitionReward stateReward T states times) =
      ((generator.uniformizationRate : ℝ) ^ eventCount *
        Real.exp (-((generator.uniformizationRate : ℝ) * T))) *
        ((eventCount : ℝ) *
            uniformizedStationaryTransitionReward generator stationary transitionReward +
          T * ∑ state, (stationary.weight state : ℝ) * stateReward state) := by
  simp_rw [finiteStateMarkovUniformizedSliceDensity_eq_clock_mul_stateWordWeight]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [show (∑ states : Fin (eventCount + 1) → State,
      Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
        (finiteStateUniformizedStateWordWeight stationary.pmf generator states *
          finiteStateMarkovAdditiveSliceReward
            transitionReward stateReward T states times)) =
      Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
        ∑ states : Fin (eventCount + 1) → State,
          finiteStateUniformizedStateWordWeight stationary.pmf generator states *
            finiteStateMarkovAdditiveSliceReward
              transitionReward stateReward T states times by
    rw [Finset.mul_sum]]
  unfold finiteStateMarkovAdditiveSliceReward
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [sum_stateWordWeight_mul_transitionRewardSum]
  rw [sum_stateWordWeight_mul_stateRewardSum]
  rw [finiteStateUniformizedWordTransitionRewardExpectation_stationary]
  rw [finiteStateUniformizedWordDwellRewardExpectation_stationary]
  ring

/-- Density-weighted additive reward integrated over all state words and ordered times at one
fixed virtual-event count. -/
noncomputable def finiteStateMarkovUniformizedCountAdditiveRewardIntegral
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (eventCount : ℕ) : ℝ :=
  ∫ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
    ∑ states : Fin (eventCount + 1) → State,
      finiteStateMarkovUniformizedSliceDensity
          stationary.pmf generator duration states times *
        finiteStateMarkovAdditiveSliceReward
          transitionReward stateReward duration states times

/-- The fixed-count ordered-time reward integral is the literal Poisson count mass times its
stationary transition-plus-occupation reward. -/
theorem finiteStateMarkovUniformizedCountAdditiveRewardIntegral_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (eventCount : ℕ) :
    finiteStateMarkovUniformizedCountAdditiveRewardIntegral generator stationary
        transitionReward stateReward duration eventCount =
      poissonCountMassReal (generator.uniformizationRate * duration) eventCount *
        ((eventCount : ℝ) *
            uniformizedStationaryTransitionReward generator stationary transitionReward +
          (duration : ℝ) *
            ∑ state, (stationary.weight state : ℝ) * stateReward state) := by
  unfold finiteStateMarkovUniformizedCountAdditiveRewardIntegral
  simp_rw [sum_uniformizedSliceDensity_mul_additiveSliceReward_stationary]
  rw [integral_const]
  rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [smul_eq_mul]
  change (volume (orderedJumpTimes eventCount duration)).toReal * _ = _
  rw [volume_orderedJumpTimes eventCount duration duration.coe_nonneg]
  rw [ENNReal.toReal_ofReal]
  · unfold poissonCountMassReal
    rw [NNReal.coe_mul]
    ring
  · exact div_nonneg (pow_nonneg duration.coe_nonneg eventCount)
      (Nat.cast_nonneg eventCount.factorial)

/-- Summing all fixed-count reward integrals gives the exact stationary uniformized reward. -/
theorem tsum_finiteStateMarkovUniformizedCountAdditiveRewardIntegral_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) :
    ∑' eventCount : ℕ,
        finiteStateMarkovUniformizedCountAdditiveRewardIntegral generator stationary
          transitionReward stateReward duration eventCount =
      ((generator.uniformizationRate : ℝ) * (duration : ℝ)) *
          uniformizedStationaryTransitionReward generator stationary transitionReward +
        (duration : ℝ) *
          ∑ state, (stationary.weight state : ℝ) * stateReward state := by
  simp_rw [finiteStateMarkovUniformizedCountAdditiveRewardIntegral_stationary]
  let intensity := generator.uniformizationRate * duration
  let transitionMean :=
    uniformizedStationaryTransitionReward generator stationary transitionReward
  let occupationMean :=
    (duration : ℝ) * ∑ state, (stationary.weight state : ℝ) * stateReward state
  have hTransition :
      HasSum (fun eventCount : ℕ ↦
        poissonCountMassReal intensity eventCount * (eventCount : ℝ) * transitionMean)
        ((intensity : ℝ) * transitionMean) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_count_mul_poissonPMFReal intensity).mul_right transitionMean
  have hOccupation :
      HasSum (fun eventCount : ℕ ↦
        poissonCountMassReal intensity eventCount * occupationMean) occupationMean := by
    simpa using (hasSum_poissonCountMassReal intensity).mul_right occupationMean
  have hCombined := hTransition.add hOccupation
  have hCombinedEq := hCombined.tsum_eq
  dsimp only [intensity, transitionMean, occupationMean] at hCombinedEq
  rw [NNReal.coe_mul] at hCombinedEq
  rw [← hCombinedEq]
  apply tsum_congr
  intro eventCount
  ring

end FiniteMarkovProcesses.Probability
