/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistory
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedWordExpectation

/-!
# Complete-word occupation rewards for finite-state uniformized chains

This module evaluates linearly weighted state rewards by literal summation over complete
uniformized state words. Under a stationary initial law, every coefficient sees the same state
mean. Consequently, dwell-time coefficients telescope to the observation horizon and give
exactly duration times the stationary reward.

This is the discrete word component of a timed-history occupation integral. It neither deletes
virtual self-events nor identifies the virtual history law with a physical jump law.

## Main Results

- `finiteStateUniformizedWordStateRewardExpectation_stationary`: a general stationary weighted
  state-word identity.
- `finiteStateUniformizedWordDwellRewardExpectation_stationary`: exact pathwise-dwell coefficient
  collapse to duration times the stationary mean.
-/

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Linearly weighted state reward along a source-anchored future-state word. -/
noncomputable def finiteStateUniformizedStateRewardSum
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 1) → ℝ)
    (source : State) (future : Fin eventCount → State) : ℝ :=
  let states : Fin (eventCount + 1) → State := Fin.cons source future
  ∑ index : Fin (eventCount + 1), coefficients index * reward (states index)

/-- Conditional fixed-count expectation of a linearly weighted state reward. -/
noncomputable def finiteStateUniformizedConditionalStateRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (reward : State → ℝ)
    {eventCount : ℕ} (coefficients : Fin (eventCount + 1) → ℝ)
    (source : State) : ℝ :=
  ∑ future : Fin eventCount → State,
    finiteStateUniformizedContinuationWeight generator source future *
      finiteStateUniformizedStateRewardSum reward coefficients source future

/-- Fixed-count expectation of a linearly weighted state reward over complete state words. -/
noncomputable def finiteStateUniformizedWordStateRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 1) → ℝ) : ℝ :=
  ∑ source,
    (law source).toReal *
      finiteStateUniformizedConditionalStateRewardExpectation
        generator reward coefficients source

/-- Mean of a state reward under a finite PMF. -/
noncomputable def finiteStatePMFRewardExpectation
    (law : PMF State) (reward : State → ℝ) : ℝ :=
  ∑ state, (law state).toReal * reward state

omit [DecidableEq State] in
/-- The PMF reward expectation of a stationary law is its stationary-weight mean. -/
theorem finiteStatePMFRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → ℝ) :
    finiteStatePMFRewardExpectation stationary.pmf reward =
      ∑ state, (stationary.weight state : ℝ) * reward state := by
  unfold finiteStatePMFRewardExpectation
  apply Finset.sum_congr rfl
  intro state _
  rw [stationary.pmf_apply, ENNReal.coe_toReal]

omit [Fintype State] [DecidableEq State] in
/-- A nonempty state-word reward is its head reward plus its weighted tail reward. -/
theorem finiteStateUniformizedStateRewardSum_cons
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 2) → ℝ)
    (source target : State) (future : Fin eventCount → State) :
    finiteStateUniformizedStateRewardSum reward coefficients source
        (Fin.cons target future) =
      coefficients 0 * reward source +
        finiteStateUniformizedStateRewardSum reward
          (fun index ↦ coefficients index.succ) target future := by
  unfold finiteStateUniformizedStateRewardSum
  rw [Fin.sum_univ_succ]
  congr 1

private theorem sum_continuationWeight_mul_stateReward_add
    (generator : FiniteStateMarkovGenerator State) (reward : State → ℝ)
    {eventCount : ℕ} (coefficients : Fin (eventCount + 1) → ℝ)
    (headReward : ℝ) (target : State) :
    (∑ future : Fin eventCount → State,
      finiteStateUniformizedContinuationWeight generator target future *
        (headReward +
          finiteStateUniformizedStateRewardSum reward coefficients target future)) =
      headReward +
        finiteStateUniformizedConditionalStateRewardExpectation
          generator reward coefficients target := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [sum_finiteStateUniformizedContinuationWeight, one_mul]
  rfl

/-- Conditional state-reward word expectation satisfies the Markov first-step recursion. -/
theorem finiteStateUniformizedConditionalStateRewardExpectation_succ
    (generator : FiniteStateMarkovGenerator State) (reward : State → ℝ)
    {eventCount : ℕ} (coefficients : Fin (eventCount + 2) → ℝ)
    (source : State) :
    finiteStateUniformizedConditionalStateRewardExpectation
        generator reward coefficients source =
      coefficients 0 * reward source +
        ∑ target,
          (generator.uniformizedTransitionPMF source target).toReal *
            finiteStateUniformizedConditionalStateRewardExpectation generator reward
              (fun index ↦ coefficients index.succ) target := by
  unfold finiteStateUniformizedConditionalStateRewardExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ target : State, ∑ future : Fin eventCount → State,
    finiteStateUniformizedContinuationWeight generator source (Fin.cons target future) *
      finiteStateUniformizedStateRewardSum reward coefficients source
        (Fin.cons target future)) = _
  simp_rw [finiteStateUniformizedContinuationWeight_cons,
    finiteStateUniformizedStateRewardSum_cons, mul_assoc]
  calc
    _ = ∑ target : State,
        (generator.uniformizedTransitionPMF source target).toReal *
          (coefficients 0 * reward source +
            finiteStateUniformizedConditionalStateRewardExpectation generator reward
              (fun index ↦ coefficients index.succ) target) := by
      apply Finset.sum_congr rfl
      intro target _
      rw [← Finset.mul_sum]
      rw [sum_continuationWeight_mul_stateReward_add]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      rw [PMF.sum_toReal, one_mul]
      rfl

/-- Complete-word state-reward expectation satisfies the law-level first-step recursion. -/
theorem finiteStateUniformizedWordStateRewardExpectation_succ
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 2) → ℝ) :
    finiteStateUniformizedWordStateRewardExpectation
        generator law reward coefficients =
      coefficients 0 * finiteStatePMFRewardExpectation law reward +
        finiteStateUniformizedWordStateRewardExpectation generator
          (generator.uniformizedAdvancePMF law) reward
          (fun index ↦ coefficients index.succ) := by
  unfold finiteStateUniformizedWordStateRewardExpectation
    finiteStatePMFRewardExpectation
  simp_rw [finiteStateUniformizedConditionalStateRewardExpectation_succ]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  · simp_rw [Finset.mul_sum]
    simp_rw [← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro target _
    rw [← Finset.sum_mul]
    rw [← finiteStateUniformizedAdvancePMF_toReal]

/-- A zero-event state word evaluates only its initial-state reward. -/
theorem finiteStateUniformizedWordStateRewardExpectation_zero
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → ℝ) (coefficients : Fin 1 → ℝ) :
    finiteStateUniformizedWordStateRewardExpectation
        generator law reward coefficients =
      coefficients 0 * finiteStatePMFRewardExpectation law reward := by
  unfold finiteStateUniformizedWordStateRewardExpectation
    finiteStateUniformizedConditionalStateRewardExpectation
    finiteStateUniformizedStateRewardSum finiteStatePMFRewardExpectation
  simp only [Fintype.sum_unique, finiteStateUniformizedContinuationWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state _
  simp
  ring

/-- At stationarity, every linearly weighted state-word reward is its coefficient sum times the
stationary mean. -/
theorem finiteStateUniformizedWordStateRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → ℝ) {eventCount : ℕ}
    (coefficients : Fin (eventCount + 1) → ℝ) :
    finiteStateUniformizedWordStateRewardExpectation
        generator stationary.pmf reward coefficients =
      (∑ index, coefficients index) *
        ∑ state, (stationary.weight state : ℝ) * reward state := by
  induction eventCount with
  | zero =>
      rw [finiteStateUniformizedWordStateRewardExpectation_zero,
        finiteStatePMFRewardExpectation_stationary,
        Fin.sum_univ_one]
  | succ eventCount inductionHypothesis =>
      rw [finiteStateUniformizedWordStateRewardExpectation_succ,
        generator.uniformizedAdvancePMF_stationary stationary,
        inductionHypothesis,
        finiteStatePMFRewardExpectation_stationary]
      rw [Fin.sum_univ_succ coefficients]
      ring

/-- Stationary dwell-weighted state rewards collapse to duration times the stationary mean. -/
theorem finiteStateUniformizedWordDwellRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → ℝ) {eventCount : ℕ} (T : ℝ)
    (times : Fin eventCount → ℝ) :
    finiteStateUniformizedWordStateRewardExpectation generator stationary.pmf reward
        (FiniteJumpHistory.dwellTimeVector T times) =
      T * ∑ state, (stationary.weight state : ℝ) * reward state := by
  rw [finiteStateUniformizedWordStateRewardExpectation_stationary,
    FiniteJumpHistory.sum_dwellTimeVector]

end FiniteMarkovProcesses.Probability
