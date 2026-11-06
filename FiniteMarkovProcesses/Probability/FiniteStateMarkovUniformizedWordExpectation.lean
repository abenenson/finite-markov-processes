/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedRewardExpectation

/-!
# Complete-word expectations for finite-state uniformized chains

This module expands the dynamic-programming expectation of an additive transition reward into
the literal finite sum over complete state words. It also proves that the conditional future-word
weights have total mass one.

The word formula is the discrete component of fixed-count uniformized-history integration. It
does not identify virtual self-events with physical jumps.

## Main Results

- `sum_finiteStateUniformizedContinuationWeight`: conditional word weights have total mass one.
- `finiteStateUniformizedWordTransitionRewardExpectation_eq_cumulative`: literal word summation
  agrees with the existing dynamic-programming expectation.
- `finiteStateUniformizedWordTransitionRewardExpectation_stationary`: stationary word rewards
  grow exactly linearly in the event count.
-/

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Weight of one future-state word conditional on its source state. -/
noncomputable def finiteStateUniformizedContinuationWeight
    (generator : FiniteStateMarkovGenerator State) (source : State)
    {eventCount : ℕ} (future : Fin eventCount → State) : ℝ :=
  let states : Fin (eventCount + 1) → State := Fin.cons source future
  ∏ index : Fin eventCount,
    (generator.uniformizedTransitionPMF
      (states index.castSucc) (states index.succ)).toReal

/-- Sum of a transition reward along a source-anchored future-state word. -/
noncomputable def finiteStateUniformizedTransitionRewardSum
    (reward : State → State → ℝ) {eventCount : ℕ}
    (source : State) (future : Fin eventCount → State) : ℝ :=
  let states : Fin (eventCount + 1) → State := Fin.cons source future
  ∑ index : Fin eventCount, reward (states index.castSucc) (states index.succ)

/-- Conditional fixed-count expectation of an additive transition reward over complete words. -/
noncomputable def finiteStateUniformizedConditionalTransitionRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (reward : State → State → ℝ)
    (source : State) (eventCount : ℕ) : ℝ :=
  ∑ future : Fin eventCount → State,
    finiteStateUniformizedContinuationWeight generator source future *
      finiteStateUniformizedTransitionRewardSum reward source future

/-- Fixed-count expectation of an additive transition reward over complete state words. -/
noncomputable def finiteStateUniformizedWordTransitionRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → State → ℝ) (eventCount : ℕ) : ℝ :=
  ∑ source,
    (law source).toReal *
      finiteStateUniformizedConditionalTransitionRewardExpectation
        generator reward source eventCount

/-- A nonempty conditional word weight factors into its first transition and its tail. -/
theorem finiteStateUniformizedContinuationWeight_cons
    (generator : FiniteStateMarkovGenerator State) (source target : State)
    {eventCount : ℕ} (future : Fin eventCount → State) :
    finiteStateUniformizedContinuationWeight generator source (Fin.cons target future) =
      (generator.uniformizedTransitionPMF source target).toReal *
        finiteStateUniformizedContinuationWeight generator target future := by
  unfold finiteStateUniformizedContinuationWeight
  rw [Fin.prod_univ_succ]
  congr 1

omit [Fintype State] [DecidableEq State] in
/-- A nonempty word reward is its first transition reward plus its tail reward. -/
theorem finiteStateUniformizedTransitionRewardSum_cons
    (reward : State → State → ℝ) (source target : State)
    {eventCount : ℕ} (future : Fin eventCount → State) :
    finiteStateUniformizedTransitionRewardSum reward source (Fin.cons target future) =
      reward source target +
        finiteStateUniformizedTransitionRewardSum reward target future := by
  unfold finiteStateUniformizedTransitionRewardSum
  rw [Fin.sum_univ_succ]
  congr 1

omit [DecidableEq State] in
/-- The real-valued masses of a finite PMF sum to one. -/
theorem PMF.sum_toReal (law : PMF State) :
    ∑ state, (law state).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun state _ => law.apply_ne_top state)]
  rw [show ∑ state, law state = 1 by
    simpa only [tsum_fintype] using law.tsum_coe]
  simp

/-- Conditional future-word weights have total mass one at every event count. -/
theorem sum_finiteStateUniformizedContinuationWeight
    (generator : FiniteStateMarkovGenerator State) (source : State)
    (eventCount : ℕ) :
    ∑ future : Fin eventCount → State,
      finiteStateUniformizedContinuationWeight generator source future = 1 := by
  induction eventCount generalizing source with
  | zero =>
      rw [Fintype.sum_unique]
      unfold finiteStateUniformizedContinuationWeight
      simp
  | succ eventCount inductionHypothesis =>
      rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
      rw [Fintype.sum_prod_type]
      change (∑ target : State, ∑ future : Fin eventCount → State,
        finiteStateUniformizedContinuationWeight generator source
          (Fin.cons target future)) = 1
      simp_rw [finiteStateUniformizedContinuationWeight_cons]
      rw [show (∑ target : State, ∑ future : Fin eventCount → State,
          (generator.uniformizedTransitionPMF source target).toReal *
            finiteStateUniformizedContinuationWeight generator target future) =
        ∑ target : State,
          (generator.uniformizedTransitionPMF source target).toReal *
            ∑ future : Fin eventCount → State,
              finiteStateUniformizedContinuationWeight generator target future by
        apply Finset.sum_congr rfl
        intro target _
        simpa using (Finset.mul_sum Finset.univ
          (fun future : Fin eventCount → State =>
            finiteStateUniformizedContinuationWeight generator target future)
          (generator.uniformizedTransitionPMF source target).toReal).symm]
      simp_rw [inductionHypothesis, mul_one]
      exact PMF.sum_toReal (generator.uniformizedTransitionPMF source)

private theorem sum_continuationWeight_mul_reward_add
    (generator : FiniteStateMarkovGenerator State) (reward : State → State → ℝ)
    (source target : State) (eventCount : ℕ) :
    (∑ future : Fin eventCount → State,
      finiteStateUniformizedContinuationWeight generator target future *
        (reward source target +
          finiteStateUniformizedTransitionRewardSum reward target future)) =
      reward source target +
        finiteStateUniformizedConditionalTransitionRewardExpectation
          generator reward target eventCount := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [sum_finiteStateUniformizedContinuationWeight, one_mul]
  rfl

/-- Conditional transition-reward word expectation satisfies the Markov first-step recursion. -/
theorem finiteStateUniformizedConditionalTransitionRewardExpectation_succ
    (generator : FiniteStateMarkovGenerator State) (reward : State → State → ℝ)
    (source : State) (eventCount : ℕ) :
    finiteStateUniformizedConditionalTransitionRewardExpectation
        generator reward source (eventCount + 1) =
      ∑ target,
        (generator.uniformizedTransitionPMF source target).toReal *
          (reward source target +
            finiteStateUniformizedConditionalTransitionRewardExpectation
              generator reward target eventCount) := by
  unfold finiteStateUniformizedConditionalTransitionRewardExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ target : State, ∑ future : Fin eventCount → State,
    finiteStateUniformizedContinuationWeight generator source (Fin.cons target future) *
      finiteStateUniformizedTransitionRewardSum reward source
        (Fin.cons target future)) = _
  simp_rw [finiteStateUniformizedContinuationWeight_cons,
    finiteStateUniformizedTransitionRewardSum_cons, mul_assoc]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.mul_sum]
  rw [sum_continuationWeight_mul_reward_add]
  rfl

/-- The real mass of the advanced PMF is the finite transition convolution. -/
theorem finiteStateUniformizedAdvancePMF_toReal
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (target : State) :
    (generator.uniformizedAdvancePMF law target).toReal =
      ∑ source,
        (law source).toReal *
          (generator.uniformizedTransitionPMF source target).toReal := by
  rw [FiniteStateMarkovGenerator.uniformizedAdvancePMF, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro source _
    exact ENNReal.mul_ne_top (law.apply_ne_top source)
      ((generator.uniformizedTransitionPMF source).apply_ne_top target)

/-- Complete-word transition-reward expectation satisfies the law-level first-step recursion. -/
theorem finiteStateUniformizedWordTransitionRewardExpectation_succ
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → State → ℝ) (eventCount : ℕ) :
    finiteStateUniformizedWordTransitionRewardExpectation
        generator law reward (eventCount + 1) =
      uniformizedTransitionRewardExpectation generator law reward +
        finiteStateUniformizedWordTransitionRewardExpectation generator
          (generator.uniformizedAdvancePMF law) reward eventCount := by
  unfold finiteStateUniformizedWordTransitionRewardExpectation
    uniformizedTransitionRewardExpectation
  simp_rw [finiteStateUniformizedConditionalTransitionRewardExpectation_succ]
  simp_rw [Finset.mul_sum]
  simp_rw [← mul_assoc, mul_add]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.sum_mul]
  rw [← finiteStateUniformizedAdvancePMF_toReal]

/-- Literal complete-word summation agrees with the dynamic-programming expectation. -/
theorem finiteStateUniformizedWordTransitionRewardExpectation_eq_cumulative
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → State → ℝ) (eventCount : ℕ) :
    finiteStateUniformizedWordTransitionRewardExpectation
        generator law reward eventCount =
      uniformizedCumulativeTransitionRewardExpectation
        generator law reward eventCount := by
  induction eventCount generalizing law with
  | zero =>
      unfold finiteStateUniformizedWordTransitionRewardExpectation
        finiteStateUniformizedConditionalTransitionRewardExpectation
        finiteStateUniformizedTransitionRewardSum
        uniformizedCumulativeTransitionRewardExpectation
      simp
  | succ eventCount inductionHypothesis =>
      rw [finiteStateUniformizedWordTransitionRewardExpectation_succ,
        uniformizedCumulativeTransitionRewardExpectation,
        inductionHypothesis]

/-- At stationarity, direct state-word summation gives exact linear transition-reward growth. -/
theorem finiteStateUniformizedWordTransitionRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) (eventCount : ℕ) :
    finiteStateUniformizedWordTransitionRewardExpectation
        generator stationary.pmf reward eventCount =
      (eventCount : ℝ) *
        uniformizedStationaryTransitionReward generator stationary reward := by
  rw [finiteStateUniformizedWordTransitionRewardExpectation_eq_cumulative,
    uniformizedCumulativeTransitionRewardExpectation_stationary]

end FiniteMarkovProcesses.Probability
