/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import FiniteMarkovProcesses.Probability.FiniteStateMarkovPoissonizedRewardExpectation
import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Stationary occupation under finite-state uniformization

This module constructs the state PMF at a fixed elapsed time by mixing the iterated uniformized
chain against the corresponding Poisson event count. A physical stationary PMF is unchanged at
every elapsed time. Consequently, integrating any state reward over a finite time interval gives
exactly duration times its stationary mean.

The construction provides exact one-time marginals and their occupation integral. A later timed
history law and Fubini theorem must identify this marginal integral with the expectation of the
pathwise complete-dwell observable.

## Main Results

- `FiniteStateMarkovGenerator.uniformizedPoissonStatePMF_stationary`: exact stationary one-time
  marginal under the uniformized Poisson semigroup.
- `intervalIntegral_uniformizedPoissonStateRewardExpectation_stationary`: exact integrated
  stationary occupation reward.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- State law at a fixed elapsed time, obtained by mixing the uniformized discrete chain against
the uniform-clock Poisson event count. -/
noncomputable def uniformizedPoissonStatePMF
    (generator : FiniteStateMarkovGenerator State) (elapsed : ℝ≥0)
    (law : PMF State) : PMF State :=
  (poissonCountPMF (generator.uniformizationRate * elapsed)).bind fun eventCount ↦
    generator.uniformizedIteratedPMF eventCount law

/-- A physical stationary PMF is unchanged by the uniformized Poisson semigroup at every elapsed
time. -/
theorem uniformizedPoissonStatePMF_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (elapsed : ℝ≥0) :
    generator.uniformizedPoissonStatePMF elapsed stationary.pmf = stationary.pmf := by
  unfold uniformizedPoissonStatePMF
  have hKernel :
      (fun eventCount ↦
        generator.uniformizedIteratedPMF eventCount stationary.pmf) =
        fun _ : ℕ ↦ stationary.pmf := by
    funext eventCount
    exact generator.uniformizedIteratedPMF_stationary stationary eventCount
  rw [hKernel, PMF.bind_const]

end FiniteStateMarkovGenerator

/-- Mean state reward under the fixed-time uniformized Poisson marginal. -/
noncomputable def uniformizedPoissonStateRewardExpectation
    (generator : FiniteStateMarkovGenerator State)
    (law : PMF State) (reward : State → ℝ) (elapsed : ℝ≥0) : ℝ :=
  ∑ state, (generator.uniformizedPoissonStatePMF elapsed law state).toReal * reward state

/-- At every elapsed time, the state-reward expectation from a physical stationary law is its
stationary mean. -/
theorem uniformizedPoissonStateRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → ℝ) (elapsed : ℝ≥0) :
    uniformizedPoissonStateRewardExpectation generator stationary.pmf reward elapsed =
      ∑ state, (stationary.weight state : ℝ) * reward state := by
  unfold uniformizedPoissonStateRewardExpectation
  rw [generator.uniformizedPoissonStatePMF_stationary stationary elapsed]
  apply Finset.sum_congr rfl
  intro state _
  rw [stationary.pmf_apply, ENNReal.coe_toReal]

/-- Integrating stationary one-time state rewards over a finite interval gives exactly duration
times the stationary mean. This is the marginal occupation identity; pathwise dwell identification
remains separate. -/
theorem intervalIntegral_uniformizedPoissonStateRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → ℝ) (duration : ℝ≥0) :
    ∫ elapsed : ℝ in 0..(duration : ℝ),
        uniformizedPoissonStateRewardExpectation generator stationary.pmf reward
          elapsed.toNNReal =
      (duration : ℝ) * ∑ state, (stationary.weight state : ℝ) * reward state := by
  simp_rw [uniformizedPoissonStateRewardExpectation_stationary]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

end FiniteMarkovProcesses.Probability
