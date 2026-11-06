/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformization

/-!
# Stationary rewards of finite-state uniformized chains

This module defines the one-step probability update for the uniformized finite-state chain and
proves that a physical stationary distribution is a literal fixed point at every discrete event
index. It also identifies every self-event-insensitive transition reward with its physical
directed-rate reward after multiplication by the uniform clock.

These are the discrete stationary ingredients for a later Poisson-event expectation theorem.
They do not identify the virtual-event carrier with the physical jump-history law.

## Main Results

- `FiniteStateMarkovGenerator.uniformizedAdvancePMF_stationary`: one-step stationarity.
- `FiniteStateMarkovGenerator.uniformizedIteratedPMF_stationary`: stationarity at every virtual
  event index.
- `uniformizationRate_mul_uniformizedStationaryTransitionReward`: exact conversion from one-event
  rewards to physical per-time directed-rate rewards.
-/

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- Advance a state law by one uniformized virtual event. -/
noncomputable def uniformizedAdvancePMF
    (generator : FiniteStateMarkovGenerator State) (law : PMF State) : PMF State :=
  law.bind generator.uniformizedTransitionPMF

/-- A physical stationary PMF is a literal fixed point of one uniformized transition. -/
theorem uniformizedAdvancePMF_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    generator.uniformizedAdvancePMF stationary.pmf = stationary.pmf := by
  apply PMF.ext
  intro target
  rw [uniformizedAdvancePMF, PMF.bind_apply, tsum_fintype]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.sum_ne_top.mpr fun source _ ↦
      ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
    (PMF.apply_ne_top _ _)).mp
  rw [ENNReal.toReal_sum (fun source _ ↦
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul]
  simpa only [FiniteStateMarkovStationaryDistribution.pmf_apply, ENNReal.coe_toReal] using
    stationary.uniformizedTransition_stationary target

/-- State law after a fixed number of uniformized virtual events. -/
noncomputable def uniformizedIteratedPMF
    (generator : FiniteStateMarkovGenerator State) (eventCount : ℕ)
    (law : PMF State) : PMF State :=
  (generator.uniformizedAdvancePMF)^[eventCount] law

/-- A physical stationary PMF remains stationary at every virtual-event index. -/
theorem uniformizedIteratedPMF_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (eventCount : ℕ) :
    generator.uniformizedIteratedPMF eventCount stationary.pmf = stationary.pmf := by
  unfold uniformizedIteratedPMF
  exact Function.IsFixedPt.iterate
    (generator.uniformizedAdvancePMF_stationary stationary) eventCount

end FiniteStateMarkovGenerator

/-- Mean reward of one uniformized event under the stationary physical weights. -/
noncomputable def uniformizedStationaryTransitionReward
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) : ℝ :=
  ∑ source, ∑ target,
    (stationary.weight source : ℝ) *
      (generator.uniformizedTransitionPMF source target).toReal * reward source target

/-- Multiplying a self-event-insensitive stationary virtual-event reward by the uniform clock
recovers its exact physical directed-rate reward per unit source time. -/
theorem uniformizationRate_mul_uniformizedStationaryTransitionReward
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ)
    (hSelf : ∀ state, reward state state = 0) :
    (generator.uniformizationRate : ℝ) *
        uniformizedStationaryTransitionReward generator stationary reward =
      ∑ source, ∑ target,
        (stationary.weight source : ℝ) * (generator.rate source target : ℝ) *
          reward source target := by
  unfold uniformizedStationaryTransitionReward
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  by_cases hEq : source = target
  · subst target
    simp [hSelf, generator.rate_self]
  · rw [generator.uniformizedTransitionPMF_toReal_of_ne hEq]
    field_simp [generator.uniformizationRate_pos.ne']

end FiniteMarkovProcesses.Probability
