/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpFluctuation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovStationaryAdditiveExpectation

/-!
# Relative entropy of stationary finite-state Markov trajectories

This module evaluates the complete finite-horizon trajectory relative entropy between two
finite-state Markov generators. The candidate begins in a positive stationary law, while the
reference begins in the same fixed law and need not preserve it. Under common directed support,
the finite real trajectory KL is exactly the observation duration times the full stationary
directed-rate relative entropy.

The proof retains jump-rate and escape/dwell sectors as separate additive history rewards before
combining their stationary expectations. No thermodynamic or historical-action interpretation is
attached to the generic identity.

## Main Results

- `finiteStateMarkovJumpLogAction_eq_additiveHistoryReward_sameStationaryInitial`: exact complete
  action decomposition with a common positive stationary initial law.
- `integral_finiteStateMarkovJumpLogAction_eq_stationaryRelativeEntropyRate`: exact expected
  complete action.
- `finiteStateMarkovTrajectoryKlDiv_toReal_eq_stationaryRelativeEntropyRate`: measure-level
  trajectory KL identity under common support.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open _root_.InformationTheory
open FiniteMarkovProcesses.Probability

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Complete stationary candidate-to-reference relative-entropy rate. Jump and dwell sectors
remain visibly separate in this definition. -/
noncomputable def finiteStateMarkovStationaryRelativeEntropyRate
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State) : ℝ :=
  (∑ source, ∑ target,
      (stationary.weight source : ℝ) * (generator.rate source target : ℝ) *
        finiteStateMarkovTransitionLogRatio generator referenceGenerator source target) +
    ∑ state,
      (stationary.weight state : ℝ) *
        finiteStateMarkovEscapeRateDifference generator referenceGenerator state

omit [DecidableEq State] in
/-- The complete stationary rate is equivalently the finite directed-rate relative-entropy sum.
The diagonal terms vanish under the generator laws but remain inside the common finite sum. -/
theorem finiteStateMarkovStationaryRelativeEntropyRate_eq_sum
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State) :
    finiteStateMarkovStationaryRelativeEntropyRate generator stationary referenceGenerator =
      ∑ source, ∑ target,
        (stationary.weight source : ℝ) *
          ((generator.rate source target : ℝ) *
              Real.log ((generator.rate source target : ℝ) /
                (referenceGenerator.rate source target : ℝ)) -
            (generator.rate source target : ℝ) +
            (referenceGenerator.rate source target : ℝ)) := by
  unfold finiteStateMarkovStationaryRelativeEntropyRate
    finiteStateMarkovTransitionLogRatio finiteStateMarkovEscapeRateDifference
    FiniteStateMarkovGenerator.escapeRate
  simp_rw [NNReal.coe_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  ring

omit [DecidableEq State] in
/-- With the same positive stationary initial law, the generic complete log action is exactly its
transition-plus-dwell additive reward. The initial-law sector is proved to vanish. -/
theorem finiteStateMarkovJumpLogAction_eq_additiveHistoryReward_sameStationaryInitial
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (history : FiniteJumpHistory State) :
    finiteStateMarkovJumpLogAction stationary.pmf stationary.pmf generator
        referenceGenerator duration history =
      finiteStateMarkovAdditiveHistoryReward
        (finiteStateMarkovTransitionLogRatio generator referenceGenerator)
        (finiteStateMarkovEscapeRateDifference generator referenceGenerator)
        duration history := by
  rcases history with ⟨eventCount, states, times⟩
  unfold finiteStateMarkovJumpLogAction finiteStateMarkovJumpSliceLogAction
    finiteStateMarkovAdditiveHistoryReward finiteStateMarkovAdditiveSliceReward
    finiteStateMarkovTransitionLogRatio finiteStateMarkovEscapeRateDifference
  simp only
  have hInitial : (stationary.pmf (states 0)).toReal ≠ 0 := by
    rw [stationary.pmf_apply, ENNReal.coe_toReal]
    exact_mod_cast (stationary.weight_pos (states 0)).ne'
  rw [div_self hInitial, Real.log_one, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- The complete stationary candidate-to-reference log action is integrable on the canonical
physical finite-history law. -/
theorem integrable_finiteStateMarkovJumpLogAction_sameStationaryInitial
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) :
    Integrable
      (finiteStateMarkovJumpLogAction stationary.pmf stationary.pmf generator
        referenceGenerator duration)
      (finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration) := by
  have hFunction :
      finiteStateMarkovJumpLogAction stationary.pmf stationary.pmf generator
          referenceGenerator duration =
        finiteStateMarkovAdditiveHistoryReward
          (finiteStateMarkovTransitionLogRatio generator referenceGenerator)
          (finiteStateMarkovEscapeRateDifference generator referenceGenerator)
          duration := by
    funext history
    exact finiteStateMarkovJumpLogAction_eq_additiveHistoryReward_sameStationaryInitial
      generator stationary referenceGenerator duration history
  rw [hFunction]
  exact integrable_finiteStateMarkovAdditiveHistoryReward_jumpDensity
    stationary.pmf generator
    (finiteStateMarkovTransitionLogRatio generator referenceGenerator)
    (finiteStateMarkovEscapeRateDifference generator referenceGenerator)
    duration (finiteStateMarkovTransitionLogRatio_self generator referenceGenerator)

/-- The expected complete log action is exactly duration times the full stationary directed-rate
relative entropy. -/
theorem integral_finiteStateMarkovJumpLogAction_eq_stationaryRelativeEntropyRate
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) :
    (∫ history : FiniteJumpHistory State,
        finiteStateMarkovJumpLogAction stationary.pmf stationary.pmf generator
          referenceGenerator duration history
      ∂finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration) =
      (duration : ℝ) *
        finiteStateMarkovStationaryRelativeEntropyRate
          generator stationary referenceGenerator := by
  simp_rw [finiteStateMarkovJumpLogAction_eq_additiveHistoryReward_sameStationaryInitial]
  exact integral_finiteStateMarkovAdditiveHistoryReward_eq_stationaryRate
    generator stationary
    (finiteStateMarkovTransitionLogRatio generator referenceGenerator)
    (finiteStateMarkovEscapeRateDifference generator referenceGenerator)
    duration (finiteStateMarkovTransitionLogRatio_self generator referenceGenerator)

/-- Under common directed support, the finite real complete-trajectory KL divergence is exactly
duration times the full stationary directed-rate relative entropy. The reference begins in the
same fixed candidate stationary law but need not preserve it. -/
theorem finiteStateMarkovTrajectoryKlDiv_toReal_eq_stationaryRelativeEntropyRate
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (referenceGenerator : FiniteStateMarkovGenerator State)
    (hSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (duration : ℝ≥0) :
    klDiv (finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration)
        (finiteStateMarkovJumpDensityMeasure stationary.pmf referenceGenerator duration) ≠ ⊤ ∧
      (klDiv (finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration)
        (finiteStateMarkovJumpDensityMeasure stationary.pmf referenceGenerator duration)).toReal =
        (duration : ℝ) *
          finiteStateMarkovStationaryRelativeEntropyRate
            generator stationary referenceGenerator := by
  have hIntegrable :=
    integrable_finiteStateMarkovJumpLogAction_sameStationaryInitial
      generator stationary referenceGenerator duration
  have hKl := integral_finiteStateMarkovJumpLogAction_eq_klDiv
    (initial := stationary.pmf) (referenceInitial := stationary.pmf)
    (generator := generator) (referenceGenerator := referenceGenerator)
    (fun _ ↦ Iff.rfl) hSupport duration
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      stationary.pmf generator duration duration.coe_nonneg)
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      stationary.pmf referenceGenerator duration duration.coe_nonneg)
    hIntegrable
  refine ⟨hKl.1, hKl.2.symm.trans ?_⟩
  exact integral_finiteStateMarkovJumpLogAction_eq_stationaryRelativeEntropyRate
    generator stationary referenceGenerator duration

end FiniteMarkovProcesses.InformationTheory
