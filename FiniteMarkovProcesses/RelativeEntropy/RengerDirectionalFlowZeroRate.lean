/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVCompleteRate

/-!
# Zero sets of complete hybrid-BV directional-flow rates

The extended Poisson cost vanishes exactly when actual and expected flow agree, including
zero-reference channels. Integrating this equality characterizes zero dynamic and complete rate
on the entire existing hybrid carrier. Infinite cost off admissibility remains visible.

## Main results

- `rengerExtendedPoissonRateCost_eq_zero_iff`: the exact one-channel zero set.
- `rengerDirectionalFlowHybridBVDynamicRate_eq_zero_iff`: full-carrier dynamic classification.
- `rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff`: the initial and dynamic zero sectors.

This classification does not assume or prove evolution uniqueness.

## References

The scalar equality case is the classical nonnegativity/equality law for relative entropy.
The directional-flow functional is due to M. Renger, *Flux large deviations of independent and
reacting particle systems, with implications for macroscopic fluctuation theory* (2018),
https://doi.org/10.1007/s10955-018-2083-0.
This module classifies the zero set of that functional on the specified hybrid carrier;
it does not prove a large-deviation principle or identify an initial cost independently.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

/-- Extended Poisson cost vanishes exactly at the reference flow, including either zero boundary. -/
@[simp]
theorem rengerExtendedPoissonRateCost_eq_zero_iff (flow expected : NNReal) :
    rengerExtendedPoissonRateCost flow expected = 0 ↔ flow = expected := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0 <;> simp [rengerExtendedPoissonRateCost, hFlow]
  by_cases hFlow : flow = 0
  · subst flow
    simp [rengerExtendedPoissonRateCost, hExpected, poissonRateDiscrimination, eq_comm]
  have hExpectedReal : 0 < (expected : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr hExpected
  have hFlowReal : 0 < (flow : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr hFlow
  rw [rengerExtendedPoissonRateCost_of_expected_pos flow
    (pos_iff_ne_zero.mpr hExpected), ENNReal.ofReal_eq_zero]
  constructor
  · intro hCost
    have hZero := le_antisymm hCost
      (poissonRateDiscrimination_nonneg hFlowReal.le hExpectedReal)
    exact_mod_cast (poissonRateDiscrimination_eq_zero_iff hFlowReal hExpectedReal).mp hZero
  · intro hEqual
    have hZero := (poissonRateDiscrimination_eq_zero_iff hFlowReal hExpectedReal).mpr
      (congrArg (fun value : NNReal ↦ (value : ℝ)) hEqual)
    exact hZero.le

variable {State : Type u} [Fintype State] [DecidableEq State] {duration : ℝ}

/-- The local extended rate is zero exactly when every ordered flow has its reference value. -/
theorem rengerDirectionalFlowLocalRateRaw_eq_zero_iff
    (generator : FiniteStateMarkovGenerator State)
    (density : State → NNReal)
    (flow : FiniteStateOrderedOffDiagonalTransition State → NNReal) :
    rengerDirectionalFlowLocalRateRaw generator density flow = 0 ↔
      ∀ transition, flow transition =
        density transition.val.1 * generator.rate transition.val.1 transition.val.2 := by
  simp [rengerDirectionalFlowLocalRateRaw, Finset.sum_eq_zero_iff]

omit [DecidableEq State] in
/-- Initial relative information vanishes exactly at the supplied stationary weight vector. -/
theorem rengerInvariantInitialCost_eq_zero_iff
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (density : FiniteStateProbabilityDensity State) :
    rengerInvariantInitialCost stationary density = 0 ↔ density.weight = stationary.weight := by
  simp [rengerInvariantInitialCost, Finset.sum_eq_zero_iff, funext_iff]

/-- Local ordered flow agrees almost everywhere with the occupied-source generator intensity.
This neither supplies admissibility nor identifies a representative off physical time. -/
def RengerDirectionalFlowHybridBVHasGeneratorFlow
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) : Prop :=
  ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ transition,
    rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition =
      rengerDirectionalFlowHybridBVDensityAt path time transition.val.1 *
        generator.rate transition.val.1 transition.val.2

/-- Zero dynamic rate over the full hybrid carrier requires both admissibility and local flow
agreement. Inadmissible paths have infinite rate and cannot enter the zero set. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_eq_zero_iff
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path = 0 ↔
      RengerDirectionalFlowHybridBVAdmissible path hDuration ∧
        RengerDirectionalFlowHybridBVHasGeneratorFlow generator path := by
  by_cases hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration
  · rw [rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration hPath, lintegral_eq_zero_iff'
        (aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path)]
    simp only [hPath, true_and, RengerDirectionalFlowHybridBVHasGeneratorFlow]
    exact eventually_congr (Eventually.of_forall fun time ↦
      rengerDirectionalFlowLocalRateRaw_eq_zero_iff generator
        (rengerDirectionalFlowHybridBVDensityAt path time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt path time))
  · rw [rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
      generator hDuration hPath]
    simp [hPath]

/-- Zero complete rate is exactly admissibility, zero supplied initial cost, and generator flow.
No finiteness or uniqueness hypothesis on the independently supplied initial rate is imposed. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = 0 ↔
      RengerDirectionalFlowHybridBVAdmissible path hDuration ∧
        rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path = 0 ∧
          RengerDirectionalFlowHybridBVHasGeneratorFlow generator path := by
  by_cases hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration
  · rw [rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
      generator hDuration initialRate hPath, add_eq_zero,
      rengerDirectionalFlowHybridBVDynamicRate_eq_zero_iff]
    simp [hPath]
  · rw [rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
      generator hDuration initialRate hPath]
    simp [hPath]

/-- On the admissible domain the nonnegative flow equality is equivalent to the raw real equation;
the clipping coercions therefore hide no density or flow defect. -/
theorem rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    RengerDirectionalFlowHybridBVHasGeneratorFlow generator path ↔
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ transition,
        rengerDirectionalFlowHybridBVFlowDerivative path time transition =
          rengerDirectionalFlowHybridBVDensityValue path time transition.val.1 *
            (generator.rate transition.val.1 transition.val.2 : ℝ) := by
  unfold RengerDirectionalFlowHybridBVHasGeneratorFlow
  apply eventually_congr
  filter_upwards [hPath.densityNonnegativeAE, hPath.flowDerivativeNonnegativeAE]
    with time hDensity hFlow
  apply forall_congr'
  intro transition
  rw [← NNReal.coe_inj, NNReal.coe_mul]
  simp only [rengerDirectionalFlowHybridBVFlowDerivativeAt,
    rengerDirectionalFlowHybridBVDensityAt,
    Real.coe_toNNReal _ (hFlow transition), Real.coe_toNNReal _ (hDensity transition.val.1)]

/-- An empty state space has no admissible probability-density path, so every complete rate
is infinite, independently of the initial cost. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_isEmpty
    [IsEmpty State]
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = ∞ := by
  apply rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
    generator hDuration initialRate
  intro hPath
  have hNormalized := hPath.initialDensityNormalized
  simp at hNormalized

/-- With at most one state, there are no ordered off-diagonal flow coordinates. The complete
zero set is exactly the admissible paths with zero initial cost. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_of_subsingleton
    [Subsingleton State]
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = 0 ↔
      RengerDirectionalFlowHybridBVAdmissible path hDuration ∧
        rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path = 0 := by
  have hFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator path := by
    apply Eventually.of_forall
    intro _time transition
    exact False.elim (transition.property (Subsingleton.elim _ _))
  rw [rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff]
  simp [hFlow]

end

end FiniteMarkovProcesses.InformationTheory
