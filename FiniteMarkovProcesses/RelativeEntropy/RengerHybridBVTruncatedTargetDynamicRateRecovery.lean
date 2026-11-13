/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTruncatedTargetFlowRecovery

/-!
# Dynamic-rate recovery from truncated Renger target flows

The finite ordered-transition family lifts channelwise dominated convergence to the complete
hybrid directional-flow action.  The reference expected flow remains formed from the unchanged
target density, while only the target flow is truncated.

This is target-side action recovery.  It does not assert that the truncated chart is the mean of
a physical jump law or supply a Radon--Nikodym/Girsanov identity.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Complete truncated target-flow action, summed over the finite ordered-transition family. -/
noncomputable def rengerDirectionalFlowHybridBVTruncatedTargetDynamicRate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (cutoff : ℕ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ∫⁻ time,
      rengerExtendedPoissonRateCost
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
          path cutoff time transition.1.1 transition.1.2)
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path time transition.1.1 transition.1.2)
      ∂finiteOpenIntervalVolume duration

/-- On the representation domain, the dynamic action is the finite sum of the measurable-version
target channel costs. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_eq_sum_measurableTargetRateCostIntegrals
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ∫⁻ time,
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time transition.1.1 transition.1.2)
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time transition.1.1 transition.1.2)
          ∂finiteOpenIntervalVolume duration := by
  rw [rengerDirectionalFlowHybridBVDynamicRate_eq_sum_channelRateCostIntegrals
    generator hDuration path]
  apply Finset.sum_congr rfl
  intro transition _hTransition
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq path.1] with
      time hDensityVersion
  simp [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt, transition.2,
    rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt,
    rengerDirectionalFlowHybridBVExpectedFlowAt, hDensityVersion]

/-- The complete truncated target-flow action converges to the exact hybrid dynamic action. -/
theorem tendsto_rengerDirectionalFlowHybridBVTruncatedTargetDynamicRate_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤) :
    Tendsto
      (rengerDirectionalFlowHybridBVTruncatedTargetDynamicRate generator path.1)
      atTop
      (nhds (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1)) := by
  rw [rengerDirectionalFlowHybridBVDynamicRate_eq_sum_measurableTargetRateCostIntegrals
    generator hDuration path]
  unfold rengerDirectionalFlowHybridBVTruncatedTargetDynamicRate
  apply tendsto_finsetSum Finset.univ
  intro transition _hTransition
  exact tendsto_lintegral_rengerExtendedPoissonRateCost_truncatedTargetFlow_atTop
    generator hDuration path hDynamicRate transition.2

/-- Total physical-time target-flow mass removed by one finite cutoff, summed over every ordered
transition. -/
noncomputable def rengerDirectionalFlowHybridBVTruncatedTargetTotalFlowError
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (cutoff : ℕ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path time transition.1.1 transition.1.2 : ENNReal) -
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
          path cutoff time transition.1.1 transition.1.2 : ENNReal)
      ∂finiteOpenIntervalVolume duration

/-- Finite action forces the total ordered-flow mass removed by the cutoff to vanish as the
cutoff diverges. -/
theorem tendsto_rengerDirectionalFlowHybridBVTruncatedTargetTotalFlowError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤) :
    Tendsto
      (rengerDirectionalFlowHybridBVTruncatedTargetTotalFlowError path.1)
      atTop (nhds 0) := by
  unfold rengerDirectionalFlowHybridBVTruncatedTargetTotalFlowError
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ fun transition _hTransition ↦
      tendsto_lintegral_rengerDirectionalFlowHybridBVTruncatedTargetFlowError_atTop
        generator hDuration path hDynamicRate transition.2)

end

end FiniteMarkovProcesses.InformationTheory
