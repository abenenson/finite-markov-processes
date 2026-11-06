/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVConvexCombinationRepresentationPath
import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual

/-!
# Dynamic-action convexity on the Renger representation domain

Extended Poisson joint convexity lifts through every ordered channel and the physical-time
integral.  Consequently the exact dynamic hybrid-BV action is convex on its representation
domain, including all zero-rate boundary sectors.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- `toNNReal` preserves a convex combination of two nonnegative real coordinates. -/
theorem realToNNReal_nonnegativeConvexCombination
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {first second : ℝ} (hFirst : 0 ≤ first) (hSecond : 0 ≤ second) :
    Real.toNNReal
        ((1 - (mixingWeight : ℝ)) * first + (mixingWeight : ℝ) * second) =
      (1 - mixingWeight) * Real.toNNReal first +
        mixingWeight * Real.toNNReal second := by
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sub hMixingWeightLeOne,
    NNReal.coe_one, Real.coe_toNNReal _ hFirst, Real.coe_toNNReal _ hSecond]
  rw [Real.coe_toNNReal]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hMixingWeightLeOne)) hFirst)
    (mul_nonneg mixingWeight.coe_nonneg hSecond)

/-- Recovered initial density coordinates combine exactly in the finite simplex. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath_initialDensity
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    (state : State) :
    rengerDirectionalFlowHybridBVInitialDensity
        (rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath
          first second mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne).1 state =
      (1 - mixingWeight) * rengerDirectionalFlowHybridBVInitialDensity first.1 state +
        mixingWeight * rengerDirectionalFlowHybridBVInitialDensity second.1 state := by
  unfold rengerDirectionalFlowHybridBVInitialDensity
  change Real.toNNReal
      ((rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight).initialTrace (Sum.inl state)) = _
  unfold rengerDirectionalFlowHybridBVConvexCombinationPath
  rw [FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact realToNNReal_nonnegativeConvexCombination mixingWeight hMixingWeightLeOne
    (first.2.initialDensityNonnegative state) (second.2.initialDensityNonnegative state)

/-- The exact recovered initial simplex point has the same coordinatewise convex formula. -/
theorem
rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath_initialProbabilityDensity_weight
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    (state : State) :
    (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
      (rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath
        first second mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne)).weight state =
      (1 - mixingWeight) *
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity first).weight state +
        mixingWeight *
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity second).weight state := by
  exact rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath_initialDensity
    first second mixingWeight hMixingWeightLeOne state

/-- Nonnegative density coordinates of a convex path combine in `NNReal`. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_densityAt
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State)
    (hFirst : 0 ≤ rengerDirectionalFlowHybridBVDensityValue first.1 time state)
    (hSecond : 0 ≤ rengerDirectionalFlowHybridBVDensityValue second.1 time state) :
    rengerDirectionalFlowHybridBVDensityAt
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) time state =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVDensityAt first.1 time state +
        mixingWeight *
          rengerDirectionalFlowHybridBVDensityAt second.1 time state := by
  unfold rengerDirectionalFlowHybridBVDensityAt
  rw [rengerDirectionalFlowHybridBVConvexCombinationPath_densityValue
    first second mixingWeight hTime state]
  exact realToNNReal_nonnegativeConvexCombination
    mixingWeight hMixingWeightLeOne hFirst hSecond

/-- Nonnegative flow derivatives of a convex path combine in `NNReal`. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivativeAt
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFirst : 0 ≤ rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition)
    (hSecond : 0 ≤ rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition)
    (hCombined :
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time transition =
        (1 - (mixingWeight : ℝ)) *
            rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition +
          (mixingWeight : ℝ) *
            rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition) :
    rengerDirectionalFlowHybridBVFlowDerivativeAt
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time transition +
        mixingWeight *
          rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time transition := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
  rw [hCombined]
  exact realToNNReal_nonnegativeConvexCombination
    mixingWeight hMixingWeightLeOne hFirst hSecond

/-- Generator-expected flow commutes with a nonnegative density convex combination. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_expectedFlowAt
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTime : time ∈ Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFirst : 0 ≤
      rengerDirectionalFlowHybridBVDensityValue first.1 time transition.val.1)
    (hSecond : 0 ≤
      rengerDirectionalFlowHybridBVDensityValue second.1 time transition.val.1) :
    rengerDirectionalFlowHybridBVExpectedFlowAt generator
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVExpectedFlowAt generator first.1 time transition +
        mixingWeight *
          rengerDirectionalFlowHybridBVExpectedFlowAt generator second.1 time transition := by
  unfold rengerDirectionalFlowHybridBVExpectedFlowAt
  rw [rengerDirectionalFlowHybridBVConvexCombinationPath_densityAt
    first second mixingWeight hMixingWeightLeOne hTime transition.val.1 hFirst hSecond]
  ring

/-- Pointwise local directional-flow action is jointly convex along representation paths. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_localRate_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTime : time ∈ Ico 0 duration)
    (hFirstDensity : ∀ state,
      0 ≤ rengerDirectionalFlowHybridBVDensityValue first.1 time state)
    (hSecondDensity : ∀ state,
      0 ≤ rengerDirectionalFlowHybridBVDensityValue second.1 time state)
    (hFirstFlow : ∀ transition,
      0 ≤ rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition)
    (hSecondFlow : ∀ transition,
      0 ≤ rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition)
    (hCombinedFlow : ∀ transition,
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time transition =
        (1 - (mixingWeight : ℝ)) *
            rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition +
          (mixingWeight : ℝ) *
            rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition) :
    rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time) ≤
      ((1 - mixingWeight : NNReal) : ENNReal) *
          rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt first.1 time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time) +
        (mixingWeight : ENNReal) *
          rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt second.1 time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time) := by
  unfold rengerDirectionalFlowLocalRateRaw
  calc
    _ ≤ ∑ transition, (
        ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time transition)
              (rengerDirectionalFlowHybridBVExpectedFlowAt
                generator first.1 time transition) +
          (mixingWeight : ENNReal) *
            rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time transition)
              (rengerDirectionalFlowHybridBVExpectedFlowAt
                generator second.1 time transition)) := by
      apply Finset.sum_le_sum
      intro transition _hTransition
      rw [show rengerDirectionalFlowHybridBVDensityAt
            (rengerDirectionalFlowHybridBVConvexCombinationPath
              first second mixingWeight) time transition.val.1 *
            generator.rate transition.val.1 transition.val.2 =
          rengerDirectionalFlowHybridBVExpectedFlowAt generator
            (rengerDirectionalFlowHybridBVConvexCombinationPath
              first second mixingWeight) time transition by rfl,
        rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivativeAt
          first second mixingWeight hMixingWeightLeOne time transition
          (hFirstFlow transition) (hSecondFlow transition) (hCombinedFlow transition),
        rengerDirectionalFlowHybridBVConvexCombinationPath_expectedFlowAt
          generator first second mixingWeight hMixingWeightLeOne hTime transition
          (hFirstDensity transition.val.1) (hSecondDensity transition.val.1)]
      exact rengerExtendedPoissonRateCost_weighted_add_le
        (1 - mixingWeight) mixingWeight
        (rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time transition)
        (rengerDirectionalFlowHybridBVExpectedFlowAt generator first.1 time transition)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time transition)
        (rengerDirectionalFlowHybridBVExpectedFlowAt generator second.1 time transition)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- The complete dynamic action is convex on the exact representation domain. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_dynamicRate_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) ≤
      ((1 - mixingWeight : NNReal) : ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration first.1 +
        (mixingWeight : ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration second.1 := by
  let combined := rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath
    first second mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  change rengerDirectionalFlowHybridBVDynamicRate generator hDuration combined.1 ≤ _
  rw [rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration combined.2,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration first.2,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration second.2]
  have hLocal : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt combined.1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt combined.1 time) ≤
        ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt first.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time) +
          (mixingWeight : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt second.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time) := by
    filter_upwards [first.2.densityNonnegativeAE, second.2.densityNonnegativeAE,
      first.2.flowDerivativeNonnegativeAE, second.2.flowDerivativeNonnegativeAE,
      ae_rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivative_eq
        first second mixingWeight,
      MeasureTheory.ae_restrict_mem measurableSet_Ioo]
      with time hFirstDensity hSecondDensity hFirstFlow hSecondFlow hCombinedFlow hTime
    change rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time) ≤ _
    exact rengerDirectionalFlowHybridBVConvexCombinationPath_localRate_le
      generator first second mixingWeight hMixingWeightLeOne
      ⟨hTime.1.le, hTime.2⟩ hFirstDensity hSecondDensity hFirstFlow hSecondFlow hCombinedFlow
  calc
    _ ≤ ∫⁻ time,
        (((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt first.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt first.1 time) +
          (mixingWeight : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt second.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt second.1 time))
        ∂finiteOpenIntervalVolume duration := MeasureTheory.lintegral_mono_ae hLocal
    _ = _ := by
      rw [MeasureTheory.lintegral_add_left'
        ((aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator first.1).const_mul _),
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]

end

end FiniteMarkovProcesses.InformationTheory
