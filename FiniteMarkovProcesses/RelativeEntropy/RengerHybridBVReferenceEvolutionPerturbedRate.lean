/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVReferenceEvolutionPerturbedPath

/-!
# Dynamic-action control for reference-evolution perturbations

The unchanged reference evolution has observed directional flow equal to its generator-expected
flow, hence zero Poisson cost in every ordered channel.  Scalar joint convexity therefore bounds
the genuine perturbed hybrid-BV action by the target coefficient times the original action.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- `toNNReal` preserves a convex combination of two nonnegative real coordinates. -/
theorem realToNNReal_convexCombination
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

/-- Pointwise density coordinates of the genuine perturbation are the same convex combination
after passage to `NNReal`. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityAt
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (state : State)
    (hTargetNonnegative :
      0 ≤ rengerDirectionalFlowHybridBVDensityValue path.1 time state) :
    rengerDirectionalFlowHybridBVDensityAt
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time state =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVDensityAt path.1 time state +
        mixingWeight * rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time state := by
  unfold rengerDirectionalFlowHybridBVDensityAt
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityValue
    generator path mixingWeight hTimeNonnegative hTimeDuration state]
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
    generator path hTimeNonnegative hTimeDuration state]
  exact realToNNReal_convexCombination mixingWeight hMixingWeightLeOne
    hTargetNonnegative (show 0 ≤
        rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
          generator path time state by
      unfold rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
      exact ENNReal.toReal_nonneg)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Pointwise flow derivatives of the genuine perturbation are the same convex combination after
passage to `NNReal`. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivativeAt
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hTargetNonnegative :
      0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition)
    (hPerturbed :
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time transition =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
          generator path mixingWeight time transition.val.1 transition.val.2)
    (hReference :
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition =
        rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue
          generator path time transition.val.1 transition.val.2) :
    rengerDirectionalFlowHybridBVFlowDerivativeAt
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition +
        mixingWeight * rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
  rw [hPerturbed, hReference]
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue
  rw [dite_eq_left transition.property]
  simpa only using
    (realToNNReal_convexCombination mixingWeight hMixingWeightLeOne
      hTargetNonnegative
      (rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue_nonnegative
        generator path time transition.val.1 transition.val.2))

/-- The reference path's observed one-way derivative is exactly its generator-expected flow in
`NNReal`. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivativeAt_eq_expectedFlowAt
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hReference :
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition =
        rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue
          generator path time transition.val.1 transition.val.2) :
    rengerDirectionalFlowHybridBVFlowDerivativeAt
        (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
        time transition =
      rengerDirectionalFlowHybridBVExpectedFlowAt generator
        (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
        time transition := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
    rengerDirectionalFlowHybridBVExpectedFlowAt
    rengerDirectionalFlowHybridBVDensityAt
  rw [hReference]
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
    generator path hTimeNonnegative hTimeDuration transition.val.1]
  apply NNReal.eq
  simp only [NNReal.coe_mul]
  have hDensityNonnegative : 0 ≤
      rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
        generator path time transition.val.1 := by
    unfold rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
    exact ENNReal.toReal_nonneg
  rw [Real.coe_toNNReal _
      (mul_nonneg hDensityNonnegative
        (generator.rate transition.val.1 transition.val.2).coe_nonneg),
    Real.coe_toNNReal _ hDensityNonnegative]

/-- Generator-expected flow commutes with the pointwise density convex combination. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_expectedFlowAt
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hTargetNonnegative :
      0 ≤ rengerDirectionalFlowHybridBVDensityValue
        path.1 time transition.val.1) :
    rengerDirectionalFlowHybridBVExpectedFlowAt generator
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVExpectedFlowAt
            generator path.1 time transition +
        mixingWeight * rengerDirectionalFlowHybridBVExpectedFlowAt generator
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition := by
  unfold rengerDirectionalFlowHybridBVExpectedFlowAt
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityAt
    generator path mixingWeight hMixingWeightLeOne hTimeNonnegative hTimeDuration
      transition.val.1 hTargetNonnegative]
  ring

/-- The local perturbed directional-flow cost is bounded by the target coefficient times the
original local cost. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_localRate_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (hTargetDensityNonnegative :
      ∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue path.1 time state)
    (hTargetFlowNonnegative :
      ∀ transition,
        0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition)
    (hPerturbedFlow :
      ∀ transition,
        rengerDirectionalFlowHybridBVFlowDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
              generator path mixingWeight) time transition =
          rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
            generator path mixingWeight time transition.val.1 transition.val.2)
    (hReferenceFlow :
      ∀ transition,
        rengerDirectionalFlowHybridBVFlowDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
            time transition =
          rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue
            generator path time transition.val.1 transition.val.2) :
    rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time) ≤
      ((1 - mixingWeight : NNReal) : ENNReal) *
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path.1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time) := by
  unfold rengerDirectionalFlowLocalRateRaw
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro transition _hTransition
  have hFlow :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivativeAt
      generator path mixingWeight hMixingWeightLeOne time transition
      (hTargetFlowNonnegative transition) (hPerturbedFlow transition)
      (hReferenceFlow transition)
  have hExpected :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_expectedFlowAt
      generator path mixingWeight hMixingWeightLeOne hTimeNonnegative hTimeDuration
      transition (hTargetDensityNonnegative transition.val.1)
  have hReference :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivativeAt_eq_expectedFlowAt
      generator path hTimeNonnegative hTimeDuration transition
      (hReferenceFlow transition)
  rw [show rengerDirectionalFlowHybridBVDensityAt
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time transition.val.1 *
          generator.rate transition.val.1 transition.val.2 =
        rengerDirectionalFlowHybridBVExpectedFlowAt generator
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time transition by rfl,
    hFlow, hExpected]
  calc
    _ ≤ ((1 - mixingWeight : NNReal) : ENNReal) *
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition)
            (rengerDirectionalFlowHybridBVExpectedFlowAt
              generator path.1 time transition) +
        (mixingWeight : ENNReal) *
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVFlowDerivativeAt
              (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
              time transition)
            (rengerDirectionalFlowHybridBVExpectedFlowAt generator
              (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
              time transition) :=
      rengerExtendedPoissonRateCost_weighted_add_le
        (1 - mixingWeight) mixingWeight
        (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition)
        (rengerDirectionalFlowHybridBVExpectedFlowAt generator path.1 time transition)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition)
        (rengerDirectionalFlowHybridBVExpectedFlowAt generator
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          time transition)
    _ = _ := by
      rw [hReference, rengerExtendedPoissonRateCost_self, mul_zero, add_zero]
      rfl

/-- The complete dynamic action of the admissible perturbation is controlled by the target
coefficient. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_dynamicRate_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) ≤
      ((1 - mixingWeight : NNReal) : ENNReal) *
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 := by
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  have hPerturbedPath : perturbed.1 =
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path mixingWeight := rfl
  rw [← hPerturbedPath,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration perturbed.2,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration path.2]
  have hLocal :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt perturbed.1 time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt perturbed.1 time) ≤
          ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt path.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time) := by
    filter_upwards
      [path.2.densityNonnegativeAE, path.2.flowDerivativeNonnegativeAE,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivative_eq
          generator path mixingWeight,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivative_eq
          generator path,
        MeasureTheory.ae_restrict_mem measurableSet_Ioo]
      with time hDensity hFlow hPerturbed hReference hTime
    change rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
            generator path mixingWeight) time) ≤ _
    exact rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_localRate_le
      generator path mixingWeight hMixingWeightLeOne hTime.1.le hTime.2
      hDensity hFlow hPerturbed hReference
  calc
    _ ≤ ∫⁻ time,
          ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt path.1 time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
          ∂finiteOpenIntervalVolume duration := MeasureTheory.lintegral_mono_ae hLocal
    _ = _ := MeasureTheory.lintegral_const_mul'
      ((1 - mixingWeight : NNReal) : ENNReal) _ ENNReal.coe_ne_top

end

end FiniteMarkovProcesses.InformationTheory
