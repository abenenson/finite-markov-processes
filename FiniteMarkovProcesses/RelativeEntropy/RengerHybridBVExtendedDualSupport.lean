/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.PoissonMeasureContinuousDualSingularity
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual
import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasurePositiveClosure

/-!
# Extended-support Renger hybrid-BV duality

This module decomposes the topological Renger dual on the total hybrid-BV carrier before any
absolute-continuity assumption.  This exposes the exact one-channel surface on which a positive
singular directional-flow derivative forces infinite dual cost.

Boundary traces remain deliberately absent from the dual.  In particular, this module does not
repair the cumulative-flow-offset obstruction or assert a path large-deviation upper bound.
-/

namespace FiniteMarkovProcesses.InformationTheory

open _root_.MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

/-- Native one-channel summand of the Renger hybrid-BV dual evaluation, defined on the total
carrier without an absolute-continuity premise. -/
noncomputable def rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) : ℝ :=
  (path.toDerivativePath.derivative (Sum.inr transition)).continuousTestIntegral test.1 -
    (generator.rate transition.1.1 transition.1.2 : ℝ) *
      finiteIntervalL1PathWeightedCoordinateIntegral
        (rengerDirectionalFlowHybridBVHamiltonianWeight test)
        (Sum.inl transition.1.1) path.toDerivativePath.toL1Path

/-- The zero relative test has zero native one-channel evaluation. -/
@[simp]
theorem rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation_zero
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation generator path transition
      (zeroFiniteOpenIntervalVanishingContinuousTest duration) = 0 := by
  unfold rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
    VagueSignedMeasure.continuousTestIntegral
  simp [zeroFiniteOpenIntervalVanishingContinuousTest,
    finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral,
    rengerDirectionalFlowHybridBVHamiltonianWeight_apply]

/-- Supremum of one native channel's continuous measure-level dual evaluations. -/
noncomputable def rengerDirectionalFlowHybridBVChannelMeasureDualRate
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) : ENNReal :=
  ⨆ test : FiniteOpenIntervalVanishingContinuousTest duration,
    ENNReal.ofReal
      (rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
        generator path transition test)

/-- Every total-carrier dual evaluation is the finite sum of its native channel evaluations. -/
theorem rengerDirectionalFlowHybridBVDualEvaluation_eq_sum_channelMeasureDualEvaluation
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    rengerDirectionalFlowHybridBVDualEvaluation generator test path =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
          generator path transition (test transition) := by
  rfl

/-- On the total hybrid-BV carrier, the path dual rate is the finite sum of its independent
native channel dual rates. -/
theorem rengerDirectionalFlowHybridBVDualRate_eq_sum_channelMeasureDualRate
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVDualRate generator path =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        rengerDirectionalFlowHybridBVChannelMeasureDualRate
          generator path transition := by
  unfold rengerDirectionalFlowHybridBVDualRate
    rengerDirectionalFlowHybridBVExtendedDualEvaluation
    rengerDirectionalFlowHybridBVChannelMeasureDualRate
  rw [show (⨆ test : RengerDirectionalFlowHybridBVDualTest State duration,
      ENNReal.ofReal (rengerDirectionalFlowHybridBVDualEvaluation generator test path)) =
      ⨆ test : RengerDirectionalFlowHybridBVDualTest State duration,
        ENNReal.ofReal
          (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
            rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
              generator path transition (test transition)) by
    congr 1]
  exact iSup_ofReal_finsetSum_eq_finsetSum_iSup_ofReal_of_zero
    (zeroFiniteOpenIntervalVanishingContinuousTest duration)
    (fun transition test =>
      rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
        generator path transition test)
    (fun transition =>
      rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation_zero
        generator path transition)

/-- The clamped expected one-way flow is integrable for every total-carrier hybrid path. -/
theorem integrable_rengerDirectionalFlowHybridBVExpectedFlowAt
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    Integrable (fun time =>
      (rengerDirectionalFlowHybridBVExpectedFlowAt
        generator path time transition : ℝ))
      (finiteOpenIntervalVolume duration) := by
  unfold rengerDirectionalFlowHybridBVExpectedFlowAt
    rengerDirectionalFlowHybridBVDensityAt
  simpa only [NNReal.coe_mul] using
    (integrable_rengerDirectionalFlowHybridBVDensityValue
      path transition.1.1).real_toNNReal.mul_const
        (generator.rate transition.1.1 transition.1.2 : ℝ)

/-- Finite physical-time reference measure carrying one channel's clamped expected flow. -/
noncomputable def rengerDirectionalFlowHybridBVExpectedFlowMeasure
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) : Measure ℝ :=
  (finiteOpenIntervalVolume duration).withDensity fun time =>
    ENNReal.ofReal
      (rengerDirectionalFlowHybridBVExpectedFlowAt
        generator path time transition : ℝ)

/-- One channel's expected-flow reference measure is finite. -/
theorem isFiniteMeasure_rengerDirectionalFlowHybridBVExpectedFlowMeasure
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    IsFiniteMeasure
      (rengerDirectionalFlowHybridBVExpectedFlowMeasure
        generator path transition) := by
  unfold rengerDirectionalFlowHybridBVExpectedFlowMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_rengerDirectionalFlowHybridBVExpectedFlowAt
      generator path transition).hasFiniteIntegral

/-- Every expected-flow reference measure remains carried by the open physical interval. -/
theorem ae_mem_finiteOpenInterval_rengerDirectionalFlowHybridBVExpectedFlowMeasure
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    ∀ᵐ time
        ∂rengerDirectionalFlowHybridBVExpectedFlowMeasure generator path transition,
      time ∈ Ioo 0 duration := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [finiteOpenIntervalVolume]
  exact ae_restrict_mem measurableSet_Ioo

/-- Every hybrid derivative's total variation remains carried by the open physical interval. -/
theorem ae_mem_finiteOpenInterval_rengerDirectionalFlowHybridBVDerivativeTotalVariation
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    ∀ᵐ time
        ∂(path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation,
      time ∈ Ioo 0 duration := by
  have hSupport :=
    (Classical.choose_spec path.hasCadlagDerivativeRealization).1 coordinate
  have hVariationSupport :=
    SignedMeasure.totalVariation_restrict_eq_self_of_restrict_eq_self
      (path.toDerivativePath.derivative coordinate).toSignedMeasure
      measurableSet_Ioo hSupport
  rw [ae_iff]
  change
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
      (Ioo 0 duration)ᶜ = 0
  have hApply := congrArg (fun measure : Measure ℝ => measure (Ioo 0 duration)ᶜ)
    hVariationSupport
  change
    ((path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation.restrict
      (Ioo 0 duration)) (Ioo 0 duration)ᶜ =
        (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
          (Ioo 0 duration)ᶜ at hApply
  rw [Measure.restrict_apply measurableSet_Ioo.compl,
    compl_inter_self] at hApply
  simpa using hApply.symm

/-- Against a nonnegative density coordinate, integration under the expected-flow measure is the
native generator-rate-weighted coordinate integral. -/
theorem integral_rengerDirectionalFlowHybridBVExpectedFlowMeasure_eq_weightedCoordinate
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hDensityNonnegative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1)
    (test : C_c(ℝ, ℝ)) :
    (∫ time, test time
        ∂rengerDirectionalFlowHybridBVExpectedFlowMeasure
          generator path transition) =
      (generator.rate transition.1.1 transition.1.2 : ℝ) *
        finiteIntervalL1PathWeightedCoordinateIntegral test
          (Sum.inl transition.1.1) path.toDerivativePath.toL1Path := by
  have hDensity : AEMeasurable
      (fun time =>
        ENNReal.ofReal
          (rengerDirectionalFlowHybridBVExpectedFlowAt
            generator path time transition : ℝ))
      (finiteOpenIntervalVolume duration) := by
    have hSourceDensity : AEMeasurable
        (fun time => rengerDirectionalFlowHybridBVDensityAt
          path time transition.1.1)
        (finiteOpenIntervalVolume duration) :=
      (measurable_pi_apply transition.1.1).comp_aemeasurable
        (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path)
    have hExpected : AEMeasurable
        (fun time => rengerDirectionalFlowHybridBVExpectedFlowAt
          generator path time transition)
        (finiteOpenIntervalVolume duration) := by
      unfold rengerDirectionalFlowHybridBVExpectedFlowAt
      exact hSourceDensity.mul aemeasurable_const
    exact hExpected.coe_nnreal_real.ennreal_ofReal
  unfold rengerDirectionalFlowHybridBVExpectedFlowMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hDensity (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) test]
  rw [rengerDirectionalFlowHybridBVWeightedDensityIntegral_eq]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hDensityNonnegative] with time hTime
  simp only [rengerDirectionalFlowHybridBVExpectedFlowAt,
    rengerDirectionalFlowHybridBVDensityAt,
    Real.coe_toNNReal _ hTime, NNReal.coe_mul,
    ENNReal.toReal_ofReal (mul_nonneg hTime NNReal.zero_le_coe), smul_eq_mul]
  ring

/-- A nonnegative native flow channel is exactly the measure-level continuous Poisson dual
against its total-variation carried measure and expected-flow reference measure. -/
theorem rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation_eq_poissonMeasure
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFlowMeasureNonnegative :
      0 ≤ (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure)
    (hDensityNonnegative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
        generator path transition test =
      poissonMeasureContinuousDualEvaluation
        (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure.totalVariation
        (rengerDirectionalFlowHybridBVExpectedFlowMeasure
          generator path transition) test := by
  unfold rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation
    poissonMeasureContinuousDualEvaluation
  rw [VagueSignedMeasure.continuousTestIntegral_eq_integral_totalVariation_of_zero_le
    _ hFlowMeasureNonnegative]
  have hCompensator :
      (∫ time, (Real.exp (test.1 time) - 1)
          ∂rengerDirectionalFlowHybridBVExpectedFlowMeasure
            generator path transition) =
        (generator.rate transition.1.1 transition.1.2 : ℝ) *
          finiteIntervalL1PathWeightedCoordinateIntegral
            (rengerDirectionalFlowHybridBVHamiltonianWeight test)
            (Sum.inl transition.1.1) path.toDerivativePath.toL1Path := by
    calc
      _ = ∫ time, rengerDirectionalFlowHybridBVHamiltonianWeight test time
          ∂rengerDirectionalFlowHybridBVExpectedFlowMeasure
            generator path transition := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun time => by
          rw [rengerDirectionalFlowHybridBVHamiltonianWeight_apply]
      _ = _ :=
        integral_rengerDirectionalFlowHybridBVExpectedFlowMeasure_eq_weightedCoordinate
          generator path transition hDensityNonnegative
            (rengerDirectionalFlowHybridBVHamiltonianWeight test)
  rw [hCompensator]

/-- The native one-channel dual rate agrees with its measure-level Poisson dual whenever the
carried signed derivative and the source density are nonnegative. -/
theorem rengerDirectionalFlowHybridBVChannelMeasureDualRate_eq_poissonMeasureContinuousDualRate
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFlowMeasureNonnegative :
      0 ≤ (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure)
    (hDensityNonnegative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1) :
    rengerDirectionalFlowHybridBVChannelMeasureDualRate
        generator path transition =
      poissonMeasureContinuousDualRate (duration := duration)
        (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure.totalVariation
        (rengerDirectionalFlowHybridBVExpectedFlowMeasure
          generator path transition) := by
  unfold rengerDirectionalFlowHybridBVChannelMeasureDualRate
    poissonMeasureContinuousDualRate
  congr 1
  funext test
  rw [rengerDirectionalFlowHybridBVChannelMeasureDualEvaluation_eq_poissonMeasure
    generator path transition hFlowMeasureNonnegative hDensityNonnegative test]

/-- A positive channel derivative singular with respect to physical time has infinite native
continuous dual cost. -/
theorem rengerDirectionalFlowHybridBVChannelMeasureDualRate_eq_top_of_not_absolutelyContinuous
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ} (hDuration : 0 < duration)
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFlowMeasureNonnegative :
      0 ≤ (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure)
    (hDensityNonnegative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1)
    (hNotAbsolutelyContinuous :
      ¬ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure ≪ᵥ
        (finiteOpenIntervalVolume duration).toENNRealVectorMeasure) :
    rengerDirectionalFlowHybridBVChannelMeasureDualRate
        generator path transition = ∞ := by
  let : IsFiniteMeasure
      (rengerDirectionalFlowHybridBVExpectedFlowMeasure
        generator path transition) :=
    isFiniteMeasure_rengerDirectionalFlowHybridBVExpectedFlowMeasure
      generator path transition
  let : IsFiniteMeasure
      (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure.totalVariation := by
    refine ⟨?_⟩
    rw [SignedMeasure.totalVariation, Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  have hVariationNotAbsolutelyContinuous :
      ¬ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure.totalVariation ≪
        finiteOpenIntervalVolume duration := by
    intro hVariation
    apply hNotAbsolutelyContinuous
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    exact hVariation
  have hVariationNotExpectedFlow :
      ¬ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure.totalVariation ≪
        rengerDirectionalFlowHybridBVExpectedFlowMeasure
          generator path transition := by
    intro hVariation
    apply hVariationNotAbsolutelyContinuous
    exact hVariation.trans (withDensity_absolutelyContinuous _ _)
  rw [rengerDirectionalFlowHybridBVChannelMeasureDualRate_eq_poissonMeasureContinuousDualRate
    generator path transition hFlowMeasureNonnegative hDensityNonnegative]
  exact poissonMeasureContinuousDualRate_eq_top_of_not_absolutelyContinuous
    hDuration hVariationNotExpectedFlow
      (ae_mem_finiteOpenInterval_rengerDirectionalFlowHybridBVDerivativeTotalVariation
        path (Sum.inr transition))
      (ae_mem_finiteOpenInterval_rengerDirectionalFlowHybridBVExpectedFlowMeasure
        generator path transition)

/-- One singular positive ordered-flow channel forces the complete total-carrier path dual to be
infinite. -/
theorem rengerDirectionalFlowHybridBVDualRate_eq_top_of_singularFlowChannel
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ} (hDuration : 0 < duration)
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hFlowMeasureNonnegative :
      0 ≤ (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure)
    (hDensityNonnegative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1)
    (hNotAbsolutelyContinuous :
      ¬ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure ≪ᵥ
        (finiteOpenIntervalVolume duration).toENNRealVectorMeasure) :
    rengerDirectionalFlowHybridBVDualRate generator path = ∞ := by
  have hChannel :=
    rengerDirectionalFlowHybridBVChannelMeasureDualRate_eq_top_of_not_absolutelyContinuous
      hDuration generator path transition hFlowMeasureNonnegative hDensityNonnegative
        hNotAbsolutelyContinuous
  rw [rengerDirectionalFlowHybridBVDualRate_eq_sum_channelMeasureDualRate]
  apply top_unique
  rw [← hChannel]
  exact Finset.single_le_sum
    (fun candidate _ => show (0 : ENNReal) ≤
      rengerDirectionalFlowHybridBVChannelMeasureDualRate
        generator path candidate from zero_le)
    (Finset.mem_univ transition)

/-- Exact support class currently licensed for the ambient dual-to-dynamic-rate bridge: either a
finite-rate admissible path or a path with a positive singular ordered-flow channel. -/
def RengerDirectionalFlowHybridBVFiniteRateOrSingularFlow
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) : Prop :=
  RengerDirectionalFlowHybridBVAdmissible path hDuration ∨
    ∃ transition : FiniteStateOrderedOffDiagonalTransition State,
      0 ≤ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure ∧
      (∀ᵐ time ∂finiteOpenIntervalVolume duration,
        0 ≤ rengerDirectionalFlowHybridBVDensityValue
          path time transition.1.1) ∧
      ¬ (path.toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure ≪ᵥ
        (finiteOpenIntervalVolume duration).toENNRealVectorMeasure

/-- On the exact finite-rate-or-positive-singular support class, the total-carrier dual rate is
the published totalized dynamic rate. -/
theorem rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_of_finiteRateOrSingularFlow
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ} (hDuration : 0 < duration)
    (generator : FiniteStateMarkovGenerator State)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVFiniteRateOrSingularFlow
      path hDuration) :
    rengerDirectionalFlowHybridBVDualRate generator path =
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
  rcases hPath with hAdmissible | ⟨transition, hFlow, hDensity, hSingular⟩
  · exact rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain
      generator hDuration ⟨path, hAdmissible⟩
  · rw [rengerDirectionalFlowHybridBVDualRate_eq_top_of_singularFlowChannel
      hDuration generator path transition hFlow hDensity hSingular]
    exact (rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
      generator hDuration fun hAdmissible =>
        hSingular (hAdmissible.absolutelyContinuousDerivative (Sum.inr transition))).symm

end

end FiniteMarkovProcesses.InformationTheory
