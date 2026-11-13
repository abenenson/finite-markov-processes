/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVDualRepresentation
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRepresentationDomain
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Finite-channel Renger hybrid-BV duality

This module lifts exact one-channel continuous-test duality through the finite family of ordered
off-diagonal transitions and identifies the existing hybrid-BV path dual with the dynamic rate
on its licensed finite-rate representation domain.

## Main results

* `iSup_ofReal_finsetSum_eq_finsetSum_iSup_ofReal_of_zero` interchanges a finite family of
  independently indexed positive-part suprema when every coordinate has an exact zero test.
* `rengerDirectionalFlowHybridBVChannelDualIntegral` isolates one ordered transition's
  integrated dual evaluation.
* `rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain` proves the
  scoped path-level converse representation.
* `lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate_on_representationDomain`
  transfers lower semicontinuity only to that named domain.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped BigOperators ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

/-- A finite family of independently indexed real tests admits exact interchange between the
positive embedding of the total sum and the sum of coordinatewise positive-embedding suprema,
provided every coordinate shares a test whose value is exactly zero. -/
theorem iSup_ofReal_finsetSum_eq_finsetSum_iSup_ofReal_of_zero
    {Index Test : Type*} [Fintype Index]
    (zeroTest : Test) (value : Index → Test → ℝ)
    (hZero : ∀ index, value index zeroTest = 0) :
    (⨆ tests : Index → Test,
      ENNReal.ofReal (∑ index : Index, value index (tests index))) =
      ∑ index : Index,
        ⨆ test : Test, ENNReal.ofReal (value index test) := by
  have hPositivePart :
      (⨆ tests : Index → Test,
        ENNReal.ofReal (∑ index : Index, value index (tests index))) =
        ⨆ tests : Index → Test,
          ∑ index : Index,
            ENNReal.ofReal (value index (tests index)) := by
    apply le_antisymm
    · apply iSup_le
      intro tests
      exact
        (ofReal_finset_sum_le_sum_ofReal
          Finset.univ (fun index => value index (tests index))).trans
          (le_iSup
            (fun candidates : Index → Test =>
              ∑ index : Index,
                ENNReal.ofReal (value index (candidates index)))
            tests)
    · apply iSup_le
      intro tests
      let nonnegativeTests : Index → Test := fun index =>
        if 0 ≤ value index (tests index) then tests index else zeroTest
      have hNonnegative :
          ∀ index, 0 ≤ value index (nonnegativeTests index) := by
        intro index
        by_cases h : 0 ≤ value index (tests index)
        · simpa only [nonnegativeTests, ite_eq_left h] using h
        · simp only [nonnegativeTests, ite_eq_right h, hZero index, le_refl]
      have hOfReal :
          ∀ index,
            ENNReal.ofReal (value index (tests index)) =
              ENNReal.ofReal (value index (nonnegativeTests index)) := by
        intro index
        by_cases h : 0 ≤ value index (tests index)
        · simp only [nonnegativeTests, ite_eq_left h]
        · simp only [nonnegativeTests, ite_eq_right h, hZero index,
            ENNReal.ofReal_zero]
          exact ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h)
      calc
        (∑ index : Index,
            ENNReal.ofReal (value index (tests index))) =
            ∑ index : Index,
              ENNReal.ofReal (value index (nonnegativeTests index)) := by
          apply Finset.sum_congr rfl
          intro index _hIndex
          exact hOfReal index
        _ = ENNReal.ofReal
            (∑ index : Index,
              value index (nonnegativeTests index)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro index _hIndex
          exact hNonnegative index
        _ ≤ ⨆ candidates : Index → Test,
            ENNReal.ofReal
              (∑ index : Index, value index (candidates index)) :=
          le_iSup
            (fun candidates : Index → Test =>
              ENNReal.ofReal
                (∑ index : Index, value index (candidates index)))
            nonnegativeTests
  rw [hPositivePart]
  symm
  have hCoordinate :
      ∀ index : Index,
        (⨆ tests : Index → Test,
          ENNReal.ofReal (value index (tests index))) =
          ⨆ test : Test, ENNReal.ofReal (value index test) := by
    intro index
    apply le_antisymm
    · apply iSup_le
      intro tests
      exact le_iSup
        (fun test => ENNReal.ofReal (value index test)) (tests index)
    · apply iSup_le
      intro test
      exact le_iSup_of_le (fun _ => test) le_rfl
  calc
    (∑ index : Index,
        ⨆ test : Test, ENNReal.ofReal (value index test)) =
        ∑ index : Index,
          ⨆ tests : Index → Test,
            ENNReal.ofReal (value index (tests index)) :=
      Finset.sum_congr rfl fun index _ => (hCoordinate index).symm
    _ = ⨆ tests : Index → Test,
        ∑ index : Index,
          ENNReal.ofReal (value index (tests index)) := by
      simpa using
        (ENNReal.finsetSum_iSup
          (s := Finset.univ)
          (f := fun index (tests : Index → Test) =>
            ENNReal.ofReal (value index (tests index)))
          (by
            intro first second
            refine ⟨fun index =>
              if ENNReal.ofReal (value index (first index)) ≤
                  ENNReal.ofReal (value index (second index))
              then second index else first index, ?_⟩
            intro index
            by_cases h :
                ENNReal.ofReal (value index (first index)) ≤
                  ENNReal.ofReal (value index (second index))
            · simp [h]
            · simp [h, le_of_not_ge h]))

/-- The identically zero relative continuous test. -/
noncomputable def zeroFiniteOpenIntervalVanishingContinuousTest
    (duration : ℝ) : FiniteOpenIntervalVanishingContinuousTest duration :=
  ⟨0, by
    intro time _hTime
    simp⟩

/-- The zero relative continuous test evaluates to zero at every time. -/
@[simp]
theorem zeroFiniteOpenIntervalVanishingContinuousTest_apply
    (duration time : ℝ) :
    (zeroFiniteOpenIntervalVanishingContinuousTest duration).1 time = 0 :=
  rfl

/-- Expected one-way flow on one ordered channel: source density times the fixed generator
rate. -/
noncomputable def rengerDirectionalFlowHybridBVExpectedFlowAt
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State) : NNReal :=
  rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
    generator.rate transition.1.1 transition.1.2

/-- Integrated one-channel exponential dual evaluation for one ordered transition. -/
noncomputable def rengerDirectionalFlowHybridBVChannelDualIntegral
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) : ℝ :=
  ∫ time,
    poissonExponentialDualEvaluation
      (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ℝ)
      (rengerDirectionalFlowHybridBVExpectedFlowAt
        generator path time transition : ℝ)
      (test.1 time)
    ∂finiteOpenIntervalVolume duration

/-- The identically zero test has zero one-channel dual integral. -/
@[simp]
theorem rengerDirectionalFlowHybridBVChannelDualIntegral_zero
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVChannelDualIntegral generator path transition
      (zeroFiniteOpenIntervalVanishingContinuousTest duration) = 0 := by
  simp [rengerDirectionalFlowHybridBVChannelDualIntegral,
    poissonExponentialDualEvaluation]

/-- On the representation domain, the existing topological path dual evaluation is the finite
sum of the independently defined one-channel integrated evaluations. -/
theorem rengerDirectionalFlowHybridBVDualEvaluation_eq_sum_channelDualIntegral
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path :
      RengerDirectionalFlowHybridBVRepresentationPath
        State duration hDuration)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    rengerDirectionalFlowHybridBVDualEvaluation generator test path.1 =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        rengerDirectionalFlowHybridBVChannelDualIntegral
          generator path.1 transition (test transition) := by
  rw [rengerDirectionalFlowHybridBVDualEvaluation_eq_integral
    generator test path.1 path.2.absolutelyContinuousDerivative]
  unfold rengerDirectionalFlowHybridBVDualIntegrand
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro transition _hTransition
    unfold rengerDirectionalFlowHybridBVChannelDualIntegral
    apply integral_congr_ae
    filter_upwards [path.2.flowDerivativeNonnegativeAE,
      path.2.densityNonnegativeAE] with time hFlow hDensity
    simp only [rengerDirectionalFlowHybridBVExpectedFlowAt,
      rengerDirectionalFlowHybridBVFlowDerivativeAt,
      rengerDirectionalFlowHybridBVDensityAt,
      Real.coe_toNNReal _ (hFlow transition),
      Real.coe_toNNReal _ (hDensity transition.1.1),
      NNReal.coe_mul, poissonExponentialDualEvaluation]
    ring
  · intro transition _hTransition
    apply Integrable.sub
    · exact integrable_compactlySupportedContinuousMap_mul_of_integrable_right
        (test transition).1
        (integrable_rengerDirectionalFlowHybridBVFlowDerivative
          path.1 transition)
    · apply Integrable.const_mul
      simpa only [rengerDirectionalFlowHybridBVHamiltonianWeight_apply] using
        integrable_compactlySupportedContinuousMap_mul_of_integrable_right
          (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
          (integrable_rengerDirectionalFlowHybridBVDensityValue
            path.1 transition.1.1)

/-- The existing path dual supremum is the finite sum of its independent one-channel continuous
dual rates on the representation domain. -/
theorem rengerDirectionalFlowHybridBVDualRate_eq_sum_channelContinuousDualRate
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path :
      RengerDirectionalFlowHybridBVRepresentationPath
        State duration hDuration) :
    rengerDirectionalFlowHybridBVDualRate generator path.1 =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        oneChannelContinuousPoissonDualRate
          (duration := duration)
          (finiteOpenIntervalVolume duration)
          (fun time =>
            rengerDirectionalFlowHybridBVFlowDerivativeAt
              path.1 time transition)
          (fun time =>
            rengerDirectionalFlowHybridBVExpectedFlowAt
              generator path.1 time transition) := by
  unfold rengerDirectionalFlowHybridBVDualRate
    rengerDirectionalFlowHybridBVExtendedDualEvaluation
  simp_rw [
    rengerDirectionalFlowHybridBVDualEvaluation_eq_sum_channelDualIntegral
      generator hDuration path]
  exact iSup_ofReal_finsetSum_eq_finsetSum_iSup_ofReal_of_zero
    (zeroFiniteOpenIntervalVanishingContinuousTest duration)
    (fun transition test =>
      rengerDirectionalFlowHybridBVChannelDualIntegral
        generator path.1 transition test)
    (fun transition =>
      rengerDirectionalFlowHybridBVChannelDualIntegral_zero
        generator path.1 transition)

/-- Exact one-channel continuous duality specialized to an ordered channel of one finite-rate
hybrid-BV representation path. -/
theorem
    rengerDirectionalFlowHybridBVChannelContinuousDualRate_eq_lintegral_rateCost
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path :
      RengerDirectionalFlowHybridBVRepresentationPath
        State duration hDuration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    oneChannelContinuousPoissonDualRate
        (duration := duration)
        (finiteOpenIntervalVolume duration)
        (fun time =>
          rengerDirectionalFlowHybridBVFlowDerivativeAt
            path.1 time transition)
        (fun time =>
          rengerDirectionalFlowHybridBVExpectedFlowAt
            generator path.1 time transition) =
      ∫⁻ time,
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt
            path.1 time transition)
          (rengerDirectionalFlowHybridBVExpectedFlowAt
            generator path.1 time transition)
        ∂finiteOpenIntervalVolume duration := by
  have hFlowAEMeasurable : AEMeasurable
      (fun time =>
        rengerDirectionalFlowHybridBVFlowDerivativeAt
          path.1 time transition)
      (finiteOpenIntervalVolume duration) :=
    (measurable_pi_apply transition).comp_aemeasurable
      (aemeasurable_rengerDirectionalFlowHybridBVFlowDerivativeAt path.1)
  have hDensityAEMeasurable : AEMeasurable
      (fun time =>
        rengerDirectionalFlowHybridBVDensityAt
          path.1 time transition.1.1)
      (finiteOpenIntervalVolume duration) :=
    (measurable_pi_apply transition.1.1).comp_aemeasurable
      (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path.1)
  have hExpectedAEMeasurable : AEMeasurable
      (fun time =>
        rengerDirectionalFlowHybridBVExpectedFlowAt
          generator path.1 time transition)
      (finiteOpenIntervalVolume duration) := by
    unfold rengerDirectionalFlowHybridBVExpectedFlowAt
    exact hDensityAEMeasurable.mul aemeasurable_const
  have hFlowIntegrable : Integrable
      (fun time =>
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          path.1 time transition : ℝ))
      (finiteOpenIntervalVolume duration) := by
    apply
      (integrable_rengerDirectionalFlowHybridBVFlowDerivative
        path.1 transition).congr
    filter_upwards [path.2.flowDerivativeNonnegativeAE] with time hFlow
    simp only [rengerDirectionalFlowHybridBVFlowDerivativeAt,
      Real.coe_toNNReal _ (hFlow transition)]
  have hDensityIntegrable : Integrable
      (fun time =>
        (rengerDirectionalFlowHybridBVDensityAt
          path.1 time transition.1.1 : ℝ))
      (finiteOpenIntervalVolume duration) := by
    apply
      (integrable_rengerDirectionalFlowHybridBVDensityValue
        path.1 transition.1.1).congr
    filter_upwards [path.2.densityNonnegativeAE] with time hDensity
    simp only [rengerDirectionalFlowHybridBVDensityAt,
      Real.coe_toNNReal _ (hDensity transition.1.1)]
  have hExpectedIntegrable : Integrable
      (fun time =>
        (rengerDirectionalFlowHybridBVExpectedFlowAt
          generator path.1 time transition : ℝ))
      (finiteOpenIntervalVolume duration) := by
    simpa only [rengerDirectionalFlowHybridBVExpectedFlowAt,
      NNReal.coe_mul] using
      hDensityIntegrable.mul_const
        (generator.rate transition.1.1 transition.1.2 : ℝ)
  apply
    oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost_of_aemeasurable
      hDuration
  · exact hFlowAEMeasurable
  · exact hExpectedAEMeasurable
  · exact hFlowIntegrable
  · exact hExpectedIntegrable
  · rw [finiteOpenIntervalVolume]
    exact ae_restrict_mem measurableSet_Ioo

/-- On the representation domain, the totalized dynamic rate is the finite sum of its integrated
ordered-channel costs. -/
theorem
    rengerDirectionalFlowHybridBVDynamicRate_eq_sum_channelRateCostIntegrals
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path :
      RengerDirectionalFlowHybridBVRepresentationPath
        State duration hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ∫⁻ time,
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVFlowDerivativeAt
              path.1 time transition)
            (rengerDirectionalFlowHybridBVExpectedFlowAt
              generator path.1 time transition)
          ∂finiteOpenIntervalVolume duration := by
  rw [
    rengerDirectionalFlowHybridBVDynamicRate_eq_integral_on_representationDomain
      generator hDuration path]
  unfold rengerDirectionalFlowLocalRateRaw
  rw [lintegral_finsetSum' Finset.univ (by
    intro transition _hTransition
    have hFlow : AEMeasurable
        (fun time =>
          rengerDirectionalFlowHybridBVFlowDerivativeAt
            path.1 time transition)
        (finiteOpenIntervalVolume duration) :=
      (measurable_pi_apply transition).comp_aemeasurable
        (aemeasurable_rengerDirectionalFlowHybridBVFlowDerivativeAt path.1)
    have hDensity : AEMeasurable
        (fun time =>
          rengerDirectionalFlowHybridBVDensityAt
            path.1 time transition.1.1)
        (finiteOpenIntervalVolume duration) :=
      (measurable_pi_apply transition.1.1).comp_aemeasurable
        (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path.1)
    exact measurable_rengerExtendedPoissonRateCost.comp_aemeasurable
      (hFlow.prodMk (hDensity.mul aemeasurable_const)))]
  rfl

/-- Renger's relative continuous-test dual is exactly the totalized dynamic rate on the named
finite-rate representation domain.  No equality is asserted on the ambient hybrid carrier. -/
theorem rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path :
      RengerDirectionalFlowHybridBVRepresentationPath
        State duration hDuration) :
    rengerDirectionalFlowHybridBVDualRate generator path.1 =
      rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration path.1 := by
  rw [
    rengerDirectionalFlowHybridBVDualRate_eq_sum_channelContinuousDualRate
      generator hDuration path,
    rengerDirectionalFlowHybridBVDynamicRate_eq_sum_channelRateCostIntegrals
      generator hDuration path]
  apply Finset.sum_congr rfl
  intro transition _hTransition
  exact
    rengerDirectionalFlowHybridBVChannelContinuousDualRate_eq_lintegral_rateCost
      generator hDuration path transition

/-- The dynamic rate is lower semicontinuous on the exact finite-rate representation subtype.
This theorem does not promote it to a lower-semicontinuous functional on the ambient hybrid
carrier, where the cumulative-flow-offset adverse control still forbids dual equality. -/
theorem
    lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate_on_representationDomain
    {State : Type u} [Fintype State] [DecidableEq State]
    {duration : ℝ}
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    LowerSemicontinuous fun path :
        RengerDirectionalFlowHybridBVRepresentationPath
          State duration hDuration =>
      rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration path.1 := by
  convert
    lowerSemicontinuous_rengerDirectionalFlowHybridBVDualRate_on_representationDomain
      generator hDuration using 1
  funext path
  exact
    (rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain
      generator hDuration path).symm

end

end FiniteMarkovProcesses.InformationTheory
