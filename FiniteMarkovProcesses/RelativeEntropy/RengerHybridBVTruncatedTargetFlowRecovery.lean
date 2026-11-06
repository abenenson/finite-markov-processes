/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateCoercivity
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTruncatedTargetRate

/-!
# Finite-action recovery of truncated Renger target flow

Finite dynamic action makes every target directional-flow coordinate integrable.  Combined with
the monotone cutoff recovery theorem, this upgrades extended-integral convergence to vanishing
physical-time `L1` error for every ordered channel.

This module remains target-side analysis.  It does not identify a source mean or assert a
Girsanov formula.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Every ordered target-flow coordinate has finite physical-time mass when the dynamic action is
finite. -/
theorem lintegral_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_ne_top
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    (∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target : ENNReal)
      ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
  have hCorrectedRateFinite :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 +
          rengerDirectionalFlowHybridBVGeneratorCorrection generator *
            ENNReal.ofReal duration ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hDynamicRate,
      ENNReal.mul_ne_top
        (rengerDirectionalFlowHybridBVGeneratorCorrection_ne_top generator)
        ENNReal.ofReal_ne_top⟩
  have hTotalVariationFinite :
      rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path.1 ≠ ⊤ :=
    ne_top_of_le_ne_top hCorrectedRateFinite
      (rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_le_dynamicRate_add_uniformCorrection
        generator hDuration path.2)
  have hSingleLeTotalVariation :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≤
        rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path.1 := by
    rw [rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_eq_totalFlowIntegral
      hDuration path.2]
    apply lintegral_mono
    intro time
    unfold rengerDirectionalFlowHybridBVTotalFlowIntegrand
    simpa [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt, hOffDiagonal] using
      (Finset.single_le_sum
        (f := fun transition : FiniteStateOrderedOffDiagonalTransition State =>
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition : ENNReal))
        (fun _ _ ↦ (bot_le : (0 : ENNReal) ≤ _))
        (Finset.mem_univ
          (⟨(source, target), hOffDiagonal⟩ :
            FiniteStateOrderedOffDiagonalTransition State)))
  exact ne_top_of_le_ne_top hTotalVariationFinite hSingleLeTotalVariation

/-- The integrated error between one exact target-flow coordinate and its truncated generated
flow tends to zero as the natural cutoff diverges. -/
theorem tendsto_lintegral_rengerDirectionalFlowHybridBVTruncatedTargetFlowError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    Tendsto
        (fun cutoff : ℕ ↦
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path.1 time source target : ENNReal) -
              (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
                path.1 cutoff time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration)
        atTop (nhds 0) := by
  let targetIntegral : ENNReal :=
    ∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target : ENNReal)
      ∂finiteOpenIntervalVolume duration
  let truncatedIntegral : ℕ → ENNReal := fun cutoff ↦
    ∫⁻ time,
      (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path.1 cutoff time source target : ENNReal)
      ∂finiteOpenIntervalVolume duration
  have hTargetIntegralFinite : targetIntegral ≠ ⊤ :=
    lintegral_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_ne_top
      generator hDuration path hDynamicRate hOffDiagonal
  have hTruncatedLe (cutoff : ℕ) : truncatedIntegral cutoff ≤ targetIntegral := by
    apply lintegral_mono
    intro time
    exact ENNReal.coe_le_coe.2
      (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
        path.1 cutoff time hOffDiagonal)
  have hTruncatedFinite (cutoff : ℕ) : truncatedIntegral cutoff ≠ ⊤ :=
    ne_top_of_le_ne_top hTargetIntegralFinite (hTruncatedLe cutoff)
  have hIntegralError (cutoff : ℕ) :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 cutoff time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) =
        targetIntegral - truncatedIntegral cutoff := by
    exact lintegral_sub
      (measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path.1 cutoff source target).coe_nnreal_ennreal
      (hTruncatedFinite cutoff)
      (ae_of_all _ fun time ↦ by
        exact ENNReal.coe_le_coe.2
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
            path.1 cutoff time hOffDiagonal))
  have hTruncatedTendsto :
      Tendsto truncatedIntegral atTop (nhds targetIntegral) :=
    tendsto_lintegral_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
      generator hDuration path hDynamicRate hOffDiagonal
  rw [show (fun cutoff : ℕ ↦
      ∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 cutoff time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) =
      fun cutoff ↦ targetIntegral - truncatedIntegral cutoff by
    funext cutoff
    exact hIntegralError cutoff]
  simpa using
    ENNReal.Tendsto.sub tendsto_const_nhds hTruncatedTendsto
      (Or.inl hTargetIntegralFinite)

/-- Reference expected directional flow formed from the measurable target density version. -/
noncomputable def rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (source target : State) : NNReal :=
  rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
    generator.rate source target

/-- Every measurable expected-flow coordinate is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path time source target := by
  exact
    ((measurable_pi_apply source).comp
      (measurable_rengerDirectionalFlowHybridBVMeasurableDensityAt path)).mul measurable_const

/-- Finite action forces zero target flow almost everywhere whenever the measurable reference
expected flow is zero. -/
theorem ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_expectedFlow_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target = 0 →
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target = 0 := by
  by_cases hGeneratorRate : generator.rate source target = 0
  · filter_upwards [
      ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_generator_rate_eq_zero
        generator hDuration path hDynamicRate hOffDiagonal hGeneratorRate] with time hFlowZero
    exact fun _hExpected ↦ hFlowZero
  · filter_upwards [
      ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_density_eq_zero
        generator hDuration path hDynamicRate hOffDiagonal] with time hDensityGate hExpected
    unfold rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt at hExpected
    rcases mul_eq_zero.mp hExpected with hDensity | hGenerator
    · exact hDensityGate hDensity
    · exact False.elim (hGeneratorRate hGenerator)

/-- On a finite-action path, every truncated one-channel extended cost converges almost
everywhere to the exact one-channel cost. -/
theorem ae_tendsto_rengerExtendedPoissonRateCost_truncatedTargetFlow_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      Tendsto
          (fun cutoff : ℕ ↦
            rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
                path.1 cutoff time source target)
              (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                generator path.1 time source target))
          atTop
          (nhds
            (rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path.1 time source target)
              (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                generator path.1 time source target))) := by
  filter_upwards [
    ae_tendsto_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
      generator hDuration path hDynamicRate hOffDiagonal,
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_expectedFlow_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal] with
      time hFlowTendsto hZeroExpectedFlow
  by_cases hExpected :
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target = 0
  · have hFlow :
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target = 0 := hZeroExpectedFlow hExpected
    have hTruncatedFlow (cutoff : ℕ) :
        rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
          path.1 cutoff time source target = 0 := by
      exact le_zero_iff.mp <|
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
          path.1 cutoff time hOffDiagonal).trans_eq hFlow
    simp [hExpected, hFlow, hTruncatedFlow, rengerExtendedPoissonRateCost_zero_zero]
  · have hExpectedPositive :
        0 < rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target := pos_iff_ne_zero.mpr hExpected
    have hExpectedRealPositive :
        0 < (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target : ℝ) := by
      exact_mod_cast hExpectedPositive
    simp_rw [rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive]
    apply ENNReal.tendsto_ofReal
    exact (continuous_poissonRateDiscrimination_left
      hExpectedRealPositive).continuousAt.tendsto.comp
      (NNReal.tendsto_coe.2 hFlowTendsto)

/-- The truncated one-channel cost is dominated by the measurable expected intensity plus the
exact target one-channel cost. -/
theorem ae_rengerExtendedPoissonRateCost_truncatedTargetFlow_le_expected_add_targetCost
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) (cutoff : NNReal) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 cutoff time source target)
          (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target) ≤
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target : ENNReal) +
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target)
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target) := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_expectedFlow_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal] with time hZeroExpectedFlow
  let expected := rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    generator path.1 time source target
  let targetFlow := rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
    path.1 time source target
  let truncatedFlow := rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
    path.1 cutoff time source target
  by_cases hExpected : expected = 0
  · have hTargetFlow : targetFlow = 0 := hZeroExpectedFlow hExpected
    have hTruncatedFlow : truncatedFlow = 0 := by
      exact le_zero_iff.mp <|
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
          path.1 cutoff time hOffDiagonal).trans_eq hTargetFlow
    simp [expected, targetFlow, truncatedFlow, hExpected, hTargetFlow, hTruncatedFlow,
      rengerExtendedPoissonRateCost_zero_zero]
  · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
    have hExpectedRealPositive : 0 < (expected : ℝ) := by exact_mod_cast hExpectedPositive
    have hTruncatedNonnegative : 0 ≤ (truncatedFlow : ℝ) := by positivity
    have hTruncatedLeTarget : (truncatedFlow : ℝ) ≤ (targetFlow : ℝ) := by
      exact_mod_cast
        rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
          path.1 cutoff time hOffDiagonal
    have hRealBound :=
      poissonRateDiscrimination_le_reference_add_upperDiscrimination
        hTruncatedNonnegative hTruncatedLeTarget hExpectedRealPositive
    rw [rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive,
      rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive]
    calc
      ENNReal.ofReal (poissonRateDiscrimination (truncatedFlow : ℝ) (expected : ℝ)) ≤
          ENNReal.ofReal ((expected : ℝ) +
            poissonRateDiscrimination (targetFlow : ℝ) (expected : ℝ)) :=
        ENNReal.ofReal_le_ofReal hRealBound
      _ = (expected : ENNReal) +
          ENNReal.ofReal
            (poissonRateDiscrimination (targetFlow : ℝ) (expected : ℝ)) := by
        rw [ENNReal.ofReal_add hExpectedRealPositive.le
          (poissonRateDiscrimination_nonneg (by positivity) hExpectedRealPositive)]
        rw [ENNReal.ofReal_coe_nnreal]

/-- The measurable expected-flow coordinate has finite physical-time integral. -/
theorem lintegral_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt_ne_top
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (source target : State) :
    (∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target : ENNReal)
      ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
  have hExpectedLe :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target : ENNReal) ≤
          (generator.rate source target : ENNReal) := by
    filter_upwards [
      rengerDirectionalFlowHybridBVDensityAt_le_one_ae hDuration path.2,
      ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq path.1] with
        time hDensity hDensityVersion
    apply ENNReal.coe_le_coe.2
    unfold rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    rw [hDensityVersion]
    calc
      rengerDirectionalFlowHybridBVDensityAt path.1 time source *
          generator.rate source target ≤
        1 * generator.rate source target := by
          gcongr
          exact hDensity source
      _ = generator.rate source target := one_mul _
  have hConstantIntegralFinite :
      (∫⁻ _time : ℝ, (generator.rate source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  exact ne_top_of_le_ne_top hConstantIntegralFinite (lintegral_mono_ae hExpectedLe)

/-- The exact measurable-version one-channel target cost has finite integral because it is a
summand of the finite dynamic action. -/
theorem lintegral_rengerExtendedPoissonRateCost_measurableTargetFlow_ne_top
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    (∫⁻ time,
      rengerExtendedPoissonRateCost
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target)
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target)
      ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
  let transition : FiniteStateOrderedOffDiagonalTransition State :=
    ⟨(source, target), hOffDiagonal⟩
  have hCostVersion :
      (fun time ↦
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target)
          (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target)) =ᵐ[finiteOpenIntervalVolume duration]
      fun time ↦
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition)
          (rengerDirectionalFlowHybridBVDensityAt path.1 time source *
            generator.rate source target) := by
    filter_upwards [
      ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq path.1] with
        time hDensityVersion
    simp [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt, hOffDiagonal,
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt, hDensityVersion, transition]
  have hChannelIntegralLeDynamicRate :
      (∫⁻ time,
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition)
          (rengerDirectionalFlowHybridBVDensityAt path.1 time source *
            generator.rate source target)
        ∂finiteOpenIntervalVolume duration) ≤
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 := by
    rw [rengerDirectionalFlowHybridBVDynamicRate_eq_integral_on_representationDomain
      generator hDuration path]
    apply lintegral_mono
    intro time
    unfold rengerDirectionalFlowLocalRateRaw
    simpa only [transition] using
      (Finset.single_le_sum
        (f := fun channel : FiniteStateOrderedOffDiagonalTransition State =>
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time channel)
            (rengerDirectionalFlowHybridBVDensityAt path.1 time channel.1.1 *
              generator.rate channel.1.1 channel.1.2))
        (fun _ _ ↦ (bot_le : (0 : ENNReal) ≤ _))
        (Finset.mem_univ transition))
  have hRawChannelFinite :
      (∫⁻ time,
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time transition)
          (rengerDirectionalFlowHybridBVDensityAt path.1 time source *
            generator.rate source target)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ :=
    ne_top_of_le_ne_top hDynamicRate hChannelIntegralLeDynamicRate
  rw [lintegral_congr_ae hCostVersion]
  exact hRawChannelFinite

/-- Dominated convergence recovers every integrated one-channel extended cost from the truncated
target-flow charts. -/
theorem tendsto_lintegral_rengerExtendedPoissonRateCost_truncatedTargetFlow_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    Tendsto
        (fun cutoff : ℕ ↦
          ∫⁻ time,
            rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
                path.1 cutoff time source target)
              (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                generator path.1 time source target)
            ∂finiteOpenIntervalVolume duration)
        atTop
        (nhds
          (∫⁻ time,
            rengerExtendedPoissonRateCost
              (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path.1 time source target)
              (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                generator path.1 time source target)
            ∂finiteOpenIntervalVolume duration)) := by
  let truncatedCost : ℕ → ℝ → ENNReal := fun cutoff time ↦
    rengerExtendedPoissonRateCost
      (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path.1 cutoff time source target)
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target)
  let targetCost : ℝ → ENNReal := fun time ↦
    rengerExtendedPoissonRateCost
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target)
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target)
  let costBound : ℝ → ENNReal := fun time ↦
    (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target : ENNReal) + targetCost time
  apply tendsto_lintegral_of_dominated_convergence costBound
  · intro cutoff
    exact measurable_rengerExtendedPoissonRateCost.comp <|
      (measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path.1 cutoff source target).prodMk
      (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 source target)
  · intro cutoff
    exact
      ae_rengerExtendedPoissonRateCost_truncatedTargetFlow_le_expected_add_targetCost
        generator hDuration path hDynamicRate hOffDiagonal cutoff
  · have hExpectedFinite :=
      lintegral_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt_ne_top
        generator hDuration path source target
    have hTargetCostFinite :=
      lintegral_rengerExtendedPoissonRateCost_measurableTargetFlow_ne_top
        generator hDuration path hDynamicRate hOffDiagonal
    change (∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target : ENNReal) + targetCost time
      ∂finiteOpenIntervalVolume duration) ≠ ⊤
    rw [lintegral_add_left]
    exact ENNReal.add_ne_top.2 ⟨hExpectedFinite, hTargetCostFinite⟩
    exact
      (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 source target).coe_nnreal_ennreal
  · exact ae_tendsto_rengerExtendedPoissonRateCost_truncatedTargetFlow_atTop
      generator hDuration path hDynamicRate hOffDiagonal

end

end FiniteMarkovProcesses.InformationTheory
