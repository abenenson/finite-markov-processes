/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetActionExpectation
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMeanConvergence
public import FiniteMarkovProcesses.MeasureTheory.Integral.OfRealIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Generated-flow action convergence for positive Renger target sources

This module connects the exact finite-law KL expectation to the positive target chart.  The
argument keeps the physical source density separate from the target density and uses the exact
homogeneity of the extended Poisson cost; no equality of scalar actions is promoted to a carrier
identification.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The source occupation mean agrees almost everywhere on its physical interval with the
resummed endpoint probability used by the ordered-flow compensator. -/
theorem ae_finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume (duration : ℝ),
      finiteStateTimeDependentMarkovMeanDensityAt initial rates duration time state =
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time state).toReal := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with time hTime
  have hMean := finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointPMF
    initial rates duration ⟨time, hTime.1.le⟩ (by exact_mod_cast hTime.2.le) state
  simpa only [finiteStateTimeDependentMarkovEndpointPMF_apply] using! hMean

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A bounded measurable real weight times one occupied-source intensity is integrable on the
complete physical interval. -/
theorem integrableOn_realWeight_mul_endpointProbability_mul_rate
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, |weight time| ≤ weightBound) :
    MeasureTheory.IntegrableOn
      (fun time ↦ weight time *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time source).toReal *
        (rates.rate time source target : ℝ))
      (Ioo 0 (duration : ℝ)) := by
  let nnrealBound : NNReal := ⟨weightBound, hWeightBoundNonnegative⟩
  have hDominating :=
    integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
      initial rates duration hNe (fun _time ↦ nnrealBound) measurable_const
      hWeightBoundNonnegative (fun _time ↦ le_rfl)
  have hEndpointMeasurable : Measurable fun time ↦
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time source).toReal := by
    unfold finiteStateTimeDependentMarkovEndpointProbability
    have hSurvival : Measurable fun time : ℝ ↦
        ENNReal.ofReal
          (Real.exp (-((rates.uniformizationRate : ℝ) * time))) := by
      fun_prop
    exact (hSurvival.mul
      (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates source)).ennreal_toReal
  have hIntegrandMeasurable : Measurable fun time ↦ weight time *
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time source).toReal *
      (rates.rate time source target : ℝ) :=
    (hWeight.mul hEndpointMeasurable).mul
      (rates.measurable_rate source target).coe_nnreal_real
  apply hDominating.mono' hIntegrandMeasurable.aestronglyMeasurable
  filter_upwards [] with time
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (rates.rate time source target).coe_nonneg]
  change |weight time| * _ * _ ≤ weightBound * _ * _
  gcongr
  exact hWeightBound time

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The jump-log plus escape integrand is the occupied-source multiple of the scalar Poisson
discrimination whenever candidate and reference rates have the same directed support. -/
theorem finiteStateTimeDependentMarkovJumpLogRatio_mul_rate_add_escapeDifference_eq
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (hSupport : FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport
      rates referenceRates)
    (time : ℝ) (source target : State) (density : ℝ) :
    finiteStateTimeDependentMarkovJumpLogRatioWeight
          rates referenceRates source target time * density *
          (rates.rate time source target : ℝ) +
        density * (referenceRates.rate time source target : ℝ) -
        density * (rates.rate time source target : ℝ) =
      density * poissonRateDiscrimination
        (rates.rate time source target : ℝ)
        (referenceRates.rate time source target : ℝ) := by
  by_cases hReference : referenceRates.rate time source target = 0
  · have hCandidate : rates.rate time source target = 0 :=
      (hSupport time source target).mpr hReference
    simp [finiteStateTimeDependentMarkovJumpLogRatioWeight,
      poissonRateDiscrimination, hReference, hCandidate]
  · unfold finiteStateTimeDependentMarkovJumpLogRatioWeight poissonRateDiscrimination
    ring

/-- Real time integral of the instantaneous Poisson rate discrimination. -/
noncomputable def finiteStateTimeDependentMarkovExpectedPoissonRateAction
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) : ℝ :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ∫ time,
      (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time transition.1.1).toReal *
        poissonRateDiscrimination
          (rates.rate time transition.1.1 transition.1.2 : ℝ)
          (referenceRates.rate time transition.1.1 transition.1.2 : ℝ)
      ∂finiteOpenIntervalVolume (duration : ℝ)

/-- The occupation-weighted escape mean is exactly the sum of the occupied-source intensities
over the finite ordered off-diagonal family. -/
theorem integral_sum_finiteStateTimeDependentMarkovMeanDensityAt_mul_escapeRate_eq
    (initial : PMF State)
    (sourceRates testedRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    (∫ time,
        ∑ state,
          finiteStateTimeDependentMarkovMeanDensityAt initial sourceRates duration time state *
            (testedRates.escapeRate time state : ℝ)
        ∂finiteOpenIntervalVolume (duration : ℝ)) =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ∫ time,
          (finiteStateTimeDependentMarkovEndpointProbability
              initial sourceRates time transition.1.1).toReal *
            (testedRates.rate time transition.1.1 transition.1.2 : ℝ)
          ∂finiteOpenIntervalVolume (duration : ℝ) := by
  have hEdgeIntegrable
      (transition : FiniteStateOrderedOffDiagonalTransition State) :
      MeasureTheory.Integrable
        (fun time ↦
          (finiteStateTimeDependentMarkovEndpointProbability
              initial sourceRates time transition.1.1).toReal *
            (testedRates.rate time transition.1.1 transition.1.2 : ℝ))
        (finiteOpenIntervalVolume (duration : ℝ)) := by
    have hEndpointMeasurable : Measurable fun time ↦
        (finiteStateTimeDependentMarkovEndpointProbability
          initial sourceRates time transition.1.1).toReal := by
      unfold finiteStateTimeDependentMarkovEndpointProbability
      have hSurvival : Measurable fun time : ℝ ↦
          ENNReal.ofReal
            (Real.exp (-((sourceRates.uniformizationRate : ℝ) * time))) := by
        fun_prop
      exact (hSurvival.mul
        (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
          initial sourceRates transition.1.1)).ennreal_toReal
    have hMeasurable : Measurable fun time ↦
        (finiteStateTimeDependentMarkovEndpointProbability
            initial sourceRates time transition.1.1).toReal *
          (testedRates.rate time transition.1.1 transition.1.2 : ℝ) :=
      hEndpointMeasurable.mul
        (testedRates.measurable_rate transition.1.1 transition.1.2).coe_nnreal_real
    apply MeasureTheory.Integrable.of_bound hMeasurable.aestronglyMeasurable
      (testedRates.uniformizationRate : ℝ)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with time hTime
    have hEndpointLeOne :
        (finiteStateTimeDependentMarkovEndpointProbability
          initial sourceRates time transition.1.1).toReal ≤ 1 := by
      have hCoordinate :
          finiteStateTimeDependentMarkovEndpointProbability
              initial sourceRates time transition.1.1 ≤
            ∑ observed : State,
              finiteStateTimeDependentMarkovEndpointProbability
                initial sourceRates time observed :=
        Finset.single_le_sum (fun observed _hObserved ↦ zero_le)
          (Finset.mem_univ transition.1.1)
      rw [sum_finiteStateTimeDependentMarkovEndpointProbability
        initial sourceRates time hTime.1.le] at hCoordinate
      exact (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.one_ne_top hCoordinate)
        ENNReal.one_ne_top).2 hCoordinate
    have hRateLe : testedRates.rate time transition.1.1 transition.1.2 ≤
        testedRates.uniformizationRate := by
      exact (Finset.single_le_sum (fun state _hState ↦ zero_le)
        (Finset.mem_erase.mpr ⟨transition.2.symm,
          Finset.mem_univ transition.1.2⟩)).trans
        (testedRates.escapeRate_le_uniformizationRate time transition.1.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 1 * (testedRates.uniformizationRate : ℝ) := by
        gcongr
      _ = _ := one_mul _
  rw [← MeasureTheory.integral_finsetSum Finset.univ fun transition _hTransition ↦
    hEdgeIntegrable transition]
  apply MeasureTheory.integral_congr_ae
  have hDensity : ∀ᵐ time ∂finiteOpenIntervalVolume (duration : ℝ), ∀ state,
      finiteStateTimeDependentMarkovMeanDensityAt initial sourceRates duration time state =
        (finiteStateTimeDependentMarkovEndpointProbability
          initial sourceRates time state).toReal := by
    rw [MeasureTheory.ae_all_iff]
    exact fun state ↦
      ae_finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointProbability
        initial sourceRates duration state
  filter_upwards [hDensity] with time hTime
  simp_rw [hTime]
  calc
    (∑ state,
          (finiteStateTimeDependentMarkovEndpointProbability
            initial sourceRates time state).toReal *
          (testedRates.escapeRate time state : ℝ)) =
      ∑ source, ∑ target : {target : State // target ≠ source},
        (finiteStateTimeDependentMarkovEndpointProbability
            initial sourceRates time source).toReal *
          (testedRates.rate time source target : ℝ) := by
      apply Finset.sum_congr rfl
      intro source _hSource
      rw [FiniteStateTimeDependentMarkovRate.escapeRate, NNReal.coe_sum,
        Finset.mul_sum]
      rw [Finset.sum_subtype (s := Finset.univ.erase source)
        (p := fun target : State ↦ target ≠ source) (by intro target; simp)]
    _ = _ :=
      sum_outgoingTransition_eq_sum_orderedOffDiagonalTransition
        (fun transition ↦
          (finiteStateTimeDependentMarkovEndpointProbability
              initial sourceRates time transition.1.1).toReal *
            (testedRates.rate time transition.1.1 transition.1.2 : ℝ))

/-- The generic complete expected jump action is exactly its source-density-weighted Poisson
rate action under a common directed support and a uniform jump-log bound. -/
theorem finiteStateTimeDependentMarkovExpectedJumpLogAction_eq_expectedPoissonRateAction
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal)
    (hSupport : FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport
      rates referenceRates)
    {jumpLogAbsoluteBound : ℝ}
    (hJumpLogAbsoluteBoundNonnegative : 0 ≤ jumpLogAbsoluteBound)
    (hJumpLogAbsoluteBound : ∀ time source target,
      source ≠ target →
      |finiteStateTimeDependentMarkovJumpLogRatioWeight
        rates referenceRates source target time| ≤ jumpLogAbsoluteBound) :
    finiteStateTimeDependentMarkovExpectedJumpLogAction
        initial rates referenceRates duration =
      finiteStateTimeDependentMarkovExpectedPoissonRateAction
        initial rates referenceRates duration := by
  have hCandidateIntegrable
      (transition : FiniteStateOrderedOffDiagonalTransition State) :
      MeasureTheory.Integrable
        (fun time ↦
          (finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1).toReal *
            (rates.rate time transition.1.1 transition.1.2 : ℝ))
        (finiteOpenIntervalVolume (duration : ℝ)) := by
    have hWeighted :=
      integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
        initial rates duration transition.2 (fun _time ↦ (1 : NNReal)) measurable_const
        (show (0 : ℝ) ≤ 1 by norm_num) (fun _time ↦ by norm_num)
    simpa only [finiteOpenIntervalVolume, NNReal.coe_one, one_mul] using! hWeighted
  have hReferenceIntegrable
      (transition : FiniteStateOrderedOffDiagonalTransition State) :
      MeasureTheory.Integrable
        (fun time ↦
          (finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1).toReal *
            (referenceRates.rate time transition.1.1 transition.1.2 : ℝ))
        (finiteOpenIntervalVolume (duration : ℝ)) := by
    have hEndpointMeasurable : Measurable fun time ↦
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time transition.1.1).toReal := by
      unfold finiteStateTimeDependentMarkovEndpointProbability
      have hSurvival : Measurable fun time : ℝ ↦
          ENNReal.ofReal
            (Real.exp (-((rates.uniformizationRate : ℝ) * time))) := by
        fun_prop
      exact (hSurvival.mul
        (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
          initial rates transition.1.1)).ennreal_toReal
    have hMeasurable : Measurable fun time ↦
        (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time transition.1.1).toReal *
          (referenceRates.rate time transition.1.1 transition.1.2 : ℝ) :=
      hEndpointMeasurable.mul
        (referenceRates.measurable_rate transition.1.1 transition.1.2).coe_nnreal_real
    apply MeasureTheory.Integrable.of_bound hMeasurable.aestronglyMeasurable
      (referenceRates.uniformizationRate : ℝ)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with time hTime
    have hEndpointLeOne :
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time transition.1.1).toReal ≤ 1 := by
      have hCoordinate :
          finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1 ≤
            ∑ observed : State,
              finiteStateTimeDependentMarkovEndpointProbability
                initial rates time observed :=
        Finset.single_le_sum (fun observed _hObserved ↦ zero_le)
          (Finset.mem_univ transition.1.1)
      rw [sum_finiteStateTimeDependentMarkovEndpointProbability
        initial rates time hTime.1.le] at hCoordinate
      exact (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.one_ne_top hCoordinate)
        ENNReal.one_ne_top).2 hCoordinate
    have hRateLe : referenceRates.rate time transition.1.1 transition.1.2 ≤
        referenceRates.uniformizationRate := by
      exact (Finset.single_le_sum (fun state _hState ↦ zero_le)
        (Finset.mem_erase.mpr ⟨transition.2.symm,
          Finset.mem_univ transition.1.2⟩)).trans
        (referenceRates.escapeRate_le_uniformizationRate time transition.1.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 1 * (referenceRates.uniformizationRate : ℝ) := by
          gcongr
      _ = _ := one_mul _
  have hJumpIntegrable
      (transition : FiniteStateOrderedOffDiagonalTransition State) :
      MeasureTheory.Integrable
        (fun time ↦
          finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
              transition.1.1 transition.1.2 time *
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1).toReal *
            (rates.rate time transition.1.1 transition.1.2 : ℝ))
        (finiteOpenIntervalVolume (duration : ℝ)) := by
    simpa only [finiteOpenIntervalVolume] using!
      integrableOn_realWeight_mul_endpointProbability_mul_rate
        initial rates duration transition.2
        (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
          transition.1.1 transition.1.2)
        (measurable_finiteStateTimeDependentMarkovJumpLogRatioWeight
          rates referenceRates transition.1.1 transition.1.2)
        hJumpLogAbsoluteBoundNonnegative
        (fun time ↦ hJumpLogAbsoluteBound time transition.1.1 transition.1.2 transition.2)
  unfold finiteStateTimeDependentMarkovExpectedJumpLogAction
    finiteStateTimeDependentMarkovDirectedTransitionWeightMean
    finiteStateTimeDependentMarkovExpectedPoissonRateAction
  rw [integral_sum_finiteStateTimeDependentMarkovMeanDensityAt_mul_escapeRate_eq
      initial rates referenceRates duration,
    integral_sum_finiteStateTimeDependentMarkovMeanDensityAt_mul_escapeRate_eq
      initial rates rates duration,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp only [finiteOpenIntervalVolume]
  apply Finset.sum_congr rfl
  intro transition _hTransition
  have hJump := hJumpIntegrable transition
  have hReference := hReferenceIntegrable transition
  have hCandidate := hCandidateIntegrable transition
  simp only [finiteOpenIntervalVolume] at hJump hReference hCandidate
  rw [← MeasureTheory.integral_add hJump hReference,
    ]
  have hSum : MeasureTheory.Integrable
      (fun time ↦
        finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
              transition.1.1 transition.1.2 time *
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1).toReal *
            (rates.rate time transition.1.1 transition.1.2 : ℝ) +
          (finiteStateTimeDependentMarkovEndpointProbability
              initial rates time transition.1.1).toReal *
            (referenceRates.rate time transition.1.1 transition.1.2 : ℝ))
      (MeasureTheory.volume.restrict (Ioo 0 (duration : ℝ))) := by
    simpa only [Pi.add_apply] using! hJump.add hReference
  rw [← MeasureTheory.integral_sub hSum hCandidate]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with time
  exact finiteStateTimeDependentMarkovJumpLogRatio_mul_rate_add_escapeDifference_eq
    rates referenceRates hSupport time transition.1.1 transition.1.2
    (finiteStateTimeDependentMarkovEndpointProbability
      initial rates time transition.1.1).toReal

/-- The finite canonical Renger expectation is exactly the source-density-weighted Poisson rate
action against the unchanged homogeneous generator. -/
theorem
  rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction_eq_expectedPoissonRateAction
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initial : PMF State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
        generator path index initial =
      finiteStateTimeDependentMarkovExpectedPoissonRateAction
        initial
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
  exact
    finiteStateTimeDependentMarkovExpectedJumpLogAction_eq_expectedPoissonRateAction
      initial
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
        generator path.1 index)
      (jumpLogAbsoluteBound :=
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
          generator index)
      (by
        unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
        positivity)
      (fun time source target hOffDiagonal ↦ by
        change
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
            generator path.1 index source target time| ≤
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
              generator index
        exact
          abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight_le
            generator path.1 index source target time)

/-- Ordered target-density flow generated by one canonical positive rate chart. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ}
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (index : ℕ) (time : ℝ) (source target : State) : NNReal :=
  rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path index).rate time source target

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every canonical target-generated flow coordinate is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ}
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (index : ℕ) (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
        generator path index time source target := by
  exact
    ((measurable_pi_apply source).comp
      (measurable_rengerDirectionalFlowHybridBVMeasurableDensityAt path)).mul
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).measurable_rate source target)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a finite-action target, the canonical generated flow is almost everywhere its truncated
target flow plus the explicit vanishing reference-floor flow. -/
theorem ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_eq
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
          generator path.1 index time source target =
        rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target +
          (1 / ((index : NNReal) + 1)) *
            rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_truncatedTargetRate
      generator hDuration path hDynamicRate index source target] with time hSupported
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
    rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
  rw [rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate, hSupported]
  ring

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every canonical target-generated ordered flow converges almost everywhere to the exact target
flow on a finite-action off-diagonal channel. -/
theorem ae_tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_atTop
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      Tendsto
        (fun index : ℕ ↦
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
            generator path.1 index time source target)
        atTop
        (nhds (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target)) := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_eq
      generator hDuration path hDynamicRate 0 source target,
    ae_tendsto_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
      generator hDuration path hDynamicRate hOffDiagonal,
    MeasureTheory.ae_all_iff.2 fun index ↦
      ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_eq
        generator hDuration path hDynamicRate index source target] with
      time _hZero hTruncated hFormula
  have hReferenceFloor : Tendsto
      (fun index : ℕ ↦
        (1 / ((index : NNReal) + 1)) *
          rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target)
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal)).mul
        (tendsto_const_nhds (x :=
          rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target))
  have hSum : Tendsto
      (fun index : ℕ ↦
        rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target +
          (1 / ((index : NNReal) + 1)) *
            rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target)
      atTop
      (nhds (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target)) := by
    simpa only [add_zero] using hTruncated.add hReferenceFloor
  apply hSum.congr'
  filter_upwards [] with index
  exact (hFormula index).symm

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Canonical generated target flow is dominated by exact target flow plus one reference expected
flow, uniformly in the chart index. -/
theorem ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_le
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
          generator path.1 index time source target ≤
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target +
          rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_eq
      generator hDuration path hDynamicRate index source target] with time hFormula
  rw [hFormula]
  apply add_le_add
  · exact rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
      path.1 index time hOffDiagonal
  · apply mul_le_of_le_one_left (zero_le)
    rw [div_le_one (by positivity : (0 : NNReal) < (index : NNReal) + 1)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg index)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Canonical generated one-channel costs converge almost everywhere to exact target cost. -/
theorem ae_tendsto_rengerExtendedPoissonRateCost_canonicalPositiveTargetGeneratedFlow_atTop
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      Tendsto
        (fun index : ℕ ↦
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
              generator path.1 index time source target)
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
    ae_tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_atTop
      generator hDuration path hDynamicRate hOffDiagonal,
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_expectedFlow_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal,
    MeasureTheory.ae_all_iff.2 fun index ↦
      ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_le
        generator hDuration path hDynamicRate index hOffDiagonal] with
      time hFlowTendsto hZeroExpected hGeneratedLe
  let expected := rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    generator path.1 time source target
  let targetFlow := rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
    path.1 time source target
  by_cases hExpected : expected = 0
  · have hTargetFlow : targetFlow = 0 := hZeroExpected hExpected
    have hGeneratedFlow (index : ℕ) :
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
          generator path.1 index time source target = 0 := by
      exact le_zero_iff.mp <| (hGeneratedLe index).trans_eq <| by
        simp [expected, targetFlow, hExpected, hTargetFlow]
    simp [expected, targetFlow, hExpected, hTargetFlow, hGeneratedFlow,
      rengerExtendedPoissonRateCost_zero_zero]
  · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
    have hExpectedRealPositive : 0 < (expected : ℝ) := by
      exact_mod_cast hExpectedPositive
    change Tendsto
      (fun index : ℕ ↦
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
            generator path.1 index time source target) expected)
      atTop (nhds (rengerExtendedPoissonRateCost targetFlow expected))
    simp_rw [rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive]
    apply ENNReal.tendsto_ofReal
    exact (continuous_poissonRateDiscrimination_left
      hExpectedRealPositive).continuousAt.tendsto.comp
      (NNReal.tendsto_coe.2 hFlowTendsto)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every canonical generated one-channel cost is dominated by the integrable sum of expected
flow, exact target cost, and exact target flow. -/
theorem ae_rengerExtendedPoissonRateCost_canonicalPositiveTargetGeneratedFlow_le
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
            generator path.1 index time source target)
          (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target) ≤
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target : ENNReal) +
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target)
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target) +
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue_le
      generator hDuration path hDynamicRate index hOffDiagonal,
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_expectedFlow_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal] with
      time hGeneratedLe hZeroExpected
  let generatedFlow :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
      generator path.1 index time source target
  let targetFlow := rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
    path.1 time source target
  let expected := rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    generator path.1 time source target
  by_cases hExpected : expected = 0
  · have hTargetFlow : targetFlow = 0 := hZeroExpected hExpected
    have hGeneratedFlow : generatedFlow = 0 :=
      le_zero_iff.mp <| hGeneratedLe.trans_eq <| by
        simp [expected, targetFlow, hExpected, hTargetFlow]
    simp [generatedFlow, targetFlow, expected, hExpected, hTargetFlow, hGeneratedFlow,
      rengerExtendedPoissonRateCost_zero_zero]
  · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
    have hExpectedRealPositive : 0 < (expected : ℝ) := by
      exact_mod_cast hExpectedPositive
    have hGeneratedRealLe : (generatedFlow : ℝ) ≤ (targetFlow + expected : NNReal) := by
      exact_mod_cast hGeneratedLe
    have hFirst := poissonRateDiscrimination_le_reference_add_upperDiscrimination
      (show 0 ≤ (generatedFlow : ℝ) by positivity) hGeneratedRealLe hExpectedRealPositive
    rw [rengerExtendedPoissonRateCost_of_expected_pos generatedFlow hExpectedPositive]
    calc
      ENNReal.ofReal (poissonRateDiscrimination (generatedFlow : ℝ) (expected : ℝ)) ≤
          (expected : ENNReal) +
            rengerExtendedPoissonRateCost (targetFlow + expected) expected := by
        rw [rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive,
          ← ENNReal.ofReal_coe_nnreal]
        rw [← ENNReal.ofReal_add hExpectedRealPositive.le
          (poissonRateDiscrimination_nonneg (by positivity) hExpectedRealPositive)]
        exact ENNReal.ofReal_le_ofReal hFirst
      _ ≤ (expected : ENNReal) +
            (rengerExtendedPoissonRateCost targetFlow expected + (targetFlow : ENNReal)) := by
        gcongr
        exact rengerExtendedPoissonRateCost_add_expected_le targetFlow expected
      _ = _ := by ac_rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Dominated convergence recovers the exact integrated target channel cost from canonical
positive generated target flows. -/
theorem tendsto_lintegral_rengerExtendedPoissonRateCost_canonicalPositiveTargetGeneratedFlow_atTop
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    Tendsto
      (fun index : ℕ ↦
        ∫⁻ time,
          rengerExtendedPoissonRateCost
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
              generator path.1 index time source target)
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
  let targetCost : ℝ → ENNReal := fun time ↦
    rengerExtendedPoissonRateCost
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target)
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target)
  let costBound : ℝ → ENNReal := fun time ↦
    (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 time source target : ENNReal) +
      targetCost time +
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target : ENNReal)
  apply MeasureTheory.tendsto_lintegral_of_dominated_convergence costBound
  · intro index
    exact measurable_rengerExtendedPoissonRateCost.comp <|
      (measurable_rengerDirectionalFlowHybridBVCanonicalPositiveTargetGeneratedFlowValue
        generator path.1 index source target).prodMk
      (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
        generator path.1 source target)
  · intro index
    exact ae_rengerExtendedPoissonRateCost_canonicalPositiveTargetGeneratedFlow_le
      generator hDuration path hDynamicRate index hOffDiagonal
  · have hExpectedFinite :=
      lintegral_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt_ne_top
        generator hDuration path source target
    have hTargetCostFinite :=
      lintegral_rengerExtendedPoissonRateCost_measurableTargetFlow_ne_top
        generator hDuration path hDynamicRate hOffDiagonal
    have hTargetFlowFinite :=
      lintegral_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_ne_top
        generator hDuration path hDynamicRate hOffDiagonal
    change (∫⁻ time,
      (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target : ENNReal) +
        targetCost time +
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target : ENNReal)
      ∂finiteOpenIntervalVolume duration) ≠ ⊤
    rw [MeasureTheory.lintegral_add_left]
    · rw [MeasureTheory.lintegral_add_left]
      · exact ENNReal.add_ne_top.2
          ⟨ENNReal.add_ne_top.2 ⟨hExpectedFinite, hTargetCostFinite⟩,
            hTargetFlowFinite⟩
      · exact
          (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 source target).coe_nnreal_ennreal
    · exact
        ((measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 source target).coe_nnreal_ennreal.add
          (measurable_rengerExtendedPoissonRateCost.comp <|
            (measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 source target).prodMk
            (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 source target)))
  · exact
      ae_tendsto_rengerExtendedPoissonRateCost_canonicalPositiveTargetGeneratedFlow_atTop
        generator hDuration path hDynamicRate hOffDiagonal

end

end FiniteMarkovProcesses.InformationTheory
