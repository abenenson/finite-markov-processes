/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceFlowConvergence

/-!
# Source-mean path convergence for positive Renger targets

This module converts ordered source-flow convergence into density-drift, derivative-variation,
and complete hybrid source-mean path convergence.
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
  {duration : ℝ}
omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The source-mean density drift error is the divergence of the ordered source-flow error and is
therefore controlled by twice its complete finite-state `L1` mass. -/
theorem abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceDensityDriftError_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (state : State) :
    |finiteStateTimeDependentMarkovEndpointProbabilityDrift
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          time state -
        rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state| ≤
      2 * ∑ source, ∑ target,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
          generator path index time source target| := by
  rw [finiteStateTimeDependentMarkovEndpointProbabilityDrift_eq_flowDivergence,
    rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence]
  have hDifference :
      finiteStateFlowDivergence
            (fun source target ↦
              (finiteStateTimeDependentMarkovEndpointProbability
                (rengerDirectionalFlowHybridBVTargetInitialPMF path)
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator path.1 index)
                time source).toReal *
                ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator path.1 index).rate time source target : ℝ))
            state -
          finiteStateFlowDivergence
            (rengerDirectionalFlowHybridBVRawFlowDerivativeValue path.1 time) state =
        finiteStateFlowDivergence
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
            generator path index time) state := by
    unfold finiteStateFlowDivergence
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hDifference]
  exact abs_finiteStateFlowDivergence_le_two_mul_sum_abs
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
      generator path index time) state

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete-interval density-drift error is bounded by twice the total integrated
source-flow error. -/
theorem lintegral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceDensityDriftError_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (state : State) :
    (∫⁻ time,
      ENNReal.ofReal
        |finiteStateTimeDependentMarkovEndpointProbabilityDrift
            (rengerDirectionalFlowHybridBVTargetInitialPMF path)
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index)
            time state -
          rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state|
      ∂finiteOpenIntervalVolume duration) ≤
      2 *
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
          generator path index := by
  have hMeasurable (source target : State) :
      AEMeasurable
        (fun time ↦ ENNReal.ofReal
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
            generator path index time source target|)
        (finiteOpenIntervalVolume duration) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
        generator hDuration path index source target).norm.aestronglyMeasurable.aemeasurable
          |>.ennreal_ofReal
  calc
    _ ≤ ∫⁻ time,
        2 * ∑ source, ∑ target,
          ENNReal.ofReal
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
              generator path index time source target|
        ∂finiteOpenIntervalVolume duration := by
      apply MeasureTheory.lintegral_mono
      intro time
      calc
        ENNReal.ofReal
            |finiteStateTimeDependentMarkovEndpointProbabilityDrift
                (rengerDirectionalFlowHybridBVTargetInitialPMF path)
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator path.1 index)
                time state -
              rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state| ≤
          ENNReal.ofReal
            (2 * ∑ source, ∑ target,
              |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
                generator path index time source target|) :=
          ENNReal.ofReal_le_ofReal <|
            abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceDensityDriftError_le
              generator path index time state
        _ = 2 * ∑ source, ∑ target,
            ENNReal.ofReal
              |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
                generator path index time source target| := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_sum_of_nonneg]
          · apply congrArg
            apply Finset.sum_congr rfl
            intro source _hSource
            rw [ENNReal.ofReal_sum_of_nonneg]
            exact fun target _hTarget ↦ abs_nonneg _
          · exact fun source _hSource ↦
              Finset.sum_nonneg fun target _hTarget ↦ abs_nonneg _
    _ = _ := by
      unfold
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
      have hIntegral :
          (∫⁻ time,
            ∑ source, ∑ target,
              ENNReal.ofReal
                |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
                  generator path index time source target|
            ∂finiteOpenIntervalVolume duration) =
            ∑ source, ∑ target,
              ∫⁻ time,
                ENNReal.ofReal
                |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
                  generator path index time source target|
                ∂finiteOpenIntervalVolume duration := by
        calc
          _ = ∑ source,
              ∫⁻ time, ∑ target,
                ENNReal.ofReal
                  |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
                    generator path index time source target|
                ∂finiteOpenIntervalVolume duration := by
            simpa using
              (MeasureTheory.lintegral_finsetSum' (μ := finiteOpenIntervalVolume duration)
                Finset.univ
                (fun source _hSource ↦
                  Finset.aemeasurable_sum Finset.univ
                    (fun target _hTarget ↦ hMeasurable source target)))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro source _hSource
            simpa using
              (MeasureTheory.lintegral_finsetSum' (μ := finiteOpenIntervalVolume duration)
                Finset.univ (fun target _hTarget ↦ hMeasurable source target))
      rw [MeasureTheory.lintegral_const_mul' _ _ (by simp), hIntegral]

/-- Every density-derivative coordinate of the canonical physical source converges in
complete-interval `L1` to a positive reference-perturbed target derivative. -/
theorem
  tendsto_lintegral_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceDensityDriftError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (state : State) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    Tendsto
      (fun index : ℕ ↦
        ∫⁻ time,
          ENNReal.ofReal
            |finiteStateTimeDependentMarkovEndpointProbabilityDrift
                (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator perturbed.1 index)
                time state -
              rengerDirectionalFlowHybridBVTargetFlowDivergence
                perturbed.1 time state|
          ∂finiteOpenIntervalVolume duration)
      atTop (nhds 0) := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  have hTotal :=
    tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetTotalIntegratedSourceFlowError_atTop
      generator hDuration path hDynamicRate mixingWeight hMixingWeight
      hMixingWeightLeOne hInitial
  have hUpper :
      Tendsto
        (fun index : ℕ ↦
          2 *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
              generator perturbed index)
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hTotal (Or.inr (by simp))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper
  · exact Filter.Eventually.of_forall fun _index ↦ zero_le
  · exact Filter.Eventually.of_forall fun index ↦
      lintegral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceDensityDriftError_le
        generator hDuration perturbed index state

/-- The complete derivative variation of the canonical physical source mean relative to its
positive reference-perturbed target vanishes.  This packages the density and every ordered-flow
estimate into the exact analytic premise required by the hybrid topology. -/
theorem
  tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceMeanDifferenceDerivativeTotalVariation_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    Tendsto
      (fun index : ℕ ↦
        finiteIntervalHybridBVDerivativeTotalVariation
          (FiniteIntervalHybridBVPath.linearCombination 1 (-1)
            (finiteStateTimeDependentMarkovMeanHybridBVPath
              (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
              (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                generator perturbed.1 index)
              ⟨duration, hDuration.le⟩)
            perturbed.1))
      atTop (nhds 0) := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  let sourcePath (index : ℕ) :=
    finiteStateTimeDependentMarkovMeanHybridBVPath
      (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator perturbed.1 index)
      ⟨duration, hDuration.le⟩
  let difference (index : ℕ) :=
    FiniteIntervalHybridBVPath.linearCombination 1 (-1) (sourcePath index) perturbed.1
  have hSourceAbsolutelyContinuous (index : ℕ) :
      (sourcePath index).HasAbsolutelyContinuousDerivative := by
    exact finiteStateTimeDependentMarkovMeanHybridBVPath_hasAbsolutelyContinuousDerivative
      (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator perturbed.1 index)
      ⟨duration, hDuration.le⟩
  have hDifferenceAbsolutelyContinuous (index : ℕ) :
      (difference index).HasAbsolutelyContinuousDerivative := by
    exact FiniteIntervalHybridBVPath.linearCombination_hasAbsolutelyContinuousDerivative
      1 (-1) (sourcePath index) perturbed.1
      (hSourceAbsolutelyContinuous index) perturbed.2.absolutelyContinuousDerivative
  have hCoordinate (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
      Tendsto
        (fun index : ℕ ↦
          ∫⁻ time, ENNReal.ofReal |(difference index).derivativeDensity coordinate time|
            ∂finiteOpenIntervalVolume duration)
        atTop (nhds 0) := by
    cases coordinate with
    | inl state =>
        have hTarget : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
            perturbed.1.derivativeDensity (Sum.inl state) time =
              rengerDirectionalFlowHybridBVTargetFlowDivergence perturbed.1 time state :=
          perturbed.2.continuityEquationAE.mono fun time hTime ↦ by
            simpa only [rengerDirectionalFlowHybridBVDensityDerivative,
              rengerDirectionalFlowHybridBVTargetFlowDivergence] using hTime state
        have hIntegralEquality (index : ℕ) :
            (∫⁻ time,
                ENNReal.ofReal
                  |(difference index).derivativeDensity (Sum.inl state) time|
                ∂finiteOpenIntervalVolume duration) =
              ∫⁻ time,
                ENNReal.ofReal
                  |finiteStateTimeDependentMarkovEndpointProbabilityDrift
                      (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
                      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                        generator perturbed.1 index)
                      time state -
                    rengerDirectionalFlowHybridBVTargetFlowDivergence
                      perturbed.1 time state|
                ∂finiteOpenIntervalVolume duration := by
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [
            FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
              1 (-1) (sourcePath index) perturbed.1
              (hSourceAbsolutelyContinuous index)
              perturbed.2.absolutelyContinuousDerivative (Sum.inl state),
            ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
              (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
              (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                generator perturbed.1 index)
              ⟨duration, hDuration.le⟩ (Sum.inl state),
            hTarget] with time hDifference hSource hTargetTime
          rw [show difference index =
              FiniteIntervalHybridBVPath.linearCombination 1 (-1)
                (sourcePath index) perturbed.1 by rfl,
            hDifference]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul]
          rw (transparency := .default) [show sourcePath index =
              finiteStateTimeDependentMarkovMeanHybridBVPath
                (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator perturbed.1 index)
                ⟨duration, hDuration.le⟩ by rfl,
            hSource, hTargetTime]
          simp [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
            sub_eq_add_neg]
        simp_rw [hIntegralEquality]
        exact
          tendsto_lintegral_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceDensityDriftError_atTop
            generator hDuration path hDynamicRate mixingWeight hMixingWeight
            hMixingWeightLeOne hInitial state
    | inr edge =>
        have hIntegralEquality (index : ℕ) :
            (∫⁻ time,
                ENNReal.ofReal
                  |(difference index).derivativeDensity (Sum.inr edge) time|
                ∂finiteOpenIntervalVolume duration) =
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
                generator perturbed index edge.val.1 edge.val.2 := by
          unfold
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards [
            FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
              1 (-1) (sourcePath index) perturbed.1
              (hSourceAbsolutelyContinuous index)
              perturbed.2.absolutelyContinuousDerivative (Sum.inr edge),
            ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
              (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
              (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                generator perturbed.1 index)
              ⟨duration, hDuration.le⟩ (Sum.inr edge)] with time hDifference hSource
          rw [show difference index =
              FiniteIntervalHybridBVPath.linearCombination 1 (-1)
                (sourcePath index) perturbed.1 by rfl,
            hDifference]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, neg_one_mul]
          rw [show sourcePath index =
              finiteStateTimeDependentMarkovMeanHybridBVPath
                (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                  generator perturbed.1 index)
                ⟨duration, hDuration.le⟩ by rfl,
            hSource]
          simp [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError,
            rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
            rengerDirectionalFlowHybridBVFlowDerivative, edge.property]
          simp only [sub_eq_add_neg]
          rfl
        simp_rw [hIntegralEquality]
        exact
          tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetIntegratedSourceFlowError_atTop
            generator hDuration path hDynamicRate mixingWeight hMixingWeight
            hMixingWeightLeOne hInitial edge.val.1 edge.val.2
  have hSum := tendsto_finsetSum Finset.univ fun coordinate _hCoordinate ↦
    hCoordinate coordinate
  change Tendsto
    (fun index : ℕ ↦ finiteIntervalHybridBVDerivativeTotalVariation (difference index))
    atTop (nhds 0)
  simp_rw [finiteIntervalHybridBVDerivativeTotalVariation_eq_sum_lintegral_ofReal_abs
    (difference _) (hDifferenceAbsolutelyContinuous _)]
  simpa only [Finset.sum_const_zero] using! hSum

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A mean source initialized by a representation target's recovered PMF has exactly the same
hybrid initial trace as that target, independently of its time-dependent rates. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_targetInitialTrace_eq
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (rates : FiniteStateTimeDependentMarkovRate State) :
    (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) rates
        ⟨duration, hDuration.le⟩).initialTrace = path.1.initialTrace := by
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
    (show 0 < (⟨duration, hDuration.le⟩ : NNReal) by exact_mod_cast hDuration)]
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  cases coordinate with
  | inl state =>
      change (rengerDirectionalFlowHybridBVTargetInitialPMF path state).toReal =
        path.1.initialTrace (Sum.inl state)
      rw [rengerDirectionalFlowHybridBVTargetInitialPMF_apply, ENNReal.coe_toReal]
      exact Real.coe_toNNReal _ (path.2.initialDensityNonnegative state)
  | inr transition =>
      change 0 = path.1.initialTrace (Sum.inr transition)
      exact (path.2.cumulativeFlowInitiallyZero transition).symm

/-- Canonical finite-state physical source means converge in the exact hybrid-BV topology to
every positive reference-evolution perturbation of a finite-rate target.  This is the complete
carrier-coherence theorem: it controls strong path `L1`, all directional-flow derivative tests,
and the recovered initial trace without identifying equal actions with equal carriers. -/
theorem
  tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceMeanHybridBVPath_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    Tendsto
      (fun index : ℕ ↦
        finiteStateTimeDependentMarkovMeanHybridBVPath
          (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator perturbed.1 index)
          ⟨duration, hDuration.le⟩)
      atTop (nhds perturbed.1) := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  apply
    FiniteIntervalHybridBVPath.tendsto_of_initialTrace_eq_of_tendsto_differenceDerivativeTotalVariation
      hDuration
  · intro index
    exact finiteStateTimeDependentMarkovMeanHybridBVPath_targetInitialTrace_eq
      hDuration perturbed
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator perturbed.1 index)
  · exact
      tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceMeanDifferenceDerivativeTotalVariation_atTop
        generator hDuration path hDynamicRate mixingWeight hMixingWeight
        hMixingWeightLeOne hInitial

end


end FiniteMarkovProcesses.InformationTheory
