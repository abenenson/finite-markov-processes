/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVReferenceEvolutionPerturbation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanHybridBVPath

/-!
# Hybrid-BV path of the unchanged reference evolution

The target-derived initial PMF is evolved under the unchanged homogeneous reference generator and
packaged as a genuine admissible Renger representation path.  Every density, cumulative-flow,
derivative, and boundary field is inherited from the source-neutral arbitrary-PMF mean path.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- Genuine hybrid-BV path of the unchanged reference evolution from the target's own initial
PMF. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceEvolutionPath
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    RengerDirectionalFlowHybridBVPath State duration :=
  finiteStateTimeDependentMarkovMeanHybridBVPath
    (rengerDirectionalFlowHybridBVTargetInitialPMF path)
    generator.toTimeDependentMarkovRate
    ⟨duration, hDuration.le⟩

/-- The reference path's selected density coordinate is the exact endpoint evolution. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (state : State) :
    rengerDirectionalFlowHybridBVDensityValue
        (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path) time state =
      rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
        generator path time state := by
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVReferenceEvolutionPath
    rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
  rw (transparency := .default)
    [finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
    _ _ (⟨duration, hDuration.le⟩ : ℝ≥0)
      ⟨hTimeNonnegative, by exact_mod_cast hTimeDuration⟩]
  change finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate (⟨duration, hDuration.le⟩ : ℝ≥0)
      time (Sum.inl state) = _
  exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
    _ _ (⟨duration, hDuration.le⟩ : ℝ≥0) hTimeNonnegative
      (by exact_mod_cast hTimeDuration.le) state

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every selected cumulative reference flow is nonnegative on physical time. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPath_cumulativeFlowValue_nonnegative
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
      time transition := by
  unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rengerDirectionalFlowHybridBVReferenceEvolutionPath
  rw (transparency := .default)
    [finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
    _ _ (⟨duration, hDuration.le⟩ : ℝ≥0)
      ⟨hTimeNonnegative, by exact_mod_cast hTimeDuration⟩]
  exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow_nonnegative
    _ _ (⟨duration, hDuration.le⟩ : ℝ≥0) hTimeNonnegative transition

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The reference path's flow derivative is the occupied-source reference intensity almost
everywhere. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivative_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ transition,
        rengerDirectionalFlowHybridBVFlowDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
            time transition =
          rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue
            generator path time transition.val.1 transition.val.2 := by
  have hCoordinate (transition : FiniteStateOrderedOffDiagonalTransition State) :=
    ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      (Sum.inr transition)
  rw [ae_all_iff]
  intro transition
  simpa only [rengerDirectionalFlowHybridBVFlowDerivative,
    rengerDirectionalFlowHybridBVReferenceEvolutionPath,
    finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
    rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue,
    rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue] using!
    hCoordinate transition

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The reference path's density derivative is the exact forward drift almost everywhere. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityDerivative_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state,
        rengerDirectionalFlowHybridBVDensityDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
            time state =
          rengerDirectionalFlowHybridBVReferenceEvolutionFlowDivergence
            generator path time state := by
  rw [ae_all_iff]
  intro state
  have hCoordinate :=
    ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      (Sum.inl state)
  simpa only [rengerDirectionalFlowHybridBVDensityDerivative,
    rengerDirectionalFlowHybridBVReferenceEvolutionPath,
    finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
    rengerDirectionalFlowHybridBVReferenceEvolutionFlowDivergence_eq_drift] using!
    hCoordinate

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The reference path retains the target's initial density exactly. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialDensity
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (state : State) :
    (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path).initialTrace
        (Sum.inl state) =
      path.1.initialTrace (Sum.inl state) := by
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPath
  rw (transparency := .default) [finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
    (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
  change (rengerDirectionalFlowHybridBVTargetInitialPMF path state).toReal = _
  rw [rengerDirectionalFlowHybridBVTargetInitialPMF_apply, ENNReal.coe_toReal]
  exact Real.coe_toNNReal _ (path.2.initialDensityNonnegative state)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every cumulative reference flow starts at zero. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialCumulativeFlow
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path).initialTrace
        (Sum.inr transition) = 0 := by
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPath
  rw (transparency := .default) [finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
    (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
  simp [finiteStateTimeDependentMarkovMeanHybridBVInitialValue]

/-- The unchanged reference evolution is a genuine admissible hybrid-BV representation path. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration := by
  let referencePath :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path
  refine ⟨referencePath, ?_⟩
  refine
    { absolutelyContinuousDerivative :=
        finiteStateTimeDependentMarkovMeanHybridBVPath_hasAbsolutelyContinuousDerivative
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      densityNonnegativeAE := ?_
      densityNormalizedAE := ?_
      cumulativeFlowNonnegativeAE := ?_
      flowDerivativeNonnegativeAE := ?_
      continuityEquationAE := ?_
      initialDensityNormalized := ?_
      initialDensityNonnegative := ?_
      cumulativeFlowInitiallyZero := ?_
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro state
    rw [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
        generator path hTime.1.le hTime.2 state]
    unfold rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
    exact ENNReal.toReal_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    rw [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl]
    simp_rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
      generator path hTime.1.le hTime.2]
    exact sum_rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
      generator path time hTime.1.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro transition
    rw [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl]
    exact
      rengerDirectionalFlowHybridBVReferenceEvolutionPath_cumulativeFlowValue_nonnegative
        generator path hTime.1.le hTime.2 transition
  · filter_upwards
      [ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivative_eq
        generator path] with time hFlow
    intro transition
    rw [show referencePath =
      rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      hFlow transition]
    exact rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue_nonnegative
      generator path time transition.val.1 transition.val.2
  · filter_upwards
      [ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityDerivative_eq
          generator path,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivative_eq
          generator path] with time hDensity hFlow
    intro state
    rw [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      hDensity state,
      rengerDirectionalFlowHybridBVReferenceEvolutionFlowDivergence]
    unfold finiteStateFlowDivergence
    simp_rw [hFlow]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
      Fintype.sum_eq_add_sum_subtype_ne _ state]
    simp [rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue,
      generator.rate_self]
  · simpa only [referencePath,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialDensity] using
      path.2.initialDensityNormalized
  · intro state
    rw [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialDensity]
    exact path.2.initialDensityNonnegative state
  · intro transition
    exact rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialCumulativeFlow
      generator path transition
  · rw (transparency := .default) [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change ∑ state, finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate (⟨duration, hDuration.le⟩ : ℝ≥0)
      ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) (Sum.inl state) = 1
    calc
      _ = ∑ state,
          (finiteStateTimeDependentMarkovEndpointProbability
            (rengerDirectionalFlowHybridBVTargetInitialPMF path)
            generator.toTimeDependentMarkovRate
            ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) state).toReal := by
        apply Finset.sum_congr rfl
        intro state _hState
        exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
          _ _ (⟨duration, hDuration.le⟩ : ℝ≥0)
          (show 0 ≤ ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) by positivity)
          le_rfl state
      _ = 1 := PMF.sum_toReal
        (finiteStateTimeDependentMarkovEndpointPMF
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩)
  · intro state
    rw (transparency := .default) [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change 0 ≤ finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate (⟨duration, hDuration.le⟩ : ℝ≥0)
      ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) (Sum.inl state)
    have hValue :=
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        generator.toTimeDependentMarkovRate
        (⟨duration, hDuration.le⟩ : ℝ≥0)
        (show 0 ≤ ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) by positivity)
        le_rfl state
    exact hValue.symm ▸ ENNReal.toReal_nonneg
  · intro transition
    rw (transparency := .default) [show referencePath =
        rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPath,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change 0 ≤ finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      generator.toTimeDependentMarkovRate (⟨duration, hDuration.le⟩ : ℝ≥0)
      ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) (Sum.inr transition)
    exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow_nonnegative
      _ _ (⟨duration, hDuration.le⟩ : ℝ≥0)
      (show 0 ≤ ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) by positivity) transition

end

end FiniteMarkovProcesses.InformationTheory
