/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRoundedInitialActionConcentration
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetActionConvergence
import FiniteMarkovProcesses.Probability.ExponentialFailureMassLogLiminf
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation
import
  FiniteMarkovProcesses.RelativeEntropy.DensityFluxLargeDeviationRepresentation

/-!
# Finite-particle regularized Renger open-event lower estimate

This module intersects one hybrid open event with the complement of the canonical action-
deviation event and applies the exact finite-product Girsanov identity.  The resulting lower
estimate keeps both candidate failure masses explicit.  Its action threshold is extensive at the
literal positive particle count.

This is a finite-regularization, finite-particle theorem.  It does not yet take logarithms, pass to
a particle limit, remove the positive perturbation, or assert an LDP lower bound.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- At fixed regularization and particle count, an upper bound on the heterogeneous mean plus
one positive deviation margin gives the exact Girsanov lower estimate for a hybrid open event.
The topology and action failure masses remain separate. -/
theorem
exp_neg_particleThreshold_mul_one_sub_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_failureMass_le_reference_openEvent
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (tolerance actionThreshold : ℝ)
    (hMeanCap :
      let rates :=
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index
      (∑ replica, ∫ history,
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index history
        ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
          (PMF.pure (initialConfiguration replica)) rates
          ⟨duration, hDuration.le⟩) +
        (successorIndex + 1 : ℝ) * tolerance ≤
      (successorIndex + 1 : ℝ) * actionThreshold) :
    let rates :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index
    let candidate :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
    let reference :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator.toTimeDependentMarkovRate
        ⟨duration, hDuration.le⟩).toMeasure
    let event : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
      {histories |
        (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration histories).toDerivativePath ∈ openSet}
    let expectedActionSum :=
      ∑ replica, ∫ history,
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure (initialConfiguration replica)) rates
        ⟨duration, hDuration.le⟩
    let badActionEvent : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
      {histories |
        (successorIndex + 1 : ℝ) * tolerance ≤
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
              generator path index initialConfiguration histories - expectedActionSum|}
    ENNReal.ofReal
        (Real.exp (-((successorIndex + 1 : ℝ) * actionThreshold))) *
      (1 - (candidate eventᶜ + candidate badActionEvent)) ≤
        reference event := by
  dsimp only at hMeanCap ⊢
  let rates :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index
  let event : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
    {histories |
      (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath ∈ openSet}
  let expectedActionSum :=
    ∑ replica, ∫ history,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index history
    ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure (initialConfiguration replica)) rates
      ⟨duration, hDuration.le⟩
  let badActionEvent : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
    {histories |
      (successorIndex + 1 : ℝ) * tolerance ≤
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
            generator path index initialConfiguration histories - expectedActionSum|}
  have hObservationMeasurable : Measurable
      (fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex ↦
        (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration histories).toDerivativePath) :=
    FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous.measurable.comp
      (PositiveFiniteJumpHistoryReplicas.measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration)
  have hEvent : MeasurableSet event :=
    hObservationMeasurable hOpen.measurableSet
  have hReplicaActionMeasurable : Measurable
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
        generator path index initialConfiguration) := by
    exact measurable_finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
      initialConfiguration rates generator.toTimeDependentMarkovRate duration
  have hBadActionEvent : MeasurableSet badActionEvent := by
    have hAbsoluteDeviationMeasurable : Measurable
        (fun histories ↦
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
              generator path index initialConfiguration histories - expectedActionSum|) := by
      simpa only [Real.norm_eq_abs] using!
        (hReplicaActionMeasurable.sub measurable_const).norm
    exact measurableSet_le measurable_const hAbsoluteDeviationMeasurable
  apply
    exp_neg_threshold_mul_one_sub_timeDependentCandidateReplica_failureMass_le_reference_event
      initialConfiguration rates generator.toTimeDependentMarkovRate
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
        generator path.1 index)
      ⟨duration, hDuration.le⟩ hEvent hBadActionEvent
      ((successorIndex + 1 : ℝ) * actionThreshold)
  intro histories _hEvent hNotBad
  have hDeviation :
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
          generator path index initialConfiguration histories - expectedActionSum| <
        (successorIndex + 1 : ℝ) * tolerance := by
    exact lt_of_not_ge hNotBad
  have hActionMinusMeanLe :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
          generator path index initialConfiguration histories - expectedActionSum ≤
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
          generator path index initialConfiguration histories - expectedActionSum| :=
    le_abs_self _
  have hMeanCap' :
      expectedActionSum + (successorIndex + 1 : ℝ) * tolerance ≤
        (successorIndex + 1 : ℝ) * actionThreshold := by
    simpa only [rates, expectedActionSum] using hMeanCap
  change
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
        generator path index initialConfiguration histories ≤
      (successorIndex + 1 : ℝ) * actionThreshold
  linarith

/-- If one fixed regularization has its exact Markov mean inside an open neighborhood and its
target-initial expected action below a real threshold, then one positive action margin makes both
candidate failure probabilities vanish and makes the finite-product Girsanov lower estimate hold
eventually in particle number. -/
theorem
exists_tolerance_tendsto_failureMass_and_eventually_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_reference_openEvent_lowerEstimate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (hMean :
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩).toDerivativePath ∈ openSet)
    (actionThreshold : ℝ)
    (hActionThreshold :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path) <
        actionThreshold) :
    ∃ tolerance : ℝ, 0 < tolerance ∧
      Tendsto
        (fun successorIndex ↦
          let rates :=
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index
          let initialConfiguration := initialConfigurations successorIndex
          let candidate :=
            (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
              initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
          candidate.real {histories |
            (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories).toDerivativePath ∉ openSet})
        atTop (nhds 0) ∧
      Tendsto
        (fun successorIndex ↦
          let rates :=
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index
          let initialConfiguration := initialConfigurations successorIndex
          let candidate :=
            (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
              initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
          let expectedActionSum :=
            ∑ replica, ∫ history,
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                generator path index history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
              (PMF.pure (initialConfiguration replica)) rates
              ⟨duration, hDuration.le⟩
          candidate.real {histories |
            (successorIndex + 1 : ℝ) * tolerance ≤
              |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
                  generator path index initialConfiguration histories - expectedActionSum|})
        atTop (nhds 0) ∧
      ∀ᶠ successorIndex in atTop,
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        let initialConfiguration := initialConfigurations successorIndex
        let candidate :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
        let reference :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration generator.toTimeDependentMarkovRate
            ⟨duration, hDuration.le⟩).toMeasure
        let event : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
          {histories |
            (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories).toDerivativePath ∈ openSet}
        let expectedActionSum :=
          ∑ replica, ∫ history,
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
              generator path index history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates
            ⟨duration, hDuration.le⟩
        let badActionEvent : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
          {histories |
            (successorIndex + 1 : ℝ) * tolerance ≤
              |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
                  generator path index initialConfiguration histories - expectedActionSum|}
        ENNReal.ofReal
            (Real.exp (-((successorIndex + 1 : ℝ) * actionThreshold))) *
          (1 - (candidate eventᶜ + candidate badActionEvent)) ≤
            reference event := by
  let expectedAction :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
      generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path)
  let tolerance := (actionThreshold - expectedAction) / 2
  have hTolerance : 0 < tolerance := by
    dsimp only [tolerance, expectedAction]
    linarith
  refine ⟨tolerance, hTolerance, ?_, ?_, ?_⟩
  · have hCenter :=
      tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_of_empiricalInitial_weight_tendsto
        initialConfigurations
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩ hWeight
    simpa only [rengerDirectionalFlowHybridBVTargetInitialPMF] using!
      tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalHybridObservation_not_mem_open_zero
        initialConfigurations
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩ (by exact_mod_cast hDuration)
        (finiteStateTimeDependentMarkovMeanHybridBVPath
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          ⟨duration, hDuration.le⟩).toDerivativePath
        hCenter hOpen hMean
  · exact
      tendsto_measureReal_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplicaJumpLogActionParticleSpeedDeviation_zero
        generator hDuration path index initialConfigurations tolerance hTolerance
  · have hAverage :=
      tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialExpectedJumpLogActionAverage_of_empiricalInitial_weight_tendsto
        generator hDuration path index initialConfigurations hWeight
    have hEventuallyAverage : ∀ᶠ successorIndex in atTop,
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        let initialConfiguration := initialConfigurations successorIndex
        (∑ replica, ∫ history,
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
              generator path index history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates
            ⟨duration, hDuration.le⟩) / (successorIndex + 1 : ℝ) <
          expectedAction + tolerance := by
      exact hAverage.eventually (eventually_lt_nhds (by
        dsimp only [expectedAction]
        linarith))
    filter_upwards [hEventuallyAverage] with successorIndex hAverageIndex
    apply
      exp_neg_particleThreshold_mul_one_sub_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_failureMass_le_reference_openEvent
        generator hDuration path index successorIndex
          (initialConfigurations successorIndex) hOpen tolerance actionThreshold
    dsimp only at hAverageIndex ⊢
    have hParticlePositive : (0 : ℝ) < successorIndex + 1 := by positivity
    have hMeanSumLt := (div_lt_iff₀ hParticlePositive).mp hAverageIndex
    dsimp only [tolerance, expectedAction] at hMeanSumLt ⊢
    nlinarith

/-- The fixed-regularization finite-product estimate yields the literal extended logarithmic
particle-speed liminf for the homogeneous reference open event.  This theorem still displays the
particle-indexed finite slices; a separate carrier theorem transports it to the common sigma
carrier required by `scaledEventLogProbability`. -/
theorem
neg_actionThreshold_le_liminf_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_reference_openEvent_logProbability
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (hMean :
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩).toDerivativePath ∈ openSet)
    (actionThreshold : ℝ)
    (hActionThreshold :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path) <
        actionThreshold) :
    ((-actionThreshold : ℝ) : EReal) ≤
      liminf
        (fun successorIndex ↦
          let initialConfiguration := initialConfigurations successorIndex
          let reference :=
            (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
              initialConfiguration generator.toTimeDependentMarkovRate
              ⟨duration, hDuration.le⟩).toMeasure
          let event : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
            {histories |
              (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
                successorIndex duration histories).toDerivativePath ∈ openSet}
          ENNReal.log (reference event) /
            (((successorIndex + 1 : ℕ) : ℝ) : EReal))
        atTop := by
  rcases
      exists_tolerance_tendsto_failureMass_and_eventually_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_reference_openEvent_lowerEstimate
        generator hDuration path index initialConfigurations hWeight hOpen hMean
          actionThreshold hActionThreshold with
    ⟨tolerance, _hTolerance, hTopologyFailureReal, hActionFailureReal,
      hEventuallyLower⟩
  let probability : ℕ → ENNReal := fun successorIndex ↦
    let initialConfiguration := initialConfigurations successorIndex
    let reference :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator.toTimeDependentMarkovRate
        ⟨duration, hDuration.le⟩).toMeasure
    let event : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
      {histories |
        (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration histories).toDerivativePath ∈ openSet}
    reference event
  let topologyFailure : ℕ → ENNReal := fun successorIndex ↦
    let rates :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index
    let initialConfiguration := initialConfigurations successorIndex
    let candidate :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
    candidate {histories |
      (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath ∉ openSet}
  let actionFailure : ℕ → ENNReal := fun successorIndex ↦
    let rates :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index
    let initialConfiguration := initialConfigurations successorIndex
    let candidate :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
    let expectedActionSum :=
      ∑ replica, ∫ history,
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure (initialConfiguration replica)) rates
        ⟨duration, hDuration.le⟩
    candidate {histories |
      (successorIndex + 1 : ℝ) * tolerance ≤
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
            generator path index initialConfiguration histories - expectedActionSum|}
  have hTopologyFailure : Tendsto topologyFailure atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff
      (hf := fun successorIndex ↦ by
        dsimp only [topologyFailure]
        finiteness)).mp
    simpa only [topologyFailure, MeasureTheory.measureReal_def] using hTopologyFailureReal
  have hActionFailure : Tendsto actionFailure atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff
      (hf := fun successorIndex ↦ by
        dsimp only [actionFailure]
        finiteness)).mp
    simpa only [actionFailure, MeasureTheory.measureReal_def] using hActionFailureReal
  have hFailureReal : Tendsto
      (fun successorIndex ↦
        (topologyFailure successorIndex + actionFailure successorIndex).toReal)
      atTop (nhds 0) := by
    have hSumReal :=
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTopologyFailure).add
        ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hActionFailure)
    rw [show (fun successorIndex ↦
        (topologyFailure successorIndex + actionFailure successorIndex).toReal) =
      fun successorIndex ↦
        (topologyFailure successorIndex).toReal +
          (actionFailure successorIndex).toReal by
      funext successorIndex
      rw [ENNReal.toReal_add]
      · dsimp only [topologyFailure]
        finiteness
      · dsimp only [actionFailure]
        finiteness]
    simpa only [ENNReal.toReal_zero, add_zero, Function.comp_apply] using hSumReal
  have hFailure : Tendsto
      (fun successorIndex ↦
        topologyFailure successorIndex + actionFailure successorIndex)
      atTop (nhds 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff
      (hf := fun successorIndex ↦ ENNReal.add_ne_top.mpr ⟨
        (by dsimp only [topologyFailure]; finiteness),
        (by dsimp only [actionFailure]; finiteness)⟩)).mp hFailureReal
  apply
    neg_le_liminf_ennrealLog_div_positiveParticleCount_of_exponential_one_sub_failure_le
      probability
      (fun successorIndex ↦
        topologyFailure successorIndex + actionFailure successorIndex)
      actionThreshold hFailure
  simpa only [probability, topologyFailure, actionFailure] using! hEventuallyLower

/-- The fixed-regularization open-event liminf transported to the existing common positive-
replica sigma carrier.  This is the carrier-correct `scaledEventLogProbability` form: microscopic
laws at every particle count inhabit one fixed measurable space, and the common observation lands
in the exact ambient strong-`L1` plus vague-derivative carrier. -/
theorem
neg_actionThreshold_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (hMean :
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩).toDerivativePath ∈ openSet)
    (actionThreshold : ℝ)
    (hActionThreshold :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path) <
        actionThreshold) :
    ((-actionThreshold : ℝ) : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦
              finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
                index (initialConfigurations index)
                generator duration hDuration.le)
            (fun _index family ↦
              (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
                duration family).toDerivativePath)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  have hSlice :=
    neg_actionThreshold_le_liminf_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplica_reference_openEvent_logProbability
      generator hDuration path index initialConfigurations hWeight hOpen hMean
        actionThreshold hActionThreshold
  have hCommonObservationMeasurable : Measurable
      (fun family : FiniteStateMarkovJumpPositiveReplicaFamily State ↦
        (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
          duration family).toDerivativePath) :=
    FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous.measurable.comp
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
  have hCommonEvent : MeasurableSet
      ((fun family : FiniteStateMarkovJumpPositiveReplicaFamily State ↦
        (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
          duration family).toDerivativePath) ⁻¹' openSet) :=
    hCommonObservationMeasurable hOpen.measurableSet
  refine hSlice.trans_eq (Filter.liminf_congr (Filter.Eventually.of_forall fun successorIndex ↦ ?_))
  let initialConfiguration := initialConfigurations successorIndex
  unfold scaledEventLogProbability finiteStateMarkovJumpParticleSpeed
  dsimp only
  rw [finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_eq_map_replicaLaw]
  rw [MeasureTheory.Measure.map_apply
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection successorIndex)
    hCommonEvent]
  have hConstant :
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator.toTimeDependentMarkovRate
        ⟨duration, hDuration.le⟩).toMeasure =
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration.le).toMeasure := by
    simpa only [NNReal.coe_mk] using!
      finiteStateTimeDependentMarkovDeterministicInitialReplica_constant_toMeasure
        initialConfiguration generator ⟨duration, hDuration.le⟩
  rw [← hConstant]
  rfl

/-- Removing the finite positive regularization chart yields the exact open-neighborhood lower
estimate at the dynamic rate of one strictly positive reference-evolution perturbation.  The
microscopic reference law, common sigma carrier, observation, and particle speed no longer depend
on the selected regularization index. -/
theorem
neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetDeterministicInitialReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (hTarget :
      (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne).1.toDerivativePath
          ∈ openSet) :
    (let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne;
      -(rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration perturbed.1 : EReal) ≤
        liminf
          (fun successorIndex ↦
            scaledEventLogProbability
              (fun index ↦
                finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
                  index (initialConfigurations index)
                  generator duration hDuration.le)
              (fun _index family ↦
                (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
                  duration family).toDerivativePath)
              finiteStateMarkovJumpParticleSpeed successorIndex openSet)
          atTop) := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  let perturbedRate :=
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration perturbed.1
  let lowerBound : EReal :=
    liminf
      (fun successorIndex ↦
        scaledEventLogProbability
          (fun index ↦
            finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
              index (initialConfigurations index)
              generator duration hDuration.le)
          (fun _index family ↦
            (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
              duration family).toDerivativePath)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet)
      atTop
  have hPerturbedRateFinite : perturbedRate ≠ ⊤ := by
    have hUpper :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_dynamicRate_le
        generator path mixingWeight hMixingWeightLeOne
    have hFinite :
        ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hDynamicRate
    exact ne_top_of_le_ne_top hFinite hUpper
  have hSourceMean :=
    tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetSourceMeanHybridBVPath_atTop
      generator hDuration path hDynamicRate mixingWeight hMixingWeight
      hMixingWeightLeOne hInitial
  have hSourceMeanDerivative : Tendsto
      (fun index : ℕ ↦
        (finiteStateTimeDependentMarkovMeanHybridBVPath
          (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator perturbed.1 index)
          ⟨duration, hDuration.le⟩).toDerivativePath)
      atTop (nhds perturbed.1.toDerivativePath) :=
    FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous.continuousAt.tendsto.comp
      hSourceMean
  have hEventuallyMean : ∀ᶠ index in atTop,
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator perturbed.1 index)
        ⟨duration, hDuration.le⟩).toDerivativePath ∈ openSet :=
    hSourceMeanDerivative.eventually (hOpen.mem_nhds hTarget)
  have hPerturbedWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed).weight state :
          ℝ)) := by
    rw (transparency := .default)
      [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath_initialProbabilityDensity]
    exact hWeight
  have hThreshold (threshold : ℝ)
      (hRateThreshold : perturbedRate < ENNReal.ofReal threshold) :
      ((-threshold : ℝ) : EReal) ≤ lowerBound := by
    have hEventuallyKL :=
      eventually_klDiv_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTarget_lt
        generator hDuration path hDynamicRate mixingWeight hMixingWeight
        hMixingWeightLeOne hInitial hRateThreshold
    obtain ⟨index, hMeanIndex, hKLIndex⟩ :=
      (hEventuallyMean.and hEventuallyKL).exists
    dsimp only at hKLIndex
    have hExpectation :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction_eq_klDiv
        generator hDuration perturbed index
          (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
    have hExpectedThreshold :
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
            generator perturbed index
              (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed) < threshold := by
      rw [hExpectation.2]
      exact ENNReal.toReal_lt_of_lt_ofReal hKLIndex
    exact
      neg_actionThreshold_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReference_openSet
        generator hDuration perturbed index initialConfigurations hPerturbedWeight hOpen
          hMeanIndex threshold hExpectedThreshold
  let threshold : ℕ → ℝ := fun index ↦
    perturbedRate.toReal + 1 / ((index + 1 : ℕ) : ℝ)
  have hThresholdRate (index : ℕ) :
      perturbedRate < ENNReal.ofReal (threshold index) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hPerturbedRateFinite).2
    dsimp only [threshold]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (by positivity))
  have hThresholdBound (index : ℕ) :
      ((-threshold index : ℝ) : EReal) ≤ lowerBound :=
    hThreshold (threshold index) (hThresholdRate index)
  have hReciprocal : Tendsto
      (fun index : ℕ ↦ 1 / ((index + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    have hParticleCount : Tendsto
        (fun index : ℕ ↦ ((index + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [one_div] using
      (tendsto_const_nhds.div_atTop hParticleCount :
        Tendsto (fun index : ℕ ↦ (1 : ℝ) / ((index + 1 : ℕ) : ℝ)) atTop (nhds 0))
  have hThresholdNegReal : Tendsto
      (fun index ↦ -threshold index) atTop (nhds (-perturbedRate.toReal)) := by
    unfold threshold
    simpa only [add_zero] using (tendsto_const_nhds.add hReciprocal).neg
  have hThresholdNeg : Tendsto
      (fun index ↦ ((-threshold index : ℝ) : EReal))
      atTop (nhds (((-perturbedRate.toReal : ℝ) : EReal))) :=
    EReal.tendsto_coe.mpr hThresholdNegReal
  rw [show -(perturbedRate : EReal) =
      ((-perturbedRate.toReal : ℝ) : EReal) by
    rw [← EReal.coe_ennreal_toReal hPerturbedRateFinite]
    norm_num]
  exact le_of_tendsto hThresholdNeg (Filter.Eventually.of_forall hThresholdBound)

/-- Letting the positive reference-evolution perturbation vanish yields the exact open-event
lower estimate at the original finite dynamic rate.  The perturbation preserves the initial law,
so the microscopic reference family is unchanged before and after the limit argument. -/
theorem
neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetDeterministicInitialReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfigurations successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet) (hTarget : path.1.toDerivativePath ∈ openSet) :
    -(rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration path.1 : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦
              finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
                index (initialConfigurations index)
                generator duration hDuration.le)
            (fun _index family ↦
              (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
                duration family).toDerivativePath)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  let mixingWeight : ℕ → NNReal := fun index ↦
    ⟨1 / ((index + 1 : ℕ) : ℝ), by positivity⟩
  have hMixingWeightPositive (index : ℕ) : 0 < mixingWeight index := by
    apply NNReal.coe_pos.mp
    dsimp only [mixingWeight]
    exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos index)
  have hMixingWeightLeOne (index : ℕ) : mixingWeight index ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    dsimp only [mixingWeight, NNReal.coe_one]
    apply (div_le_iff₀ (by exact_mod_cast Nat.succ_pos index)).2
    norm_num
  have hParticleCount : Tendsto
      (fun index : ℕ ↦ ((index + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hMixingWeightZero : Tendsto
      (fun index ↦ (mixingWeight index : ℝ)) atTop (nhds 0) := by
    simpa only [mixingWeight, one_div] using!
      (tendsto_const_nhds.div_atTop hParticleCount :
        Tendsto (fun index : ℕ ↦ (1 : ℝ) / ((index + 1 : ℕ) : ℝ))
          atTop (nhds 0))
  have hPerturbedPath : Tendsto
      (fun index ↦
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
          generator path (mixingWeight index) (mixingWeight index).coe_nonneg
            (hMixingWeightLeOne index)).1)
      atTop (nhds path.1) := by
    simpa only using!
      tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path hMixingWeightZero
  have hPerturbedDerivativePath : Tendsto
      (fun index ↦
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
          generator path (mixingWeight index) (mixingWeight index).coe_nonneg
            (hMixingWeightLeOne index)).1.toDerivativePath)
      atTop (nhds path.1.toDerivativePath) :=
    FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous.continuousAt.tendsto.comp
      hPerturbedPath
  obtain ⟨index, hPerturbedTarget⟩ :=
    (hPerturbedDerivativePath.eventually (hOpen.mem_nhds hTarget)).exists
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path (mixingWeight index) (mixingWeight index).coe_nonneg
        (hMixingWeightLeOne index)
  have hLower :=
    neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetDeterministicInitialReference_openSet
      generator hDuration path hDynamicRate (mixingWeight index)
        (hMixingWeightPositive index) (hMixingWeightLeOne index) hInitial
        initialConfigurations hWeight hOpen hPerturbedTarget
  dsimp only at hLower
  have hPerturbedRateLe :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration perturbed.1 ≤
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 := by
    calc
      _ ≤ ((1 - mixingWeight index : NNReal) : ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 :=
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_dynamicRate_le
          generator path (mixingWeight index) (hMixingWeightLeOne index)
      _ ≤ 1 * rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 := by
        have hCoefficient :
            ((1 - mixingWeight index : NNReal) : ENNReal) ≤ 1 := by
          exact_mod_cast
            (tsub_le_self : (1 : NNReal) - mixingWeight index ≤ 1)
        simpa only [mul_comm] using
          mul_le_mul_right hCoefficient
            (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1)
      _ = _ := one_mul _
  have hNegativeRate :
      -(rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration path.1 : EReal) ≤
        -(rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration perturbed.1 : EReal) := by
    rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact hPerturbedRateLe
  exact hNegativeRate.trans hLower

/-- Canonical rounded deterministic initial configurations satisfy the exact original-target
open-event lower estimate. -/
theorem
neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetRoundedInitialReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet) (hTarget : path.1.toDerivativePath ∈ openSet) :
    -(rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration path.1 : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦
              finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
                index
                (finiteStateProbabilityDensityRoundedInitialConfiguration
                  (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) index)
                generator duration hDuration.le)
            (fun _index family ↦
              (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
                duration family).toDerivativePath)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  apply
    neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetDeterministicInitialReference_openSet
      generator hDuration path hDynamicRate hInitial
      (fun successorIndex ↦
        finiteStateProbabilityDensityRoundedInitialConfiguration
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) successorIndex)
  · intro state
    simpa only [finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration] using
      finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) state
  · exact hOpen
  · exact hTarget

end

end FiniteMarkovProcesses.InformationTheory
