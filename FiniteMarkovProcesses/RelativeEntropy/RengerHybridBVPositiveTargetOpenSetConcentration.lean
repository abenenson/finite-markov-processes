/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMeanConvergence
import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovRoundedInitialMeanConvergence

/-!
# Open-set concentration around positive Renger target regularizations

For a finite-rate hybrid-BV target with positive initial density, mix in one fixed positive amount
of the unchanged reference evolution.  The canonical regularized source means then converge to
that perturbed target.  Consequently every open neighborhood of the perturbed target contains
the exact source mean for all sufficiently advanced regularization indices, and canonical rounded
deterministic initial configurations concentrate in that neighborhood as particle number grows.

The regularization index is frozen before the particle-number limit.  This module does not take
the positive-perturbation limit, perform a likelihood change of measure, or assert an LDP lower
bound.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- For every open neighborhood of a positive reference-evolution perturbation, all sufficiently
advanced frozen canonical regularizations have deterministic replica observations concentrating
in that neighborhood whenever their empirical initial densities converge coordinatewise. -/
theorem
eventually_tendsto_measureReal_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetDeterministicInitialReplica_totalHybridObservation_not_mem_open_zero_of_empiricalInitial_weight_tendsto
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
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
    ∀ᶠ index in atTop,
      Tendsto
        (fun successorIndex ↦
          let perturbed :=
            rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
              generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
          let rates :=
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator perturbed.1 index
          let law :=
            (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
              (initialConfiguration successorIndex) rates
                ⟨duration, hDuration.le⟩).toMeasure
          law.real {histories |
            (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories).toDerivativePath ∉ openSet})
        atTop (nhds 0) := by
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
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
  filter_upwards [hEventuallyMean] with index hMean
  have hPerturbedWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed).weight state :
          ℝ)) := by
    rw (transparency := .default)
      [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath_initialProbabilityDensity]
    exact hWeight
  have hCenter :=
    tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_of_empiricalInitial_weight_tendsto
      initialConfiguration
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator perturbed.1 index)
      ⟨duration, hDuration.le⟩ hPerturbedWeight
  simpa only [perturbed, rengerDirectionalFlowHybridBVTargetInitialPMF] using!
    tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalHybridObservation_not_mem_open_zero
      initialConfiguration
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator perturbed.1 index)
      ⟨duration, hDuration.le⟩ (by exact_mod_cast hDuration)
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        (rengerDirectionalFlowHybridBVTargetInitialPMF perturbed)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator perturbed.1 index)
        ⟨duration, hDuration.le⟩).toDerivativePath
      hCenter hOpen hMean

/-- Canonical rounded initial configurations satisfy the generic deterministic-initial open-set
concentration theorem. -/
theorem
eventually_tendsto_measureReal_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetRoundedInitialReplica_totalHybridObservation_not_mem_open_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hOpen : IsOpen openSet)
    (hTarget :
      (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne).1.toDerivativePath
          ∈ openSet) :
    ∀ᶠ index in atTop,
      Tendsto
        (fun successorIndex ↦
          let perturbed :=
            rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
              generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
          let rates :=
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator perturbed.1 index
          let initialConfiguration :=
            finiteStateProbabilityDensityRoundedInitialConfiguration
              (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed)
              successorIndex
          let law :=
            (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
              initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
          law.real {histories |
            (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories).toDerivativePath ∉ openSet})
        atTop (nhds 0) := by
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  let initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State :=
    fun successorIndex ↦
      finiteStateProbabilityDensityRoundedInitialConfiguration
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed) successorIndex
  have hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight
          state : ℝ)) := by
      intro state
      rw [←
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath_initialProbabilityDensity
          generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne]
      simpa only [initialConfiguration,
        finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration] using
        finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity perturbed) state
  have hGeneric :=
    eventually_tendsto_measureReal_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetDeterministicInitialReplica_totalHybridObservation_not_mem_open_zero_of_empiricalInitial_weight_tendsto
      generator hDuration path hDynamicRate mixingWeight hMixingWeight hMixingWeightLeOne
        hInitial initialConfiguration hWeight hOpen hTarget
  simpa only [perturbed, initialConfiguration] using hGeneric

end

end FiniteMarkovProcesses.InformationTheory
