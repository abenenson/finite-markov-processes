/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRegularizedOpenLowerEstimate
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVCompleteRateCompactness

/-!
# Renger Theorem 4.1 hybrid-BV open lower bound

This module transports the finite-particle deterministic-initial lower estimate from the ambient
strong-`L1` plus vague derivative carrier back to the exact hybrid-BV graph carrier.  The transport
uses the graph inclusion's inducing property: every hybrid-open event is the inverse image of one
ambient open event.  It does not assert that the graph image itself is ambient-open.

For Renger Theorem 4.1's arbitrary deterministic configurations, every finite complete-rate
candidate is then shown to have the prescribed limiting initial density.  Its complete rate is
therefore exactly its dynamic rate, so the pointwise open-event estimates assemble into the
literal large-deviation lower-bound contract on the theorem's own hybrid carrier.

This is only the open lower half of the deterministic-initial path LDP.  The closed upper bound,
exponential tightness/goodness, and the separately mixed initial regimes remain independent.
-/

@[expose] public section

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

/-- Every finite complete-rate Theorem 4.1 candidate satisfies the pointwise hybrid-open lower
estimate.  Finiteness forces both admissibility and the prescribed limiting initial density; no
alternative initial configuration or rounded source is introduced. -/
theorem
neg_rengerTheoremFourOneHybridBVCompleteRate_le_liminf_scaledEventLogProbability_deterministicInitialReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hCompleteRate :
      rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData path ≠ ⊤)
    {openSet : Set (RengerDirectionalFlowHybridBVPath State duration)}
    (hOpen : IsOpen openSet) (hTarget : path ∈ openSet) :
    -(rengerTheoremFourOneHybridBVCompleteRate
        generator hDuration initialData path : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦
              finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
                index (initialData.initialState index)
                generator duration hDuration.le)
            (fun _index family ↦
              finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  have hAdmissible : RengerDirectionalFlowHybridBVAdmissible path hDuration := by
    by_contra hPath
    exact hCompleteRate (by
      simpa only [rengerTheoremFourOneHybridBVCompleteRate] using
        rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
          generator hDuration (rengerTheoremFourOneInitialRate initialData) hPath)
  let representationPath :
      RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
    ⟨path, hAdmissible⟩
  have hSumNeTop :
      rengerDirectionalFlowHybridBVLiftedInitialCost
          (rengerTheoremFourOneInitialRate initialData) path +
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ⊤ := by
    rw [← rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
      generator hDuration (rengerTheoremFourOneInitialRate initialData) hAdmissible]
    exact hCompleteRate
  have hInitialCostNeTop :
      rengerDirectionalFlowHybridBVLiftedInitialCost
          (rengerTheoremFourOneInitialRate initialData) path ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hSumNeTop).1
  have hTargetInitial :
      rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath =
        initialData.limitingDensity := by
    by_contra hDensity
    apply hInitialCostNeTop
    rw [rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
      (rengerTheoremFourOneInitialRate initialData) hDuration hAdmissible]
    change rengerTheoremFourOneInitialRate initialData
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath) = ⊤
    exact rengerTheoremFourOneInitialRate_of_ne initialData hDensity
  have hDynamicRateNeTop :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hSumNeTop).2
  have hCompleteRateEq :
      rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData path =
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
    rw [rengerTheoremFourOneHybridBVCompleteRate,
      rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
        generator hDuration (rengerTheoremFourOneInitialRate initialData) hAdmissible,
      rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
        (rengerTheoremFourOneInitialRate initialData) hDuration hAdmissible]
    change rengerTheoremFourOneInitialRate initialData
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath) +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path =
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path
    rw [hTargetInitial]
    simp
  obtain ⟨ambientOpenSet, hAmbientOpen, hAmbientPreimage⟩ :=
    FiniteIntervalHybridBVPath.isInducing_toDerivativePath.isOpen_iff.mp hOpen
  have hTargetAmbient : path.toDerivativePath ∈ ambientOpenSet := by
    have : path ∈
        (fun candidate : RengerDirectionalFlowHybridBVPath State duration ↦
          candidate.toDerivativePath) ⁻¹' ambientOpenSet := by
      rw [hAmbientPreimage]
      exact hTarget
    exact this
  have hInitialPositive : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity representationPath.1 state := by
    intro state
    change 0 <
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
        representationPath).weight state
    rw [hTargetInitial]
    exact initialData.limitingDensity_interior state
  have hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialData.initialState successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
          representationPath).weight state : ℝ)) := by
    intro state
    have hNNReal := initialData.empiricalInitialDensity_tendsto state
    have hReal :
        Tendsto
          (fun successorIndex ↦
            ((initialData.empiricalInitialDensity successorIndex).weight state : ℝ))
          atTop
          (nhds (initialData.limitingDensity.weight state : ℝ)) :=
      (NNReal.continuous_coe.tendsto
        (initialData.limitingDensity.weight state)).comp hNNReal
    convert hReal using 1
    · funext successorIndex
      rw [finiteIIDEmpiricalProbabilityDensity_weight,
        finiteIIDPositiveSampleStateCount, ← initialData.empiricalInitialDensity_eq]
    · rw [hTargetInitial]
  have hLower :=
    neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetDeterministicInitialReference_openSet
      generator hDuration representationPath hDynamicRateNeTop hInitialPositive
        initialData.initialState hWeight hAmbientOpen hTargetAmbient
  rw [hCompleteRateEq]
  rw [← hAmbientPreimage]
  exact hLower

/-- Renger Theorem 4.1's arbitrary deterministic initial configurations satisfy the literal
hybrid-BV open-set lower bound at the complete initial-plus-dynamic rate. -/
theorem rengerTheoremFourOneDeterministicInitialHybridBV_hasLargeDeviationLowerBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    HasLargeDeviationLowerBound
      (fun successorIndex openSet ↦
        scaledEventLogProbability
          (fun index ↦
            finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
              index (initialData.initialState index)
              generator duration hDuration.le)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet)
      (rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData) := by
  intro openSet hOpen
  let pointwiseLowerEnvelope : EReal :=
    ⨆ path, ⨆ (_hPath : path ∈ openSet),
      -(rengerTheoremFourOneHybridBVCompleteRate
        generator hDuration initialData path : EReal)
  have hInfimumToEnvelope :
      -(⨅ path, ⨅ (_hPath : path ∈ openSet),
          (rengerTheoremFourOneHybridBVCompleteRate
            generator hDuration initialData path : EReal)) ≤
        pointwiseLowerEnvelope := by
    rw [EReal.neg_le]
    apply le_iInf
    intro path
    apply le_iInf
    intro hPath
    apply EReal.neg_le_of_neg_le
    exact le_iSup_of_le path (le_iSup_of_le hPath le_rfl)
  apply hInfimumToEnvelope.trans
  apply iSup_le
  intro path
  apply iSup_le
  intro hPath
  by_cases hCompleteRate :
      rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData path = ⊤
  · rw [hCompleteRate]
    exact bot_le
  · exact
      neg_rengerTheoremFourOneHybridBVCompleteRate_le_liminf_scaledEventLogProbability_deterministicInitialReference_openSet
        generator hDuration initialData path hCompleteRate hOpen hPath

end

end FiniteMarkovProcesses.InformationTheory
