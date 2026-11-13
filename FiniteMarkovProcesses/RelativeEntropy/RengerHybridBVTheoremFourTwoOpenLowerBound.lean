/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoBoundaryOpenLowerBound
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVCompleteRateCompactness

/-!
# Renger Theorem 4.2 hybrid-BV open lower bound

This module assembles the interior and lower-boundary pointwise estimates into the literal
hybrid-BV open-set lower bound for Renger Theorem 4.2.  Every finite complete-rate candidate first
recovers an admissible representation path and finite initial and dynamic sectors.  The supplied
left-continuity hypothesis is used only when the recovered initial density lies on the lower
simplex boundary.

This is the lower half of the theorem's path LDP.  It does not identify the invariant-i.i.d.
Corollary 4.16 source, prove the closed upper bound, or infer any carrier equivalence beyond the
exact hybrid-BV observation already constructed.
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

/-- Every finite complete-rate Theorem 4.2 candidate satisfies the pointwise hybrid-open lower
estimate at its exact initial-plus-dynamic rate. -/
theorem
neg_rengerTheoremFourTwoHybridBVCompleteRate_le_liminf_scaledEventLogProbability_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hCompleteRate :
      rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData path ≠ ⊤)
    {openSet : Set (RengerDirectionalFlowHybridBVPath State duration)}
    (hOpen : IsOpen openSet) (hTarget : path ∈ openSet) :
    -(rengerTheoremFourTwoHybridBVCompleteRate
        generator hDuration initialData path : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
              initialData index generator duration hDuration.le)
            (fun _index family ↦
              finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  have hAdmissible : RengerDirectionalFlowHybridBVAdmissible path hDuration := by
    by_contra hPath
    exact hCompleteRate (by
      simpa only [rengerTheoremFourTwoHybridBVCompleteRate] using
        rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
          generator hDuration initialData.initialRate hPath)
  let representationPath :
      RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
    ⟨path, hAdmissible⟩
  have hSumNeTop :
      rengerDirectionalFlowHybridBVLiftedInitialCost initialData.initialRate path +
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ⊤ := by
    rw [← rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
      generator hDuration initialData.initialRate hAdmissible]
    exact hCompleteRate
  have hInitialCostNeTop :
      rengerDirectionalFlowHybridBVLiftedInitialCost initialData.initialRate path ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hSumNeTop).1
  have hDynamicRateNeTop :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hSumNeTop).2
  have hLiftedInitialCostEq :
      rengerDirectionalFlowHybridBVLiftedInitialCost initialData.initialRate path =
        initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath) := by
    rw [rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
      initialData.initialRate hDuration hAdmissible]
    congr 1
  have hInitialRateNeTop :
      initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath) ≠
        ⊤ := by
    rw [← hLiftedInitialCostEq]
    exact hInitialCostNeTop
  have hCompleteRateEq :
      rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData path =
        initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity representationPath) +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
    rw [rengerTheoremFourTwoHybridBVCompleteRate,
      rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
        generator hDuration initialData.initialRate hAdmissible,
      hLiftedInitialCostEq]
  have hLower :=
    neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwo_openSet
      generator hDuration initialData representationPath hDynamicRateNeTop hInitialRateNeTop
        hOpen hTarget
  rw [hCompleteRateEq, EReal.coe_ennreal_add,
    EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
      (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg]
  exact hLower

/-- Renger Theorem 4.2's empirical-initial source satisfies the literal hybrid-BV open-set lower
bound at the complete initial-plus-dynamic rate. -/
theorem rengerTheoremFourTwoHybridBV_hasLargeDeviationLowerBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State) :
    HasLargeDeviationLowerBound
      (fun successorIndex openSet ↦
        scaledEventLogProbability
          (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
            initialData index generator duration hDuration.le)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet)
      (rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData) := by
  intro openSet hOpen
  let pointwiseLowerEnvelope : EReal :=
    ⨆ path, ⨆ (_hPath : path ∈ openSet),
      -(rengerTheoremFourTwoHybridBVCompleteRate
        generator hDuration initialData path : EReal)
  have hInfimumToEnvelope :
      -(⨅ path, ⨅ (_hPath : path ∈ openSet),
          (rengerTheoremFourTwoHybridBVCompleteRate
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
      rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData path = ⊤
  · rw [hCompleteRate]
    exact bot_le
  · exact
      neg_rengerTheoremFourTwoHybridBVCompleteRate_le_liminf_scaledEventLogProbability_openSet
        generator hDuration initialData path hCompleteRate hOpen hPath

end

end FiniteMarkovProcesses.InformationTheory
