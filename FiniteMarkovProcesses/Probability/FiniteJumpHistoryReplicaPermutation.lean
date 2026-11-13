/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservationMeasurability

/-!
# Replica permutation invariance of empirical jump-history observations

This module reindexes a fixed positive family of finite jump histories by a permutation of its
replica coordinates.  The labelled microscopic family changes, but every empirical density and
directional-flow observation is unchanged.  The result includes the total hybrid bounded-
variation observation with its measurable ordered-or-fallback extension.

No probability law, Markov generator, or large-deviation estimate enters here.

## Main declarations

- `positiveFiniteJumpHistoryReplicasReindex`: replica-coordinate reindexing.
- `positiveFiniteJumpHistoryReplicasReindexing`: its measurable equivalence.
- `empiricalDensityDirectionalFlowFullDerivative_reindexing`: derivative-family invariance.
- `empiricalDensityDirectionalFlowTotalHybridBVObservation_reindexing`: total observation
  invariance.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

namespace PositiveFiniteJumpHistoryReplicas

/-- Reindex a positive replica family by a permutation of its replica coordinates.  The output
coordinate `permutation replica` contains the input coordinate `replica`. -/
def positiveFiniteJumpHistoryReplicasReindex
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    PositiveFiniteJumpHistoryReplicas State successorIndex :=
  fun replica => histories (permutation.symm replica)

/-- Measurable equivalence implementing replica-coordinate reindexing. -/
def positiveFiniteJumpHistoryReplicasReindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1))) :
    PositiveFiniteJumpHistoryReplicas State successorIndex ≃ᵐ
      PositiveFiniteJumpHistoryReplicas State successorIndex :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (successorIndex + 1) => FiniteJumpHistory State) permutation

omit [Fintype State] [MeasurableSingletonClass State] [DecidableEq State] in
/-- The measurable equivalence acts by replica reindexing. -/
@[simp]
theorem positiveFiniteJumpHistoryReplicasReindexing_apply
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (replica : Fin (successorIndex + 1)) :
    positiveFiniteJumpHistoryReplicasReindexing successorIndex permutation histories replica =
      histories (permutation.symm replica) := by
  have hApply := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (successorIndex + 1) => FiniteJumpHistory State)
    permutation histories (permutation.symm replica)
  simpa using! hApply

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical initial density is invariant under replica reindexing. -/
theorem empiricalInitialDensity_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) :
    empiricalInitialDensity successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) state =
      empiricalInitialDensity successorIndex histories state := by
  unfold empiricalInitialDensity
  congr 1
  simpa only [positiveFiniteJumpHistoryReplicasReindex] using
    permutation.symm.sum_comp
      (fun replica => FiniteJumpHistory.stateMembershipIndicator
        (histories replica).initialState state)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical density at every time is invariant under replica reindexing. -/
theorem empiricalDensityAtTime_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) :
    empiricalDensityAtTime successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) time state =
      empiricalDensityAtTime successorIndex histories time state := by
  unfold empiricalDensityAtTime
  congr 1
  simpa only [positiveFiniteJumpHistoryReplicasReindex] using
    permutation.symm.sum_comp
      (fun replica => FiniteJumpHistory.stateMembershipIndicator
        ((histories replica).stateAtTime time) state)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every empirical directional-flow coordinate is invariant under replica reindexing. -/
theorem empiricalSpecificDirectionalFlowAtTime_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) :
    empiricalSpecificDirectionalFlowAtTime successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) time source target =
      empiricalSpecificDirectionalFlowAtTime
        successorIndex histories time source target := by
  unfold empiricalSpecificDirectionalFlowAtTime
  congr 1
  simpa only [positiveFiniteJumpHistoryReplicasReindex] using
    permutation.symm.sum_comp
      (fun replica => ((histories replica).directedTransitionCountAtTime
        time source target : ℝ))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The continuity-reconstructed empirical density is invariant under replica reindexing. -/
theorem empiricalContinuityDensityAtTime_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) :
    empiricalContinuityDensityAtTime successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) time state =
      empiricalContinuityDensityAtTime successorIndex histories time state := by
  unfold empiricalContinuityDensityAtTime
  rw [empiricalInitialDensity_reindexing]
  simp_rw [empiricalSpecificDirectionalFlowAtTime_reindexing]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The tagged initial empirical value is invariant under replica reindexing. -/
theorem empiricalDensityDirectionalFlowInitialL1Value_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    empiricalDensityDirectionalFlowInitialL1Value successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) =
      empiricalDensityDirectionalFlowInitialL1Value successorIndex histories := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  cases coordinate with
  | inl state =>
      simpa only [PiLp.continuousLinearEquiv_apply,
        empiricalDensityDirectionalFlowInitialL1Value_density] using
        empiricalInitialDensity_reindexing successorIndex permutation histories state
  | inr edge =>
      simp only [PiLp.continuousLinearEquiv_apply,
        empiricalDensityDirectionalFlowInitialL1Value_flow]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal empirical event-step representative is invariant under replica reindexing. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) time =
      empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories time := by
  rw [empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_continuity,
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_continuity]
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  cases coordinate with
  | inl state =>
      simpa only [PiLp.continuousLinearEquiv_apply,
        empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using
        empiricalContinuityDensityAtTime_reindexing
          successorIndex permutation histories time state
  | inr edge =>
      simpa only [PiLp.continuousLinearEquiv_apply,
        empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using
        empiricalSpecificDirectionalFlowAtTime_reindexing
          successorIndex permutation histories time edge.val.1 edge.val.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit strong-`L1` empirical path is invariant under replica reindexing. -/
theorem empiricalDensityDirectionalFlowExplicitL1Path_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) :
    empiricalDensityDirectionalFlowExplicitL1Path successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) duration =
      empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration := by
  let reindexedHistories := positiveFiniteJumpHistoryReplicasReindex
    successorIndex permutation histories
  let reindexedRepresentative := empiricalDensityDirectionalFlowEventStepL1ValueAtTime
    successorIndex reindexedHistories
  let representative := empiricalDensityDirectionalFlowEventStepL1ValueAtTime
    successorIndex histories
  have hRepresentative : reindexedRepresentative = representative := by
    funext time
    exact empiricalDensityDirectionalFlowEventStepL1ValueAtTime_reindexing
      successorIndex permutation histories time
  have hReindexed := empiricalDensityDirectionalFlowExplicitL1Path_represents
    successorIndex reindexedHistories duration
  have hOriginal := empiricalDensityDirectionalFlowExplicitL1Path_represents
    successorIndex histories duration
  have hRepresentativeFormula :
      empiricalDensityDirectionalFlowEventStepL1ValueAtTime
          successorIndex reindexedHistories =
        empiricalDensityDirectionalFlowEventStepL1ValueAtTime
          successorIndex histories := by
    exact hRepresentative
  rw [hRepresentativeFormula] at hReindexed
  rcases hReindexed with ⟨hMemReindexed, hReindexed⟩
  rcases hOriginal with ⟨hMemOriginal, hOriginal⟩
  calc
    empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex reindexedHistories duration =
        hMemReindexed.toLp representative := hReindexed.symm
    _ = hMemOriginal.toLp representative :=
      hMemReindexed.toLp_congr hMemOriginal (Filter.Eventually.of_forall fun _ => rfl)
    _ = empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration := hOriginal

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The full signed derivative family is invariant under replica reindexing. -/
theorem empiricalDensityDirectionalFlowFullDerivative_reindexing
    (successorIndex : ℕ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    empiricalDensityDirectionalFlowFullDerivative successorIndex
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) coordinate =
      empiricalDensityDirectionalFlowFullDerivative
        successorIndex histories coordinate := by
  unfold empiricalDensityDirectionalFlowFullDerivative
  congr 1
  simpa only [positiveFiniteJumpHistoryReplicasReindex] using
    permutation.symm.sum_comp
      (fun replica => (singleHistoryDensityDirectionalFlowFullDerivative
        successorIndex coordinate (histories replica)).toSignedMeasure)

section Topological

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The ordered empirical hybrid-BV observation is invariant under replica reindexing. -/
theorem orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_reindexing
    (successorIndex : ℕ) (duration : ℝ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : OrderedPositiveFiniteJumpHistoryReplicas
      State successorIndex duration) :
    orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
        successorIndex duration (fun replica => histories (permutation.symm replica)) =
      orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
        successorIndex duration histories := by
  apply FiniteIntervalHybridBVPath.ext
  apply FiniteIntervalL1DerivativePath.ext
  · simp only [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation,
      empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path]
    exact empiricalDensityDirectionalFlowExplicitL1Path_reindexing
      successorIndex permutation
        (orderedReplicaHistories successorIndex duration histories) duration
  · funext coordinate
    rw [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_derivative,
      orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_derivative]
    exact empiricalDensityDirectionalFlowFullDerivative_reindexing
      successorIndex permutation
        (orderedReplicaHistories successorIndex duration histories) coordinate

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] in
/-- Coordinatewise ordered-or-fallback totalization commutes with replica reindexing. -/
theorem orderedPositiveFiniteJumpHistoryReplicasOrFallback_reindexing
    (successorIndex : ℕ) (duration : ℝ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    orderedPositiveFiniteJumpHistoryReplicasOrFallback successorIndex duration
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) =
      fun replica =>
        orderedPositiveFiniteJumpHistoryReplicasOrFallback
          successorIndex duration histories (permutation.symm replica) := by
  funext replica
  simp only [orderedPositiveFiniteJumpHistoryReplicasOrFallback,
    positiveFiniteJumpHistoryReplicasReindex]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] in
/-- The total empirical density--directional-flow hybrid-BV observation is invariant under every
replica-coordinate permutation, including on the measurable fallback complement. -/
theorem empiricalDensityDirectionalFlowTotalHybridBVObservation_reindexing
    (successorIndex : ℕ) (duration : ℝ)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration
        (positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories) =
      empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories := by
  unfold empiricalDensityDirectionalFlowTotalHybridBVObservation
  rw [orderedPositiveFiniteJumpHistoryReplicasOrFallback_reindexing]
  exact orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_reindexing
    successorIndex duration permutation
      (orderedPositiveFiniteJumpHistoryReplicasOrFallback
        successorIndex duration histories)

end Topological

end PositiveFiniteJumpHistoryReplicas

end

end FiniteMarkovProcesses.Probability
