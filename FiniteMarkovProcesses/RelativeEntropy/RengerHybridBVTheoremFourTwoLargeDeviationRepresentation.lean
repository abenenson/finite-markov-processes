/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVJointClosedUpperBound
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoOpenLowerBound

/-!
# Renger Theorem 4.2 hybrid-BV large-deviation representation

This module assembles the exact empirical-initial positive-replica source, total hybrid-BV
observation, complete initial-plus-dynamic rate, closed upper bound, open lower bound, good-rate
compactness, Borel topology, and theorem-labelled provenance into one literal representation.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- The microscopic positive-replica formulation of Theorem 4.2 satisfies the literal closed-set
upper bound.  This is the exact transport of the mixed observation-law theorem through the
already proved measurable total hybrid-BV observation map. -/
theorem rengerTheoremFourTwoHybridBV_hasLargeDeviationUpperBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun index => rengerTheoremFourTwoPositiveReplicaFamilyLaw
          initialData index generator duration hDuration.le)
        (fun _index family =>
          finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
        finiteStateMarkovJumpParticleSpeed)
      (rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData) := by
  intro closedPathTarget hClosedPathTarget
  have hMacroscopicUpper :=
    rengerTheoremFourTwoHybridBVObservationLaw_closedUpperBound
      initialData generator duration hDuration closedPathTarget hClosedPathTarget
  let microscopicScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => rengerTheoremFourTwoPositiveReplicaFamilyLaw
        initialData index generator duration hDuration.le)
      (fun _index family =>
        finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
      finiteStateMarkovJumpParticleSpeed successorIndex closedPathTarget
  let macroscopicScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => rengerTheoremFourTwoHybridBVObservationLaw
        initialData index generator duration hDuration.le)
      (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget
  have hScaledLogEquality : microscopicScaledLog = macroscopicScaledLog := by
    funext successorIndex
    unfold microscopicScaledLog macroscopicScaledLog scaledEventLogProbability
    simp only [preimage_id]
    rw [← Measure.map_apply
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
      hClosedPathTarget.measurableSet]
    rw [map_hybridBVObservation_rengerTheoremFourTwoPositiveReplicaFamilyLaw]
    rfl
  change limsup microscopicScaledLog atTop ≤ _
  rw [hScaledLogEquality]
  exact hMacroscopicUpper

/-- Full provenance-bearing Renger Theorem 4.2 representation on the actual hybrid-BV carrier. -/
noncomputable def rengerTheoremFourTwoHybridBVLargeDeviationRepresentation
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State) :
    DensityFluxLargeDeviationRepresentation
      (FiniteStateMarkovJumpPositiveReplicaFamily State)
      (RengerDirectionalFlowHybridBVPath State duration)
      ℝ (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal)
      Renger2018DirectionalFlowProvenance where
  microscopicLaw := fun index => rengerTheoremFourTwoPositiveReplicaFamilyLaw
    initialData index generator duration hDuration.le
  microscopicLaw_probability := fun index =>
    rengerTheoremFourTwoPositiveReplicaFamilyLaw_isProbabilityMeasure
      initialData index generator duration hDuration.le
  observation := fun _index family =>
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family
  observation_measurable := fun _index =>
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
  speed := finiteStateMarkovJumpParticleSpeed
  speed_pos := finiteStateMarkovJumpParticleSpeed_pos
  speed_tendsto_atTop := finiteStateMarkovJumpParticleSpeed_tendsto_atTop
  rateData := rengerDirectionalFlowHybridBVCompleteRateData
    generator hDuration initialData.initialRate
  topology_generates_measurableSpace :=
    FiniteIntervalHybridBVPath.measurableSpace_eq_borel
  rate_good := by
    simpa only [rengerTheoremFourTwoHybridBVCompleteRate] using!
      rengerTheoremFourTwoHybridBVCompleteRate_isGoodRateFunction
        generator hDuration initialData
  provenance := ⟨.theoremFourTwo⟩
  upperBound := rengerTheoremFourTwoHybridBV_hasLargeDeviationUpperBound
    generator hDuration initialData
  lowerBound := rengerTheoremFourTwoHybridBV_hasLargeDeviationLowerBound
    generator hDuration initialData

end

end FiniteMarkovProcesses.InformationTheory
