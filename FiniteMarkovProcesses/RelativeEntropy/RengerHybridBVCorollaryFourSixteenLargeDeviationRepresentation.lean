/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoLargeDeviationRepresentation
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVCorollaryFourSixteenOpenLowerBound

/-!
# Renger Corollary 4.16 hybrid-BV large-deviation representation

This module assembles the genuinely invariant-IID labelled replica source, total hybrid-BV
observation, invariant-relative-entropy plus dynamic rate, good-rate compactness, literal LDP
bounds, and corollary-labelled provenance.  The exact observation transport to the count-type
Theorem 4.2 source is used only to inherit the closed upper bound; the IID microscopic law,
unique-invariant-law hypothesis, and independently transported open lower bound remain distinct.
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

/-- Corollary 4.16's genuinely invariant-IID microscopic source satisfies the literal closed-set
upper bound at its invariant-relative-entropy plus dynamic complete rate. -/
theorem rengerCorollaryFourSixteenInvariantIIDHybridBV_hasLargeDeviationUpperBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun index => finiteStateMarkovJumpInvariantIIDMicroscopicLaw
          generator initialData.stationary duration hDuration.le index)
        (fun _index family =>
          finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
        finiteStateMarkovJumpParticleSpeed)
      (rengerCorollaryFourSixteenHybridBVCompleteRate
        generator hDuration initialData) := by
  intro closedPathTarget hClosedPathTarget
  have hGenericUpper :=
    rengerTheoremFourTwoHybridBVObservationLaw_closedUpperBound
      (rengerInvariantIIDInitialLargeDeviationData initialData.stationary)
        generator duration hDuration closedPathTarget hClosedPathTarget
  let invariantIIDScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => finiteStateMarkovJumpInvariantIIDMicroscopicLaw
        generator initialData.stationary duration hDuration.le index)
      (fun _index family =>
        finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
      finiteStateMarkovJumpParticleSpeed successorIndex closedPathTarget
  let countTypeScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => rengerTheoremFourTwoHybridBVObservationLaw
        (rengerInvariantIIDInitialLargeDeviationData initialData.stationary)
          index generator duration hDuration.le)
      (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget
  have hScaledLogEquality : invariantIIDScaledLog = countTypeScaledLog := by
    funext successorIndex
    unfold invariantIIDScaledLog countTypeScaledLog scaledEventLogProbability
    simp only [preimage_id]
    congr 1
    congr 1
    rw [← Measure.map_apply
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
      hClosedPathTarget.measurableSet]
    change finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
        generator initialData.stationary duration hDuration.le successorIndex closedPathTarget = _
    rw [← rengerInvariantIIDTheoremFourTwoHybridBVObservationLaw_eq_corollaryFourSixteenLaw
      generator initialData.stationary duration hDuration.le successorIndex]
  change limsup invariantIIDScaledLog atTop ≤ _
  rw [hScaledLogEquality,
    ← rengerInvariantIIDTheoremFourTwoHybridBVCompleteRate_eq_corollaryFourSixteenCompleteRate
      generator hDuration initialData]
  exact hGenericUpper

/-- Full provenance-bearing Renger Corollary 4.16 representation on the genuinely invariant-IID
microscopic source and actual hybrid-BV carrier. -/
noncomputable def rengerCorollaryFourSixteenHybridBVLargeDeviationRepresentation
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    DensityFluxLargeDeviationRepresentation
      (FiniteStateMarkovJumpPositiveReplicaFamily State)
      (RengerDirectionalFlowHybridBVPath State duration)
      ℝ (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal)
      Renger2018DirectionalFlowProvenance where
  microscopicLaw := fun index => finiteStateMarkovJumpInvariantIIDMicroscopicLaw
    generator initialData.stationary duration hDuration.le index
  microscopicLaw_probability := fun index =>
    finiteStateMarkovJumpInvariantIIDMicroscopicLaw_isProbabilityMeasure
      generator initialData.stationary duration hDuration.le index
  observation := fun _index family =>
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family
  observation_measurable := fun _index =>
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
  speed := finiteStateMarkovJumpParticleSpeed
  speed_pos := finiteStateMarkovJumpParticleSpeed_pos
  speed_tendsto_atTop := finiteStateMarkovJumpParticleSpeed_tendsto_atTop
  rateData := rengerDirectionalFlowHybridBVCompleteRateData generator hDuration
    (rengerInvariantInitialCost initialData.stationary)
  topology_generates_measurableSpace :=
    FiniteIntervalHybridBVPath.measurableSpace_eq_borel
  rate_good := by
    simpa only [rengerCorollaryFourSixteenHybridBVCompleteRate] using!
      rengerCorollaryFourSixteenHybridBVCompleteRate_isGoodRateFunction
        generator hDuration initialData
  provenance := ⟨.corollaryFourSixteen⟩
  upperBound := rengerCorollaryFourSixteenInvariantIIDHybridBV_hasLargeDeviationUpperBound
    generator hDuration initialData
  lowerBound := rengerCorollaryFourSixteenInvariantIIDHybridBV_hasLargeDeviationLowerBound
    generator hDuration initialData

end

end FiniteMarkovProcesses.InformationTheory
