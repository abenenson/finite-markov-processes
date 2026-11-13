/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoOpenLowerBound
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovInvariantIIDInitialLDP
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpIIDHybridBVObservationTransport

/-!
# Renger Corollary 4.16 hybrid-BV open lower bound

This module specializes the Theorem 4.2 lower bound to Corollary 4.16 without conflating their
source contracts.  Corollary 4.16 retains its unique invariant distribution and its genuinely
IID-initialized labelled replica law.  The separately proved observation transport identifies its
empirical hybrid-BV pushforward with the canonical count-type mixture used by Theorem 4.2; the
labelled microscopic laws themselves remain distinct.

The invariant relative-entropy initial rate is identified definitionally from the independently
proved invariant-IID initial LDP.  No uniqueness premise or stationary source is promoted back to
the generic Theorem 4.2 regime.
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

/-- The Theorem 4.2 count-type source instantiated from an invariant IID sample has exactly the
same empirical hybrid-BV observation law as genuinely IID-initialized labelled replicas. -/
theorem rengerInvariantIIDTheoremFourTwoHybridBVObservationLaw_eq_corollaryFourSixteenLaw
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (duration : ℝ) (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    rengerTheoremFourTwoHybridBVObservationLaw
        (rengerInvariantIIDInitialLargeDeviationData stationary)
        successorIndex generator duration hDuration =
      finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
        generator stationary duration hDuration successorIndex := by
  unfold rengerTheoremFourTwoHybridBVObservationLaw
    rengerInvariantIIDInitialLargeDeviationData
    finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
  exact
    (finiteStateMarkovJumpIIDHybridBVObservationLaw_eq_randomEmpiricalTypeHybridBVObservationLaw
      successorIndex stationary.pmf generator duration hDuration
        (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
          stationary.pmf generator duration hDuration)).symm

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The Theorem 4.2 complete rate instantiated at the invariant-IID initial LDP is exactly
Corollary 4.16's independently named complete rate. -/
theorem rengerInvariantIIDTheoremFourTwoHybridBVCompleteRate_eq_corollaryFourSixteenCompleteRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    rengerTheoremFourTwoHybridBVCompleteRate generator hDuration
        (rengerInvariantIIDInitialLargeDeviationData initialData.stationary) =
      rengerCorollaryFourSixteenHybridBVCompleteRate generator hDuration initialData := by
  rfl

/-- Renger Corollary 4.16's genuinely invariant-IID microscopic source satisfies the literal
hybrid-BV open-set lower bound at its invariant-relative-entropy plus dynamic complete rate. -/
theorem rengerCorollaryFourSixteenInvariantIIDHybridBV_hasLargeDeviationLowerBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    HasLargeDeviationLowerBound
      (fun successorIndex openSet ↦
        scaledEventLogProbability
          (fun index ↦ finiteStateMarkovJumpInvariantIIDMicroscopicLaw
            generator initialData.stationary duration hDuration.le index)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet)
      (rengerCorollaryFourSixteenHybridBVCompleteRate
        generator hDuration initialData) := by
  have hGeneric := rengerTheoremFourTwoHybridBV_hasLargeDeviationLowerBound
    generator hDuration
      (rengerInvariantIIDInitialLargeDeviationData initialData.stationary)
  intro openSet hOpen
  have hLower := hGeneric openSet hOpen
  rw [
    rengerInvariantIIDTheoremFourTwoHybridBVCompleteRate_eq_corollaryFourSixteenCompleteRate
      generator hDuration initialData] at hLower
  have hScaled (successorIndex : ℕ) :
      scaledEventLogProbability
          (fun index ↦ finiteStateMarkovJumpInvariantIIDMicroscopicLaw
            generator initialData.stationary duration hDuration.le index)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet =
        scaledEventLogProbability
          (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
            (rengerInvariantIIDInitialLargeDeviationData initialData.stationary)
              index generator duration hDuration.le)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet := by
    have hMap :
        MeasureTheory.Measure.map
            (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
            (finiteStateMarkovJumpInvariantIIDMicroscopicLaw generator initialData.stationary
              duration hDuration.le successorIndex) =
          MeasureTheory.Measure.map
            (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
            (rengerTheoremFourTwoPositiveReplicaFamilyLaw
              (rengerInvariantIIDInitialLargeDeviationData initialData.stationary)
                successorIndex generator duration hDuration.le) := by
      rw [map_hybridBVObservation_rengerTheoremFourTwoPositiveReplicaFamilyLaw]
      change finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
          generator initialData.stationary duration hDuration.le successorIndex = _
      exact
        (rengerInvariantIIDTheoremFourTwoHybridBVObservationLaw_eq_corollaryFourSixteenLaw
          generator initialData.stationary duration hDuration.le successorIndex).symm
    have hProbability := congrArg
      (fun law : MeasureTheory.Measure _ ↦ law openSet) hMap
    unfold scaledEventLogProbability
    congr 2
    simpa only [MeasureTheory.Measure.map_apply
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
      hOpen.measurableSet] using hProbability
  simpa only [hScaled] using hLower

end

end FiniteMarkovProcesses.InformationTheory
