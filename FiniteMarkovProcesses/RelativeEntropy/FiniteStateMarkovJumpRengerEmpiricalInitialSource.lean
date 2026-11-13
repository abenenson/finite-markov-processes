/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateJumpDirectionalFlowLDPBoundary
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpRandomEmpiricalTypeHybridBVObservation

/-!
# Renger empirical-initial Markov-jump source

This module instantiates the canonical random empirical-type Markov-jump source from the exact
finite count-type law associated with `RengerTheoremFourTwoInitialData`. The microscopic and
hybrid-BV laws are normalized, hybrid observation commutes with the mixture, and the microscopic
  initial
density has exactly the theorem contract's supplied simplex law.

The construction chooses the canonical representative of every empirical count type.  It does
not assert representative-independent labelled laws, conditional path estimates, or a dynamic
large-deviation principle.

## Main declarations

- `rengerTheoremFourTwoPositiveReplicaFamilyLaw`: canonical random-initial microscopic source.
- `rengerTheoremFourTwoHybridBVObservationLaw`: its exact hybrid-BV observation law.
- `map_initialDensity_rengerTheoremFourTwoPositiveReplicaFamilyLaw`: exact supplied initial-law
  recovery.
- `rengerTheoremFourTwoHybridBVObservationLaw_apply_eq_sum`: finite conditional disintegration.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Canonical random-initial common-carrier source associated with Theorem 4.2's empirical
count-type law. -/
noncomputable def rengerTheoremFourTwoPositiveReplicaFamilyLaw
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw successorIndex
    (initialData.initialEmpiricalTypeLaw successorIndex) generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Theorem 4.2's canonical random-initial microscopic source is normalized. -/
theorem rengerTheoremFourTwoPositiveReplicaFamilyLaw_isProbabilityMeasure
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (rengerTheoremFourTwoPositiveReplicaFamilyLaw
        initialData successorIndex generator duration hDuration) := by
  let : IsProbabilityMeasure (initialData.initialEmpiricalTypeLaw successorIndex) :=
    initialData.initialEmpiricalTypeLaw_probability successorIndex
  unfold rengerTheoremFourTwoPositiveReplicaFamilyLaw
  exact finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_isProbabilityMeasure
    successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
      generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The empirical initial-density pushforward of Theorem 4.2's microscopic source is exactly its
supplied simplex law. -/
theorem map_initialDensity_rengerTheoremFourTwoPositiveReplicaFamilyLaw
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
        (rengerTheoremFourTwoPositiveReplicaFamilyLaw
          initialData successorIndex generator duration hDuration) =
      initialData.initialLaw successorIndex := by
  calc
    Measure.map finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
        (rengerTheoremFourTwoPositiveReplicaFamilyLaw
          initialData successorIndex generator duration hDuration) =
        Measure.map FiniteIIDPositiveEmpiricalType.probabilityDensity
          (initialData.initialEmpiricalTypeLaw successorIndex) := by
      unfold rengerTheoremFourTwoPositiveReplicaFamilyLaw
      exact
        map_initialDensity_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
          successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
            generator duration hDuration
    _ = initialData.initialLaw successorIndex :=
      (initialData.initialLaw_eq_map_probabilityDensity successorIndex).symm

/-- Canonical random-initial hybrid-BV observation law associated with Theorem 4.2's empirical
count-type law. -/
noncomputable def rengerTheoremFourTwoHybridBVObservationLaw
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw successorIndex
    (initialData.initialEmpiricalTypeLaw successorIndex) generator duration hDuration

/-- Theorem 4.2's canonical random-initial hybrid-BV observation law is normalized. -/
theorem rengerTheoremFourTwoHybridBVObservationLaw_isProbabilityMeasure
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (rengerTheoremFourTwoHybridBVObservationLaw
        initialData successorIndex generator duration hDuration) := by
  let : IsProbabilityMeasure (initialData.initialEmpiricalTypeLaw successorIndex) :=
    initialData.initialEmpiricalTypeLaw_probability successorIndex
  unfold rengerTheoremFourTwoHybridBVObservationLaw
  exact finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_isProbabilityMeasure
    successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
      generator duration hDuration

/-- Theorem 4.2's hybrid law is exactly the total observation of its microscopic source. -/
theorem map_hybridBVObservation_rengerTheoremFourTwoPositiveReplicaFamilyLaw
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map
        (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
        (rengerTheoremFourTwoPositiveReplicaFamilyLaw
          initialData successorIndex generator duration hDuration) =
      rengerTheoremFourTwoHybridBVObservationLaw
        initialData successorIndex generator duration hDuration := by
  unfold rengerTheoremFourTwoPositiveReplicaFamilyLaw
    rengerTheoremFourTwoHybridBVObservationLaw
  exact
    map_hybridBVObservation_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
      successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
        generator duration hDuration

/-- Eventwise Theorem 4.2 hybrid disintegration over the exact empirical count-type law. -/
theorem rengerTheoremFourTwoHybridBVObservationLaw_apply
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hEvent : MeasurableSet event) :
    rengerTheoremFourTwoHybridBVObservationLaw
        initialData successorIndex generator duration hDuration event =
      ∫⁻ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
          empiricalType generator duration hDuration event
            ∂initialData.initialEmpiricalTypeLaw successorIndex := by
  unfold rengerTheoremFourTwoHybridBVObservationLaw
  exact finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply
    successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
      generator duration hDuration hEvent

/-- Theorem 4.2's eventwise hybrid disintegration is an ordinary finite sum. -/
theorem rengerTheoremFourTwoHybridBVObservationLaw_apply_eq_sum
    (initialData : RengerTheoremFourTwoInitialData State) (successorIndex : ℕ)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hEvent : MeasurableSet event) :
    rengerTheoremFourTwoHybridBVObservationLaw
        initialData successorIndex generator duration hDuration event =
      ∑ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
            empiricalType generator duration hDuration event *
          initialData.initialEmpiricalTypeLaw successorIndex {empiricalType} := by
  unfold rengerTheoremFourTwoHybridBVObservationLaw
  exact finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply_eq_sum
    successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
      generator duration hDuration hEvent

end

end FiniteMarkovProcesses.InformationTheory
