/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryReplicaPermutation
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation

/-!
# Permutation covariance of deterministic-initial Markov-jump replicas

The labelled heterogeneous replica law is covariant under a common permutation of the initial
configuration and history coordinates.  Its empirical density--directional-flow hybrid-BV
pushforward is therefore invariant.  Since two finite configurations have the same empirical
count type exactly when they differ by a replica permutation, the hybrid law depends only on that
count type and not on the chosen labelled representative.

No large-deviation estimate or asymptotic exchangeability claim enters here.

## Main declarations

- `map_reindexing_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure`:
  labelled product-law covariance.
- `finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_permutedConfiguration`:
  empirical-law permutation invariance.
- `finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_empiricalType_eq`:
  representative-independent same-count-type law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] [Nonempty State] in
/-- Reindexing the product history law initialized from a permuted configuration gives exactly
the product history law initialized from the original labelled configuration. -/
theorem map_reindexing_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map
        (positiveFiniteJumpHistoryReplicasReindexing
          (State := State) successorIndex permutation)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          (fun replica => initialConfiguration (permutation replica))
          generator duration hDuration).toMeasure =
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure := by
  let : ∀ replica : Fin (successorIndex + 1),
      IsProbabilityMeasure
        (finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration replica)) generator duration) :=
    fun replica => ⟨finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure (initialConfiguration replica)) generator duration hDuration⟩
  rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure,
    finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  exact Measure.pi_map_piCongrLeft permutation
    (fun replica : Fin (successorIndex + 1) =>
      finiteStateMarkovJumpDensityMeasure
        (PMF.pure (initialConfiguration replica)) generator duration)

/-- Permuting a deterministic initial configuration does not change its total empirical
density--directional-flow hybrid-BV observation law. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_permutedConfiguration
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (permutation : Equiv.Perm (Fin (successorIndex + 1)))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex (fun replica => initialConfiguration (permutation replica))
        generator duration hDuration =
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration := by
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw,
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw]
  let observation := empiricalDensityDirectionalFlowTotalHybridBVObservation
    (State := State) successorIndex duration
  let reindexing := positiveFiniteJumpHistoryReplicasReindexing
    (State := State) successorIndex permutation
  let permutedLaw :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      (fun replica => initialConfiguration (permutation replica))
      generator duration hDuration).toMeasure
  have hObservation : observation ∘ reindexing = observation := by
    funext histories
    have hReindexing : reindexing histories =
        positiveFiniteJumpHistoryReplicasReindex
          successorIndex permutation histories := by
      funext replica
      exact positiveFiniteJumpHistoryReplicasReindexing_apply
        successorIndex permutation histories replica
    change observation (reindexing histories) = observation histories
    rw [hReindexing]
    exact empiricalDensityDirectionalFlowTotalHybridBVObservation_reindexing
      successorIndex duration permutation histories
  calc
    Measure.map observation permutedLaw =
        Measure.map (observation ∘ reindexing) permutedLaw := by rw [hObservation]
    _ = Measure.map observation (Measure.map reindexing permutedLaw) := by
      rw [Measure.map_map
        (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
          (State := State) successorIndex duration)
        reindexing.measurable]
    _ = Measure.map observation
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
      rw [map_reindexing_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure]

/-- Any two deterministic configurations with the same state counts induce the same empirical
hybrid-BV observation law. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_stateCount_eq
    (successorIndex : ℕ)
    (first second : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (hCount : ∀ state,
      finiteIIDPositiveSampleStateCount successorIndex first state =
        finiteIIDPositiveSampleStateCount successorIndex second state) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex first generator duration hDuration =
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex second generator duration hDuration := by
  rcases exists_domPermutation_smul_eq_of_stateCount_eq first second hCount with
    ⟨domainPermutation, hPermutation⟩
  let permutation : Equiv.Perm (Fin (successorIndex + 1)) :=
    DomMulAct.mk.symm domainPermutation
  have hConfiguration :
      (fun replica => first (permutation replica)) = second := by
    change domainPermutation • first = second
    exact hPermutation
  rw [← hConfiguration]
  exact (finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_permutedConfiguration
    successorIndex first permutation generator duration hDuration).symm

/-- The deterministic empirical hybrid-BV law depends only on the complete empirical count type,
not on a labelled representative of that type. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_empiricalType_eq
    (successorIndex : ℕ)
    (first second : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (hType : finiteIIDPositiveSampleEmpiricalType successorIndex first =
      finiteIIDPositiveSampleEmpiricalType successorIndex second) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex first generator duration hDuration =
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex second generator duration hDuration := by
  apply finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_stateCount_eq
  intro state
  have hCoordinate := congrArg
    (fun empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex =>
      (empiricalType.count state : ℕ)) hType
  simpa [finiteIIDPositiveSampleEmpiricalType] using hCoordinate

end

end FiniteMarkovProcesses.Probability
