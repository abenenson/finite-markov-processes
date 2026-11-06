/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialReplication
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovOrderedSupport
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw

/-!
# Deterministic-initial replicas for time-dependent Markov jump rates

This module tensors the normalized reduced-history source for bounded time-dependent rates over a
finite prospectively supplied initial configuration.  Replica labels may start in different
states, while every coordinate evolves under the same time-dependent rate family.  The resulting
product is normalized, has the exact coordinate marginals, and its homogeneous specialization
recovers the existing deterministic-initial replica source.

These are source declarations only.  No law of large numbers, change-of-measure estimate, or
large-deviation lower bound is asserted here.

## Main declarations

- `finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure`.
- `finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinates_iIndepFun`.
- `finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map`.
- `finiteStateTimeDependentMarkovDeterministicInitialReplica_constant_toMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Normalized finite product of reduced time-dependent histories with a prospectively supplied
initial state for every labelled replica. -/
noncomputable def finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    ProbabilityMeasure (Fin replicaCount → FiniteJumpHistory State) :=
  ProbabilityMeasure.pi fun replica ↦
    finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure
      (PMF.pure (initialConfiguration replica)) rates duration

/-- The underlying replica measure is literally the finite product of its reduced-history
coordinate laws. -/
@[simp]
theorem finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure =
        Measure.pi fun replica : Fin replicaCount ↦
          finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration := by
  rw [finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure,
    ProbabilityMeasure.toMeasure_pi]
  congr 1

/-- Coordinate histories are mutually independent under the time-dependent product source. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinates_iIndepFun
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    iIndepFun
      (fun replica : Fin replicaCount ↦
        fun histories : Fin replicaCount → FiniteJumpHistory State ↦ histories replica)
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure := by
  let : ∀ replica : Fin replicaCount,
      IsProbabilityMeasure
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          (PMF.pure (initialConfiguration replica)) rates duration) :=
    fun replica ↦ ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      (PMF.pure (initialConfiguration replica)) rates duration⟩
  rw [finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- Every coordinate has exactly its Dirac-initial reduced time-dependent history law. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (replica : Fin replicaCount) :
    Measure.map (Function.eval replica)
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates duration).toMeasure =
      finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure (initialConfiguration replica)) rates duration := by
  let : ∀ coordinate : Fin replicaCount,
      IsProbabilityMeasure
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          (PMF.pure (initialConfiguration coordinate)) rates duration) :=
    fun coordinate ↦ ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      (PMF.pure (initialConfiguration coordinate)) rates duration⟩
  rw [finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  exact (measurePreserving_eval
    (fun coordinate : Fin replicaCount ↦
      finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure (initialConfiguration coordinate)) rates duration) replica).map_eq

/-- Almost surely, every coordinate in the deterministic-initial time-dependent replica family
has strictly ordered physical jump times before the common horizon. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    ∀ᵐ histories ∂
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates duration).toMeasure,
      ∀ replica, (histories replica).OrderedBefore (duration : ℝ) := by
  rw [ae_all_iff]
  intro replica
  have hHistory :=
    ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure (initialConfiguration replica)) rates duration
  rw [← finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
    initialConfiguration rates duration replica] at hHistory
  exact ae_of_ae_map (measurable_pi_apply replica).aemeasurable hHistory

/-- Constant rates recover the existing deterministic-initial physical replica source exactly at
the level of its underlying measure. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_constant_toMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : NNReal) :
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator.toTimeDependentMarkovRate duration).toMeasure =
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration duration.coe_nonneg).toMeasure := by
  rw [finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure,
    finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  congr 1
  funext replica
  exact finiteStateTimeDependentMarkovReducedHistoryMeasure_constant
    (PMF.pure (initialConfiguration replica)) generator duration

end

end FiniteMarkovProcesses.Probability
