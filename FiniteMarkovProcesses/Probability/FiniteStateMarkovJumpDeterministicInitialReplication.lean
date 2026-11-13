/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpInitialStateMarginal
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpReplication

/-!
# Deterministic-initial independent Markov-jump replicas

This module constructs a finite product of Markov-jump histories whose coordinates may start from
different prospectively supplied states.  Every coordinate evolves with the same generator and
physical duration, but its initial law is the Dirac PMF at the corresponding configuration entry.
The product is normalized, its histories are genuinely independent, and their initial states
recover the supplied configuration almost surely.

This is the microscopic source needed before mixing over random empirical initial configurations.
It does not assert a path large-deviation bound or identify a macroscopic rate.

## Main declarations

- `finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure`: heterogeneous product law.
- `finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun`:
  coordinate independence.
- `finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map`: exact
  coordinate history marginal.
- `ae_initialState_eq_configuration_finiteStateMarkovJumpDeterministicInitialReplica`: exact
  almost-sure recovery of the supplied initial configuration.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- The normalized finite product of coordinate-specific deterministic-initial Markov-jump
history laws.  Every coordinate uses the same generator and duration. -/
noncomputable def finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    ProbabilityMeasure (Fin replicaCount → FiniteJumpHistory State) :=
  ProbabilityMeasure.pi fun replica =>
    finiteStateMarkovJumpProbabilityMeasure (PMF.pure (initialConfiguration replica))
      generator duration
      (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
        (PMF.pure (initialConfiguration replica)) generator duration hDuration)

/-- The underlying heterogeneous replica measure is literally the finite product of the
coordinate-specific Dirac-initial history measures. -/
@[simp]
theorem finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure =
      Measure.pi fun replica : Fin replicaCount =>
        finiteStateMarkovJumpDensityMeasure (PMF.pure (initialConfiguration replica))
          generator duration := by
  rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure,
    ProbabilityMeasure.toMeasure_pi]
  congr 1

/-- Coordinate histories are mutually independent under the heterogeneous deterministic-initial
replica law. -/
theorem
    finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    iIndepFun
      (fun replica : Fin replicaCount =>
        fun histories : Fin replicaCount → FiniteJumpHistory State => histories replica)
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure := by
  let : ∀ replica : Fin replicaCount,
      IsProbabilityMeasure
        (finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration replica)) generator duration) :=
    fun replica => ⟨finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure (initialConfiguration replica)) generator duration hDuration⟩
  rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  exact iIndepFun_pi fun _ => measurable_id.aemeasurable

/-- Each coordinate history has exactly the Markov-jump law initialized at its prospectively
supplied state. -/
theorem finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) (replica : Fin replicaCount) :
    Measure.map (Function.eval replica)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure =
      finiteStateMarkovJumpDensityMeasure (PMF.pure (initialConfiguration replica))
        generator duration := by
  let : ∀ coordinate : Fin replicaCount,
      IsProbabilityMeasure
        (finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration coordinate)) generator duration) :=
    fun coordinate => ⟨finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure (initialConfiguration coordinate)) generator duration hDuration⟩
  rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  exact (measurePreserving_eval
    (fun coordinate : Fin replicaCount =>
      finiteStateMarkovJumpDensityMeasure (PMF.pure (initialConfiguration coordinate))
        generator duration) replica).map_eq

/-- Reading all initial states from the heterogeneous history product gives the product of the
corresponding Dirac measures. -/
theorem map_initialState_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map
        (fun histories replica => (histories replica).initialState)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure =
      Measure.pi fun replica : Fin replicaCount =>
        Measure.dirac (initialConfiguration replica) := by
  let : ∀ replica : Fin replicaCount,
      IsProbabilityMeasure
        (finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration replica)) generator duration) :=
    fun replica => ⟨finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure (initialConfiguration replica)) generator duration hDuration⟩
  rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  rw [Measure.pi_map_pi fun _ => FiniteJumpHistory.measurable_initialState.aemeasurable]
  congr 1
  funext replica
  rw [finiteStateMarkovJumpDensityMeasureInitialStateMarginal
    (PMF.pure (initialConfiguration replica)) generator duration hDuration]
  exact PMF.toMeasure_pure (initialConfiguration replica)

/-- Almost surely, every coordinate history starts at the corresponding entry of the supplied
deterministic initial configuration. -/
theorem ae_initialState_eq_configuration_finiteStateMarkovJumpDeterministicInitialReplica
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure,
      ∀ replica, (histories replica).initialState = initialConfiguration replica := by
  rw [ae_all_iff]
  intro replica
  have hInitialState :
      ∀ᵐ state ∂(PMF.pure (initialConfiguration replica) : PMF State).toMeasure,
        state = initialConfiguration replica := by
    rw [PMF.toMeasure_pure (initialConfiguration replica)]
    simp
  rw [← finiteStateMarkovJumpDensityMeasureInitialStateMarginal
    (PMF.pure (initialConfiguration replica)) generator duration hDuration] at hInitialState
  have hHistory :
      ∀ᵐ history ∂finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration replica)) generator duration,
        history.initialState = initialConfiguration replica :=
    ae_of_ae_map FiniteJumpHistory.measurable_initialState.aemeasurable hInitialState
  rw [← finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
    initialConfiguration generator duration hDuration replica] at hHistory
  exact ae_of_ae_map (measurable_pi_apply replica).aemeasurable hHistory

/-- Reading all initial states gives the Dirac law at the supplied deterministic configuration,
not merely matching coordinate marginals. -/
theorem map_initialState_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_eq_dirac
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map
        (fun histories replica => (histories replica).initialState)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure =
      Measure.dirac initialConfiguration := by
  let : IsProbabilityMeasure
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure := inferInstance
  have hReadInitial :
      (fun histories : Fin replicaCount → FiniteJumpHistory State =>
          fun replica => (histories replica).initialState) =ᵐ[
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure]
        fun _ => initialConfiguration := by
    filter_upwards [
      ae_initialState_eq_configuration_finiteStateMarkovJumpDeterministicInitialReplica
        initialConfiguration generator duration hDuration] with histories hHistories
    funext replica
    exact hHistories replica
  calc
    Measure.map
        (fun histories replica => (histories replica).initialState)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure =
      Measure.map (fun _ => initialConfiguration)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure :=
      Measure.map_congr hReadInitial
    _ = Measure.dirac initialConfiguration := by
      rw [Measure.map_const, measure_univ, one_smul]

/-- Almost surely, every coordinate history has strictly ordered jump times before the common
physical horizon. -/
theorem ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure,
      ∀ replica, (histories replica).OrderedBefore duration := by
  rw [ae_all_iff]
  intro replica
  have hHistory :
      ∀ᵐ history ∂finiteStateMarkovJumpDensityMeasure
          (PMF.pure (initialConfiguration replica)) generator duration,
        history.OrderedBefore duration :=
    (ae_physicalAt_finiteStateMarkovJumpDensityMeasure
      (PMF.pure (initialConfiguration replica)) generator duration).mono
        fun _history hPhysical => hPhysical.1
  rw [← finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
    initialConfiguration generator duration hDuration replica] at hHistory
  exact ae_of_ae_map (measurable_pi_apply replica).aemeasurable hHistory

end

end FiniteMarkovProcesses.Probability
