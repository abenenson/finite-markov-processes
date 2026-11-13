/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalType
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialReplication
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpPositiveReplicaHybridBVObservation

/-!
# Hybrid-BV observation of deterministic-initial Markov-jump replicas

This module embeds a heterogeneous deterministic-initial replica product in the existing common
positive-replica carrier and pushes it through the existing total hybrid bounded-variation
observation.  The resulting microscopic and macroscopic laws are normalized.  The no-jump
fallback is absent almost surely, and the hybrid initial trace recovers exactly the empirical
density of the supplied initial configuration together with zero cumulative directional flow.

No large-deviation estimate or reduction from configurations to empirical types is asserted here.

## Main declarations

- `finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw`: common-carrier source law.
- `finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw`: exact total observation law.
- `ae_initialTrace_eq_deterministicConfigurationEmpiricalL1Value`: exact hybrid initial trace.
- `map_initialDensity_finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_eq_dirac`:
  exact empirical initial-density pushforward.
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

/-- Tagged deterministic initial value: the configuration's empirical density and zero cumulative
directional flow. -/
def deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      match coordinate with
      | Sum.inl state =>
          ((finiteIIDEmpiricalProbabilityDensity
            successorIndex initialConfiguration).weight state : ℝ)
      | Sum.inr _edge => 0

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Density coordinates of the deterministic initial value are the exact empirical frequencies. -/
@[simp]
theorem deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value_density
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (state : State) :
    deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value
        successorIndex initialConfiguration (Sum.inl state) =
      ((finiteIIDEmpiricalProbabilityDensity
        successorIndex initialConfiguration).weight state : ℝ) := by
  simp [deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Every cumulative directional-flow coordinate starts at zero. -/
@[simp]
theorem deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value_flow
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (edge : FiniteStateOffDiagonalEdge State) :
    deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value
        successorIndex initialConfiguration (Sum.inr edge) = 0 := by
  simp [deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value]

/-- Deterministic-initial replicas embedded into the existing successor-indexed common carrier. -/
noncomputable def finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  Measure.map
    (@Sigma.mk ℕ
      (fun index => PositiveFiniteJumpHistoryReplicas State index)
      successorIndex)
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure

omit [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] [Nonempty State] in
/-- Every deterministic-initial common-carrier law is exactly normalized. -/
theorem finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_isProbabilityMeasure
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
        successorIndex initialConfiguration generator duration hDuration) := by
  unfold finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection
      successorIndex).aemeasurable).2 inferInstance

omit [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] [Nonempty State] in
/-- The common-carrier law reduces exactly to the heterogeneous fixed-count product law. -/
theorem finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_eq_map_replicaLaw
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
        successorIndex initialConfiguration generator duration hDuration =
      Measure.map
        (@Sigma.mk ℕ
          (fun index => PositiveFiniteJumpHistoryReplicas State index)
          successorIndex)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
  rfl

/-- Exact total hybrid-BV observation law for a deterministic initial configuration. -/
noncomputable def finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  Measure.map
    (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
    (finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
      successorIndex initialConfiguration generator duration hDuration)

/-- The deterministic-initial hybrid law is the fixed-count heterogeneous product pushed through
the existing total slice observation. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration =
      Measure.map
        (empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration)
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
  unfold finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
  rw [Measure.map_map
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection successorIndex)]
  rfl

/-- Every deterministic-initial hybrid-BV observation law is exactly normalized. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_isProbabilityMeasure
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration) := by
  let : IsProbabilityMeasure
      (finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
        successorIndex initialConfiguration generator duration hDuration) :=
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_isProbabilityMeasure
      successorIndex initialConfiguration generator duration hDuration
  unfold finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
      duration).aemeasurable).2 inferInstance

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The empirical initial density read directly from the heterogeneous histories is almost surely
the empirical density of the supplied deterministic configuration. -/
theorem ae_initialDensity_eq_deterministicConfigurationEmpiricalDensity
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure,
      finiteIIDEmpiricalProbabilityDensity successorIndex
          (fun replica => (histories replica).initialState) =
        finiteIIDEmpiricalProbabilityDensity successorIndex initialConfiguration := by
  filter_upwards [
    ae_initialState_eq_configuration_finiteStateMarkovJumpDeterministicInitialReplica
      initialConfiguration generator duration hDuration] with histories hHistories
  congr 1
  funext replica
  exact hHistories replica

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The common-carrier empirical initial-density observation has the literal Dirac law at the
supplied configuration's empirical density. -/
theorem
    map_initialDensity_finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_eq_dirac
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
        (finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
          successorIndex initialConfiguration generator duration hDuration) =
      Measure.dirac
        (finiteIIDEmpiricalProbabilityDensity successorIndex initialConfiguration) := by
  unfold finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
  rw [Measure.map_map
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection successorIndex)]
  change Measure.map
      (finiteIIDEmpiricalProbabilityDensity successorIndex ∘
        positiveFiniteJumpHistoryReplicaInitialStates successorIndex)
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure = _
  rw [← Measure.map_map
    (measurable_finiteIIDEmpiricalProbabilityDensity successorIndex)
    (measurable_positiveFiniteJumpHistoryReplicaInitialStates successorIndex)]
  have hInitialMap :
      Measure.map (positiveFiniteJumpHistoryReplicaInitialStates successorIndex)
          (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration generator duration hDuration).toMeasure =
        Measure.dirac initialConfiguration := by
    simpa only [positiveFiniteJumpHistoryReplicaInitialStates] using!
      map_initialState_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_eq_dirac
        initialConfiguration generator duration hDuration
  rw [hInitialMap]
  rw [Measure.map_dirac' (measurable_finiteIIDEmpiricalProbabilityDensity successorIndex)]

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Almost surely, the total hybrid observation uses the ordered physical branch and its initial
trace is the literal empirical-density/zero-flow value of the histories. -/
theorem ae_initialTrace_eq_empiricalDensityDirectionalFlowInitialL1Value
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration.le).toMeasure,
      (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
        ⟨successorIndex, histories⟩).initialTrace =
          PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowInitialL1Value
            successorIndex histories := by
  filter_upwards [
    ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration.le] with histories hOrdered
  exact
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_of_ordered
      successorIndex duration hDuration histories hOrdered

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Almost surely, the hybrid initial trace is the supplied deterministic configuration's exact
empirical density together with zero cumulative directional flow. -/
theorem ae_initialTrace_eq_deterministicConfigurationEmpiricalL1Value
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration.le).toMeasure,
      (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
        ⟨successorIndex, histories⟩).initialTrace =
          deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value
            successorIndex initialConfiguration := by
  filter_upwards [
    ae_initialTrace_eq_empiricalDensityDirectionalFlowInitialL1Value
      successorIndex initialConfiguration generator duration hDuration,
    ae_initialState_eq_configuration_finiteStateMarkovJumpDeterministicInitialReplica
      initialConfiguration generator duration hDuration.le] with histories hTrace hInitial
  rw [hTrace]
  ext coordinate
  rcases coordinate with state | edge
  · rw [empiricalDensityDirectionalFlowInitialL1Value_density,
      deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value_density]
    unfold empiricalInitialDensity finiteIIDEmpiricalProbabilityDensity
      finiteIIDPositiveSampleStateCount
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    congr 1
    have hCount :
        (∑ replica,
          if initialConfiguration replica = state then 1 else 0 : ℕ) =
            (Finset.univ.filter fun replica =>
              initialConfiguration replica = state).card :=
      Finset.sum_boole
        (fun replica => initialConfiguration replica = state) Finset.univ
    calc
      (∑ replica,
          FiniteJumpHistory.stateMembershipIndicator
            (histories replica).initialState state) =
          ∑ replica,
            if initialConfiguration replica = state then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro replica _hReplica
        rw [hInitial replica]
        rfl
      _ = ((∑ replica,
          if initialConfiguration replica = state then 1 else 0 : ℕ) : ℝ) := by
        norm_cast
      _ = ((Finset.univ.filter fun replica =>
          initialConfiguration replica = state).card : ℝ) := by
        exact_mod_cast hCount
  · rw [empiricalDensityDirectionalFlowInitialL1Value_flow,
      deterministicConfigurationEmpiricalDensityDirectionalFlowInitialL1Value_flow]

/-- Canonical deterministic-initial common-carrier source indexed by an empirical count type. -/
noncomputable def finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw successorIndex
    empiricalType.representative generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Every canonical empirical-type common-carrier source is normalized. -/
theorem finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw_isProbabilityMeasure
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
        empiricalType generator duration hDuration) := by
  unfold finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
  exact
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_isProbabilityMeasure
      successorIndex empiricalType.representative generator duration hDuration

/-- Canonical hybrid-BV observation law indexed by an empirical count type. -/
noncomputable def finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw successorIndex
    empiricalType.representative generator duration hDuration

/-- Every canonical empirical-type hybrid-BV observation law is normalized. -/
theorem finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw_isProbabilityMeasure
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
        empiricalType generator duration hDuration) := by
  unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
  exact finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_isProbabilityMeasure
    successorIndex empiricalType.representative generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The empirical initial-density pushforward of the canonical type-indexed source is exactly
the Dirac law at that count type's simplex point. -/
theorem map_initialDensity_finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw_eq_dirac
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
        (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
          empiricalType generator duration hDuration) =
      Measure.dirac empiricalType.probabilityDensity := by
  unfold finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
  rw [
    map_initialDensity_finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_eq_dirac]
  congr 1
  rw [← finiteIIDPositiveSampleEmpiricalType_probabilityDensity,
    finiteIIDPositiveSampleEmpiricalType_representative]

end

end FiniteMarkovProcesses.Probability
