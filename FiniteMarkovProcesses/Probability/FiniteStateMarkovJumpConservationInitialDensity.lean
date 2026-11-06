/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVConservationInitialDensity
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpRandomEmpiricalTypeHybridBVObservation

/-!
# Conservation recovery under finite-state Markov-jump source laws

This module connects the continuous hybrid-path conservation observable to the microscopic
initial configuration.  For every deterministic initial configuration, its observed law pushes
the conservation-recovered coordinate family to the Dirac mass at the exact empirical initial
density.  The result is source-law ownership, not an endpoint-continuity assertion.

## Main declarations

* `ae_finiteStateMarkovJumpDeterministicInitialHybridBVConservationInitialDensity_eq` proves the
  almost-sure microscopic coupling.
* `map_conservationInitialDensity_finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw`
  identifies the exact pushforward law.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory

open FiniteMarkovProcesses
open FiniteMarkovProcesses.InformationTheory
open PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The whole-carrier conservation-recovered initial coordinate family is Borel measurable. -/
theorem measurable_rengerDirectionalFlowHybridBVConservationInitialDensity
    {duration : ℝ} (hDuration : 0 < duration) :
    Measurable fun path : RengerDirectionalFlowHybridBVPath State duration =>
      rengerDirectionalFlowHybridBVConservationInitialDensity hDuration path :=
  (continuous_rengerDirectionalFlowHybridBVConservationInitialDensity hDuration).measurable

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Under one deterministic-initial replica source, conservation recovery of the total hybrid
observation is almost surely the real coordinate family of that configuration's empirical
initial density. -/
theorem ae_finiteStateMarkovJumpDeterministicInitialHybridBVConservationInitialDensity_eq
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    ∀ᵐ histories ∂
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration.le).toMeasure,
      rengerDirectionalFlowHybridBVConservationInitialDensity hDuration
          (empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories) =
        (finiteIIDEmpiricalProbabilityDensity
          successorIndex initialConfiguration).realWeight := by
  filter_upwards [
    ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration.le,
    ae_initialDensity_eq_deterministicConfigurationEmpiricalDensity
      successorIndex initialConfiguration generator duration hDuration.le
  ] with histories hOrdered hInitialDensity
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  unfold orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    orderedReplicaHistories
  rw [rengerDirectionalFlowHybridBVConservationInitialDensity_explicitObservation_eq
    successorIndex histories duration hDuration hOrdered]
  rw [hInitialDensity]

/-- The deterministic-initial hybrid observation law has exactly the Dirac conservation-initial
pushforward at its empirical initial density. -/
theorem
    map_conservationInitialDensity_finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    Measure.map
        (rengerDirectionalFlowHybridBVConservationInitialDensity hDuration)
        (finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration.le) =
      Measure.dirac
        (finiteIIDEmpiricalProbabilityDensity
          successorIndex initialConfiguration).realWeight := by
  let sourceMeasure :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration.le).toMeasure
  let recoveredInitialDensity :=
    (finiteIIDEmpiricalProbabilityDensity successorIndex initialConfiguration).realWeight
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw]
  rw [Measure.map_map
    (measurable_rengerDirectionalFlowHybridBVConservationInitialDensity hDuration)
    (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
      successorIndex duration)]
  calc
    Measure.map
        (rengerDirectionalFlowHybridBVConservationInitialDensity hDuration ∘
          empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration)
        sourceMeasure =
      Measure.map (fun _ => recoveredInitialDensity) sourceMeasure := by
        apply Measure.map_congr
        exact
          ae_finiteStateMarkovJumpDeterministicInitialHybridBVConservationInitialDensity_eq
            successorIndex initialConfiguration generator duration hDuration
    _ = Measure.dirac recoveredInitialDensity := by
      rw [Measure.map_const, measure_univ, one_smul]

/-- The canonical empirical-type conditional law recovers exactly that count type's simplex
coordinate family. -/
theorem map_conservationInitialDensity_finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    Measure.map
        (rengerDirectionalFlowHybridBVConservationInitialDensity hDuration)
        (finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
          empiricalType generator duration hDuration.le) =
      Measure.dirac empiricalType.probabilityDensity.realWeight := by
  unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
  rw [
    map_conservationInitialDensity_finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw]
  congr 1
  rw [← finiteIIDPositiveSampleEmpiricalType_probabilityDensity,
    finiteIIDPositiveSampleEmpiricalType_representative]

/-- Every empirical-type conditional hybrid law is concentrated on the closed conservation graph
over that type's exact simplex point. -/
theorem finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw_conservationGraph_eq_one
    {successorIndex : ℕ}
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
        empiricalType generator duration hDuration.le
        {path |
          (empiricalType.probabilityDensity, path) ∈
            RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration} = 1 := by
  classical
  let recoveredInitialDensity := empiricalType.probabilityDensity.realWeight
  have hPreimage :
      rengerDirectionalFlowHybridBVConservationInitialDensity hDuration ⁻¹'
          {recoveredInitialDensity} =
        {path |
          (empiricalType.probabilityDensity, path) ∈
            RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration} := by
    ext path
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    unfold RengerDirectionalFlowHybridBVConservationInitialDensityGraph
    exact eq_comm
  rw [← hPreimage]
  rw [← Measure.map_apply
    (measurable_rengerDirectionalFlowHybridBVConservationInitialDensity hDuration)
    (MeasurableSet.singleton recoveredInitialDensity)]
  rw [map_conservationInitialDensity_finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw]
  simp [recoveredInitialDensity]

/-- The mixed probability-density/hybrid-path joint law is concentrated on the single closed
conservation graph, even though its initial density is random. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_conservationGraph_eq_one
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration.le
        (RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration) = 1 := by
  let typePathMap := fun source :
      FiniteIIDPositiveEmpiricalType State successorIndex ×
        RengerDirectionalFlowHybridBVPath State duration =>
    (source.1.probabilityDensity, source.2)
  have hTypePathMap : Measurable typePathMap :=
    measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
      successorIndex duration
  have hGraphMeasurable :
      MeasurableSet
        (RengerDirectionalFlowHybridBVConservationInitialDensityGraph
          (State := State) hDuration) :=
    measurableSet_rengerDirectionalFlowHybridBVConservationInitialDensityGraph
      (State := State) hDuration
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
  rw [Measure.map_apply hTypePathMap hGraphMeasurable]
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
  rw [Measure.compProd_apply (hGraphMeasurable.preimage hTypePathMap)]
  simp only [finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel_apply]
  have hSection (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
      Prod.mk empiricalType ⁻¹'
          (typePathMap ⁻¹'
            RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration) =
        {path |
          (empiricalType.probabilityDensity, path) ∈
            RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration} := by
    rfl
  simp_rw [hSection,
    finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw_conservationGraph_eq_one]
  simp

end

end FiniteMarkovProcesses.Probability
