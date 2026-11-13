/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservationMeasurability
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpEmpiricalInitialDensity
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpPositiveReplicaFamily

/-!
# Full-carrier hybrid-BV observation of positive Markov-jump replicas

This module joins the normalized successor-indexed independent-particle source to the exact
hybrid bounded-variation carrier.  The observation is total on the common sigma carrier, Borel
measurable, and equal to the ordered physical construction almost surely.  Off the ordered null
set it uses the fixed no-jump fallback; that totalization is a measurable-interface device, not a
new source path or a modification of the physical law.

## Main declarations

- `finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation`: total common-carrier map.
- `finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw`: exact pushed-forward law.
- `ae_orderedBefore_finiteStateMarkovJumpReplicaProbabilityMeasure`: the fallback is absent almost
  surely under every normalized finite-replica source.
- `finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_map_replicaLaw`: the common
  sigma-carrier law reduces exactly to the fixed particle-count product law.
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

/-- Total hybrid-BV observation on the common positive-replica sigma carrier. -/
noncomputable def finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
    (duration : ℝ) (family : FiniteStateMarkovJumpPositiveReplicaFamily State) :
    FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
    family.1 duration family.2

/-- The total common-carrier hybrid-BV observation is Borel measurable. -/
theorem measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
    (duration : ℝ) :
    Measurable (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
      (State := State) duration) := by
  rw [measurable_sigma_iff]
  intro successorIndex
  exact
    measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration

omit [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] [Nonempty State] in
/-- Every normalized fixed-count Markov-jump replica law is concentrated on histories whose jump
times are strictly ordered inside the physical interval. -/
theorem ae_orderedBefore_finiteStateMarkovJumpReplicaProbabilityMeasure
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    ∀ᵐ histories ∂(finiteStateMarkovJumpReplicaProbabilityMeasure
        replicaCount initial generator duration hNormalized).toMeasure,
      ∀ replica, (histories replica).OrderedBefore duration := by
  rw [ae_all_iff]
  intro replica
  have hCoordinate :
      ∀ᵐ history ∂finiteStateMarkovJumpDensityMeasure initial generator duration,
        history.OrderedBefore duration :=
    (ae_physicalAt_finiteStateMarkovJumpDensityMeasure
      initial generator duration).mono fun _history hPhysical => hPhysical.1
  rw [← finiteStateMarkovJumpReplicaProbabilityMeasure_coordinate_map
    replicaCount initial generator duration hNormalized replica] at hCoordinate
  exact ae_of_ae_map (measurable_pi_apply replica).aemeasurable hCoordinate

omit [DecidableEq State] [TopologicalSpace State] [DiscreteTopology State]
  [BorelSpace State] in
/-- Almost surely, the ordered-or-fallback totalization retains every original replica history;
the fallback branch has zero source probability. -/
theorem ae_orderedPositiveFiniteJumpHistoryReplicasOrFallback_val_eq
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    ∀ᵐ histories ∂(finiteStateMarkovJumpReplicaProbabilityMeasure
        (successorIndex + 1) initial generator duration hNormalized).toMeasure,
      ∀ replica,
        (PositiveFiniteJumpHistoryReplicas.orderedPositiveFiniteJumpHistoryReplicasOrFallback
          successorIndex duration histories replica).val = histories replica := by
  filter_upwards [ae_orderedBefore_finiteStateMarkovJumpReplicaProbabilityMeasure
    (successorIndex + 1) initial generator duration hNormalized] with histories hOrdered
  intro replica
  simp [PositiveFiniteJumpHistoryReplicas.orderedPositiveFiniteJumpHistoryReplicasOrFallback,
    PositiveFiniteJumpHistoryReplicas.orderedFiniteJumpHistoryOrFallback,
    hOrdered replica]

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On the ordered physical slice, the total hybrid-BV observation's canonical initial trace is
the literal empirical initial density together with zero cumulative directional flow. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_of_ordered
    (successorIndex : ℕ) (duration : ℝ) (hDuration : 0 < duration)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
      ⟨successorIndex, histories⟩).initialTrace =
        empiricalDensityDirectionalFlowInitialL1Value successorIndex histories := by
  unfold finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  unfold orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    orderedReplicaHistories
  simpa using empiricalDensityDirectionalFlowExplicitHybridBVPath_initialTrace
    successorIndex histories duration hDuration hOrdered

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On the ordered physical slice, every density coordinate of the hybrid initial trace equals
the corresponding coordinate of the common-carrier empirical initial-density observation. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_density
    (successorIndex : ℕ) (duration : ℝ) (hDuration : 0 < duration)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (state : State) :
    (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
      ⟨successorIndex, histories⟩).initialTrace (Sum.inl state) =
        ((finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
          ⟨successorIndex, histories⟩).weight state : ℝ) := by
  rw [finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_of_ordered
    successorIndex duration hDuration histories hOrdered]
  rw [empiricalDensityDirectionalFlowInitialL1Value_density]
  unfold empiricalInitialDensity
    finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
    finiteIIDEmpiricalProbabilityDensity
    positiveFiniteJumpHistoryReplicaInitialStates
  simp only [NNReal.coe_div,
    FiniteJumpHistory.stateMembershipIndicator]
  congr 1
  have hCount :
      (∑ replica, if (histories replica).initialState = state then 1 else 0 : ℕ) =
        finiteIIDPositiveSampleStateCount successorIndex
          (fun replica => (histories replica).initialState) state := by
    unfold finiteIIDPositiveSampleStateCount
    exact Finset.sum_boole (R := ℕ)
      (fun replica => (histories replica).initialState = state) Finset.univ
  have hCountReal := congrArg (fun count : ℕ => (count : ℝ)) hCount
  calc
    (∑ replica, if (histories replica).initialState = state then (1 : ℝ) else 0) =
        ((∑ replica,
          if (histories replica).initialState = state then 1 else 0 : ℕ) : ℝ) := by
      norm_cast
    _ = _ := hCountReal

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Under the normalized fixed-count Markov-jump source, every density coordinate of the total
hybrid observation's initial trace agrees almost surely with the common-carrier empirical initial
density.  The only excluded inputs are the already-proved null set of unordered histories. -/
theorem ae_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_density
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    ∀ᵐ histories ∂(finiteStateMarkovJumpReplicaProbabilityMeasure
        (successorIndex + 1) initial generator duration hNormalized).toMeasure,
      ∀ state,
        (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
          ⟨successorIndex, histories⟩).initialTrace (Sum.inl state) =
          ((finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
            ⟨successorIndex, histories⟩).weight state : ℝ) := by
  filter_upwards [ae_orderedBefore_finiteStateMarkovJumpReplicaProbabilityMeasure
    (successorIndex + 1) initial generator duration hNormalized] with histories hOrdered
  intro state
  exact
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation_initialTrace_density
      successorIndex duration hDuration histories hOrdered state

/-- Exact hybrid-BV observation law at one positive particle count, formed on the common sigma
carrier used by every successor index. -/
noncomputable def finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  Measure.map
    (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
    (finiteStateMarkovJumpPositiveReplicaFamilyLaw
      successorIndex initial generator duration hNormalized)

/-- The common-carrier hybrid-BV observation law is exactly the fixed-count product-law
pushforward by the total slice observation. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_map_replicaLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
        successorIndex initial generator duration hNormalized =
      Measure.map
        (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration)
        (finiteStateMarkovJumpReplicaProbabilityMeasure
          (successorIndex + 1) initial generator duration hNormalized).toMeasure := by
  unfold finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
    finiteStateMarkovJumpPositiveReplicaFamilyLaw
  rw [Measure.map_map
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection successorIndex)]
  rfl

/-- Every exact hybrid-BV observation law is normalized. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_isProbabilityMeasure
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
        successorIndex initial generator duration hNormalized) := by
  unfold finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
  let : IsProbabilityMeasure
      (finiteStateMarkovJumpPositiveReplicaFamilyLaw
        successorIndex initial generator duration hNormalized) :=
    finiteStateMarkovJumpPositiveReplicaFamilyLaw_isProbabilityMeasure
      successorIndex initial generator duration hNormalized
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation
      duration).aemeasurable).2
    inferInstance

end

end FiniteMarkovProcesses.Probability
