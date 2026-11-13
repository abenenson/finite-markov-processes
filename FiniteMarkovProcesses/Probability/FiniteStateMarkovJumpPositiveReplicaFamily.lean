/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryEmpiricalDirectionalFlow

/-!
# Positive independent-particle Markov jump family

This module places every positive finite product of one normalized finite-state Markov jump law on
one measurable sigma carrier.  The law at successor index `n` is supported on the slice containing
exactly `n + 1` independent histories.  Its observation is the exact empirical density and
cumulative ordered one-way-flow path, and its speed is particle number.

The construction supplies all finite source data needed by a dynamic large-deviation statement.
It does not assert a topology, rate function, or asymptotic upper or lower bound.

## Main results

- `finiteStateMarkovJumpPositiveReplicaFamilyLaw`: one normalized law family on a fixed carrier.
- `finiteStateMarkovJumpPositiveReplicaFamilyObservation`: exact published finite observation.
- `finiteStateMarkovJumpPositiveReplicaFamilyObservationLaw`: exact pushed-forward observation law.
- `finiteStateMarkovJumpParticleSpeed_tendsto_atTop`: particle number is the diverging speed.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

/-- One fixed measurable carrier for every positive finite family of jump histories.  The sigma
index `successorIndex` records a literal particle count of `successorIndex + 1`. -/
abbrev FiniteStateMarkovJumpPositiveReplicaFamily (State : Type u) :=
  Σ successorIndex : ℕ, PositiveFiniteJumpHistoryReplicas State successorIndex

omit [Fintype State] [MeasurableSingletonClass State] [DecidableEq State] in
/-- The canonical injection of one positive-particle slice into the common sigma carrier is
measurable. -/
theorem measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection
    (successorIndex : ℕ) :
    Measurable
      (@Sigma.mk ℕ
        (fun index => PositiveFiniteJumpHistoryReplicas State index)
        successorIndex) := by
  apply Measurable.of_comap_le
  exact (MeasurableSpace.comap_mono (iInf_le _ successorIndex)).trans
    MeasurableSpace.comap_map_le

/-- The normalized positive-replica law at one successor index, embedded into the fixed sigma
carrier.  Duration and every generator rate are unchanged as particle number varies. -/
noncomputable def finiteStateMarkovJumpPositiveReplicaFamilyLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  Measure.map
    (@Sigma.mk ℕ
      (fun index => PositiveFiniteJumpHistoryReplicas State index)
      successorIndex)
    (finiteStateMarkovJumpReplicaProbabilityMeasure
      (successorIndex + 1) initial generator duration hNormalized).toMeasure

omit [MeasurableSingletonClass State] [DecidableEq State] in
/-- Every law in the positive-replica family is an exact probability measure. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyLaw_isProbabilityMeasure
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpPositiveReplicaFamilyLaw
        successorIndex initial generator duration hNormalized) := by
  unfold finiteStateMarkovJumpPositiveReplicaFamilyLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection
      successorIndex).aemeasurable).2
    inferInstance

/-- Exact empirical density and cumulative ordered one-way-flow observation on the common positive
replica carrier. -/
noncomputable def finiteStateMarkovJumpPositiveReplicaFamilyObservation
    (family : FiniteStateMarkovJumpPositiveReplicaFamily State) :
    EmpiricalDensityDirectionalFlowPath State :=
  PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowPath
    family.1 family.2

/-- The exact positive-replica observation is measurable on the common sigma carrier. -/
theorem measurable_finiteStateMarkovJumpPositiveReplicaFamilyObservation :
    Measurable
      (finiteStateMarkovJumpPositiveReplicaFamilyObservation
        (State := State)) := by
  rw [measurable_sigma_iff]
  intro successorIndex
  exact PositiveFiniteJumpHistoryReplicas.measurable_empiricalDensityDirectionalFlowPath
    successorIndex

/-- The observed law at one particle count is the exact pushforward of the common-carrier law. -/
noncomputable def finiteStateMarkovJumpPositiveReplicaFamilyObservationLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    Measure (EmpiricalDensityDirectionalFlowPath State) :=
  Measure.map
    finiteStateMarkovJumpPositiveReplicaFamilyObservation
    (finiteStateMarkovJumpPositiveReplicaFamilyLaw
      successorIndex initial generator duration hNormalized)

/-- The common-carrier observation law is literally the empirical observation pushed forward from
the corresponding normalized independent-replica product. -/
theorem finiteStateMarkovJumpPositiveReplicaFamilyObservationLaw_eq_map_replicaLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    finiteStateMarkovJumpPositiveReplicaFamilyObservationLaw
        successorIndex initial generator duration hNormalized =
      Measure.map
        (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowPath successorIndex)
        (finiteStateMarkovJumpReplicaProbabilityMeasure
          (successorIndex + 1) initial generator duration hNormalized).toMeasure := by
  unfold finiteStateMarkovJumpPositiveReplicaFamilyObservationLaw
    finiteStateMarkovJumpPositiveReplicaFamilyLaw
  rw [Measure.map_map
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyObservation
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyInjection
      successorIndex)]
  rfl

/-- The macroscopic speed is literal particle number, not duration or a clock multiplier. -/
def finiteStateMarkovJumpParticleSpeed (successorIndex : ℕ) : ℝ :=
  ((successorIndex + 1 : ℕ) : ℝ)

/-- Every successor-indexed particle speed is strictly positive. -/
theorem finiteStateMarkovJumpParticleSpeed_pos (successorIndex : ℕ) :
    0 < finiteStateMarkovJumpParticleSpeed successorIndex := by
  unfold finiteStateMarkovJumpParticleSpeed
  positivity

/-- Particle number tends to infinity along the successor-indexed source family. -/
theorem finiteStateMarkovJumpParticleSpeed_tendsto_atTop :
    Filter.Tendsto finiteStateMarkovJumpParticleSpeed Filter.atTop Filter.atTop := by
  unfold finiteStateMarkovJumpParticleSpeed
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp
    (Filter.tendsto_add_atTop_nat 1)

end FiniteMarkovProcesses.Probability
