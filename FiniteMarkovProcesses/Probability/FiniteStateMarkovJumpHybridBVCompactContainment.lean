/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVEnvelopeCompactness
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryHybridBVObservationVariation
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialCountMoment
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation

/-!
# Compact containment for empirical Markov-jump hybrid-BV observations

This module transports the configuration-uniform microscopic jump-count tail into one compact
set in the total hybrid-BV observation carrier.  On the almost-sure ordered physical slice, a
particle-scaled count cutoff places the explicit observation in a uniform quantitative envelope;
the generic unique-lift theorem places that envelope in a compact hybrid container.  The
unordered fallback branch remains source-null.

The resulting estimate is uniform in the deterministic initial configuration and has exact
particle-number speed.  It is compact containment only, not a conditional closed-set upper bound
or a path large-deviation principle.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open PositiveFiniteJumpHistoryReplicas
open FiniteMarkovProcesses
open scoped ENNReal NNReal Topology

noncomputable section

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- The replica-count-independent compact hybrid container induced by a normalized microscopic
jump-count cutoff. -/
noncomputable def finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
    (duration countCutoff : ℝ) :
    Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  finiteIntervalHybridBVUniformL1VariationCompactContainer
    (empiricalDensityDirectionalFlowL1Bound duration countCutoff)
    (empiricalDensityDirectionalFlowVariationBound countCutoff)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The empirical hybrid container is compact for every positive physical duration. -/
theorem isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
    (duration countCutoff : ℝ) (hDuration : 0 < duration) :
    IsCompact
      (finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
        (State := State) duration countCutoff) := by
  exact isCompact_finiteIntervalHybridBVUniformL1VariationCompactContainer
    hDuration
      (empiricalDensityDirectionalFlowL1Bound_lt_top duration countCutoff)
      (empiricalDensityDirectionalFlowVariationBound_lt_top countCutoff)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On the ordered physical slice, a particle-scaled total-count cutoff places the totalized
observation in the common compact hybrid container. -/
theorem empiricalDensityDirectionalFlowTotalHybridBVObservation_mem_compactContainer
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration countCutoff : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (hCount : (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) ≤
      (successorIndex + 1 : ℝ) * countCutoff) :
    empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories ∈
      finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
        duration countCutoff := by
  apply finiteIntervalHybridBVUniformL1VariationEnvelope_subset_compactContainer
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  simpa only [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation,
    orderedReplicaHistories] using!
      empiricalDensityDirectionalFlowExplicitHybridBVPath_mem_uniformL1VariationEnvelope
        successorIndex histories duration countCutoff hDuration hOrdered hCount

/-- Uniform particle-speed compact containment for every deterministic initial configuration.
The right side is the exact heterogeneous-product Chernoff bound. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_compl_compactContainer_le
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ≥0)
    (hDuration : 0 < duration) {exponent : ℝ} (hExponent : 0 < exponent)
    (countCutoff : ℝ) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration.le
        (finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
          (State := State) duration countCutoff)ᶜ ≤
      ENNReal.ofReal
        (Real.exp
          (((successorIndex + 1 : ℕ) : ℝ) *
              (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
                (Real.exp exponent - 1)) -
            (((successorIndex + 1 : ℕ) : ℝ) * countCutoff) * exponent)) := by
  have hDurationReal : 0 < (duration : ℝ) := by exact_mod_cast hDuration
  have hCompact :=
    isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff hDurationReal
  rw (transparency := .default)
    [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw,
      Measure.map_apply
        (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration)
        hCompact.isClosed.measurableSet.compl]
  calc
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration.le).toMeasure
        (empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration ⁻¹'
          (finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
            (State := State) duration countCutoff)ᶜ) ≤
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration.le).toMeasure
        {histories |
          ((successorIndex + 1 : ℕ) : ℝ) * countCutoff <
            finiteJumpHistoryReplicaTotalJumpCount histories} := by
      apply measure_mono_ae
      filter_upwards [
        ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration.le] with histories hOrdered
      intro hOutside
      have hObservationOutside :
          empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories ∉
            finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
              duration countCutoff := by
        simpa only [Set.mem_preimage, Set.mem_compl_iff] using hOutside
      by_contra hCount
      apply hObservationOutside
      apply empiricalDensityDirectionalFlowTotalHybridBVObservation_mem_compactContainer
        successorIndex histories duration countCutoff hDurationReal hOrdered
      simpa only [Nat.cast_add, Nat.cast_one] using le_of_not_gt hCount
    _ ≤ ENNReal.ofReal
        (Real.exp
          (((successorIndex + 1 : ℕ) : ℝ) *
              (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
                (Real.exp exponent - 1)) -
            (((successorIndex + 1 : ℕ) : ℝ) * countCutoff) * exponent)) :=
      finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_gt_le_exponential
        initialConfiguration generator duration hExponent
          (((successorIndex + 1 : ℕ) : ℝ) * countCutoff)

end

end FiniteMarkovProcesses.Probability
