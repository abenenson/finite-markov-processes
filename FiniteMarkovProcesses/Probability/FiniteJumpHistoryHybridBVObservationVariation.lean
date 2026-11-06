/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservation
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryReplicaJumpCount

/-!
# Derivative variation of empirical finite-jump observations

This module bounds the complete coordinatewise derivative variation of the explicit empirical
density--directional-flow hybrid path by the normalized total number of microscopic events.  The
bound applies on the total ordered carrier: self-events contribute zero, and reduced physical
support is not imported into the admissibility-free estimate.

## Main declarations

- `PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowDerivativeTotalVariation_le`:
  complete derivative variation is at most `3` times normalized total jump count.
- `PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1Enorm_le`: the strong-`L1`
  norm is bounded by duration times one plus that normalized event budget.
- `PositiveFiniteJumpHistoryReplicas.
    empiricalDensityDirectionalFlowExplicitHybridBVPath_mem_uniformL1VariationEnvelope`:
  a particle-number-scaled total-count cutoff places the explicit observation in one replica-count-
  independent `L1`--variation envelope.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open FiniteMarkovProcesses FiniteMarkovProcesses.FiniteIntervalBVAlgebra
open scoped BigOperators ENNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

namespace PositiveFiniteJumpHistoryReplicas

/-- Replica-count-independent derivative-variation budget induced by a normalized microscopic
jump-count cutoff. -/
noncomputable def empiricalDensityDirectionalFlowVariationBound
    (countCutoff : ℝ) : ENNReal :=
  ENNReal.ofReal (3 * countCutoff)

/-- Replica-count-independent strong-`L1` budget induced by a normalized microscopic jump-count
cutoff. -/
noncomputable def empiricalDensityDirectionalFlowL1Bound
    (duration countCutoff : ℝ) : ENNReal :=
  ENNReal.ofReal duration *
    (1 + empiricalDensityDirectionalFlowVariationBound countCutoff)

/-- The normalized-count derivative-variation budget is always finite. -/
theorem empiricalDensityDirectionalFlowVariationBound_lt_top
    (countCutoff : ℝ) :
    empiricalDensityDirectionalFlowVariationBound countCutoff < ∞ := by
  exact ENNReal.ofReal_lt_top

/-- The normalized-count strong-`L1` budget is always finite. -/
theorem empiricalDensityDirectionalFlowL1Bound_lt_top
    (duration countCutoff : ℝ) :
    empiricalDensityDirectionalFlowL1Bound duration countCutoff < ∞ := by
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  rw [ENNReal.add_lt_top]
  exact ⟨by simp, empiricalDensityDirectionalFlowVariationBound_lt_top countCutoff⟩

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete derivative variation of the explicit empirical density--directional-flow path is
bounded by `3` times the total microscopic jump count divided by the replica number. -/
theorem empiricalDensityDirectionalFlowDerivativeTotalVariation_le
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    finiteIntervalHybridBVDerivativeTotalVariation
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered) ≤
      (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
        ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) := by
  classical
  rw [finiteIntervalHybridBVDerivativeTotalVariation]
  calc
    (∑ coordinate,
      ((empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered).toDerivativePath.derivative
          coordinate).toSignedMeasure.totalVariation Set.univ) ≤
        ∑ coordinate,
          ∑ event : EmpiricalDensityDirectionalFlowEventIndex
              successorIndex histories,
            ENNReal.ofReal
              |empiricalDensityDirectionalFlowEventIncrement
                successorIndex (histories event.1) event.2 coordinate| := by
      apply Finset.sum_le_sum
      intro coordinate _hCoordinate
      rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative_eq_finiteRestricted]
      exact
        finiteRestrictedWeightedDiracVagueSignedMeasure_totalVariation_apply_univ_le
          duration _ _
    _ = ∑ event : EmpiricalDensityDirectionalFlowEventIndex
            successorIndex histories,
          ∑ coordinate,
            ENNReal.ofReal
              |empiricalDensityDirectionalFlowEventIncrement
                successorIndex (histories event.1) event.2 coordinate| := by
      exact Finset.sum_comm
    _ ≤ ∑ event : EmpiricalDensityDirectionalFlowEventIndex
            successorIndex histories,
          ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro event _hEvent
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal
          (sum_abs_empiricalDensityDirectionalFlowEventIncrement_le_three_div
            successorIndex (histories event.1) event.2)
      · intro coordinate _hCoordinate
        exact abs_nonneg _
    _ = (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
          ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) := by
      rw [Fintype.sum_sigma]
      simp [finiteJumpHistoryReplicaTotalJumpCount, nsmul_eq_mul,
        Nat.cast_sum]
      rw [Finset.sum_mul]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit empirical observation's strong-`L1` norm is controlled by duration times its unit
initial density plus the normalized total-event variation budget. -/
theorem empiricalDensityDirectionalFlowL1Enorm_le
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    ‖(empiricalDensityDirectionalFlowExplicitHybridBVPath
      successorIndex histories duration hOrdered).toDerivativePath.toL1Path‖ₑ ≤
      ENNReal.ofReal duration *
        (1 + (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
          ENNReal.ofReal (3 / (successorIndex + 1 : ℝ))) := by
  let path := empiricalDensityDirectionalFlowExplicitHybridBVPath
    successorIndex histories duration hOrdered
  calc
    ‖path.toDerivativePath.toL1Path‖ₑ ≤
        ENNReal.ofReal duration *
          (‖path.initialTrace‖ₑ +
            finiteIntervalHybridBVDerivativeTotalVariation path) :=
      enorm_toL1Path_le_duration_mul_initialTrace_add_derivativeTotalVariation path
    _ ≤ ENNReal.ofReal duration *
        (1 + (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
          ENNReal.ofReal (3 / (successorIndex + 1 : ℝ))) := by
      apply mul_le_mul_right
      apply add_le_add
      · change ‖(empiricalDensityDirectionalFlowExplicitHybridBVPath
          successorIndex histories duration hOrdered).initialTrace‖ₑ ≤ 1
        rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_initialTrace
          successorIndex histories duration hDuration hOrdered,
          enorm_empiricalDensityDirectionalFlowInitialL1Value]
      · exact empiricalDensityDirectionalFlowDerivativeTotalVariation_le
          successorIndex histories duration hOrdered

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] in
/-- A total-count bound at particle-number scale controls the normalized empirical derivative
variation by a cutoff independent of the number of replicas. -/
theorem empiricalDensityDirectionalFlowNormalizedTotalJumpCount_le_variationBound
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (countCutoff : ℝ)
    (hCount : (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) ≤
      (successorIndex + 1 : ℝ) * countCutoff) :
    (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
        ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) ≤
      empiricalDensityDirectionalFlowVariationBound countCutoff := by
  have hReplicaCount : 0 < (successorIndex + 1 : ℝ) := by positivity
  have hThreeCount :
      3 * (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) ≤
        3 * ((successorIndex + 1 : ℝ) * countCutoff) :=
    mul_le_mul_of_nonneg_left hCount (by norm_num)
  have hNormalized :
      (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) *
          (3 / (successorIndex + 1 : ℝ)) ≤
        3 * countCutoff := by
    calc
      (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) *
          (3 / (successorIndex + 1 : ℝ)) =
          (3 * (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ)) /
            (successorIndex + 1 : ℝ) := by ring
      _ ≤ (3 * ((successorIndex + 1 : ℝ) * countCutoff)) /
          (successorIndex + 1 : ℝ) :=
        div_le_div_of_nonneg_right hThreeCount hReplicaCount.le
      _ = 3 * countCutoff := by field_simp
  calc
    (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
        ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) =
        ENNReal.ofReal
          ((finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) *
            (3 / (successorIndex + 1 : ℝ))) := by
      rw [← ENNReal.ofReal_natCast (finiteJumpHistoryReplicaTotalJumpCount histories),
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (3 * countCutoff) :=
      ENNReal.ofReal_le_ofReal hNormalized
    _ = empiricalDensityDirectionalFlowVariationBound countCutoff := rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Under a particle-number-scaled total-count cutoff, the explicit empirical observation belongs
to one broad, admissibility-free hybrid-`BV` envelope whose budgets do not depend on the number of
replicas. -/
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_mem_uniformL1VariationEnvelope
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration countCutoff : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (hCount : (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) ≤
      (successorIndex + 1 : ℝ) * countCutoff) :
    empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered ∈
      finiteIntervalHybridBVUniformL1VariationEnvelope
        (empiricalDensityDirectionalFlowL1Bound duration countCutoff)
        (empiricalDensityDirectionalFlowVariationBound countCutoff) := by
  rw [mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff]
  have hNormalized :=
    empiricalDensityDirectionalFlowNormalizedTotalJumpCount_le_variationBound
      successorIndex histories countCutoff hCount
  constructor
  · apply (empiricalDensityDirectionalFlowL1Enorm_le
      successorIndex histories duration hDuration hOrdered).trans
    have hAdd :
        1 + (finiteJumpHistoryReplicaTotalJumpCount histories : ENNReal) *
            ENNReal.ofReal (3 / (successorIndex + 1 : ℝ)) ≤
          1 + empiricalDensityDirectionalFlowVariationBound countCutoff :=
      add_le_add (le_refl 1) hNormalized
    simpa only [empiricalDensityDirectionalFlowL1Bound] using
      mul_le_mul_right hAdd (ENNReal.ofReal duration)
  · exact (empiricalDensityDirectionalFlowDerivativeTotalVariation_le
      successorIndex histories duration hOrdered).trans hNormalized

end PositiveFiniteJumpHistoryReplicas

end

end FiniteMarkovProcesses.Probability
