/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovExponentialTimeTiltHistoryDensity
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialReplication
import Mathlib.Probability.Independence.Integration

/-!
# Heterogeneous deterministic-initial exponential tilts

This module tensors the source-neutral one-history exponential time-tilt estimate through a
finite heterogeneous product of deterministic-initial Markov jump histories.  The transition
exponent is arbitrary subject to the existing continuous bounded-rate contract.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The product of all time-dependent exponential-tilt weights has expectation at most one under
every heterogeneous deterministic-initial replica law. -/
theorem lintegral_prod_finiteStateMarkovExponentialTimeTiltHistoryExponential_le_one
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    ∫⁻ histories,
      ∏ replica : Fin replicaCount,
        finiteStateMarkovExponentialTimeTiltHistoryExponential
          generator tilt duration (histories replica)
      ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure ≤ 1 := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
  let exponentialWeight : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ≥0∞ :=
    fun replica histories =>
      finiteStateMarkovExponentialTimeTiltHistoryExponential
        generator tilt duration (histories replica)
  have hWeightMeasurable : ∀ replica, Measurable (exponentialWeight replica) := by
    intro replica
    exact
      (measurable_finiteStateMarkovExponentialTimeTiltHistoryExponential
        generator tilt duration).comp (measurable_pi_apply replica)
  have hIndependent : iIndepFun exponentialWeight law := by
    have hHistoryIndependent :=
      finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun
        initialConfiguration generator duration hDuration
    exact iIndepFun.comp
      (β := fun _ : Fin replicaCount => FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount => ℝ≥0∞) hHistoryIndependent
      (fun _ history =>
        finiteStateMarkovExponentialTimeTiltHistoryExponential
          generator tilt duration history)
      (fun _ =>
        measurable_finiteStateMarkovExponentialTimeTiltHistoryExponential
          generator tilt duration)
  have hCoordinateMoment (replica : Fin replicaCount) :
      ∫⁻ histories, exponentialWeight replica histories ∂law ≤ 1 := by
    calc
      _ = ∫⁻ history,
          finiteStateMarkovExponentialTimeTiltHistoryExponential
            generator tilt duration history
          ∂Measure.map (Function.eval replica) law := by
        rw [lintegral_map
          (measurable_finiteStateMarkovExponentialTimeTiltHistoryExponential
            generator tilt duration)
          (measurable_pi_apply replica)]
      _ = ∫⁻ history,
          finiteStateMarkovExponentialTimeTiltHistoryExponential
            generator tilt duration history
          ∂finiteStateMarkovJumpDensityMeasure
            (PMF.pure (initialConfiguration replica)) generator duration := by
        rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
          initialConfiguration generator duration hDuration replica]
      _ ≤ 1 :=
        lintegral_finiteStateMarkovExponentialTimeTiltHistoryExponential_le_one
          (PMF.pure (initialConfiguration replica)) generator tilt
            hDuration
  change (∫⁻ histories, ∏ replica : Fin replicaCount,
      exponentialWeight replica histories ∂law) ≤ 1
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun
    Finset.univ exponentialWeight hIndependent hWeightMeasurable]
  calc
    (∏ replica : Fin replicaCount,
        ∫⁻ histories, exponentialWeight replica histories ∂law) ≤
      ∏ _replica : Fin replicaCount, (1 : ℝ≥0∞) := by
        apply Finset.prod_le_prod₀
        · intro replica _hReplica
          exact bot_le
        · intro replica _hReplica
          exact hCoordinateMoment replica
    _ = 1 := by simp

/-- Equivalently, the exponential of the sum of heterogeneous microscopic tilt scores has
expectation at most one. -/
theorem lintegral_exp_sum_finiteStateMarkovExponentialTimeTiltHistoryScore_le_one
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    ∫⁻ histories,
      ENNReal.ofReal (Real.exp
        (∑ replica : Fin replicaCount,
          finiteStateMarkovExponentialTimeTiltHistoryScore
            generator tilt duration (histories replica)))
      ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure ≤ 1 := by
  calc
    _ = ∫⁻ histories,
        ∏ replica : Fin replicaCount,
          finiteStateMarkovExponentialTimeTiltHistoryExponential
            generator tilt duration (histories replica)
        ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
      apply lintegral_congr
      intro histories
      unfold finiteStateMarkovExponentialTimeTiltHistoryExponential
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
      intro replica _hReplica
      exact (Real.exp_pos _).le
    _ ≤ 1 :=
      lintegral_prod_finiteStateMarkovExponentialTimeTiltHistoryExponential_le_one
        initialConfiguration generator tilt duration hDuration

end

end FiniteMarkovProcesses.Probability
