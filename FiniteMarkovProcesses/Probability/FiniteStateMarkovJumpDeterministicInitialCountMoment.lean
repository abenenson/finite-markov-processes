/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryReplicaJumpCount
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpCountExponentialTail
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialReplication

/-!
# Count moments for deterministic-initial Markov-jump replicas

Coordinate histories in the deterministic-initial replica source are independent but generally
not identically distributed because their initial states may differ.  Their physical jump-count
moments nevertheless share the same initial-law-uniform Poisson bound.  This module tensors that
bound through the exact heterogeneous product law.

## Main declarations

- `integrable_exp_mul_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount`:
  integrability of the total-count exponential.
- `mgf_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_le`:
  the particle-extensive moment bound, uniform in the initial configuration.
- `finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_gt_le_exponential`:
  the corresponding particle-speed Chernoff tail.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- The exponential of the total physical jump count is integrable under every heterogeneous
deterministic-initial replica source at a nonnegative exponent. -/
theorem integrable_exp_mul_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ≥0)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    Integrable
      (fun histories : Fin replicaCount → FiniteJumpHistory State =>
        Real.exp
          ((finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) * exponent))
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration duration.coe_nonneg).toMeasure := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration duration.coe_nonneg).toMeasure
  let coordinateCount : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
    fun replica histories => ((histories replica).jumpCount : ℝ)
  have hCoordinateCountMeasurable : ∀ replica, Measurable (coordinateCount replica) := by
    intro replica
    exact (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
      (FiniteJumpHistory.measurable_jumpCount.comp (measurable_pi_apply replica))
  have hIndependent : iIndepFun coordinateCount law := by
    have hHistoryIndependent :=
      finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun
        initialConfiguration generator duration duration.coe_nonneg
    have hCountIndependent := iIndepFun.comp
      (β := fun _ : Fin replicaCount => FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount => ℝ) hHistoryIndependent
      (fun _ history => (history.jumpCount : ℝ))
      (fun _ => (show Measurable
          (fun history : FiniteJumpHistory State => (history.jumpCount : ℝ)) from
        (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
          FiniteJumpHistory.measurable_jumpCount))
    simpa [coordinateCount, Function.comp_def] using! hCountIndependent
  have hCoordinateIntegrable : ∀ replica ∈ (Finset.univ : Finset (Fin replicaCount)),
      Integrable
        (fun histories => Real.exp (exponent * coordinateCount replica histories)) law := by
    intro replica _hReplica
    have hSingle := integrable_exp_mul_finiteStateMarkovJumpCount
      (PMF.pure (initialConfiguration replica)) generator duration hExponent
    rw [← finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
      initialConfiguration generator duration duration.coe_nonneg replica] at hSingle
    have hMapped := (integrable_map_measure hSingle.1
      (measurable_pi_apply replica).aemeasurable).mp hSingle
    simpa [law, coordinateCount, Function.comp_def, mul_comm] using hMapped
  have hSumIntegrable := hIndependent.integrable_exp_mul_sum
    hCoordinateCountMeasurable hCoordinateIntegrable
  simpa [law, coordinateCount, finiteJumpHistoryReplicaTotalJumpCount, mul_comm] using
    hSumIntegrable

/-- The total physical jump-count moment is bounded by the exponential of replica number times the
single-clock Poisson cumulant.  The estimate is uniform over every labelled initial
configuration; identical initial states are not assumed. -/
theorem mgf_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ≥0)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    mgf
        (fun histories : Fin replicaCount → FiniteJumpHistory State =>
          (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ))
        (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration duration.coe_nonneg).toMeasure
        exponent ≤
      Real.exp ((replicaCount : ℝ) *
        (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
          (Real.exp exponent - 1))) := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration duration.coe_nonneg).toMeasure
  let coordinateCount : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
    fun replica histories => ((histories replica).jumpCount : ℝ)
  have hCoordinateCountMeasurable : ∀ replica, Measurable (coordinateCount replica) := by
    intro replica
    exact (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
      (FiniteJumpHistory.measurable_jumpCount.comp (measurable_pi_apply replica))
  have hIndependent : iIndepFun coordinateCount law := by
    have hHistoryIndependent :=
      finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun
        initialConfiguration generator duration duration.coe_nonneg
    have hCountIndependent := iIndepFun.comp
      (β := fun _ : Fin replicaCount => FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount => ℝ) hHistoryIndependent
      (fun _ history => (history.jumpCount : ℝ))
      (fun _ => (show Measurable
          (fun history : FiniteJumpHistory State => (history.jumpCount : ℝ)) from
        (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
          FiniteJumpHistory.measurable_jumpCount))
    simpa [coordinateCount, Function.comp_def] using! hCountIndependent
  have hCoordinateMoment (replica : Fin replicaCount) :
      mgf (coordinateCount replica) law exponent ≤
        Real.exp (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
          (Real.exp exponent - 1)) := by
    calc
      mgf (coordinateCount replica) law exponent =
          mgf (fun history : FiniteJumpHistory State => (history.jumpCount : ℝ))
            (Measure.map (Function.eval replica) law) exponent := by
        have hHistoryCountExponential : Measurable
            (fun history : FiniteJumpHistory State =>
              Real.exp (exponent * (history.jumpCount : ℝ))) :=
          (((measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
            FiniteJumpHistory.measurable_jumpCount).const_mul exponent).exp
        simpa [coordinateCount, Function.comp_def] using
          (mgf_map (μ := law) (Y := Function.eval replica)
            (X := fun history : FiniteJumpHistory State => (history.jumpCount : ℝ))
            (t := exponent) (measurable_pi_apply replica).aemeasurable
            hHistoryCountExponential.aestronglyMeasurable).symm
      _ = mgf (fun history : FiniteJumpHistory State => (history.jumpCount : ℝ))
          (finiteStateMarkovJumpDensityMeasure
            (PMF.pure (initialConfiguration replica)) generator duration) exponent := by
        change mgf (fun history : FiniteJumpHistory State => (history.jumpCount : ℝ))
            (Measure.map (Function.eval replica)
              (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
                initialConfiguration generator duration duration.coe_nonneg).toMeasure)
            exponent = _
        rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map]
      _ ≤ Real.exp (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
          (Real.exp exponent - 1)) := by
        simpa [mgf, mul_comm] using
          (integral_exp_mul_finiteStateMarkovJumpCount_le
            (PMF.pure (initialConfiguration replica)) generator duration hExponent)
  have hSumMoment := hIndependent.mgf_sum (t := exponent) hCoordinateCountMeasurable
    (Finset.univ : Finset (Fin replicaCount))
  change mgf
      (fun histories : Fin replicaCount → FiniteJumpHistory State =>
        (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ))
      law exponent ≤ _
  rw [show (fun histories : Fin replicaCount → FiniteJumpHistory State =>
      (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ)) =
      ∑ replica ∈ (Finset.univ : Finset (Fin replicaCount)), coordinateCount replica by
        funext histories
        simp [coordinateCount, finiteJumpHistoryReplicaTotalJumpCount]]
  rw [hSumMoment]
  calc
    ∏ replica ∈ (Finset.univ : Finset (Fin replicaCount)),
        mgf (coordinateCount replica) law exponent ≤
      ∏ _replica ∈ (Finset.univ : Finset (Fin replicaCount)),
        Real.exp (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
          (Real.exp exponent - 1)) := by
      apply Finset.prod_le_prod₀
      · intro replica _hReplica
        exact mgf_nonneg
      · intro replica _hReplica
        exact hCoordinateMoment replica
    _ = Real.exp ((replicaCount : ℝ) *
        (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
          (Real.exp exponent - 1))) := by
      rw [Finset.prod_const, Finset.card_fin, ← Real.exp_nat_mul]

/-- A configuration-uniform Chernoff bound for total physical jump count at particle-number
speed.  The threshold remains a real number so callers can use a replica-scaled compactness
cutoff without integer rounding. -/
theorem finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_gt_le_exponential
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ≥0)
    {exponent : ℝ} (hExponent : 0 < exponent) (threshold : ℝ) :
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration duration.coe_nonneg).toMeasure
        {histories | threshold < finiteJumpHistoryReplicaTotalJumpCount histories} ≤
      ENNReal.ofReal
        (Real.exp
          ((replicaCount : ℝ) *
              (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
                (Real.exp exponent - 1)) -
            threshold * exponent)) := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration duration.coe_nonneg).toMeasure
  let exponentialCount :
      (Fin replicaCount → FiniteJumpHistory State) → ℝ≥0∞ :=
    fun histories => ENNReal.ofReal
      (Real.exp
        ((finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) * exponent))
  let exponentialThreshold : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (threshold * exponent))
  have hExponentialCountMeasurable : Measurable exponentialCount := by
    exact (measurable_of_countable fun count : ℕ =>
      ENNReal.ofReal (Real.exp ((count : ℝ) * exponent))).comp
        measurable_finiteJumpHistoryReplicaTotalJumpCount
  have hThresholdPositive : exponentialThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hEventSubset :
      {histories : Fin replicaCount → FiniteJumpHistory State |
          threshold < finiteJumpHistoryReplicaTotalJumpCount histories} ⊆
        {histories | exponentialThreshold ≤ exponentialCount histories} := by
    intro histories hHistories
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hHistories.le hExponent.le
  have hIntegrable :=
    integrable_exp_mul_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount
      initialConfiguration generator duration hExponent.le
  have hMoment :=
    mgf_finiteStateMarkovJumpDeterministicInitialReplicaTotalJumpCount_le
      initialConfiguration generator duration hExponent.le
  change law
      {histories | threshold < finiteJumpHistoryReplicaTotalJumpCount histories} ≤ _
  calc
    law {histories | threshold < finiteJumpHistoryReplicaTotalJumpCount histories} ≤
        law {histories | exponentialThreshold ≤ exponentialCount histories} :=
      measure_mono hEventSubset
    _ ≤ (∫⁻ histories, exponentialCount histories ∂law) / exponentialThreshold :=
      meas_ge_le_lintegral_div hExponentialCountMeasurable.aemeasurable
        hThresholdPositive ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal
          (∫ histories : Fin replicaCount → FiniteJumpHistory State,
            Real.exp
              ((finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) * exponent) ∂law) /
        exponentialThreshold := by
      rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable
        (Filter.Eventually.of_forall fun histories =>
          (Real.exp_pos
            ((finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) * exponent)).le)]
    _ ≤ ENNReal.ofReal
          (Real.exp
            ((replicaCount : ℝ) *
              (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
                (Real.exp exponent - 1)))) /
        exponentialThreshold := by
      apply ENNReal.div_le_div_right
      apply ENNReal.ofReal_le_ofReal
      simpa [mgf, law, mul_comm] using hMoment
    _ = ENNReal.ofReal
        (Real.exp
          ((replicaCount : ℝ) *
              (((generator.uniformizationRate * duration : ℝ≥0) : ℝ) *
                (Real.exp exponent - 1)) -
            threshold * exponent)) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]

end

end FiniteMarkovProcesses.Probability
