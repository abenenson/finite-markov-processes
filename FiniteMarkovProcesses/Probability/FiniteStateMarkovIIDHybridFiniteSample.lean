/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalHybridL1Concentration
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovRoundedInitialMeanConvergence
public import FiniteMarkovProcesses.Probability.PoissonCountExactSecondMoment
public import FiniteMarkovProcesses.Probability.FiniteIIDIntegratedL1Concentration

/-!
# Finite-sample hybrid-path control with the original IID initial randomness

The one-history density and ordered-count observables retain arbitrary initial PMFs. Their
literal expectations identify the canonical mean hybrid path. The empirical product source
therefore centers at that mean, without conditioning on an initial configuration.

## Main results

- `finiteJumpHistoryHybridCoordinate`: the original microscopic coordinate observables.
- `integral_finiteJumpHistoryHybridCoordinate_eq_mean`: exact source-mean identification.
- `norm_totalHybridBVObservation_sub_iidMean_eq_integral`: the unchanged strong-L1 statistic.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open FiniteMarkovProcesses
open PositiveFiniteJumpHistoryReplicas
open scoped BigOperators ENNReal NNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The actual density indicator or cumulative ordered-flow count of one complete history. -/
def finiteJumpHistoryHybridCoordinate
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (time : ℝ) (history : FiniteJumpHistory State) : ℝ :=
  match coordinate with
  | Sum.inl state => finiteJumpHistoryStateMembershipAtTime time state history
  | Sum.inr edge => (history.directedTransitionCountAtTime time edge.val.1 edge.val.2 : ℝ)

/-- Each microscopic coordinate is jointly measurable in history and physical time. -/
theorem measurable_finiteJumpHistoryHybridCoordinate_uncurry
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    Measurable (fun data : FiniteJumpHistory State × ℝ ↦
      finiteJumpHistoryHybridCoordinate coordinate data.2 data.1) := by
  cases coordinate with
  | inl state => exact measurable_finiteJumpHistoryStateMembershipAtTime_uncurry state
  | inr edge =>
      exact FiniteJumpHistory.measurable_real_directedTransitionCountAtTime_uncurry
        edge.val.1 edge.val.2

/-- Every coordinate retains the existing arbitrary-initial-PMF finite second moment. -/
theorem memLp_two_finiteJumpHistoryHybridCoordinate
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (time : ℝ) :
    MemLp (finiteJumpHistoryHybridCoordinate coordinate time) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  cases coordinate with
  | inl state =>
      exact memLp_two_finiteJumpHistoryStateMembershipAtTime initial rates duration time state
  | inr edge =>
      exact memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
        initial rates duration time edge.val.1 edge.val.2

/-- The mean of the actual microscopic observable is the existing mean hybrid coordinate on
physical time. Random initial states remain integrated under the original initial PMF. -/
theorem integral_finiteJumpHistoryHybridCoordinate_eq_mean
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    {time : ℝ} (hTime : time ∈ Ioo (0 : ℝ) duration) :
    (∫ history, finiteJumpHistoryHybridCoordinate coordinate time history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) =
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time coordinate := by
  cases coordinate with
  | inl state =>
      exact finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
        initial rates duration hTime.1.le hTime.2.le state
  | inr edge =>
      exact finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_meanHybridBVValueAtTime
        initial rates duration hTime.1.le edge

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Microscopic averaging recovers the existing empirical coordinate, not a new observation. -/
theorem empiricalHybridCoordinate_eq_average
    (successorIndex : ℕ) (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time coordinate =
      (∑ replica, finiteJumpHistoryHybridCoordinate coordinate time (histories replica)) /
        (successorIndex + 1 : ℝ) := by
  cases coordinate with
  | inl state => rfl
  | inr edge => rfl

/-- The true source means are square-integrable in physical time. Density means are bounded by
one, and cumulative-flow means by the finite expected complete jump count. -/
theorem memLp_two_mean_finiteJumpHistoryHybridCoordinate
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    MemLp (fun time ↦ ∫ history, finiteJumpHistoryHybridCoordinate coordinate time history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration)
      2 (finiteOpenIntervalVolume (duration : ℝ)) := by
  cases coordinate with
  | inl state =>
      change MemLp (fun time ↦
        finiteStateTimeDependentMarkovMeanDensityAt initial rates duration time state) 2 _
      apply MemLp.of_bound
        (measurable_finiteStateTimeDependentMarkovMeanDensityAt
          initial rates duration state).aestronglyMeasurable 1
      filter_upwards [] with time
      have h := finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
        initial rates duration time state
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  | inr edge =>
      change MemLp (fun time ↦
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          initial rates duration time edge.val.1 edge.val.2) 2 _
      apply MemLp.of_bound
        (measurable_finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          initial rates duration edge.val.1 edge.val.2).aestronglyMeasurable
        (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ)
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration)
      filter_upwards [] with time
      have h :=
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_mem_Icc_jumpCountMean
          initial rates duration time edge.val.1 edge.val.2
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- Joint history/time square integrability is proved from the actual arbitrary-PMF law. -/
theorem memLp_two_finiteJumpHistoryHybridCoordinate_uncurry
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    MemLp (fun data : FiniteJumpHistory State × ℝ ↦
      finiteJumpHistoryHybridCoordinate coordinate data.2 data.1) 2
      ((finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration).prod
        (finiteOpenIntervalVolume (duration : ℝ))) := by
  cases coordinate with
  | inl state =>
      exact memLp_two_finiteJumpHistoryStateMembershipAtTime_uncurry
        initial rates duration state _
  | inr edge =>
      exact memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_uncurry
        initial rates duration edge.val.1 edge.val.2 _

/-- Density indicators use variance one; each ordered-flow count uses the exact Poisson
second-moment envelope of the existing uniformization clock. -/
def finiteStateMarkovIIDHybridVarianceBound
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) : ℝ :=
  match coordinate with
  | Sum.inl _state => 1
  | Sum.inr _edge =>
      ((rates.uniformizationRate * duration : NNReal) : ℝ) ^ 2 +
        ((rates.uniformizationRate * duration : NNReal) : ℝ)

/-- The actual one-history coordinate variance obeys the same bound at every observation time. -/
theorem variance_finiteJumpHistoryHybridCoordinate_le
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (time : ℝ) :
    variance (finiteJumpHistoryHybridCoordinate coordinate time)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      finiteStateMarkovIIDHybridVarianceBound rates duration coordinate := by
  cases coordinate with
  | inl state =>
      exact variance_finiteJumpHistoryStateMembershipAtTime_le_one
        initial rates duration time state
  | inr edge =>
      exact
        variance_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_le_poissonSecondMoment
        initial rates duration time edge.val.1 edge.val.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The variance budget retains separate state and ordered-flow cardinalities. -/
theorem sum_finiteStateMarkovIIDHybridVarianceBound
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    (∑ coordinate, finiteStateMarkovIIDHybridVarianceBound rates duration coordinate) =
      (Fintype.card State : ℝ) + (Fintype.card (FiniteStateOffDiagonalEdge State) : ℝ) *
        (((rates.uniformizationRate * duration : NNReal) : ℝ) ^ 2 +
          ((rates.uniformizationRate * duration : NNReal) : ℝ)) := by
  simp only [Fintype.sum_sum_type, finiteStateMarkovIIDHybridVarianceBound,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Under the original IID product source every history is ordered almost surely. No initial
configuration is selected or conditioned on. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovIIDReplica
    (successorIndex : ℕ) (initial : PMF State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    ∀ᵐ histories ∂(Measure.pi fun _ : Fin (successorIndex + 1) ↦
      finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration),
      ∀ replica, (histories replica).OrderedBefore (duration : ℝ) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  rw [ae_all_iff]
  intro replica
  have hHistory := ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates duration
  have hMap : Measure.map (Function.eval replica)
      (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law) = law :=
    (measurePreserving_eval (fun _ : Fin (successorIndex + 1) ↦ law) replica).map_eq
  change ∀ᵐ history ∂law, history.OrderedBefore (duration : ℝ) at hHistory
  rw [← hMap] at hHistory
  exact ae_of_ae_map (measurable_pi_apply replica).aemeasurable hHistory

/-- Explicit squared strong-L1 moment constant from the actual clock and coordinate variances. -/
def finiteStateMarkovIIDHybridFiniteSampleConstant
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) : ℝ :=
  (duration : ℝ) ^ 2 * (Fintype.card (EmpiricalDensityDirectionalFlowCoordinate State) : ℝ) *
    ((Fintype.card State : ℝ) + (Fintype.card (FiniteStateOffDiagonalEdge State) : ℝ) *
      (((rates.uniformizationRate * duration : NNReal) : ℝ) ^ 2 +
        ((rates.uniformizationRate * duration : NNReal) : ℝ)))

section TotalObservation

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On the original ordered physical slice, the actual strong-L1 norm equals the integrated
sum of centered IID coordinate averages. This identity is independent of any rate budget. -/
theorem norm_totalHybridBVObservation_sub_iidMean_eq_integral
    (successorIndex : ℕ) (initial : PMF State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore (duration : ℝ)) :
    ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath.toL1Path -
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        initial rates duration).toDerivativePath.toL1Path‖ =
      ∫ time, ∑ coordinate,
        |(∑ replica, finiteJumpHistoryHybridCoordinate coordinate time (histories replica)) /
            (successorIndex + 1 : ℝ) -
          ∫ history, finiteJumpHistoryHybridCoordinate coordinate time history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration|
        ∂finiteOpenIntervalVolume (duration : ℝ) := by
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  simp only [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation,
    empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path]
  let actual :=
    empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories
  let mean := finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration
  have hActual : MemLp actual 1 (finiteOpenIntervalVolume (duration : ℝ)) :=
    memLp_empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories duration hDuration hOrdered
  have hMean := memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration
  rcases empiricalDensityDirectionalFlowExplicitL1Path_represents
      successorIndex histories duration with ⟨hEventStep, hEventStepQuotient⟩
  have hActualQuotient : hActual.toLp actual =
      empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration := by
    calc
      _ = hEventStep.toLp
          (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
            successorIndex histories) := by
        apply hActual.toLp_congr hEventStep
        filter_upwards [] with time
        exact (empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
          successorIndex histories duration time hOrdered).symm
      _ = _ := hEventStepQuotient
  change ‖empiricalDensityDirectionalFlowExplicitL1Path
      successorIndex histories duration - hMean.toLp mean‖ = _
  rw [← hActualQuotient, ← hActual.toLp_sub hMean, Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm (hActual.sub hMean).aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm (hActual.sub hMean).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  simp only [Pi.sub_apply, PiLp.norm_eq_of_L1]
  apply Finset.sum_congr rfl
  intro coordinate _hCoordinate
  rw [PiLp.sub_apply]
  change |actual time coordinate - mean time coordinate| = _
  rw [empiricalHybridCoordinate_eq_average,
    integral_finiteJumpHistoryHybridCoordinate_eq_mean initial rates duration coordinate hTime]

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- An all-particle-count probability bound for the actual IID total observation around the
unconditional source mean. Every moment, mean, and totalization premise is discharged here. -/
theorem measure_iid_totalHybridBVObservation_projection_deviation_ge_le
    (successorIndex : ℕ) (initial : PMF State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration) {radius : ℝ} (hRadius : 0 < radius) :
    (Measure.pi fun _ : Fin (successorIndex + 1) ↦
      finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration)
      {histories | radius ≤
        ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath.toL1Path -
          (finiteStateTimeDependentMarkovMeanHybridBVPath
            initial rates duration).toDerivativePath.toL1Path‖} ≤
      ENNReal.ofReal (finiteStateMarkovIIDHybridFiniteSampleConstant rates duration /
        ((successorIndex + 1 : ℝ) * radius ^ 2)) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let timeMeasure := finiteOpenIntervalVolume (duration : ℝ)
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hGeneric := measure_finiteIIDIntegratedL1Deviation_ge_le
    law timeMeasure successorIndex (finiteJumpHistoryHybridCoordinate (State := State))
    (memLp_two_finiteJumpHistoryHybridCoordinate_uncurry initial rates duration)
    (memLp_two_mean_finiteJumpHistoryHybridCoordinate initial rates duration)
    (memLp_two_finiteJumpHistoryHybridCoordinate initial rates duration)
    (finiteStateMarkovIIDHybridVarianceBound rates duration)
    (variance_finiteJumpHistoryHybridCoordinate_le initial rates duration) hRadius
  have hEvents :
      {histories | radius ≤
        ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath.toL1Path -
          (finiteStateTimeDependentMarkovMeanHybridBVPath
            initial rates duration).toDerivativePath.toL1Path‖} =ᵐ[
          Measure.pi fun _ : Fin (successorIndex + 1) ↦ law]
      {histories | radius ≤ finiteIIDIntegratedL1Deviation law timeMeasure successorIndex
        (finiteJumpHistoryHybridCoordinate (State := State)) histories} := by
    filter_upwards [ae_orderedBefore_finiteStateTimeDependentMarkovIIDReplica
      successorIndex initial rates duration] with histories hOrdered
    simp only [law, timeMeasure, finiteIIDIntegratedL1Deviation, finiteIIDCoordinateDeviation,
      norm_totalHybridBVObservation_sub_iidMean_eq_integral
        successorIndex initial rates duration hDuration histories hOrdered]
  rw [measure_congr hEvents]
  simpa only [timeMeasure, Measure.real, finiteOpenIntervalVolume_apply_univ,
    ENNReal.toReal_ofReal duration.coe_nonneg, finiteStateMarkovIIDHybridFiniteSampleConstant,
    sum_finiteStateMarkovIIDHybridVarianceBound] using hGeneric

end TotalObservation

end

end FiniteMarkovProcesses.Probability
