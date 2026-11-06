/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovIIDHybridFiniteSample
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpCountExponentialTail
import FiniteMarkovProcesses.Probability.PoissonDominatedCenteredExponential
import FiniteMarkovProcesses.Probability.FiniteIIDIntegratedL1Exponential

/-!
# Exponential confidence for the original IID Markov hybrid observation

Self-event deletion transports centered count estimates from the exact uniformized Poisson
law to the physical history law. Density randomness and arbitrary initial PMFs remain visible.
The resulting finite-particle estimate concerns the existing total hybrid observation and its
unconditional mean, with the physical time interval unchanged.

## Main results

* `mgf_centered_physical_count_observable_le`: source-preserving Poisson domination.
* `finiteJumpHistoryHybridCoordinate_centered_mgf_le`: common local coordinate estimate.
* `measure_iid_totalHybridBVObservation_deviation_le_exponential`: actual path-event bound.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open FiniteMarkovProcesses PositiveFiniteJumpHistoryReplicas
open scoped BigOperators ENNReal NNReal

noncomputable section

universe u
variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A nonnegative physical observation bounded by complete jump count inherits a centered
Poisson remainder bound through the exact deletion pushforward. -/
theorem mgf_centered_physical_count_observable_le
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : NNReal) (observable : FiniteJumpHistory State → ℝ)
    (hMeasurable : Measurable observable)
    (hBound : ∀ history, 0 ≤ observable history ∧ observable history ≤ (history.jumpCount : ℝ))
    (tilt : ℝ) :
    Integrable (fun history ↦ Real.exp (tilt * (observable history -
      ∫ point, observable point ∂finiteStateMarkovJumpDensityMeasure initial generator duration)))
      (finiteStateMarkovJumpDensityMeasure initial generator duration) ∧
    mgf (fun history ↦ observable history - ∫ point, observable point
      ∂finiteStateMarkovJumpDensityMeasure initial generator duration)
      (finiteStateMarkovJumpDensityMeasure initial generator duration) tilt ≤
        Real.exp (poissonExponentialRemainder
          ((generator.uniformizationRate * duration : NNReal) : ℝ) |tilt|) := by
  let uniformized := finiteStateMarkovUniformizedDensityMeasure initial generator duration
  let : IsProbabilityMeasure uniformized :=
    ⟨finiteStateMarkovUniformizedDensityMeasure_univ initial generator duration.coe_nonneg⟩
  have hDeletion := map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator duration.coe_nonneg
  have hMean : (∫ point, observable point
      ∂finiteStateMarkovJumpDensityMeasure initial generator duration) =
      ∫ point, observable point.deleteSelfEvents ∂uniformized := by
    rw [← hDeletion, integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
      hMeasurable.aestronglyMeasurable]
  have hScalar := mgf_centered_le_poissonRemainder uniformized
    (fun history ↦ observable history.deleteSelfEvents) FiniteJumpHistory.jumpCount
    (generator.uniformizationRate * duration)
    (hMeasurable.comp FiniteJumpHistory.measurable_deleteSelfEvents)
    FiniteJumpHistory.measurable_jumpCount
    (fun history ↦ ⟨(hBound history.deleteSelfEvents).1,
      (hBound history.deleteSelfEvents).2.trans
        (by exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history)⟩)
    (map_jumpCount_finiteStateMarkovUniformizedDensityMeasure initial generator duration) tilt
  constructor
  · rw [hMean, ← hDeletion]
    exact (integrable_map_measure (by fun_prop)
      FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable).mpr hScalar.1
  · rw [hMean, mgf, ← hDeletion,
      integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable (by fun_prop)]
    exact hScalar.2

/-- Every density or cumulative ordered-flow coordinate has a centered local exponential bound
under the original arbitrary-initial-PMF law. The virtual intensity does not replace its mean. -/
theorem finiteJumpHistoryHybridCoordinate_centered_mgf_le
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : NNReal) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (time tilt : ℝ)
    (hTilt : |tilt| ≤ 1 /
      (4 * (((generator.uniformizationRate * duration : NNReal) : ℝ) + 1))) :
    Integrable (fun history ↦ Real.exp (tilt *
      (finiteJumpHistoryHybridCoordinate coordinate time history -
        ∫ point, finiteJumpHistoryHybridCoordinate coordinate time point
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            initial generator.toTimeDependentMarkovRate duration)))
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration) ∧
    mgf (fun history ↦ finiteJumpHistoryHybridCoordinate coordinate time history -
      ∫ point, finiteJumpHistoryHybridCoordinate coordinate time point
        ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
          initial generator.toTimeDependentMarkovRate duration)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration) tilt ≤
      Real.exp (((((generator.uniformizationRate * duration : NNReal) : ℝ) + 1) ^ 2) *
        tilt ^ 2) := by
  let intensity : ℝ := ((generator.uniformizationRate * duration : NNReal) : ℝ)
  have hIntensity : 0 ≤ intensity := NNReal.coe_nonneg _
  have hTiltOne : |tilt| ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 4 * (intensity + 1) by positivity)).mp hTilt
    nlinarith [mul_nonneg (abs_nonneg tilt) hIntensity]
  cases coordinate with
  | inl state =>
      let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration
      let : IsProbabilityMeasure law :=
        ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial _ duration⟩
      have h := mgf_centered_le_exp_sq_of_mem_Icc law
        (finiteJumpHistoryStateMembershipAtTime time state)
        (measurable_finiteJumpHistoryStateMembershipAtTime time state)
        (finiteJumpHistoryStateMembershipAtTime_mem_Icc time state) hTiltOne
      refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
      change tilt ^ 2 ≤ (intensity + 1) ^ 2 * tilt ^ 2
      nlinarith [sq_nonneg tilt, mul_nonneg hIntensity (sq_nonneg tilt),
        sq_nonneg (intensity * tilt)]
  | inr edge =>
      rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_constant]
      have h := mgf_centered_physical_count_observable_le initial generator duration
        (fun history ↦ (history.directedTransitionCountAtTime time edge.val.1 edge.val.2 : ℝ))
        ((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
          (FiniteJumpHistory.measurable_directedTransitionCountAtTime
            time edge.val.1 edge.val.2))
        (fun history ↦ ⟨by positivity, by exact_mod_cast
          history.directedTransitionCountAtTime_le_jumpCount time edge.val.1 edge.val.2⟩) tilt
      refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
      simpa only [sq_abs] using
        poissonExponentialRemainder_le_quadratic hIntensity (abs_nonneg tilt) hTilt

/-- The existing total hybrid observation obeys a direct exponential Chernoff bound on its
original IID law and unconditional mean. The tilt cap retains unbounded count tails. -/
theorem measure_iid_totalHybridBVObservation_deviation_le_exponential
    [Nonempty State] (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : NNReal)
    (hDuration : 0 < duration) (tilt : ℝ) (hTilt : 0 ≤ tilt)
    (hCap : tilt ≤ 1 /
      (4 * (((generator.uniformizationRate * duration : NNReal) : ℝ) + 1)))
    (radius : ℝ) :
    (Measure.pi fun _ : Fin (successorIndex + 1) ↦
      finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration)
      {histories | radius ≤
        ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath.toL1Path -
          (finiteStateTimeDependentMarkovMeanHybridBVPath initial
            generator.toTimeDependentMarkovRate duration).toDerivativePath.toL1Path‖} ≤
      ENNReal.ofReal (2 * Real.exp
        ((successorIndex + 1 : ℝ) *
          ((((generator.uniformizationRate * duration : NNReal) : ℝ) + 1) ^ 2 * tilt ^ 2) -
         (successorIndex + 1 : ℝ) * tilt * radius /
          ((duration : ℝ) *
            (Fintype.card (EmpiricalDensityDirectionalFlowCoordinate State) : ℝ)))) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial generator.toTimeDependentMarkovRate duration
  let timeLaw := finiteOpenIntervalVolume (duration : ℝ)
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial _ duration⟩
  have hMass : 0 < timeLaw.real univ := by
    simp only [timeLaw, Measure.real, finiteOpenIntervalVolume_apply_univ,
      ENNReal.toReal_ofReal duration.coe_nonneg]
    exact_mod_cast hDuration
  have hGeneric := measure_finiteIIDIntegratedL1Deviation_ge_le_exponential
    law timeLaw hMass successorIndex (finiteJumpHistoryHybridCoordinate (State := State))
    (fun coordinate time ↦ (measurable_finiteJumpHistoryHybridCoordinate_uncurry coordinate).comp
      (measurable_id.prodMk measurable_const))
    (memLp_two_finiteJumpHistoryHybridCoordinate_uncurry initial _ duration)
    (memLp_two_mean_finiteJumpHistoryHybridCoordinate initial _ duration)
    tilt ((((generator.uniformizationRate * duration : NNReal) : ℝ) + 1) ^ 2 * tilt ^ 2)
    hTilt (fun coordinate time sign hSign ↦ by
      have h := finiteJumpHistoryHybridCoordinate_centered_mgf_le initial generator duration
        coordinate time sign (by rw [hSign]; exact hCap)
      have hSquare : sign ^ 2 = tilt ^ 2 := by rw [← sq_abs sign, hSign]
      simpa only [hSquare] using h) radius
  have hEvents :
      {histories | radius ≤
        ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath.toL1Path -
          (finiteStateTimeDependentMarkovMeanHybridBVPath initial
            generator.toTimeDependentMarkovRate duration).toDerivativePath.toL1Path‖} =ᵐ[
          Measure.pi fun _ : Fin (successorIndex + 1) ↦ law]
      {histories | radius ≤ finiteIIDIntegratedL1Deviation law timeLaw successorIndex
        (finiteJumpHistoryHybridCoordinate (State := State)) histories} := by
    filter_upwards [ae_orderedBefore_finiteStateTimeDependentMarkovIIDReplica
      successorIndex initial generator.toTimeDependentMarkovRate duration] with histories hOrdered
    simp only [law, timeLaw, finiteIIDIntegratedL1Deviation, finiteIIDCoordinateDeviation,
      norm_totalHybridBVObservation_sub_iidMean_eq_integral
        successorIndex initial generator.toTimeDependentMarkovRate duration
          hDuration histories hOrdered]
  rw [measure_congr hEvents]
  simpa only [timeLaw, Measure.real, finiteOpenIntervalVolume_apply_univ,
    ENNReal.toReal_ofReal duration.coe_nonneg] using hGeneric

end

end FiniteMarkovProcesses.Probability
