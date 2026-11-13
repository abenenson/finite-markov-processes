/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1PathWeightedCoordinateIntegral
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialBoundaryExponentialTail
public import
  FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservationMeasurability
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation

/-!
# Initial-boundary control of empirical hybrid-BV flow observations

This module constructs a continuous strong-`L1` probe supported next to the initial temporal
boundary and bounds its value on an empirical cumulative-flow coordinate by the weighted number
of microscopic jumps in that boundary layer.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal Topology

open FiniteMarkovProcesses
open PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

/-- A compact continuous initial-boundary probe: zero outside `[0, margin]` and one on the middle
third of that interval. -/
noncomputable def finiteStateMarkovJumpInitialBoundaryFlowObservationTest
    (margin : ℝ) (hMargin : 0 < margin) : C_c(ℝ, ℝ) :=
  finiteOpenIntervalCoreCutoff margin (margin / 3) (by positivity)

/-- The initial-boundary flow probe is nonnegative. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_nonnegative
    {margin : ℝ} (hMargin : 0 < margin) (time : ℝ) :
    0 ≤ finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time :=
  (finiteOpenIntervalCoreCutoff_mem_Icc (by positivity) time).1

/-- The initial-boundary flow probe is at most one. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_le_one
    {margin : ℝ} (hMargin : 0 < margin) (time : ℝ) :
    finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time ≤ 1 :=
  (finiteOpenIntervalCoreCutoff_mem_Icc (by positivity) time).2

/-- The initial-boundary flow probe vanishes outside its positive-margin support interval. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_eq_zero_of_not_mem
    {margin time : ℝ} (hMargin : 0 < margin) (hTime : time ∉ Ioo 0 margin) :
    finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time = 0 :=
  finiteOpenIntervalCoreCutoff_eq_zero_of_not_mem (by positivity) hTime

/-- The initial-boundary probe has physical-time integral at least the width of its middle-third
plateau. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_integral_ge_margin_div_three
    {duration margin : ℝ} (hDuration : 0 ≤ duration)
    (hMargin : 0 < margin) (hLayer : margin ≤ duration) :
    margin / 3 ≤
      ∫ time, finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time
        ∂finiteOpenIntervalVolume duration := by
  let test := finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin
  have hTestIntegrable : IntervalIntegrable test volume 0 duration :=
    test.continuous.intervalIntegrable 0 duration
  have hCoreOrder : margin / 3 ≤ margin - margin / 3 := by linarith
  have hCoreIntegral :
      (∫ time in margin / 3..margin - margin / 3, test time) = margin / 3 := by
    rw [show (∫ time in margin / 3..margin - margin / 3, test time) =
        ∫ _time in margin / 3..margin - margin / 3, (1 : ℝ) by
      apply intervalIntegral.integral_congr
      intro time hTime
      have hTimeIcc : time ∈ Icc (margin / 3) (margin - margin / 3) := by
        simpa only [uIcc_of_le hCoreOrder] using hTime
      exact finiteOpenIntervalCoreCutoff_eq_one_of_mem_core (by positivity) hTimeIcc]
    simp
    ring
  have hCoreLe :
      (∫ time in margin / 3..margin - margin / 3, test time) ≤
        ∫ time in 0..duration, test time := by
    exact intervalIntegral.integral_mono_interval
      (by positivity) hCoreOrder (by linarith) (by
        exact Filter.Eventually.of_forall fun time =>
          finiteStateMarkovJumpInitialBoundaryFlowObservationTest_nonnegative hMargin time)
      hTestIntegrable
  calc
    margin / 3 = ∫ time in margin / 3..margin - margin / 3, test time :=
      hCoreIntegral.symm
    _ ≤ ∫ time in 0..duration, test time := hCoreLe
    _ = ∫ time, test time ∂finiteOpenIntervalVolume duration := by
      have hConstant := integral_compactTest_mul_constant_finiteOpenIntervalVolume
        (duration := duration) test 1 hDuration
      simpa only [mul_one, one_mul] using hConstant.symm

/-- A tail integral of the initial-boundary probe is nonnegative and bounded by the margin times
the microscopic cutoff evaluated at the tail's starting time. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_tailIntegral_mem_Icc
    {duration margin eventTime : ℝ}
    (hMargin : 0 < margin) (hLayer : margin ≤ duration)
    (hEventTime : eventTime ∈ Ioo 0 duration) :
    (∫ time in eventTime..duration,
        finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time) ∈
      Icc 0
        (margin * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin eventTime) := by
  let test := finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin
  have hTestContinuous : Continuous test := test.continuous
  have hTestIntegrable (lower upper : ℝ) :
      IntervalIntegrable test volume lower upper :=
    hTestContinuous.intervalIntegrable lower upper
  have hIntegralNonnegative :
      0 ≤ ∫ time in eventTime..duration, test time := by
    exact intervalIntegral.integral_nonneg hEventTime.2.le
      fun time _hTime =>
        finiteStateMarkovJumpInitialBoundaryFlowObservationTest_nonnegative hMargin time
  refine ⟨hIntegralNonnegative, ?_⟩
  by_cases hBeforeMargin : eventTime ≤ margin
  · have hTailAfterMargin : (∫ time in margin..duration, test time) = 0 := by
      rw [show (∫ time in margin..duration, test time) =
          ∫ _time in margin..duration, (0 : ℝ) by
        apply intervalIntegral.integral_congr
        intro time hTime
        have hTimeIcc : time ∈ Icc margin duration := by
          simpa only [uIcc_of_le hLayer] using hTime
        exact finiteStateMarkovJumpInitialBoundaryFlowObservationTest_eq_zero_of_not_mem
          hMargin (by simp only [mem_Ioo, not_and_or, not_lt]; exact Or.inr hTimeIcc.1)]
      simp
    have hSplit := intervalIntegral.integral_add_adjacent_intervals
      (hTestIntegrable eventTime margin) (hTestIntegrable margin duration)
    have hToMargin :
        (∫ time in eventTime..duration, test time) =
          ∫ time in eventTime..margin, test time := by
      linarith
    rw [hToMargin]
    rw [finiteStateMarkovJumpInitialBoundaryTimeCutoff_eq_one hMargin hBeforeMargin]
    simp only [mul_one]
    calc
      (∫ time in eventTime..margin, test time) ≤
          ∫ _time in eventTime..margin, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on hBeforeMargin
          (hTestIntegrable eventTime margin) intervalIntegrable_const
          (fun time _ =>
            finiteStateMarkovJumpInitialBoundaryFlowObservationTest_le_one hMargin time)
      _ = margin - eventTime := by simp
      _ ≤ margin := by linarith [hEventTime.1]
  · have hAfterMargin : margin < eventTime := lt_of_not_ge hBeforeMargin
    have hIntegralZero : (∫ time in eventTime..duration, test time) = 0 := by
      rw [show (∫ time in eventTime..duration, test time) =
          ∫ _time in eventTime..duration, (0 : ℝ) by
        apply intervalIntegral.integral_congr
        intro time hTime
        have hTimeIcc : time ∈ Icc eventTime duration := by
          simpa only [uIcc_of_le hEventTime.2.le] using hTime
        exact finiteStateMarkovJumpInitialBoundaryFlowObservationTest_eq_zero_of_not_mem
          hMargin (by
            simp only [mem_Ioo, not_and_or, not_lt]
            exact Or.inr (hAfterMargin.le.trans hTimeIcc.1))]
      simp
    rw [hIntegralZero]
    exact mul_nonneg hMargin.le
      (finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc margin eventTime).1

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On the explicit ordered observation, one flow-coordinate boundary probe is the sum of the
corresponding microscopic event weights times their probe-tail integrals. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_explicitFlow_eq_eventSum
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    {duration margin : ℝ} (hMargin : 0 < margin)
    (hDuration : 0 ≤ duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (edge : FiniteStateOffDiagonalEdge State) :
    finiteIntervalL1PathWeightedCoordinateIntegral
        (finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin)
        (Sum.inr edge)
        (empiricalDensityDirectionalFlowExplicitHybridBVPath
          successorIndex histories duration hOrdered).toDerivativePath.toL1Path =
      ∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
        empiricalDensityDirectionalFlowEventIncrement successorIndex
            (histories event.1) event.2 (Sum.inr edge) *
          ∫ time in (histories event.1).jumpTimes event.2..duration,
            finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time := by
  rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path]
  unfold empiricalDensityDirectionalFlowExplicitL1Path
  rw [map_add]
  unfold finiteCoordinateVectorEventStepL1PathSum
  rw [map_sum]
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_constant _ _ _ hDuration]
  simp only [empiricalDensityDirectionalFlowInitialL1Value_flow, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro event _hEvent
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_vectorRightEventStep]
  · simp
  · exact (hOrdered event.1).1 event.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every ordered empirical flow-coordinate boundary probe is controlled by the normalized total
weighted number of microscopic jumps in the same initial layer. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationTest_explicitFlow_le_weightedJumpCount
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    {duration margin : ℝ} (hDuration : 0 ≤ duration)
    (hMargin : 0 < margin) (hLayer : margin ≤ duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (edge : FiniteStateOffDiagonalEdge State) :
    finiteIntervalL1PathWeightedCoordinateIntegral
        (finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin)
        (Sum.inr edge)
        (empiricalDensityDirectionalFlowExplicitHybridBVPath
          successorIndex histories duration hOrdered).toDerivativePath.toL1Path ≤
      margin / (successorIndex + 1 : ℝ) *
        finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories := by
  rw [finiteStateMarkovJumpInitialBoundaryFlowObservationTest_explicitFlow_eq_eventSum
    successorIndex histories hMargin hDuration hOrdered edge]
  calc
    (∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
        empiricalDensityDirectionalFlowEventIncrement successorIndex
            (histories event.1) event.2 (Sum.inr edge) *
          ∫ time in (histories event.1).jumpTimes event.2..duration,
            finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time) ≤
      ∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
        margin / (successorIndex + 1 : ℝ) *
          finiteStateMarkovJumpInitialBoundaryTimeCutoff margin
            ((histories event.1).jumpTimes event.2) := by
      apply Finset.sum_le_sum
      intro event _hEvent
      have hTail :=
        (finiteStateMarkovJumpInitialBoundaryFlowObservationTest_tailIntegral_mem_Icc
          hMargin hLayer ((hOrdered event.1).1 event.2)).2
      unfold empiricalDensityDirectionalFlowEventIncrement
      by_cases hMatches :
          (histories event.1).states event.2.castSucc = edge.val.1 ∧
            (histories event.1).states event.2.succ = edge.val.2
      · simp only [hMatches]
        calc
          (1 / (successorIndex + 1 : ℝ)) *
              ∫ time in (histories event.1).jumpTimes event.2..duration,
                finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time ≤
            (1 / (successorIndex + 1 : ℝ)) *
              (margin * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin
                ((histories event.1).jumpTimes event.2)) :=
            mul_le_mul_of_nonneg_left hTail (by positivity)
          _ = margin / (successorIndex + 1 : ℝ) *
              finiteStateMarkovJumpInitialBoundaryTimeCutoff margin
                ((histories event.1).jumpTimes event.2) := by ring
      · simp only [hMatches, ite_false, zero_div, zero_mul]
        exact mul_nonneg (div_nonneg hMargin.le (by positivity))
          (finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc margin _).1
    _ = margin / (successorIndex + 1 : ℝ) *
        finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories := by
      rw [Fintype.sum_sigma]
      unfold finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro replica _hReplica
      have hWeightedCount (history : FiniteJumpHistory State) :
          finiteJumpHistoryInitialBoundaryWeightedJumpCount margin history =
            ∑ index : Fin history.jumpCount,
              finiteStateMarkovJumpInitialBoundaryTimeCutoff margin
                (history.jumpTimes index) := by
        rcases history with ⟨eventCount, states, times⟩
        rfl
      rw [hWeightedCount]
      rw [Finset.mul_sum]

/-- Continuous strong-`L1` initial-boundary probe of one cumulative directional-flow coordinate. -/
noncomputable def finiteStateMarkovJumpInitialBoundaryFlowObservationProbe
    {duration margin : ℝ} (hMargin : 0 < margin)
    (edge : FiniteStateOffDiagonalEdge State)
    (path : FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) : ℝ :=
  finiteIntervalL1PathWeightedCoordinateIntegral
    (finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin)
    (Sum.inr edge) path.toDerivativePath.toL1Path

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every initial-boundary flow probe is continuous in the published hybrid topology. -/
theorem continuous_finiteStateMarkovJumpInitialBoundaryFlowObservationProbe
    {duration margin : ℝ} (hMargin : 0 < margin)
    (edge : FiniteStateOffDiagonalEdge State) :
    Continuous (finiteStateMarkovJumpInitialBoundaryFlowObservationProbe
      (State := State) (duration := duration) hMargin edge) :=
  (continuous_finiteIntervalL1PathWeightedCoordinateIntegral
    (finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin)
    (Sum.inr edge)).comp FiniteIntervalHybridBVPath.continuous_toL1Path

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A path with a strictly positive recovered initial flow has a continuous boundary probe whose
value is uniformly positive after normalization by a sufficiently small boundary margin. -/
theorem
    exists_initialBoundaryFlowObservationProbe_gt_margin_mul_of_initialTrace_flow_pos
    {duration : ℝ} (hDuration : 0 < duration)
    (path : FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)
    (edge : FiniteStateOffDiagonalEdge State)
    {upperMargin : ℝ} (hUpperMargin : 0 < upperMargin)
    (hInitialFlow : 0 < path.initialTrace (Sum.inr edge)) :
    ∃ margin : ℝ, ∃ hMargin : 0 < margin, margin ≤ upperMargin ∧
      2 * margin ≤ duration ∧
      margin * (path.initialTrace (Sum.inr edge) / 12) <
        finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path := by
  let coordinate : EmpiricalDensityDirectionalFlowCoordinate State := Sum.inr edge
  let initialFlow : ℝ := path.initialTrace coordinate
  let representative := path.cadlagRepresentative.representative
  have hCoordinateTendsto :
      Tendsto (fun time => representative time coordinate) (𝓝[Ici 0] 0)
        (𝓝 initialFlow) := by
    have hProjection :=
      (PiLp.proj (𝕜 := ℝ) (p := 1)
        (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ) coordinate).continuous
        |>.continuousAt.tendsto.comp (path.tendsto_initialTrace hDuration)
    simpa only [PiLp.proj_apply] using! hProjection
  have hHalfFlow : initialFlow / 2 < initialFlow := by
    dsimp only [initialFlow, coordinate]
    linarith
  have hNearInitial :
      {time | initialFlow / 2 < representative time coordinate} ∈ 𝓝[Ici 0] 0 :=
    hCoordinateTendsto (Ioi_mem_nhds hHalfFlow)
  obtain ⟨radius, hRadius, hRadiusControl⟩ :=
    Metric.mem_nhdsWithin_iff.mp hNearInitial
  let margin := min (min (radius / 2) (duration / 2)) upperMargin
  have hMargin : 0 < margin := by
    exact lt_min (lt_min (half_pos hRadius) (half_pos hDuration)) hUpperMargin
  have hMarginUpper : margin ≤ upperMargin := min_le_right _ _
  have hLayer : 2 * margin ≤ duration := by
    dsimp only [margin]
    linarith [min_le_left (min (radius / 2) (duration / 2)) upperMargin,
      min_le_right (radius / 2) (duration / 2)]
  have hRepresentativeLower (time : ℝ) (hTime : time ∈ Ioo 0 margin) :
      initialFlow / 2 < representative time coordinate := by
    apply hRadiusControl
    constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      have hTimeRadius : time < radius := by
        dsimp only [margin] at hTime
        exact (hTime.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))).trans
          (half_lt_self hRadius)
      simpa [abs_of_nonneg hTime.1.le] using hTimeRadius
    · exact hTime.1.le
  let physicalVolume := finiteOpenIntervalVolume duration
  obtain ⟨hRepresentativeMemLp, hRepresentativeToLp⟩ :=
    path.cadlagRepresentative.represents
  have hRepresentativeAE :
      (fun time => path.toDerivativePath.toL1Path time coordinate) =ᵐ[physicalVolume]
        (fun time => representative time coordinate) := by
    have hVectorAE := MemLp.coeFn_toLp hRepresentativeMemLp
    rw [hRepresentativeToLp] at hVectorAE
    exact hVectorAE.mono fun time hTime => congrArg (fun value => value coordinate) hTime
  let test := finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin
  have hTestBound : ∀ᵐ time ∂physicalVolume, ‖test time‖ ≤ 1 :=
    Filter.Eventually.of_forall fun time => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (finiteStateMarkovJumpInitialBoundaryFlowObservationTest_nonnegative hMargin time)]
      exact finiteStateMarkovJumpInitialBoundaryFlowObservationTest_le_one hMargin time
  have hRepresentativeIntegrable : Integrable representative physicalVolume :=
    memLp_one_iff_integrable.mp hRepresentativeMemLp
  have hCoordinateIntegrable : Integrable (fun time => representative time coordinate)
      physicalVolume :=
    ContinuousLinearMap.integrable_comp
      (PiLp.proj (𝕜 := ℝ) (p := 1)
        (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ) coordinate)
      hRepresentativeIntegrable
  have hTestAEMeasurable : AEStronglyMeasurable test physicalVolume :=
    test.continuous.aestronglyMeasurable
  have hProductIntegrable : Integrable
      (fun time => test time * representative time coordinate) physicalVolume :=
    hCoordinateIntegrable.bdd_mul hTestAEMeasurable hTestBound
  have hTestIntegrable : Integrable test physicalVolume :=
    (test.continuous.memLp_top_of_hasCompactSupport test.hasCompactSupport
      physicalVolume).integrable (by simp)
  have hLowerIntegrable : Integrable (fun time => initialFlow / 2 * test time)
      physicalVolume := hTestIntegrable.const_mul _
  have hPointwiseLower :
      ∀ᵐ time ∂physicalVolume,
        initialFlow / 2 * test time ≤ test time * representative time coordinate := by
    apply Filter.Eventually.of_forall
    intro time
    by_cases hTime : time ∈ Ioo 0 margin
    · have hTestNonnegative :=
        finiteStateMarkovJumpInitialBoundaryFlowObservationTest_nonnegative hMargin time
      nlinarith [hRepresentativeLower time hTime]
    · have hTestZero :=
        finiteStateMarkovJumpInitialBoundaryFlowObservationTest_eq_zero_of_not_mem
          hMargin hTime
      simp [test, hTestZero]
  have hIntegralLower :
      initialFlow / 2 * (margin / 3) ≤
        finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path := by
    rw [finiteStateMarkovJumpInitialBoundaryFlowObservationProbe,
      finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral]
    calc
      initialFlow / 2 * (margin / 3) ≤
          initialFlow / 2 * ∫ time, test time ∂physicalVolume := by
        exact mul_le_mul_of_nonneg_left
          (finiteStateMarkovJumpInitialBoundaryFlowObservationTest_integral_ge_margin_div_three
            hDuration.le hMargin (by linarith))
          (by dsimp only [initialFlow, coordinate]; linarith)
      _ = ∫ time, initialFlow / 2 * test time ∂physicalVolume := by
        rw [integral_const_mul]
      _ ≤ ∫ time, test time * representative time coordinate ∂physicalVolume :=
        integral_mono_ae hLowerIntegrable hProductIntegrable hPointwiseLower
      _ = ∫ time,
          finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin time *
            path.toDerivativePath.toL1Path time (Sum.inr edge)
          ∂finiteOpenIntervalVolume duration := by
        apply integral_congr_ae
        exact hRepresentativeAE.symm.mono fun time hTime => by
          change test time * representative time coordinate =
            test time * path.toDerivativePath.toL1Path time coordinate
          exact congrArg (fun value => test time * value) hTime
  refine ⟨margin, hMargin, hMarginUpper, hLayer, ?_⟩
  apply lt_of_lt_of_le _ hIntegralLower
  dsimp only [initialFlow, coordinate]
  nlinarith

omit [MeasurableSingletonClass State] in
/-- On ordered histories, the totalized observation's boundary probe obeys the same normalized
weighted-jump bound as the explicit ordered observation. -/
theorem finiteStateMarkovJumpInitialBoundaryFlowObservationProbe_totalObservation_le
    [TopologicalSpace State] [_unusedDiscreteTopology : DiscreteTopology State]
    [_unusedBorelSpace : BorelSpace State] [Nonempty State]
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    {duration margin : ℝ} (hDuration : 0 ≤ duration)
    (hMargin : 0 < margin) (hLayer : margin ≤ duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (edge : FiniteStateOffDiagonalEdge State) :
    finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge
        (empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration histories) ≤
      margin / (successorIndex + 1 : ℝ) *
        finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories := by
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  change finiteIntervalL1PathWeightedCoordinateIntegral
      (finiteStateMarkovJumpInitialBoundaryFlowObservationTest margin hMargin)
      (Sum.inr edge)
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered).toDerivativePath.toL1Path ≤ _
  exact
    finiteStateMarkovJumpInitialBoundaryFlowObservationTest_explicitFlow_le_weightedJumpCount
      successorIndex histories hDuration hMargin hLayer hOrdered edge

/-- A positive boundary-probe deviation has a particle-speed exponential tail under every
deterministic initial configuration. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVBoundaryFlowProbe_gt_le
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ} (hDuration : 0 < duration)
    (hMargin : 0 < margin) (hLayer : 2 * margin ≤ duration)
    (hScale : 0 < scale) (edge : FiniteStateOffDiagonalEdge State)
    (threshold : ℝ) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration.le
        {path | threshold <
          finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path} ≤
      ENNReal.ofReal (Real.exp
        ((successorIndex + 1 : ℝ) *
            (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1)) -
          scale * (threshold / (margin / (successorIndex + 1 : ℝ))))) := by
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw]
  rw [Measure.map_apply
    (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
      successorIndex duration)
    (measurableSet_lt measurable_const
      (continuous_finiteStateMarkovJumpInitialBoundaryFlowObservationProbe
        hMargin edge).measurable)]
  calc
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration.le).toMeasure
        (empiricalDensityDirectionalFlowTotalHybridBVObservation successorIndex duration ⁻¹'
          {path | threshold <
            finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path}) ≤
      (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration.le).toMeasure
        {histories |
          threshold / (margin / (successorIndex + 1 : ℝ)) <
            finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories} := by
      apply measure_mono_ae
      filter_upwards [
        ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration.le] with histories hOrdered
      intro hProbe
      have hProbeUpper :=
        finiteStateMarkovJumpInitialBoundaryFlowObservationProbe_totalObservation_le
          successorIndex histories hDuration.le hMargin (by linarith) hOrdered edge
      have hDeviation :
          threshold < margin / (successorIndex + 1 : ℝ) *
            finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories :=
        hProbe.trans_le hProbeUpper
      exact (div_lt_iff₀ (div_pos hMargin (by positivity))).mpr
        (by simpa only [mul_comm] using hDeviation)
    _ ≤ ENNReal.ofReal (Real.exp
        ((successorIndex + 1 : ℝ) *
            (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1)) -
          scale * (threshold / (margin / (successorIndex + 1 : ℝ))))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (finiteStateMarkovJumpDeterministicInitialReplicaInitialBoundaryWeightedJumpCount_gt_le
          initialConfiguration generator hDuration.le hMargin hLayer hScale
            (threshold / (margin / (successorIndex + 1 : ℝ))))

/-- Scale-normalized form of the boundary-probe tail: a threshold proportional to the boundary
margin forces a replica fraction independent of that margin. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVBoundaryFlowProbe_gt_margin_mul_le
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ} (hDuration : 0 < duration)
    (hMargin : 0 < margin) (hLayer : 2 * margin ≤ duration)
    (hScale : 0 < scale) (edge : FiniteStateOffDiagonalEdge State)
    (thresholdCoefficient : ℝ) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration.le
        {path | margin * thresholdCoefficient <
          finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path} ≤
      ENNReal.ofReal (Real.exp
        ((successorIndex + 1 : ℝ) *
          (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1) -
            scale * thresholdCoefficient))) := by
  convert finiteStateMarkovJumpDeterministicInitialHybridBVBoundaryFlowProbe_gt_le
    successorIndex initialConfiguration generator hDuration hMargin hLayer hScale edge
      (margin * thresholdCoefficient) using 1
  congr 2
  have hParticleCount : (0 : ℝ) < successorIndex + 1 := by positivity
  field_simp

/-- Every path with positive recovered initial cumulative flow has an open neighborhood whose
probability is bounded at any prescribed particle-speed exponential level, uniformly over all
deterministic initial configurations. -/
theorem
    exists_open_initialBoundaryFlowNeighborhood_probability_le_of_initialTrace_flow_pos
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 < duration)
    (targetPath : FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)
    (edge : FiniteStateOffDiagonalEdge State)
    (hInitialFlow : 0 < targetPath.initialTrace (Sum.inr edge))
    (level : ℝ) (hLevel : 0 ≤ level) :
    ∃ neighborhood : Set (FiniteIntervalHybridBVPath
        (EmpiricalDensityDirectionalFlowCoordinate State) duration),
      IsOpen neighborhood ∧ targetPath ∈ neighborhood ∧
        ∀ (successorIndex : ℕ)
          (initialConfiguration : Fin (successorIndex + 1) → State),
          finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
              successorIndex initialConfiguration generator duration hDuration.le neighborhood ≤
            ENNReal.ofReal
              (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  let thresholdCoefficient : ℝ :=
    targetPath.initialTrace (Sum.inr edge) / 12
  have hThresholdCoefficient : 0 < thresholdCoefficient := by
    dsimp only [thresholdCoefficient]
    positivity
  let scale : ℝ := 2 * (level + 1) / thresholdCoefficient
  have hScale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hScaleThreshold : scale * thresholdCoefficient = 2 * (level + 1) := by
    dsimp only [scale]
    field_simp
  let escapeCoefficient : ℝ :=
    2 * (finiteStateTotalEscapeBound generator : ℝ) * (Real.exp scale - 1)
  have hEscapeCoefficient : 0 ≤ escapeCoefficient := by
    dsimp only [escapeCoefficient]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (sub_nonneg.mpr (Real.one_le_exp hScale.le))
  let slack : ℝ := scale * thresholdCoefficient - level
  have hSlack : 0 < slack := by
    dsimp only [slack]
    rw [hScaleThreshold]
    linarith
  let upperMargin : ℝ := slack / (2 * (escapeCoefficient + 1))
  have hUpperMargin : 0 < upperMargin := by
    dsimp only [upperMargin]
    positivity
  obtain ⟨margin, hMargin, hMarginUpper, hLayer, hTargetProbe⟩ :=
    exists_initialBoundaryFlowObservationProbe_gt_margin_mul_of_initialTrace_flow_pos
      hDuration targetPath edge hUpperMargin hInitialFlow
  let neighborhood : Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
    {path | margin * thresholdCoefficient <
      finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge path}
  have hNeighborhoodOpen : IsOpen neighborhood := by
    exact isOpen_lt continuous_const
      (continuous_finiteStateMarkovJumpInitialBoundaryFlowObservationProbe hMargin edge)
  have hTargetNeighborhood : targetPath ∈ neighborhood := by
    simpa only [neighborhood, Set.mem_ofPred_eq, thresholdCoefficient] using hTargetProbe
  refine ⟨neighborhood, hNeighborhoodOpen, hTargetNeighborhood, ?_⟩
  intro successorIndex initialConfiguration
  have hTail :=
    finiteStateMarkovJumpDeterministicInitialHybridBVBoundaryFlowProbe_gt_margin_mul_le
      successorIndex initialConfiguration generator hDuration hMargin hLayer hScale edge
        thresholdCoefficient
  have hUpperMarginIdentity :
      2 * (escapeCoefficient + 1) * upperMargin = slack := by
    dsimp only [upperMargin]
    field_simp
  have hEscapeStrict : margin * escapeCoefficient < slack := by
    have hMarginEscape :
        margin * escapeCoefficient ≤ upperMargin * escapeCoefficient :=
      mul_le_mul_of_nonneg_right hMarginUpper hEscapeCoefficient
    have hCoefficientOrder :
        escapeCoefficient < 2 * (escapeCoefficient + 1) := by
      linarith
    have hUpperEscape :
        upperMargin * escapeCoefficient <
          upperMargin * (2 * (escapeCoefficient + 1)) :=
      mul_lt_mul_of_pos_left hCoefficientOrder hUpperMargin
    have hUpperSlack :
        upperMargin * (2 * (escapeCoefficient + 1)) = slack := by
      calc
        upperMargin * (2 * (escapeCoefficient + 1)) =
            2 * (escapeCoefficient + 1) * upperMargin := by ring
        _ = slack := hUpperMarginIdentity
    exact hMarginEscape.trans_lt (hUpperEscape.trans_eq hUpperSlack)
  have hExponent :
      (successorIndex + 1 : ℝ) *
          (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1) -
            scale * thresholdCoefficient) ≤
        -(successorIndex + 1 : ℝ) * level := by
    have hInside :
        2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1) -
            scale * thresholdCoefficient ≤ -level := by
      dsimp only [escapeCoefficient] at hEscapeStrict
      dsimp only [slack] at hEscapeStrict
      linarith
    nlinarith [show (0 : ℝ) < successorIndex + 1 by positivity]
  exact hTail.trans <| ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr hExponent

end

end FiniteMarkovProcesses.Probability
