/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialExponentialTilt

/-!
# Initial-boundary exponential bounds for finite-state jump histories

This module constructs a microscopic time-dependent tilt that remains fully active at time zero,
then vanishes after a prescribed initial boundary layer.  It is intentionally not a relative
`C₀((0,T))` macroscopic dual test: its purpose is to control the source events that the published
boundary-blind derivative topology cannot detect.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal

universe u

noncomputable section

private theorem sum_intervalIntegral_adjacent_fin
    {eventCount : ℕ} (integrand : ℝ → ℝ)
    (hIntegrable : ∀ lower upper,
      IntervalIntegrable integrand volume lower upper)
    (boundaries : Fin (eventCount + 2) → ℝ) :
    (∑ block : Fin (eventCount + 1),
      ∫ time in boundaries block.castSucc..boundaries block.succ,
        integrand time) =
      ∫ time in boundaries 0..boundaries (Fin.last (eventCount + 1)),
        integrand time := by
  induction eventCount with
  | zero =>
      rw [Fin.sum_univ_succ]
      simp
  | succ eventCount inductionHypothesis =>
      rw [Fin.sum_univ_castSucc]
      have hPrefix := inductionHypothesis
        (fun boundary : Fin (eventCount + 2) => boundaries boundary.castSucc)
      simp_rw [← Fin.castSucc_succ]
      rw [hPrefix]
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · simp [Fin.succ_last]
      · exact hIntegrable _ _
      · exact hIntegrable _ _

/-- Continuous cutoff equal to one through `margin` and zero from `2 * margin` onward. -/
noncomputable def finiteStateMarkovJumpInitialBoundaryTimeCutoff
    (margin time : ℝ) : ℝ :=
  max 0 (min 1 ((2 * margin - time) / margin))

/-- The initial-boundary time cutoff is continuous. -/
theorem continuous_finiteStateMarkovJumpInitialBoundaryTimeCutoff
    (margin : ℝ) :
    Continuous (finiteStateMarkovJumpInitialBoundaryTimeCutoff margin) := by
  unfold finiteStateMarkovJumpInitialBoundaryTimeCutoff
  fun_prop

/-- A positive-margin initial-boundary cutoff takes values in the unit interval. -/
theorem finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc
    (margin time : ℝ) :
    finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time ∈ Icc 0 1 := by
  unfold finiteStateMarkovJumpInitialBoundaryTimeCutoff
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

/-- The initial-boundary cutoff is exactly one at every time not exceeding its margin. -/
theorem finiteStateMarkovJumpInitialBoundaryTimeCutoff_eq_one
    {margin time : ℝ} (hMargin : 0 < margin) (hTime : time ≤ margin) :
    finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time = 1 := by
  have hRatio : 1 ≤ (2 * margin - time) / margin := by
    rw [le_div_iff₀ hMargin]
    linarith
  unfold finiteStateMarkovJumpInitialBoundaryTimeCutoff
  rw [min_eq_left hRatio, max_eq_right zero_le_one]

/-- The initial-boundary cutoff vanishes from twice its margin onward. -/
theorem finiteStateMarkovJumpInitialBoundaryTimeCutoff_eq_zero
    {margin time : ℝ} (hMargin : 0 < margin) (hTime : 2 * margin ≤ time) :
    finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time = 0 := by
  have hRatio : (2 * margin - time) / margin ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hTime) hMargin.le
  unfold finiteStateMarkovJumpInitialBoundaryTimeCutoff
  rw [max_eq_left (min_le_of_right_le hRatio)]

/-- Uniform transition exponent that counts jumps in the initial boundary layer and vanishes
after twice the supplied margin. -/
noncomputable def finiteStateMarkovJumpInitialBoundaryTransitionExponent
    {State : Type u} (margin scale : ℝ) (hScale : 0 ≤ scale) :
    FiniteStateTransitionExponent State where
  exponent := fun time _source _target =>
    scale * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time
  measurable_exponent := fun _source _target =>
    (continuous_const.mul
      (continuous_finiteStateMarkovJumpInitialBoundaryTimeCutoff margin)).measurable
  upperBound := scale
  exponent_le_upperBound := fun time _source _target => by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc margin time).2 hScale

/-- The initial-boundary transition exponent is continuous in time. -/
theorem continuous_finiteStateMarkovJumpInitialBoundaryTransitionExponent
    {State : Type u} (margin scale : ℝ) (hScale : 0 ≤ scale)
    (source target : State) :
    Continuous fun time =>
      (finiteStateMarkovJumpInitialBoundaryTransitionExponent
        margin scale hScale).exponent time source target := by
  unfold finiteStateMarkovJumpInitialBoundaryTransitionExponent
  exact continuous_const.mul
    (continuous_finiteStateMarkovJumpInitialBoundaryTimeCutoff margin)

/-- Sum of the initial-boundary cutoff over all retained physical jumps in one history. -/
noncomputable def finiteJumpHistoryInitialBoundaryWeightedJumpCount
    {State : Type u} (margin : ℝ) : FiniteJumpHistory State → ℝ
  | ⟨_, _states, times⟩ =>
      ∑ index, finiteStateMarkovJumpInitialBoundaryTimeCutoff margin (times index)

/-- The time-dependent jump-score sector of the initial-boundary tilt is exactly scale times the
weighted initial-boundary jump count. -/
theorem finiteStateMarkovInitialBoundaryTiltJumpScore_eq
    {State : Type u} [_unusedFintype : Fintype State] [_unusedDecidableEq : DecidableEq State]
    (margin scale : ℝ) (hScale : 0 ≤ scale)
    (history : FiniteJumpHistory State) :
    finiteStateMarkovExponentialTimeTiltJumpScore
        (finiteStateMarkovJumpInitialBoundaryTransitionExponent
          margin scale hScale)
        history.states history.jumpTimes =
      scale * finiteJumpHistoryInitialBoundaryWeightedJumpCount margin history := by
  rcases history with ⟨eventCount, states, times⟩
  unfold finiteStateMarkovExponentialTimeTiltJumpScore
    finiteStateMarkovJumpInitialBoundaryTransitionExponent
    finiteJumpHistoryInitialBoundaryWeightedJumpCount
  change (∑ index : Fin eventCount,
      scale * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin (times index)) = _
  rw [Finset.mul_sum]

/-- Because the boundary tilt is uniform across directed targets, its escape-row difference is
the original escape rate times one scalar exponential factor. -/
theorem finiteStateMarkovInitialBoundaryTiltEscapeDifference_eq
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (margin scale : ℝ) (hScale : 0 ≤ scale) (time : ℝ) (state : State) :
    finiteStateMarkovExponentialTimeTiltEscapeDifference generator
        (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
        time state =
      (generator.escapeRate state : ℝ) *
        (Real.exp
          (scale * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time) - 1) := by
  rw [finiteStateMarkovExponentialTimeTiltEscapeDifference_eq_sum]
  unfold finiteStateMarkovJumpInitialBoundaryTransitionExponent
  change (∑ target ∈ Finset.univ.erase state,
      (generator.rate state target : ℝ) *
        (Real.exp
          (scale * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time) - 1)) = _
  rw [← Finset.sum_mul]
  congr 1
  norm_cast
  unfold FiniteStateMarkovGenerator.escapeRate
  rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self state)]

/-- The initial-boundary escape correction is pointwise bounded by a constant supported on the
initial layer through `2 * margin`. -/
theorem finiteStateMarkovInitialBoundaryTiltEscapeDifference_le_indicator
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    {margin scale : ℝ} (hMargin : 0 < margin) (hScale : 0 ≤ scale)
    (time : ℝ) (state : State) :
    finiteStateMarkovExponentialTimeTiltEscapeDifference generator
        (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
        time state ≤
      (Iic (2 * margin)).indicator (fun _ =>
        (finiteStateTotalEscapeBound generator : ℝ) *
          (Real.exp scale - 1)) time := by
  rw [finiteStateMarkovInitialBoundaryTiltEscapeDifference_eq]
  by_cases hTime : time ≤ 2 * margin
  · rw [Set.indicator_of_mem (s := Iic (2 * margin)) (a := time)
      (hTime : time ∈ Iic (2 * margin))]
    have hCutoff :=
      (finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc margin time).2
    have hCutoffNonnegative :=
      (finiteStateMarkovJumpInitialBoundaryTimeCutoff_mem_Icc margin time).1
    have hExponent :
        scale * finiteStateMarkovJumpInitialBoundaryTimeCutoff margin time ≤ scale := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hCutoff hScale
    exact mul_le_mul
      (by exact_mod_cast escapeRate_le_finiteStateTotalEscapeBound generator state)
      (sub_le_sub_right (Real.exp_le_exp.mpr hExponent) 1)
      (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hScale hCutoffNonnegative)))
      (by positivity)
  · rw [Set.indicator_of_notMem (s := Iic (2 * margin)) (a := time)
      (hTime : time ∉ Iic (2 * margin))]
    rw [finiteStateMarkovJumpInitialBoundaryTimeCutoff_eq_zero
      hMargin (le_of_not_ge hTime)]
    simp

/-- On every physical history, the complete escape correction of the initial-boundary tilt is
bounded by the length of its support times the uniform total escape bound. -/
theorem finiteStateMarkovInitialBoundaryTiltEscapeCorrection_le
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ}
    (hDuration : 0 ≤ duration) (hMargin : 0 < margin)
    (hLayer : 2 * margin ≤ duration) (hScale : 0 ≤ scale)
    (history : FiniteJumpHistory State) (hOrdered : history.OrderedBefore duration) :
    finiteStateMarkovExponentialTimeTiltEscapeCorrection generator
        (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
        duration history.states history.jumpTimes ≤
      2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
        (Real.exp scale - 1) := by
  rcases history with ⟨eventCount, states, times⟩
  let escapeBound : ℝ :=
    (finiteStateTotalEscapeBound generator : ℝ) * (Real.exp scale - 1)
  let supportedEscapeBound : ℝ → ℝ :=
    (Iic (2 * margin)).indicator (fun _ => escapeBound)
  have hSupportedEscapeBoundIntegrable (lower upper : ℝ) :
      IntervalIntegrable supportedEscapeBound volume lower upper := by
    rcases le_total lower upper with hLowerUpper | hUpperLower
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hLowerUpper]
      exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
        ((measurable_const.indicator measurableSet_Iic).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun time => by
          change ‖supportedEscapeBound time‖ ≤ |escapeBound|
          by_cases hTime : time ∈ Iic (2 * margin)
          · simp [supportedEscapeBound, hTime]
          · simp [supportedEscapeBound, hTime])
    · exact (IntervalIntegrable.symm <| by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hUpperLower]
        exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
          ((measurable_const.indicator measurableSet_Iic).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun time => by
            change ‖supportedEscapeBound time‖ ≤ |escapeBound|
            by_cases hTime : time ∈ Iic (2 * margin)
            · simp [supportedEscapeBound, hTime]
            · simp [supportedEscapeBound, hTime]))
  rw [finiteStateMarkovExponentialTimeTiltEscapeCorrection_eq_sum_integral
    generator _ (continuous_finiteStateMarkovJumpInitialBoundaryTransitionExponent
      margin scale hScale)]
  calc
    (∑ block : Fin (eventCount + 1),
        ∫ time in
          (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
          (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
            finiteStateMarkovExponentialTimeTiltEscapeDifference generator
              (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
              time (states block)) ≤
        ∑ block : Fin (eventCount + 1),
          ∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
              supportedEscapeBound time := by
      apply Finset.sum_le_sum
      intro block _hBlock
      apply intervalIntegral.integral_mono_on
      · exact (FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
          hDuration hOrdered) (Fin.castSucc_le_succ block)
      · exact (continuous_finiteStateMarkovExponentialTimeTiltEscapeDifference generator _
          (continuous_finiteStateMarkovJumpInitialBoundaryTransitionExponent
            margin scale hScale) (states block)).intervalIntegrable _ _
      · exact hSupportedEscapeBoundIntegrable _ _
      · intro time _hTime
        exact finiteStateMarkovInitialBoundaryTiltEscapeDifference_le_indicator
          generator hMargin hScale time (states block)
    _ = ∫ time in 0..duration, supportedEscapeBound time := by
      rw [sum_intervalIntegral_adjacent_fin supportedEscapeBound
        hSupportedEscapeBoundIntegrable]
      simp
    _ = 2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
        (Real.exp scale - 1) := by
      unfold supportedEscapeBound
      have hIndicator :
          (∫ time in 0..duration,
              (Iic (2 * margin)).indicator (fun _ => escapeBound) time) =
            ∫ time in 0..(2 * margin), escapeBound := by
        simpa only [Iic] using
          (intervalIntegral.integral_indicator
            (f := fun _ : ℝ => escapeBound) (μ := volume)
            (⟨by linarith, hLayer⟩ : 2 * margin ∈ Icc 0 duration))
      rw [hIndicator]
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, sub_zero]
      change 2 * margin * escapeBound = _
      unfold escapeBound
      ring

/-- The complete initial-boundary tilt score dominates its weighted jump reward minus the
uniform escape budget for the boundary layer. -/
theorem finiteStateMarkovInitialBoundaryWeightedJumpScoreLowerBound
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ}
    (hDuration : 0 ≤ duration) (hMargin : 0 < margin)
    (hLayer : 2 * margin ≤ duration) (hScale : 0 ≤ scale)
    (history : FiniteJumpHistory State) (hOrdered : history.OrderedBefore duration) :
    scale * finiteJumpHistoryInitialBoundaryWeightedJumpCount margin history -
        2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
          (Real.exp scale - 1) ≤
      finiteStateMarkovExponentialTimeTiltHistoryScore generator
        (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
        duration history := by
  rcases history with ⟨eventCount, states, times⟩
  simp only [finiteStateMarkovExponentialTimeTiltHistoryScore,
    finiteStateMarkovExponentialTimeTiltSliceScore,
    finiteJumpHistoryInitialBoundaryWeightedJumpCount]
  unfold finiteStateMarkovExponentialTimeTiltJumpScore
    finiteStateMarkovJumpInitialBoundaryTransitionExponent
  rw [Finset.mul_sum]
  exact sub_le_sub_left
    (finiteStateMarkovInitialBoundaryTiltEscapeCorrection_le generator
      hDuration hMargin hLayer hScale ⟨eventCount, states, times⟩ hOrdered) _

end

end FiniteMarkovProcesses.Probability
