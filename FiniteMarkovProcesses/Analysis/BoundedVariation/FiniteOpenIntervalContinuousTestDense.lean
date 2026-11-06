/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Density of finite-open-interval continuous tests

This module proves the `L1` density statement required by open-interval variational formulas.
For a finite Borel measure concentrated on `(0, T)`, every integrable real function can be
approximated by a compactly supported continuous real-line function that vanishes identically
outside `(0, T)`.  The proof first uses the standard compact-support density theorem and then
applies the canonical shrinking boundary cutoff.

## Main results

* `tendsto_finiteOpenIntervalCoreCutoff_div_nat` proves pointwise convergence of the canonical
  interior cutoffs to one at every physical time.
* `FiniteOpenIntervalVanishingContinuousTest.symmetricClamp` preserves the relative test family
  while bounding its range.
* `MeasureTheory.Integrable.exists_finiteOpenIntervalVanishingContinuousTest_integral_norm_sub_lt`
  gives the relative-test `L1` approximation theorem.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

noncomputable section

/-- The canonical shrinking interior cutoff converges to one at every point of the open physical
interval. -/
theorem tendsto_finiteOpenIntervalCoreCutoff_div_nat
    {duration time : ℝ} (hDuration : 0 < duration)
    (hTime : time ∈ Set.Ioo 0 duration) :
    Tendsto (fun index : ℕ =>
      finiteOpenIntervalCoreCutoff duration
        (duration / (index + 3 : ℕ)) (by positivity) time)
      atTop (nhds 1) := by
  have hMarginTendsto : Tendsto
      (fun index : ℕ => duration / (index + 3 : ℕ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp
      (Filter.tendsto_add_atTop_nat 3)
  have hGapPositive : 0 < min time (duration - time) := by
    exact lt_min hTime.1 (sub_pos.mpr hTime.2)
  have hMarginEventually : ∀ᶠ index : ℕ in atTop,
      duration / (index + 3 : ℕ) < min time (duration - time) :=
    (tendsto_order.1 hMarginTendsto).2 _ hGapPositive
  apply tendsto_const_nhds.congr'
  filter_upwards [hMarginEventually] with index hMargin
  symm
  apply finiteOpenIntervalCoreCutoff_eq_one_of_mem_core
  exact ⟨le_of_lt (hMargin.trans_le (min_le_left _ _)), by
    have hRight := hMargin.trans_le (min_le_right time (duration - time))
    linarith⟩

/-- Continuous projection of the real line onto the symmetric closed interval `[-bound, bound]`.
-/
noncomputable def symmetricClosedIntervalClampContinuousMap (bound : ℝ) : C(ℝ, ℝ) where
  toFun value := max (-bound) (min bound value)
  continuous_toFun := by fun_prop

/-- Pointwise formula for the symmetric closed-interval clamp. -/
@[simp]
theorem symmetricClosedIntervalClampContinuousMap_apply (bound value : ℝ) :
    symmetricClosedIntervalClampContinuousMap bound value =
      max (-bound) (min bound value) :=
  rfl

namespace FiniteOpenIntervalVanishingContinuousTest

/-- Clamp a relative continuous test into `[-bound, bound]`.  Nonnegative bounds make the clamp
fix zero, so compact support and exact vanishing off the physical interval are preserved. -/
noncomputable def symmetricClamp
    {duration : ℝ} (bound : ℝ) (hBound : 0 ≤ bound)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    FiniteOpenIntervalVanishingContinuousTest duration :=
  ⟨test.1.compLeft (symmetricClosedIntervalClampContinuousMap bound), by
    intro time hTime
    rw [CompactlySupportedContinuousMap.compLeft_apply
      (by simp [symmetricClosedIntervalClampContinuousMap, hBound]) test.1 time,
      test.property hTime]
    simp [symmetricClosedIntervalClampContinuousMap, hBound]⟩

/-- The clamped test evaluates by projection onto the symmetric closed interval. -/
@[simp]
theorem symmetricClamp_apply
    {duration : ℝ} (bound : ℝ) (hBound : 0 ≤ bound)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) (time : ℝ) :
    (symmetricClamp bound hBound test).1 time =
      max (-bound) (min bound (test.1 time)) := by
  exact CompactlySupportedContinuousMap.compLeft_apply
    (by simp [symmetricClosedIntervalClampContinuousMap, hBound]) test.1 time

/-- Every clamped test value lies in its symmetric closed interval. -/
theorem symmetricClamp_mem_Icc
    {duration : ℝ} (bound : ℝ) (hBound : 0 ≤ bound)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) (time : ℝ) :
    (symmetricClamp bound hBound test).1 time ∈ Set.Icc (-bound) bound := by
  rw [symmetricClamp_apply]
  exact ⟨le_max_left _ _, max_le (neg_le_self hBound) (min_le_left _ _)⟩

/-- Projection into a symmetric interval cannot increase distance from a target already in that
interval. -/
theorem abs_sub_symmetricClamp_le
    {duration bound target : ℝ} (hBound : 0 ≤ bound)
    (hTarget : target ∈ Set.Icc (-bound) bound)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) (time : ℝ) :
    |target - (symmetricClamp bound hBound test).1 time| ≤
      |target - test.1 time| := by
  have hInterval : -bound ≤ bound := neg_le_self hBound
  have hProjection := Set.abs_projIcc_sub_projIcc
    (c := target) (d := test.1 time) hInterval
  rw [Set.projIcc_val hInterval ⟨target, hTarget⟩,
    Set.coe_projIcc] at hProjection
  simpa only [symmetricClamp_apply, Subtype.coe_eta] using hProjection

end FiniteOpenIntervalVanishingContinuousTest

namespace MeasureTheory.Integrable

/-- Every integrable real function under a finite measure concentrated on the open physical
interval admits arbitrarily accurate `L1` approximation by a zero-extended `C₀((0,T))` test. -/
theorem exists_finiteOpenIntervalVanishingContinuousTest_integral_norm_sub_lt
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ} [IsFiniteMeasure measure]
    {function : ℝ → ℝ} (hFunction : Integrable function measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      ∫ time, |function time - test.1 time| ∂measure < epsilon := by
  obtain ⟨approximationFunction, hApproximationCompact, hApproximationError,
      hApproximationContinuous, hApproximationIntegrable⟩ :=
    hFunction.exists_hasCompactSupport_integral_sub_le (half_pos hEpsilon)
  let approximation : C_c(ℝ, ℝ) :=
    ⟨⟨approximationFunction, hApproximationContinuous⟩, hApproximationCompact⟩
  let margin : ℕ → ℝ := fun index => duration / (index + 3 : ℕ)
  have hMarginPositive (index : ℕ) : 0 < margin index := by
    dsimp only [margin]
    positivity
  let approximationError : ℕ → ℝ → ℝ := fun index time =>
    |approximation time - approximation time *
      finiteOpenIntervalCoreCutoff duration (margin index) (hMarginPositive index) time|
  have hApproximationErrorMeasurable (index : ℕ) :
      AEStronglyMeasurable (approximationError index) measure := by
    apply Continuous.aestronglyMeasurable
    dsimp only [approximationError]
    fun_prop
  have hApproximationErrorBound (index : ℕ) :
      ∀ᵐ time ∂measure,
        ‖approximationError index time‖ ≤ |approximation time| := by
    apply Filter.Eventually.of_forall
    intro time
    have hCutoff := finiteOpenIntervalCoreCutoff_mem_Icc
      (duration := duration) (hMarginPositive index) time
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    calc
      |approximation time - approximation time *
          finiteOpenIntervalCoreCutoff duration (margin index)
            (hMarginPositive index) time| =
          |approximation time| *
            |1 - finiteOpenIntervalCoreCutoff duration (margin index)
              (hMarginPositive index) time| := by
        rw [show approximation time - approximation time *
            finiteOpenIntervalCoreCutoff duration (margin index)
              (hMarginPositive index) time =
            approximation time *
              (1 - finiteOpenIntervalCoreCutoff duration (margin index)
                (hMarginPositive index) time) by ring, abs_mul]
      _ ≤ |approximation time| * 1 := by
        apply mul_le_mul le_rfl
        · rw [abs_of_nonneg (sub_nonneg.mpr hCutoff.2)]
          linarith [hCutoff.1]
        · exact abs_nonneg _
        · exact abs_nonneg _
      _ = |approximation time| := mul_one _
  have hApproximationBoundIntegrable :
      Integrable (fun time => |approximation time|) measure := by
    simpa only [Real.norm_eq_abs] using! hApproximationIntegrable.norm
  have hApproximationErrorTendstoAE :
      ∀ᵐ time ∂measure,
        Tendsto (fun index => approximationError index time) atTop (nhds 0) := by
    filter_upwards [hPhysical] with time hTime
    have hCutoffTendsto :=
      tendsto_finiteOpenIntervalCoreCutoff_div_nat hDuration hTime
    have hScaledTendsto : Tendsto
        (fun index : ℕ => (approximation time : ℝ) *
          finiteOpenIntervalCoreCutoff duration (duration / (index + 3 : ℕ))
            (by positivity) time)
        atTop (nhds ((approximation time : ℝ) * 1)) :=
      tendsto_const_nhds.mul hCutoffTendsto
    have hDifferenceTendsto : Tendsto
        (fun index : ℕ => (approximation time : ℝ) -
          (approximation time : ℝ) *
            finiteOpenIntervalCoreCutoff duration (duration / (index + 3 : ℕ))
              (by positivity) time)
        atTop (nhds ((approximation time : ℝ) - (approximation time : ℝ) * 1)) :=
      tendsto_const_nhds.sub hScaledTendsto
    simpa only [approximationError, margin, mul_one, sub_self, abs_zero] using
      hDifferenceTendsto.abs
  have hApproximationIntegralTendsto : Tendsto
      (fun index => ∫ time, approximationError index time ∂measure)
      atTop (nhds 0) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence
        (fun time => |approximation time|)
        hApproximationErrorMeasurable hApproximationBoundIntegrable
        hApproximationErrorBound hApproximationErrorTendstoAE
  have hApproximationIntegralEventually : ∀ᶠ index : ℕ in atTop,
      ∫ time, approximationError index time ∂measure < epsilon / 2 :=
    (tendsto_order.1 hApproximationIntegralTendsto).2 _ (half_pos hEpsilon)
  obtain ⟨index, hCutoffError⟩ := hApproximationIntegralEventually.exists
  let test : FiniteOpenIntervalVanishingContinuousTest duration :=
    finiteOpenIntervalCoreCutoffMulTest (hMarginPositive index) approximation
  refine ⟨test, ?_⟩
  have hTestIntegrable : Integrable (fun time => test.1 time) measure :=
    test.1.integrable
  have hFirstErrorIntegrable :
      Integrable (fun time => |function time - approximation time|) measure := by
    simpa only [Real.norm_eq_abs] using!
      (hFunction.sub hApproximationIntegrable).norm
  have hSecondErrorIntegrable :
      Integrable (fun time => |approximation time - test.1 time|) measure := by
    simpa only [Real.norm_eq_abs] using!
      (hApproximationIntegrable.sub hTestIntegrable).norm
  have hFirstError :
      (∫ time, |function time - approximation time| ∂measure) ≤ epsilon / 2 := by
    simpa only [approximation, Real.norm_eq_abs] using! hApproximationError
  calc
    ∫ time, |function time - test.1 time| ∂measure ≤
        ∫ time, (|function time - approximation time| +
          |approximation time - test.1 time|) ∂measure := by
      apply integral_mono
      · simpa only [Real.norm_eq_abs] using! (hFunction.sub hTestIntegrable).norm
      · exact hFirstErrorIntegrable.add hSecondErrorIntegrable
      · intro time
        exact abs_sub_le _ _ _
    _ = (∫ time, |function time - approximation time| ∂measure) +
        ∫ time, |approximation time - test.1 time| ∂measure :=
      integral_add hFirstErrorIntegrable hSecondErrorIntegrable
    _ < epsilon := by
      have hTestError :
          (∫ time, |approximation time - test.1 time| ∂measure) < epsilon / 2 := by
        simpa only [test, finiteOpenIntervalCoreCutoffMulTest, approximationError,
          margin, CompactlySupportedContinuousMap.mul_apply] using hCutoffError
      linarith [hFirstError]

/-- The indicator of a measurable event admits a relative continuous approximation clamped to
`[-1, 1]`.  The clamping preserves the approximation error because the indicator already takes
values in that interval.  This is the source-neutral approximation kernel needed to detect
singular positive measure sectors by continuous exponential tests. -/
theorem exists_finiteOpenIntervalVanishingContinuousTest_indicator_integral_abs_sub_lt
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ} [IsFiniteMeasure measure]
    {event : Set ℝ} (hEvent : MeasurableSet event)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ time, test.1 time ∈ Set.Icc (-1 : ℝ) 1) ∧
        ∫ time, |event.indicator (fun _ => (1 : ℝ)) time - test.1 time| ∂measure <
          epsilon := by
  let indicator : ℝ → ℝ := event.indicator fun _ => 1
  have hIndicatorIntegrable : Integrable indicator measure := by
    exact (integrable_const (1 : ℝ)).indicator hEvent
  obtain ⟨rawTest, hRawError⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_integral_norm_sub_lt
      hDuration hIndicatorIntegrable hPhysical hEpsilon
  let test := rawTest.symmetricClamp 1 zero_le_one
  refine ⟨test, fun time => rawTest.symmetricClamp_mem_Icc 1 zero_le_one time, ?_⟩
  have hTargetRange (time : ℝ) : indicator time ∈ Set.Icc (-1 : ℝ) 1 := by
    by_cases hTime : time ∈ event
    · simp [indicator, hTime]
    · simp [indicator, hTime]
  have hTestIntegrable : Integrable (fun time => test.1 time) measure :=
    test.1.integrable
  have hRawTestIntegrable : Integrable (fun time => rawTest.1 time) measure :=
    rawTest.1.integrable
  calc
    (∫ time, |indicator time - test.1 time| ∂measure) ≤
        ∫ time, |indicator time - rawTest.1 time| ∂measure := by
      apply integral_mono
      · simpa only [Real.norm_eq_abs] using!
          (hIndicatorIntegrable.sub hTestIntegrable).norm
      · simpa only [Real.norm_eq_abs] using!
          (hIndicatorIntegrable.sub hRawTestIntegrable).norm
      · intro time
        exact rawTest.abs_sub_symmetricClamp_le zero_le_one
          (hTargetRange time) time
    _ < epsilon := hRawError

/-- A reference-null event carrying a second finite measure admits one relative continuous test
that approximates its indicator under the carried measure while remaining small under the
reference.  This separates the two error channels needed for the singular-measure exponential
dual argument. -/
theorem exists_finiteOpenIntervalVanishingContinuousTest_singularIndicator_errors_lt
    {duration : ℝ} (hDuration : 0 < duration)
    {carried reference : Measure ℝ} [IsFiniteMeasure carried] [IsFiniteMeasure reference]
    {event : Set ℝ} (hEvent : MeasurableSet event) (hReferenceNull : reference event = 0)
    (hCarriedPhysical : ∀ᵐ time ∂carried, time ∈ Set.Ioo 0 duration)
    (hReferencePhysical : ∀ᵐ time ∂reference, time ∈ Set.Ioo 0 duration)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ time, test.1 time ∈ Set.Icc (-1 : ℝ) 1) ∧
        (∫ time,
          |event.indicator (fun _ => (1 : ℝ)) time - test.1 time| ∂carried) < epsilon ∧
        (∫ time, |test.1 time| ∂reference) < epsilon := by
  let combined := carried + reference
  have hCombinedPhysical : ∀ᵐ time ∂combined, time ∈ Set.Ioo 0 duration := by
    rw [MeasureTheory.ae_add_measure_iff]
    exact ⟨hCarriedPhysical, hReferencePhysical⟩
  obtain ⟨test, hTestRange, hCombinedError⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_indicator_integral_abs_sub_lt
      hDuration hEvent hCombinedPhysical hEpsilon
  let indicator : ℝ → ℝ := event.indicator fun _ => 1
  have hIndicatorIntegrable : Integrable indicator combined :=
    (integrable_const (1 : ℝ)).indicator hEvent
  have hTestIntegrable : Integrable (fun time => test.1 time) combined :=
    test.1.integrable
  have hErrorIntegrable : Integrable (fun time => |indicator time - test.1 time|) combined := by
    simpa only [Real.norm_eq_abs] using!
      (hIndicatorIntegrable.sub hTestIntegrable).norm
  have hCarriedLe : carried ≤ combined :=
    le_add_of_nonneg_right bot_le
  have hReferenceLe : reference ≤ combined :=
    le_add_of_nonneg_left bot_le
  have hCarriedError :
      (∫ time, |indicator time - test.1 time| ∂carried) < epsilon := by
    exact (integral_mono_measure hCarriedLe
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hErrorIntegrable).trans_lt
        hCombinedError
  have hEventuallyOutside : ∀ᵐ time ∂reference, time ∉ event := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hReferenceNull
  have hIndicatorZero : indicator =ᵐ[reference] 0 := by
    filter_upwards [hEventuallyOutside] with time hTime
    simp [indicator, hTime]
  have hReferenceError :
      (∫ time, |test.1 time| ∂reference) < epsilon := by
    have hReferenceCombinedError :
        (∫ time, |indicator time - test.1 time| ∂reference) < epsilon := by
      exact (integral_mono_measure hReferenceLe
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hErrorIntegrable).trans_lt
          hCombinedError
    rw [show (∫ time, |test.1 time| ∂reference) =
        ∫ time, |indicator time - test.1 time| ∂reference by
          apply integral_congr_ae
          filter_upwards [hIndicatorZero] with time hTime
          change indicator time = 0 at hTime
          simp only [hTime, zero_sub, abs_neg]]
    exact hReferenceCombinedError
  exact ⟨test, hTestRange, hCarriedError, hReferenceError⟩

end MeasureTheory.Integrable

end

end FiniteMarkovProcesses
