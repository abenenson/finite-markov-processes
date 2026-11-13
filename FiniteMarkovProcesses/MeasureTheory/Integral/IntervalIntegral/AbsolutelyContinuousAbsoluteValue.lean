/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
FiniteMarkovProcesses.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFundamentalTheorem
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Absolute values of absolutely continuous real functions

The absolute value of an absolutely continuous real function is absolutely continuous.  Its
classical derivative is the sign-paired derivative almost everywhere, including on the zero
fibre: points where a function vanishes with a nonzero derivative are isolated on one side and
therefore form a countable exceptional set.

These results supply a reusable Kato bridge from coordinate derivatives to endpoint `L1`
estimates.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped Topology

universe u

/-- Absolute continuity depends only on the function values on the ambient interval. -/
theorem AbsolutelyContinuousOnInterval.congr_on
    {X : Type u} [PseudoMetricSpace X] {function replacement : ℝ → X} {lower upper : ℝ}
    (hEqual : Set.EqOn function replacement (uIcc lower upper))
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function lower upper) :
    _root_.AbsolutelyContinuousOnInterval replacement lower upper := by
  rw [absolutelyContinuousOnInterval_iff] at hContinuous ⊢
  intro epsilon hEpsilon
  obtain ⟨delta, hDelta, hControl⟩ := hContinuous epsilon hEpsilon
  refine ⟨delta, hDelta, fun intervals hIntervals hLength ↦ ?_⟩
  have hOriginal := hControl intervals hIntervals hLength
  convert hOriginal using 1
  apply Finset.sum_congr rfl
  intro index hIndex
  rw [hEqual (hIntervals.1 index hIndex).1,
    hEqual (hIntervals.1 index hIndex).2]

/-- Adding a fixed value preserves absolute continuity on an interval. -/
theorem AbsolutelyContinuousOnInterval.const_add
    {F : Type*} [SeminormedAddCommGroup F]
    {function : ℝ → F} {lower upper : ℝ} (constant : F)
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function lower upper) :
    _root_.AbsolutelyContinuousOnInterval
      (fun point ↦ constant + function point) lower upper := by
  unfold _root_.AbsolutelyContinuousOnInterval at hContinuous ⊢
  simpa only [dist_add_left] using hContinuous

/-- Zeroes at which a real function owns some nonzero classical derivative. -/
def nonzeroDerivativeZeroSet (function : ℝ → ℝ) : Set ℝ :=
  {point | function point = 0 ∧
    ∃ derivative, derivative ≠ 0 ∧ HasDerivAt function derivative point}

/-- Zeroes carrying a nonzero classical derivative form a countable set. -/
theorem countable_nonzeroDerivativeZeroSet (function : ℝ → ℝ) :
    (nonzeroDerivativeZeroSet function).Countable := by
  apply countable_setOfPred_isolated_right_within.mono
  intro point hPoint
  rcases hPoint with ⟨hZero, derivative, hDerivativeNonzero, hDerivative⟩
  refine ⟨hZero, ?_⟩
  apply Filter.eventually_false_iff_eq_bot.mp
  have hEventuallyNonzero :
      ∀ᶠ nearby in 𝓝[≠] point, function nearby ≠ 0 :=
    hDerivative.eventually_ne hDerivativeNonzero
  have hFilterMono :
      𝓝[{nearby | function nearby = 0} ∩ Ioi point] point ≤ 𝓝[≠] point := by
    apply nhdsWithin_mono
    intro nearby hNearby
    simp only [mem_inter_iff, mem_Ioi] at hNearby
    simp only [mem_compl_iff, mem_singleton_iff]
    exact ne_of_gt hNearby.2
  have hEventuallyNonzeroWithin := hEventuallyNonzero.filter_mono hFilterMono
  filter_upwards [hEventuallyNonzeroWithin, self_mem_nhdsWithin] with
    nearby hNearbyNonzero hNearby
  exact hNearbyNonzero hNearby.1

/-- If both a real function and its derivative vanish at a point, its absolute value has zero
derivative there. -/
theorem hasDerivAt_abs_of_eq_zero_of_deriv_eq_zero
    {function : ℝ → ℝ} {point : ℝ}
    (hDerivative : HasDerivAt function 0 point) (hZero : function point = 0) :
    HasDerivAt (fun nearby ↦ |function nearby|) 0 point := by
  apply HasDerivAt.of_isLittleO
  simpa only [hZero, smul_zero, sub_zero, Real.norm_eq_abs, abs_zero] using
    hDerivative.isLittleO.norm_left

/-- An almost-everywhere classical derivative passes through absolute value with the real sign
multiplier under any atomless measure. -/
theorem ae_hasDerivAt_abs_of_ae_hasDerivAt
    (measure : Measure ℝ) [NullSingletonClass measure]
    {function derivative : ℝ → ℝ}
    (hDerivative : ∀ᵐ point ∂measure,
      HasDerivAt function (derivative point) point) :
    ∀ᵐ point ∂measure,
      HasDerivAt (fun nearby ↦ |function nearby|)
        (Real.sign (function point) * derivative point) point := by
  filter_upwards [hDerivative,
    (countable_nonzeroDerivativeZeroSet function).ae_notMem measure] with
      point hDerivativeAt hNotExceptional
  by_cases hZero : function point = 0
  · have hDerivativeZero : derivative point = 0 := by
      by_contra hNonzero
      exact hNotExceptional ⟨hZero, derivative point, hNonzero, hDerivativeAt⟩
    rw [hDerivativeZero, mul_zero]
    exact hasDerivAt_abs_of_eq_zero_of_deriv_eq_zero
      (hDerivativeZero ▸ hDerivativeAt) hZero
  · have hAbsDerivative := (hDerivativeAt.hasFDerivAt.abs hZero).hasDerivAt
    rcases lt_or_gt_of_ne hZero with hNegative | hPositive
    · simpa [hNegative, Real.sign_of_neg hNegative] using hAbsDerivative
    · simpa [hPositive, Real.sign_of_pos hPositive] using hAbsDerivative

/-- Absolute value preserves absolute continuity for real functions. -/
theorem AbsolutelyContinuousOnInterval.abs
    {function : ℝ → ℝ} {lower upper : ℝ}
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function lower upper) :
    _root_.AbsolutelyContinuousOnInterval (fun point ↦ |function point|) lower upper := by
  unfold _root_.AbsolutelyContinuousOnInterval at hContinuous ⊢
  apply squeeze_zero
    (fun _data ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg)
    (fun data ↦ by
      apply Finset.sum_le_sum
      intro index _hIndex
      simpa only [Real.dist_eq] using
        abs_abs_sub_abs_le_abs_sub
          (function (data.2 index).1) (function (data.2 index).2))
    (by simpa only [Real.dist_eq] using hContinuous)

end FiniteMarkovProcesses
