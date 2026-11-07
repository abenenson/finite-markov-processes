/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1DerivativeTopology
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalStepL1Path
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted coordinate integrals of finite-interval L1 paths

This module exposes integration of one finite-coordinate `L1` path against a compactly supported
continuous real test as a continuous linear functional on the genuine almost-everywhere quotient.
It is the strong-`L1` half of the continuous dual evaluations used in finite-interval hybrid-BV
rate functionals.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped CompactlySupported ENNReal

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- A compactly supported continuous real test as an `L∞` equivalence class on the physical
open interval. -/
noncomputable def finiteIntervalCompactTestToLpTop (test : C_c(ℝ, ℝ)) :
    Lp ℝ ∞ (finiteOpenIntervalVolume duration) :=
  (test.continuous.memLp_top_of_hasCompactSupport test.hasCompactSupport
    (finiteOpenIntervalVolume duration)).toLp test

/-- Projection of a finite-coordinate `L1` path onto one scalar coordinate, as a continuous
linear map of quotient spaces. -/
noncomputable def finiteIntervalL1PathCoordinateProjection
    (coordinate : Coordinate) :
    FiniteIntervalL1Path Coordinate duration →L[ℝ]
      Lp ℝ 1 (finiteOpenIntervalVolume duration) :=
  (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).compLpL
    1 (finiteOpenIntervalVolume duration)

/-- Integration of one path coordinate against a compact continuous test, as a continuous linear
functional of the strong-`L1` quotient. -/
noncomputable def finiteIntervalL1PathWeightedCoordinateIntegral
    (test : C_c(ℝ, ℝ)) (coordinate : Coordinate) :
    FiniteIntervalL1Path Coordinate duration →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (finiteOpenIntervalVolume duration) ∞ 1
      (finiteIntervalCompactTestToLpTop test)).comp
        (finiteIntervalL1PathCoordinateProjection coordinate)

/-- The chosen `L∞` representative of a compact continuous test agrees almost everywhere with
the original test. -/
theorem finiteIntervalCompactTestToLpTop_coeFn (test : C_c(ℝ, ℝ)) :
    finiteIntervalCompactTestToLpTop (duration := duration) test
      =ᵐ[finiteOpenIntervalVolume duration] test := by
  exact MemLp.coeFn_toLp _

/-- The quotient-level coordinate projection agrees almost everywhere with pointwise coordinate
evaluation. -/
theorem finiteIntervalL1PathCoordinateProjection_coeFn
    (coordinate : Coordinate) (path : FiniteIntervalL1Path Coordinate duration) :
    finiteIntervalL1PathCoordinateProjection coordinate path
      =ᵐ[finiteOpenIntervalVolume duration] fun time => path time coordinate := by
  refine (ContinuousLinearMap.coeFn_compLpL _ _).trans ?_
  exact Filter.Eventually.of_forall fun _time => by simp only [PiLp.proj_apply]

/-- The continuous quotient functional is the expected weighted coordinate integral for
Mathlib's chosen coefficient functions. -/
theorem finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral
    (test : C_c(ℝ, ℝ)) (coordinate : Coordinate)
    (path : FiniteIntervalL1Path Coordinate duration) :
    finiteIntervalL1PathWeightedCoordinateIntegral test coordinate path =
      ∫ time, test time * path time coordinate
        ∂finiteOpenIntervalVolume duration := by
  rw [finiteIntervalL1PathWeightedCoordinateIntegral,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [finiteIntervalCompactTestToLpTop_coeFn test,
    finiteIntervalL1PathCoordinateProjection_coeFn coordinate path] with
      time hTest hPath
  simp only [ContinuousLinearMap.mul_apply', hTest, hPath]

/-- A compact test paired with a constant scalar on the open physical interval is its ordinary
interval integral times that scalar. -/
theorem integral_compactTest_mul_constant_finiteOpenIntervalVolume
    (test : C_c(ℝ, ℝ)) (coefficient : ℝ) (hDuration : 0 ≤ duration) :
    (∫ time, test time * coefficient ∂finiteOpenIntervalVolume duration) =
      coefficient * ∫ time in 0..duration, test time := by
  unfold finiteOpenIntervalVolume
  rw [show (fun time => test time * coefficient) =
      fun time => coefficient * test time by
    funext time
    ring]
  rw [integral_const_mul]
  calc
    coefficient * ∫ time in Ioo 0 duration, test time =
        coefficient * ∫ time in Ioc 0 duration, test time := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = coefficient * ∫ time in 0..duration, test time := by
      rw [intervalIntegral.integral_of_le hDuration]

/-- A compact test paired with one right-continuous scalar event step is the corresponding tail
interval integral times the event weight. -/
theorem integral_compactTest_mul_scalarRightEventStep_finiteOpenIntervalVolume
    (test : C_c(ℝ, ℝ)) (eventTime coefficient : ℝ)
    (hEventTime : eventTime ∈ Ioo 0 duration) :
    (∫ time, test time * scalarRightEventStep eventTime coefficient time
      ∂finiteOpenIntervalVolume duration) =
      coefficient * ∫ time in eventTime..duration, test time := by
  unfold finiteOpenIntervalVolume
  rw [show (fun time => test time * scalarRightEventStep eventTime coefficient time) =
      Set.indicator (Ici eventTime) (fun time => test time * coefficient) by
    funext time
    simp only [scalarRightEventStep]
    by_cases hObserved : eventTime ≤ time
    · simp [hObserved]
    · simp [hObserved]]
  rw [integral_indicator measurableSet_Ici]
  rw [Measure.restrict_restrict measurableSet_Ici]
  rw [show Ici eventTime ∩ Ioo 0 duration = Ico eventTime duration by
    ext time
    simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico]
    constructor
    · rintro ⟨hLower, _hZero, hUpper⟩
      exact ⟨hLower, hUpper⟩
    · intro hTime
      exact ⟨hTime.1, hEventTime.1.trans_le hTime.1, hTime.2⟩]
  rw [show (fun time => test time * coefficient) =
      fun time => coefficient * test time by
    funext time
    ring]
  rw [integral_const_mul]
  rw [integral_Ico_eq_integral_Ioo]
  calc
    coefficient * ∫ time in Ioo eventTime duration, test time =
        coefficient * ∫ time in Ioc eventTime duration, test time := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = coefficient * ∫ time in eventTime..duration, test time := by
      rw [intervalIntegral.integral_of_le hEventTime.2.le]

/-- Weighted coordinate evaluation of a constant finite-coordinate `L1` path. -/
theorem finiteIntervalL1PathWeightedCoordinateIntegral_constant
    (test : C_c(ℝ, ℝ)) (coordinate : Coordinate)
    (value : FiniteCoordinateL1Value Coordinate) (hDuration : 0 ≤ duration) :
    finiteIntervalL1PathWeightedCoordinateIntegral test coordinate
        (finiteIntervalConstantL1Path duration value) =
      value coordinate * ∫ time in 0..duration, test time := by
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral]
  calc
    (∫ time, test time *
        (finiteIntervalConstantL1Path duration value : ℝ →
          FiniteCoordinateL1Value Coordinate) time coordinate
        ∂finiteOpenIntervalVolume duration) =
        ∫ time, test time * value coordinate
          ∂finiteOpenIntervalVolume duration := by
      apply integral_congr_ae
      filter_upwards [finiteIntervalConstantL1Path_eventuallyEq duration value] with time hTime
      rw [hTime]
    _ = value coordinate * ∫ time in 0..duration, test time :=
      integral_compactTest_mul_constant_finiteOpenIntervalVolume test
        (value coordinate) hDuration

/-- Weighted coordinate evaluation of one vector-valued right-continuous event step. -/
theorem finiteIntervalL1PathWeightedCoordinateIntegral_vectorRightEventStep
    [DecidableEq Coordinate]
    (test : C_c(ℝ, ℝ)) (coordinate : Coordinate) (eventTime : ℝ)
    (value : FiniteCoordinateL1Value Coordinate)
    (hEventTime : eventTime ∈ Ioo 0 duration) :
    finiteIntervalL1PathWeightedCoordinateIntegral test coordinate
        (finiteCoordinateVectorRightEventStepL1Path duration eventTime value) =
      value coordinate * ∫ time in eventTime..duration, test time := by
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral]
  calc
    (∫ time, test time *
        (finiteCoordinateVectorRightEventStepL1Path duration eventTime value : ℝ →
          FiniteCoordinateL1Value Coordinate) time coordinate
        ∂finiteOpenIntervalVolume duration) =
        ∫ time, test time * scalarRightEventStep eventTime (value coordinate) time
          ∂finiteOpenIntervalVolume duration := by
      apply integral_congr_ae
      filter_upwards [
        finiteCoordinateVectorRightEventStepL1Path_eventuallyEq duration eventTime value
      ] with time hTime
      rw [hTime]
      simp only [PiLp.smul_apply, smul_eq_mul]
      unfold scalarRightEventStep
      by_cases hObserved : eventTime ≤ time
      · simp [hObserved]
      · simp [hObserved]
    _ = value coordinate * ∫ time in eventTime..duration, test time :=
      integral_compactTest_mul_scalarRightEventStep_finiteOpenIntervalVolume test
        eventTime (value coordinate) hEventTime

/-- Weighted coordinate integration is continuous in the strong-`L1` quotient topology. -/
theorem continuous_finiteIntervalL1PathWeightedCoordinateIntegral
    (test : C_c(ℝ, ℝ)) (coordinate : Coordinate) :
    Continuous fun path : FiniteIntervalL1Path Coordinate duration =>
      finiteIntervalL1PathWeightedCoordinateIntegral test coordinate path :=
  (finiteIntervalL1PathWeightedCoordinateIntegral test coordinate).continuous

end

end FiniteMarkovProcesses
