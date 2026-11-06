/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Probability.Moments.Variance

/-!
# Variance concentration for finite independent heterogeneous families

This module records the source-neutral Chebyshev estimate needed for empirical observables of
independent but not necessarily identically distributed replicas.  A uniform coordinate variance
bound gives the exact finite-family deviation estimate around the sum of the coordinate means.

## Main result

- `measure_sum_deviation_ge_le_of_iIndepFun_of_variance_le`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

universe u v

variable {Sample : Type u} {Index : Type v} [MeasurableSpace Sample]

/-- A finite independent heterogeneous family with coordinate variances bounded by `varianceBound`
has the corresponding Chebyshev deviation estimate for its sum. -/
theorem measure_sum_deviation_ge_le_of_iIndepFun_of_variance_le
    [Fintype Index] (μ : Measure Sample) [IsProbabilityMeasure μ]
    (observable : Index → Sample → ℝ)
    (hObservable : ∀ index, MemLp (observable index) 2 μ)
    (hIndependent : iIndepFun observable μ)
    (varianceBound : ℝ)
    (hVariance : ∀ index, variance (observable index) μ ≤ varianceBound)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    μ {sample |
        deviation ≤
          |∑ index, observable index sample -
            ∑ index, ∫ sample, observable index sample ∂μ|} ≤
      ENNReal.ofReal
        ((Fintype.card Index : ℝ) * varianceBound / deviation ^ 2) := by
  let total : Sample → ℝ := fun sample ↦ ∑ index, observable index sample
  have hTotal : MemLp total 2 μ := by
    exact memLp_finsetSum Finset.univ fun index _ ↦ hObservable index
  have hPairwise : Set.Pairwise (↑(Finset.univ : Finset Index) : Set Index)
      (fun first second ↦
        IndepFun (observable first) (observable second) μ) := by
    intro first _hFirst second _hSecond hNe
    exact hIndependent.indepFun hNe
  have hTotalEq : total = ∑ index, observable index := by
    funext sample
    simp only [total, Finset.sum_apply]
  have hVarianceTotal : variance total μ ≤
      (Fintype.card Index : ℝ) * varianceBound := by
    rw [hTotalEq]
    calc
      variance (∑ index, observable index) μ =
          ∑ index, variance (observable index) μ :=
        ProbabilityTheory.IndepFun.variance_sum
          (s := Finset.univ) (fun index _ ↦ hObservable index) hPairwise
      _ ≤ ∑ _index : Index, varianceBound := by
        exact Finset.sum_le_sum fun index _ ↦ hVariance index
      _ = (Fintype.card Index : ℝ) * varianceBound := by simp
  have hChebyshev := meas_ge_le_variance_div_sq hTotal hDeviation
  have hIntegral : ∫ sample, total sample ∂μ =
      ∑ index, ∫ sample, observable index sample ∂μ := by
    exact integral_finsetSum Finset.univ fun index _ ↦
      (hObservable index).integrable one_le_two
  rw [show {sample |
          deviation ≤
            |∑ index, observable index sample -
              ∑ index, ∫ sample, observable index sample ∂μ|} =
        {sample | deviation ≤ |total sample - ∫ sample, total sample ∂μ|} by
      ext sample
      simp only [total, hIntegral]]
  refine hChebyshev.trans ?_
  exact ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right hVarianceTotal (sq_nonneg deviation)

/-- The expected absolute centered deviation of a finite independent heterogeneous sum is at
most the square root of the summed uniform variance bound. -/
theorem integral_abs_sum_sub_mean_le_sqrt_card_mul_varianceBound
    [Fintype Index] (μ : Measure Sample) [IsProbabilityMeasure μ]
    (observable : Index → Sample → ℝ)
    (hObservable : ∀ index, MemLp (observable index) 2 μ)
    (hIndependent : iIndepFun observable μ)
    (varianceBound : ℝ)
    (hVariance : ∀ index, variance (observable index) μ ≤ varianceBound) :
    (∫ sample,
        |∑ index, observable index sample -
          ∑ index, ∫ sample, observable index sample ∂μ| ∂μ) ≤
      Real.sqrt ((Fintype.card Index : ℝ) * varianceBound) := by
  let total : Sample → ℝ := fun sample ↦ ∑ index, observable index sample
  have hTotal : MemLp total 2 μ :=
    memLp_finsetSum Finset.univ fun index _hIndex ↦ hObservable index
  have hPairwise : Set.Pairwise (↑(Finset.univ : Finset Index) : Set Index)
      (fun first second ↦
        IndepFun (observable first) (observable second) μ) := by
    intro first _hFirst second _hSecond hNe
    exact hIndependent.indepFun hNe
  have hTotalEq : total = ∑ index, observable index := by
    funext sample
    simp only [total, Finset.sum_apply]
  have hVarianceTotal : variance total μ ≤
      (Fintype.card Index : ℝ) * varianceBound := by
    rw [hTotalEq]
    calc
      variance (∑ index, observable index) μ =
          ∑ index, variance (observable index) μ :=
        ProbabilityTheory.IndepFun.variance_sum
          (s := Finset.univ) (fun index _hIndex ↦ hObservable index) hPairwise
      _ ≤ ∑ _index : Index, varianceBound :=
        Finset.sum_le_sum fun index _hIndex ↦ hVariance index
      _ = (Fintype.card Index : ℝ) * varianceBound := by simp
  have hIntegral : ∫ sample, total sample ∂μ =
      ∑ index, ∫ sample, observable index sample ∂μ :=
    integral_finsetSum Finset.univ fun index _hIndex ↦
      (hObservable index).integrable one_le_two
  let centered : Sample → ℝ := fun sample ↦ total sample - ∫ sample, total sample ∂μ
  have hCentered : MemLp centered 2 μ :=
    hTotal.sub (memLp_const (∫ sample, total sample ∂μ))
  have hOne : MemLp (fun _sample : Sample ↦ (1 : ℝ)) 2 μ :=
    memLp_const 1
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := centered) (g := fun _sample : Sample ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hCentered) (by simpa using hOne)
  have hCenteredSquare :
      (∫ sample, ‖centered sample‖ ^ (2 : ℝ) ∂μ) = variance total μ := by
    rw [variance_eq_integral hTotal.aemeasurable]
    apply integral_congr_ae
    filter_upwards [] with sample
    rw [Real.norm_eq_abs, Real.rpow_two]
    exact sq_abs (centered sample)
  have hOneSquare :
      (∫ sample, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) = 1 := by simp
  have hExpectedLeVarianceRoot :
      (∫ sample, |centered sample| ∂μ) ≤ Real.sqrt (variance total μ) := by
    calc
      (∫ sample, |centered sample| ∂μ) =
          ∫ sample, ‖centered sample‖ * ‖(1 : ℝ)‖ ∂μ := by simp
      _ ≤ (∫ sample, ‖centered sample‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ sample, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
      _ = Real.sqrt (variance total μ) := by
        rw [hCenteredSquare, hOneSquare]
        norm_num [Real.sqrt_eq_rpow]
  rw [show (fun sample ↦
      |∑ index, observable index sample -
        ∑ index, ∫ sample, observable index sample ∂μ|) =
      fun sample ↦ |centered sample| by
    funext sample
    simp only [centered, total, hIntegral]]
  exact hExpectedLeVarianceRoot.trans
    (Real.sqrt_le_sqrt hVarianceTotal)

end FiniteMarkovProcesses.Probability
