/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume
public import
FiniteMarkovProcesses.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFundamentalTheorem

/-!
# Weighted integrals over ordered event times

This module evaluates the product weight of a nonnegative continuous function over the ordered
event-time simplex. Splitting off the last coordinate gives the Volterra recursion; the
fundamental theorem of calculus then identifies the integral with a factorial-normalized power
of the one-dimensional weight integral.

The resulting exponential series supplies the integral formula for resumming
time-dependent virtual self events inside a physical dwell.

## Main Results

- `lintegral_weightedOrderedJumpTimes_succ`: last-time disintegration of the weighted simplex.
- `lintegral_weightedOrderedJumpTimes`: exact factorial-normalized weighted integral.
- `tsum_lintegral_weightedOrderedJumpTimes`: exponential resummation over every event count.
- `tsum_lintegral_weightedOrderedTimesInInterval`: the translated arbitrary-interval form.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

/-- Product of one nonnegative real weight over a finite event-time vector, valued in extended
nonnegative reals for Tonelli integration. -/
noncomputable def weightedOrderedJumpTimesIntegrand
    (weight : ℝ → ℝ) (n : ℕ) (times : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ index, ENNReal.ofReal (weight (times index))

/-- A measurable one-dimensional weight gives a measurable finite product weight. -/
theorem measurable_weightedOrderedJumpTimesIntegrand
    {weight : ℝ → ℝ} (hWeight : Measurable weight) (n : ℕ) :
    Measurable (weightedOrderedJumpTimesIntegrand weight n) := by
  unfold weightedOrderedJumpTimesIntegrand
  fun_prop

/-- Splitting off the last event time turns the weighted `(n+1)`-simplex integral into the
one-dimensional integral of the weighted `n`-simplex integral. -/
theorem lintegral_weightedOrderedJumpTimes_succ
    {weight : ℝ → ℝ} (hWeight : Measurable weight) (n : ℕ) (T : ℝ) :
    ∫⁻ times : Fin (n + 1) → ℝ in orderedJumpTimes (n + 1) T,
        weightedOrderedJumpTimesIntegrand weight (n + 1) times =
      ∫⁻ lastTime : ℝ in Ioo 0 T,
        ENNReal.ofReal (weight lastTime) *
          ∫⁻ earlierTimes : Fin n → ℝ in orderedJumpTimes n lastTime,
            weightedOrderedJumpTimesIntegrand weight n earlierTimes := by
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  let lastSection := orderedJumpTimesLastSection n T
  have hPreserving := volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hSection : MeasurableSet lastSection :=
    measurableSet_orderedJumpTimesLastSection n T
  have hMap :
      Measure.map split (volume.restrict (orderedJumpTimes (n + 1) T)) =
        volume.restrict lastSection := by
    calc
      Measure.map split (volume.restrict (orderedJumpTimes (n + 1) T)) =
          Measure.map split (volume.restrict (split ⁻¹' lastSection)) := by
        rw [show split ⁻¹' lastSection = orderedJumpTimes (n + 1) T by
          exact piFinSuccAbove_preimage_orderedJumpTimesLastSection n T]
      _ = (Measure.map split volume).restrict lastSection := by
        rw [Measure.restrict_map hPreserving.measurable hSection]
      _ = volume.restrict lastSection := by rw [hPreserving.map_eq]
  let pairWeight : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun coordinates ↦
    ENNReal.ofReal (weight coordinates.1) *
      weightedOrderedJumpTimesIntegrand weight n coordinates.2
  have hSplitWeight (times : Fin (n + 1) → ℝ) :
      pairWeight (split times) =
        weightedOrderedJumpTimesIntegrand weight (n + 1) times := by
    unfold pairWeight weightedOrderedJumpTimesIntegrand
    rw [Fin.prod_univ_castSucc]
    change
      ENNReal.ofReal (weight (times (Fin.last n))) *
          (∏ index, ENNReal.ofReal (weight (times ((Fin.last n).succAbove index)))) =
        (∏ index : Fin n, ENNReal.ofReal (weight (times index.castSucc))) *
          ENNReal.ofReal (weight (times (Fin.last n)))
    simp only [Fin.succAbove_last]
    ac_rfl
  calc
    (∫⁻ times : Fin (n + 1) → ℝ in orderedJumpTimes (n + 1) T,
        weightedOrderedJumpTimesIntegrand weight (n + 1) times) =
        ∫⁻ coordinates, pairWeight coordinates ∂Measure.map split
          (volume.restrict (orderedJumpTimes (n + 1) T)) := by
      rw [MeasureTheory.lintegral_map_equiv]
      exact lintegral_congr fun times ↦ (hSplitWeight times).symm
    _ = ∫⁻ coordinates in lastSection, pairWeight coordinates := by rw [hMap]
    _ = _ := by
      have hPairWeight : Measurable pairWeight := by
        unfold pairWeight
        exact ((hWeight.comp measurable_fst).ennreal_ofReal).mul
          ((measurable_weightedOrderedJumpTimesIntegrand hWeight n).comp measurable_snd)
      rw [← lintegral_indicator hSection]
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod _ ((hPairWeight.indicator hSection).aemeasurable)]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro lastTime
      have hFiber :
          (fun earlierTimes ↦ lastSection.indicator pairWeight (lastTime, earlierTimes)) =
            if lastTime ∈ Ioo (0 : ℝ) T then
              fun earlierTimes ↦
                ENNReal.ofReal (weight lastTime) *
                  (orderedJumpTimes n lastTime).indicator
                    (weightedOrderedJumpTimesIntegrand weight n) earlierTimes
            else fun _ ↦ 0 := by
        funext earlierTimes
        by_cases hLast : lastTime ∈ Ioo (0 : ℝ) T
        · by_cases hEarlier : earlierTimes ∈ orderedJumpTimes n lastTime
          · have hMem : (lastTime, earlierTimes) ∈ lastSection := by
              exact ⟨hLast, hEarlier⟩
            rw [Set.indicator_of_mem hMem, ite_eq_left hLast,
              Set.indicator_of_mem hEarlier]
          · have hNotMem : (lastTime, earlierTimes) ∉ lastSection := by
              intro hMem
              exact hEarlier hMem.2
            rw [Set.indicator_of_notMem hNotMem, ite_eq_left hLast,
              Set.indicator_of_notMem hEarlier]
            simp
        · have hNotMem : (lastTime, earlierTimes) ∉ lastSection := by
            intro hMem
            exact hLast hMem.1
          rw [Set.indicator_of_notMem hNotMem, ite_eq_right hLast]
      rw [hFiber]
      by_cases hLast : lastTime ∈ Ioo (0 : ℝ) T
      · rw [ite_eq_left hLast, Set.indicator_of_mem hLast]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_indicator (measurableSet_orderedJumpTimes n lastTime)]
      · rw [ite_eq_right hLast, Set.indicator_of_notMem hLast]
        simp

/-- Integrating one weight against a factorial-normalized power of its cumulative interval
integral produces the next factorial-normalized power. -/
theorem integral_Ioo_weight_mul_intervalIntegral_pow_div_factorial
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∫ time in Ioo 0 T,
        weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial =
      (∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) / (n + 1).factorial := by
  let cumulative : ℝ → ℝ := fun time ↦ ∫ prior in (0 : ℝ)..time, weight prior
  let antiderivative : ℝ → ℝ := fun time ↦ cumulative time ^ (n + 1) / (n + 1).factorial
  have hCumulativeDeriv (time : ℝ) :
      HasDerivAt cumulative (weight time) time := by
    unfold cumulative
    exact intervalIntegral.integral_hasDerivAt_right
      (hContinuous.intervalIntegrable 0 time)
      hContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hContinuous.continuousAt
  have hAntiderivativeDeriv (time : ℝ) :
      HasDerivAt antiderivative
        (weight time * cumulative time ^ n / n.factorial) time := by
    have hPower := (hCumulativeDeriv time).pow (n + 1)
    have hQuotient := hPower.div_const ((n + 1).factorial : ℝ)
    convert hQuotient using 1
    simp only [Nat.add_one_sub_one, Nat.factorial_succ]
    push_cast
    field_simp
  have hIntegrandContinuous :
      Continuous fun time ↦ weight time * cumulative time ^ n / n.factorial := by
    have hCumulativeContinuous : Continuous cumulative :=
      continuous_iff_continuousAt.mpr fun time ↦ (hCumulativeDeriv time).continuousAt
    fun_prop
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hT (continuous_iff_continuousAt.mpr
      (fun time ↦ (hAntiderivativeDeriv time).continuousAt)).continuousOn
    (fun time _hTime ↦ hAntiderivativeDeriv time)
    (hIntegrandContinuous.intervalIntegrable 0 T)
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hT]
  rw [hIntegral]
  simp [antiderivative, cumulative]

/-- The cumulative-weight power recursion for an arbitrary interval-integrable weight.  The
interval primitive is absolutely continuous, so its power owns the required derivative almost
everywhere without any pointwise continuity hypothesis. -/
theorem integral_Ioo_weight_mul_intervalIntegral_pow_div_factorial_of_intervalIntegrable
    {weight : ℝ → ℝ} (T : ℝ)
    (hIntegrable : IntervalIntegrable weight volume 0 T)
    (n : ℕ) (hT : 0 ≤ T) :
    ∫ time in Ioo 0 T,
        weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial =
      (∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) / (n + 1).factorial := by
  let cumulative : ℝ → ℝ := fun time ↦ ∫ prior in (0 : ℝ)..time, weight prior
  let antiderivative : ℝ → ℝ :=
    fun time ↦ cumulative time ^ (n + 1) / (n + 1).factorial
  have hCumulativeAbsoluteContinuous :
      AbsolutelyContinuousOnInterval cumulative 0 T :=
    FiniteMarkovProcesses.intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
      hIntegrable (by simp)
  have hPowerAbsoluteContinuous :
      AbsolutelyContinuousOnInterval (fun time ↦ cumulative time ^ (n + 1)) 0 T := by
    induction n with
    | zero =>
        simpa using hCumulativeAbsoluteContinuous
    | succ exponent inductionHypothesis =>
        simpa [pow_succ] using
          inductionHypothesis.fun_mul hCumulativeAbsoluteContinuous
  have hAntiderivativeAbsoluteContinuous :
      AbsolutelyContinuousOnInterval antiderivative 0 T := by
    have hScaled := hPowerAbsoluteContinuous.const_mul
      (((n + 1).factorial : ℝ)⁻¹)
    simpa [antiderivative, div_eq_mul_inv, mul_comm] using hScaled
  have hPrimitiveDerivative := hIntegrable.ae_hasDerivAt_integral
  have hDerivativeEquality : ∀ᵐ time,
      time ∈ uIoc (0 : ℝ) T →
        deriv antiderivative time =
          weight time * cumulative time ^ n / n.factorial := by
    filter_upwards [hPrimitiveDerivative] with time hDerivative hTime
    have hTimeClosed : time ∈ uIcc (0 : ℝ) T := by
      exact uIoc_subset_uIcc hTime
    have hCumulativeDerivative : HasDerivAt cumulative (weight time) time := by
      exact hDerivative hTimeClosed 0 (by simp)
    have hPowerDerivative := (hCumulativeDerivative.pow (n + 1)).div_const
      ((n + 1).factorial : ℝ)
    have hAntiderivativeDerivative : HasDerivAt antiderivative
        (weight time * cumulative time ^ n / n.factorial) time := by
      convert hPowerDerivative using 1
      simp only [Nat.add_one_sub_one, Nat.factorial_succ]
      push_cast
      field_simp
    exact hAntiderivativeDerivative.deriv
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hT]
  calc
    (∫ time in (0 : ℝ)..T,
        weight time * cumulative time ^ n / n.factorial) =
        ∫ time in (0 : ℝ)..T, deriv antiderivative time := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hDerivativeEquality] with time hDerivative hTime
      exact (hDerivative hTime).symm
    _ = antiderivative T - antiderivative 0 :=
      FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
        hAntiderivativeAbsoluteContinuous
    _ = (∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) /
        (n + 1).factorial := by
      simp [antiderivative, cumulative]

/-- Extended-nonnegative form of the cumulative-weight power recursion. -/
theorem lintegral_Ioo_weight_mul_intervalIntegral_pow_div_factorial
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ time : ℝ in Ioo 0 T,
        ENNReal.ofReal
          (weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial) =
      ENNReal.ofReal
        ((∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) / (n + 1).factorial) := by
  have hCumulativeContinuous :
      Continuous fun time ↦ ∫ prior in (0 : ℝ)..time, weight prior := by
    rw [continuous_iff_continuousAt]
    intro time
    exact (intervalIntegral.integral_hasDerivAt_right
      (hContinuous.intervalIntegrable 0 time)
      hContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hContinuous.continuousAt).continuousAt
  have hIntegrable :
      Integrable
        (fun time ↦
          weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial)
        (volume.restrict (Ioo 0 T)) := by
    exact ((hContinuous.mul (hCumulativeContinuous.pow n)).div_const
      (n.factorial : ℝ)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hNonnegativeAE :
      0 ≤ᶠ[ae (volume.restrict (Ioo 0 T))]
        fun time ↦
          weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    have hCumulativeNonnegative :
        0 ≤ ∫ prior in (0 : ℝ)..time, weight prior :=
      intervalIntegral.integral_nonneg_of_forall hTime.1.le hNonnegative
    exact div_nonneg
      (mul_nonneg (hNonnegative time) (pow_nonneg hCumulativeNonnegative n))
      (Nat.cast_nonneg n.factorial)
  rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hNonnegativeAE]
  congr 1
  exact integral_Ioo_weight_mul_intervalIntegral_pow_div_factorial
    hContinuous n T hT

/-- Extended-nonnegative cumulative-weight recursion for measurable interval-integrable weights. -/
theorem lintegral_Ioo_weight_mul_intervalIntegral_pow_div_factorial_of_intervalIntegrable
    {weight : ℝ → ℝ} (T : ℝ)
    (hIntegrable : IntervalIntegrable weight volume 0 T)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (n : ℕ) (hT : 0 ≤ T) :
    ∫⁻ time : ℝ in Ioo 0 T,
        ENNReal.ofReal
          (weight time * (∫ prior in (0 : ℝ)..time, weight prior) ^ n / n.factorial) =
      ENNReal.ofReal
        ((∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) / (n + 1).factorial) := by
  let cumulative : ℝ → ℝ := fun time ↦ ∫ prior in (0 : ℝ)..time, weight prior
  let multiplier : ℝ → ℝ :=
    fun time ↦ cumulative time ^ n / n.factorial
  have hCumulativeAbsoluteContinuous :
      AbsolutelyContinuousOnInterval cumulative 0 T :=
    FiniteMarkovProcesses.intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
      hIntegrable (by simp)
  have hWeightIntegrable : Integrable weight (volume.restrict (Ioo 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mp hIntegrable
  have hMultiplierContinuousOn : ContinuousOn multiplier (uIcc (0 : ℝ) T) := by
    unfold multiplier
    exact hCumulativeAbsoluteContinuous.continuousOn.pow n |>.div_const _
  have hOpenSubset : Ioo (0 : ℝ) T ⊆ uIcc 0 T := by
    rw [uIcc_of_le hT]
    exact Ioo_subset_Icc_self
  have hMultiplierStronglyMeasurable :
      AEStronglyMeasurable multiplier (volume.restrict (Ioo 0 T)) :=
    (hMultiplierContinuousOn.mono hOpenSubset).aestronglyMeasurable
      measurableSet_Ioo
  obtain ⟨bound, hBound⟩ := hCumulativeAbsoluteContinuous.exists_bound
  have hBoundNonnegative : 0 ≤ bound := by
    exact (norm_nonneg (cumulative 0)).trans (hBound 0 (by simp))
  have hMultiplierBound : ∀ᵐ time ∂volume.restrict (Ioo 0 T),
      ‖multiplier time‖ ≤ bound ^ n / n.factorial := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    unfold multiplier
    rw [norm_div, norm_pow, Real.norm_natCast]
    gcongr
    exact hBound time (hOpenSubset hTime)
  have hIntegrableProduct : Integrable (fun time ↦ weight time * multiplier time)
      (volume.restrict (Ioo 0 T)) :=
    hWeightIntegrable.mul_bdd hMultiplierStronglyMeasurable hMultiplierBound
  have hIntegrableTarget : Integrable
      (fun time ↦ weight time * cumulative time ^ n / n.factorial)
      (volume.restrict (Ioo 0 T)) := by
    simpa [multiplier, mul_div_assoc] using hIntegrableProduct
  have hNonnegativeAE :
      0 ≤ᶠ[ae (volume.restrict (Ioo 0 T))]
        fun time ↦ weight time * cumulative time ^ n / n.factorial := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    have hCumulativeNonnegative : 0 ≤ cumulative time := by
      unfold cumulative
      exact intervalIntegral.integral_nonneg_of_forall hTime.1.le hNonnegative
    exact div_nonneg
      (mul_nonneg (hNonnegative time) (pow_nonneg hCumulativeNonnegative n))
      (Nat.cast_nonneg n.factorial)
  rw [← ofReal_integral_eq_lintegral_ofReal hIntegrableTarget hNonnegativeAE]
  congr 1
  exact integral_Ioo_weight_mul_intervalIntegral_pow_div_factorial_of_intervalIntegrable
    T hIntegrable n hT

/-- The product weight over the ordered `n`-event simplex is the `n`th power of its
one-dimensional integral divided by `n!`. -/
theorem lintegral_weightedOrderedJumpTimes
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (hNonnegative : ∀ time, 0 ≤ weight time) (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ times : Fin n → ℝ in orderedJumpTimes n T,
        weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal ((∫ time in Ioo 0 T, weight time) ^ n / n.factorial) := by
  induction n generalizing T with
  | zero =>
      have hIntegrand : weightedOrderedJumpTimesIntegrand weight 0 = fun _ ↦ 1 := by
        funext times
        simp [weightedOrderedJumpTimesIntegrand]
      rw [hIntegrand]
      simp [volume_orderedJumpTimes 0 T hT]
  | succ n inductionHypothesis =>
      rw [lintegral_weightedOrderedJumpTimes_succ hContinuous.measurable]
      calc
        (∫⁻ lastTime : ℝ in Ioo 0 T,
            ENNReal.ofReal (weight lastTime) *
              ∫⁻ earlierTimes : Fin n → ℝ in orderedJumpTimes n lastTime,
                weightedOrderedJumpTimesIntegrand weight n earlierTimes) =
            ∫⁻ lastTime : ℝ in Ioo 0 T,
              ENNReal.ofReal
                (weight lastTime *
                  (∫ prior in (0 : ℝ)..lastTime, weight prior) ^ n / n.factorial) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with lastTime hLastTime
          rw [inductionHypothesis lastTime hLastTime.1.le]
          have hIntegralIdentity :
              (∫ prior in Ioo 0 lastTime, weight prior) =
                ∫ prior in (0 : ℝ)..lastTime, weight prior := by
            rw [← integral_Ioc_eq_integral_Ioo]
            rw [← intervalIntegral.integral_of_le hLastTime.1.le]
          rw [hIntegralIdentity]
          rw [← ENNReal.ofReal_mul (hNonnegative lastTime)]
          congr 1
          ring
        _ = ENNReal.ofReal
            ((∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) / (n + 1).factorial) :=
          lintegral_Ioo_weight_mul_intervalIntegral_pow_div_factorial
            hContinuous hNonnegative n T hT
        _ = ENNReal.ofReal
            ((∫ time in Ioo 0 T, weight time) ^ (n + 1) / (n + 1).factorial) := by
          congr 2
          rw [← integral_Ioc_eq_integral_Ioo]
          rw [← intervalIntegral.integral_of_le hT]

/-- The weighted ordered-simplex formula for measurable interval-integrable nonnegative
weights. -/
theorem lintegral_weightedOrderedJumpTimes_of_intervalIntegrable
    {weight : ℝ → ℝ} (hMeasurable : Measurable weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hIntegrable : IntervalIntegrable weight volume 0 T) :
    ∫⁻ times : Fin n → ℝ in orderedJumpTimes n T,
        weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal ((∫ time in Ioo 0 T, weight time) ^ n / n.factorial) := by
  induction n generalizing T with
  | zero =>
      have hIntegrand : weightedOrderedJumpTimesIntegrand weight 0 = fun _ ↦ 1 := by
        funext times
        simp [weightedOrderedJumpTimesIntegrand]
      rw [hIntegrand]
      simp [volume_orderedJumpTimes 0 T hT]
  | succ n inductionHypothesis =>
      rw [lintegral_weightedOrderedJumpTimes_succ hMeasurable]
      calc
        (∫⁻ lastTime : ℝ in Ioo 0 T,
            ENNReal.ofReal (weight lastTime) *
              ∫⁻ earlierTimes : Fin n → ℝ in orderedJumpTimes n lastTime,
                weightedOrderedJumpTimesIntegrand weight n earlierTimes) =
            ∫⁻ lastTime : ℝ in Ioo 0 T,
              ENNReal.ofReal
                (weight lastTime *
                  (∫ prior in (0 : ℝ)..lastTime, weight prior) ^ n / n.factorial) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with lastTime hLastTime
          have hIntegrableEarlier :
              IntervalIntegrable weight volume 0 lastTime := by
            apply IntervalIntegrable.mono_set' hIntegrable
            rw [uIoc_of_le hT, uIoc_of_le hLastTime.1.le]
            exact Ioc_subset_Ioc_right hLastTime.2.le
          rw [inductionHypothesis lastTime hLastTime.1.le hIntegrableEarlier]
          have hIntegralIdentity :
              (∫ prior in Ioo 0 lastTime, weight prior) =
                ∫ prior in (0 : ℝ)..lastTime, weight prior := by
            rw [← integral_Ioc_eq_integral_Ioo]
            rw [← intervalIntegral.integral_of_le hLastTime.1.le]
          rw [hIntegralIdentity]
          rw [← ENNReal.ofReal_mul (hNonnegative lastTime)]
          congr 1
          ring
        _ = ENNReal.ofReal
            ((∫ time in (0 : ℝ)..T, weight time) ^ (n + 1) /
              (n + 1).factorial) :=
          lintegral_Ioo_weight_mul_intervalIntegral_pow_div_factorial_of_intervalIntegrable
            T hIntegrable hNonnegative n hT
        _ = ENNReal.ofReal
            ((∫ time in Ioo 0 T, weight time) ^ (n + 1) / (n + 1).factorial) := by
          congr 2
          rw [← integral_Ioc_eq_integral_Ioo]
          rw [← intervalIntegral.integral_of_le hT]

/-- Summing the weighted ordered-simplex integral over every finite count gives the exponential
of the one-dimensional weight integral. -/
theorem tsum_lintegral_weightedOrderedJumpTimes
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (hNonnegative : ∀ time, 0 ≤ weight time) (T : ℝ) (hT : 0 ≤ T) :
    ∑' n : ℕ,
        ∫⁻ times : Fin n → ℝ in orderedJumpTimes n T,
          weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal (Real.exp (∫ time in Ioo 0 T, weight time)) := by
  simp_rw [lintegral_weightedOrderedJumpTimes hContinuous hNonnegative _ T hT]
  let totalWeight := ∫ time in Ioo 0 T, weight time
  have hTotalWeightNonnegative : 0 ≤ totalWeight := by
    unfold totalWeight
    exact integral_nonneg hNonnegative
  have hTermNonnegative (n : ℕ) :
      0 ≤ totalWeight ^ n / n.factorial :=
    div_nonneg (pow_nonneg hTotalWeightNonnegative n) (Nat.cast_nonneg n.factorial)
  have hSummable : Summable fun n : ℕ ↦ totalWeight ^ n / n.factorial :=
    (NormedSpace.expSeries_div_hasSum_exp totalWeight).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg hTermNonnegative hSummable]
  rw [(NormedSpace.expSeries_div_hasSum_exp totalWeight).tsum_eq]
  rw [← Real.exp_eq_exp_ℝ]

/-- The factorial-power formula transported to an arbitrary ordered open interval. -/
theorem lintegral_weightedOrderedTimesInInterval
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (n : ℕ) (lower upper : ℝ) (hBounds : lower ≤ upper) :
    ∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
        weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal ((∫ time in Ioo lower upper, weight time) ^ n / n.factorial) := by
  let translate : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun times ↦ times + fun _ ↦ lower
  let shiftedWeight : ℝ → ℝ := fun time ↦ weight (time + lower)
  have hTranslateMeasurable : Measurable translate := by
    fun_prop
  have hTranslatePreserving : MeasurePreserving translate volume volume := by
    refine ⟨hTranslateMeasurable, ?_⟩
    exact map_add_right_eq_self volume (fun _ : Fin n ↦ lower)
  have hOriginalMeasurable :
      Measurable (weightedOrderedJumpTimesIntegrand weight n) :=
    measurable_weightedOrderedJumpTimesIntegrand hContinuous.measurable n
  have hComposition (times : Fin n → ℝ) :
      weightedOrderedJumpTimesIntegrand weight n (translate times) =
        weightedOrderedJumpTimesIntegrand shiftedWeight n times := by
    unfold weightedOrderedJumpTimesIntegrand shiftedWeight translate
    apply Finset.prod_congr rfl
    intro index _hIndex
    rfl
  have hShiftIntegral :
      (∫ time in Ioo 0 (upper - lower), shiftedWeight time) =
        ∫ time in Ioo lower upper, weight time := by
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hBounds)]
    rw [intervalIntegral.integral_comp_add_right]
    rw [zero_add, sub_add_cancel]
    rw [intervalIntegral.integral_of_le hBounds]
    rw [integral_Ioc_eq_integral_Ioo]
  calc
    (∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
        weightedOrderedJumpTimesIntegrand weight n times) =
        ∫⁻ times : Fin n → ℝ in
          translate ⁻¹' orderedTimesInInterval n lower upper,
            weightedOrderedJumpTimesIntegrand weight n (translate times) := by
      exact (hTranslatePreserving.setLIntegral_comp_preimage
        (measurableSet_orderedTimesInInterval n lower upper) hOriginalMeasurable).symm
    _ = ∫⁻ times : Fin n → ℝ in orderedJumpTimes n (upper - lower),
          weightedOrderedJumpTimesIntegrand shiftedWeight n times := by
      rw [translate_preimage_orderedTimesInInterval]
      exact lintegral_congr hComposition
    _ = ENNReal.ofReal
        ((∫ time in Ioo 0 (upper - lower), shiftedWeight time) ^ n / n.factorial) := by
      exact lintegral_weightedOrderedJumpTimes
        (hContinuous.comp (continuous_id.add continuous_const))
        (fun time ↦ hNonnegative (time + lower)) n (upper - lower)
        (sub_nonneg.mpr hBounds)
    _ = _ := by rw [hShiftIntegral]

/-- The arbitrary-interval weighted ordered-simplex formula for measurable interval-integrable
nonnegative weights. -/
theorem lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
    {weight : ℝ → ℝ} (hMeasurable : Measurable weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (lower upper : ℝ)
    (hIntegrable : IntervalIntegrable weight volume lower upper)
    (n : ℕ) (hBounds : lower ≤ upper) :
    ∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
        weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal ((∫ time in Ioo lower upper, weight time) ^ n / n.factorial) := by
  let translate : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun times ↦ times + fun _ ↦ lower
  let shiftedWeight : ℝ → ℝ := fun time ↦ weight (time + lower)
  have hTranslateMeasurable : Measurable translate := by
    fun_prop
  have hTranslatePreserving : MeasurePreserving translate volume volume := by
    refine ⟨hTranslateMeasurable, ?_⟩
    exact map_add_right_eq_self volume (fun _ : Fin n ↦ lower)
  have hOriginalMeasurable :
      Measurable (weightedOrderedJumpTimesIntegrand weight n) :=
    measurable_weightedOrderedJumpTimesIntegrand hMeasurable n
  have hShiftedMeasurable : Measurable shiftedWeight :=
    hMeasurable.comp (measurable_id.add_const lower)
  have hShiftedIntegrable :
      IntervalIntegrable shiftedWeight volume 0 (upper - lower) := by
    simpa [shiftedWeight] using hIntegrable.comp_add_right lower
  have hComposition (times : Fin n → ℝ) :
      weightedOrderedJumpTimesIntegrand weight n (translate times) =
        weightedOrderedJumpTimesIntegrand shiftedWeight n times := by
    unfold weightedOrderedJumpTimesIntegrand shiftedWeight translate
    apply Finset.prod_congr rfl
    intro index _hIndex
    rfl
  have hShiftIntegral :
      (∫ time in Ioo 0 (upper - lower), shiftedWeight time) =
        ∫ time in Ioo lower upper, weight time := by
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (sub_nonneg.mpr hBounds)]
    rw [intervalIntegral.integral_comp_add_right]
    rw [zero_add, sub_add_cancel]
    rw [intervalIntegral.integral_of_le hBounds]
    rw [integral_Ioc_eq_integral_Ioo]
  calc
    (∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
        weightedOrderedJumpTimesIntegrand weight n times) =
        ∫⁻ times : Fin n → ℝ in
          translate ⁻¹' orderedTimesInInterval n lower upper,
            weightedOrderedJumpTimesIntegrand weight n (translate times) := by
      exact (hTranslatePreserving.setLIntegral_comp_preimage
        (measurableSet_orderedTimesInInterval n lower upper) hOriginalMeasurable).symm
    _ = ∫⁻ times : Fin n → ℝ in orderedJumpTimes n (upper - lower),
          weightedOrderedJumpTimesIntegrand shiftedWeight n times := by
      rw [translate_preimage_orderedTimesInInterval]
      exact lintegral_congr hComposition
    _ = ENNReal.ofReal
        ((∫ time in Ioo 0 (upper - lower), shiftedWeight time) ^ n / n.factorial) := by
      exact lintegral_weightedOrderedJumpTimes_of_intervalIntegrable
        hShiftedMeasurable (fun time ↦ hNonnegative (time + lower)) n
        (upper - lower) (sub_nonneg.mpr hBounds) hShiftedIntegrable
    _ = _ := by rw [hShiftIntegral]

/-- Summing the weighted ordered-simplex integrals over every count on an arbitrary interval gives
the exponential of the one-dimensional interval weight. -/
theorem tsum_lintegral_weightedOrderedTimesInInterval
    {weight : ℝ → ℝ} (hContinuous : Continuous weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (lower upper : ℝ) (hBounds : lower ≤ upper) :
    ∑' n : ℕ,
        ∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
          weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal (Real.exp (∫ time in Ioo lower upper, weight time)) := by
  simp_rw [lintegral_weightedOrderedTimesInInterval
    hContinuous hNonnegative _ lower upper hBounds]
  let totalWeight := ∫ time in Ioo lower upper, weight time
  have hTotalWeightNonnegative : 0 ≤ totalWeight := integral_nonneg hNonnegative
  have hTermNonnegative (n : ℕ) :
      0 ≤ totalWeight ^ n / n.factorial :=
    div_nonneg (pow_nonneg hTotalWeightNonnegative n) (Nat.cast_nonneg n.factorial)
  have hSummable : Summable fun n : ℕ ↦ totalWeight ^ n / n.factorial :=
    (NormedSpace.expSeries_div_hasSum_exp totalWeight).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg hTermNonnegative hSummable]
  rw [(NormedSpace.expSeries_div_hasSum_exp totalWeight).tsum_eq]
  rw [← Real.exp_eq_exp_ℝ]

/-- Measurable interval-integrable nonnegative weights have the same arbitrary-interval
exponential resummation. -/
theorem tsum_lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
    {weight : ℝ → ℝ} (hMeasurable : Measurable weight)
    (hNonnegative : ∀ time, 0 ≤ weight time)
    (lower upper : ℝ) (hIntegrable : IntervalIntegrable weight volume lower upper)
    (hBounds : lower ≤ upper) :
    ∑' n : ℕ,
        ∫⁻ times : Fin n → ℝ in orderedTimesInInterval n lower upper,
          weightedOrderedJumpTimesIntegrand weight n times =
      ENNReal.ofReal (Real.exp (∫ time in Ioo lower upper, weight time)) := by
  simp_rw [lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
    hMeasurable hNonnegative lower upper hIntegrable _ hBounds]
  let totalWeight := ∫ time in Ioo lower upper, weight time
  have hTotalWeightNonnegative : 0 ≤ totalWeight := integral_nonneg hNonnegative
  have hTermNonnegative (n : ℕ) :
      0 ≤ totalWeight ^ n / n.factorial :=
    div_nonneg (pow_nonneg hTotalWeightNonnegative n) (Nat.cast_nonneg n.factorial)
  have hSummable : Summable fun n : ℕ ↦ totalWeight ^ n / n.factorial :=
    (NormedSpace.expSeries_div_hasSum_exp totalWeight).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg hTermNonnegative hSummable]
  rw [(NormedSpace.expSeries_div_hasSum_exp totalWeight).tsum_eq]
  rw [← Real.exp_eq_exp_ℝ]

end FiniteMarkovProcesses.Probability
