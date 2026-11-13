/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteOpenIntervalContinuousTestDense
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDualEvaluation
public import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality

/-!
# Continuous Poisson duality for singular finite measures

This module begins the measure-level extension of the finite-state directional-flow dual.  The
carried flow is a finite positive measure rather than an already supplied Lebesgue density.  A
reference-null event carrying positive flow can be approximated by relative continuous tests,
with the carried and reference errors controlled separately.

The declarations are source-neutral and do not assert a path large-deviation principle.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open _root_.MeasureTheory Set
open scoped ENNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.MeasureTheory.Integrable

noncomputable section

/-- One measure-level Poisson dual evaluation against a relative continuous test. -/
noncomputable def poissonMeasureContinuousDualEvaluation
    {duration : ℝ} (carried reference : Measure ℝ)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) : ℝ :=
  (∫ time, test.1 time ∂carried) -
    ∫ time, (Real.exp (test.1 time) - 1) ∂reference

/-- Supremum of the nonnegative embeddings of all measure-level continuous Poisson dual
evaluations. -/
noncomputable def poissonMeasureContinuousDualRate
    {duration : ℝ} (carried reference : Measure ℝ) : ENNReal :=
  ⨆ test : FiniteOpenIntervalVanishingContinuousTest duration,
    ENNReal.ofReal (poissonMeasureContinuousDualEvaluation carried reference test)

/-- Scaling preserves the relative continuous-test carrier. -/
noncomputable def scaledFiniteOpenIntervalVanishingContinuousTest
    {duration : ℝ} (scale : ℝ) (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    FiniteOpenIntervalVanishingContinuousTest duration :=
  ⟨scale • test.1, by
    intro time hTime
    change scale * test.1 time = 0
    rw [test.property hTime]
    simp⟩

/-- Evaluating a scaled relative continuous test multiplies its value by the same scalar. -/
@[simp]
theorem scaledFiniteOpenIntervalVanishingContinuousTest_apply
    {duration scale time : ℝ} (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    (scaledFiniteOpenIntervalVanishingContinuousTest scale test).1 time = scale * test.1 time :=
  rfl

/-- A reference-null event yields a scaled continuous test whose measure-level Poisson dual
evaluation has the explicit carried-mass lower bound. -/
theorem exists_poissonMeasureContinuousDualEvaluation_ge_of_referenceNull
    {duration : ℝ} (hDuration : 0 < duration)
    {carried reference : Measure ℝ} [IsFiniteMeasure carried] [IsFiniteMeasure reference]
    {event : Set ℝ} (hEvent : MeasurableSet event) (hReferenceNull : reference event = 0)
    (hCarriedPhysical : ∀ᵐ time ∂carried, time ∈ Ioo 0 duration)
    (hReferencePhysical : ∀ᵐ time ∂reference, time ∈ Ioo 0 duration)
    (scale : ℝ) (hScale : 0 ≤ scale) {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      poissonMeasureContinuousDualEvaluation carried reference test ≥
        scale * (carried.real event - epsilon) - Real.exp scale * scale * epsilon := by
  obtain ⟨test, hTestRange, hCarriedError, hReferenceError⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_singularIndicator_errors_lt
      hDuration hEvent hReferenceNull hCarriedPhysical hReferencePhysical hEpsilon
  let scaledTest := scaledFiniteOpenIntervalVanishingContinuousTest scale test
  refine ⟨scaledTest, ?_⟩
  let indicator : ℝ → ℝ := event.indicator fun _ => 1
  have hIndicatorIntegrable : Integrable indicator carried :=
    (integrable_const (1 : ℝ)).indicator hEvent
  have hTestIntegrableCarried : Integrable (fun time => test.1 time) carried :=
    test.1.integrable
  have hIndicatorIntegral :
      (∫ time, indicator time ∂carried) = carried.real event := by
    simp [indicator, hEvent]
  have hIntegralDifference :
      |carried.real event - ∫ time, test.1 time ∂carried| < epsilon := by
    calc
      |carried.real event - ∫ time, test.1 time ∂carried| =
          |∫ time, (indicator time - test.1 time) ∂carried| := by
        rw [integral_sub hIndicatorIntegrable hTestIntegrableCarried,
          hIndicatorIntegral]
      _ ≤ ∫ time, |indicator time - test.1 time| ∂carried := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (fun time => indicator time - test.1 time)
      _ < epsilon := hCarriedError
  have hCarriedIntegralLower :
      carried.real event - epsilon ≤ ∫ time, test.1 time ∂carried := by
    linarith [le_abs_self (carried.real event - ∫ time, test.1 time ∂carried)]
  have hCompensatorIntegrable : Integrable
      (fun time => Real.exp (scale * test.1 time) - 1) reference := by
    refine ((rengerDirectionalFlowHybridBVHamiltonianWeight scaledTest).integrable
      (μ := reference)).congr ?_
    filter_upwards with time
    rw [rengerDirectionalFlowHybridBVHamiltonianWeight_apply]
    rfl
  have hCompensatorPointwise (time : ℝ) :
      |Real.exp (scale * test.1 time) - 1| ≤
        Real.exp scale * scale * |test.1 time| := by
    have hScaledRange : scale * test.1 time ∈ Icc (-scale) scale := by
      have hRange := hTestRange time
      constructor
      · simpa only [mul_neg, mul_one] using
          mul_le_mul_of_nonneg_left hRange.1 hScale
      · simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hRange.2 hScale
    have hZeroRange : (0 : ℝ) ∈ Icc (-scale) scale :=
      ⟨neg_nonpos.mpr hScale, hScale⟩
    have hExponential :=
      abs_exp_sub_exp_le_exp_mul_abs_sub_of_mem_Icc hScaledRange hZeroRange
    rw [Real.exp_zero, sub_zero, abs_mul, abs_of_nonneg hScale] at hExponential
    simpa only [mul_assoc] using hExponential
  have hCompensatorUpper :
      (∫ time, (Real.exp (scale * test.1 time) - 1) ∂reference) ≤
        Real.exp scale * scale * epsilon := by
    calc
      (∫ time, (Real.exp (scale * test.1 time) - 1) ∂reference) ≤
          |∫ time, (Real.exp (scale * test.1 time) - 1) ∂reference| :=
        le_abs_self _
      _ ≤ ∫ time, |Real.exp (scale * test.1 time) - 1| ∂reference := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (fun time => Real.exp (scale * test.1 time) - 1)
      _ ≤ ∫ time, Real.exp scale * scale * |test.1 time| ∂reference := by
        apply integral_mono
        · simpa only [Real.norm_eq_abs] using hCompensatorIntegrable.norm
        · exact (test.1.integrable.norm.const_mul _)
        · exact hCompensatorPointwise
      _ = Real.exp scale * scale *
          (∫ time, |test.1 time| ∂reference) := by
        rw [integral_const_mul]
      _ ≤ Real.exp scale * scale * epsilon := by
        gcongr
  unfold poissonMeasureContinuousDualEvaluation
  simp only [scaledTest,
    scaledFiniteOpenIntervalVanishingContinuousTest_apply]
  rw [integral_const_mul]
  nlinarith [Real.exp_pos scale]

/-- A positive carried mass on a reference-null event makes the continuous Poisson dual rate
infinite. -/
theorem poissonMeasureContinuousDualRate_eq_top_of_referenceNull
    {duration : ℝ} (hDuration : 0 < duration)
    {carried reference : Measure ℝ} [IsFiniteMeasure carried] [IsFiniteMeasure reference]
    {event : Set ℝ} (hEvent : MeasurableSet event) (hReferenceNull : reference event = 0)
    (hCarriedNonzero : carried event ≠ 0)
    (hCarriedPhysical : ∀ᵐ time ∂carried, time ∈ Ioo 0 duration)
    (hReferencePhysical : ∀ᵐ time ∂reference, time ∈ Ioo 0 duration) :
    poissonMeasureContinuousDualRate (duration := duration) carried reference = ∞ := by
  have hMassNonzero : carried.real event ≠ 0 := by
    rwa [measureReal_ne_zero_iff]
  have hMassPositive : 0 < carried.real event :=
    lt_of_le_of_ne measureReal_nonneg
      (Ne.symm hMassNonzero)
  refine ENNReal.eq_top_of_forall_nnreal_le fun target => ?_
  let scale : ℝ := 2 * ((target : ℝ) + 1) / carried.real event
  have hScalePositive : 0 < scale := by
    dsimp [scale]
    positivity
  let epsilon : ℝ :=
    carried.real event / (2 * (1 + Real.exp scale))
  have hEpsilonPositive : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨test, hEvaluation⟩ :=
    exists_poissonMeasureContinuousDualEvaluation_ge_of_referenceNull
      hDuration hEvent hReferenceNull hCarriedPhysical hReferencePhysical
      scale hScalePositive.le hEpsilonPositive
  have hLowerIdentity :
      scale * (carried.real event - epsilon) -
          Real.exp scale * scale * epsilon = (target : ℝ) + 1 := by
    dsimp [scale, epsilon]
    field_simp
    ring
  have hTargetEvaluation :
      (target : ℝ) ≤ poissonMeasureContinuousDualEvaluation carried reference test := by
    rw [hLowerIdentity] at hEvaluation
    linarith
  calc
    (target : ENNReal) = ENNReal.ofReal (target : ℝ) := by simp
    _ ≤ ENNReal.ofReal (poissonMeasureContinuousDualEvaluation carried reference test) :=
      ENNReal.ofReal_le_ofReal hTargetEvaluation
    _ ≤ poissonMeasureContinuousDualRate carried reference := by
      exact le_iSup (fun test : FiniteOpenIntervalVanishingContinuousTest duration =>
        ENNReal.ofReal (poissonMeasureContinuousDualEvaluation carried reference test)) test

/-- Failure of absolute continuity is exactly enough to force an infinite continuous Poisson
dual rate on measures carried by the physical open interval. -/
theorem poissonMeasureContinuousDualRate_eq_top_of_not_absolutelyContinuous
    {duration : ℝ} (hDuration : 0 < duration)
    {carried reference : Measure ℝ} [IsFiniteMeasure carried] [IsFiniteMeasure reference]
    (hNotAbsolutelyContinuous : ¬ carried ≪ reference)
    (hCarriedPhysical : ∀ᵐ time ∂carried, time ∈ Ioo 0 duration)
    (hReferencePhysical : ∀ᵐ time ∂reference, time ∈ Ioo 0 duration) :
    poissonMeasureContinuousDualRate (duration := duration) carried reference = ∞ := by
  have hWitness : ∃ event : Set ℝ,
      MeasurableSet event ∧ reference event = 0 ∧ carried event ≠ 0 := by
    by_contra hNoWitness
    apply hNotAbsolutelyContinuous
    apply Measure.AbsolutelyContinuous.mk
    intro event hEvent hReferenceNull
    by_contra hCarriedNonzero
    exact hNoWitness ⟨event, hEvent, hReferenceNull, hCarriedNonzero⟩
  obtain ⟨event, hEvent, hReferenceNull, hCarriedNonzero⟩ := hWitness
  exact poissonMeasureContinuousDualRate_eq_top_of_referenceNull
    hDuration hEvent hReferenceNull hCarriedNonzero hCarriedPhysical hReferencePhysical

end

end FiniteMarkovProcesses.InformationTheory
