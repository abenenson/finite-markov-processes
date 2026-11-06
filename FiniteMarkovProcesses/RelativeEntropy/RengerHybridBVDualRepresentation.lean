/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteOpenIntervalContinuousTestDense
import FiniteMarkovProcesses.MeasureTheory.Integral.OfRealIntegral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Renger hybrid-BV dual representation

This module proves the converse variational inequality for the directional-flow action on its
licensed finite-rate representation domain.  The first layer constructs a bounded measurable
pointwise exponent that treats both singular zero-intensity sectors explicitly.

## Main results

* `boundedPoissonOptimalExponent` truncates the exact pointwise exponential-dual optimizer.
* `measurable_boundedPoissonOptimalExponent` proves joint Borel measurability.
* `poissonExponentialDualEvaluation_boundedPoissonOptimalExponent_nonneg` proves that every
  truncated evaluation is nonnegative.
* `tendsto_ofReal_poissonExponentialDualEvaluation_boundedPoissonOptimalExponent` recovers the
  extended Poisson cost as the truncation radius diverges.
* `lintegral_rengerExtendedPoissonRateCost_le_liminf_boundedPoissonDualEvaluation` passes the
  pointwise convergence through an arbitrary measure by Fatou's lemma.
* `exists_finiteOpenIntervalVanishingContinuousTest_weighted_boundedPoissonOptimalExponent`
  approximates each bounded optimizer in the exact flow/reference weighted norm.
* `exists_finiteOpenIntervalVanishingContinuousTest_integral_abs_poissonDual_sub_lt` converts
  that weighted approximation into convergence of the integrated nonlinear dual evaluation.
* `integrable_poissonExponentialDualEvaluation_of_bounded_exponent` supplies the generic
  bounded-test integrability needed to form one-channel dual suprema.
* `boundedPoissonOptimalExponent_integral_le_continuousDualRate` embeds every truncated
  pointwise optimizer into the relative continuous-test supremum.
* `oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost` proves exact integrated
  one-channel duality, including both singular zero-rate sectors.
* `oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost_of_aemeasurable` supplies the
  almost-everywhere measurable interface needed by hybrid-BV representatives.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open FiniteMarkovProcesses.MeasureTheory.Integrable
open _root_.MeasureTheory
open Set
open scoped BoundedContinuousFunction ENNReal Topology

noncomputable section

/-- Bounded pointwise optimizer for the Poisson exponential dual.  Zero observed flow moves
toward the negative boundary; positive flow against zero reference moves toward the positive
boundary; the positive--positive logarithmic optimizer is projected into the same interval. -/
noncomputable def boundedPoissonOptimalExponent
    (bound : ℝ) (flow expected : NNReal) : ℝ :=
  if flow = 0 then -bound
  else if expected = 0 then bound
  else max (-bound) (min bound (Real.log ((flow : ℝ) / (expected : ℝ))))

/-- The bounded pointwise optimizer is jointly Borel measurable in observed and expected
intensity. -/
theorem measurable_boundedPoissonOptimalExponent (bound : ℝ) :
    Measurable fun intensities : NNReal × NNReal =>
      boundedPoissonOptimalExponent bound intensities.1 intensities.2 := by
  unfold boundedPoissonOptimalExponent
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_fst measurable_const
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_eq_fun measurable_snd measurable_const
    · exact measurable_const
    · exact measurable_const.max <| measurable_const.min <|
        Real.measurable_log.comp <|
          (measurable_coe_nnreal_real.comp measurable_fst).div <|
            measurable_coe_nnreal_real.comp measurable_snd

/-- A nonnegative truncation radius keeps the pointwise optimizer in its symmetric closed
interval. -/
theorem boundedPoissonOptimalExponent_mem_Icc
    (bound : ℝ) (hBound : 0 ≤ bound) (flow expected : NNReal) :
    boundedPoissonOptimalExponent bound flow expected ∈ Set.Icc (-bound) bound := by
  by_cases hFlow : flow = 0
  · simp [boundedPoissonOptimalExponent, hFlow, hBound]
  · by_cases hExpected : expected = 0
    · simp [boundedPoissonOptimalExponent, hFlow, hExpected, hBound]
    · rw [boundedPoissonOptimalExponent, ite_eq_right hFlow, ite_eq_right hExpected]
      exact ⟨le_max_left _ _, max_le (neg_le_self hBound) (min_le_left _ _)⟩

/-- Symmetric truncation of a real exponent lies on the unoriented interval joining zero to that
exponent. -/
theorem max_neg_min_mem_uIcc_zero
    (bound exponent : ℝ) (hBound : 0 ≤ bound) :
    max (-bound) (min bound exponent) ∈ Set.uIcc 0 exponent := by
  by_cases hExponent : 0 ≤ exponent
  · rw [uIcc_of_le hExponent]
    constructor
    · exact (le_min hBound hExponent).trans (le_max_right _ _)
    · exact max_le (neg_nonpos.mpr hBound |>.trans hExponent) (min_le_right _ _)
  · have hExponentNonpositive : exponent ≤ 0 := le_of_not_ge hExponent
    rw [uIcc_of_ge hExponentNonpositive]
    constructor
    · exact
        (le_min (hExponentNonpositive.trans hBound) le_rfl).trans
          (le_max_right _ _)
    · exact max_le (neg_nonpos.mpr hBound)
        ((min_le_right bound exponent).trans hExponentNonpositive)

/-- The one-channel exponential dual evaluation is concave in its exponent whenever the expected
intensity is nonnegative. -/
theorem concaveOn_poissonExponentialDualEvaluation
    {flow expected : ℝ} (hExpected : 0 ≤ expected) :
    ConcaveOn ℝ Set.univ
      (poissonExponentialDualEvaluation flow expected) := by
  have hLinear :
      ConcaveOn ℝ Set.univ (fun exponent : ℝ => flow * exponent) := by
    simpa only [mul_comm] using!
      (LinearMap.mul ℝ ℝ flow).concaveOn convex_univ
  have hExponential :
      ConvexOn ℝ Set.univ
        (fun exponent : ℝ => expected * (Real.exp exponent - 1)) := by
    have hScaled := ConvexOn.smul hExpected convexOn_exp
    have hShifted := hScaled.add_const (-expected)
    convert hShifted using 1
    ext exponent
    dsimp
    ring
  exact hLinear.sub hExponential

/-- Every nonnegative truncation of the pointwise Poisson optimizer has a nonnegative exponential
dual evaluation. -/
theorem poissonExponentialDualEvaluation_boundedPoissonOptimalExponent_nonneg
    (bound : ℝ) (hBound : 0 ≤ bound) (flow expected : NNReal) :
    0 ≤ poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ)
      (boundedPoissonOptimalExponent bound flow expected) := by
  by_cases hFlow : flow = 0
  · subst flow
    simp only [boundedPoissonOptimalExponent, ↓reduceIte, NNReal.coe_zero]
    have hExp : Real.exp (-bound) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hBound)
    have hExpected : 0 ≤ (expected : ℝ) := expected.coe_nonneg
    unfold poissonExponentialDualEvaluation
    nlinarith
  · have hFlowPositive : 0 < (flow : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hFlow)
    by_cases hExpected : expected = 0
    · subst expected
      simpa only [boundedPoissonOptimalExponent, hFlow, ↓reduceIte, NNReal.coe_zero,
        poissonExponentialDualEvaluation, zero_mul, sub_zero] using
          mul_nonneg hFlowPositive.le hBound
    · have hExpectedPositive : 0 < (expected : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hExpected)
      let optimizer := Real.log ((flow : ℝ) / (expected : ℝ))
      have hSegment :
          boundedPoissonOptimalExponent bound flow expected ∈
            segment ℝ 0 optimizer := by
        rw [segment_eq_uIcc]
        simpa only [boundedPoissonOptimalExponent, hFlow, hExpected, ite_false,
          optimizer] using
            max_neg_min_mem_uIcc_zero bound optimizer hBound
      have hConcavity :=
        concaveOn_poissonExponentialDualEvaluation (flow := (flow : ℝ))
          hExpectedPositive.le
      have hEndpoint := hConcavity.min_le_of_mem_segment
        (Set.mem_univ 0) (Set.mem_univ optimizer) hSegment
      have hDiscrimination :
          0 ≤ poissonRateDiscrimination (flow : ℝ) (expected : ℝ) :=
        poissonRateDiscrimination_nonneg hFlowPositive.le hExpectedPositive
      rw [show poissonExponentialDualEvaluation
            (flow : ℝ) (expected : ℝ) 0 = 0 by
          simp [poissonExponentialDualEvaluation],
        poissonExponentialDualEvaluation_eq_discrimination_at_log_ratio
          hFlowPositive hExpectedPositive,
        min_eq_left hDiscrimination] at hEndpoint
      exact hEndpoint

/-- The nonnegative truncated evaluations converge to the exact extended Poisson cost as the
natural truncation radius diverges.  The limit is finite in the zero-flow sector, infinite for
positive flow against zero reference, and eventually attained in the positive--positive
sector. -/
theorem
    tendsto_ofReal_poissonExponentialDualEvaluation_boundedPoissonOptimalExponent
    (flow expected : NNReal) :
    Tendsto (fun index : ℕ =>
      ENNReal.ofReal
        (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ)
          (boundedPoissonOptimalExponent (index : ℝ) flow expected)))
      atTop (nhds (rengerExtendedPoissonRateCost flow expected)) := by
  by_cases hFlow : flow = 0
  · subst flow
    by_cases hExpected : expected = 0
    · subst expected
      simp [boundedPoissonOptimalExponent, poissonExponentialDualEvaluation,
        rengerExtendedPoissonRateCost]
    · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
      rw [rengerExtendedPoissonRateCost_of_expected_pos 0 hExpectedPositive]
      have hRealTendsto : Tendsto
          (fun index : ℕ =>
            poissonExponentialDualEvaluation 0 (expected : ℝ)
              (boundedPoissonOptimalExponent (index : ℝ) 0 expected))
          atTop (nhds (expected : ℝ)) := by
        convert
          (tendsto_const_nhds.mul
            (tendsto_const_nhds.sub
              (Real.tendsto_exp_neg_atTop_nhds_zero.comp
                tendsto_natCast_atTop_atTop)) :
              Tendsto (fun index : ℕ =>
                (expected : ℝ) * (1 - Real.exp (-(index : ℝ))))
                atTop (nhds ((expected : ℝ) * (1 - 0)))) using 1
        · funext index
          simp only [boundedPoissonOptimalExponent, ↓reduceIte]
          unfold poissonExponentialDualEvaluation
          ring
        · congr 1
          ring
      simpa [poissonRateDiscrimination] using
        ENNReal.tendsto_ofReal hRealTendsto
  · have hFlowPositive : 0 < flow := pos_iff_ne_zero.mpr hFlow
    by_cases hExpected : expected = 0
    · subst expected
      rw [rengerExtendedPoissonRateCost_pos_zero hFlowPositive]
      rw [ENNReal.tendsto_ofReal_nhds_top]
      simpa only [boundedPoissonOptimalExponent, hFlow, ↓reduceIte,
        NNReal.coe_zero, poissonExponentialDualEvaluation, zero_mul, sub_zero] using
          tendsto_natCast_atTop_atTop.const_mul_atTop
            (show 0 < (flow : ℝ) by exact_mod_cast hFlowPositive)
    · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
      rw [rengerExtendedPoissonRateCost_of_expected_pos flow hExpectedPositive]
      let optimizer := Real.log ((flow : ℝ) / (expected : ℝ))
      have hEventually : ∀ᶠ index : ℕ in atTop,
          |optimizer| ≤ (index : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually
          (eventually_ge_atTop |optimizer|)
      have hEvaluationEventually :
          (fun index : ℕ =>
            ENNReal.ofReal
              (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ)
                (boundedPoissonOptimalExponent
                  (index : ℝ) flow expected))) =ᶠ[atTop]
          (fun _ : ℕ =>
            ENNReal.ofReal
              (poissonRateDiscrimination (flow : ℝ) (expected : ℝ))) := by
        filter_upwards [hEventually] with index hIndex
        have hOptimizerUpper : optimizer ≤ (index : ℝ) :=
          (le_abs_self optimizer).trans hIndex
        have hOptimizerLower : -(index : ℝ) ≤ optimizer := by
          have hLower := (neg_le_abs optimizer).trans hIndex
          linarith
        rw [boundedPoissonOptimalExponent, ite_eq_right hFlow, ite_eq_right hExpected,
          min_eq_right hOptimizerUpper, max_eq_right hOptimizerLower]
        exact congrArg ENNReal.ofReal <|
          poissonExponentialDualEvaluation_eq_discrimination_at_log_ratio
            (by exact_mod_cast hFlowPositive)
            (by exact_mod_cast hExpectedPositive)
      exact tendsto_const_nhds.congr' hEvaluationEventually.symm

/-- The nonnegative extended-real evaluation at the bounded pointwise optimizer. -/
noncomputable def boundedPoissonDualEvaluation
    (bound : ℝ) (flow expected : NNReal) : ENNReal :=
  ENNReal.ofReal
    (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ)
      (boundedPoissonOptimalExponent bound flow expected))

/-- Bounded optimized Poisson dual evaluation is jointly Borel measurable in its two
intensities. -/
theorem measurable_boundedPoissonDualEvaluation (bound : ℝ) :
    Measurable fun intensities : NNReal × NNReal =>
      boundedPoissonDualEvaluation bound intensities.1 intensities.2 := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.sub
  · exact (measurable_coe_nnreal_real.comp measurable_fst).mul <|
      measurable_boundedPoissonOptimalExponent bound
  · exact (measurable_coe_nnreal_real.comp measurable_snd).mul <|
      (Real.measurable_exp.comp
        (measurable_boundedPoissonOptimalExponent bound)).sub measurable_const

/-- Fatou's lemma transports pointwise bounded-optimizer convergence through an arbitrary
measure.  This is the integral limiting direction needed by the converse dual representation. -/
theorem
    lintegral_rengerExtendedPoissonRateCost_le_liminf_boundedPoissonDualEvaluation
    {Carrier : Type*} [MeasurableSpace Carrier]
    (measure : Measure Carrier)
    (flow expected : Carrier → NNReal)
    (hFlow : Measurable flow) (hExpected : Measurable expected) :
    (∫⁻ point,
      rengerExtendedPoissonRateCost (flow point) (expected point) ∂measure) ≤
      liminf (fun index : ℕ =>
        ∫⁻ point,
          boundedPoissonDualEvaluation (index : ℝ)
            (flow point) (expected point) ∂measure) atTop := by
  have hMeasurable (index : ℕ) :
      Measurable fun point =>
        boundedPoissonDualEvaluation (index : ℝ)
          (flow point) (expected point) :=
    (measurable_boundedPoissonDualEvaluation (index : ℝ)).comp
      (hFlow.prodMk hExpected)
  have hFatou := lintegral_liminf_le
    (μ := measure) (ι := ℕ) (u := atTop) (f := fun index point =>
      boundedPoissonDualEvaluation (index : ℝ)
        (flow point) (expected point)) hMeasurable
  have hPointwise :
      (fun point =>
        liminf (fun index : ℕ =>
          boundedPoissonDualEvaluation (index : ℝ)
            (flow point) (expected point)) atTop) =
        fun point =>
          rengerExtendedPoissonRateCost (flow point) (expected point) := by
    funext point
    exact
      (tendsto_ofReal_poissonExponentialDualEvaluation_boundedPoissonOptimalExponent
        (flow point) (expected point)).liminf_eq
  rw [hPointwise] at hFatou
  exact hFatou

/-- Weight controlling the nonlinear change in one Poisson dual evaluation when its bounded
exponent changes. -/
noncomputable def poissonDualApproximationWeight
    (bound : ℝ) (flow expected : NNReal) : ℝ :=
  (flow : ℝ) + (expected : ℝ) * Real.exp bound

/-- On one symmetric bounded interval, the change in Poisson dual evaluation is controlled by
the flow/reference approximation weight times the change in exponent. -/
theorem abs_poissonExponentialDualEvaluation_sub_le_approximationWeight
    {bound flow expected target approximation : ℝ}
    (hFlow : 0 ≤ flow) (hExpected : 0 ≤ expected)
    (hTarget : target ∈ Set.Icc (-bound) bound)
    (hApproximation : approximation ∈ Set.Icc (-bound) bound) :
    |poissonExponentialDualEvaluation flow expected target -
        poissonExponentialDualEvaluation flow expected approximation| ≤
      (flow + expected * Real.exp bound) * |target - approximation| := by
  have hExponential :=
    abs_exp_sub_exp_le_exp_mul_abs_sub_of_mem_Icc
      hTarget hApproximation
  unfold poissonExponentialDualEvaluation
  calc
    |(flow * target - expected * (Real.exp target - 1)) -
        (flow * approximation - expected * (Real.exp approximation - 1))| =
        |flow * (target - approximation) -
          expected * (Real.exp target - Real.exp approximation)| := by
      congr 1
      ring
    _ ≤ |flow * (target - approximation)| +
        |expected * (Real.exp target - Real.exp approximation)| := abs_sub _ _
    _ = flow * |target - approximation| +
        expected * |Real.exp target - Real.exp approximation| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hFlow, abs_of_nonneg hExpected]
    _ ≤ flow * |target - approximation| +
        expected * (Real.exp bound * |target - approximation|) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hExponential hExpected)
    _ = (flow + expected * Real.exp bound) *
        |target - approximation| := by
      ring

/-- Every bounded measurable Poisson optimizer admits arbitrary approximation by a relative
continuous test in the exact weighted norm controlling both the linear flow term and nonlinear
exponential compensator. -/
theorem
    exists_finiteOpenIntervalVanishingContinuousTest_weighted_boundedPoissonOptimalExponent
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ}
    (flow expected : ℝ → NNReal)
    (hFlowMeasurable : Measurable flow)
    (hExpectedMeasurable : Measurable expected)
    (hFlowIntegrable : Integrable (fun time => (flow time : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun time => (expected time : ℝ)) measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration)
    (bound : ℝ) (hBound : 0 ≤ bound)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ time, test.1 time ∈ Set.Icc (-bound) bound) ∧
        ∫ time,
          poissonDualApproximationWeight bound (flow time) (expected time) *
            |boundedPoissonOptimalExponent bound (flow time) (expected time) -
              test.1 time| ∂measure < epsilon := by
  let weight : ℝ → ℝ := fun time =>
    poissonDualApproximationWeight bound (flow time) (expected time)
  have hWeightNonnegative (time : ℝ) : 0 ≤ weight time := by
    dsimp only [weight, poissonDualApproximationWeight]
    positivity
  have hWeightMeasurable : Measurable weight := by
    dsimp only [weight, poissonDualApproximationWeight]
    fun_prop
  have hWeightIntegrable : Integrable weight measure := by
    dsimp only [weight, poissonDualApproximationWeight]
    exact hFlowIntegrable.add
      (hExpectedIntegrable.mul_const (Real.exp bound))
  have hDensityMeasurable :
      Measurable (fun time => ENNReal.ofReal (weight time)) :=
    ENNReal.measurable_ofReal.comp hWeightMeasurable
  let weightedMeasure : Measure ℝ :=
    measure.withDensity fun time => ENNReal.ofReal (weight time)
  let : IsFiniteMeasure weightedMeasure := by
    unfold weightedMeasure
    exact isFiniteMeasure_withDensity_ofReal
      hWeightIntegrable.hasFiniteIntegral
  let target : ℝ → ℝ := fun time =>
    boundedPoissonOptimalExponent bound (flow time) (expected time)
  have hTargetMeasurable : Measurable target := by
    dsimp only [target]
    exact (measurable_boundedPoissonOptimalExponent bound).comp
      (hFlowMeasurable.prodMk hExpectedMeasurable)
  have hTargetIntegrable : Integrable target weightedMeasure := by
    apply Integrable.of_bound hTargetMeasurable.aestronglyMeasurable bound
    apply Filter.Eventually.of_forall
    intro time
    rw [Real.norm_eq_abs]
    exact abs_le.mpr
      (boundedPoissonOptimalExponent_mem_Icc
        bound hBound (flow time) (expected time))
  have hPhysicalWeighted :
      ∀ᵐ time ∂weightedMeasure, time ∈ Set.Ioo 0 duration :=
    (withDensity_absolutelyContinuous measure _).ae_le hPhysical
  obtain ⟨rawTest, hRawError⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_integral_norm_sub_lt
      hDuration hTargetIntegrable hPhysicalWeighted hEpsilon
  let test := rawTest.symmetricClamp bound hBound
  refine ⟨test, ?_, ?_⟩
  · exact fun time =>
      FiniteOpenIntervalVanishingContinuousTest.symmetricClamp_mem_Icc
        bound hBound rawTest time
  have hRawTestIntegrable :
      Integrable (fun time => rawTest.1 time) weightedMeasure := by
    exact Continuous.integrable_of_hasCompactSupport
      rawTest.1.continuous rawTest.1.hasCompactSupport
  have hTestIntegrable :
      Integrable (fun time => test.1 time) weightedMeasure := by
    exact Continuous.integrable_of_hasCompactSupport
      test.1.continuous test.1.hasCompactSupport
  have hRawIntegrable :=
    (hTargetIntegrable.sub hRawTestIntegrable).norm
  have hTestDifferenceIntegrable :=
    (hTargetIntegrable.sub hTestIntegrable).norm
  have hClampedError :
      ∫ time, |target time - test.1 time| ∂weightedMeasure < epsilon := by
    apply lt_of_le_of_lt _ hRawError
    apply integral_mono_ae hTestDifferenceIntegrable hRawIntegrable
    apply Filter.Eventually.of_forall
    intro time
    simpa only [Real.norm_eq_abs, target, test] using!
      FiniteOpenIntervalVanishingContinuousTest.abs_sub_symmetricClamp_le
        hBound
        (boundedPoissonOptimalExponent_mem_Icc
          bound hBound (flow time) (expected time))
        rawTest time
  change
    (∫ time, |target time - test.1 time|
      ∂measure.withDensity fun time => ENNReal.ofReal (weight time)) < epsilon
    at hClampedError
  rw [integral_withDensity_eq_integral_toReal_smul
    hDensityMeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun time => |target time - test.1 time|)] at hClampedError
  simpa only [ENNReal.toReal_ofReal (hWeightNonnegative _), smul_eq_mul,
    weight, target] using hClampedError

/-- Every bounded measurable optimized Poisson dual evaluation can be approximated arbitrarily
well in integrated absolute error by an evaluation at a relative continuous test. -/
theorem
    exists_finiteOpenIntervalVanishingContinuousTest_integral_abs_poissonDual_sub_lt
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ}
    (flow expected : ℝ → NNReal)
    (hFlowMeasurable : Measurable flow)
    (hExpectedMeasurable : Measurable expected)
    (hFlowIntegrable : Integrable (fun time => (flow time : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun time => (expected time : ℝ)) measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration)
    (bound : ℝ) (hBound : 0 ≤ bound)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∃ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ time, test.1 time ∈ Set.Icc (-bound) bound) ∧
      ∫ time,
        |poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
            (boundedPoissonOptimalExponent bound (flow time) (expected time)) -
          poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
            (test.1 time)| ∂measure < epsilon := by
  obtain ⟨test, hTestRange, hWeightedError⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_weighted_boundedPoissonOptimalExponent
      hDuration flow expected hFlowMeasurable hExpectedMeasurable hFlowIntegrable
        hExpectedIntegrable hPhysical bound hBound hEpsilon
  refine ⟨test, hTestRange, ?_⟩
  let target : ℝ → ℝ := fun time =>
    boundedPoissonOptimalExponent bound (flow time) (expected time)
  let weight : ℝ → ℝ := fun time =>
    poissonDualApproximationWeight bound (flow time) (expected time)
  let difference : ℝ → ℝ := fun time =>
    |target time - test.1 time|
  have hTargetMeasurable : Measurable target := by
    dsimp only [target]
    exact (measurable_boundedPoissonOptimalExponent bound).comp
      (hFlowMeasurable.prodMk hExpectedMeasurable)
  have hWeightIntegrable : Integrable weight measure := by
    dsimp only [weight, poissonDualApproximationWeight]
    exact hFlowIntegrable.add
      (hExpectedIntegrable.mul_const (Real.exp bound))
  have hDifferenceMeasurable : Measurable difference := by
    dsimp only [difference]
    fun_prop
  have hDifferenceBound :
      ∀ᵐ time ∂measure, ‖difference time‖ ≤ 2 * bound := by
    apply Filter.Eventually.of_forall
    intro time
    have hTargetAbs : |target time| ≤ bound :=
      abs_le.mpr
        (boundedPoissonOptimalExponent_mem_Icc
          bound hBound (flow time) (expected time))
    have hTestAbs : |test.1 time| ≤ bound :=
      abs_le.mpr (hTestRange time)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact (abs_sub _ _).trans <| by
      linarith
  have hWeightedIntegrable :
      Integrable (fun time => weight time * difference time) measure :=
    hWeightIntegrable.mul_bdd hDifferenceMeasurable.aestronglyMeasurable
      hDifferenceBound
  let dualDifference : ℝ → ℝ := fun time =>
    |poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
        (target time) -
      poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
        (test.1 time)|
  have hDualDifferenceMeasurable : Measurable dualDifference := by
    dsimp only [dualDifference, poissonExponentialDualEvaluation]
    fun_prop
  have hDualErrorBound :
      ∀ᵐ time ∂measure, ‖dualDifference time‖ ≤
        weight time * difference time := by
    apply Filter.Eventually.of_forall
    intro time
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_poissonExponentialDualEvaluation_sub_le_approximationWeight
      (flow time).coe_nonneg (expected time).coe_nonneg
      (boundedPoissonOptimalExponent_mem_Icc
        bound hBound (flow time) (expected time))
      (hTestRange time)
  have hDualDifferenceIntegrable : Integrable dualDifference measure :=
    hWeightedIntegrable.mono'
      hDualDifferenceMeasurable.aestronglyMeasurable hDualErrorBound
  apply lt_of_le_of_lt _ hWeightedError
  apply integral_mono_ae hDualDifferenceIntegrable hWeightedIntegrable
  apply Filter.Eventually.of_forall
  intro time
  exact abs_poissonExponentialDualEvaluation_sub_le_approximationWeight
    (flow time).coe_nonneg (expected time).coe_nonneg
    (boundedPoissonOptimalExponent_mem_Icc
      bound hBound (flow time) (expected time))
    (hTestRange time)

/-- A bounded measurable exponent has an integrable Poisson dual evaluation whenever its
observed and expected intensities are integrable. -/
theorem integrable_poissonExponentialDualEvaluation_of_bounded_exponent
    {Carrier : Type*} [MeasurableSpace Carrier] {measure : Measure Carrier}
    (flow expected : Carrier → NNReal)
    (hFlowIntegrable : Integrable (fun point => (flow point : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun point => (expected point : ℝ)) measure)
    (exponent : Carrier → ℝ) (hExponentMeasurable : Measurable exponent)
    (bound : ℝ)
    (hExponentBound : ∀ᵐ point ∂measure, |exponent point| ≤ bound) :
    Integrable (fun point =>
      poissonExponentialDualEvaluation (flow point : ℝ) (expected point : ℝ)
        (exponent point)) measure := by
  have hExponentNormBound :
      ∀ᵐ point ∂measure, ‖exponent point‖ ≤ bound := by
    simpa only [Real.norm_eq_abs] using hExponentBound
  have hFlowTermIntegrable :
      Integrable (fun point => (flow point : ℝ) * exponent point) measure :=
    hFlowIntegrable.mul_bdd hExponentMeasurable.aestronglyMeasurable
      hExponentNormBound
  have hCompensatorMeasurable :
      Measurable fun point => Real.exp (exponent point) - 1 := by
    fun_prop
  have hCompensatorBound :
      ∀ᵐ point ∂measure,
        ‖Real.exp (exponent point) - 1‖ ≤ Real.exp bound + 1 := by
    filter_upwards [hExponentBound] with point hPoint
    rw [Real.norm_eq_abs]
    calc
      |Real.exp (exponent point) - 1| ≤
          |Real.exp (exponent point)| + |(1 : ℝ)| :=
        abs_sub _ _
      _ = Real.exp (exponent point) + 1 := by
        rw [abs_of_pos (Real.exp_pos _), abs_one]
      _ ≤ Real.exp bound + 1 := by
        gcongr
        exact (le_abs_self _).trans hPoint
  have hExpectedTermIntegrable :
      Integrable (fun point =>
        (expected point : ℝ) * (Real.exp (exponent point) - 1)) measure :=
    hExpectedIntegrable.mul_bdd hCompensatorMeasurable.aestronglyMeasurable
      hCompensatorBound
  simpa only [poissonExponentialDualEvaluation] using!
    hFlowTermIntegrable.sub hExpectedTermIntegrable

/-- Supremum of one-channel integrated Poisson dual evaluations over the relative
`C₀((0,T))` test family. -/
noncomputable def oneChannelContinuousPoissonDualRate
    {duration : ℝ} (measure : Measure ℝ)
    (flow expected : ℝ → NNReal) : ENNReal :=
  ⨆ test : FiniteOpenIntervalVanishingContinuousTest duration,
    ENNReal.ofReal (∫ time,
      poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
        (test.1 time) ∂measure)

/-- Every bounded pointwise optimizer integral is bounded by the one-channel relative
continuous-test supremum. -/
theorem boundedPoissonOptimalExponent_integral_le_continuousDualRate
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ}
    (flow expected : ℝ → NNReal)
    (hFlowMeasurable : Measurable flow)
    (hExpectedMeasurable : Measurable expected)
    (hFlowIntegrable : Integrable (fun time => (flow time : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun time => (expected time : ℝ)) measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration)
    (bound : ℝ) (hBound : 0 ≤ bound) :
    ENNReal.ofReal (∫ time,
      poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
        (boundedPoissonOptimalExponent bound (flow time) (expected time))
        ∂measure) ≤
      oneChannelContinuousPoissonDualRate
        (duration := duration) measure flow expected := by
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hEpsilon _hRateFinite
  have hEpsilonReal : 0 < (epsilon : ℝ) := by
    exact_mod_cast hEpsilon
  obtain ⟨test, hTestRange, hApproximation⟩ :=
    exists_finiteOpenIntervalVanishingContinuousTest_integral_abs_poissonDual_sub_lt
      hDuration flow expected hFlowMeasurable hExpectedMeasurable hFlowIntegrable
        hExpectedIntegrable hPhysical bound hBound hEpsilonReal
  let target : ℝ → ℝ := fun time =>
    poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
      (boundedPoissonOptimalExponent bound (flow time) (expected time))
  let approximation : ℝ → ℝ := fun time =>
    poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
      (test.1 time)
  have hTargetIntegrable : Integrable target measure := by
    apply integrable_poissonExponentialDualEvaluation_of_bounded_exponent
      flow expected hFlowIntegrable hExpectedIntegrable
    · exact (measurable_boundedPoissonOptimalExponent bound).comp
        (hFlowMeasurable.prodMk hExpectedMeasurable)
    · apply Filter.Eventually.of_forall
      intro time
      exact abs_le.mpr
        (boundedPoissonOptimalExponent_mem_Icc
          bound hBound (flow time) (expected time))
  have hApproximationIntegrable : Integrable approximation measure := by
    apply integrable_poissonExponentialDualEvaluation_of_bounded_exponent
      flow expected hFlowIntegrable hExpectedIntegrable
    · exact test.1.continuous.measurable
    · apply Filter.Eventually.of_forall
      intro time
      exact abs_le.mpr (hTestRange time)
  have hIntegralSub :
      |(∫ time, target time ∂measure) -
          (∫ time, approximation time ∂measure)| ≤
        ∫ time, |target time - approximation time| ∂measure := by
    rw [← integral_sub hTargetIntegrable hApproximationIntegrable]
    simpa only [Real.norm_eq_abs] using
      (_root_.MeasureTheory.norm_integral_le_integral_norm
        (fun time => target time - approximation time) :
          ‖∫ time, target time - approximation time ∂measure‖ ≤
            ∫ time, ‖target time - approximation time‖ ∂measure)
  have hApproximationError :
      ∫ time, |target time - approximation time| ∂measure <
        (epsilon : ℝ) :=
    hApproximation
  have hIntegralLe :
      (∫ time, target time ∂measure) ≤
        (∫ time, approximation time ∂measure) + (epsilon : ℝ) := by
    linarith [le_abs_self
      ((∫ time, target time ∂measure) -
        (∫ time, approximation time ∂measure))]
  calc
    ENNReal.ofReal (∫ time, target time ∂measure) ≤
        ENNReal.ofReal
          ((∫ time, approximation time ∂measure) + (epsilon : ℝ)) :=
      ENNReal.ofReal_le_ofReal hIntegralLe
    _ ≤ ENNReal.ofReal (∫ time, approximation time ∂measure) +
        ENNReal.ofReal (epsilon : ℝ) :=
      ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (∫ time, approximation time ∂measure) + epsilon := by
      rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ oneChannelContinuousPoissonDualRate
          (duration := duration) measure flow expected + epsilon := by
      simpa only [approximation, oneChannelContinuousPoissonDualRate, add_comm] using
        add_le_add_right (le_iSup
          (fun candidate : FiniteOpenIntervalVanishingContinuousTest duration =>
            ENNReal.ofReal (∫ time,
              poissonExponentialDualEvaluation
                (flow time : ℝ) (expected time : ℝ)
                (candidate.1 time) ∂measure)) test) epsilon

/-- The relative continuous-test supremum is exactly the integrated extended Poisson rate for
one channel.  This includes positive flow against zero reference and zero flow against positive
reference; neither singular sector is discarded by an interior logarithm. -/
theorem oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ}
    (flow expected : ℝ → NNReal)
    (hFlowMeasurable : Measurable flow)
    (hExpectedMeasurable : Measurable expected)
    (hFlowIntegrable : Integrable (fun time => (flow time : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun time => (expected time : ℝ)) measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration) :
    oneChannelContinuousPoissonDualRate
        (duration := duration) measure flow expected =
      ∫⁻ time,
        rengerExtendedPoissonRateCost (flow time) (expected time) ∂measure := by
  apply le_antisymm
  · apply iSup_le
    intro test
    let boundedTest :=
      ofCompactSupport test.1 test.1.continuous test.1.hasCompactSupport
    have hTestIntegrable :
        Integrable (fun time =>
          poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
            (test.1 time)) measure := by
      apply integrable_poissonExponentialDualEvaluation_of_bounded_exponent
        flow expected hFlowIntegrable hExpectedIntegrable
      · exact test.1.continuous.measurable
      · apply Filter.Eventually.of_forall
        intro time
        change |boundedTest time| ≤ ‖boundedTest‖
        simpa only [Real.norm_eq_abs] using
          boundedTest.norm_coe_le_norm time
    calc
      ENNReal.ofReal (∫ time,
          poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
            (test.1 time) ∂measure) ≤
          ∫⁻ time, ENNReal.ofReal
            (poissonExponentialDualEvaluation
              (flow time : ℝ) (expected time : ℝ)
              (test.1 time)) ∂measure :=
        _root_.MeasureTheory.ofReal_integral_le_lintegral_ofReal hTestIntegrable
      _ ≤ ∫⁻ time,
          rengerExtendedPoissonRateCost
            (flow time) (expected time) ∂measure := by
        apply _root_.MeasureTheory.lintegral_mono
        intro time
        simpa only [poissonExponentialDualEvaluation] using
          ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
            (flow time) (expected time) (test.1 time)
  · apply le_trans
      (lintegral_rengerExtendedPoissonRateCost_le_liminf_boundedPoissonDualEvaluation
        measure flow expected hFlowMeasurable hExpectedMeasurable)
    apply Filter.liminf_le_of_frequently_le'
    apply Filter.Frequently.of_forall
    intro index
    have hOptimizerIntegrable :
        Integrable (fun time =>
          poissonExponentialDualEvaluation (flow time : ℝ) (expected time : ℝ)
            (boundedPoissonOptimalExponent
              (index : ℝ) (flow time) (expected time))) measure := by
      apply integrable_poissonExponentialDualEvaluation_of_bounded_exponent
        flow expected hFlowIntegrable hExpectedIntegrable
      · exact
          (measurable_boundedPoissonOptimalExponent (index : ℝ)).comp
            (hFlowMeasurable.prodMk hExpectedMeasurable)
      · apply Filter.Eventually.of_forall
        intro time
        exact abs_le.mpr
          (boundedPoissonOptimalExponent_mem_Icc
            (index : ℝ) (by positivity) (flow time) (expected time))
    have hOptimizerNonnegative :
        ∀ᵐ time ∂measure,
          0 ≤ poissonExponentialDualEvaluation
            (flow time : ℝ) (expected time : ℝ)
            (boundedPoissonOptimalExponent
              (index : ℝ) (flow time) (expected time)) := by
      apply Filter.Eventually.of_forall
      intro time
      exact
        poissonExponentialDualEvaluation_boundedPoissonOptimalExponent_nonneg
          (index : ℝ) (by positivity) (flow time) (expected time)
    change
      (∫⁻ time, ENNReal.ofReal
        (poissonExponentialDualEvaluation
          (flow time : ℝ) (expected time : ℝ)
          (boundedPoissonOptimalExponent
            (index : ℝ) (flow time) (expected time))) ∂measure) ≤
        oneChannelContinuousPoissonDualRate
          (duration := duration) measure flow expected
    rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hOptimizerIntegrable hOptimizerNonnegative]
    exact boundedPoissonOptimalExponent_integral_le_continuousDualRate
      hDuration flow expected hFlowMeasurable hExpectedMeasurable
      hFlowIntegrable hExpectedIntegrable hPhysical (index : ℝ) (by positivity)

/-- Exact one-channel duality only requires almost-everywhere measurable intensities.  The
continuous-test functional and extended rate integral are both invariant under the measurable
modifications used in the proof. -/
theorem
    oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost_of_aemeasurable
    {duration : ℝ} (hDuration : 0 < duration)
    {measure : Measure ℝ}
    (flow expected : ℝ → NNReal)
    (hFlowMeasurable : AEMeasurable flow measure)
    (hExpectedMeasurable : AEMeasurable expected measure)
    (hFlowIntegrable : Integrable (fun time => (flow time : ℝ)) measure)
    (hExpectedIntegrable :
      Integrable (fun time => (expected time : ℝ)) measure)
    (hPhysical : ∀ᵐ time ∂measure, time ∈ Set.Ioo 0 duration) :
    oneChannelContinuousPoissonDualRate
        (duration := duration) measure flow expected =
      ∫⁻ time,
        rengerExtendedPoissonRateCost (flow time) (expected time) ∂measure := by
  let measurableFlow : ℝ → NNReal :=
    AEMeasurable.mk flow hFlowMeasurable
  let measurableExpected : ℝ → NNReal :=
    AEMeasurable.mk expected hExpectedMeasurable
  have hFlowEq : flow =ᵐ[measure] measurableFlow :=
    hFlowMeasurable.ae_eq_mk
  have hExpectedEq : expected =ᵐ[measure] measurableExpected :=
    hExpectedMeasurable.ae_eq_mk
  have hMeasurableFlowIntegrable :
      Integrable (fun time => (measurableFlow time : ℝ)) measure := by
    apply hFlowIntegrable.congr
    filter_upwards [hFlowEq] with time hTime
    simp only [hTime]
  have hMeasurableExpectedIntegrable :
      Integrable (fun time => (measurableExpected time : ℝ)) measure := by
    apply hExpectedIntegrable.congr
    filter_upwards [hExpectedEq] with time hTime
    simp only [hTime]
  have hContinuousRate :
      oneChannelContinuousPoissonDualRate
          (duration := duration) measure flow expected =
        oneChannelContinuousPoissonDualRate
          (duration := duration) measure measurableFlow measurableExpected := by
    unfold oneChannelContinuousPoissonDualRate
    congr 1
    funext test
    congr 1
    apply integral_congr_ae
    filter_upwards [hFlowEq, hExpectedEq] with
      time hFlowTime hExpectedTime
    simp only [hFlowTime, hExpectedTime]
  have hRateCost :
      (∫⁻ time,
        rengerExtendedPoissonRateCost (flow time) (expected time) ∂measure) =
      ∫⁻ time,
        rengerExtendedPoissonRateCost
          (measurableFlow time) (measurableExpected time) ∂measure := by
    apply lintegral_congr_ae
    filter_upwards [hFlowEq, hExpectedEq] with
      time hFlowTime hExpectedTime
    simp only [hFlowTime, hExpectedTime]
  rw [hContinuousRate, hRateCost]
  exact oneChannelContinuousPoissonDualRate_eq_lintegral_rateCost
    hDuration measurableFlow measurableExpected
    hFlowMeasurable.measurable_mk hExpectedMeasurable.measurable_mk
    hMeasurableFlowIntegrable hMeasurableExpectedIntegrable hPhysical

end

end FiniteMarkovProcesses.InformationTheory
