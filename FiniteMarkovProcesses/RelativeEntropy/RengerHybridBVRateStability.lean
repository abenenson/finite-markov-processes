/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFlowStability
import FiniteMarkovProcesses.RelativeEntropy.PoissonRateHellinger
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Quantitative finite-rate stability on the existing hybrid-BV carrier

The original extended dynamic rate controls the integrated raw ordered-flow residual. The
argument first extracts admissibility and finiteness, then integrates the scalar Poisson
inequality. Normalization controls expected total activity by the physical horizon times a
row escape bound. No bound on a competitor's flow, or additional integrability, is assumed.

## Main results

- `rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le`: finite action gives admissibility.
- `rengerDirectionalFlowHybridBVExpectedActivity_le`: normalized expected activity is bounded.
- `rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le`: the explicit
  square-root residual modulus on every path of sufficiently small original dynamic rate.
- The `initial_add_rateModulus` bounds retain actual initial error and control density,
  cumulative ordered flow, terminal left traces, carried derivative variation, and strong L1.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] {duration : ℝ}

private theorem linear_bound_of_sq_le
    {error cost activity : ℝ} (hCost : 0 ≤ cost) (hActivity : 0 ≤ activity)
    (hSquare : error ^ 2 ≤ 2 * activity * cost) (test : ℝ) :
    2 * test * error ≤ 2 * cost + test ^ 2 * activity := by
  by_cases hZero : activity = 0
  · have hError : error = 0 := by nlinarith [sq_nonneg error]
    subst error
    subst activity
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCost
  · have hPositive : 0 < activity := lt_of_le_of_ne hActivity (Ne.symm hZero)
    nlinarith [sq_nonneg (error - test * activity)]

/-- A finite real dynamic-rate budget forces the original hybrid admissibility constraints. -/
theorem rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration} {epsilon : ℝ}
    (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤
      ENNReal.ofReal epsilon) :
    RengerDirectionalFlowHybridBVAdmissible path hDuration := by
  by_contra hNotAdmissible
  rw [rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
    generator hDuration hNotAdmissible] at hRate
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hRate)

/-- Raw density and RN flow agree almost everywhere with the nonnegative coordinates used by
the original extended Poisson integrand, after admissibility has been obtained. -/
theorem ae_rengerDirectionalFlowHybridBVRateCoordinates_eq_raw
    (hDuration : 0 < duration) {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (∀ state, (rengerDirectionalFlowHybridBVDensityAt path time state : ℝ) =
        rengerDirectionalFlowHybridBVDensityValue path time state) ∧
      (∀ transition, (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ℝ) =
        rengerDirectionalFlowHybridBVFlowDerivative path time transition) := by
  filter_upwards [hPath.densityNonnegativeAE, hPath.flowDerivativeNonnegativeAE]
    with time hDensity hFlow
  constructor
  · intro state
    exact Real.coe_toNNReal _ (hDensity state)
  · intro transition
    exact Real.coe_toNNReal _ (hFlow transition)

/-- Expected total ordered activity of a raw hybrid path on the physical open interval. -/
noncomputable def rengerDirectionalFlowHybridBVExpectedActivity
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ℝ :=
  ∫ time, ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
      (generator.rate transition.1.1 transition.1.2 : ℝ)
    ∂finiteOpenIntervalVolume duration

/-- Expected total activity is integrable on the original carrier. -/
theorem integrable_rengerDirectionalFlowHybridBVExpectedActivity
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Integrable (fun time ↦ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
        (generator.rate transition.1.1 transition.1.2 : ℝ))
      (finiteOpenIntervalVolume duration) := by
  apply integrable_finsetSum
  intro transition _hTransition
  exact (integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1).mul_const _

/-- Normalization bounds the expected total ordered activity by the physical escape budget.
The row bound is supplied explicitly, so no nonempty-state assumption is required. -/
theorem rengerDirectionalFlowHybridBVExpectedActivity_le
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {escapeBound : ℝ}
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    rengerDirectionalFlowHybridBVExpectedActivity generator path ≤ duration * escapeBound := by
  have hPointwise : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
          (generator.rate transition.1.1 transition.1.2 : ℝ)) ≤ escapeBound := by
    filter_upwards [hPath.densityNonnegativeAE, hPath.densityNormalizedAE]
      with time hNonnegative hNormalized
    calc
      _ = ∑ source, rengerDirectionalFlowHybridBVDensityValue path time source *
          (generator.escapeRate source : ℝ) := by
        rw [← sum_outgoingTransition_eq_sum_orderedOffDiagonalTransition]
        apply Finset.sum_congr rfl
        intro source _hSource
        rw [FiniteStateMarkovGenerator.escapeRate, NNReal.coe_sum, Finset.mul_sum,
          Fintype.sum_eq_add_sum_subtype_ne _ source]
        simp only [generator.rate_self, NNReal.coe_zero, mul_zero, zero_add]
      _ ≤ ∑ source, rengerDirectionalFlowHybridBVDensityValue path time source *
          escapeBound := Finset.sum_le_sum fun source _hSource ↦
        mul_le_mul_of_nonneg_left (hEscape source) (hNonnegative source)
      _ = escapeBound := by rw [← Finset.sum_mul, hNormalized, one_mul]
  unfold rengerDirectionalFlowHybridBVExpectedActivity
  calc
    _ ≤ ∫ _time, escapeBound ∂finiteOpenIntervalVolume duration :=
      integral_mono_ae (integrable_rengerDirectionalFlowHybridBVExpectedActivity generator path)
        (integrable_const _) hPointwise
    _ = duration * escapeBound := by
      rw [integral_const, smul_eq_mul, measureReal_def,
        finiteOpenIntervalVolume_apply_univ, ENNReal.toReal_ofReal hDuration.le]

private theorem integrated_young_bound
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (hFinite : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ∞)
    (test : ℝ) :
    2 * test * rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path ≤
      2 * (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path).toReal +
        test ^ 2 * (∫ time,
          ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
            (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
              rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
                (generator.rate transition.1.1 transition.1.2 : ℝ))
          ∂finiteOpenIntervalVolume duration) := by
  let cost := fun time ↦ rengerDirectionalFlowLocalRateRaw generator
    (rengerDirectionalFlowHybridBVDensityAt path time)
    (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)
  have hMeasurable := aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path
  have hIntegralFinite : (∫⁻ time, cost time ∂finiteOpenIntervalVolume duration) ≠ ∞ := by
    rwa [← rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration hPath]
  have hLocalFinite := ae_lt_top' hMeasurable hIntegralFinite
  have hCostIntegrable := integrable_toReal_of_lintegral_ne_top hMeasurable hIntegralFinite
  have hActivityIntegrable : Integrable (fun time ↦
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ)))
      (finiteOpenIntervalVolume duration) := by
    apply integrable_finsetSum
    intro transition _hTransition
    exact (integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition).add
      ((integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1).mul_const _)
  have hPointwise : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      2 * test * (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ)|) ≤
      2 * (cost time).toReal + test ^ 2 *
        (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
            rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
              (generator.rate transition.1.1 transition.1.2 : ℝ))) := by
    filter_upwards [hLocalFinite,
      ae_rengerDirectionalFlowHybridBVRateCoordinates_eq_raw hDuration hPath]
      with time hFiniteAt hRaw
    have hChannelFinite (transition : FiniteStateOrderedOffDiagonalTransition State) :
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2) ≠ ∞ := by
      apply ne_top_of_le_ne_top hFiniteAt.ne
      unfold rengerDirectionalFlowLocalRateRaw
      exact Finset.single_le_sum (f := fun transition ↦
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2)) (fun _ _ ↦ bot_le)
        (Finset.mem_univ transition)
    have hScalar (transition : FiniteStateOrderedOffDiagonalTransition State) :=
      linear_bound_of_sq_le
        (error := |(rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ℝ) -
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2 : NNReal)|)
        (activity := (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ℝ) +
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2 : NNReal))
        (cost := (rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2)).toReal)
        ENNReal.toReal_nonneg (by positivity)
        (by simpa only [sq_abs] using
          (sq_sub_le_two_mul_add_mul_rengerExtendedPoissonRateCost_toReal
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
            (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
              generator.rate transition.1.1 transition.1.2) (hChannelFinite transition))) test
    have hSum := Finset.sum_le_sum (s := Finset.univ) (fun transition _ ↦ hScalar transition)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hSum
    rw [← ENNReal.toReal_sum (fun transition _ ↦ hChannelFinite transition)] at hSum
    simpa only [NNReal.coe_mul, hRaw.1, hRaw.2, Finset.sum_add_distrib,
      cost, rengerDirectionalFlowLocalRateRaw] using hSum
  have hIntegrated := integral_mono_ae
    ((integrable_rengerDirectionalFlowHybridBVFlowResidual generator path).const_mul (2 * test))
    ((hCostIntegrable.const_mul 2).add (hActivityIntegrable.const_mul (test ^ 2))) hPointwise
  simp only [Pi.add_apply] at hIntegrated
  rw [integral_const_mul, integral_add (hCostIntegrable.const_mul 2)
    (hActivityIntegrable.const_mul (test ^ 2)), integral_const_mul, integral_const_mul,
    integral_toReal hMeasurable hLocalFinite,
    ← rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible generator hDuration hPath]
    at hIntegrated
  exact hIntegrated

/-- Original finite dynamic action controls the integrated raw residual with the explicit
Poisson square-root modulus. All raw/clamped identifications are made only after finiteness
has forced admissibility; positive flow against zero expected intensity retains infinite cost. -/
theorem rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration} {epsilon escapeBound : ℝ}
    (hEpsilon : 0 ≤ epsilon) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound)
    (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤
      ENNReal.ofReal epsilon) :
    rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path ≤
      poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  have hFinite : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRate
  have hRealRate :
      (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path).toReal ≤ epsilon := by
    simpa only [ENNReal.toReal_ofReal hEpsilon] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hRate
  let activity := ∫ time,
    ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
        rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
          (generator.rate transition.1.1 transition.1.2 : ℝ))
    ∂finiteOpenIntervalVolume duration
  have hActivityIntegrable : Integrable (fun time ↦
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ)))
      (finiteOpenIntervalVolume duration) := by
    apply integrable_finsetSum
    intro transition _hTransition
    exact (integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition).add
      ((integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1).mul_const _)
  have hActivityNonnegative : 0 ≤ activity := by
    apply integral_nonneg_of_ae
    filter_upwards [hPath.flowDerivativeNonnegativeAE, hPath.densityNonnegativeAE]
      with time hFlow hDensity
    exact Finset.sum_nonneg fun transition _ ↦
      add_nonneg (hFlow transition) (mul_nonneg (hDensity _) (NNReal.coe_nonneg _))
  have hActivityBound : activity ≤
      rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path +
        2 * (duration * escapeBound) := by
    have hExpected := rengerDirectionalFlowHybridBVExpectedActivity_le
      generator hDuration hPath hEscape
    have hPointwise : ∀ time,
        (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          (rengerDirectionalFlowHybridBVFlowDerivative path time transition +
            rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
              (generator.rate transition.1.1 transition.1.2 : ℝ))) ≤
        (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
            rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
              (generator.rate transition.1.1 transition.1.2 : ℝ)|) +
        2 * (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ)) := by
      intro time
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun transition _ ↦ by
        linarith [le_abs_self (rengerDirectionalFlowHybridBVFlowDerivative path time transition -
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ))]
    have hIntegral := integral_mono hActivityIntegrable
      ((integrable_rengerDirectionalFlowHybridBVFlowResidual generator path).add
        ((integrable_rengerDirectionalFlowHybridBVExpectedActivity generator path).const_mul 2))
      hPointwise
    simp only [Pi.add_apply] at hIntegral
    rw [integral_add (integrable_rengerDirectionalFlowHybridBVFlowResidual generator path)
      ((integrable_rengerDirectionalFlowHybridBVExpectedActivity generator path).const_mul 2),
      integral_const_mul] at hIntegral
    exact hIntegral.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hExpected (by norm_num : (0 : ℝ) ≤ 2)))
  have hDiscriminant := discrim_le_zero (a := activity)
    (b := -2 * rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path)
    (c := 2 * (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path).toReal)
    (fun test ↦ by
      have hYoung := integrated_young_bound generator hDuration hPath hFinite test
      dsimp only [activity]
      nlinarith only [hYoung])
  have hCauchy : (rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path) ^ 2 ≤
      2 * (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path).toReal *
        activity := by
    unfold discrim at hDiscriminant
    nlinarith only [hDiscriminant]
  apply le_poissonRateBudgetModulus_of_sq_le hEpsilon
    (mul_nonneg hDuration.le hEscapeNonnegative)
  exact hCauchy.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hRealRate (by norm_num)) hActivityNonnegative).trans
      (mul_le_mul_of_nonneg_left hActivityBound (mul_nonneg (by norm_num) hEpsilon)))

section Consequences

variable (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
  {path : RengerDirectionalFlowHybridBVPath State duration}
  (mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
  (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
  {epsilon escapeBound : ℝ} (hEpsilon : 0 ≤ epsilon)
  (hEscapeNonnegative : 0 ≤ escapeBound)
  (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound)
  (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤
    ENNReal.ofReal epsilon)

include hMeanFlow hEpsilon hEscapeNonnegative hEscape hRate

/-- Every finite-rate competitor stays close in density to the fixed-generator reference,
with its actual initial density error retained. -/
theorem sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_rateModulus
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (∑ state, |rengerDirectionalFlowHybridBVDensityValue path time state -
      rengerDirectionalFlowHybridBVDensityValue mean.1 time state|) ≤
      (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        2 * poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual
    generator hDuration ⟨path, hPath⟩ mean hMeanFlow hTime).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
          generator hDuration hEpsilon hEscapeNonnegative hEscape hRate) (by norm_num)))

/-- Original dynamic action controls complete integrated ordered-flow error relative to the
existing same-generator reference, without any hypothesis on competitor flow size. -/
theorem rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_rateModulus :
    rengerDirectionalFlowHybridBVIntegratedFlowDistance path mean.1 ≤
      (duration * escapeBound) *
          (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_residual
    generator hDuration ⟨path, hPath⟩ mean hMeanFlow escapeBound hEscapeNonnegative hEscape).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
          generator hDuration hEpsilon hEscapeNonnegative hEscape hRate)
        (by positivity)))

/-- Cumulative ordered-flow error on `[0,T)` has the same finite-rate bound as integrated
actual flow-derivative error. -/
theorem sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_initial_add_rateModulus
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition -
        rengerDirectionalFlowHybridBVCumulativeFlowValue mean.1 time transition|) ≤
      (duration * escapeBound) *
          (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_integratedFlowDistance
    hDuration ⟨path, hPath⟩ mean hTime).trans
      (rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_rateModulus
        generator hDuration mean hMeanFlow hEpsilon hEscapeNonnegative hEscape hRate)

/-- The density bound holds also at the separately recovered terminal left trace. -/
theorem sum_abs_rengerDirectionalFlowHybridBVTerminalDensity_sub_le_initial_add_rateModulus :
    (∑ state, |path.terminalTrace hDuration (Sum.inl state) -
      mean.1.terminalTrace hDuration (Sum.inl state)|) ≤
      (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        2 * poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (sum_abs_rengerDirectionalFlowHybridBVTerminalDensity_sub_le_initial_add_residual
    generator hDuration ⟨path, hPath⟩ mean hMeanFlow).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
          generator hDuration hEpsilon hEscapeNonnegative hEscape hRate) (by norm_num)))

/-- Recovered terminal cumulative flow retains the exact physical escape budget. -/
theorem sum_abs_rengerDirectionalFlowHybridBVTerminalFlow_sub_le_initial_add_rateModulus :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |path.terminalTrace hDuration (Sum.inr transition) -
        mean.1.terminalTrace hDuration (Sum.inr transition)|) ≤
      (duration * escapeBound) *
          (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          poissonRateBudgetModulus epsilon (duration * escapeBound) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (sum_abs_rengerDirectionalFlowHybridBVTerminalFlow_sub_le_initial_add_residual
    generator hDuration ⟨path, hPath⟩ mean hMeanFlow escapeBound hEscapeNonnegative hEscape).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
          generator hDuration hEpsilon hEscapeNonnegative hEscape hRate) (by positivity)))

/-- The sum of actual carried density and ordered-flow derivative variations obeys the
finite-rate modulus, rather than a statement about only selected RN representatives. -/
theorem sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_initial_add_rateModulus :
    (∑ coordinate : EmpiricalDensityDirectionalFlowCoordinate State,
      (((path.toDerivativePath.derivative coordinate).toSignedMeasure -
        (mean.1.toDerivativePath.derivative coordinate).toSignedMeasure).totalVariation
          univ).toReal) ≤
      3 * ((duration * escapeBound) *
          (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          poissonRateBudgetModulus epsilon (duration * escapeBound)) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact
    (sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_integratedFlowDistance
      hDuration ⟨path, hPath⟩ mean).trans (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_rateModulus
          generator hDuration mean hMeanFlow hEpsilon hEscapeNonnegative hEscape hRate)
        (by norm_num))

/-- The norm is that of the difference of the existing strong-L1 projections. Finite original
action controls it with the same horizon, initial error, and fixed-generator modulus. -/
theorem norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_rateModulus :
    ‖path.toDerivativePath.toL1Path - mean.1.toDerivativePath.toL1Path‖ ≤
      duration * ((1 + duration * escapeBound) *
          (∑ state, |path.initialTrace (Sum.inl state) - mean.1.initialTrace (Sum.inl state)|) +
        (3 + 2 * (duration * escapeBound)) *
          poissonRateBudgetModulus epsilon (duration * escapeBound)) := by
  have hPath := rengerDirectionalFlowHybridBVAdmissible_of_dynamicRate_le
    generator hDuration hRate
  exact (norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_residual
    generator hDuration ⟨path, hPath⟩ mean hMeanFlow escapeBound hEscapeNonnegative hEscape).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le
          generator hDuration hEpsilon hEscapeNonnegative hEscape hRate) (by positivity)))
        hDuration.le)

end Consequences

/-- Zero dynamic budget and matching initial density recover literal equality of the complete
hybrid paths via injectivity of their existing strong-L1 projections. Zero escape is allowed. -/
theorem rengerDirectionalFlowHybridBVPath_eq_of_dynamicRate_le_zero_initialDensity
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    {escapeBound : ℝ} (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound)
    (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤ 0)
    (hInitial : ∀ state, path.initialTrace (Sum.inl state) =
      mean.1.initialTrace (Sum.inl state)) :
    path = mean.1 := by
  have hNorm := norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_rateModulus
    generator hDuration mean hMeanFlow (epsilon := 0) (by norm_num)
      hEscapeNonnegative hEscape (by simpa only [ENNReal.ofReal_zero] using hRate)
  have hNormZero : ‖path.toDerivativePath.toL1Path - mean.1.toDerivativePath.toL1Path‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa [hInitial, poissonRateBudgetModulus] using hNorm
  exact FiniteIntervalHybridBVPath.injective_toL1Path
    (sub_eq_zero.mp (norm_eq_zero.mp hNormZero))

end

end FiniteMarkovProcesses.InformationTheory
