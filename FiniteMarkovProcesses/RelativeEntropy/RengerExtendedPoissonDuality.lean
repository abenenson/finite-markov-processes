/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDynamicRate
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Extended Poisson exponential duality

This module proves the exact scalar Fenchel representation underlying the Renger directional-flow
rate.  It keeps both singular boundary sectors visible: zero observed flow against a positive
reference is obtained as the exponent tends to negative infinity, while positive observed flow
against a zero reference makes the dual supremum infinite.

## Main results

* `poissonExponentialDualEvaluation_eq_discrimination_at_log_ratio` identifies the optimizer in
  the positive--positive sector.
* `abs_exp_sub_exp_le_exp_mul_abs_sub_of_mem_Icc` controls continuous approximations uniformly on
  a bounded dual interval.
* `iSup_ofReal_poissonExponentialDualEvaluation_eq_rengerExtendedPoissonRateCost` proves exact
  extended one-channel duality in all four zero/positive sectors.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open scoped ENNReal Topology

noncomputable section

/-- Real one-channel exponential dual evaluation. -/
def poissonExponentialDualEvaluation
    (flow expected exponent : ℝ) : ℝ :=
  flow * exponent - expected * (Real.exp exponent - 1)

/-- Positive observed and reference intensities attain the Poisson discrimination at their
logarithmic ratio. -/
theorem poissonExponentialDualEvaluation_eq_discrimination_at_log_ratio
    {flow expected : ℝ} (hFlow : 0 < flow) (hExpected : 0 < expected) :
    poissonExponentialDualEvaluation flow expected (Real.log (flow / expected)) =
      poissonRateDiscrimination flow expected := by
  unfold poissonExponentialDualEvaluation poissonRateDiscrimination
  rw [Real.exp_log (div_pos hFlow hExpected)]
  field_simp
  ring

/-- The real exponential is Lipschitz with constant `exp bound` when both arguments lie in the
closed interval from `-bound` to `bound`. -/
theorem abs_exp_sub_exp_le_exp_mul_abs_sub_of_mem_Icc
    {bound first second : ℝ}
    (hFirst : first ∈ Set.Icc (-bound) bound)
    (hSecond : second ∈ Set.Icc (-bound) bound) :
    |Real.exp first - Real.exp second| ≤
      Real.exp bound * |first - second| := by
  have hLipschitz := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (C := Real.exp bound)
    (fun _ _ => Real.differentiableAt_exp)
    (fun point hPoint => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos point)]
      exact Real.exp_le_exp.mpr hPoint.2)
    (convex_Icc _ _) hFirst hSecond
  simpa only [Real.norm_eq_abs, abs_sub_comm] using hLipschitz

/-- The scalar exponential dual supremum is exactly the extended Poisson rate cost, including
both zero-intensity boundary sectors. -/
theorem iSup_ofReal_poissonExponentialDualEvaluation_eq_rengerExtendedPoissonRateCost
    (flow expected : NNReal) :
    (⨆ exponent : ℝ,
      ENNReal.ofReal
        (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ) exponent)) =
      rengerExtendedPoissonRateCost flow expected := by
  apply le_antisymm
  · apply iSup_le
    intro exponent
    simpa only [poissonExponentialDualEvaluation] using
      ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
        flow expected exponent
  · by_cases hExpected : expected = 0
    · subst expected
      by_cases hFlow : flow = 0
      · subst flow
        simp [poissonExponentialDualEvaluation, rengerExtendedPoissonRateCost]
      · have hFlowPositive : 0 < flow := pos_iff_ne_zero.mpr hFlow
        rw [rengerExtendedPoissonRateCost_pos_zero hFlowPositive]
        apply top_le_iff.mpr
        rw [iSup_eq_top]
        intro bound hBound
        have hBoundFinite : bound ≠ ∞ := ne_of_lt hBound
        refine ⟨(bound.toReal + 1) / (flow : ℝ), ?_⟩
        rw [ENNReal.lt_ofReal_iff_toReal_lt hBoundFinite]
        simp only [poissonExponentialDualEvaluation, NNReal.coe_zero]
        have hFlowRealPositive : 0 < (flow : ℝ) := by exact_mod_cast hFlowPositive
        field_simp
        linarith
    · have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
      by_cases hFlow : flow = 0
      · subst flow
        rw [rengerExtendedPoissonRateCost_of_expected_pos 0 hExpectedPositive]
        have hDiscrimination :
            poissonRateDiscrimination 0 (expected : ℝ) = (expected : ℝ) := by
          unfold poissonRateDiscrimination
          simp
        simp only [NNReal.coe_zero]
        rw [hDiscrimination]
        have hRealTendsto : Tendsto
            (fun exponent : ℝ =>
              poissonExponentialDualEvaluation 0 (expected : ℝ) (-exponent))
            atTop (nhds (expected : ℝ)) := by
          convert
            (tendsto_const_nhds.mul
              (tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero) :
                Tendsto (fun exponent : ℝ =>
                  (expected : ℝ) * (1 - Real.exp (-exponent)))
                  atTop (nhds ((expected : ℝ) * (1 - 0)))) using 1
          · funext exponent
            unfold poissonExponentialDualEvaluation
            ring
          · congr 1
            ring
        have hExtendedTendsto : Tendsto
            (fun exponent : ℝ => ENNReal.ofReal
              (poissonExponentialDualEvaluation 0 (expected : ℝ) (-exponent)))
            atTop (nhds (ENNReal.ofReal (expected : ℝ))) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp hRealTendsto
        apply le_of_tendsto hExtendedTendsto
        exact Filter.Eventually.of_forall fun exponent =>
          le_iSup (fun candidate : ℝ => ENNReal.ofReal
            (poissonExponentialDualEvaluation 0 (expected : ℝ) candidate)) (-exponent)
      · have hFlowPositive : 0 < flow := pos_iff_ne_zero.mpr hFlow
        rw [rengerExtendedPoissonRateCost_of_expected_pos flow hExpectedPositive]
        calc
          ENNReal.ofReal
              (poissonRateDiscrimination (flow : ℝ) (expected : ℝ)) =
              ENNReal.ofReal
                (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ)
                  (Real.log ((flow : ℝ) / (expected : ℝ)))) := by
            rw [poissonExponentialDualEvaluation_eq_discrimination_at_log_ratio]
            · exact_mod_cast hFlowPositive
            · exact_mod_cast hExpectedPositive
          _ ≤ _ := le_iSup (fun exponent : ℝ => ENNReal.ofReal
            (poissonExponentialDualEvaluation (flow : ℝ) (expected : ℝ) exponent)) _

/-- Matching observed and expected intensities have zero extended Poisson cost, including at the
zero-rate boundary. -/
theorem rengerExtendedPoissonRateCost_self (expected : NNReal) :
    rengerExtendedPoissonRateCost expected expected = 0 := by
  by_cases hExpected : expected = 0
  · subst expected
    exact rengerExtendedPoissonRateCost_zero_zero
  · rw [rengerExtendedPoissonRateCost_of_expected_pos expected
      (pos_iff_ne_zero.mpr hExpected)]
    simp [poissonRateDiscrimination]

/-- Zero observed intensity costs exactly the supplied expected intensity, including the common
zero boundary. -/
theorem rengerExtendedPoissonRateCost_zero_left (expected : NNReal) :
    rengerExtendedPoissonRateCost 0 expected = (expected : ENNReal) := by
  by_cases hExpected : expected = 0
  · subst expected
    exact rengerExtendedPoissonRateCost_zero_zero
  · rw [rengerExtendedPoissonRateCost_of_expected_pos 0
      (pos_iff_ne_zero.mpr hExpected)]
    simp [poissonRateDiscrimination]

/-- On two nonnegative intensities with matching zero support, the extended Poisson cost is the
positive embedding of the ordinary real Poisson discrimination. -/
theorem rengerExtendedPoissonRateCost_eq_ofReal_poissonRateDiscrimination_of_zero_iff
    (flow expected : NNReal) (hZero : flow = 0 ↔ expected = 0) :
    rengerExtendedPoissonRateCost flow expected =
      ENNReal.ofReal (poissonRateDiscrimination (flow : ℝ) (expected : ℝ)) := by
  by_cases hExpected : expected = 0
  · have hFlow : flow = 0 := hZero.mpr hExpected
    subst flow
    subst expected
    simp [rengerExtendedPoissonRateCost, poissonRateDiscrimination]
  · exact rengerExtendedPoissonRateCost_of_expected_pos flow
      (pos_iff_ne_zero.mpr hExpected)

/-- The extended Poisson cost is exactly homogeneous under a common nonnegative intensity
scale, including every zero-rate boundary sector. -/
theorem rengerExtendedPoissonRateCost_commonScale
    (scale flow expected : NNReal) :
    rengerExtendedPoissonRateCost (scale * flow) (scale * expected) =
      (scale : ENNReal) * rengerExtendedPoissonRateCost flow expected := by
  by_cases hScale : scale = 0
  · subst scale
    simp [rengerExtendedPoissonRateCost]
  have hScalePositive : 0 < scale := pos_iff_ne_zero.mpr hScale
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · have hScaledFlow : 0 < scale * flow :=
        mul_pos hScalePositive (pos_iff_ne_zero.mpr hFlow)
      simp only [mul_zero]
      rw [rengerExtendedPoissonRateCost_pos_zero hScaledFlow,
        rengerExtendedPoissonRateCost_pos_zero (pos_iff_ne_zero.mpr hFlow)]
      simp [hScale]
  have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
  have hScaledExpectedPositive : 0 < scale * expected :=
    mul_pos hScalePositive hExpectedPositive
  rw [rengerExtendedPoissonRateCost_of_expected_pos _ hScaledExpectedPositive,
    rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive,
    ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (show 0 ≤ (scale : ℝ) by positivity)]
  apply congrArg ENNReal.ofReal
  unfold poissonRateDiscrimination
  have hScaleReal : (scale : ℝ) ≠ 0 := by exact_mod_cast hScale
  have hExpectedReal : (expected : ℝ) ≠ 0 := by exact_mod_cast hExpected
  rw [show ((scale * flow : NNReal) : ℝ) = (scale : ℝ) * (flow : ℝ) by norm_num,
    show ((scale * expected : NNReal) : ℝ) =
      (scale : ℝ) * (expected : ℝ) by norm_num,
    mul_div_mul_left _ _ hScaleReal]
  ring

/-- Adding one copy of the expected intensity raises extended Poisson cost by at most the
original flow, uniformly across the zero-expected boundary. -/
theorem rengerExtendedPoissonRateCost_add_expected_le
    (flow expected : NNReal) :
    rengerExtendedPoissonRateCost (flow + expected) expected ≤
      rengerExtendedPoissonRateCost flow expected + (flow : ENNReal) := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · simp [rengerExtendedPoissonRateCost, hFlow]
  have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
  rw [rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive,
    rengerExtendedPoissonRateCost_of_expected_pos _ hExpectedPositive,
    ← ENNReal.ofReal_coe_nnreal]
  rw [← ENNReal.ofReal_add
    (poissonRateDiscrimination_nonneg (show 0 ≤ (flow : ℝ) by positivity)
      (show 0 < (expected : ℝ) by exact_mod_cast hExpectedPositive))
    (show 0 ≤ (flow : ℝ) by positivity)]
  exact ENNReal.ofReal_le_ofReal <|
    poissonRateDiscrimination_add_reference_le
      (show 0 ≤ (flow : ℝ) by positivity)
      (show 0 < (expected : ℝ) by exact_mod_cast hExpectedPositive)

/-- The extended Poisson cost is sublinear under a common nonnegative weighted addition of
observed and expected intensities.  Exact scalar duality makes this statement valid without
separate zero-rate cases. -/
theorem rengerExtendedPoissonRateCost_weighted_add_le
    (firstWeight secondWeight firstFlow firstExpected secondFlow secondExpected : NNReal) :
    rengerExtendedPoissonRateCost
        (firstWeight * firstFlow + secondWeight * secondFlow)
        (firstWeight * firstExpected + secondWeight * secondExpected) ≤
      (firstWeight : ENNReal) *
          rengerExtendedPoissonRateCost firstFlow firstExpected +
        (secondWeight : ENNReal) *
          rengerExtendedPoissonRateCost secondFlow secondExpected := by
  rw [← iSup_ofReal_poissonExponentialDualEvaluation_eq_rengerExtendedPoissonRateCost]
  apply iSup_le
  intro exponent
  have hEvaluation :
      poissonExponentialDualEvaluation
          ((firstWeight * firstFlow + secondWeight * secondFlow : NNReal) : ℝ)
          ((firstWeight * firstExpected + secondWeight * secondExpected : NNReal) : ℝ)
          exponent =
        (firstWeight : ℝ) *
            poissonExponentialDualEvaluation
              (firstFlow : ℝ) (firstExpected : ℝ) exponent +
          (secondWeight : ℝ) *
            poissonExponentialDualEvaluation
              (secondFlow : ℝ) (secondExpected : ℝ) exponent := by
    unfold poissonExponentialDualEvaluation
    push_cast
    ring
  rw [hEvaluation]
  calc
    ENNReal.ofReal
        ((firstWeight : ℝ) *
            poissonExponentialDualEvaluation
              (firstFlow : ℝ) (firstExpected : ℝ) exponent +
          (secondWeight : ℝ) *
            poissonExponentialDualEvaluation
              (secondFlow : ℝ) (secondExpected : ℝ) exponent) ≤
        ENNReal.ofReal
            ((firstWeight : ℝ) *
              poissonExponentialDualEvaluation
                (firstFlow : ℝ) (firstExpected : ℝ) exponent) +
          ENNReal.ofReal
            ((secondWeight : ℝ) *
              poissonExponentialDualEvaluation
                (secondFlow : ℝ) (secondExpected : ℝ) exponent) :=
      ENNReal.ofReal_add_le
    _ = (firstWeight : ENNReal) *
          ENNReal.ofReal
            (poissonExponentialDualEvaluation
              (firstFlow : ℝ) (firstExpected : ℝ) exponent) +
        (secondWeight : ENNReal) *
          ENNReal.ofReal
            (poissonExponentialDualEvaluation
              (secondFlow : ℝ) (secondExpected : ℝ) exponent) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp
    _ ≤ (firstWeight : ENNReal) *
          rengerExtendedPoissonRateCost firstFlow firstExpected +
        (secondWeight : ENNReal) *
          rengerExtendedPoissonRateCost secondFlow secondExpected := by
      gcongr
      · exact ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
          firstFlow firstExpected exponent
      · exact ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
          secondFlow secondExpected exponent

end

end FiniteMarkovProcesses.InformationTheory
