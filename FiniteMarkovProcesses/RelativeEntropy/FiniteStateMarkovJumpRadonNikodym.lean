/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpAction

/-!
# Radon--Nikodym derivatives of finite-state Markov jump measures

This module lifts the physical finite-state jump-density action to an exact measure-level
Radon--Nikodym derivative under literal common initial and directed support. It applies to the
sigma-finite density measures before probability normalization; fluctuation and expected-KL
identities remain gated by normalization.

## Main results

- `finiteStateMarkovJumpDensityMeasure_withDensity_ratio`: exact density-ratio factorization.
- `finiteStateMarkovJumpDensityMeasure_absolutelyContinuous`: common-support domination.
- `rnDeriv_finiteStateMarkovJumpDensityMeasure`: exact extended-real RN derivative.
- `rnDeriv_finiteStateMarkovJumpDensityMeasure_eq_exp_logAction`: RN derivative as the
  exponential of the complete physical action.
- `llr_finiteStateMarkovJumpDensityMeasure`: real log-likelihood action on the candidate law.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

variable {State : Type u} [Fintype State]

/-- Extended-real candidate/reference density ratio on the common base. The value at a common
zero is immaterial to either induced measure. -/
noncomputable def finiteStateMarkovJumpDensityRatioENNReal
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ≥0∞ :=
  fun history =>
    (finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T history)⁻¹ *
      finiteStateMarkovJumpDensityENNReal initial generator T history

/-- The extended-real physical density ratio is measurable. -/
theorem measurable_finiteStateMarkovJumpDensityRatioENNReal
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
      referenceGenerator T) :=
  (measurable_finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T).inv.mul
    (measurable_finiteStateMarkovJumpDensityENNReal initial generator T)

/-- Under common support, multiplying the reference density by the extended-real ratio recovers
the candidate density at every history, including common zeros. -/
theorem finiteStateMarkovJumpReferenceDensity_mul_ratio
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) (history : FiniteJumpHistory State) :
    finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T history *
        finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
          referenceGenerator T history =
      finiteStateMarkovJumpDensityENNReal initial generator T history := by
  by_cases hReference :
      finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history = 0
  · have hCandidate : finiteStateMarkovJumpDensity initial generator T history = 0 :=
      (finiteStateMarkovJumpDensity_eq_zero_iff
        hInitialSupport hRateSupport T history).mpr hReference
    simp [finiteStateMarkovJumpDensityENNReal,
      finiteStateMarkovJumpDensityRatioENNReal, hReference, hCandidate]
  · have hReferenceNonneg :=
      finiteStateMarkovJumpDensity_nonneg referenceInitial referenceGenerator T history
    have hReferencePos :
        0 < finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history :=
      lt_of_le_of_ne hReferenceNonneg (Ne.symm hReference)
    have hReferenceENNRealZero :
        finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T history ≠ 0 := by
      unfold finiteStateMarkovJumpDensityENNReal
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hReferencePos)
    have hReferenceENNRealTop :
        finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T history ≠ ⊤ := by
      unfold finiteStateMarkovJumpDensityENNReal
      exact ENNReal.ofReal_ne_top
    unfold finiteStateMarkovJumpDensityRatioENNReal
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel hReferenceENNRealZero hReferenceENNRealTop, one_mul]

/-- The candidate density measure is the reference density measure tilted by their literal
extended-real density ratio. -/
theorem finiteStateMarkovJumpDensityMeasure_withDensity_ratio
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T).withDensity
        (finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
          referenceGenerator T) =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  unfold finiteStateMarkovJumpDensityMeasure
  rw [← withDensity_mul (finiteJumpHistoryBaseMeasure State T)
    (measurable_finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T)
    (measurable_finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
      referenceGenerator T)]
  apply congrArg ((finiteJumpHistoryBaseMeasure State T).withDensity)
  funext history
  exact finiteStateMarkovJumpReferenceDensity_mul_ratio
    hInitialSupport hRateSupport T history

/-- Common support makes the candidate density measure absolutely continuous with respect to the
reference density measure. -/
theorem finiteStateMarkovJumpDensityMeasure_absolutelyContinuous
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator T ≪
      finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T := by
  rw [← finiteStateMarkovJumpDensityMeasure_withDensity_ratio
    hInitialSupport hRateSupport T]
  exact withDensity_absolutelyContinuous _ _

/-- Exact Radon--Nikodym derivative between common-support physical jump density measures. -/
theorem rnDeriv_finiteStateMarkovJumpDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    (finiteStateMarkovJumpDensityMeasure initial generator T).rnDeriv
        (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T) =ᵐ[
          finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T]
      finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
        referenceGenerator T := by
  rw [← finiteStateMarkovJumpDensityMeasure_withDensity_ratio
    hInitialSupport hRateSupport T]
  exact Measure.rnDeriv_withDensity _
    (measurable_finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
      referenceGenerator T)

/-- The reference density measure almost surely occupies its nonzero density support. -/
theorem eventually_finiteStateMarkovJumpReferenceDensity_ne_zero
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (referenceInitial : PMF State)
    (referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ∀ᵐ history ∂finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T,
      finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history ≠ 0 := by
  unfold finiteStateMarkovJumpDensityMeasure
  apply (ae_withDensity_iff
    (measurable_finiteStateMarkovJumpDensityENNReal referenceInitial referenceGenerator T)).mpr
  exact ae_of_all _ fun history hDensity => by
    intro hZero
    apply hDensity
    simp [finiteStateMarkovJumpDensityENNReal, hZero]

/-- On positive common support, the extended-real density ratio is the exponential of the
complete physical action, reference-almost everywhere. -/
theorem finiteStateMarkovJumpDensityRatioENNReal_eq_exp_logAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
        referenceGenerator T =ᵐ[
          finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T]
      fun history => ENNReal.ofReal
        (Real.exp (finiteStateMarkovJumpLogAction initial referenceInitial generator
          referenceGenerator T history)) := by
  filter_upwards [eventually_finiteStateMarkovJumpReferenceDensity_ne_zero
    referenceInitial referenceGenerator T] with history hReference
  have hCandidate : finiteStateMarkovJumpDensity initial generator T history ≠ 0 := by
    intro hZero
    exact hReference ((finiteStateMarkovJumpDensity_eq_zero_iff
      hInitialSupport hRateSupport T history).mp hZero)
  have hPositive := finiteStateMarkovJumpDensityPositiveAt_of_ne_zero
    initial generator T history hCandidate
  have hReferencePositive := finiteStateMarkovJumpDensityPositiveAt_of_ne_zero
    referenceInitial referenceGenerator T history hReference
  have hReferenceDensityPos :
      0 < finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history :=
    lt_of_le_of_ne
      (finiteStateMarkovJumpDensity_nonneg referenceInitial referenceGenerator T history)
      hReference.symm
  unfold finiteStateMarkovJumpDensityRatioENNReal finiteStateMarkovJumpDensityENNReal
  calc
    (ENNReal.ofReal
        (finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history))⁻¹ *
          ENNReal.ofReal (finiteStateMarkovJumpDensity initial generator T history) =
        ENNReal.ofReal
          (finiteStateMarkovJumpDensity initial generator T history /
            finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history) := by
      rw [ENNReal.ofReal_div_of_pos hReferenceDensityPos, div_eq_mul_inv, mul_comm]
    _ = _ := by
      rw [finiteStateMarkovJumpDensity_div_eq_exp_logAction
        initial referenceInitial generator referenceGenerator T history
          hPositive hReferencePositive]

/-- The Radon--Nikodym derivative is the exponential of the complete physical action on the
reference density measure. -/
theorem rnDeriv_finiteStateMarkovJumpDensityMeasure_eq_exp_logAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    (finiteStateMarkovJumpDensityMeasure initial generator T).rnDeriv
        (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T) =ᵐ[
          finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T]
      fun history => ENNReal.ofReal
        (Real.exp (finiteStateMarkovJumpLogAction initial referenceInitial generator
          referenceGenerator T history)) :=
  (rnDeriv_finiteStateMarkovJumpDensityMeasure hInitialSupport hRateSupport T).trans
    (finiteStateMarkovJumpDensityRatioENNReal_eq_exp_logAction
      hInitialSupport hRateSupport T)

/-- The real log-likelihood ratio on the candidate density measure is the complete physical
sector action. -/
theorem llr_finiteStateMarkovJumpDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    llr (finiteStateMarkovJumpDensityMeasure initial generator T)
        (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T) =ᵐ[
          finiteStateMarkovJumpDensityMeasure initial generator T]
      finiteStateMarkovJumpLogAction initial referenceInitial generator referenceGenerator T := by
  have hRN :=
    (finiteStateMarkovJumpDensityMeasure_absolutelyContinuous
      hInitialSupport hRateSupport T).ae_le
      (rnDeriv_finiteStateMarkovJumpDensityMeasure_eq_exp_logAction
        hInitialSupport hRateSupport T)
  filter_upwards [hRN] with history hDerivative
  rw [llr, hDerivative]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

end FiniteMarkovProcesses.InformationTheory
