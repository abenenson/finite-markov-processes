/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.CommonBaseDensityAction
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateTimeDependentMarkovJumpAction

/-!
# Radon--Nikodym derivatives for bounded time-dependent finite-state jump laws

Two bounded measurable time-dependent jump laws with common initial and pointwise directed
support are represented by explicit densities on the existing finite-history base measure.  The
generic common-base action machinery then supplies exact density tilt, absolute continuity,
Radon--Nikodym, log-likelihood, and fluctuation identities for the normalized physical laws.

The common-support and boundedness hypotheses remain explicit in these change-of-measure
identities. Large-deviation lower bounds are established separately.

## Main results

- `finiteStateTimeDependentMarkovJumpCommonBaseDensityAction`: exact common-base representation.
- `finiteStateTimeDependentMarkovJumpDensityMeasure_withDensity_expLogAction`: physical Girsanov
  identity.
- `rnDeriv_finiteStateTimeDependentMarkovJumpDensityMeasure_eq_exp_logAction`: exact RN density.
- `llr_finiteStateTimeDependentMarkovJumpDensityMeasure`: exact physical log likelihood.
- `lintegral_exp_neg_finiteStateTimeDependentMarkovJumpLogAction`: exact fluctuation identity.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The candidate and reference bounded time-dependent jump laws as one common-base density
action. -/
noncomputable def finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    CommonBaseDensityAction (FiniteJumpHistory State)
      (finiteJumpHistoryBaseMeasure State duration) where
  candidateDensity :=
    finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration
  comparisonDensity :=
    finiteStateTimeDependentMarkovJumpDensityENNReal
      referenceInitial referenceRates duration
  action := finiteStateTimeDependentMarkovJumpLogAction
    initial referenceInitial rates referenceRates duration
  measurable_candidateDensity :=
    measurable_finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration
  measurable_comparisonDensity :=
    measurable_finiteStateTimeDependentMarkovJumpDensityENNReal
      referenceInitial referenceRates duration
  measurable_action := measurable_finiteStateTimeDependentMarkovJumpLogAction
    initial referenceInitial rates referenceRates duration
  candidateDensity_eq_zero_iff := by
    intro history
    have hCandidateNonnegative :=
      finiteStateTimeDependentMarkovJumpDensity_nonneg initial rates duration history
    have hReferenceNonnegative :=
      finiteStateTimeDependentMarkovJumpDensity_nonneg
        referenceInitial referenceRates duration history
    unfold finiteStateTimeDependentMarkovJumpDensityENNReal
    rw [ENNReal.ofReal_eq_zero, ENNReal.ofReal_eq_zero]
    constructor
    · intro hCandidate
      have hCandidateZero := le_antisymm hCandidate hCandidateNonnegative
      exact (finiteStateTimeDependentMarkovJumpDensity_eq_zero_iff
        hInitialSupport hRateSupport duration history).mp hCandidateZero ▸ le_rfl
    · intro hReference
      have hReferenceZero := le_antisymm hReference hReferenceNonnegative
      exact (finiteStateTimeDependentMarkovJumpDensity_eq_zero_iff
        hInitialSupport hRateSupport duration history).mpr hReferenceZero ▸ le_rfl
  candidateDensity_ne_top := fun _history => ENNReal.ofReal_ne_top
  comparisonDensity_ne_top := fun _history => ENNReal.ofReal_ne_top
  densityRatio_eq_exp_action_of_comparison_ne_zero := by
    intro history hReferenceDensity
    have hReferenceReal :
        finiteStateTimeDependentMarkovJumpDensity
          referenceInitial referenceRates duration history ≠ 0 := by
      intro hZero
      apply hReferenceDensity
      simp [finiteStateTimeDependentMarkovJumpDensityENNReal, hZero]
    have hCandidateReal :
        finiteStateTimeDependentMarkovJumpDensity initial rates duration history ≠ 0 := by
      intro hZero
      exact hReferenceReal
        ((finiteStateTimeDependentMarkovJumpDensity_eq_zero_iff
          hInitialSupport hRateSupport duration history).mp hZero)
    have hPositive := finiteStateTimeDependentMarkovJumpDensityPositiveAt_of_ne_zero
      initial rates duration history hCandidateReal
    have hReferencePositive :=
      finiteStateTimeDependentMarkovJumpDensityPositiveAt_of_ne_zero
        referenceInitial referenceRates duration history hReferenceReal
    have hReferenceDensityPos : 0 <
        finiteStateTimeDependentMarkovJumpDensity
          referenceInitial referenceRates duration history :=
      lt_of_le_of_ne
        (finiteStateTimeDependentMarkovJumpDensity_nonneg
          referenceInitial referenceRates duration history)
        hReferenceReal.symm
    unfold finiteStateTimeDependentMarkovJumpDensityENNReal
    calc
      (ENNReal.ofReal
          (finiteStateTimeDependentMarkovJumpDensity
            referenceInitial referenceRates duration history))⁻¹ *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovJumpDensity
              initial rates duration history) =
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovJumpDensity initial rates duration history /
            finiteStateTimeDependentMarkovJumpDensity
              referenceInitial referenceRates duration history) := by
          rw [ENNReal.ofReal_div_of_pos hReferenceDensityPos, div_eq_mul_inv, mul_comm]
      _ = _ := by
        rw [finiteStateTimeDependentMarkovJumpDensity_div_eq_exp_logAction
          initial referenceInitial rates referenceRates duration history
            hPositive hReferencePositive]

/-- The common-base representation's candidate measure is the explicit physical candidate law. -/
theorem finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    (finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
      hInitialSupport hRateSupport duration).candidateMeasure =
      finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration := by
  unfold CommonBaseDensityAction.candidateMeasure
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
  exact (finiteStateTimeDependentMarkovJumpDensityMeasure_eq_withDensity
    initial rates duration).symm

/-- The common-base representation's comparison measure is the explicit physical reference law. -/
theorem finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    (finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
      hInitialSupport hRateSupport duration).comparisonMeasure =
      finiteStateTimeDependentMarkovJumpDensityMeasure
        referenceInitial referenceRates duration := by
  unfold CommonBaseDensityAction.comparisonMeasure
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
  exact (finiteStateTimeDependentMarkovJumpDensityMeasure_eq_withDensity
    referenceInitial referenceRates duration).symm

/-- Exact physical Girsanov identity: exponentially tilting the normalized reference law by the
complete time-dependent action gives the normalized candidate law. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_withDensity_expLogAction
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    (finiteStateTimeDependentMarkovJumpDensityMeasure
        referenceInitial referenceRates duration).withDensity
      (fun history => ENNReal.ofReal
        (Real.exp (finiteStateTimeDependentMarkovJumpLogAction
          initial referenceInitial rates referenceRates duration history))) =
      finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration := by
  let representation := finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    hInitialSupport hRateSupport duration
  have hTilt := representation.comparisonMeasure_withDensity_expAction
  rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
      hInitialSupport hRateSupport duration,
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
      hInitialSupport hRateSupport duration] at hTilt
  exact hTilt

/-- Common support makes the normalized physical candidate law absolutely continuous with
respect to the normalized physical reference law. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_absolutelyContinuous
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration ≪
      finiteStateTimeDependentMarkovJumpDensityMeasure
        referenceInitial referenceRates duration := by
  let representation := finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    hInitialSupport hRateSupport duration
  have hAbsoluteContinuity := representation.candidateMeasure_absolutelyContinuous
  rwa [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
      hInitialSupport hRateSupport duration,
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
      hInitialSupport hRateSupport duration] at hAbsoluteContinuity

/-- The exact Radon--Nikodym derivative is the exponential of the complete physical
time-dependent action. -/
theorem rnDeriv_finiteStateTimeDependentMarkovJumpDensityMeasure_eq_exp_logAction
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    (finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration).rnDeriv
        (finiteStateTimeDependentMarkovJumpDensityMeasure
          referenceInitial referenceRates duration) =ᵐ[
            finiteStateTimeDependentMarkovJumpDensityMeasure
              referenceInitial referenceRates duration]
      fun history => ENNReal.ofReal
        (Real.exp (finiteStateTimeDependentMarkovJumpLogAction
          initial referenceInitial rates referenceRates duration history)) := by
  let representation := finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    hInitialSupport hRateSupport duration
  have hDerivative := representation.rnDeriv_candidateMeasure_eq_exp_action
  rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
      hInitialSupport hRateSupport duration,
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
      hInitialSupport hRateSupport duration] at hDerivative
  exact hDerivative

/-- The real log likelihood on the normalized candidate law is exactly the complete physical
time-dependent action. -/
theorem llr_finiteStateTimeDependentMarkovJumpDensityMeasure
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) :
    llr (finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration)
        (finiteStateTimeDependentMarkovJumpDensityMeasure
          referenceInitial referenceRates duration) =ᵐ[
            finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration]
      finiteStateTimeDependentMarkovJumpLogAction
        initial referenceInitial rates referenceRates duration := by
  let representation := finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    hInitialSupport hRateSupport duration
  have hLikelihood := representation.llr_candidateMeasure_eq_action
  rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
      hInitialSupport hRateSupport duration,
    finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
      hInitialSupport hRateSupport duration] at hLikelihood
  exact hLikelihood

/-- The negative exponential of the complete candidate-to-reference action has exact expectation
one under the normalized physical candidate law. -/
theorem lintegral_exp_neg_finiteStateTimeDependentMarkovJumpLogAction
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    ∫⁻ history,
        ENNReal.ofReal (Real.exp
          (-finiteStateTimeDependentMarkovJumpLogAction
            initial referenceInitial rates referenceRates duration history))
      ∂finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration = 1 := by
  let representation := finiteStateTimeDependentMarkovJumpCommonBaseDensityAction
    hInitialSupport hRateSupport duration
  have hCandidateNormalized : representation.candidateMeasure Set.univ = 1 := by
    rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
      hInitialSupport hRateSupport duration]
    exact finiteStateTimeDependentMarkovJumpDensityMeasure_univ
      initial rates hDuration
  have hComparisonNormalized : representation.comparisonMeasure Set.univ = 1 := by
    rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_comparisonMeasure
      hInitialSupport hRateSupport duration]
    exact finiteStateTimeDependentMarkovJumpDensityMeasure_univ
      referenceInitial referenceRates hDuration
  have hFluctuation := representation.lintegral_exp_neg_action
    hCandidateNormalized hComparisonNormalized
  rw [finiteStateTimeDependentMarkovJumpCommonBaseDensityAction_candidateMeasure
    hInitialSupport hRateSupport duration] at hFluctuation
  exact hFluctuation

end

end FiniteMarkovProcesses.InformationTheory
