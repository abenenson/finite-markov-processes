/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# Log actions represented by two densities on one common base

This module packages the reusable measure theory behind an exact log-density action. A candidate
and comparison density live on one sigma-finite base, have the same pointwise zero set and finite
values, and their density ratio is the exponential of a measurable real action wherever the
comparison density is nonzero.

The resulting theorems derive the Radon--Nikodym derivative, real log likelihood, exponential
tilt, integral fluctuation identity, and expected-action/KL identity. Source-specific modules
remain responsible for constructing the carrier, base, densities, normalization, support, action,
and integrability.

## Main results

- `CommonBaseDensityAction.comparisonMeasure_withDensity_densityRatio`: exact common-base tilt.
- `CommonBaseDensityAction.rnDeriv_candidateMeasure_eq_exp_action`: exact RN derivative.
- `CommonBaseDensityAction.llr_candidateMeasure_eq_action`: real log likelihood on the candidate.
- `CommonBaseDensityAction.exp_neg_threshold_mul_candidateMeasure_event_le_comparisonMeasure`:
  finite-event change-of-measure lower estimate.
- `CommonBaseDensityAction.lintegral_exp_neg_action`: extended-real fluctuation identity.
- `CommonBaseDensityAction.integral_action_eq_klDiv`: expected action is finite KL when integrable.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped ENNReal
open _root_.InformationTheory

universe u

/-- Complete data needed to represent a real log action by two finite densities on one common
base measure. The same-zero and ratio fields are pointwise so source-specific support bookkeeping
cannot be hidden in an almost-everywhere coercion. -/
structure CommonBaseDensityAction (Carrier : Type u) [MeasurableSpace Carrier]
    (base : Measure Carrier) where
  /-- Candidate density against the common base. -/
  candidateDensity : Carrier → ℝ≥0∞
  /-- Comparison density against the common base. -/
  comparisonDensity : Carrier → ℝ≥0∞
  /-- Real complete-history log action. -/
  action : Carrier → ℝ
  /-- Candidate density is measurable. -/
  measurable_candidateDensity : Measurable candidateDensity
  /-- Comparison density is measurable. -/
  measurable_comparisonDensity : Measurable comparisonDensity
  /-- The action is measurable. -/
  measurable_action : Measurable action
  /-- Candidate and comparison have identical pointwise zero support. -/
  candidateDensity_eq_zero_iff : ∀ history,
    candidateDensity history = 0 ↔ comparisonDensity history = 0
  /-- Candidate density takes no infinite value. -/
  candidateDensity_ne_top : ∀ history, candidateDensity history ≠ ⊤
  /-- Comparison density takes no infinite value. -/
  comparisonDensity_ne_top : ∀ history, comparisonDensity history ≠ ⊤
  /-- On positive comparison support, the density ratio is the exponential of the action. -/
  densityRatio_eq_exp_action_of_comparison_ne_zero : ∀ history,
    comparisonDensity history ≠ 0 →
      (comparisonDensity history)⁻¹ * candidateDensity history =
        ENNReal.ofReal (Real.exp (action history))

namespace CommonBaseDensityAction

variable {Carrier : Type u} [MeasurableSpace Carrier] {base : Measure Carrier}

/-- Candidate measure induced by the common base and candidate density. -/
noncomputable def candidateMeasure
    (representation : CommonBaseDensityAction Carrier base) : Measure Carrier :=
  base.withDensity representation.candidateDensity

/-- Comparison measure induced by the common base and comparison density. -/
noncomputable def comparisonMeasure
    (representation : CommonBaseDensityAction Carrier base) : Measure Carrier :=
  base.withDensity representation.comparisonDensity

/-- Extended-real candidate/comparison density ratio. Its common-zero value is irrelevant to
either induced measure. -/
noncomputable def densityRatio
    (representation : CommonBaseDensityAction Carrier base) : Carrier → ℝ≥0∞ :=
  fun history ↦
    (representation.comparisonDensity history)⁻¹ *
      representation.candidateDensity history

/-- The common-base density ratio is measurable. -/
theorem measurable_densityRatio
    (representation : CommonBaseDensityAction Carrier base) :
    Measurable representation.densityRatio :=
  representation.measurable_comparisonDensity.inv.mul
    representation.measurable_candidateDensity

/-- Multiplying the comparison density by the ratio recovers the candidate density pointwise,
including their common zero set. -/
theorem comparisonDensity_mul_densityRatio
    (representation : CommonBaseDensityAction Carrier base) (history : Carrier) :
    representation.comparisonDensity history * representation.densityRatio history =
      representation.candidateDensity history := by
  by_cases hComparison : representation.comparisonDensity history = 0
  · have hCandidate : representation.candidateDensity history = 0 :=
      (representation.candidateDensity_eq_zero_iff history).2 hComparison
    simp [densityRatio, hComparison, hCandidate]
  · unfold densityRatio
    rw [← mul_assoc,
      ENNReal.mul_inv_cancel hComparison (representation.comparisonDensity_ne_top history),
      one_mul]

/-- The candidate measure is exactly the comparison measure tilted by the pointwise density
ratio. -/
theorem comparisonMeasure_withDensity_densityRatio
    (representation : CommonBaseDensityAction Carrier base) :
    representation.comparisonMeasure.withDensity representation.densityRatio =
      representation.candidateMeasure := by
  unfold comparisonMeasure candidateMeasure
  rw [← withDensity_mul base representation.measurable_comparisonDensity
    representation.measurable_densityRatio]
  apply congrArg base.withDensity
  funext history
  exact representation.comparisonDensity_mul_densityRatio history

/-- The candidate measure is absolutely continuous with respect to the comparison measure. -/
theorem candidateMeasure_absolutelyContinuous
    (representation : CommonBaseDensityAction Carrier base) :
    representation.candidateMeasure ≪ representation.comparisonMeasure := by
  rw [← representation.comparisonMeasure_withDensity_densityRatio]
  exact withDensity_absolutelyContinuous _ _

/-- The candidate measure is sigma-finite when the common base is sigma-finite. -/
noncomputable instance instSigmaFiniteCandidateMeasure [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base) :
    SigmaFinite representation.candidateMeasure := by
  unfold candidateMeasure
  exact SigmaFinite.withDensity_of_ne_top' representation.candidateDensity_ne_top

/-- The comparison measure is sigma-finite when the common base is sigma-finite. -/
noncomputable instance instSigmaFiniteComparisonMeasure [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base) :
    SigmaFinite representation.comparisonMeasure := by
  unfold comparisonMeasure
  exact SigmaFinite.withDensity_of_ne_top' representation.comparisonDensity_ne_top

/-- Exact Radon--Nikodym derivative between the two common-base measures. -/
theorem rnDeriv_candidateMeasure [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base) :
    representation.candidateMeasure.rnDeriv representation.comparisonMeasure =ᵐ[
        representation.comparisonMeasure]
      representation.densityRatio := by
  rw [← representation.comparisonMeasure_withDensity_densityRatio]
  exact Measure.rnDeriv_withDensity _ representation.measurable_densityRatio

/-- The comparison measure almost surely occupies its nonzero density support. -/
theorem eventually_comparisonDensity_ne_zero
    (representation : CommonBaseDensityAction Carrier base) :
    ∀ᵐ history ∂representation.comparisonMeasure,
      representation.comparisonDensity history ≠ 0 := by
  unfold comparisonMeasure
  apply (ae_withDensity_iff representation.measurable_comparisonDensity).mpr
  exact ae_of_all _ fun history hDensity ↦ by
    intro hZero
    apply hDensity
    simp [hZero]

/-- The density ratio is the exponential of the action on comparison-almost-every history. -/
theorem densityRatio_eq_exp_action
    (representation : CommonBaseDensityAction Carrier base) :
    representation.densityRatio =ᵐ[representation.comparisonMeasure]
      fun history ↦ ENNReal.ofReal (Real.exp (representation.action history)) := by
  filter_upwards [representation.eventually_comparisonDensity_ne_zero] with history hDensity
  exact representation.densityRatio_eq_exp_action_of_comparison_ne_zero history hDensity

/-- The exact RN derivative is the exponential of the common-base action. -/
theorem rnDeriv_candidateMeasure_eq_exp_action [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base) :
    representation.candidateMeasure.rnDeriv representation.comparisonMeasure =ᵐ[
        representation.comparisonMeasure]
      fun history ↦ ENNReal.ofReal (Real.exp (representation.action history)) :=
  representation.rnDeriv_candidateMeasure.trans representation.densityRatio_eq_exp_action

/-- The real log likelihood on the candidate measure is exactly the supplied action. -/
theorem llr_candidateMeasure_eq_action [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base) :
    llr representation.candidateMeasure representation.comparisonMeasure =ᵐ[
        representation.candidateMeasure]
      representation.action := by
  have hRN := representation.candidateMeasure_absolutelyContinuous.ae_le
    representation.rnDeriv_candidateMeasure_eq_exp_action
  filter_upwards [hRN] with history hDerivative
  rw [llr, hDerivative, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

/-- Extended-real exponential of the action. -/
noncomputable def expActionENNReal
    (representation : CommonBaseDensityAction Carrier base) : Carrier → ℝ≥0∞ :=
  fun history ↦ ENNReal.ofReal (Real.exp (representation.action history))

/-- The extended-real exponential action is measurable. -/
theorem measurable_expActionENNReal
    (representation : CommonBaseDensityAction Carrier base) :
    Measurable representation.expActionENNReal :=
  (representation.measurable_action.exp).ennreal_ofReal

/-- The candidate is the comparison measure exponentially tilted by the action. -/
theorem comparisonMeasure_withDensity_expAction
    (representation : CommonBaseDensityAction Carrier base) :
    representation.comparisonMeasure.withDensity representation.expActionENNReal =
      representation.candidateMeasure := by
  calc
    _ = representation.comparisonMeasure.withDensity representation.densityRatio :=
      withDensity_congr_ae representation.densityRatio_eq_exp_action.symm
    _ = _ := representation.comparisonMeasure_withDensity_densityRatio

/-- If the complete action is at most one threshold throughout a measurable event, then the
candidate event mass is at most the corresponding exponential factor times its comparison mass. -/
theorem candidateMeasure_event_le_exp_threshold_mul_comparisonMeasure
    (representation : CommonBaseDensityAction Carrier base)
    {event : Set Carrier} (hEvent : MeasurableSet event) (threshold : ℝ)
    (hAction : ∀ history ∈ event, representation.action history ≤ threshold) :
    representation.candidateMeasure event ≤
      ENNReal.ofReal (Real.exp threshold) * representation.comparisonMeasure event := by
  rw [← representation.comparisonMeasure_withDensity_expAction]
  rw [withDensity_apply _ hEvent]
  calc
    (∫⁻ history in event, representation.expActionENNReal history
        ∂representation.comparisonMeasure) ≤
      ∫⁻ _history in event, ENNReal.ofReal (Real.exp threshold)
        ∂representation.comparisonMeasure := by
          apply setLIntegral_mono' hEvent
          intro history hHistory
          unfold expActionENNReal
          exact ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hAction history hHistory))
    _ = _ := setLIntegral_const event _

/-- Finite-event Girsanov lower estimate: an action upper bound on an event turns candidate mass
into an explicit lower bound on the comparison mass. -/
theorem exp_neg_threshold_mul_candidateMeasure_event_le_comparisonMeasure
    (representation : CommonBaseDensityAction Carrier base)
    {event : Set Carrier} (hEvent : MeasurableSet event) (threshold : ℝ)
    (hAction : ∀ history ∈ event, representation.action history ≤ threshold) :
    ENNReal.ofReal (Real.exp (-threshold)) * representation.candidateMeasure event ≤
      representation.comparisonMeasure event := by
  calc
    ENNReal.ofReal (Real.exp (-threshold)) * representation.candidateMeasure event ≤
        ENNReal.ofReal (Real.exp (-threshold)) *
          (ENNReal.ofReal (Real.exp threshold) *
            representation.comparisonMeasure event) :=
      mul_le_mul_right (representation.candidateMeasure_event_le_exp_threshold_mul_comparisonMeasure
        hEvent threshold hAction) _
    _ = representation.comparisonMeasure event := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp

/-- The positive and negative exponential action factors multiply to one pointwise. -/
theorem expActionENNReal_mul_exp_neg
    (representation : CommonBaseDensityAction Carrier base) (history : Carrier) :
    representation.expActionENNReal history *
        ENNReal.ofReal (Real.exp (-representation.action history)) = 1 := by
  unfold expActionENNReal
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

/-- Exact extended-real integral fluctuation theorem. Both induced measures must pass explicit
normalization gates before this probability-law interpretation is available. -/
theorem lintegral_exp_neg_action
    (representation : CommonBaseDensityAction Carrier base)
    (_hCandidateNormalized : representation.candidateMeasure Set.univ = 1)
    (hComparisonNormalized : representation.comparisonMeasure Set.univ = 1) :
    ∫⁻ history,
        ENNReal.ofReal (Real.exp (-representation.action history))
      ∂representation.candidateMeasure = 1 := by
  rw [← representation.comparisonMeasure_withDensity_expAction]
  rw [lintegral_withDensity_eq_lintegral_mul representation.comparisonMeasure
    representation.measurable_expActionENNReal
    (g := fun history ↦ ENNReal.ofReal (Real.exp (-representation.action history)))
    (by simpa only [Pi.neg_def] using
      (representation.measurable_action.neg.exp.ennreal_ofReal))]
  simp only [Pi.mul_apply]
  simp_rw [representation.expActionENNReal_mul_exp_neg]
  simpa using hComparisonNormalized

/-- The real exponential fluctuation observable is integrable and has expectation one. -/
theorem integral_exp_neg_action
    (representation : CommonBaseDensityAction Carrier base)
    (hCandidateNormalized : representation.candidateMeasure Set.univ = 1)
    (hComparisonNormalized : representation.comparisonMeasure Set.univ = 1) :
    Integrable (fun history ↦ Real.exp (-representation.action history))
        representation.candidateMeasure ∧
      ∫ history, Real.exp (-representation.action history)
          ∂representation.candidateMeasure = 1 := by
  have hLIntegral := representation.lintegral_exp_neg_action
    hCandidateNormalized hComparisonNormalized
  have hMeasurable : Measurable fun history ↦
      Real.exp (-representation.action history) := representation.measurable_action.neg.exp
  have hNonnegative : ∀ᵐ history ∂representation.candidateMeasure,
      0 ≤ Real.exp (-representation.action history) :=
    ae_of_all _ fun _ ↦ (Real.exp_pos _).le
  have hIntegrable : Integrable
      (fun history ↦ Real.exp (-representation.action history))
      representation.candidateMeasure := by
    constructor
    · exact hMeasurable.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_ofReal hNonnegative, hLIntegral]
      exact ENNReal.one_lt_top
  refine ⟨hIntegrable, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hNonnegative hMeasurable.aestronglyMeasurable,
    hLIntegral]
  norm_num

/-- With an integrable action, its candidate expectation is the finite real KL divergence. -/
theorem integral_action_eq_klDiv [SigmaFinite base]
    (representation : CommonBaseDensityAction Carrier base)
    (hCandidateNormalized : representation.candidateMeasure Set.univ = 1)
    (hComparisonNormalized : representation.comparisonMeasure Set.univ = 1)
    (hActionIntegrable : Integrable representation.action representation.candidateMeasure) :
    klDiv representation.candidateMeasure representation.comparisonMeasure ≠ ⊤ ∧
      ∫ history, representation.action history ∂representation.candidateMeasure =
        (klDiv representation.candidateMeasure representation.comparisonMeasure).toReal := by
  let : IsProbabilityMeasure representation.candidateMeasure :=
    ⟨hCandidateNormalized⟩
  let : IsProbabilityMeasure representation.comparisonMeasure :=
    ⟨hComparisonNormalized⟩
  have hAC := representation.candidateMeasure_absolutelyContinuous
  have hLLR := representation.llr_candidateMeasure_eq_action
  have hLLRIntegrable :
      Integrable (llr representation.candidateMeasure representation.comparisonMeasure)
        representation.candidateMeasure := hActionIntegrable.congr hLLR.symm
  constructor
  · exact klDiv_ne_top_iff.mpr ⟨hAC, hLLRIntegrable⟩
  · calc
      _ = ∫ history,
          llr representation.candidateMeasure representation.comparisonMeasure history
            ∂representation.candidateMeasure := integral_congr_ae hLLR.symm
      _ = _ := (toReal_klDiv_of_measure_eq hAC (by simp)).symm

end CommonBaseDensityAction

end FiniteMarkovProcesses.InformationTheory
