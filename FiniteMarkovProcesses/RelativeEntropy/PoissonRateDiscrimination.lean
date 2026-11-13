/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Poisson rate discrimination and activity selection

This file develops the scalar discrimination between positive Poisson intensities and classifies
an information-minus-activity objective. It also identifies the unique affine compatibility
between that objective and an independently chosen comparison intensity.

The parameters are integrated expected counts over one experiment. The final results expose how
physical rates transform when the clock duration changes. No comparison intensity in this file is
identified as a thermodynamic time reverse.

## Main results

- `poissonRateDiscrimination_nonneg`: nonnegativity of Poisson rate discrimination.
- `poissonRateDiscrimination_eq_zero_iff`: literal equality classification.
- `poissonActivityObjective_eq_gauge_sub_discrimination`: exact selected-intensity identity.
- `poissonActivityObjective_eq_selected_iff`: literal unique activity optimizer.
- `poissonOperationalCompatibility_iff`: full-fibre affine compatibility classifier.
- `contactIntensity_clockChange`: covariance of integrated intensity under a clock change.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open _root_.InformationTheory

/-- Scalar discrimination between a law intensity and a positive reference intensity. -/
noncomputable def poissonRateDiscrimination
    (lawIntensity referenceIntensity : ℝ) : ℝ :=
  lawIntensity * Real.log (lawIntensity / referenceIntensity) -
    lawIntensity + referenceIntensity

/-- Poisson discrimination is a positive reference times Mathlib's normalized `klFun`. -/
theorem poissonRateDiscrimination_eq_reference_mul_klFun
    {lawIntensity referenceIntensity : ℝ} (hReference : 0 < referenceIntensity) :
    poissonRateDiscrimination lawIntensity referenceIntensity =
      referenceIntensity * klFun (lawIntensity / referenceIntensity) := by
  unfold poissonRateDiscrimination klFun
  field_simp
  ring

/-- Poisson rate discrimination is nonnegative on nonnegative law intensities. -/
theorem poissonRateDiscrimination_nonneg
    {lawIntensity referenceIntensity : ℝ}
    (hLaw : 0 ≤ lawIntensity) (hReference : 0 < referenceIntensity) :
    0 ≤ poissonRateDiscrimination lawIntensity referenceIntensity := by
  rw [poissonRateDiscrimination_eq_reference_mul_klFun hReference]
  exact mul_nonneg hReference.le (klFun_nonneg (div_nonneg hLaw hReference.le))

/-- At positive reference intensity, Poisson discrimination is continuous in the law
intensity, including at zero. -/
theorem continuous_poissonRateDiscrimination_left
    {referenceIntensity : ℝ} (hReference : 0 < referenceIntensity) :
    Continuous fun lawIntensity =>
      poissonRateDiscrimination lawIntensity referenceIntensity := by
  have hFormula :
      (fun lawIntensity =>
        poissonRateDiscrimination lawIntensity referenceIntensity) =
      fun lawIntensity =>
        lawIntensity * Real.log lawIntensity -
          lawIntensity * Real.log referenceIntensity -
            lawIntensity + referenceIntensity := by
    funext lawIntensity
    by_cases hLaw : lawIntensity = 0
    · simp [hLaw, poissonRateDiscrimination]
    · rw [poissonRateDiscrimination, Real.log_div hLaw hReference.ne']
      ring
  rw [hFormula]
  fun_prop

/-- At positive reference intensity, Poisson discrimination is convex in every nonnegative law
intensity. -/
theorem convexOn_poissonRateDiscrimination_left
    {referenceIntensity : ℝ} (hReference : 0 < referenceIntensity) :
    ConvexOn ℝ (Set.Ici 0)
      (fun lawIntensity =>
        poissonRateDiscrimination lawIntensity referenceIntensity) := by
  let scale : ℝ →ᵃ[ℝ] ℝ :=
    (1 / referenceIntensity) • AffineMap.id ℝ ℝ
  have hScale (lawIntensity : ℝ) :
      scale lawIntensity = lawIntensity / referenceIntensity := by
    simp [scale]
    ring
  have hComposition :
      ConvexOn ℝ (Set.Ici 0)
        (fun lawIntensity => klFun (lawIntensity / referenceIntensity)) := by
    have hPreimage := convexOn_klFun.comp_affineMap scale
    have hSubset : Set.Ici (0 : ℝ) ⊆ scale ⁻¹' Set.Ici 0 := by
      intro lawIntensity hLaw
      change 0 ≤ scale lawIntensity
      rw [hScale]
      exact div_nonneg hLaw hReference.le
    have hRestricted := hPreimage.subset hSubset (convex_Ici 0)
    convert hRestricted using 1
    funext lawIntensity
    simp only [Function.comp_apply, hScale]
  have hScaled := ConvexOn.smul hReference.le hComposition
  simpa only [smul_eq_mul,
    poissonRateDiscrimination_eq_reference_mul_klFun hReference] using hScaled

/-- Every intermediate nonnegative law intensity is controlled by the two endpoint costs; the
displayed additive bound is the form needed for dominated convergence. -/
theorem poissonRateDiscrimination_le_reference_add_upperDiscrimination
    {lawIntensity upperIntensity referenceIntensity : ℝ}
    (hLaw : 0 ≤ lawIntensity) (hUpper : lawIntensity ≤ upperIntensity)
    (hReference : 0 < referenceIntensity) :
    poissonRateDiscrimination lawIntensity referenceIntensity ≤
      referenceIntensity +
        poissonRateDiscrimination upperIntensity referenceIntensity := by
  have hUpperNonnegative : 0 ≤ upperIntensity := hLaw.trans hUpper
  have hEndpointBound :=
    (convexOn_poissonRateDiscrimination_left hReference).le_max_of_mem_Icc
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      hUpperNonnegative
      (show lawIntensity ∈ Set.Icc 0 upperIntensity from ⟨hLaw, hUpper⟩)
  have hUpperCostNonnegative :
      0 ≤ poissonRateDiscrimination upperIntensity referenceIntensity :=
    poissonRateDiscrimination_nonneg hUpperNonnegative hReference
  calc
    poissonRateDiscrimination lawIntensity referenceIntensity ≤
        max (poissonRateDiscrimination 0 referenceIntensity)
          (poissonRateDiscrimination upperIntensity referenceIntensity) := hEndpointBound
    _ = max referenceIntensity
        (poissonRateDiscrimination upperIntensity referenceIntensity) := by
      simp [poissonRateDiscrimination]
    _ ≤ referenceIntensity +
        poissonRateDiscrimination upperIntensity referenceIntensity := by
      exact max_le (le_add_of_nonneg_right hUpperCostNonnegative)
        (le_add_of_nonneg_left hReference.le)

/-- Adding one copy of the reference intensity increases Poisson discrimination by at most the
original law intensity. -/
theorem poissonRateDiscrimination_add_reference_le
    {lawIntensity referenceIntensity : ℝ}
    (hLaw : 0 ≤ lawIntensity) (hReference : 0 < referenceIntensity) :
    poissonRateDiscrimination (lawIntensity + referenceIntensity) referenceIntensity ≤
      poissonRateDiscrimination lawIntensity referenceIntensity + lawIntensity := by
  by_cases hLawZero : lawIntensity = 0
  · subst lawIntensity
    simpa [poissonRateDiscrimination] using hReference.le
  have hLawPositive : 0 < lawIntensity := lt_of_le_of_ne hLaw (Ne.symm hLawZero)
  let ratio := lawIntensity / referenceIntensity
  have hRatioPositive : 0 < ratio := div_pos hLawPositive hReference
  have hRatioIdentity :
      (lawIntensity + referenceIntensity) / referenceIntensity = ratio + 1 := by
    dsimp only [ratio]
    field_simp [hReference.ne']
  have hLogFactor :
      Real.log (ratio + 1) = Real.log ratio + Real.log (1 + 1 / ratio) := by
    rw [← Real.log_mul hRatioPositive.ne' (by positivity : (1 + 1 / ratio) ≠ 0)]
    congr 1
    field_simp [hRatioPositive.ne']
  have hLogRatioAddOne : Real.log (ratio + 1) ≤ ratio := by
    have hBound := Real.log_le_sub_one_of_pos (by positivity : 0 < ratio + 1)
    linarith
  have hLogReciprocalAddOne : Real.log (1 + 1 / ratio) ≤ 1 / ratio := by
    have hBound := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / ratio)
    linarith
  have hScaledLogReciprocal :
      ratio * Real.log (1 + 1 / ratio) ≤ 1 := by
    calc
      ratio * Real.log (1 + 1 / ratio) ≤ ratio * (1 / ratio) :=
        mul_le_mul_of_nonneg_left hLogReciprocalAddOne hRatioPositive.le
      _ = 1 := by field_simp [hRatioPositive.ne']
  have hKlFun : klFun (ratio + 1) ≤ klFun ratio + ratio := by
    unfold klFun
    rw [hLogFactor]
    nlinarith
  rw [poissonRateDiscrimination_eq_reference_mul_klFun hReference,
    poissonRateDiscrimination_eq_reference_mul_klFun hReference,
    hRatioIdentity]
  have hScaled := mul_le_mul_of_nonneg_left hKlFun hReference.le
  calc
    referenceIntensity * klFun (ratio + 1) ≤
        referenceIntensity * (klFun ratio + ratio) := hScaled
    _ = referenceIntensity * klFun ratio + lawIntensity := by
      dsimp only [ratio]
      field_simp [hReference.ne']

/-- Every exponential dual evaluation lies below the Poisson discrimination.  This is the
one-channel Fenchel inequality used by directional-flow large-deviation dual formulas. -/
theorem poissonExponentialDualEvaluation_le_discrimination
    {lawIntensity referenceIntensity exponent : ℝ}
    (hLaw : 0 ≤ lawIntensity) (hReference : 0 < referenceIntensity) :
    lawIntensity * exponent - referenceIntensity * (Real.exp exponent - 1) ≤
      poissonRateDiscrimination lawIntensity referenceIntensity := by
  by_cases hLawZero : lawIntensity = 0
  · subst lawIntensity
    unfold poissonRateDiscrimination
    simp only [zero_div, Real.log_zero, zero_mul, zero_sub]
    have hProduct : 0 ≤ referenceIntensity * Real.exp exponent := by positivity
    nlinarith
  have hLawPositive : 0 < lawIntensity := lt_of_le_of_ne hLaw (Ne.symm hLawZero)
  have hShiftedReferencePositive :
      0 < referenceIntensity * Real.exp exponent := by positivity
  have hShiftedDiscriminationNonnegative :=
    poissonRateDiscrimination_nonneg hLaw hShiftedReferencePositive
  have hIdentity :
      poissonRateDiscrimination lawIntensity
          (referenceIntensity * Real.exp exponent) =
        poissonRateDiscrimination lawIntensity referenceIntensity -
          (lawIntensity * exponent -
            referenceIntensity * (Real.exp exponent - 1)) := by
    unfold poissonRateDiscrimination
    rw [Real.log_div hLawPositive.ne'
        (mul_ne_zero hReference.ne' (Real.exp_ne_zero exponent)),
      Real.log_div hLawPositive.ne' hReference.ne',
      Real.log_mul hReference.ne' (Real.exp_ne_zero exponent), Real.log_exp]
    ring
  rw [hIdentity] at hShiftedDiscriminationNonnegative
  linarith

/-- Poisson discrimination controls the observed intensity up to the explicit reference-rate
correction `(exp 1 - 1) * referenceIntensity`.  This is the scalar coercivity estimate used to
reduce hybrid-BV compactness to bounded directional-flow variation. -/
theorem lawIntensity_le_poissonRateDiscrimination_add_referenceCorrection
    {lawIntensity referenceIntensity : ℝ}
    (hLaw : 0 ≤ lawIntensity) (hReference : 0 < referenceIntensity) :
    lawIntensity ≤
      poissonRateDiscrimination lawIntensity referenceIntensity +
        (Real.exp 1 - 1) * referenceIntensity := by
  by_cases hLawZero : lawIntensity = 0
  · subst lawIntensity
    unfold poissonRateDiscrimination
    simp only [zero_div, Real.log_zero, zero_mul]
    have hProduct : 0 ≤ Real.exp 1 * referenceIntensity := by positivity
    nlinarith
  have hLawPos : 0 < lawIntensity := lt_of_le_of_ne hLaw (Ne.symm hLawZero)
  have hRatioNonnegative :
      0 ≤ lawIntensity / (referenceIntensity * Real.exp 1) := by
    positivity
  have hScaledNonnegative :
      0 ≤ referenceIntensity * Real.exp 1 *
        klFun (lawIntensity / (referenceIntensity * Real.exp 1)) :=
    mul_nonneg (mul_nonneg hReference.le (Real.exp_pos 1).le)
      (klFun_nonneg hRatioNonnegative)
  have hIdentity :
      referenceIntensity * Real.exp 1 *
          klFun (lawIntensity / (referenceIntensity * Real.exp 1)) =
        poissonRateDiscrimination lawIntensity referenceIntensity +
          (Real.exp 1 - 1) * referenceIntensity - lawIntensity := by
    unfold poissonRateDiscrimination klFun
    rw [Real.log_div hLawPos.ne'
      (mul_ne_zero hReference.ne' (Real.exp_ne_zero 1)),
      Real.log_div hLawPos.ne' hReference.ne',
      Real.log_mul hReference.ne' (Real.exp_ne_zero 1),
      Real.log_exp]
    field_simp
    ring
  rw [hIdentity] at hScaledNonnegative
  linarith

/-- Positive Poisson intensities have zero discrimination exactly when they are equal. -/
theorem poissonRateDiscrimination_eq_zero_iff
    {lawIntensity referenceIntensity : ℝ}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) :
    poissonRateDiscrimination lawIntensity referenceIntensity = 0 ↔
      lawIntensity = referenceIntensity := by
  rw [poissonRateDiscrimination_eq_reference_mul_klFun hReference,
    mul_eq_zero, klFun_eq_zero_iff (div_nonneg hLaw.le hReference.le)]
  constructor
  · rintro (hReferenceZero | hRatio)
    · exact False.elim (hReference.ne' hReferenceZero)
    · exact (div_eq_one_iff_eq hReference.ne').mp hRatio
  · intro hEqual
    exact Or.inr ((div_eq_one_iff_eq hReference.ne').mpr hEqual)

/-- Distinct positive Poisson intensities have strictly positive discrimination. -/
theorem poissonRateDiscrimination_pos
    {lawIntensity referenceIntensity : ℝ}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity)
    (hDistinct : lawIntensity ≠ referenceIntensity) :
    0 < poissonRateDiscrimination lawIntensity referenceIntensity := by
  exact lt_of_le_of_ne
    (poissonRateDiscrimination_nonneg hLaw.le hReference)
    (Ne.symm (mt (poissonRateDiscrimination_eq_zero_iff hLaw hReference).mp hDistinct))

/-- Information relative to a passive Poisson intensity. -/
noncomputable def poissonPassiveInformation
    (baseIntensity controlledIntensity : ℝ) : ℝ :=
  -poissonRateDiscrimination controlledIntensity baseIntensity

/-- Dynamical activity, represented by the expected contact count. -/
def poissonContactActivity (controlledIntensity : ℝ) : ℝ := controlledIntensity

/-- Passive-relative information minus a covector paired with contact activity. -/
noncomputable def poissonActivityObjective
    (baseIntensity multiplier controlledIntensity : ℝ) : ℝ :=
  poissonPassiveInformation baseIntensity controlledIntensity -
    multiplier * poissonContactActivity controlledIntensity

/-- The positive intensity selected by the activity covector. -/
noncomputable def selectedPoissonIntensity (baseIntensity multiplier : ℝ) : ℝ :=
  baseIntensity * Real.exp (-multiplier)

/-- A positive passive intensity gives a positive selected intensity. -/
theorem selectedPoissonIntensity_pos {baseIntensity multiplier : ℝ}
    (hBase : 0 < baseIntensity) :
    0 < selectedPoissonIntensity baseIntensity multiplier := by
  exact mul_pos hBase (Real.exp_pos _)

/-- The objective is a gauge minus discrimination from its selected intensity. -/
theorem poissonActivityObjective_eq_gauge_sub_discrimination
    {baseIntensity multiplier controlledIntensity : ℝ}
    (hBase : 0 < baseIntensity) (hControlled : 0 < controlledIntensity) :
    poissonActivityObjective baseIntensity multiplier controlledIntensity =
      selectedPoissonIntensity baseIntensity multiplier - baseIntensity -
        poissonRateDiscrimination controlledIntensity
          (selectedPoissonIntensity baseIntensity multiplier) := by
  unfold poissonActivityObjective poissonPassiveInformation poissonContactActivity
  unfold poissonRateDiscrimination selectedPoissonIntensity
  rw [Real.log_div hControlled.ne' hBase.ne',
    Real.log_div hControlled.ne' (mul_ne_zero hBase.ne' (Real.exp_ne_zero _)),
    Real.log_mul hBase.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The selected intensity dominates the full positive-intensity fibre. -/
theorem poissonActivityObjective_le_selected
    {baseIntensity multiplier controlledIntensity : ℝ}
    (hBase : 0 < baseIntensity) (hControlled : 0 < controlledIntensity) :
    poissonActivityObjective baseIntensity multiplier controlledIntensity ≤
      poissonActivityObjective baseIntensity multiplier
        (selectedPoissonIntensity baseIntensity multiplier) := by
  have hSelected := selectedPoissonIntensity_pos (multiplier := multiplier) hBase
  rw [poissonActivityObjective_eq_gauge_sub_discrimination hBase hControlled,
    poissonActivityObjective_eq_gauge_sub_discrimination hBase hSelected]
  rw [(poissonRateDiscrimination_eq_zero_iff hSelected hSelected).2 rfl, sub_zero]
  exact sub_le_self _ (poissonRateDiscrimination_nonneg hControlled.le hSelected)

/-- Objective equality with the selected value holds exactly at the selected intensity. -/
theorem poissonActivityObjective_eq_selected_iff
    {baseIntensity multiplier controlledIntensity : ℝ}
    (hBase : 0 < baseIntensity) (hControlled : 0 < controlledIntensity) :
    poissonActivityObjective baseIntensity multiplier controlledIntensity =
        poissonActivityObjective baseIntensity multiplier
          (selectedPoissonIntensity baseIntensity multiplier) ↔
      controlledIntensity = selectedPoissonIntensity baseIntensity multiplier := by
  have hSelected := selectedPoissonIntensity_pos (multiplier := multiplier) hBase
  rw [poissonActivityObjective_eq_gauge_sub_discrimination hBase hControlled,
    poissonActivityObjective_eq_gauge_sub_discrimination hBase hSelected]
  rw [(poissonRateDiscrimination_eq_zero_iff hSelected hSelected).2 rfl, sub_zero]
  constructor
  · intro hEqual
    apply (poissonRateDiscrimination_eq_zero_iff hControlled hSelected).mp
    linarith
  · intro hEqual
    rw [hEqual, (poissonRateDiscrimination_eq_zero_iff hSelected hSelected).2 rfl]
    ring

/-- The action against an independently fixed operational comparison intensity. -/
noncomputable def poissonOperationalAction
    (referenceIntensity controlledIntensity : ℝ) : ℝ :=
  poissonRateDiscrimination controlledIntensity referenceIntensity

/-- Exact affine defect between the activity objective and operational comparison action. -/
theorem poissonActivityObjective_add_operationalAction
    {baseIntensity referenceIntensity multiplier controlledIntensity : ℝ}
    (hBase : 0 < baseIntensity) (hReference : 0 < referenceIntensity)
    (hControlled : 0 < controlledIntensity) :
    poissonActivityObjective baseIntensity multiplier controlledIntensity +
        poissonOperationalAction referenceIntensity controlledIntensity =
      referenceIntensity - baseIntensity +
        controlledIntensity * (Real.log (baseIntensity / referenceIntensity) - multiplier) := by
  unfold poissonActivityObjective poissonPassiveInformation poissonContactActivity
  unfold poissonOperationalAction poissonRateDiscrimination
  rw [Real.log_div hControlled.ne' hBase.ne',
    Real.log_div hControlled.ne' hReference.ne',
    Real.log_div hBase.ne' hReference.ne']
  ring

/-- Agreement at two distinct intensities forces the multiplier and visible affine gauge. -/
theorem poissonOperationalCompatibility_of_two_intensities
    {baseIntensity referenceIntensity multiplier gauge intensity₁ intensity₂ : ℝ}
    (hBase : 0 < baseIntensity) (hReference : 0 < referenceIntensity)
    (hIntensity₁ : 0 < intensity₁) (hIntensity₂ : 0 < intensity₂)
    (hDistinct : intensity₁ ≠ intensity₂)
    (h₁ : poissonActivityObjective baseIntensity multiplier intensity₁ =
      gauge - poissonOperationalAction referenceIntensity intensity₁)
    (h₂ : poissonActivityObjective baseIntensity multiplier intensity₂ =
      gauge - poissonOperationalAction referenceIntensity intensity₂) :
    multiplier = Real.log (baseIntensity / referenceIntensity) ∧
      gauge = referenceIntensity - baseIntensity := by
  have hDefect₁ := poissonActivityObjective_add_operationalAction
    (multiplier := multiplier) hBase hReference hIntensity₁
  have hDefect₂ := poissonActivityObjective_add_operationalAction
    (multiplier := multiplier) hBase hReference hIntensity₂
  have hGauge₁ : referenceIntensity - baseIntensity +
      intensity₁ * (Real.log (baseIntensity / referenceIntensity) - multiplier) = gauge := by
    rw [← hDefect₁]
    linarith
  have hGauge₂ : referenceIntensity - baseIntensity +
      intensity₂ * (Real.log (baseIntensity / referenceIntensity) - multiplier) = gauge := by
    rw [← hDefect₂]
    linarith
  have hProduct : (intensity₁ - intensity₂) *
      (Real.log (baseIntensity / referenceIntensity) - multiplier) = 0 := by
    calc
      _ = intensity₁ * (Real.log (baseIntensity / referenceIntensity) - multiplier) -
          intensity₂ * (Real.log (baseIntensity / referenceIntensity) - multiplier) := by
        ring
      _ = 0 := by linarith
  have hCoefficient : Real.log (baseIntensity / referenceIntensity) - multiplier = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr hDistinct)
  constructor
  · linarith
  · rw [hCoefficient, mul_zero, add_zero] at hGauge₁
    exact hGauge₁.symm

/-- Full-fibre affine compatibility holds exactly at the calibrated multiplier and gauge. -/
theorem poissonOperationalCompatibility_iff
    {baseIntensity referenceIntensity multiplier gauge : ℝ}
    (hBase : 0 < baseIntensity) (hReference : 0 < referenceIntensity) :
    (∀ controlledIntensity, 0 < controlledIntensity →
      poissonActivityObjective baseIntensity multiplier controlledIntensity =
        gauge - poissonOperationalAction referenceIntensity controlledIntensity) ↔
      multiplier = Real.log (baseIntensity / referenceIntensity) ∧
        gauge = referenceIntensity - baseIntensity := by
  constructor
  · intro h
    exact poissonOperationalCompatibility_of_two_intensities hBase hReference
      zero_lt_one (by norm_num) (by norm_num) (h 1 zero_lt_one) (h 2 (by norm_num))
  · rintro ⟨hMultiplier, hGauge⟩ controlledIntensity hControlled
    have hDefect := poissonActivityObjective_add_operationalAction
      (multiplier := multiplier) hBase hReference hControlled
    apply (eq_sub_iff_add_eq).2
    rw [hGauge]
    simpa [hMultiplier] using hDefect

/-- At the calibrated multiplier, the selected intensity is the comparison intensity. -/
theorem selectedPoissonIntensity_eq_reference
    {baseIntensity referenceIntensity multiplier : ℝ}
    (hBase : 0 < baseIntensity) (hReference : 0 < referenceIntensity)
    (hMultiplier : multiplier = Real.log (baseIntensity / referenceIntensity)) :
    selectedPoissonIntensity baseIntensity multiplier = referenceIntensity := by
  rw [hMultiplier]
  unfold selectedPoissonIntensity
  rw [Real.exp_neg, Real.exp_log (div_pos hBase hReference)]
  field_simp

/-- A smaller comparison intensity yields a positive calibrated activity multiplier. -/
theorem poissonCalibratedMultiplier_pos
    {baseIntensity referenceIntensity : ℝ}
    (hReference : 0 < referenceIntensity) (hSmaller : referenceIntensity < baseIntensity) :
    0 < Real.log (baseIntensity / referenceIntensity) := by
  exact Real.log_pos ((one_lt_div hReference).2 hSmaller)

/-- The multiplier is identifiable from the objective at any positive controlled intensity. -/
theorem poissonActivityObjective_multiplier_injective
    {baseIntensity controlledIntensity multiplier₁ multiplier₂ : ℝ}
    (hControlled : 0 < controlledIntensity) :
    poissonActivityObjective baseIntensity multiplier₁ controlledIntensity =
        poissonActivityObjective baseIntensity multiplier₂ controlledIntensity ↔
      multiplier₁ = multiplier₂ := by
  constructor
  · intro hEqual
    unfold poissonActivityObjective poissonContactActivity at hEqual
    have hProduct : controlledIntensity * (multiplier₁ - multiplier₂) = 0 := by
      calc
        _ = multiplier₁ * controlledIntensity - multiplier₂ * controlledIntensity := by
          ring
        _ = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left hControlled.ne')
  · rintro rfl
    rfl

/-- The frozen primary scalar assay selects intensity one with gauge minus one. -/
theorem poissonPrimaryScalarAssay :
    selectedPoissonIntensity 2 (Real.log 2) = 1 ∧
      ∀ controlledIntensity, 0 < controlledIntensity →
        poissonActivityObjective 2 (Real.log 2) controlledIntensity =
          -1 - poissonOperationalAction 1 controlledIntensity := by
  constructor
  · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) (by norm_num)
  · apply (poissonOperationalCompatibility_iff (by norm_num) (by norm_num)).2
    constructor <;> norm_num

/-- The independently frozen held-out assay selects intensity two with gauge minus three. -/
theorem poissonHeldoutScalarAssay :
    selectedPoissonIntensity 5 (Real.log (5 / 2)) = 2 ∧
      ∀ controlledIntensity, 0 < controlledIntensity →
        poissonActivityObjective 5 (Real.log (5 / 2)) controlledIntensity =
          -3 - poissonOperationalAction 2 controlledIntensity := by
  constructor
  · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) rfl
  · apply (poissonOperationalCompatibility_iff (by norm_num) (by norm_num)).2
    constructor
    · rfl
    · norm_num

/-- Integrated contact intensity is physical duration paired with physical contact rate. -/
def contactIntensity (clockDuration physicalRate : ℝ) : ℝ :=
  clockDuration * physicalRate

/-- Physical contact rate is integrated intensity divided by physical duration. -/
noncomputable def physicalContactRate (clockDuration intensity : ℝ) : ℝ :=
  intensity / clockDuration

/-- Converting an intensity to a physical rate and back preserves it on a nonzero clock. -/
@[simp]
theorem contactIntensity_physicalContactRate {clockDuration intensity : ℝ}
    (hClock : clockDuration ≠ 0) :
    contactIntensity clockDuration (physicalContactRate clockDuration intensity) = intensity := by
  unfold contactIntensity physicalContactRate
  rw [mul_div_cancel₀ _ hClock]

/-- Enlarging the physical clock scales the corresponding physical rate inversely. -/
theorem physicalContactRate_clockChange {scale clockDuration intensity : ℝ}
    (hScale : scale ≠ 0) (hClock : clockDuration ≠ 0) :
    physicalContactRate (scale * clockDuration) intensity =
      physicalContactRate clockDuration intensity / scale := by
  unfold physicalContactRate
  field_simp [hScale, hClock]

/-- A clock change and inverse rate change preserve integrated contact intensity. -/
theorem contactIntensity_clockChange {scale clockDuration physicalRate : ℝ}
    (hScale : scale ≠ 0) :
    contactIntensity (scale * clockDuration) (physicalRate / scale) =
      contactIntensity clockDuration physicalRate := by
  unfold contactIntensity
  field_simp [hScale]

/-- The operational affine gauge is preserved by covariant physical clock conversion. -/
theorem poissonOperationalGauge_clockChange
    {scale clockDuration baseRate referenceRate : ℝ} (hScale : scale ≠ 0) :
    contactIntensity (scale * clockDuration) (referenceRate / scale) -
        contactIntensity (scale * clockDuration) (baseRate / scale) =
      contactIntensity clockDuration referenceRate -
        contactIntensity clockDuration baseRate := by
  rw [contactIntensity_clockChange hScale, contactIntensity_clockChange hScale]

/-- Poisson discrimination is invariant under covariant physical clock conversion. -/
theorem poissonRateDiscrimination_clockChange
    {scale clockDuration lawRate referenceRate : ℝ} (hScale : scale ≠ 0) :
    poissonRateDiscrimination
        (contactIntensity (scale * clockDuration) (lawRate / scale))
        (contactIntensity (scale * clockDuration) (referenceRate / scale)) =
      poissonRateDiscrimination
        (contactIntensity clockDuration lawRate)
        (contactIntensity clockDuration referenceRate) := by
  rw [contactIntensity_clockChange hScale, contactIntensity_clockChange hScale]

/-- The activity objective is invariant under covariant rates with an unchanged covector. -/
theorem poissonActivityObjective_clockChange
    {scale clockDuration baseRate multiplier controlledRate : ℝ}
    (hScale : scale ≠ 0) :
    poissonActivityObjective
        (contactIntensity (scale * clockDuration) (baseRate / scale)) multiplier
        (contactIntensity (scale * clockDuration) (controlledRate / scale)) =
      poissonActivityObjective
        (contactIntensity clockDuration baseRate) multiplier
        (contactIntensity clockDuration controlledRate) := by
  rw [contactIntensity_clockChange hScale, contactIntensity_clockChange hScale]

/-- The operational action is invariant under covariant physical clock conversion. -/
theorem poissonOperationalAction_clockChange
    {scale clockDuration referenceRate controlledRate : ℝ} (hScale : scale ≠ 0) :
    poissonOperationalAction
        (contactIntensity (scale * clockDuration) (referenceRate / scale))
        (contactIntensity (scale * clockDuration) (controlledRate / scale)) =
      poissonOperationalAction
        (contactIntensity clockDuration referenceRate)
        (contactIntensity clockDuration controlledRate) := by
  rw [contactIntensity_clockChange hScale, contactIntensity_clockChange hScale]

end FiniteMarkovProcesses.InformationTheory
