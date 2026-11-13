/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Exponential

/-!
# Information identities for exponential waiting times

This file develops exact measure-theoretic identities for Mathlib's exponential probability
measure. The rate is always assumed positive, and extended Kullback--Leibler divergence remains
the canonical information quantity until finiteness has been established.

## Main results

- `integral_expMeasure_eq_integral_density`: integration against `expMeasure` through its density.
- `integrable_id_expMeasure`: integrability and exact first moment of the waiting time.
- `integral_sq_expMeasure`: exact second moment of the waiting time.
- `toReal_klDiv_expMeasure`: exact relative entropy between two positive-rate waiting laws.
- `expMeasure_injective`: identifiability of a positive exponential rate from its law.
- `klDiv_expMeasure_scale`: invariance under common positive rescaling of both rates.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory ProbabilityTheory Set
open _root_.InformationTheory
open scoped ENNReal

/-- Integration against a positive-rate exponential law is integration against its real density. -/
theorem integral_expMeasure_eq_integral_density (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂expMeasure r = ∫ x, exponentialPDFReal r x * f x := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [gammaPDF, exponentialPDFReal]
    simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _), smul_eq_mul]
  · exact (measurable_gammaPDFReal 1 r).ennreal_ofReal
  · exact ae_of_all _ fun x => by simp [gammaPDF]

/-- An exponential law is a strictly positive density over nonnegative Lebesgue time. -/
theorem expMeasure_eq_restrict_withDensity (r : ℝ) :
    expMeasure r =
      (volume.restrict (Ici 0)).withDensity
        (fun x => ENNReal.ofReal (r * Real.exp (-(r * x)))) := by
  change volume.withDensity (exponentialPDF r) =
    (volume.restrict (Ici 0)).withDensity
      (fun x => ENNReal.ofReal (r * Real.exp (-(r * x))))
  rw [← withDensity_indicator measurableSet_Ici]
  congr 1
  funext x
  by_cases hx : 0 ≤ x
  · simp [Set.indicator, hx, exponentialPDF_eq]
  · simp [Set.indicator, hx, exponentialPDF_eq]

/-- An exponential law assigns no mass to negative waiting times. -/
@[simp]
theorem expMeasure_Iio_zero (r : ℝ) : expMeasure r (Iio 0) = 0 := by
  rw [expMeasure_eq_restrict_withDensity]
  apply (withDensity_absolutelyContinuous _ _)
  rw [Measure.restrict_apply measurableSet_Iio]
  have hDisjoint : Iio (0 : ℝ) ∩ Ici 0 = ∅ := by
    ext x
    simp
  rw [hDisjoint, measure_empty]

/-- At a nonpositive rate, Mathlib's exponential measure degenerates to the zero measure. -/
theorem expMeasure_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    expMeasure r = 0 := by
  change volume.withDensity (exponentialPDF r) = 0
  have hPDF : exponentialPDF r = 0 := by
    funext x
    rw [exponentialPDF_eq]
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx]
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hr (Real.exp_pos _).le
    · rw [ite_eq_right hx]
      simp
  rw [hPDF, withDensity_zero]

/-- A nonpositive-rate exponential measure cannot be a probability measure. -/
theorem not_isProbabilityMeasure_expMeasure_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    ¬IsProbabilityMeasure (expMeasure r) := by
  intro hProbability
  have hUniv := hProbability.measure_univ
  rw [expMeasure_eq_zero_of_nonpos hr] at hUniv
  simp at hUniv

/-- Exponential waiting laws have no point masses. -/
theorem expMeasure_singleton (r x : ℝ) : expMeasure r {x} = 0 := by
  apply (show expMeasure r ≪ volume by
    exact withDensity_absolutelyContinuous _ _)
  simp

/-- The original exponential measure has zero singleton mass at every real rate. -/
noncomputable instance instNoAtomsExpMeasure (r : ℝ) : NullSingletonClass (expMeasure r) where
  measure_singleton := expMeasure_singleton r

/-- Every exponential law is absolutely continuous with respect to a positive-rate one. -/
theorem expMeasure_absolutelyContinuous_of_pos (r : ℝ) {s : ℝ} (hs : 0 < s) :
    expMeasure r ≪ expMeasure s := by
  rw [expMeasure_eq_restrict_withDensity r, expMeasure_eq_restrict_withDensity s]
  apply (withDensity_absolutelyContinuous _ _).trans
  apply withDensity_absolutelyContinuous'
  · exact ((measurable_const.mul
      (measurable_const.mul measurable_id).neg.exp).ennreal_ofReal).aemeasurable
  · exact ae_of_all _ fun x => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity

/-- Positive-rate exponential laws are mutually absolutely continuous. -/
theorem expMeasure_mutuallyAbsolutelyContinuous {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    expMeasure r ≪ expMeasure s ∧ expMeasure s ≪ expMeasure r :=
  ⟨expMeasure_absolutelyContinuous_of_pos r hs,
    expMeasure_absolutelyContinuous_of_pos s hr⟩

/-- The exact Radon--Nikodym derivative between positive-reference exponential laws. -/
theorem rnDeriv_expMeasure {r s : ℝ} (hs : 0 < s) :
    (expMeasure r).rnDeriv (expMeasure s) =ᵐ[expMeasure s]
      fun x => (ENNReal.ofReal (s * Real.exp (-(s * x))))⁻¹ *
        ENNReal.ofReal (r * Real.exp (-(r * x))) := by
  rw [expMeasure_eq_restrict_withDensity r, expMeasure_eq_restrict_withDensity s]
  let μ := volume.restrict (Ici (0 : ℝ))
  let fr : ℝ → ENNReal := fun x => ENNReal.ofReal (r * Real.exp (-(r * x)))
  let fs : ℝ → ENNReal := fun x => ENNReal.ofReal (s * Real.exp (-(s * x)))
  change (μ.withDensity fr).rnDeriv (μ.withDensity fs) =ᵐ[μ.withDensity fs]
    fun x => (fs x)⁻¹ * fr x
  have hfr : Measurable fr :=
    (measurable_const.mul (measurable_const.mul measurable_id).neg.exp).ennreal_ofReal
  have hfs : Measurable fs :=
    (measurable_const.mul (measurable_const.mul measurable_id).neg.exp).ennreal_ofReal
  have hfsZero : ∀ᵐ x ∂μ, fs x ≠ 0 := ae_of_all _ fun x => by
    simp only [fs, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hfsTop : ∀ᵐ x ∂μ, fs x ≠ ⊤ := ae_of_all _ fun x => by simp [fs]
  have hRight := Measure.rnDeriv_withDensity_right (μ.withDensity fr) μ
    hfs.aemeasurable hfsZero hfsTop
  have hLeft := Measure.rnDeriv_withDensity μ hfr
  filter_upwards [(withDensity_absolutelyContinuous μ fs).ae_le hRight,
    (withDensity_absolutelyContinuous μ fs).ae_le hLeft] with x hxRight hxLeft
  rw [hxRight, hxLeft]

/-- The log-likelihood ratio between exponential waiting laws is affine in the waiting time. -/
theorem llr_expMeasure {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    llr (expMeasure r) (expMeasure s) =ᵐ[expMeasure r]
      fun x => Real.log (r / s) + (s - r) * x := by
  have hRN := (expMeasure_absolutelyContinuous_of_pos r hs).ae_le
    (rnDeriv_expMeasure (r := r) hs)
  filter_upwards [hRN] with x hx
  rw [llr, hx]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ s * Real.exp (-(s * x))),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r * Real.exp (-(r * x)))]
  have hRatio :
      (s * Real.exp (-(s * x)))⁻¹ * (r * Real.exp (-(r * x))) =
        (r / s) * Real.exp ((s - r) * x) := by
    rw [show (s - r) * x = -(r * x) - (-(s * x)) by ring, Real.exp_sub]
    field_simp
  rw [hRatio, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]

private lemma weightedExponentialIntegrableOn (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => exponentialPDFReal r x * x) (Ioi 0) := by
  have hBase :
      IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hScaled :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ ((2 : ℝ) - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) 0 hr).mpr
    simpa using hBase
  refine hScaled.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [mem_Ioi] at hx
  norm_num
  simp [exponentialPDFReal, gammaPDFReal, hx.le]
  ring

private lemma weightedExponentialIntegrable (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => exponentialPDFReal r x * x) := by
  have hOn : IntegrableOn (fun x : ℝ => exponentialPDFReal r x * x) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ => exponentialPDFReal r x * x) (b := 0)).mpr
        (weightedExponentialIntegrableOn r hr)
  have hIndicator := hOn.integrable_indicator measurableSet_Ici
  apply hIndicator.congr
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]

private lemma squaredWeightedExponentialIntegrableOn (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => exponentialPDFReal r x * x ^ 2) (Ioi 0) := by
  have hBase :
      IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hScaled :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ ((3 : ℝ) - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1)) 0 hr).mpr
    simpa using hBase
  have hAdjusted :
      IntegrableOn
        (fun x : ℝ => (1 / r) * (Real.exp (-(r * x)) * (r * x) ^ ((3 : ℝ) - 1)))
        (Ioi 0) :=
    hScaled.const_mul (1 / r)
  refine hAdjusted.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [mem_Ioi] at hx
  norm_num
  simp [exponentialPDFReal, gammaPDFReal, hx.le]
  field_simp

private lemma squaredWeightedExponentialIntegrable (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => exponentialPDFReal r x * x ^ 2) := by
  have hOn : IntegrableOn (fun x : ℝ => exponentialPDFReal r x * x ^ 2) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ => exponentialPDFReal r x * x ^ 2) (b := 0)).mpr
        (squaredWeightedExponentialIntegrableOn r hr)
  have hIndicator := hOn.integrable_indicator measurableSet_Ici
  apply hIndicator.congr
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]

/-- The waiting-time coordinate is integrable under every positive-rate exponential law. -/
theorem integrable_id_expMeasure (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  change Integrable (fun x : ℝ => x) (volume.withDensity (exponentialPDF r))
  rw [integrable_withDensity_iff]
  · simpa only [exponentialPDF,
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr _), mul_comm] using
        weightedExponentialIntegrable r hr
  · exact (measurable_exponentialPDFReal r).ennreal_ofReal
  · exact ae_of_all _ fun x => by simp [exponentialPDF]

/-- A positive-rate exponential waiting time has mean `1 / r`. -/
theorem integral_id_expMeasure (r : ℝ) (hr : 0 < r) :
    ∫ x, x ∂expMeasure r = 1 / r := by
  rw [integral_expMeasure_eq_integral_density r hr]
  calc
    ∫ x, exponentialPDFReal r x * x =
        ∫ x in Ici 0, exponentialPDFReal r x * x := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]
      · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]
    _ = ∫ x in Ioi 0, exponentialPDFReal r x * x := integral_Ici_eq_integral_Ioi
    _ = ∫ x in Ioi 0, r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      norm_num
      simp only [mem_Ioi] at hx
      simp [exponentialPDFReal, gammaPDFReal, hx.le]
      ring
    _ = r * ((1 / r) ^ (2 : ℝ) * Real.Gamma 2) := by
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    _ = 1 / r := by
      rw [show Real.Gamma 2 = 1 by
        convert Real.Gamma_nat_eq_factorial 1 using 1
        all_goals norm_num]
      rw [mul_one, Real.rpow_two]
      field_simp

/-- The squared waiting-time coordinate is integrable under every positive-rate exponential law. -/
theorem integrable_sq_expMeasure (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => x ^ 2) (expMeasure r) := by
  change Integrable (fun x : ℝ => x ^ 2) (volume.withDensity (exponentialPDF r))
  rw [integrable_withDensity_iff]
  · simpa only [exponentialPDF,
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr _), mul_comm] using
        squaredWeightedExponentialIntegrable r hr
  · exact (measurable_exponentialPDFReal r).ennreal_ofReal
  · exact ae_of_all _ fun x => by simp [exponentialPDF]

/-- A positive-rate exponential waiting time has second moment `2 / r ^ 2`. -/
theorem integral_sq_expMeasure (r : ℝ) (hr : 0 < r) :
    ∫ x, x ^ 2 ∂expMeasure r = 2 / r ^ 2 := by
  rw [integral_expMeasure_eq_integral_density r hr]
  calc
    ∫ x, exponentialPDFReal r x * x ^ 2 =
        ∫ x in Ici 0, exponentialPDFReal r x * x ^ 2 := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]
      · simp [Set.indicator, hx, exponentialPDFReal, gammaPDFReal]
    _ = ∫ x in Ioi 0, exponentialPDFReal r x * x ^ 2 := integral_Ici_eq_integral_Ioi
    _ = ∫ x in Ioi 0, r * (x ^ ((3 : ℝ) - 1) * Real.exp (-(r * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      norm_num
      simp only [mem_Ioi] at hx
      simp [exponentialPDFReal, gammaPDFReal, hx.le]
      ring
    _ = r * ((1 / r) ^ (3 : ℝ) * Real.Gamma 3) := by
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    _ = 2 / r ^ 2 := by
      rw [show Real.Gamma 3 = 2 by
        convert Real.Gamma_nat_eq_factorial 2 using 1
        all_goals norm_num]
      norm_num [Real.rpow_natCast]
      field_simp

/-- The exponential-law log-likelihood ratio is integrable on every positive-rate pair. -/
theorem integrable_llr_expMeasure {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (llr (expMeasure r) (expMeasure s)) (expMeasure r) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [integrable_congr (llr_expMeasure hr hs)]
  exact (integrable_const _).add ((integrable_id_expMeasure r hr).const_mul (s - r))

/-- Relative entropy between positive-rate exponential laws is finite. -/
theorem klDiv_expMeasure_ne_top {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    klDiv (expMeasure r) (expMeasure s) ≠ ⊤ :=
  klDiv_ne_top_iff.mpr
    ⟨expMeasure_absolutelyContinuous_of_pos r hs, integrable_llr_expMeasure hr hs⟩

/-- Exact real-valued relative entropy between two positive-rate exponential waiting laws. -/
theorem toReal_klDiv_expMeasure {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (klDiv (expMeasure r) (expMeasure s)).toReal =
      Real.log (r / s) + s / r - 1 := by
  have := isProbabilityMeasure_expMeasure hr
  have := isProbabilityMeasure_expMeasure hs
  have hAC := expMeasure_absolutelyContinuous_of_pos r hs
  rw [toReal_klDiv hAC (integrable_llr_expMeasure hr hs)]
  simp only [probReal_univ]
  rw [integral_congr_ae (llr_expMeasure hr hs)]
  rw [integral_add (integrable_const _)
    ((integrable_id_expMeasure r hr).const_mul (s - r))]
  rw [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_id_expMeasure r hr]
  field_simp
  ring

/-- Exact extended relative entropy between two positive-rate exponential waiting laws. -/
theorem klDiv_expMeasure {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    klDiv (expMeasure r) (expMeasure s) =
      ENNReal.ofReal (Real.log (r / s) + s / r - 1) := by
  have hNonneg : 0 ≤ Real.log (r / s) + s / r - 1 := by
    rw [← toReal_klDiv_expMeasure hr hs]
    exact ENNReal.toReal_nonneg
  apply (ENNReal.toReal_eq_toReal_iff' (klDiv_expMeasure_ne_top hr hs) (by simp)).mp
  rw [ENNReal.toReal_ofReal hNonneg, toReal_klDiv_expMeasure hr hs]

/-- A positive exponential rate is identifiable from its probability law. -/
theorem expMeasure_injective {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hLaw : expMeasure r = expMeasure s) : r = s := by
  have hReciprocal : 1 / r = 1 / s := calc
    1 / r = ∫ x, x ∂expMeasure r := (integral_id_expMeasure r hr).symm
    _ = ∫ x, x ∂expMeasure s := by rw [hLaw]
    _ = 1 / s := integral_id_expMeasure s hs
  apply inv_injective
  simpa only [one_div] using hReciprocal

/-- Distinct positive exponential rates have strictly positive real-valued relative entropy. -/
theorem toReal_klDiv_expMeasure_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r ≠ s) : 0 < (klDiv (expMeasure r) (expMeasure s)).toReal := by
  apply ENNReal.toReal_pos
  · intro hZero
    have := isProbabilityMeasure_expMeasure hr
    have := isProbabilityMeasure_expMeasure hs
    exact hrs (expMeasure_injective hr hs (klDiv_eq_zero_iff.mp hZero))
  · exact klDiv_expMeasure_ne_top hr hs

/-- Common positive rescaling of both rates leaves relative entropy unchanged. -/
theorem klDiv_expMeasure_scale {a r s : ℝ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s) :
    klDiv (expMeasure (a * r)) (expMeasure (a * s)) =
      klDiv (expMeasure r) (expMeasure s) := by
  rw [klDiv_expMeasure (mul_pos ha hr) (mul_pos ha hs), klDiv_expMeasure hr hs]
  congr 1
  field_simp

end FiniteMarkovProcesses.InformationTheory
