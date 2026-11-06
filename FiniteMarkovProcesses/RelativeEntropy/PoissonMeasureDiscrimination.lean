/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.CountablePMF
import FiniteMarkovProcesses.RelativeEntropy.PoissonRateDiscrimination
import FiniteMarkovProcesses.Probability.PoissonContactHistory
import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Relative entropy and mean of Poisson count laws

This file connects the scalar Poisson discrimination formula to Mathlib's actual Poisson count
measure. It proves the first moment, the pointwise likelihood ratio, its integrability, and the
closed form of the measure-level KL divergence. The final results transport the first moment to
the complete Poisson-contact history law through its exact count marginal.

## Main results

- `integral_poissonCount`: the expected Poisson count is its intensity.
- `poissonLogLikelihoodRatio`: the count-law log-likelihood ratio is affine in the count.
- `toReal_klDiv_poissonMeasure`: the exact Poisson--Poisson KL formula.
- `toReal_klDiv_poissonMeasure_eq_rateDiscrimination`: equality with the scalar classifier.
- `integral_poissonContactHistory_contactCount`: expected count on the complete history law.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory ProbabilityTheory
open _root_.InformationTheory
open scoped ENNReal NNReal

open FiniteMarkovProcesses.Probability

export FiniteMarkovProcesses.Probability
  (succ_mul_poissonPMFReal hasSum_count_mul_poissonPMFReal integrable_poissonCount
    integral_poissonCount)

/-- Every count has nonzero mass under a positive-intensity Poisson law. -/
theorem poissonPMF_ne_zero {intensity : ℝ≥0} (hIntensity : 0 < intensity) (count : ℕ) :
    poissonCountPMF intensity count ≠ 0 := by
  change ENNReal.ofReal (poissonCountMassReal intensity count) ≠ 0
  rw [ne_eq, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (poissonCountMassReal_pos hIntensity)

/-- The ratio of two real Poisson masses cancels to an exponential times a rate ratio power. -/
theorem poissonPMFReal_div {lawIntensity referenceIntensity : ℝ≥0}
    (hReference : 0 < referenceIntensity) (count : ℕ) :
    poissonCountMassReal lawIntensity count / poissonCountMassReal referenceIntensity count =
      Real.exp ((referenceIntensity : ℝ) - (lawIntensity : ℝ)) *
        ((lawIntensity : ℝ) / (referenceIntensity : ℝ)) ^ count := by
  rw [poissonCountMassReal, poissonCountMassReal, div_pow]
  have hExp : Real.exp (-(referenceIntensity : ℝ)) ≠ 0 := Real.exp_ne_zero _
  have hPower : (referenceIntensity : ℝ) ^ count ≠ 0 :=
    pow_ne_zero _ (mod_cast hReference.ne')
  field_simp
  rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]
  field_simp

/-- The pointwise Poisson log-likelihood ratio is affine in the realized count. -/
theorem poissonLogLikelihoodRatio {lawIntensity referenceIntensity : ℝ≥0}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) (count : ℕ) :
    Real.log
        ((poissonCountPMF lawIntensity count / poissonCountPMF referenceIntensity count).toReal) =
      (referenceIntensity : ℝ) - (lawIntensity : ℝ) +
        (count : ℝ) * Real.log ((lawIntensity : ℝ) / (referenceIntensity : ℝ)) := by
  rw [ENNReal.toReal_div]
  change Real.log
    ((ENNReal.ofReal (poissonCountMassReal lawIntensity count)).toReal /
      (ENNReal.ofReal (poissonCountMassReal referenceIntensity count)).toReal) = _
  rw [ENNReal.toReal_ofReal poissonCountMassReal_nonneg,
    ENNReal.toReal_ofReal poissonCountMassReal_nonneg, poissonPMFReal_div hReference]
  rw [Real.log_mul (Real.exp_ne_zero _)
    (pow_ne_zero _ (div_ne_zero (mod_cast hLaw.ne') (mod_cast hReference.ne'))),
    Real.log_exp, Real.log_pow]

/-- The Poisson log-likelihood ratio is integrable under the law measure. -/
theorem integrable_poissonLogLikelihoodRatio {lawIntensity referenceIntensity : ℝ≥0}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) :
    Integrable
      (fun count : ℕ ↦
        Real.log
          ((poissonCountPMF lawIntensity count /
            poissonCountPMF referenceIntensity count).toReal))
      (poissonMeasure lawIntensity) := by
  have hFunction :
      (fun count : ℕ ↦
        Real.log
          ((poissonCountPMF lawIntensity count /
            poissonCountPMF referenceIntensity count).toReal)) =
        fun count : ℕ ↦ (referenceIntensity : ℝ) - (lawIntensity : ℝ) +
          (count : ℝ) * Real.log ((lawIntensity : ℝ) / (referenceIntensity : ℝ)) := by
    funext count
    exact poissonLogLikelihoodRatio hLaw hReference count
  rw [hFunction]
  exact (integrable_const _).add ((integrable_poissonCount lawIntensity).mul_const _)

/-- The KL divergence between positive Poisson count laws has its standard closed form. -/
theorem toReal_klDiv_poissonMeasure {lawIntensity referenceIntensity : ℝ≥0}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) :
    (klDiv (poissonMeasure lawIntensity) (poissonMeasure referenceIntensity)).toReal =
      (lawIntensity : ℝ) * Real.log ((lawIntensity : ℝ) / (referenceIntensity : ℝ)) -
        (lawIntensity : ℝ) + (referenceIntensity : ℝ) := by
  simp_rw [poissonMeasure_eq_poissonCountPMF_toMeasure]
  rw [toReal_klDiv_pmfToMeasure _ _ (poissonPMF_ne_zero hReference)]
  have hFunction :
      (fun count : ℕ ↦
        Real.log
          ((poissonCountPMF lawIntensity count /
            poissonCountPMF referenceIntensity count).toReal)) =
        fun count : ℕ ↦ (referenceIntensity : ℝ) - (lawIntensity : ℝ) +
          (count : ℝ) * Real.log ((lawIntensity : ℝ) / (referenceIntensity : ℝ)) := by
    funext count
    exact poissonLogLikelihoodRatio hLaw hReference count
  rw [hFunction]
  rw [← poissonMeasure_eq_poissonCountPMF_toMeasure lawIntensity]
  rw [integral_add (integrable_const _)
    ((integrable_poissonCount lawIntensity).mul_const _), integral_const,
    integral_mul_const, integral_poissonCount]
  simp
  ring

/-- Measure-level Poisson KL is exactly the reusable scalar rate discrimination. -/
theorem toReal_klDiv_poissonMeasure_eq_rateDiscrimination
    {lawIntensity referenceIntensity : ℝ≥0}
    (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) :
    (klDiv (poissonMeasure lawIntensity) (poissonMeasure referenceIntensity)).toReal =
      poissonRateDiscrimination (lawIntensity : ℝ) (referenceIntensity : ℝ) := by
  rw [toReal_klDiv_poissonMeasure hLaw hReference]
  rfl

/-- The registered contact count is integrable on the complete Poisson-contact history law. -/
theorem integrable_poissonContactHistory_contactCount (intensity : ℝ≥0) :
    Integrable
      (fun history : PoissonContactHistory ↦ (history.contactCount : ℝ))
      (poissonContactHistoryMeasure intensity) := by
  have hMapped : Integrable (fun count : ℕ ↦ (count : ℝ))
      (Measure.map PoissonContactHistory.contactCount
        (poissonContactHistoryMeasure intensity)) := by
    rw [poissonContactHistoryMeasure_countMarginal]
    exact integrable_poissonCount intensity
  simpa [Function.comp_def] using
    hMapped.comp_aemeasurable
      measurable_contactCount.aemeasurable

/-- Expected registered contacts on the complete history law equal the integrated intensity. -/
theorem integral_poissonContactHistory_contactCount (intensity : ℝ≥0) :
    ∫ history : PoissonContactHistory, (history.contactCount : ℝ)
        ∂poissonContactHistoryMeasure intensity =
      (intensity : ℝ) := by
  calc
    _ = ∫ count : ℕ, (count : ℝ)
        ∂Measure.map PoissonContactHistory.contactCount
          (poissonContactHistoryMeasure intensity) := by
      symm
      exact integral_map measurable_contactCount.aemeasurable
        (measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).aestronglyMeasurable
    _ = ∫ count : ℕ, (count : ℝ) ∂poissonMeasure intensity := by
      rw [poissonContactHistoryMeasure_countMarginal]
    _ = (intensity : ℝ) := integral_poissonCount intensity

end FiniteMarkovProcesses.InformationTheory
