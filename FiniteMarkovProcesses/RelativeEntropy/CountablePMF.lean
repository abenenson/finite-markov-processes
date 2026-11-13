/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Relative entropy of countable probability mass functions

This file identifies the Radon--Nikodym derivative and log-likelihood ratio of two probability
mass functions when the reference mass is everywhere positive. The results provide a reusable
bridge from countable probability calculations to Mathlib's measure-level KL divergence.

## Main results

- `pmfToMeasure_eq_withDensity_div`: density representation by pointwise mass ratios.
- `rnDeriv_pmfToMeasure`: Radon--Nikodym derivative of countable PMF measures.
- `llr_pmfToMeasure`: log-likelihood ratio of countable PMF measures.
- `toReal_klDiv_pmfToMeasure`: integral representation of their KL divergence.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open _root_.InformationTheory

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- A countable PMF is its positive reference PMF weighted by the pointwise mass ratio. -/
theorem pmfToMeasure_eq_withDensity_div (p q : PMF α) (hq : ∀ x, q x ≠ 0) :
    p.toMeasure = q.toMeasure.withDensity fun x ↦ p x / q x := by
  symm
  apply Measure.ext_of_singleton
  intro x
  rw [withDensity_apply _ (MeasurableSet.singleton x), lintegral_singleton,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact ENNReal.div_mul_cancel (hq x) (q.apply_ne_top x)

/-- A countable PMF is absolutely continuous with respect to an everywhere-positive PMF. -/
theorem pmfToMeasure_absolutelyContinuous (p q : PMF α) (hq : ∀ x, q x ≠ 0) :
    p.toMeasure ≪ q.toMeasure := by
  rw [pmfToMeasure_eq_withDensity_div p q hq]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon--Nikodym derivative of countable PMF measures is their pointwise mass ratio. -/
theorem rnDeriv_pmfToMeasure (p q : PMF α) (hq : ∀ x, q x ≠ 0) :
    p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] fun x ↦ p x / q x := by
  rw [pmfToMeasure_eq_withDensity_div p q hq]
  exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)

/-- The log-likelihood ratio of countable PMF measures is the logarithm of their mass ratio. -/
theorem llr_pmfToMeasure (p q : PMF α) (hq : ∀ x, q x ≠ 0) :
    llr p.toMeasure q.toMeasure =ᵐ[p.toMeasure]
      fun x ↦ Real.log ((p x / q x).toReal) := by
  have hAc := pmfToMeasure_absolutelyContinuous p q hq
  filter_upwards [hAc.ae_le (rnDeriv_pmfToMeasure p q hq)] with x hx
  change Real.log (p.toMeasure.rnDeriv q.toMeasure x).toReal = _
  rw [hx]

/-- The real KL divergence of countable PMFs is the expected logarithmic mass ratio. -/
theorem toReal_klDiv_pmfToMeasure (p q : PMF α) (hq : ∀ x, q x ≠ 0) :
    (klDiv p.toMeasure q.toMeasure).toReal =
      ∫ x, Real.log ((p x / q x).toReal) ∂p.toMeasure := by
  have hAc := pmfToMeasure_absolutelyContinuous p q hq
  rw [toReal_klDiv_of_measure_eq hAc (by simp)]
  exact integral_congr_ae (llr_pmfToMeasure p q hq)

end FiniteMarkovProcesses.InformationTheory
