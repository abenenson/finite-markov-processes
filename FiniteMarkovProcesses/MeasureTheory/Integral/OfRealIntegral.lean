/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive embeddings of real integrals

This module supplies inequalities relating Bochner integrals of real functions to
Lebesgue integrals after the positive embedding into `ENNReal`.

## Main results

* `MeasureTheory.ofReal_integral_le_lintegral_ofReal` bounds the positive embedding of an
  integrable real function's integral by the integral of its pointwise positive embedding.
-/

namespace MeasureTheory

open scoped ENNReal

/-- For an integrable real function, the positive embedding of its integral is bounded by the
integral of its pointwise positive embedding. -/
theorem ofReal_integral_le_lintegral_ofReal
    {Carrier : Type*} [MeasurableSpace Carrier]
    {measure : Measure Carrier} {integrand : Carrier → ℝ}
    (hIntegrable : Integrable integrand measure) :
    ENNReal.ofReal (∫ point, integrand point ∂measure) ≤
      ∫⁻ point, ENNReal.ofReal (integrand point) ∂measure := by
  have hPositiveIntegrable :
      Integrable (fun point => max (integrand point) 0) measure :=
    hIntegrable.pos_part
  have hIntegralLe :
      (∫ point, integrand point ∂measure) ≤
        ∫ point, max (integrand point) 0 ∂measure :=
    integral_mono_ae hIntegrable hPositiveIntegrable
      (Filter.Eventually.of_forall fun point => le_max_left _ _)
  calc
    ENNReal.ofReal (∫ point, integrand point ∂measure) ≤
        ENNReal.ofReal (∫ point, max (integrand point) 0 ∂measure) :=
      ENNReal.ofReal_le_ofReal hIntegralLe
    _ = ∫⁻ point, ENNReal.ofReal (max (integrand point) 0) ∂measure :=
      ofReal_integral_eq_lintegral_ofReal hPositiveIntegrable
        (Filter.Eventually.of_forall fun point => le_max_right _ _)
    _ = ∫⁻ point, ENNReal.ofReal (integrand point) ∂measure := by
      apply lintegral_congr
      intro point
      simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left, zero_le]

end MeasureTheory
