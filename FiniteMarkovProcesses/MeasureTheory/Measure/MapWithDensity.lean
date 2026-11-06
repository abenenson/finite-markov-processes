/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Pushforwards of pulled-back measure densities

This module records the elementary naturality identity for a density pulled back along a
measurable map. No injectivity or probability assumption is required.

## Main Result

- `Measure.map_withDensity_comp`: pushing forward a measure weighted by `g ∘ f` equals weighting
  the pushforward by `g`.
-/

open MeasureTheory
open scoped ENNReal

universe u v

namespace MeasureTheory.Measure

/-- A density pulled back along a measurable map commutes exactly with pushforward. -/
theorem map_withDensity_comp
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) =
      (Measure.map f μ).withDensity g := by
  ext measurableSet hMeasurableSet
  rw [Measure.map_apply hf hMeasurableSet]
  rw [withDensity_apply _ (hf hMeasurableSet)]
  rw [withDensity_apply _ hMeasurableSet]
  rw [← lintegral_indicator (hf hMeasurableSet),
    ← lintegral_indicator hMeasurableSet]
  rw [lintegral_map (hg.indicator hMeasurableSet) hf]
  rfl

end MeasureTheory.Measure
