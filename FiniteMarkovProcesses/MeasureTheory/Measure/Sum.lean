/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Measure.Sum

/-!
# Reindexing sums of measures

Identities for dependent, product, and injectively embedded sums of measures.

## Main results

- `measureSum_sigma`: split a dependent sigma-indexed measure sum.
- `measureSum_prod`: split a product-indexed measure sum.
- `measureSum_comp_le_of_injective`: an injectively indexed subfamily is dominated by the full
  measure sum.
- `measureSum_comp_eq_of_bijective`: a bijective reindexing preserves the complete measure sum.
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace MeasureTheory

/-- A measure sum over a dependent sigma index is the corresponding iterated measure sum. -/
theorem measureSum_sigma {Index : Type*} {Fibre : Index → Type*}
    {X : Type u} [MeasurableSpace X]
    (measure : (index : Index) → Fibre index → Measure X) :
    Measure.sum (fun code : (Σ index : Index, Fibre index) ↦
      measure code.1 code.2) =
      Measure.sum fun index ↦ Measure.sum fun fibre ↦ measure index fibre := by
  ext event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  simp_rw [Measure.sum_apply _ hEvent]
  exact ENNReal.tsum_sigma (fun index fibre ↦ measure index fibre event)

/-- A measure sum over a product index is the corresponding iterated measure sum. -/
theorem measureSum_prod {First Second : Type*} {X : Type u} [MeasurableSpace X]
    (measure : First → Second → Measure X) :
    Measure.sum (fun pair : First × Second ↦ measure pair.1 pair.2) =
      Measure.sum fun first ↦ Measure.sum fun second ↦ measure first second := by
  ext event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  simp_rw [Measure.sum_apply _ hEvent]
  exact ENNReal.tsum_prod'

/-- An injective subfamily of a measure family has sum bounded by the complete family sum. -/
theorem measureSum_comp_le_of_injective {Source Target : Type*} {X : Type u}
    [MeasurableSpace X] (embedding : Source → Target)
    (hEmbedding : Function.Injective embedding)
    (measure : Target → Measure X) :
    Measure.sum (measure ∘ embedding) ≤ Measure.sum measure := by
  rw [← Measure.sum_extend_zero hEmbedding (measure ∘ embedding)]
  apply Measure.le_iff.mpr
  intro event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  apply ENNReal.tsum_le_tsum
  intro target
  by_cases hTarget : ∃ source, embedding source = target
  · obtain ⟨source, rfl⟩ := hTarget
    simp [hEmbedding.extend_apply]
  · rw [Function.extend_apply' _ _ _ hTarget]
    simp

/-- Reindexing a complete measure family by a bijection preserves its measure sum. -/
theorem measureSum_comp_eq_of_bijective {Source Target : Type*} {X : Type u}
    [MeasurableSpace X] (reindex : Source → Target)
    (hReindex : Function.Bijective reindex)
    (measure : Target → Measure X) :
    Measure.sum (measure ∘ reindex) = Measure.sum measure := by
  ext event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  exact (Equiv.ofBijective reindex hReindex).tsum_eq
    (fun target ↦ measure target event)

end MeasureTheory
