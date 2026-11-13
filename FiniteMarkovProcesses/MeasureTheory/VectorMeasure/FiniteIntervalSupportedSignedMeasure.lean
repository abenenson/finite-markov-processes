/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureTopology

/-!
# Signed measures supported on a finite open interval

This module provides extensionality principles for finite signed measures on the real line.
General measures are determined by all nondegenerate half-open intervals.  Measures supported on
one finite open interval are determined by the half-open intervals lying inside that physical
interval.

## Main results

* `signedMeasure_eq_of_apply_Ioc_eq` gives unrestricted half-open-interval extensionality.
* `signedMeasure_eq_of_apply_Ioc_eq_of_restrict_openInterval` localizes the required comparisons
  to measures supported on one finite open interval.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set

noncomputable section

/-- Finite signed Borel measures on the real line are determined by their values on all
nondegenerate half-open intervals. -/
theorem signedMeasure_eq_of_apply_Ioc_eq
    (first second : SignedMeasure ℝ)
    (hInterval : ∀ {start finish : ℝ}, start < finish →
      first (Ioc start finish) = second (Ioc start finish)) :
    first = second := by
  let firstJordan := first.toJordanDecomposition
  let secondJordan := second.toJordanDecomposition
  have hBalance :
      firstJordan.posPart + secondJordan.negPart =
        secondJordan.posPart + firstJordan.negPart := by
    apply Measure.ext_of_Ioc
    intro start finish hOrder
    rw [← measureReal_eq_measureReal_iff,
      measureReal_add_apply, measureReal_add_apply]
    have hSignedInterval :
        firstJordan.toSignedMeasure (Ioc start finish) =
          secondJordan.toSignedMeasure (Ioc start finish) := by
      simpa only [firstJordan, secondJordan,
        SignedMeasure.toSignedMeasure_toJordanDecomposition] using
          hInterval hOrder
    rw [JordanDecomposition.toSignedMeasure,
      JordanDecomposition.toSignedMeasure,
      Measure.toSignedMeasure_sub_apply measurableSet_Ioc,
      Measure.toSignedMeasure_sub_apply measurableSet_Ioc] at hSignedInterval
    exact sub_eq_sub_iff_add_eq_add.mp hSignedInterval
  calc
    first = firstJordan.toSignedMeasure := by
      simp only [firstJordan,
        SignedMeasure.toSignedMeasure_toJordanDecomposition]
    _ = secondJordan.toSignedMeasure := by
      unfold JordanDecomposition.toSignedMeasure
      apply sub_eq_sub_iff_add_eq_add.mpr
      rw [← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
      exact Measure.toSignedMeasure_congr hBalance
    _ = second := by
      simp only [secondJordan,
        SignedMeasure.toSignedMeasure_toJordanDecomposition]

/-- Signed measures supported on `(0, duration)` are determined by half-open intervals whose
endpoints lie inside the corresponding physical half-open interval. -/
theorem signedMeasure_eq_of_apply_Ioc_eq_of_restrict_openInterval
    {duration : ℝ} (first second : SignedMeasure ℝ)
    (hFirstSupport : first.restrict (Ioo 0 duration) = first)
    (hSecondSupport : second.restrict (Ioo 0 duration) = second)
    (hInterval : ∀ {start finish : ℝ}, 0 ≤ start → start ≤ finish → finish < duration →
      first (Ioc start finish) = second (Ioc start finish)) :
    first = second := by
  let exhaustion : ℕ → Set ℝ :=
    fun index => Ioc 0 (duration - 1 / ((index : ℝ) + 1))
  have hExhaustionMeasurable :
      ∀ index, MeasurableSet (exhaustion index) :=
    fun _ => measurableSet_Ioc
  have hExhaustionUnion :
      (⋃ index, exhaustion index) = Ioo 0 duration := by
    ext time
    constructor
    · intro hTime
      obtain ⟨index, hIndex⟩ := mem_iUnion.mp hTime
      change time ∈ Ioc 0 (duration - 1 / ((index : ℝ) + 1)) at hIndex
      refine ⟨hIndex.1, lt_of_le_of_lt hIndex.2 ?_⟩
      exact sub_lt_self duration (by positivity)
    · intro hTime
      have hEventuallySmall :
          ∀ᶠ index : ℕ in atTop,
            1 / ((index : ℝ) + 1) < duration - time :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (Iio_mem_nhds (sub_pos.mpr hTime.2))
      obtain ⟨index, hIndex⟩ := hEventuallySmall.exists
      refine mem_iUnion.mpr ⟨index, ?_⟩
      exact ⟨hTime.1, by linarith⟩
  have hRestricted :
      ∀ index, first.restrict (exhaustion index) =
        second.restrict (exhaustion index) := by
    intro index
    apply signedMeasure_eq_of_apply_Ioc_eq
    intro start finish hOrder
    rw [VectorMeasure.restrict_apply _ (hExhaustionMeasurable index)
        measurableSet_Ioc,
      VectorMeasure.restrict_apply _ (hExhaustionMeasurable index)
        measurableSet_Ioc]
    have hIntersection :
        Ioc start finish ∩ exhaustion index =
          Ioc (max start 0)
            (min finish (duration - 1 / ((index : ℝ) + 1))) := by
      ext time
      simp only [exhaustion, mem_inter_iff, mem_Ioc,
        max_lt_iff, le_min_iff]
      aesop
    rw [hIntersection]
    by_cases hClippedOrder :
        max start 0 < min finish (duration - 1 / ((index : ℝ) + 1))
    · exact hInterval (le_max_right _ _) hClippedOrder.le
        ((min_le_right _ _).trans_lt (sub_lt_self duration (by positivity)))
    · rw [Ioc_eq_empty hClippedOrder, first.empty, second.empty]
  have hRestrictionEquality :
      first.restrict (Ioo 0 duration) = second.restrict (Ioo 0 duration) := by
    rw [← hExhaustionUnion]
    apply le_antisymm
    · exact VectorMeasure.restrict_le_restrict_iUnion
        first second hExhaustionMeasurable
        (fun index => (hRestricted index).le)
    · exact VectorMeasure.restrict_le_restrict_iUnion
        second first hExhaustionMeasurable
        (fun index => (hRestricted index).ge)
  exact hFirstSupport.symm.trans (hRestrictionEquality.trans hSecondSupport)

end

end FiniteMarkovProcesses
