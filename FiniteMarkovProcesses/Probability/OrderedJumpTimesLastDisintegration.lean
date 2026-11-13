/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume

/-!
# Last-coordinate disintegration of ordered jump-time integrals

This module gives the reusable Tonelli theorem behind last-event recursions.  An arbitrary
nonnegative measurable integrand on the `(n+1)`-event ordered simplex is integrated by first
choosing its last event time and then integrating the preceding `n` ordered times.

## Main results

- `orderedJumpTimesLastJoin`.
- `lintegral_orderedJumpTimes_succ`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal

/-- Join a final event time to its preceding finite time vector. -/
noncomputable def orderedJumpTimesLastJoin (eventCount : ℕ) :
    ℝ × (Fin eventCount → ℝ) ≃ᵐ (Fin (eventCount + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (eventCount + 1) ↦ ℝ) (Fin.last eventCount)).symm

/-- The joined time vector has the supplied final coordinate. -/
@[simp]
theorem orderedJumpTimesLastJoin_last
    (eventCount : ℕ) (lastTime : ℝ) (earlierTimes : Fin eventCount → ℝ) :
    orderedJumpTimesLastJoin eventCount (lastTime, earlierTimes)
        (Fin.last eventCount) =
      lastTime := by
  unfold orderedJumpTimesLastJoin
  simp

/-- Removing the final coordinate of the joined time vector recovers the supplied preceding
vector. -/
@[simp]
theorem orderedJumpTimesLastJoin_init
    (eventCount : ℕ) (lastTime : ℝ) (earlierTimes : Fin eventCount → ℝ) :
    Fin.init (orderedJumpTimesLastJoin eventCount (lastTime, earlierTimes)) =
      earlierTimes := by
  unfold orderedJumpTimesLastJoin
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv_last]
  exact @Fin.init_snoc eventCount (fun _ : Fin (eventCount + 1) ↦ ℝ)
    lastTime earlierTimes

/-- Tonelli disintegration of an arbitrary nonnegative measurable integrand over the ordered
`(n+1)`-event simplex. -/
theorem lintegral_orderedJumpTimes_succ
    (eventCount : ℕ)
    {integrand : (Fin (eventCount + 1) → ℝ) → ℝ≥0∞}
    (hIntegrand : Measurable integrand) (duration : ℝ) :
    ∫⁻ times : Fin (eventCount + 1) → ℝ in
        orderedJumpTimes (eventCount + 1) duration,
      integrand times =
    ∫⁻ lastTime : ℝ in Ioo 0 duration,
      ∫⁻ earlierTimes : Fin eventCount → ℝ in
          orderedJumpTimes eventCount lastTime,
        integrand (orderedJumpTimesLastJoin eventCount (lastTime, earlierTimes)) := by
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (eventCount + 1) ↦ ℝ) (Fin.last eventCount)
  let lastSection := orderedJumpTimesLastSection eventCount duration
  have hPreserving := volume_preserving_piFinSuccAbove
    (fun _ : Fin (eventCount + 1) ↦ ℝ) (Fin.last eventCount)
  have hSection : MeasurableSet lastSection :=
    measurableSet_orderedJumpTimesLastSection eventCount duration
  have hMap :
      Measure.map split (volume.restrict
          (orderedJumpTimes (eventCount + 1) duration)) =
        volume.restrict lastSection := by
    calc
      Measure.map split (volume.restrict
          (orderedJumpTimes (eventCount + 1) duration)) =
          Measure.map split (volume.restrict (split ⁻¹' lastSection)) := by
        rw [show split ⁻¹' lastSection =
            orderedJumpTimes (eventCount + 1) duration by
          exact piFinSuccAbove_preimage_orderedJumpTimesLastSection
            eventCount duration]
      _ = (Measure.map split volume).restrict lastSection := by
        rw [Measure.restrict_map hPreserving.measurable hSection]
      _ = volume.restrict lastSection := by
        rw [hPreserving.map_eq]
  let pairIntegrand : ℝ × (Fin eventCount → ℝ) → ℝ≥0∞ :=
    fun coordinates ↦ integrand (split.symm coordinates)
  have hPairIntegrand : Measurable pairIntegrand :=
    hIntegrand.comp split.symm.measurable
  calc
    (∫⁻ times : Fin (eventCount + 1) → ℝ in
        orderedJumpTimes (eventCount + 1) duration,
      integrand times) =
        ∫⁻ coordinates, pairIntegrand coordinates ∂Measure.map split
          (volume.restrict (orderedJumpTimes (eventCount + 1) duration)) := by
      rw [MeasureTheory.lintegral_map_equiv]
      apply lintegral_congr
      intro times
      simp only [pairIntegrand, MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ coordinates in lastSection, pairIntegrand coordinates := by
      rw [hMap]
    _ = _ := by
      rw [← lintegral_indicator hSection]
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod _ ((hPairIntegrand.indicator hSection).aemeasurable)]
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro lastTime
      have hFiber :
          (fun earlierTimes ↦
            lastSection.indicator pairIntegrand (lastTime, earlierTimes)) =
          if lastTime ∈ Ioo (0 : ℝ) duration then
            fun earlierTimes ↦
              (orderedJumpTimes eventCount lastTime).indicator
                (fun earlierTimes ↦ pairIntegrand (lastTime, earlierTimes)) earlierTimes
          else fun _ ↦ 0 := by
        funext earlierTimes
        by_cases hLast : lastTime ∈ Ioo (0 : ℝ) duration
        · by_cases hEarlier : earlierTimes ∈ orderedJumpTimes eventCount lastTime
          · have hMem : (lastTime, earlierTimes) ∈ lastSection :=
              ⟨hLast, hEarlier⟩
            rw [Set.indicator_of_mem hMem, ite_eq_left hLast,
              Set.indicator_of_mem hEarlier]
          · have hNotMem : (lastTime, earlierTimes) ∉ lastSection := by
              intro hMem
              exact hEarlier hMem.2
            rw [Set.indicator_of_notMem hNotMem, ite_eq_left hLast,
              Set.indicator_of_notMem hEarlier]
        · have hNotMem : (lastTime, earlierTimes) ∉ lastSection := by
            intro hMem
            exact hLast hMem.1
          rw [Set.indicator_of_notMem hNotMem, ite_eq_right hLast]
      rw [hFiber]
      by_cases hLast : lastTime ∈ Ioo (0 : ℝ) duration
      · rw [ite_eq_left hLast, Set.indicator_of_mem hLast]
        rw [lintegral_indicator
          (measurableSet_orderedJumpTimes eventCount lastTime)]
        apply lintegral_congr
        intro earlierTimes
        rfl
      · rw [ite_eq_right hLast, Set.indicator_of_notMem hLast]
        simp

end FiniteMarkovProcesses.Probability
