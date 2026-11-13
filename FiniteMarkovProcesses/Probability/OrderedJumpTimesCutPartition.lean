/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowObservation
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesCutDisintegration

/-!
# Partition of ordered event times at a physical cut

The cut sector with `earlierCount` coordinates below a cut and `laterCount` coordinates above it
is exactly the corresponding observed-event-count fibre inside the complete ordered simplex,
away from the coordinate hyperplanes at the cut.  Those hyperplanes are kept explicit here; a
later measure theorem may discard them only after proving they are null.

## Main results

- `orderedJumpTimesCutBoundary`: the finite union of coordinate hyperplanes at the cut.
- `volume_orderedJumpTimesCutBoundary`: that boundary has zero Lebesgue volume.
- `orderedTimesInInterval_eq_iUnion_observedCountSector`: exact finite partition by observed
  event count, including the boundary convention.
- `lintegral_orderedTimesInInterval_eq_sum_observedCountSector`: integral decomposition over
  that finite partition.
- `volume_restrict_orderedTimesInIntervalObservedCountSector_eq_cutSector`: replacement of one
  observed-count fibre by the strict cut sector after the proved null-boundary removal.
- `orderedJumpTimesCutSector_subset_orderedTimesInInterval`.
- `mem_orderedJumpTimesCutSector_iff`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Set
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Time vectors with at least one coordinate exactly at the physical cut. -/
def orderedJumpTimesCutBoundary (eventCount : ℕ) (cut : ℝ) :
    Set (Fin eventCount → ℝ) :=
  ⋃ index : Fin eventCount, Function.eval index ⁻¹' {cut}

/-- The finite coordinate boundary at a physical cut is measurable. -/
theorem measurableSet_orderedJumpTimesCutBoundary (eventCount : ℕ) (cut : ℝ) :
    MeasurableSet (orderedJumpTimesCutBoundary eventCount cut) := by
  unfold orderedJumpTimesCutBoundary
  apply MeasurableSet.iUnion
  intro index
  exact (measurableSet_singleton cut).preimage (measurable_pi_apply index)

/-- A finite time vector lies outside the cut boundary exactly when no coordinate equals the
cut. -/
theorem not_mem_orderedJumpTimesCutBoundary_iff
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (cut : ℝ) :
    times ∉ orderedJumpTimesCutBoundary eventCount cut ↔
      ∀ index, times index ≠ cut := by
  simp [orderedJumpTimesCutBoundary]

/-- The finite union of coordinate hyperplanes at a physical cut has zero Lebesgue volume. -/
theorem volume_orderedJumpTimesCutBoundary (eventCount : ℕ) (cut : ℝ) :
    volume (orderedJumpTimesCutBoundary eventCount cut) = 0 := by
  unfold orderedJumpTimesCutBoundary
  apply measure_iUnion_null
  intro index
  rw [volume_pi]
  apply Measure.pi_eval_preimage_null
  exact measure_singleton cut

/-- One exact observed-event-count fibre inside a complete ordered time interval.  Events exactly
at the cut follow the càdlàg at-or-before convention and are included in the observed count. -/
def orderedTimesInIntervalObservedCountSector
    (eventCount : ℕ) (lower cut upper : ℝ) (observedCount : ℕ) :
    Set (Fin eventCount → ℝ) :=
  orderedTimesInInterval eventCount lower upper ∩
    {times |
      FiniteJumpHistory.eventCountAtOrBeforeTimeVector times cut = observedCount}

/-- Every exact observed-count sector is measurable. -/
theorem measurableSet_orderedTimesInIntervalObservedCountSector
    (eventCount : ℕ) (lower cut upper : ℝ) (observedCount : ℕ) :
    MeasurableSet (orderedTimesInIntervalObservedCountSector
      eventCount lower cut upper observedCount) := by
  exact (measurableSet_orderedTimesInInterval eventCount lower upper).inter
    (FiniteJumpHistory.measurable_eventCountAtOrBeforeTimeVector cut
      (measurableSet_singleton observedCount))

/-- The complete ordered interval is the union of its `eventCount + 1` possible observed-count
fibres. -/
theorem orderedTimesInInterval_eq_iUnion_observedCountSector
    (eventCount : ℕ) (lower cut upper : ℝ) :
    orderedTimesInInterval eventCount lower upper =
      ⋃ observedCount : Fin (eventCount + 1),
        orderedTimesInIntervalObservedCountSector
          eventCount lower cut upper observedCount := by
  ext times
  constructor
  · intro hOrdered
    let observedCount : Fin (eventCount + 1) :=
      ⟨FiniteJumpHistory.eventCountAtOrBeforeTimeVector times cut,
        Nat.lt_succ_of_le
          (FiniteJumpHistory.eventCountAtOrBeforeTimeVector_le times cut)⟩
    exact Set.mem_iUnion.2 ⟨observedCount, hOrdered, rfl⟩
  · intro hUnion
    rcases Set.mem_iUnion.1 hUnion with ⟨observedCount, hSector⟩
    exact hSector.1

/-- Distinct observed-count fibres are disjoint. -/
theorem pairwise_disjoint_orderedTimesInIntervalObservedCountSector
    (eventCount : ℕ) (lower cut upper : ℝ) :
    Pairwise (Function.onFun Disjoint fun observedCount : Fin (eventCount + 1) ↦
      orderedTimesInIntervalObservedCountSector
        eventCount lower cut upper observedCount) := by
  intro first second hNe
  change Disjoint
    (orderedTimesInIntervalObservedCountSector
      eventCount lower cut upper first)
    (orderedTimesInIntervalObservedCountSector
      eventCount lower cut upper second)
  rw [Set.disjoint_left]
  intro times hFirst hSecond
  have hValue : first.val = second.val := hFirst.2.symm.trans hSecond.2
  exact hNe (Fin.ext hValue)

/-- Every nonnegative integrand over the complete ordered interval decomposes exactly over the
finite observed-count partition. -/
theorem lintegral_orderedTimesInInterval_eq_sum_observedCountSector
    (eventCount : ℕ) (lower cut upper : ℝ)
    (integrand : (Fin eventCount → ℝ) → ℝ≥0∞) :
    (∫⁻ times in orderedTimesInInterval eventCount lower upper,
      integrand times) =
      ∑ observedCount : Fin (eventCount + 1),
        ∫⁻ times in orderedTimesInIntervalObservedCountSector
            eventCount lower cut upper observedCount,
          integrand times := by
  rw [orderedTimesInInterval_eq_iUnion_observedCountSector]
  rw [Measure.restrict_iUnion
    (pairwise_disjoint_orderedTimesInIntervalObservedCountSector
      eventCount lower cut upper)
    (fun observedCount ↦
      measurableSet_orderedTimesInIntervalObservedCountSector
        eventCount lower cut upper observedCount)]
  rw [lintegral_sum_measure]
  rw [tsum_fintype]

/-- A cut sector is contained in the complete ordered interval whenever the cut lies between the
outer endpoints. -/
theorem orderedJumpTimesCutSector_subset_orderedTimesInInterval
    (earlierCount laterCount : ℕ) (lower cut upper : ℝ)
    (hLowerCut : lower ≤ cut) (hCutUpper : cut ≤ upper) :
    orderedJumpTimesCutSector earlierCount laterCount lower cut upper ⊆
      orderedTimesInInterval (earlierCount + laterCount) lower upper := by
  intro times hSector
  change orderedJumpTimesCutSplit earlierCount laterCount times ∈
    orderedTimesInInterval earlierCount lower cut ×ˢ
      orderedTimesInInterval laterCount cut upper at hSector
  rcases hSector with ⟨hEarlier, hLater⟩
  constructor
  · intro index
    by_cases hIndex : index.val < earlierCount
    · let earlierIndex : Fin earlierCount := ⟨index.val, hIndex⟩
      have hIndexEq : index = Fin.castAdd laterCount earlierIndex := Fin.ext rfl
      rw [hIndexEq, ← orderedJumpTimesCutSplit_fst_apply
        earlierCount laterCount times earlierIndex]
      exact ⟨(hEarlier.1 earlierIndex).1,
        (hEarlier.1 earlierIndex).2.trans_le hCutUpper⟩
    · have hLaterValue : index.val - earlierCount < laterCount := by
        omega
      let laterIndex : Fin laterCount :=
        ⟨index.val - earlierCount, hLaterValue⟩
      have hIndexEq : index = Fin.natAdd earlierCount laterIndex := by
        apply Fin.ext
        simp [laterIndex]
        omega
      rw [hIndexEq, ← orderedJumpTimesCutSplit_snd_apply
        earlierCount laterCount times laterIndex]
      exact ⟨hLowerCut.trans_lt (hLater.1 laterIndex).1,
        (hLater.1 laterIndex).2⟩
  · intro first second hFirstSecond
    by_cases hFirst : first.val < earlierCount
    · let earlierFirst : Fin earlierCount := ⟨first.val, hFirst⟩
      have hFirstEq : first = Fin.castAdd laterCount earlierFirst := Fin.ext rfl
      by_cases hSecond : second.val < earlierCount
      · let earlierSecond : Fin earlierCount := ⟨second.val, hSecond⟩
        have hSecondEq : second = Fin.castAdd laterCount earlierSecond := Fin.ext rfl
        rw [hFirstEq, hSecondEq,
          ← orderedJumpTimesCutSplit_fst_apply
            earlierCount laterCount times earlierFirst,
          ← orderedJumpTimesCutSplit_fst_apply
            earlierCount laterCount times earlierSecond]
        exact hEarlier.2 (by omega)
      · have hLaterValue : second.val - earlierCount < laterCount := by omega
        let laterSecond : Fin laterCount :=
          ⟨second.val - earlierCount, hLaterValue⟩
        have hSecondEq : second = Fin.natAdd earlierCount laterSecond := by
          apply Fin.ext
          simp [laterSecond]
          omega
        rw [hFirstEq, hSecondEq,
          ← orderedJumpTimesCutSplit_fst_apply
            earlierCount laterCount times earlierFirst,
          ← orderedJumpTimesCutSplit_snd_apply
            earlierCount laterCount times laterSecond]
        exact (hEarlier.1 earlierFirst).2.trans (hLater.1 laterSecond).1
    · have hSecond : ¬second.val < earlierCount := by omega
      have hFirstLaterValue : first.val - earlierCount < laterCount := by omega
      have hSecondLaterValue : second.val - earlierCount < laterCount := by omega
      let laterFirst : Fin laterCount :=
        ⟨first.val - earlierCount, hFirstLaterValue⟩
      let laterSecond : Fin laterCount :=
        ⟨second.val - earlierCount, hSecondLaterValue⟩
      have hFirstEq : first = Fin.natAdd earlierCount laterFirst := by
        apply Fin.ext
        simp [laterFirst]
        omega
      have hSecondEq : second = Fin.natAdd earlierCount laterSecond := by
        apply Fin.ext
        simp [laterSecond]
        omega
      rw [hFirstEq, hSecondEq,
        ← orderedJumpTimesCutSplit_snd_apply
          earlierCount laterCount times laterFirst,
        ← orderedJumpTimesCutSplit_snd_apply
          earlierCount laterCount times laterSecond]
      have hLaterOrder : laterFirst < laterSecond := by
        change first.val - earlierCount < second.val - earlierCount
        omega
      exact hLater.2 hLaterOrder

/-- Away from a coordinate exactly at the cut, one cut sector is exactly the ordered-simplex
fibre with the corresponding number of observed events. -/
theorem mem_orderedJumpTimesCutSector_iff
    (earlierCount laterCount : ℕ) (lower cut upper : ℝ)
    (hLowerCut : lower ≤ cut) (hCutUpper : cut ≤ upper)
    (times : Fin (earlierCount + laterCount) → ℝ)
    (hNoCut : ∀ index, times index ≠ cut) :
    times ∈ orderedJumpTimesCutSector
        earlierCount laterCount lower cut upper ↔
      times ∈ orderedTimesInInterval
          (earlierCount + laterCount) lower upper ∧
        FiniteJumpHistory.eventCountAtOrBeforeTimeVector times cut = earlierCount := by
  constructor
  · intro hSector
    have hOrdered := orderedJumpTimesCutSector_subset_orderedTimesInInterval
      earlierCount laterCount lower cut upper hLowerCut hCutUpper hSector
    refine ⟨hOrdered, ?_⟩
    let observedCount :=
      FiniteJumpHistory.eventCountAtOrBeforeTimeVector times cut
    have hObservedCountLe : observedCount ≤ earlierCount + laterCount :=
      FiniteJumpHistory.eventCountAtOrBeforeTimeVector_le times cut
    have hLower : earlierCount ≤ observedCount := by
      by_contra hNotLower
      have hCountLt : observedCount < earlierCount := by omega
      let index : Fin (earlierCount + laterCount) :=
        ⟨observedCount, by omega⟩
      let earlierIndex : Fin earlierCount := ⟨observedCount, hCountLt⟩
      have hIndexEq : index = Fin.castAdd laterCount earlierIndex := Fin.ext rfl
      have hBefore : times index < cut := by
        change orderedJumpTimesCutSplit earlierCount laterCount times ∈
          orderedTimesInInterval earlierCount lower cut ×ˢ
            orderedTimesInInterval laterCount cut upper at hSector
        rw [hIndexEq, ← orderedJumpTimesCutSplit_fst_apply
          earlierCount laterCount times earlierIndex]
        exact (hSector.1.1 earlierIndex).2
      have hCharacterization :=
        FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
          hOrdered.2 cut index
      have hImpossible : index.val < observedCount :=
        hCharacterization.1 hBefore.le
      simp [index] at hImpossible
    have hUpper : observedCount ≤ earlierCount := by
      by_contra hNotUpper
      have hCountGt : earlierCount < observedCount := by omega
      have hLaterPositive : 0 < laterCount := by omega
      let index : Fin (earlierCount + laterCount) :=
        ⟨earlierCount, by omega⟩
      let laterIndex : Fin laterCount := ⟨0, hLaterPositive⟩
      have hIndexEq : index = Fin.natAdd earlierCount laterIndex := Fin.ext rfl
      have hAfter : cut < times index := by
        change orderedJumpTimesCutSplit earlierCount laterCount times ∈
          orderedTimesInInterval earlierCount lower cut ×ˢ
            orderedTimesInInterval laterCount cut upper at hSector
        rw [hIndexEq, ← orderedJumpTimesCutSplit_snd_apply
          earlierCount laterCount times laterIndex]
        exact (hSector.2.1 laterIndex).1
      have hCharacterization :=
        FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
          hOrdered.2 cut index
      exact (not_le_of_gt hAfter) (hCharacterization.2 hCountGt)
    omega
  · rintro ⟨hOrdered, hCount⟩
    change orderedJumpTimesCutSplit earlierCount laterCount times ∈
      orderedTimesInInterval earlierCount lower cut ×ˢ
        orderedTimesInInterval laterCount cut upper
    constructor
    · constructor
      · intro index
        rw [orderedJumpTimesCutSplit_fst_apply]
        let completeIndex := Fin.castAdd laterCount index
        have hBeforeOrAt : times completeIndex ≤ cut := by
          apply (FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
            hOrdered.2 cut completeIndex).2
          simpa only [completeIndex, hCount, Fin.val_castAdd] using index.isLt
        exact ⟨(hOrdered.1 completeIndex).1,
          lt_of_le_of_ne hBeforeOrAt (hNoCut completeIndex)⟩
      · intro first second hFirstSecond
        rw [orderedJumpTimesCutSplit_fst_apply,
          orderedJumpTimesCutSplit_fst_apply]
        exact hOrdered.2 (Fin.strictMono_castAdd laterCount hFirstSecond)
    · constructor
      · intro index
        rw [orderedJumpTimesCutSplit_snd_apply]
        let completeIndex := Fin.natAdd earlierCount index
        have hNotBeforeOrAt : ¬times completeIndex ≤ cut := by
          intro hBeforeOrAt
          have hIndexBefore :=
            (FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
              hOrdered.2 cut completeIndex).1 hBeforeOrAt
          simp only [completeIndex, hCount, Fin.natAdd] at hIndexBefore
          omega
        exact ⟨lt_of_not_ge hNotBeforeOrAt, (hOrdered.1 completeIndex).2⟩
      · intro first second hFirstSecond
        rw [orderedJumpTimesCutSplit_snd_apply,
          orderedJumpTimesCutSplit_snd_apply]
        exact hOrdered.2 (Fin.strictMono_natAdd earlierCount hFirstSecond)

/-- After removing the proved-null coordinate boundary, the exact observed-count fibre and the
strict before/after cut sector induce the same restricted Lebesgue measure. -/
theorem volume_restrict_orderedTimesInIntervalObservedCountSector_eq_cutSector
    (earlierCount laterCount : ℕ) (lower cut upper : ℝ)
    (hLowerCut : lower ≤ cut) (hCutUpper : cut ≤ upper) :
    volume.restrict
        (orderedTimesInIntervalObservedCountSector
          (earlierCount + laterCount) lower cut upper earlierCount) =
      volume.restrict
        (orderedJumpTimesCutSector
          earlierCount laterCount lower cut upper) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null
    · intro times hDifference
      by_contra hNotBoundary
      have hNoCut :=
        (not_mem_orderedJumpTimesCutBoundary_iff times cut).1 hNotBoundary
      have hCutSector :=
        (mem_orderedJumpTimesCutSector_iff
          earlierCount laterCount lower cut upper hLowerCut hCutUpper times hNoCut).2
          hDifference.1
      exact hDifference.2 hCutSector
    · exact volume_orderedJumpTimesCutBoundary
        (earlierCount + laterCount) cut
  · apply measure_mono_null
    · intro times hDifference
      by_contra hNotBoundary
      have hNoCut :=
        (not_mem_orderedJumpTimesCutBoundary_iff times cut).1 hNotBoundary
      have hObservedSector :=
        (mem_orderedJumpTimesCutSector_iff
          earlierCount laterCount lower cut upper hLowerCut hCutUpper times hNoCut).1
          hDifference.1
      exact hDifference.2 hObservedSector
    · exact volume_orderedJumpTimesCutBoundary
        (earlierCount + laterCount) cut

end

end FiniteMarkovProcesses.Probability
