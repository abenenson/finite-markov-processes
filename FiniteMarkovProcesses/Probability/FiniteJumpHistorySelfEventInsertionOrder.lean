/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertion
import FiniteMarkovProcesses.Probability.OrderedSelfEventInsertionVolume

/-!
# Ordering canonically inserted self-event times

This module joins a reduced physical jump-time vector with one ordered insertion simplex in every
physical dwell. It proves that the canonical merged vector is itself strictly ordered and that
the resulting virtual history deletes exactly to the original physical history.

The result is finite-coordinate geometry only. It contains no Markov rates, source model, or
action interpretation.

## Main Results

- `FiniteJumpHistory.selfEventInsertedJumpTimes_mem_orderedJumpTimes`: ordered physical and
  insertion coordinates merge into the complete ordered virtual-time simplex.
- `FiniteJumpHistory.strictMono_selfEventInsertedSelfEventIndex`: inserted self-events retain
  their strict local order.
- `FiniteJumpHistory.deleteSelfEvents_insertedHistory`: the resulting virtual history deletes
  exactly to the original reduced physical history.
-/

open FiniteMarkovProcesses.Probability

universe u

namespace FiniteJumpHistory

variable {State : Type u}

/-- Inserted self-events within one physical dwell retain their strict local order in the virtual
event word. -/
theorem strictMono_selfEventInsertedSelfEventIndex {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (block : Fin (physicalEventCount + 1)) :
    StrictMono (selfEventInsertedSelfEventIndex selfEventCounts block) := by
  intro first second hIndex
  apply Fin.castSucc_lt_castSucc_iff.mp
  simp only [selfEventInsertedSelfEventIndex_castSucc]
  unfold selfEventInsertedSelfEventStatePosition
  exact (strictMono_selfEventInsertedStatePositionEquiv_block
    selfEventCounts block) (Fin.castSucc_lt_castSucc_iff.mpr hIndex)

/-- Every inserted self-event in a nonterminal dwell precedes that dwell's retained physical
transition. -/
theorem selfEventInsertedSelfEventIndex_lt_physicalTransitionEventIndex
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (block : Fin (physicalEventCount + 1))
    (hBlock : block ≠ Fin.last physicalEventCount)
    (selfEventIndex : Fin (selfEventCounts block)) :
    selfEventInsertedSelfEventIndex selfEventCounts block selfEventIndex <
      selfEventInsertedPhysicalTransitionEventIndex selfEventCounts
        (block.castPred hBlock) := by
  apply Fin.castSucc_lt_castSucc_iff.mp
  rw [selfEventInsertedSelfEventIndex_castSucc,
    selfEventInsertedPhysicalTransitionEventIndex_castSucc]
  unfold selfEventInsertedSelfEventStatePosition
    selfEventInsertedPhysicalTransitionStatePosition
  rw [Fin.castSucc_castPred block hBlock]
  exact (strictMono_selfEventInsertedStatePositionEquiv_block
    selfEventCounts block) (Fin.castSucc_lt_last selfEventIndex)

/-- A retained transition sourced in an earlier physical block precedes every inserted self-event
in a later block. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_lt_selfEventIndex_of_block_lt
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (physicalIndex : Fin physicalEventCount)
    (block : Fin (physicalEventCount + 1))
    (hBlock : physicalIndex.castSucc < block)
    (selfEventIndex : Fin (selfEventCounts block)) :
    selfEventInsertedPhysicalTransitionEventIndex selfEventCounts physicalIndex <
      selfEventInsertedSelfEventIndex selfEventCounts block selfEventIndex := by
  apply Fin.castSucc_lt_castSucc_iff.mp
  rw [selfEventInsertedPhysicalTransitionEventIndex_castSucc,
    selfEventInsertedSelfEventIndex_castSucc]
  unfold selfEventInsertedPhysicalTransitionStatePosition
    selfEventInsertedSelfEventStatePosition
  exact selfEventInsertedStatePositionEquiv_lt_of_block_lt
    selfEventCounts hBlock (Fin.last (selfEventCounts physicalIndex.castSucc))
      selfEventIndex.castSucc

/-- Physical dwell block containing either an inserted self-event or a retained physical
transition coordinate. -/
def selfEventInsertedEventCoordinateBlock {physicalEventCount : ℕ}
    {selfEventCounts : Fin (physicalEventCount + 1) → ℕ} :
    SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount →
      Fin (physicalEventCount + 1)
  | Sum.inl ⟨index, _⟩ => index
  | Sum.inr index => index.castSucc

/-- Every canonical event time lies weakly below the upper boundary of its physical dwell. -/
theorem selfEventInsertedJumpTimes_le_upperBoundary {physicalEventCount : ℕ}
    {T : ℝ} {physicalTimes : Fin physicalEventCount → ℝ}
    {selfEventCounts : Fin (physicalEventCount + 1) → ℕ}
    {insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ}
    (hInsertions :
      insertionTimes ∈ orderedSelfEventInsertions T physicalTimes selfEventCounts)
    (coordinate : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount) :
    selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedEventCoordinate selfEventCounts coordinate) ≤
      boundaryTimeVector T physicalTimes
        (selfEventInsertedEventCoordinateBlock coordinate).succ := by
  rcases coordinate with ⟨index, selfEventIndex⟩ | index
  · simp only [selfEventInsertedEventCoordinate,
      selfEventInsertedEventCoordinateBlock]
    rw [selfEventInsertedJumpTimes_selfEventIndex]
    exact (hInsertions index (Set.mem_univ index)).1 selfEventIndex |>.2.le
  · simp only [selfEventInsertedEventCoordinate,
      selfEventInsertedEventCoordinateBlock]
    rw [selfEventInsertedJumpTimes_physicalTransitionEventIndex]
    rw [boundaryTimeVector_succ_castSucc]

/-- Every canonical event time lies strictly above the lower boundary of its physical dwell. -/
theorem lowerBoundary_lt_selfEventInsertedJumpTimes {physicalEventCount : ℕ}
    {T : ℝ} {physicalTimes : Fin physicalEventCount → ℝ}
    {selfEventCounts : Fin (physicalEventCount + 1) → ℕ}
    {insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ}
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T)
    (hInsertions :
      insertionTimes ∈ orderedSelfEventInsertions T physicalTimes selfEventCounts)
    (coordinate : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount) :
    boundaryTimeVector T physicalTimes
        (selfEventInsertedEventCoordinateBlock coordinate).castSucc <
      selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedEventCoordinate selfEventCounts coordinate) := by
  rcases coordinate with ⟨index, selfEventIndex⟩ | index
  · simp only [selfEventInsertedEventCoordinate,
      selfEventInsertedEventCoordinateBlock]
    rw [selfEventInsertedJumpTimes_selfEventIndex]
    exact (hInsertions index (Set.mem_univ index)).1 selfEventIndex |>.1
  · simp only [selfEventInsertedEventCoordinate,
      selfEventInsertedEventCoordinateBlock]
    rw [selfEventInsertedJumpTimes_physicalTransitionEventIndex]
    simpa only [boundaryTimeVector_succ_castSucc] using
      boundaryTimeVector_castSucc_lt_succ_of_mem_orderedJumpTimes
        hPhysicalTimes index

/-- Events belonging to strictly earlier physical dwell blocks have strictly earlier merged
jump times. -/
theorem selfEventInsertedJumpTimes_lt_of_block_lt {physicalEventCount : ℕ}
    {T : ℝ} (hT : 0 ≤ T)
    {physicalTimes : Fin physicalEventCount → ℝ}
    {selfEventCounts : Fin (physicalEventCount + 1) → ℕ}
    {insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ}
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T)
    (hInsertions :
      insertionTimes ∈ orderedSelfEventInsertions T physicalTimes selfEventCounts)
    {first second : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount}
    (hBlock : selfEventInsertedEventCoordinateBlock first <
      selfEventInsertedEventCoordinateBlock second) :
    selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedEventCoordinate selfEventCounts first) <
      selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedEventCoordinate selfEventCounts second) := by
  have hBoundary :
      (selfEventInsertedEventCoordinateBlock first).succ ≤
        (selfEventInsertedEventCoordinateBlock second).castSucc := by
    change (selfEventInsertedEventCoordinateBlock first).val + 1 ≤
      (selfEventInsertedEventCoordinateBlock second).val
    exact hBlock
  exact (selfEventInsertedJumpTimes_le_upperBoundary hInsertions first).trans_lt <|
    ((monotone_boundaryTimeVector_of_mem_orderedJumpTimes hT hPhysicalTimes)
      hBoundary).trans_lt <|
        lowerBoundary_lt_selfEventInsertedJumpTimes
          hPhysicalTimes hInsertions second

/-- Ordered physical jump times and ordered self-event insertions merge into the complete ordered
virtual jump-time simplex. -/
theorem selfEventInsertedJumpTimes_mem_orderedJumpTimes {physicalEventCount : ℕ}
    {T : ℝ} (hT : 0 ≤ T)
    {physicalTimes : Fin physicalEventCount → ℝ}
    {selfEventCounts : Fin (physicalEventCount + 1) → ℕ}
    {insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ}
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T)
    (hInsertions :
      insertionTimes ∈ orderedSelfEventInsertions T physicalTimes selfEventCounts) :
    selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes ∈
      orderedJumpTimes (selfEventInsertedEventCount selfEventCounts) T := by
  constructor
  · intro eventIndex
    let coordinate :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).symm eventIndex
    have hEvent :
        selfEventInsertedEventCoordinate selfEventCounts coordinate = eventIndex :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).apply_symm_apply eventIndex
    rw [← hEvent]
    constructor
    · have hLowerNonnegative :=
        (monotone_boundaryTimeVector_of_mem_orderedJumpTimes hT hPhysicalTimes)
          (Fin.zero_le
            (selfEventInsertedEventCoordinateBlock coordinate).castSucc)
      rw [boundaryTimeVector_zero] at hLowerNonnegative
      exact hLowerNonnegative.trans_lt <|
        lowerBoundary_lt_selfEventInsertedJumpTimes
          hPhysicalTimes hInsertions coordinate
    · rcases coordinate with ⟨index, selfEventIndex⟩ | index
      · simp only [selfEventInsertedEventCoordinate]
        rw [selfEventInsertedJumpTimes_selfEventIndex]
        exact ((hInsertions index (Set.mem_univ index)).1 selfEventIndex).2.trans_le <| by
          simpa only [boundaryTimeVector_last] using
            (monotone_boundaryTimeVector_of_mem_orderedJumpTimes hT hPhysicalTimes)
              (Fin.le_last index.succ)
      · simp only [selfEventInsertedEventCoordinate]
        rw [selfEventInsertedJumpTimes_physicalTransitionEventIndex]
        exact (hPhysicalTimes.1 index).2
  · intro firstEvent secondEvent hEvents
    let firstCoordinate :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).symm firstEvent
    let secondCoordinate :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).symm secondEvent
    have hFirst :
        selfEventInsertedEventCoordinate selfEventCounts firstCoordinate = firstEvent :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).apply_symm_apply firstEvent
    have hSecond :
        selfEventInsertedEventCoordinate selfEventCounts secondCoordinate = secondEvent :=
      (selfEventInsertedEventCoordinateEquiv selfEventCounts).apply_symm_apply secondEvent
    rw [← hFirst, ← hSecond] at hEvents ⊢
    rcases firstCoordinate with ⟨firstBlock, firstIndex⟩ | firstIndex
    · rcases secondCoordinate with ⟨secondBlock, secondIndex⟩ | secondIndex
      · have hPositions := Fin.castSucc_lt_castSucc_iff.mpr hEvents
        simp only [selfEventInsertedEventCoordinate,
          selfEventInsertedSelfEventIndex_castSucc] at hPositions
        unfold selfEventInsertedSelfEventStatePosition at hPositions
        rcases lt_trichotomy firstBlock secondBlock with
          hBlock | hBlock | hBlock
        · exact selfEventInsertedJumpTimes_lt_of_block_lt
            hT hPhysicalTimes hInsertions hBlock
        · subst secondBlock
          have hLocalCast :=
            (strictMono_selfEventInsertedStatePositionEquiv_block
              selfEventCounts firstBlock).lt_iff_lt.mp hPositions
          have hLocal := Fin.castSucc_lt_castSucc_iff.mp hLocalCast
          simp only [selfEventInsertedEventCoordinate]
          rw [selfEventInsertedJumpTimes_selfEventIndex,
            selfEventInsertedJumpTimes_selfEventIndex]
          exact (hInsertions firstBlock (Set.mem_univ firstBlock)).2 hLocal
        · have hReverse :=
            selfEventInsertedStatePositionEquiv_lt_of_block_lt
              selfEventCounts hBlock secondIndex.castSucc firstIndex.castSucc
          exact False.elim (hPositions.asymm hReverse)
      · have hPositions := Fin.castSucc_lt_castSucc_iff.mpr hEvents
        simp only [selfEventInsertedEventCoordinate,
          selfEventInsertedSelfEventIndex_castSucc,
          selfEventInsertedPhysicalTransitionEventIndex_castSucc] at hPositions
        unfold selfEventInsertedSelfEventStatePosition
          selfEventInsertedPhysicalTransitionStatePosition at hPositions
        rcases lt_trichotomy firstBlock secondIndex.castSucc with
          hBlock | hBlock | hBlock
        · exact selfEventInsertedJumpTimes_lt_of_block_lt
            hT hPhysicalTimes hInsertions hBlock
        · subst firstBlock
          simp only [selfEventInsertedEventCoordinate]
          rw [selfEventInsertedJumpTimes_selfEventIndex,
            selfEventInsertedJumpTimes_physicalTransitionEventIndex]
          simpa only [boundaryTimeVector_succ_castSucc] using
            ((hInsertions secondIndex.castSucc
              (Set.mem_univ secondIndex.castSucc)).1 firstIndex).2
        · have hReverse :=
            selfEventInsertedStatePositionEquiv_lt_of_block_lt
              selfEventCounts hBlock
              (Fin.last (selfEventCounts secondIndex.castSucc))
              firstIndex.castSucc
          exact False.elim (hPositions.asymm hReverse)
    · rcases secondCoordinate with ⟨secondBlock, secondIndex⟩ | secondIndex
      · have hPositions := Fin.castSucc_lt_castSucc_iff.mpr hEvents
        simp only [selfEventInsertedEventCoordinate,
          selfEventInsertedSelfEventIndex_castSucc,
          selfEventInsertedPhysicalTransitionEventIndex_castSucc] at hPositions
        unfold selfEventInsertedSelfEventStatePosition
          selfEventInsertedPhysicalTransitionStatePosition at hPositions
        rcases lt_trichotomy firstIndex.castSucc secondBlock with
          hBlock | hBlock | hBlock
        · exact selfEventInsertedJumpTimes_lt_of_block_lt
            hT hPhysicalTimes hInsertions hBlock
        · subst secondBlock
          have hReverse :=
            (strictMono_selfEventInsertedStatePositionEquiv_block
              selfEventCounts firstIndex.castSucc) (Fin.castSucc_lt_last secondIndex)
          exact False.elim (hPositions.asymm hReverse)
        · have hReverse :=
            selfEventInsertedStatePositionEquiv_lt_of_block_lt
              selfEventCounts hBlock secondIndex.castSucc
              (Fin.last (selfEventCounts firstIndex.castSucc))
          exact False.elim (hPositions.asymm hReverse)
      · have hIndex :=
          (strictMono_selfEventInsertedPhysicalTransitionEventIndex
            selfEventCounts).lt_iff_lt.mp hEvents
        simp only [selfEventInsertedEventCoordinate]
        rw [selfEventInsertedJumpTimes_physicalTransitionEventIndex,
          selfEventInsertedJumpTimes_physicalTransitionEventIndex]
        exact hPhysicalTimes.2 hIndex

/-- The canonically inserted virtual history is an exact representative of its reduced physical
history under self-event deletion. -/
theorem deleteSelfEvents_insertedHistory [DecidableEq State]
    {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    deleteSelfEvents
        (embedJumpTimes (selfEventInsertedEventCount selfEventCounts)
          (selfEventInsertedStateWord states selfEventCounts)
          (selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes)) =
      embedJumpTimes physicalEventCount states physicalTimes := by
  exact deleteSelfEventsSlice_selfEventInsertedStateWord_selfEventInsertedJumpTimes
    states selfEventCounts hReduced insertionTimes physicalTimes

end FiniteJumpHistory
