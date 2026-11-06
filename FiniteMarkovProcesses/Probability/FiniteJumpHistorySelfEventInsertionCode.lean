/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertion

/-!
# Injective codes for finite-history self-event insertion

This module packages reduced physical state words and per-dwell self-event counts into the
dependent virtual-word carrier. Exact retained-transition positions recover every prefix count,
while self-event deletion recovers the original physical word. Together these facts make the
global encoding injective.

## Main Results

- `selfEventInsertedPhysicalTransitionEventIndex_val_eq_prefix`: exact cumulative-count position
  of every retained physical transition.
- `injective_selfEventInsertedStateWordCode`: fixed-word insertion-count encoding is injective.
- `injective_reducedSelfEventInsertionWordCode`: the global dependent encoding is injective.
-/

open scoped BigOperators

universe u

namespace FiniteJumpHistory

variable {State : Type u}

/-- Numeric position of a retained physical transition: all complete earlier repeated blocks,
followed by the self-events in its source block. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_val
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).val =
      (∑ previous : Fin index.val,
        (selfEventCounts
          (Fin.castLE index.castSucc.isLt.le previous) + 1)) +
        selfEventCounts index.castSucc := by
  unfold selfEventInsertedPhysicalTransitionEventIndex
    selfEventInsertedPhysicalTransitionStatePosition
    selfEventInsertedStatePositionEquiv
  simp only [Fin.coe_castPred, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  simp

/-- Equivalent cumulative-count form of the retained-transition position. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_val_eq_prefix
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).val =
      index.val +
        ∑ previous : Fin (index.val + 1),
          selfEventCounts (Fin.castLE index.castSucc.isLt previous) := by
  rw [selfEventInsertedPhysicalTransitionEventIndex_val]
  rw [Fin.sum_univ_castSucc]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hPrefix :
      (∑ previous : Fin index.val,
        selfEventCounts (Fin.castLE index.castSucc.isLt.le previous)) =
        ∑ previous : Fin index.val,
          selfEventCounts
            (Fin.castLE index.castSucc.isLt previous.castSucc) := by
    apply Finset.sum_congr rfl
    intro previous _
    congr 1
  have hLast :
      Fin.castLE index.castSucc.isLt (Fin.last index.val) = index.castSucc := by
    apply Fin.ext
    rfl
  rw [← hPrefix, hLast]
  change
    (∑ previous : Fin index.val,
        selfEventCounts (Fin.castLE index.castSucc.isLt.le previous)) +
          index.val + selfEventCounts index.castSucc =
      index.val +
        ((∑ previous : Fin index.val,
          selfEventCounts (Fin.castLE index.castSucc.isLt.le previous)) +
            selfEventCounts index.castSucc)
  omega

/-- Package the event count and expanded state word produced by one insertion-count vector. -/
def selfEventInsertedStateWordCode {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Σ eventCount : ℕ, Fin (eventCount + 1) → State :=
  ⟨selfEventInsertedEventCount selfEventCounts,
    selfEventInsertedStateWord states selfEventCounts⟩

/-- For a reduced physical state word, distinct per-dwell self-event count vectors produce
distinct dependent virtual state-word codes. -/
theorem injective_selfEventInsertedStateWordCode
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Function.Injective (selfEventInsertedStateWordCode states) := by
  intro firstCounts secondCounts hCode
  have hEventCount := congrArg (fun code ↦ code.1) hCode
  change selfEventInsertedEventCount firstCounts =
    selfEventInsertedEventCount secondCounts at hEventCount
  let genuineValue :
      (Σ eventCount : ℕ, Fin (eventCount + 1) → State) → ℕ → ℕ :=
    fun code index ↦
      if hIndex : index < genuineEventCount code.2 then
        (genuineEventIndex code.2 ⟨index, hIndex⟩).val
      else 0
  have hGenuineValue := congrArg genuineValue hCode
  have hTransitionValue (physicalIndex : Fin physicalEventCount) :
      (selfEventInsertedPhysicalTransitionEventIndex
          firstCounts physicalIndex).val =
        (selfEventInsertedPhysicalTransitionEventIndex
          secondCounts physicalIndex).val := by
    have hFirstCount := genuineEventCount_selfEventInsertedStateWord
      states firstCounts hReduced
    have hSecondCount := genuineEventCount_selfEventInsertedStateWord
      states secondCounts hReduced
    have hFirstBound : physicalIndex.val <
        genuineEventCount (selfEventInsertedStateWord states firstCounts) := by
      rw [hFirstCount]
      exact physicalIndex.isLt
    have hSecondBound : physicalIndex.val <
        genuineEventCount (selfEventInsertedStateWord states secondCounts) := by
      rw [hSecondCount]
      exact physicalIndex.isLt
    have hValue := congrFun hGenuineValue physicalIndex.val
    change (if hIndex : physicalIndex.val <
          genuineEventCount (selfEventInsertedStateWord states firstCounts) then
        (genuineEventIndex (selfEventInsertedStateWord states firstCounts)
          ⟨physicalIndex.val, hIndex⟩).val else 0) =
      (if hIndex : physicalIndex.val <
          genuineEventCount (selfEventInsertedStateWord states secondCounts) then
        (genuineEventIndex (selfEventInsertedStateWord states secondCounts)
          ⟨physicalIndex.val, hIndex⟩).val else 0) at hValue
    rw [dite_eq_left hFirstBound, dite_eq_left hSecondBound] at hValue
    have hFirstIndex :
        (⟨physicalIndex.val, hFirstBound⟩ :
            Fin (genuineEventCount
              (selfEventInsertedStateWord states firstCounts))) =
          Fin.cast hFirstCount.symm physicalIndex := by
      apply Fin.ext
      rfl
    have hSecondIndex :
        (⟨physicalIndex.val, hSecondBound⟩ :
            Fin (genuineEventCount
              (selfEventInsertedStateWord states secondCounts))) =
          Fin.cast hSecondCount.symm physicalIndex := by
      apply Fin.ext
      rfl
    rw [hFirstIndex,
      genuineEventIndex_selfEventInsertedStateWord
        states firstCounts hReduced physicalIndex] at hValue
    rw [hSecondIndex,
      genuineEventIndex_selfEventInsertedStateWord
        states secondCounts hReduced physicalIndex] at hValue
    exact hValue
  have hPrefix (block : Fin (physicalEventCount + 1)) :
      (∑ previous : Fin (block.val + 1),
        firstCounts (Fin.castLE block.isLt previous)) =
      ∑ previous : Fin (block.val + 1),
        secondCounts (Fin.castLE block.isLt previous) := by
    by_cases hLast : block = Fin.last physicalEventCount
    · subst block
      have hSum : (∑ index, firstCounts index) =
          ∑ index, secondCounts index := by
        unfold selfEventInsertedEventCount at hEventCount
        omega
      have hFirstFunction :
          (fun previous : Fin (physicalEventCount + 1) ↦
            firstCounts
              (Fin.castLE (Fin.last physicalEventCount).isLt previous)) =
            firstCounts := by
        funext previous
        congr 1
      have hSecondFunction :
          (fun previous : Fin (physicalEventCount + 1) ↦
            secondCounts
              (Fin.castLE (Fin.last physicalEventCount).isLt previous)) =
            secondCounts := by
        funext previous
        congr 1
      simpa only [Fin.val_last, hFirstFunction, hSecondFunction] using hSum
    · let physicalIndex : Fin physicalEventCount := block.castPred hLast
      have hFirstPosition :=
        selfEventInsertedPhysicalTransitionEventIndex_val_eq_prefix
          firstCounts physicalIndex
      have hSecondPosition :=
        selfEventInsertedPhysicalTransitionEventIndex_val_eq_prefix
          secondCounts physicalIndex
      have hFirstPosition' :
          (selfEventInsertedPhysicalTransitionEventIndex
              firstCounts physicalIndex).val =
            block.val +
              ∑ previous : Fin (block.val + 1),
                firstCounts (Fin.castLE block.isLt previous) := by
        simpa +instances only [physicalIndex, Fin.coe_castPred, Fin.val_castSucc]
          using hFirstPosition
      have hSecondPosition' :
          (selfEventInsertedPhysicalTransitionEventIndex
              secondCounts physicalIndex).val =
            block.val +
              ∑ previous : Fin (block.val + 1),
                secondCounts (Fin.castLE block.isLt previous) := by
        simpa +instances only [physicalIndex, Fin.coe_castPred, Fin.val_castSucc]
          using hSecondPosition
      have hPosition := hTransitionValue physicalIndex
      omega
  funext block
  refine Fin.cases ?_ (fun previous ↦ ?_) block
  · have hPrefixZero := hPrefix (0 : Fin (physicalEventCount + 1))
    simp +instances only [Fin.val_zero] at hPrefixZero
    convert hPrefixZero using 1 <;> congr 1
  · have hCurrent := hPrefix previous.succ
    have hPrevious := hPrefix previous.castSucc
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hCurrent
    have hFirstPrefix :
        (∑ index : Fin (previous.val + 1),
          firstCounts
            (Fin.castLE previous.succ.isLt index.castSucc)) =
        ∑ index : Fin (previous.val + 1),
          firstCounts (Fin.castLE previous.castSucc.isLt index) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
    have hSecondPrefix :
        (∑ index : Fin (previous.val + 1),
          secondCounts
            (Fin.castLE previous.succ.isLt index.castSucc)) =
        ∑ index : Fin (previous.val + 1),
          secondCounts (Fin.castLE previous.castSucc.isLt index) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
    have hLast :
        Fin.castLE previous.succ.isLt (Fin.last (previous.val + 1)) =
          previous.succ := by
      apply Fin.ext
      rfl
    have hCurrentNormalized :
        (∑ index : Fin (previous.val + 1),
            firstCounts (Fin.castLE previous.castSucc.isLt index)) +
              firstCounts previous.succ =
          (∑ index : Fin (previous.val + 1),
            secondCounts (Fin.castLE previous.castSucc.isLt index)) +
              secondCounts previous.succ := by
      calc
        (∑ index : Fin (previous.val + 1),
            firstCounts (Fin.castLE previous.castSucc.isLt index)) +
              firstCounts previous.succ =
            (∑ index : Fin (previous.val + 1),
              firstCounts
                (Fin.castLE previous.succ.isLt index.castSucc)) +
                firstCounts previous.succ := by rw [hFirstPrefix]
        _ = (∑ index : Fin (previous.val + 1),
              firstCounts
                (Fin.castLE previous.succ.isLt index.castSucc)) +
                firstCounts
                  (Fin.castLE previous.succ.isLt
                    (Fin.last (previous.val + 1))) := by rw [hLast]
        _ = (∑ index : Fin (previous.val + 1),
              secondCounts
                (Fin.castLE previous.succ.isLt index.castSucc)) +
                secondCounts
                  (Fin.castLE previous.succ.isLt
                    (Fin.last (previous.val + 1))) := hCurrent
        _ = (∑ index : Fin (previous.val + 1),
              secondCounts
                (Fin.castLE previous.succ.isLt index.castSucc)) +
                secondCounts previous.succ := by rw [hLast]
        _ = (∑ index : Fin (previous.val + 1),
              secondCounts (Fin.castLE previous.castSucc.isLt index)) +
                secondCounts previous.succ := by rw [hSecondPrefix]
    have hPreviousNormalized :
        (∑ index : Fin (previous.val + 1),
          firstCounts (Fin.castLE previous.castSucc.isLt index)) =
        ∑ index : Fin (previous.val + 1),
          secondCounts (Fin.castLE previous.castSucc.isLt index) := by
      simpa only [Fin.val_castSucc] using hPrevious
    clear hCurrent hPrevious hFirstPrefix hSecondPrefix hLast
    omega

/-- Global code for a reduced physical state word together with arbitrary per-dwell self-event
counts. -/
abbrev ReducedSelfEventInsertionWordCode (State : Type u) :=
  Σ physicalEventCount : ℕ,
    ({states : Fin (physicalEventCount + 1) → State //
        ∀ index : Fin physicalEventCount,
          states index.castSucc ≠ states index.succ} ×
      (Fin (physicalEventCount + 1) → ℕ))

/-- Expand a global reduced-word insertion code to its dependent virtual event-count/state-word
code. -/
def reducedSelfEventInsertionWordCode
    (code : ReducedSelfEventInsertionWordCode State) :
    Σ eventCount : ℕ, Fin (eventCount + 1) → State :=
  selfEventInsertedStateWordCode code.2.1.1 code.2.2

/-- The global reduced-word insertion encoding is injective. -/
theorem injective_reducedSelfEventInsertionWordCode [DecidableEq State] :
    Function.Injective
      (reducedSelfEventInsertionWordCode (State := State)) := by
  rintro ⟨firstEventCount, ⟨⟨firstStates, hFirstReduced⟩, firstCounts⟩⟩
    ⟨secondEventCount, ⟨⟨secondStates, hSecondReduced⟩, secondCounts⟩⟩ hCode
  let deleteCode :
      (Σ eventCount : ℕ, Fin (eventCount + 1) → State) →
        FiniteJumpHistory State :=
    fun code ↦ deleteSelfEvents <|
      embedJumpTimes code.1 code.2 (fun _ ↦ 0)
  have hDeleted := congrArg deleteCode hCode
  have hFirstDeletion :
      deleteCode (selfEventInsertedStateWordCode firstStates firstCounts) =
        embedJumpTimes firstEventCount firstStates (fun _ ↦ 0) := by
    change deleteSelfEventsSlice
      (selfEventInsertedStateWord firstStates firstCounts) (fun _ ↦ 0) = _
    apply deleteSelfEventsSlice_selfEventInsertedStateWord
      firstStates firstCounts hFirstReduced
    intro index
    rfl
  have hSecondDeletion :
      deleteCode (selfEventInsertedStateWordCode secondStates secondCounts) =
        embedJumpTimes secondEventCount secondStates (fun _ ↦ 0) := by
    change deleteSelfEventsSlice
      (selfEventInsertedStateWord secondStates secondCounts) (fun _ ↦ 0) = _
    apply deleteSelfEventsSlice_selfEventInsertedStateWord
      secondStates secondCounts hSecondReduced
    intro index
    rfl
  have hPhysicalHistory :
      embedJumpTimes firstEventCount firstStates (fun _ ↦ 0) =
        embedJumpTimes secondEventCount secondStates (fun _ ↦ 0) := by
    rw [← hFirstDeletion, ← hSecondDeletion]
    exact hDeleted
  have hEventCount := congrArg FiniteJumpHistory.jumpCount hPhysicalHistory
  change firstEventCount = secondEventCount at hEventCount
  subst secondEventCount
  have hHistoryComponents := (Sigma.mk.inj_iff).mp hPhysicalHistory
  have hStateTime :
      (firstStates, (fun _ : Fin firstEventCount ↦ (0 : ℝ))) =
        (secondStates, (fun _ : Fin firstEventCount ↦ (0 : ℝ))) :=
    eq_of_heq hHistoryComponents.2
  have hStates : firstStates = secondStates := congrArg Prod.fst hStateTime
  subst secondStates
  have hCounts : firstCounts = secondCounts :=
    injective_selfEventInsertedStateWordCode firstStates hFirstReduced hCode
  subst secondCounts
  rfl

end FiniteJumpHistory
