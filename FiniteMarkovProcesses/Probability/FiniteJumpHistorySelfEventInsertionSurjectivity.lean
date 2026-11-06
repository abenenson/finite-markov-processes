/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionCode

/-!
# Canonical run-length decoder for finite state words

This module constructs the block geometry needed to prove that every finite virtual state word is
the self-event expansion of its uniquely reduced physical word.  The block starts are zero and the
successors of genuine events; the block ends are genuine-event source positions and the terminal
state position.  Their differences are the canonical self-event counts.

The resulting decoder is the missing surjectivity direction complementary to the existing
injective insertion code.  No measure or jump-law claim is made before the expanded-word identity
is proved.
-/

open scoped BigOperators

universe u

namespace FiniteJumpHistory

variable {State : Type u}

/-- First state position in one maximal constant block of a finite state word. -/
noncomputable def genuineStateBlockStart
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    Fin (genuineEventCount states + 1) → Fin (eventCount + 1) :=
  Fin.cases 0 fun previous ↦ (genuineEventIndex states previous).succ

/-- Last state position in one maximal constant block of a finite state word. -/
noncomputable def genuineStateBlockEnd
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) : Fin (eventCount + 1) :=
  if hBlock : block.val < genuineEventCount states then
    (genuineEventIndex states ⟨block.val, hBlock⟩).castSucc
  else Fin.last eventCount

/-- Every canonical maximal-constant block has its start weakly before its end. -/
theorem genuineStateBlockStart_le_end
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) :
    genuineStateBlockStart states block ≤ genuineStateBlockEnd states block := by
  refine Fin.cases ?_ (fun previous ↦ ?_) block
  · simp [genuineStateBlockStart, genuineStateBlockEnd]
  · unfold genuineStateBlockStart genuineStateBlockEnd
    split_ifs with hBlock
    · change (genuineEventIndex states previous).val + 1 ≤
        (genuineEventIndex states ⟨previous.val + 1, hBlock⟩).val
      let current : Fin (genuineEventCount states) :=
        ⟨previous.val + 1, hBlock⟩
      have hStrict : previous < current := by
        change previous.val < current.val
        simp [current]
      have hEvents :=
        ((genuineEventIndices states).orderEmbOfFin rfl).strictMono hStrict
      change (genuineEventIndex states previous).val <
        (genuineEventIndex states current).val at hEvents
      change (genuineEventIndex states previous).val + 1 ≤
        (genuineEventIndex states current).val
      omega
    · change (genuineEventIndex states previous).val + 1 ≤ eventCount
      exact (genuineEventIndex states previous).isLt

/-- Canonical maximal-constant block starts occur in chronological order. -/
theorem monotone_genuineStateBlockStart
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    Monotone (genuineStateBlockStart states) := by
  intro first second hLe
  revert second
  refine Fin.cases ?_ (fun firstPrevious ↦ ?_) first
  · intro second _
    exact Fin.zero_le _
  · intro second hLe
    have hSecondPositive : 0 < second := lt_of_lt_of_le (Fin.succ_pos _) hLe
    let secondPrevious : Fin (genuineEventCount states) :=
      second.pred (Fin.ne_of_gt hSecondPositive)
    have hSecond : secondPrevious.succ = second := by
      exact Fin.succ_pred second (Fin.ne_of_gt hSecondPositive)
    rw [← hSecond] at hLe ⊢
    change firstPrevious.val + 1 ≤ secondPrevious.val + 1 at hLe
    unfold genuineStateBlockStart
    change (genuineEventIndex states firstPrevious).val + 1 ≤
      (genuineEventIndex states secondPrevious).val + 1
    exact Nat.add_le_add_right
      (((genuineEventIndices states).orderEmbOfFin rfl).monotone (by omega)) 1

/-- The first maximal-constant block begins at the first state position. -/
@[simp]
theorem genuineStateBlockStart_zero
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    genuineStateBlockStart states 0 = 0 := by
  rfl

/-- The block following a genuine transition begins immediately after the preceding block ends. -/
theorem genuineStateBlockEnd_castSucc_add_one
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states)) :
    (genuineStateBlockEnd states block.castSucc).val + 1 =
      (genuineStateBlockStart states block.succ).val := by
  unfold genuineStateBlockEnd genuineStateBlockStart
  simp only [Fin.val_castSucc, dite_eq_left block.isLt, Fin.cases_succ]
  rfl

/-- The final maximal-constant block ends at the final state position. -/
@[simp]
theorem genuineStateBlockEnd_last
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    genuineStateBlockEnd states (Fin.last (genuineEventCount states)) =
      Fin.last eventCount := by
  unfold genuineStateBlockEnd
  rw [dite_eq_right]
  simp

/-- Number of virtual self-events inside one canonical maximal-constant block. -/
noncomputable def genuineStateBlockSelfEventCount
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) : ℕ :=
  (genuineStateBlockEnd states block).val -
    (genuineStateBlockStart states block).val

/-- A canonical block has exactly one more state position than its self-event count. -/
theorem genuineStateBlockStart_add_selfEventCount
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) :
    (genuineStateBlockStart states block).val +
        genuineStateBlockSelfEventCount states block =
      (genuineStateBlockEnd states block).val := by
  unfold genuineStateBlockSelfEventCount
  have hLe := genuineStateBlockStart_le_end states block
  change (genuineStateBlockStart states block).val ≤
    (genuineStateBlockEnd states block).val at hLe
  omega

/-- A nonterminal block occupies the interval between two consecutive canonical starts. -/
theorem genuineStateBlockSelfEventCount_castSucc_add_one
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states)) :
    genuineStateBlockSelfEventCount states block.castSucc + 1 =
      (genuineStateBlockStart states block.succ).val -
        (genuineStateBlockStart states block.castSucc).val := by
  have hBlock := genuineStateBlockStart_add_selfEventCount states block.castSucc
  have hNext := genuineStateBlockEnd_castSucc_add_one states block
  have hStartLe := genuineStateBlockStart_le_end states block.castSucc
  change (genuineStateBlockStart states block.castSucc).val ≤
    (genuineStateBlockEnd states block.castSucc).val at hStartLe
  omega

/-- The final block occupies the remaining state positions through the terminal state. -/
theorem genuineStateBlockSelfEventCount_last_add_one
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    genuineStateBlockSelfEventCount states
          (Fin.last (genuineEventCount states)) + 1 =
      eventCount + 1 -
        (genuineStateBlockStart states
          (Fin.last (genuineEventCount states))).val := by
  have hBlock := genuineStateBlockStart_add_selfEventCount states
    (Fin.last (genuineEventCount states))
  rw [genuineStateBlockEnd_last] at hBlock
  change (genuineStateBlockStart states
      (Fin.last (genuineEventCount states))).val +
        genuineStateBlockSelfEventCount states
          (Fin.last (genuineEventCount states)) = eventCount at hBlock
  have hStartLe := genuineStateBlockStart_le_end states
    (Fin.last (genuineEventCount states))
  rw [genuineStateBlockEnd_last] at hStartLe
  change (genuineStateBlockStart states
    (Fin.last (genuineEventCount states))).val ≤ eventCount at hStartLe
  omega

/-- Block-start values extended to all naturals by holding the final block start constant. -/
noncomputable def cappedGenuineStateBlockStartValue
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) (index : ℕ) : ℕ :=
  (genuineStateBlockStart states
    ⟨min index (genuineEventCount states),
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩).val

/-- The capped block-start sequence is monotone. -/
theorem monotone_cappedGenuineStateBlockStartValue
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    Monotone (cappedGenuineStateBlockStartValue states) := by
  intro first second hLe
  apply monotone_genuineStateBlockStart states
  change min first (genuineEventCount states) ≤
    min second (genuineEventCount states)
  exact min_le_min hLe le_rfl

/-- Successive maximal-block starts telescope from zero to the final block start. -/
theorem sum_genuineStateBlockStart_successiveDifference
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    (∑ block : Fin (genuineEventCount states),
      ((genuineStateBlockStart states
          (Fin.succ (block : Fin (genuineEventCount states)))).val -
        (genuineStateBlockStart states
          (Fin.castSucc (block : Fin (genuineEventCount states)))).val)) =
      (genuineStateBlockStart states
        (Fin.last (genuineEventCount states))).val := by
  have hTelescope := Finset.sum_range_tsub
    (monotone_cappedGenuineStateBlockStartValue states)
    (genuineEventCount states)
  calc
    (∑ block : Fin (genuineEventCount states),
        ((genuineStateBlockStart states block.succ).val -
          (genuineStateBlockStart states block.castSucc).val)) =
        ∑ index ∈ Finset.range (genuineEventCount states),
          (cappedGenuineStateBlockStartValue states (index + 1) -
            cappedGenuineStateBlockStartValue states index) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hIndex
      have hIndexLt : index < genuineEventCount states :=
        Finset.mem_range.mp hIndex
      rw [dite_eq_left hIndexLt]
      simp only [cappedGenuineStateBlockStartValue]
      have hSuccessor :
          (⟨min (index + 1) (genuineEventCount states),
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
              Fin (genuineEventCount states + 1)) =
            (⟨index, hIndexLt⟩ : Fin (genuineEventCount states)).succ := by
        apply Fin.ext
        simp [Nat.min_eq_left (Nat.succ_le_iff.mpr hIndexLt)]
      have hCurrent :
          (⟨min index (genuineEventCount states),
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
              Fin (genuineEventCount states + 1)) =
            (⟨index, hIndexLt⟩ : Fin (genuineEventCount states)).castSucc := by
        apply Fin.ext
        simp [Nat.min_eq_left hIndexLt.le]
      rw [hSuccessor, hCurrent]
    _ = cappedGenuineStateBlockStartValue states
          (genuineEventCount states) -
        cappedGenuineStateBlockStartValue states 0 := hTelescope
    _ = (genuineStateBlockStart states
          (Fin.last (genuineEventCount states))).val := by
      unfold cappedGenuineStateBlockStartValue
      simp only [Nat.min_self]
      apply congrArg Fin.val
      apply congrArg (genuineStateBlockStart states)
      apply Fin.ext
      simp

/-- The canonical maximal blocks partition all state positions exactly. -/
theorem sum_genuineStateBlockSelfEventCount_add_one
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    (∑ block : Fin (genuineEventCount states + 1),
      (genuineStateBlockSelfEventCount states block + 1)) = eventCount + 1 := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [genuineStateBlockSelfEventCount_castSucc_add_one]
  rw [sum_genuineStateBlockStart_successiveDifference,
    genuineStateBlockSelfEventCount_last_add_one]
  have hStartLe := genuineStateBlockStart_le_end states
    (Fin.last (genuineEventCount states))
  rw [genuineStateBlockEnd_last] at hStartLe
  change (genuineStateBlockStart states
    (Fin.last (genuineEventCount states))).val ≤ eventCount at hStartLe
  omega

/-- Canonical per-block self-event counts reproduce the original virtual event count exactly. -/
theorem selfEventInsertedEventCount_genuineStateBlockSelfEventCount
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    selfEventInsertedEventCount (genuineStateBlockSelfEventCount states) =
      eventCount := by
  have hExpanded :=
    sum_selfEventCounts_add_one (genuineStateBlockSelfEventCount states)
  have hPartition := sum_genuineStateBlockSelfEventCount_add_one states
  omega

/-- Reduced physical state word obtained by deleting every self-event from a virtual word. -/
noncomputable def genuineStateBlockValue
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    Fin (genuineEventCount states + 1) → State :=
  (deleteSelfEventsSlice states (fun _ ↦ 0)).states

/-- Consecutive canonical block values are distinct. -/
theorem genuineStateBlockValue_ne_succ
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states)) :
    genuineStateBlockValue states block.castSucc ≠
      genuineStateBlockValue states block.succ := by
  unfold genuineStateBlockValue
  rw [states_deleteSelfEventsSlice_castSucc,
    states_deleteSelfEventsSlice_succ]
  exact (Finset.mem_filter.mp (genuineEventIndex_mem states block)).2

/-- The reduced block value is the original value at the block's first position. -/
theorem genuineStateBlockValue_eq_state_start
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) :
    genuineStateBlockValue states block =
      states (genuineStateBlockStart states block) := by
  refine Fin.cases ?_ (fun previous ↦ ?_) block
  · rfl
  · unfold genuineStateBlockValue genuineStateBlockStart
    exact states_deleteSelfEventsSlice_succ states (fun _ ↦ 0) previous

/-- No event strictly inside one canonical block is a genuine state-changing event. -/
theorem eventIndex_not_mem_genuineEventIndices_of_mem_genuineStateBlock
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1))
    (eventIndex : Fin eventCount)
    (hStart : (genuineStateBlockStart states block).val ≤ eventIndex.val)
    (hEnd : eventIndex.val < (genuineStateBlockEnd states block).val) :
    eventIndex ∉ genuineEventIndices states := by
  intro hGenuine
  obtain ⟨selected, hSelected⟩ :=
    exists_genuineEventIndex_eq states hGenuine
  induction block using Fin.cases with
  | zero =>
      by_cases hCount : genuineEventCount states = 0
      · exact Fin.elim0 (hCount ▸ selected)
      · have hPositive : 0 < genuineEventCount states := Nat.pos_of_ne_zero hCount
        unfold genuineStateBlockEnd at hEnd
        simp +instances only [Fin.val_zero] at hEnd
        rw (transparency := .default) [dite_eq_left hPositive] at hEnd
        let first : Fin (genuineEventCount states) := ⟨0, hPositive⟩
        have hFirstLeSelected :
            genuineEventIndex states first ≤
              genuineEventIndex states selected :=
          ((genuineEventIndices states).orderEmbOfFin rfl).monotone
            (by change first.val ≤ selected.val; exact Nat.zero_le _)
        rw [hSelected] at hFirstLeSelected
        exact (not_lt_of_ge hFirstLeSelected) hEnd
  | succ previous =>
      have hPreviousBeforeSelected :
          genuineEventIndex states previous < genuineEventIndex states selected := by
        rw [hSelected]
        unfold genuineStateBlockStart at hStart
        change (genuineEventIndex states previous).val + 1 ≤ eventIndex.val at hStart
        exact hStart
      have hPreviousLtSelected : previous < selected :=
        (((genuineEventIndices states).orderEmbOfFin rfl).lt_iff_lt).mp
          hPreviousBeforeSelected
      by_cases hNext : previous.val + 1 < genuineEventCount states
      · let next : Fin (genuineEventCount states) := ⟨previous.val + 1, hNext⟩
        unfold genuineStateBlockEnd at hEnd
        simp only [Fin.val_succ] at hEnd
        rw [dite_eq_left hNext] at hEnd
        have hSelectedBeforeNext :
            genuineEventIndex states selected < genuineEventIndex states next := by
          rw [hSelected]
          exact hEnd
        have hSelectedLtNext : selected < next :=
          (((genuineEventIndices states).orderEmbOfFin rfl).lt_iff_lt).mp
            hSelectedBeforeNext
        change previous.val < selected.val at hPreviousLtSelected
        change selected.val < previous.val + 1 at hSelectedLtNext
        omega
      · change previous.val < selected.val at hPreviousLtSelected
        have hSelectedBound := selected.isLt
        omega

/-- Every state position in a canonical block has the block's reduced value. -/
theorem state_eq_genuineStateBlockValue_of_mem_block
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1))
    (position : Fin (eventCount + 1))
    (hStart : genuineStateBlockStart states block ≤ position)
    (hEnd : position ≤ genuineStateBlockEnd states block) :
    states position = genuineStateBlockValue states block := by
  rw [genuineStateBlockValue_eq_state_start]
  symm
  apply state_eq_of_no_change_between states hStart
  intro eventIndex hAfter hBefore
  have hNotGenuine :=
    eventIndex_not_mem_genuineEventIndices_of_mem_genuineStateBlock
      states block eventIndex hAfter
        (lt_of_lt_of_le hBefore hEnd)
  simpa [genuineEventIndices] using hNotGenuine

/-- The sizes of all blocks preceding a block sum to that block's canonical start position. -/
theorem sum_genuineStateBlockSelfEventCount_add_one_before
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1)) :
    (∑ previous : Fin block.val,
      (genuineStateBlockSelfEventCount states
          (Fin.castLE block.isLt.le previous) + 1)) =
      (genuineStateBlockStart states block).val := by
  have hTelescope := Finset.sum_range_tsub
    (monotone_cappedGenuineStateBlockStartValue states) block.val
  have hBlockLe : block.val ≤ genuineEventCount states := by
    omega
  calc
    (∑ previous : Fin block.val,
        (genuineStateBlockSelfEventCount states
            (Fin.castLE block.isLt.le previous) + 1)) =
        ∑ index ∈ Finset.range block.val,
          (cappedGenuineStateBlockStartValue states (index + 1) -
            cappedGenuineStateBlockStartValue states index) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hIndex
      have hIndexLtBlock : index < block.val := Finset.mem_range.mp hIndex
      rw [dite_eq_left hIndexLtBlock]
      have hIndexLtGenuine : index < genuineEventCount states :=
        lt_of_lt_of_le hIndexLtBlock hBlockLe
      let canonical : Fin (genuineEventCount states) :=
        ⟨index, hIndexLtGenuine⟩
      have hCast :
          Fin.castLE block.isLt.le ⟨index, hIndexLtBlock⟩ =
            canonical.castSucc := by
        apply Fin.ext
        rfl
      rw [hCast,
        genuineStateBlockSelfEventCount_castSucc_add_one states canonical]
      unfold cappedGenuineStateBlockStartValue
      have hSuccessor :
          (⟨min (index + 1) (genuineEventCount states),
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
              Fin (genuineEventCount states + 1)) = canonical.succ := by
        apply Fin.ext
        simp [canonical, Nat.min_eq_left (Nat.succ_le_iff.mpr hIndexLtGenuine)]
      have hCurrent :
          (⟨min index (genuineEventCount states),
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
              Fin (genuineEventCount states + 1)) = canonical.castSucc := by
        apply Fin.ext
        simp [canonical, Nat.min_eq_left hIndexLtGenuine.le]
      rw [hSuccessor, hCurrent]
    _ = cappedGenuineStateBlockStartValue states block.val -
        cappedGenuineStateBlockStartValue states 0 := hTelescope
    _ = (genuineStateBlockStart states block).val := by
      unfold cappedGenuineStateBlockStartValue
      have hBlock :
          (⟨min block.val (genuineEventCount states),
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
              Fin (genuineEventCount states + 1)) = block := by
        apply Fin.ext
        simp [Nat.min_eq_left hBlockLe]
      rw [hBlock]
      simp

/-- The insertion position of a decoded block offset is its block start plus that offset. -/
theorem selfEventInsertedStatePositionEquiv_genuineStateBlock_val
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (block : Fin (genuineEventCount states + 1))
    (offset : Fin (genuineStateBlockSelfEventCount states block + 1)) :
    (selfEventInsertedStatePositionEquiv
        (genuineStateBlockSelfEventCount states) ⟨block, offset⟩).val =
      (genuineStateBlockStart states block).val + offset.val := by
  unfold selfEventInsertedStatePositionEquiv
  simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  rw [sum_genuineStateBlockSelfEventCount_add_one_before]

/-- Expanding the canonical deletion decoder recovers every original state position. -/
theorem selfEventInsertedStateWord_genuineStateBlockValue_cast
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State)
    (position : Fin (eventCount + 1)) :
    selfEventInsertedStateWord (genuineStateBlockValue states)
        (genuineStateBlockSelfEventCount states)
        (Fin.cast
          (congrArg (· + 1)
            (selfEventInsertedEventCount_genuineStateBlockSelfEventCount states).symm)
          position) =
      states position := by
  let expandedPosition :
      Fin (selfEventInsertedEventCount
          (genuineStateBlockSelfEventCount states) + 1) :=
    Fin.cast
      (congrArg (· + 1)
        (selfEventInsertedEventCount_genuineStateBlockSelfEventCount states).symm)
      position
  let decoded :=
    (selfEventInsertedStatePositionEquiv
      (genuineStateBlockSelfEventCount states)).symm expandedPosition
  have hDecoded :
      selfEventInsertedStatePositionEquiv
          (genuineStateBlockSelfEventCount states) decoded = expandedPosition :=
    (selfEventInsertedStatePositionEquiv
      (genuineStateBlockSelfEventCount states)).apply_symm_apply expandedPosition
  change selfEventInsertedStateWord (genuineStateBlockValue states)
      (genuineStateBlockSelfEventCount states) expandedPosition = states position
  rw [← hDecoded,
    selfEventInsertedStateWord_apply_blockPosition]
  symm
  apply state_eq_genuineStateBlockValue_of_mem_block states decoded.1 position
  · change (genuineStateBlockStart states decoded.1).val ≤ position.val
    have hDecodedValue :=
      selfEventInsertedStatePositionEquiv_genuineStateBlock_val
        states decoded.1 decoded.2
    change (selfEventInsertedStatePositionEquiv
        (genuineStateBlockSelfEventCount states) decoded).val =
      (genuineStateBlockStart states decoded.1).val + decoded.2.val at hDecodedValue
    have hPositionValue :
        (selfEventInsertedStatePositionEquiv
          (genuineStateBlockSelfEventCount states) decoded).val = position.val := by
      rw [hDecoded]
      rfl
    omega
  · change position.val ≤ (genuineStateBlockEnd states decoded.1).val
    have hDecodedValue :=
      selfEventInsertedStatePositionEquiv_genuineStateBlock_val
        states decoded.1 decoded.2
    change (selfEventInsertedStatePositionEquiv
        (genuineStateBlockSelfEventCount states) decoded).val =
      (genuineStateBlockStart states decoded.1).val + decoded.2.val at hDecodedValue
    have hPositionValue :
        (selfEventInsertedStatePositionEquiv
          (genuineStateBlockSelfEventCount states) decoded).val = position.val := by
      rw [hDecoded]
      rfl
    have hBlockEnd :=
      genuineStateBlockStart_add_selfEventCount states decoded.1
    have hOffsetBound := decoded.2.isLt
    omega

/-- Casting a finite-word function between equal lengths acts by the inverse cast on positions. -/
theorem cast_fin_add_one_function_apply
    {firstCount secondCount : ℕ} (hCount : firstCount = secondCount)
    (word : Fin (firstCount + 1) → State) (position : Fin (secondCount + 1)) :
    cast (congrArg (fun count ↦ Fin (count + 1) → State) hCount) word position =
      word (Fin.cast (congrArg (· + 1) hCount.symm) position) := by
  subst secondCount
  rfl

/-- The canonical reduced word and its block counts encode the original dependent state word. -/
theorem selfEventInsertedStateWordCode_genuineStateBlockValue
    {eventCount : ℕ} [DecidableEq State]
    (states : Fin (eventCount + 1) → State) :
    selfEventInsertedStateWordCode (genuineStateBlockValue states)
        (genuineStateBlockSelfEventCount states) =
      ⟨eventCount, states⟩ := by
  let hEventCount :=
    selfEventInsertedEventCount_genuineStateBlockSelfEventCount states
  apply Sigma.ext hEventCount
  apply heq_of_cast_eq
    (congrArg (fun count ↦ Fin (count + 1) → State) hEventCount)
  funext position
  change cast (congrArg (fun count ↦ Fin (count + 1) → State) hEventCount)
      (selfEventInsertedStateWord (genuineStateBlockValue states)
        (genuineStateBlockSelfEventCount states)) position = states position
  rw [cast_fin_add_one_function_apply hEventCount]
  exact selfEventInsertedStateWord_genuineStateBlockValue_cast states position

/-- Every dependent finite state word has a canonical reduced-word/self-event-count preimage. -/
theorem surjective_reducedSelfEventInsertionWordCode [DecidableEq State] :
    Function.Surjective
      (reducedSelfEventInsertionWordCode (State := State)) := by
  rintro ⟨eventCount, states⟩
  refine ⟨⟨genuineEventCount states,
    ⟨⟨genuineStateBlockValue states, ?_⟩,
      genuineStateBlockSelfEventCount states⟩⟩, ?_⟩
  · intro block
    exact genuineStateBlockValue_ne_succ states block
  · exact selfEventInsertedStateWordCode_genuineStateBlockValue states

/-- The global reduced-word insertion code is a bijection onto all dependent finite state words. -/
theorem bijective_reducedSelfEventInsertionWordCode [DecidableEq State] :
    Function.Bijective
      (reducedSelfEventInsertionWordCode (State := State)) :=
  ⟨injective_reducedSelfEventInsertionWordCode,
    surjective_reducedSelfEventInsertionWordCode⟩

/-- Canonical equivalence between reduced words with self-event counts and arbitrary finite
words. -/
noncomputable def reducedSelfEventInsertionWordEquiv [DecidableEq State] :
    ReducedSelfEventInsertionWordCode State ≃
      (Σ eventCount : ℕ, Fin (eventCount + 1) → State) :=
  Equiv.ofBijective (reducedSelfEventInsertionWordCode (State := State))
    bijective_reducedSelfEventInsertionWordCode

end FiniteJumpHistory
