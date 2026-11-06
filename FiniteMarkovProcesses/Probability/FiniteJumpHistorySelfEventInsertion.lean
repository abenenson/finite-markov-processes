/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Algebra.BigOperators.Fin
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventDeletion

/-!
# Canonical insertion of self-events into finite state words

A vector of nonnegative counts specifies how many virtual self-events occur in each physical
dwell. Expanding each physical state into a block of `count + 1` repeated state positions gives a
canonical virtual state word with the physical transitions retained between adjacent blocks.

This module fixes the finite-coordinate reindexing used by the uniformized deletion-law proof.
It contains no Markov rates or measures; those enter only after the combinatorial carrier is fixed.

## Main Results

- `selfEventInsertedEventCount`: total virtual event count after inserting all self-events.
- `selfEventInsertedStatePositionEquiv`: canonical block-position equivalence for the expanded
  state word.
- `selfEventInsertedStateWord`: expanded virtual state word.
- `selfEventInsertedStateWord_apply_blockPosition`: exact value throughout every repeated block.
- `selfEventInsertedPhysicalTransitionEventIndex`: canonical virtual-event index of each retained
  physical transition.
- `selfEventInsertedSelfEventIndex`: canonical virtual-event index of each inserted self-event.
- `selfEventInsertedEventIndex_cases`: every expanded virtual event is either one inserted
  self-event or one retained physical transition.
- `selfEventInsertedEventCoordinateEquiv`: canonical partition of every virtual event coordinate
  into one inserted self-event or retained physical transition.
- `selfEventInsertedJumpTimes`: canonical merge of insertion and physical jump-time coordinates.
- `deleteSelfEventsSlice_selfEventInsertedStateWord`: deletion recovers every reduced physical
  history when its retained transition times agree.
- `selfEventInsertedStateWord_zero`: preservation of the initial state.
- `selfEventInsertedStateWord_last`: preservation of the final state.
-/

open scoped BigOperators

universe u

namespace FiniteJumpHistory

variable {State : Type u}

/-- Total virtual event count after inserting the specified self-events into every physical
dwell. The original physical transitions contribute `physicalEventCount` further events. -/
def selfEventInsertedEventCount {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) : ℕ :=
  physicalEventCount + ∑ index, selfEventCounts index

/-- The number of expanded state positions is one more than the total virtual event count. -/
theorem sum_selfEventCounts_add_one {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    (∑ index, (selfEventCounts index + 1)) =
      selfEventInsertedEventCount selfEventCounts + 1 := by
  simp [selfEventInsertedEventCount, Finset.sum_add_distrib]
  omega

/-- Canonical equivalence between a physical dwell together with one position in its repeated
state block and a position in the complete expanded virtual state word. -/
def selfEventInsertedStatePositionEquiv {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    ((index : Fin (physicalEventCount + 1)) × Fin (selfEventCounts index + 1)) ≃
      Fin (selfEventInsertedEventCount selfEventCounts + 1) :=
  finSigmaFinEquiv.trans <| finCongr <| sum_selfEventCounts_add_one selfEventCounts

/-- The first position of the first repeated state block is the first virtual state position. -/
@[simp]
theorem selfEventInsertedStatePositionEquiv_first {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨0, 0⟩ = 0 := by
  apply Fin.ext
  simp [selfEventInsertedStatePositionEquiv, finSigmaFinEquiv_apply]

/-- The last position of the final repeated state block is the final virtual state position. -/
@[simp]
theorem selfEventInsertedStatePositionEquiv_last {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨Fin.last physicalEventCount,
          Fin.last (selfEventCounts (Fin.last physicalEventCount))⟩ =
      Fin.last (selfEventInsertedEventCount selfEventCounts) := by
  apply Fin.ext
  have hInitialBlocks :
      (∑ index : Fin physicalEventCount,
          selfEventCounts (Fin.castLE (Fin.last physicalEventCount).isLt.le index)) =
        ∑ index : Fin physicalEventCount, selfEventCounts index.castSucc := by
    apply Finset.sum_congr rfl
    intro index _
    apply congrArg selfEventCounts
    apply Fin.ext
    rfl
  change ((finSigmaFinEquiv.trans
      (finCongr (sum_selfEventCounts_add_one selfEventCounts)))
      ⟨Fin.last physicalEventCount,
        Fin.last (selfEventCounts (Fin.last physicalEventCount))⟩).val =
    selfEventInsertedEventCount selfEventCounts
  rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp only [Fin.val_last]
  rw [Finset.sum_add_distrib, hInitialBlocks]
  have hCard : (∑ _index : Fin physicalEventCount, (1 : ℕ)) = physicalEventCount := by
    simp
  rw [hCard]
  unfold selfEventInsertedEventCount
  rw [Fin.sum_univ_castSucc]
  omega

/-- Expanded virtual state word obtained by repeating each physical state once for its occupied
position and once more for every inserted self-event in that dwell. -/
def selfEventInsertedStateWord {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Fin (selfEventInsertedEventCount selfEventCounts + 1) → State :=
  fun position ↦
    states ((selfEventInsertedStatePositionEquiv selfEventCounts).symm position).1

/-- Every position in a repeated block carries exactly its corresponding physical state. -/
@[simp]
theorem selfEventInsertedStateWord_apply_blockPosition {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (position : Fin (selfEventCounts index + 1)) :
    selfEventInsertedStateWord states selfEventCounts
        (selfEventInsertedStatePositionEquiv selfEventCounts ⟨index, position⟩) =
      states index := by
  simp [selfEventInsertedStateWord]

/-- Within one repeated physical-state block, the canonical expanded position map is monotone. -/
theorem monotone_selfEventInsertedStatePositionEquiv_block {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1)) :
    Monotone fun position : Fin (selfEventCounts index + 1) ↦
      selfEventInsertedStatePositionEquiv selfEventCounts ⟨index, position⟩ := by
  intro first second hLe
  change (selfEventInsertedStatePositionEquiv selfEventCounts
      ⟨index, first⟩).val ≤
    (selfEventInsertedStatePositionEquiv selfEventCounts
      ⟨index, second⟩).val
  simp only [selfEventInsertedStatePositionEquiv, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  omega

/-- Positions within one repeated physical-state block occur in strict local order. -/
theorem strictMono_selfEventInsertedStatePositionEquiv_block {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1)) :
    StrictMono fun position : Fin (selfEventCounts index + 1) ↦
      selfEventInsertedStatePositionEquiv selfEventCounts ⟨index, position⟩ := by
  apply (monotone_selfEventInsertedStatePositionEquiv_block
    selfEventCounts index).strictMono_of_injective
  intro first second hEqual
  have hPair :=
    (selfEventInsertedStatePositionEquiv selfEventCounts).injective hEqual
  rw [Sigma.mk.inj_iff] at hPair
  exact eq_of_heq hPair.2

/-- Expanded state position that sources one retained physical transition. It is the final state
position in the corresponding nonterminal physical block. -/
def selfEventInsertedPhysicalTransitionStatePosition {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    Fin (selfEventInsertedEventCount selfEventCounts + 1) :=
  selfEventInsertedStatePositionEquiv selfEventCounts
    ⟨index.castSucc, Fin.last (selfEventCounts index.castSucc)⟩

/-- A retained physical-transition source position is never the final expanded state position. -/
theorem selfEventInsertedPhysicalTransitionStatePosition_ne_last
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    selfEventInsertedPhysicalTransitionStatePosition selfEventCounts index ≠
      Fin.last (selfEventInsertedEventCount selfEventCounts) := by
  rw [← selfEventInsertedStatePositionEquiv_last selfEventCounts]
  intro hEqual
  have hBlocks := congrArg Sigma.fst <|
    (selfEventInsertedStatePositionEquiv selfEventCounts).injective hEqual
  exact Fin.castSucc_ne_last index hBlocks

/-- Canonical virtual-event index of one retained physical transition in the expanded word. -/
def selfEventInsertedPhysicalTransitionEventIndex {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    Fin (selfEventInsertedEventCount selfEventCounts) :=
  (selfEventInsertedPhysicalTransitionStatePosition selfEventCounts index).castPred
    (selfEventInsertedPhysicalTransitionStatePosition_ne_last selfEventCounts index)

/-- Casting a retained physical-transition event back into the expanded state positions recovers
its defining source position. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_castSucc
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).castSucc =
      selfEventInsertedPhysicalTransitionStatePosition selfEventCounts index := by
  rw [selfEventInsertedPhysicalTransitionEventIndex, Fin.castSucc_castPred]

/-- Distinct physical transitions retain distinct virtual-event indices. -/
theorem injective_selfEventInsertedPhysicalTransitionEventIndex
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Function.Injective
      (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts) := by
  intro first second hEqual
  have hPositions := congrArg Fin.castSucc hEqual
  simp only [selfEventInsertedPhysicalTransitionEventIndex_castSucc,
    selfEventInsertedPhysicalTransitionStatePosition] at hPositions
  have hBlocks := congrArg Sigma.fst <|
    (selfEventInsertedStatePositionEquiv selfEventCounts).injective hPositions
  exact Fin.castSucc_injective _ hBlocks

/-- The state position following a retained physical-transition event is the first position in
the next repeated physical-state block. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_succ
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).succ =
      selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨index.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ := by
  apply Fin.ext
  simp only [selfEventInsertedPhysicalTransitionEventIndex,
    selfEventInsertedPhysicalTransitionStatePosition,
    selfEventInsertedStatePositionEquiv, Equiv.trans_apply, finCongr_apply,
    Fin.val_cast, finSigmaFinEquiv_apply, Fin.coe_castPred, Fin.val_succ]
  let blockSize : Fin (index.val + 1) → ℕ := fun localIndex ↦
    selfEventCounts (Fin.castLE index.succ.isLt.le localIndex) + 1
  have hBlocks := Fin.sum_univ_castSucc blockSize
  simpa only [blockSize, Fin.castLE, Fin.castSucc, Fin.castAdd, Fin.val_last,
    Nat.add_assoc, Nat.add_zero] using hBlocks.symm

/-- The first expanded state positions of successive physical dwell blocks occur in strict
chronological order. -/
theorem strictMono_selfEventInsertedStatePositionEquiv_blockFirst
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    StrictMono fun index : Fin (physicalEventCount + 1) ↦
      selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨index, (0 : Fin (selfEventCounts index + 1))⟩ := by
  apply Fin.strictMono_iff_lt_succ.2
  intro index
  have hWithin :=
    monotone_selfEventInsertedStatePositionEquiv_block
      selfEventCounts index.castSucc
      (Fin.zero_le (Fin.last (selfEventCounts index.castSucc)))
  calc
    selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨index.castSucc, (0 : Fin (selfEventCounts index.castSucc + 1))⟩ ≤
        selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨index.castSucc, Fin.last (selfEventCounts index.castSucc)⟩ := hWithin
    _ = (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).castSucc := by
      rw [selfEventInsertedPhysicalTransitionEventIndex_castSucc]
      rfl
    _ < (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).succ :=
      Fin.castSucc_lt_succ
    _ = selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨index.succ, (0 : Fin (selfEventCounts index.succ + 1))⟩ :=
      selfEventInsertedPhysicalTransitionEventIndex_succ selfEventCounts index

/-- Every expanded position in an earlier physical dwell block precedes every position in a
later physical dwell block. -/
theorem selfEventInsertedStatePositionEquiv_lt_of_block_lt
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    {firstBlock secondBlock : Fin (physicalEventCount + 1)}
    (hBlock : firstBlock < secondBlock)
    (firstPosition : Fin (selfEventCounts firstBlock + 1))
    (secondPosition : Fin (selfEventCounts secondBlock + 1)) :
    selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨firstBlock, firstPosition⟩ <
      selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨secondBlock, secondPosition⟩ := by
  have hFirstNotLast : firstBlock ≠ Fin.last physicalEventCount := by
    exact ne_of_lt (hBlock.trans_le (Fin.le_last secondBlock))
  let transitionIndex : Fin physicalEventCount :=
    firstBlock.castPred hFirstNotLast
  have hTransitionBlock : transitionIndex.castSucc = firstBlock :=
    Fin.castSucc_castPred firstBlock hFirstNotLast
  have hNextBlock : transitionIndex.succ ≤ secondBlock := by
    change transitionIndex.val + 1 ≤ secondBlock.val
    rw [show transitionIndex.val = firstBlock.val by
      exact congrArg Fin.val hTransitionBlock]
    exact hBlock
  have hWithinFirst :=
    monotone_selfEventInsertedStatePositionEquiv_block
      selfEventCounts firstBlock (Fin.le_last firstPosition)
  have hWithinSecond :=
    monotone_selfEventInsertedStatePositionEquiv_block
      selfEventCounts secondBlock (Fin.zero_le secondPosition)
  have hFirstBlocks :=
    (strictMono_selfEventInsertedStatePositionEquiv_blockFirst selfEventCounts).monotone
      hNextBlock
  calc
    selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨firstBlock, firstPosition⟩ ≤
        selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨firstBlock, Fin.last (selfEventCounts firstBlock)⟩ := hWithinFirst
    _ = (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts transitionIndex).castSucc := by
      rw [selfEventInsertedPhysicalTransitionEventIndex_castSucc]
      unfold selfEventInsertedPhysicalTransitionStatePosition
      rw [hTransitionBlock]
    _ < (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts transitionIndex).succ := Fin.castSucc_lt_succ
    _ = selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨transitionIndex.succ,
            (0 : Fin (selfEventCounts transitionIndex.succ + 1))⟩ :=
      selfEventInsertedPhysicalTransitionEventIndex_succ
        selfEventCounts transitionIndex
    _ ≤ selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨secondBlock, (0 : Fin (selfEventCounts secondBlock + 1))⟩ := hFirstBlocks
    _ ≤ selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨secondBlock, secondPosition⟩ := hWithinSecond

/-- Retained physical transitions occur in their original strict chronological order in the
expanded virtual word. -/
theorem strictMono_selfEventInsertedPhysicalTransitionEventIndex
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    StrictMono (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts) := by
  cases physicalEventCount with
  | zero =>
      intro first
      exact Fin.elim0 first
  | succ physicalEventCount =>
      apply Fin.strictMono_iff_lt_succ.2
      intro index
      let nextBlock : Fin (physicalEventCount + 2) := index.succ.castSucc
      have hWithin :=
        monotone_selfEventInsertedStatePositionEquiv_block selfEventCounts nextBlock
          (a := (0 : Fin (selfEventCounts nextBlock + 1)))
          (b := Fin.last (selfEventCounts nextBlock)) (Fin.zero_le _)
      change selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨nextBlock, 0⟩ ≤
        selfEventInsertedStatePositionEquiv selfEventCounts
          ⟨nextBlock, Fin.last (selfEventCounts nextBlock)⟩ at hWithin
      have hNextBlock : index.castSucc.succ = nextBlock := by
        apply Fin.ext
        rfl
      have hFirst :=
        selfEventInsertedPhysicalTransitionEventIndex_succ
          selfEventCounts index.castSucc
      rw [hNextBlock] at hFirst
      have hFirst' :
          (selfEventInsertedPhysicalTransitionEventIndex
            selfEventCounts index.castSucc).succ =
            selfEventInsertedStatePositionEquiv selfEventCounts
              ⟨nextBlock, (0 : Fin (selfEventCounts nextBlock + 1))⟩ := by
        simpa using hFirst
      have hLast :=
        selfEventInsertedPhysicalTransitionEventIndex_castSucc
          selfEventCounts index.succ
      unfold selfEventInsertedPhysicalTransitionStatePosition at hLast
      change index.succ.castSucc = nextBlock at hNextBlock
      rw [hNextBlock] at hLast
      rw [← hFirst', ← hLast] at hWithin
      change (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index.castSucc).val + 1 ≤
        (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index.succ).val at hWithin
      omega

/-- The expanded-word source of a retained physical transition is its original physical source
state. -/
@[simp]
theorem selfEventInsertedStateWord_physicalTransitionEventIndex_castSucc
    {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    selfEventInsertedStateWord states selfEventCounts
        (selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).castSucc =
      states index.castSucc := by
  rw [selfEventInsertedPhysicalTransitionEventIndex_castSucc]
  exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _

/-- The expanded-word target of a retained physical transition is its original physical target
state. -/
@[simp]
theorem selfEventInsertedStateWord_physicalTransitionEventIndex_succ
    {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin physicalEventCount) :
    selfEventInsertedStateWord states selfEventCounts
        (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index).succ =
      states index.succ := by
  rw [selfEventInsertedPhysicalTransitionEventIndex_succ]
  exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _

/-- Expanded state position that sources one inserted self-event. -/
def selfEventInsertedSelfEventStatePosition {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    Fin (selfEventInsertedEventCount selfEventCounts + 1) :=
  selfEventInsertedStatePositionEquiv selfEventCounts
    ⟨index, selfEventIndex.castSucc⟩

/-- An inserted self-event source position is never the final expanded state position. -/
theorem selfEventInsertedSelfEventStatePosition_ne_last {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    selfEventInsertedSelfEventStatePosition selfEventCounts index selfEventIndex ≠
      Fin.last (selfEventInsertedEventCount selfEventCounts) := by
  rw [← selfEventInsertedStatePositionEquiv_last selfEventCounts]
  intro hEqual
  have hPairs :=
    (selfEventInsertedStatePositionEquiv selfEventCounts).injective hEqual
  simp only [Sigma.mk.inj_iff] at hPairs
  obtain ⟨rfl, hPosition⟩ := hPairs
  rw [heq_eq_eq] at hPosition
  exact Fin.castSucc_ne_last selfEventIndex hPosition

/-- Canonical virtual-event index of one inserted self-event. -/
def selfEventInsertedSelfEventIndex {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    Fin (selfEventInsertedEventCount selfEventCounts) :=
  (selfEventInsertedSelfEventStatePosition
    selfEventCounts index selfEventIndex).castPred
      (selfEventInsertedSelfEventStatePosition_ne_last
        selfEventCounts index selfEventIndex)

/-- Casting an inserted self-event back into the expanded state positions recovers its defining
source position. -/
@[simp]
theorem selfEventInsertedSelfEventIndex_castSucc {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    (selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex).castSucc =
      selfEventInsertedSelfEventStatePosition selfEventCounts index selfEventIndex := by
  rw [selfEventInsertedSelfEventIndex, Fin.castSucc_castPred]

/-- The position following an inserted self-event is the next position in the same repeated
physical-state block. -/
theorem selfEventInsertedSelfEventIndex_succ {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    (selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex).succ =
      selfEventInsertedStatePositionEquiv selfEventCounts
        ⟨index, selfEventIndex.succ⟩ := by
  apply Fin.ext
  simp [selfEventInsertedSelfEventIndex, selfEventInsertedSelfEventStatePosition,
    selfEventInsertedStatePositionEquiv, finSigmaFinEquiv_apply]
  omega

/-- Both endpoints of an inserted self-event carry the same physical state. -/
theorem selfEventInsertedStateWord_selfEventIndex_endpoints
    {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    selfEventInsertedStateWord states selfEventCounts
        (selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex).castSucc =
        states index ∧
      selfEventInsertedStateWord states selfEventCounts
        (selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex).succ =
        states index := by
  constructor
  · rw [selfEventInsertedSelfEventIndex_castSucc]
    exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _
  · rw [selfEventInsertedSelfEventIndex_succ]
    exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _

/-- Every event in the expanded virtual word is either one inserted self-event or one retained
physical transition. -/
theorem selfEventInsertedEventIndex_cases {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (eventIndex : Fin (selfEventInsertedEventCount selfEventCounts)) :
    (∃ (index : Fin (physicalEventCount + 1))
        (selfEventIndex : Fin (selfEventCounts index)),
        eventIndex = selfEventInsertedSelfEventIndex
          selfEventCounts index selfEventIndex) ∨
      ∃ index : Fin physicalEventCount,
        eventIndex = selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index := by
  let blockPosition :=
    (selfEventInsertedStatePositionEquiv selfEventCounts).symm eventIndex.castSucc
  have hBlockPosition :
      selfEventInsertedStatePositionEquiv selfEventCounts blockPosition =
        eventIndex.castSucc :=
    (selfEventInsertedStatePositionEquiv selfEventCounts).apply_symm_apply _
  rcases blockPosition with ⟨index, position⟩
  by_cases hSelfEvent : position.val < selfEventCounts index
  · left
    let selfEventIndex : Fin (selfEventCounts index) := ⟨position.val, hSelfEvent⟩
    refine ⟨index, selfEventIndex, ?_⟩
    apply Fin.castSucc_injective
    rw [selfEventInsertedSelfEventIndex, Fin.castSucc_castPred]
    unfold selfEventInsertedSelfEventStatePosition
    have hPosition : selfEventIndex.castSucc = position := by
      apply Fin.ext
      rfl
    rw [hPosition]
    exact hBlockPosition.symm
  · right
    have hPositionLast : position = Fin.last (selfEventCounts index) := by
      apply Fin.ext
      change position.val = selfEventCounts index
      omega
    have hIndexNotLast : index ≠ Fin.last physicalEventCount := by
      intro hIndexLast
      subst index
      apply Fin.castSucc_ne_last eventIndex
      rw [show eventIndex.castSucc =
          selfEventInsertedStatePositionEquiv selfEventCounts
            ⟨Fin.last physicalEventCount,
              Fin.last (selfEventCounts (Fin.last physicalEventCount))⟩ by
        rw [← hPositionLast]
        exact hBlockPosition.symm]
      exact selfEventInsertedStatePositionEquiv_last selfEventCounts
    let physicalIndex : Fin physicalEventCount := index.castPred hIndexNotLast
    refine ⟨physicalIndex, ?_⟩
    apply Fin.castSucc_injective
    rw [selfEventInsertedPhysicalTransitionEventIndex, Fin.castSucc_castPred]
    unfold selfEventInsertedPhysicalTransitionStatePosition
    have hIndex : physicalIndex.castSucc = index := by
      exact Fin.castSucc_castPred index hIndexNotLast
    rw [hIndex]
    simpa only [hPositionLast] using hBlockPosition.symm

/-- Coordinate type for one inserted self-event, recording its physical dwell and its local
index within that dwell. -/
abbrev SelfEventInsertionCoordinate {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :=
  (index : Fin (physicalEventCount + 1)) × Fin (selfEventCounts index)

/-- Send either an inserted self-event coordinate or a retained physical transition to its
canonical virtual-event index. -/
def selfEventInsertedEventCoordinate {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount →
      Fin (selfEventInsertedEventCount selfEventCounts)
  | Sum.inl ⟨index, selfEventIndex⟩ =>
      selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex
  | Sum.inr index =>
      selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index

/-- The inserted/retained event-coordinate map is injective. -/
theorem injective_selfEventInsertedEventCoordinate {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Function.Injective (selfEventInsertedEventCoordinate selfEventCounts) := by
  intro first second hEqual
  rcases first with first | first
  · rcases first with ⟨firstBlock, firstIndex⟩
    rcases second with second | second
    · rcases second with ⟨secondBlock, secondIndex⟩
      have hPosition := congrArg Fin.castSucc hEqual
      simp only [selfEventInsertedEventCoordinate,
        selfEventInsertedSelfEventIndex_castSucc] at hPosition
      unfold selfEventInsertedSelfEventStatePosition at hPosition
      have hPair :=
        (selfEventInsertedStatePositionEquiv selfEventCounts).injective hPosition
      have hBlock : firstBlock = secondBlock := congrArg Sigma.fst hPair
      subst secondBlock
      have hIndex : firstIndex.castSucc = secondIndex.castSucc := by
        rw [Sigma.mk.inj_iff] at hPair
        exact eq_of_heq hPair.2
      have hIndex' : firstIndex = secondIndex := Fin.castSucc_injective _ hIndex
      subst secondIndex
      rfl
    · exfalso
      have hPosition := congrArg Fin.castSucc hEqual
      simp only [selfEventInsertedEventCoordinate,
        selfEventInsertedSelfEventIndex_castSucc,
        selfEventInsertedPhysicalTransitionEventIndex_castSucc] at hPosition
      unfold selfEventInsertedSelfEventStatePosition
        selfEventInsertedPhysicalTransitionStatePosition at hPosition
      have hPair :=
        (selfEventInsertedStatePositionEquiv selfEventCounts).injective hPosition
      have hBlock : firstBlock = second.castSucc := congrArg Sigma.fst hPair
      subst firstBlock
      have hLocalValue := congrArg (fun pair ↦ pair.2.val) hPair
      change firstIndex.val = selfEventCounts second.castSucc at hLocalValue
      exact (Nat.ne_of_lt firstIndex.isLt) hLocalValue
  · rcases second with second | second
    · rcases second with ⟨secondBlock, secondIndex⟩
      exfalso
      have hPosition := congrArg Fin.castSucc hEqual
      simp only [selfEventInsertedEventCoordinate,
        selfEventInsertedSelfEventIndex_castSucc,
        selfEventInsertedPhysicalTransitionEventIndex_castSucc] at hPosition
      unfold selfEventInsertedSelfEventStatePosition
        selfEventInsertedPhysicalTransitionStatePosition at hPosition
      have hPair :=
        (selfEventInsertedStatePositionEquiv selfEventCounts).injective hPosition
      have hBlock : first.castSucc = secondBlock := congrArg Sigma.fst hPair
      subst secondBlock
      have hLocalValue := congrArg (fun pair ↦ pair.2.val) hPair
      change selfEventCounts first.castSucc = secondIndex.val at hLocalValue
      exact (Nat.ne_of_lt secondIndex.isLt) hLocalValue.symm
    · exact congrArg Sum.inr <|
        injective_selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts hEqual

/-- Every virtual-event index is represented by one inserted or retained coordinate. -/
theorem surjective_selfEventInsertedEventCoordinate {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Function.Surjective (selfEventInsertedEventCoordinate selfEventCounts) := by
  intro eventIndex
  rcases selfEventInsertedEventIndex_cases selfEventCounts eventIndex with
    ⟨index, selfEventIndex, hEqual⟩ | ⟨index, hEqual⟩
  · exact ⟨Sum.inl ⟨index, selfEventIndex⟩, hEqual.symm⟩
  · exact ⟨Sum.inr index, hEqual.symm⟩

/-- Canonical equivalence partitioning virtual-event indices into inserted self-events and
retained physical transitions. -/
noncomputable def selfEventInsertedEventCoordinateEquiv {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    (SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount) ≃
      Fin (selfEventInsertedEventCount selfEventCounts) :=
  Equiv.ofBijective (selfEventInsertedEventCoordinate selfEventCounts)
    ⟨injective_selfEventInsertedEventCoordinate selfEventCounts,
      surjective_selfEventInsertedEventCoordinate selfEventCounts⟩

/-- Merge the ordered self-event times in each physical dwell with the retained physical jump
times into their canonical virtual-event order. -/
noncomputable def selfEventInsertedJumpTimes {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    Fin (selfEventInsertedEventCount selfEventCounts) → ℝ :=
  fun eventIndex ↦
    match (selfEventInsertedEventCoordinateEquiv selfEventCounts).symm eventIndex with
    | Sum.inl ⟨index, selfEventIndex⟩ => insertionTimes index selfEventIndex
    | Sum.inr index => physicalTimes index

/-- The merged jump-time vector evaluates to the specified insertion time at every inserted
self-event coordinate. -/
@[simp]
theorem selfEventInsertedJumpTimes_selfEventIndex {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex) =
      insertionTimes index selfEventIndex := by
  rw [show selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex =
      selfEventInsertedEventCoordinateEquiv selfEventCounts
        (Sum.inl ⟨index, selfEventIndex⟩) by rfl]
  simp [selfEventInsertedJumpTimes]

/-- The merged jump-time vector evaluates to the original physical jump time at every retained
transition coordinate. -/
@[simp]
theorem selfEventInsertedJumpTimes_physicalTransitionEventIndex
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (index : Fin physicalEventCount) :
    selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index) =
      physicalTimes index := by
  rw [show selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index =
      selfEventInsertedEventCoordinateEquiv selfEventCounts (Sum.inr index) by rfl]
  simp [selfEventInsertedJumpTimes]

/-- Every inserted self-event is excluded from the genuine-event set of the expanded word. -/
theorem selfEventInsertedSelfEventIndex_not_mem_genuineEventIndices
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (index : Fin (physicalEventCount + 1))
    (selfEventIndex : Fin (selfEventCounts index)) :
    selfEventInsertedSelfEventIndex selfEventCounts index selfEventIndex ∉
      genuineEventIndices (selfEventInsertedStateWord states selfEventCounts) := by
  rw [genuineEventIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [(selfEventInsertedStateWord_selfEventIndex_endpoints
    states selfEventCounts index selfEventIndex).1,
    (selfEventInsertedStateWord_selfEventIndex_endpoints
      states selfEventCounts index selfEventIndex).2]
  exact not_ne_iff.mpr rfl

/-- Under a reduced physical state word, every retained physical transition belongs to the
genuine-event set of the expanded word. -/
theorem selfEventInsertedPhysicalTransitionEventIndex_mem_genuineEventIndices
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (index : Fin physicalEventCount) :
    selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index ∈
      genuineEventIndices (selfEventInsertedStateWord states selfEventCounts) := by
  rw [genuineEventIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and,
    selfEventInsertedStateWord_physicalTransitionEventIndex_castSucc,
    selfEventInsertedStateWord_physicalTransitionEventIndex_succ]
  exact hReduced index

/-- Under a reduced physical state word, the genuine expanded events are exactly the retained
physical-transition indices. -/
theorem mem_genuineEventIndices_selfEventInsertedStateWord_iff
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (eventIndex : Fin (selfEventInsertedEventCount selfEventCounts)) :
    eventIndex ∈ genuineEventIndices (selfEventInsertedStateWord states selfEventCounts) ↔
      ∃ index : Fin physicalEventCount,
        eventIndex = selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index := by
  constructor
  · intro hGenuine
    rcases selfEventInsertedEventIndex_cases selfEventCounts eventIndex with
      ⟨index, selfEventIndex, hEqual⟩ | ⟨index, hEqual⟩
    · subst eventIndex
      exact False.elim <|
        selfEventInsertedSelfEventIndex_not_mem_genuineEventIndices
          states selfEventCounts index selfEventIndex hGenuine
    · exact ⟨index, hEqual⟩
  · rintro ⟨index, rfl⟩
    exact selfEventInsertedPhysicalTransitionEventIndex_mem_genuineEventIndices
      states selfEventCounts hReduced index

/-- Under a reduced physical state word, the genuine-event finset of the expanded word is the
image of the original physical transition indices. -/
theorem genuineEventIndices_selfEventInsertedStateWord
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    genuineEventIndices (selfEventInsertedStateWord states selfEventCounts) =
      Finset.univ.image
        (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts) := by
  ext eventIndex
  rw [mem_genuineEventIndices_selfEventInsertedStateWord_iff
    states selfEventCounts hReduced]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, hEqual⟩
    exact ⟨index, hEqual.symm⟩
  · rintro ⟨index, hEqual⟩
    exact ⟨index, hEqual.symm⟩

/-- Inserting arbitrary self-event counts into a reduced physical word preserves the number of
genuine transitions exactly. -/
theorem genuineEventCount_selfEventInsertedStateWord
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    genuineEventCount (selfEventInsertedStateWord states selfEventCounts) =
      physicalEventCount := by
  unfold genuineEventCount
  rw [genuineEventIndices_selfEventInsertedStateWord states selfEventCounts hReduced]
  rw [Finset.card_image_of_injective _
    (injective_selfEventInsertedPhysicalTransitionEventIndex selfEventCounts)]
  simp

/-- The canonical increasing enumeration of genuine expanded events is exactly the retained
physical-transition index map, with only the unavoidable cardinality transport exposed. -/
theorem genuineEventIndex_selfEventInsertedStateWord
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (index : Fin physicalEventCount) :
    genuineEventIndex (selfEventInsertedStateWord states selfEventCounts)
        (Fin.cast
          (genuineEventCount_selfEventInsertedStateWord
            states selfEventCounts hReduced).symm index) =
      selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index := by
  unfold genuineEventIndex
  let expandedStates := selfEventInsertedStateWord states selfEventCounts
  have hCard :
      (genuineEventIndices expandedStates).card = physicalEventCount := by
    exact genuineEventCount_selfEventInsertedStateWord states selfEventCounts hReduced
  have hMembership (physicalIndex : Fin physicalEventCount) :
      selfEventInsertedPhysicalTransitionEventIndex selfEventCounts physicalIndex ∈
        genuineEventIndices expandedStates :=
    selfEventInsertedPhysicalTransitionEventIndex_mem_genuineEventIndices
      states selfEventCounts hReduced physicalIndex
  have hUnique :=
    Finset.orderEmbOfFin_unique hCard hMembership
      (strictMono_selfEventInsertedPhysicalTransitionEventIndex selfEventCounts)
  rw [hUnique]
  apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
  rfl

/-- Deleting the canonical self-event expansion recovers the reduced physical history whenever
the retained transition times agree with the physical jump times. -/
theorem deleteSelfEventsSlice_selfEventInsertedStateWord
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (virtualTimes : Fin (selfEventInsertedEventCount selfEventCounts) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (hPhysicalTimes : ∀ index : Fin physicalEventCount,
      virtualTimes
          (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index) =
        physicalTimes index) :
    deleteSelfEventsSlice
        (selfEventInsertedStateWord states selfEventCounts) virtualTimes =
      embedJumpTimes physicalEventCount states physicalTimes := by
  have hCount := genuineEventCount_selfEventInsertedStateWord
    states selfEventCounts hReduced
  calc
    deleteSelfEventsSlice
        (selfEventInsertedStateWord states selfEventCounts) virtualTimes =
        embedJumpTimesOfCountEq hCount.symm states physicalTimes := by
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · funext position
          refine Fin.cases ?_ (fun index ↦ ?_) position
          · change selfEventInsertedStateWord states selfEventCounts 0 =
              states (Fin.cast (congrArg (· + 1) hCount) 0)
            rw [← selfEventInsertedStatePositionEquiv_first selfEventCounts,
              selfEventInsertedStateWord_apply_blockPosition]
            apply congrArg states
            apply Fin.ext
            rfl
          · let physicalIndex : Fin physicalEventCount := Fin.cast hCount index
            have hRoundTrip : Fin.cast hCount.symm physicalIndex = index := by
              apply Fin.ext
              rfl
            have hGenuine := genuineEventIndex_selfEventInsertedStateWord
              states selfEventCounts hReduced physicalIndex
            change selfEventInsertedStateWord states selfEventCounts
                (genuineEventIndex
                  (selfEventInsertedStateWord states selfEventCounts) index).succ =
              states (Fin.cast (congrArg (· + 1) hCount) index.succ)
            rw [← hRoundTrip, hGenuine]
            rw [selfEventInsertedStateWord_physicalTransitionEventIndex_succ]
            apply congrArg states
            apply Fin.ext
            rfl
        · funext index
          let physicalIndex : Fin physicalEventCount := Fin.cast hCount index
          have hRoundTrip : Fin.cast hCount.symm physicalIndex = index := by
            apply Fin.ext
            rfl
          have hGenuine := genuineEventIndex_selfEventInsertedStateWord
            states selfEventCounts hReduced physicalIndex
          change virtualTimes
              (genuineEventIndex
                (selfEventInsertedStateWord states selfEventCounts) index) =
            physicalTimes (Fin.cast hCount index)
          rw [← hRoundTrip, hGenuine]
          simpa [physicalIndex] using hPhysicalTimes physicalIndex
    _ = embedJumpTimes physicalEventCount states physicalTimes :=
      embedJumpTimesOfCountEq_eq hCount.symm states physicalTimes

/-- Deleting a canonically merged insertion-time vector recovers the exact reduced physical
history, independently of all inserted self-event times. -/
theorem deleteSelfEventsSlice_selfEventInsertedStateWord_selfEventInsertedJumpTimes
    [DecidableEq State] {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    deleteSelfEventsSlice (selfEventInsertedStateWord states selfEventCounts)
        (selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes) =
      embedJumpTimes physicalEventCount states physicalTimes := by
  apply deleteSelfEventsSlice_selfEventInsertedStateWord
    states selfEventCounts hReduced
  exact selfEventInsertedJumpTimes_physicalTransitionEventIndex
    selfEventCounts insertionTimes physicalTimes

/-- Self-event insertion preserves the initial state of the physical word. -/
@[simp]
theorem selfEventInsertedStateWord_zero {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    selfEventInsertedStateWord states selfEventCounts 0 = states 0 := by
  rw [← selfEventInsertedStatePositionEquiv_first selfEventCounts]
  exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _

/-- Self-event insertion preserves the final state of the physical word. -/
@[simp]
theorem selfEventInsertedStateWord_last {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    selfEventInsertedStateWord states selfEventCounts
        (Fin.last (selfEventInsertedEventCount selfEventCounts)) =
      states (Fin.last physicalEventCount) := by
  rw [← selfEventInsertedStatePositionEquiv_last selfEventCounts]
  exact selfEventInsertedStateWord_apply_blockPosition states selfEventCounts _ _

end FiniteJumpHistory
