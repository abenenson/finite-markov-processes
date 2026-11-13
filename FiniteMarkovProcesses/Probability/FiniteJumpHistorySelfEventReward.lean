/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.CumulativeWaitTimes
public import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventDeletion

/-!
# Rewards under finite-history self-event deletion

This module proves that deleting repeated-state virtual events preserves state-occupation
rewards. The proof rewrites a complete dwell sum as a terminal reward plus a time-weighted sum of
adjacent reward differences; every deleted self-event then contributes zero.

## Main Results

- `FiniteJumpHistory.sum_dwellTimeVector_mul_stateReward_eq_terminal_add_jumpTimes`: discrete
  integration by parts for a finite timed state word.
- `FiniteJumpHistory.sum_dwellReward_deleteSelfEventsSlice`: exact occupation-reward invariance
  under canonical self-event deletion.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators

universe u

variable {State : Type u}

/-- A complete dwell reward is the terminal reward plus the time-weighted sum of adjacent reward
differences. -/
theorem FiniteJumpHistory.sum_dwellTimeVector_mul_stateReward_eq_terminal_add_jumpTimes
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (stateReward : State → ℝ) (T : ℝ) :
    (∑ index : Fin (n + 1),
      _root_.FiniteJumpHistory.dwellTimeVector T times index * stateReward (states index)) =
      T * stateReward (states (Fin.last n)) +
        ∑ index : Fin n, times index *
          (stateReward (states index.castSucc) - stateReward (states index.succ)) := by
  unfold _root_.FiniteJumpHistory.dwellTimeVector
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hSuccessor :
      (∑ index : Fin (n + 1),
          _root_.FiniteJumpHistory.boundaryTimeVector T times index.succ *
            stateReward (states index)) =
        (∑ index : Fin n, times index * stateReward (states index.castSucc)) +
          T * stateReward (states (Fin.last n)) := by
    rw [Fin.sum_univ_castSucc]
    simp_rw [FiniteJumpHistory.boundaryTimeVector_castSucc_succ]
    rw [FiniteJumpHistory.boundaryTimeVector_succ, Fin.lastCases_last]
  have hPredecessor :
      (∑ index : Fin (n + 1),
          _root_.FiniteJumpHistory.boundaryTimeVector T times index.castSucc *
            stateReward (states index)) =
        ∑ index : Fin n, times index * stateReward (states index.succ) := by
    rw [Fin.sum_univ_succ]
    rw [Fin.castSucc_zero, FiniteJumpHistory.boundaryTimeVector_zero,
      zero_mul, zero_add]
    simp_rw [← Fin.succ_castSucc]
    simp_rw [FiniteJumpHistory.boundaryTimeVector_castSucc_succ]
  rw [hSuccessor, hPredecessor]
  have hDifference :
      (∑ index : Fin n, times index *
        (stateReward (states index.castSucc) - stateReward (states index.succ))) =
        (∑ index : Fin n, times index * stateReward (states index.castSucc)) -
          ∑ index : Fin n, times index * stateReward (states index.succ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hDifference]
  ring

/-- Deleting virtual self-events preserves every complete state-occupation reward. -/
theorem FiniteJumpHistory.sum_dwellReward_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (stateReward : State → ℝ) (T : ℝ) :
    (∑ index : Fin ((_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).jumpCount + 1),
      _root_.FiniteJumpHistory.dwellTimeVector T
          (_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).jumpTimes index *
        stateReward
          ((_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).states index)) =
      ∑ index : Fin (n + 1),
        _root_.FiniteJumpHistory.dwellTimeVector T times index * stateReward (states index) := by
  rw [FiniteJumpHistory.sum_dwellTimeVector_mul_stateReward_eq_terminal_add_jumpTimes
    (_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).states
    (_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).jumpTimes]
  rw [FiniteJumpHistory.sum_dwellTimeVector_mul_stateReward_eq_terminal_add_jumpTimes
    states times]
  have hFinal := _root_.FiniteJumpHistory.finalState_deleteSelfEventsSlice states times
  change (_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).states
      (Fin.last (_root_.FiniteJumpHistory.deleteSelfEventsSlice states times).jumpCount) =
    states (Fin.last n) at hFinal
  rw [hFinal]
  rw [_root_.FiniteJumpHistory.sum_jumpTime_mul_stateRewardDifference_deleteSelfEventsSlice]

end FiniteMarkovProcesses.Probability
