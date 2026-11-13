/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Tactic.NormNum
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryCadlag

/-!
# A one-jump observation with distinct endpoints

The observed real state changes from zero to one at time one half. The value at
the jump is one, the left limit is zero, and the terminal value stays one.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Examples

open FiniteJumpHistory

/-- A history that jumps from zero to one at time one half. -/
noncomputable def oneJumpHistory : FiniteJumpHistory ℝ :=
  ⟨1, (fun index ↦ (index.val : ℝ)), fun _ ↦ 1 / 2⟩

/-- The public occupied-state observation is càdlàg. -/
theorem oneJumpHistory_isCadlag : IsCadlag oneJumpHistory.stateAtTime :=
  oneJumpHistory.isCadlag_stateAtTime

/-- Initial and terminal states differ: the observation does not reset. -/
theorem oneJumpHistory_endpoints :
    oneJumpHistory.stateAtTime 0 = 0 ∧ oneJumpHistory.stateAtTime 1 = 1 := by
  classical
  dsimp only [stateAtTime, FiniteJumpHistory.states, FiniteJumpHistory.jumpTimes,
    FiniteJumpHistory.jumpCount, oneJumpHistory]
  norm_num [stateAtTimeVector, stateIndexAtTimeVector, eventCountAtOrBeforeTimeVector]

/-- All events at the observation time are included, while its left limit
excludes them. -/
theorem oneJumpHistory_jump_convention :
    oneJumpHistory.stateAtTime (1 / 2) = 1 ∧
      stateBeforeTimeVector oneJumpHistory.states oneJumpHistory.jumpTimes (1 / 2) = 0 := by
  classical
  dsimp only [stateAtTime, FiniteJumpHistory.states, FiniteJumpHistory.jumpTimes,
    FiniteJumpHistory.jumpCount, oneJumpHistory]
  norm_num [stateAtTimeVector, stateIndexAtTimeVector,
    stateBeforeTimeVector, stateIndexBeforeTimeVector, eventCountAtOrBeforeTimeVector,
    eventCountBeforeTimeVector]

/-- The zero-event slice has a constant observation on the entire real clock. -/
theorem noJumpHistory_observation (state time : ℝ) :
    (noJumpHistory state).stateAtTime time = state := by
  simp [noJumpHistory, stateAtTime, stateAtTimeVector, stateIndexAtTimeVector,
    eventCountAtOrBeforeTimeVector, FiniteJumpHistory.states, FiniteJumpHistory.jumpTimes,
    embedJumpTimes]

/-- Two events at the same time advance both count slots together. -/
theorem simultaneous_events_observation :
    stateAtTimeVector (fun index : Fin 3 ↦ (index.val : ℝ))
        (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) (1 / 2) = 2 ∧
      stateBeforeTimeVector (fun index : Fin 3 ↦ (index.val : ℝ))
        (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) (1 / 2) = 0 := by
  norm_num [stateAtTimeVector, stateIndexAtTimeVector, stateBeforeTimeVector,
    stateIndexBeforeTimeVector, eventCountAtOrBeforeTimeVector, eventCountBeforeTimeVector,
    Fin.sum_univ_succ]

/-- On a raw unordered vector the public selector still counts elapsed times;
the first elapsed event selects state-word index one. -/
theorem unordered_events_observation :
    stateAtTimeVector (fun index : Fin 3 ↦ (index.val : ℝ))
      (fun index : Fin 2 ↦ if index = 0 then (3 / 4 : ℝ) else 1 / 4) (1 / 2) = 1 := by
  simp only [stateAtTimeVector, stateIndexAtTimeVector, eventCountAtOrBeforeTimeVector,
    Fin.sum_univ_two]
  norm_num

end FiniteMarkovProcesses.Examples
