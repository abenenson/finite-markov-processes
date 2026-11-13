/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Topology.Order.Cadlag
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation

/-!
# Càdlàg observations of finite jump histories

The existing at-or-before state selector is a càdlàg function on the real clock.
Its left limit is the strict-before selector. Finiteness of the event coordinates
is enough: neither ordering nor distinctness of their times is required.

These statements use Mathlib's `IsCadlag` predicate and any topology on the state
space. They introduce no topology on a space of paths. The state after the last
event remains the final state; no terminal reset is added.
-/

@[expose] public section

open Filter Topology

namespace FiniteJumpHistory

universe u

variable {State : Type u} {eventCount : ℕ}

/-- A finite history's state selector is constant on a sufficiently short right
neighborhood of each time, with the value after events occurring at that time. -/
theorem stateAtTimeVector_eventuallyEq_right
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) (time : ℝ) :
    (fun observed ↦ stateAtTimeVector states times observed) =ᶠ[𝓝[>] time]
      fun _ ↦ stateAtTimeVector states times time := by
  have hCoordinates : ∀ index : Fin eventCount,
      ∀ᶠ observed in 𝓝[>] time, (times index ≤ observed ↔ times index ≤ time) := by
    intro index
    by_cases hBefore : times index ≤ time
    · filter_upwards [self_mem_nhdsWithin] with observed hObserved
      exact iff_of_true (hBefore.trans hObserved.le) hBefore
    · filter_upwards
        [(eventually_lt_nhds (lt_of_not_ge hBefore)).filter_mono nhdsWithin_le_nhds]
        with observed hObserved
      exact iff_of_false (not_le.mpr hObserved) hBefore
  filter_upwards [Filter.eventually_all.2 hCoordinates] with observed hObserved
  unfold stateAtTimeVector
  congr 1
  apply Fin.ext
  change eventCountAtOrBeforeTimeVector times observed =
    eventCountAtOrBeforeTimeVector times time
  unfold eventCountAtOrBeforeTimeVector
  exact Finset.sum_congr rfl fun index _ ↦ by simp only [hObserved index]

/-- Just before a time, the state selector is constant with value given by
strictly earlier events. Simultaneous events are all excluded from this limit. -/
theorem stateAtTimeVector_eventuallyEq_left
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) (time : ℝ) :
    (fun observed ↦ stateAtTimeVector states times observed) =ᶠ[𝓝[<] time]
      fun _ ↦ stateBeforeTimeVector states times time := by
  have hCoordinates : ∀ index : Fin eventCount,
      ∀ᶠ observed in 𝓝[<] time, (times index ≤ observed ↔ times index < time) := by
    intro index
    by_cases hBefore : times index < time
    · filter_upwards
        [(eventually_gt_nhds hBefore).filter_mono nhdsWithin_le_nhds]
        with observed hObserved
      exact iff_of_true hObserved.le hBefore
    · filter_upwards [self_mem_nhdsWithin] with observed hObserved
      exact iff_of_false (not_le.mpr (hObserved.trans_le (not_lt.mp hBefore))) hBefore
  filter_upwards [Filter.eventually_all.2 hCoordinates] with observed hObserved
  unfold stateAtTimeVector stateBeforeTimeVector
  congr 1
  apply Fin.ext
  change eventCountAtOrBeforeTimeVector times observed =
    eventCountBeforeTimeVector times time
  unfold eventCountAtOrBeforeTimeVector eventCountBeforeTimeVector
  exact Finset.sum_congr rfl fun index _ ↦ by simp only [hObserved index]

/-- The finite-coordinate selector is càdlàg in any topological state space. -/
theorem isCadlag_stateAtTimeVector [TopologicalSpace State]
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    IsCadlag (stateAtTimeVector states times) where
  isRightContinuous time :=
    tendsto_const_nhds.congr' (stateAtTimeVector_eventuallyEq_right states times time).symm
  tendsto_nhdsLT time :=
    ⟨stateBeforeTimeVector states times time,
      tendsto_const_nhds.congr' (stateAtTimeVector_eventuallyEq_left states times time).symm⟩

/-- The occupied-state observation of every complete finite jump history is
càdlàg, without any ordering, separation, or finite-state assumption. -/
theorem isCadlag_stateAtTime [TopologicalSpace State] (history : FiniteJumpHistory State) :
    IsCadlag history.stateAtTime :=
  isCadlag_stateAtTimeVector history.states history.jumpTimes

end FiniteJumpHistory
