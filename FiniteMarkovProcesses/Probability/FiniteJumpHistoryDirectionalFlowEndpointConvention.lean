/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryEmpiricalDirectionalFlow

/-!
# Endpoint conventions for finite-jump directional flow

The repository's càdlàg observation counts a jump at time `t`, while the published open-interval
convention records only jumps strictly before `t`.  This module defines the strict observation and
proves that the two complete empirical paths agree almost everywhere in physical time.  The result
licenses passage to an `L1` equivalence class, but it does not construct that quotient or its hybrid
bounded-variation topology.

## Main results

- `FiniteJumpHistory.stateAtTime_ae_eq_stateBeforeTime`: càdlàg and strict state selectors agree
  almost everywhere in time.
- `FiniteJumpHistory.directedTransitionCountAtTime_ae_eq_beforeTime`: the two one-way count
  conventions agree almost everywhere in time.
- `PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowPath_endpoint_ae`: the exact
  positive-particle density and ordered one-way-flow paths agree componentwise almost everywhere.
-/

open MeasureTheory

namespace FiniteJumpHistory

universe u

noncomputable section

variable {State : Type u}

/-- Occupied state immediately before a fixed physical time on a complete finite jump history. -/
def stateBeforeTime (history : FiniteJumpHistory State) (time : ℝ) : State :=
  stateBeforeTimeVector history.states history.jumpTimes time

/-- The strictly-before selected state-word index is measurable on every fixed-count time slice. -/
theorem measurable_stateIndexBeforeTimeVector {eventCount : ℕ} (time : ℝ) :
    Measurable fun times : Fin eventCount → ℝ => stateIndexBeforeTimeVector times time := by
  classical
  intro selectedSet _
  have hPreimage :
      (fun times : Fin eventCount → ℝ => stateIndexBeforeTimeVector times time) ⁻¹' selectedSet =
        ⋃ selected : Fin (eventCount + 1),
          {times | selected ∈ selectedSet ∧
            eventCountBeforeTimeVector times time = selected.val} := by
    ext times
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hSelected
      exact ⟨stateIndexBeforeTimeVector times time, hSelected, rfl⟩
    · rintro ⟨selected, hSelected, hCount⟩
      have hIndex : stateIndexBeforeTimeVector times time = selected := Fin.ext hCount
      exact hIndex.symm ▸ hSelected
  rw [hPreimage]
  apply MeasurableSet.iUnion
  intro selected
  by_cases hSelected : selected ∈ selectedSet
  · have hFiber : MeasurableSet
        {times : Fin eventCount → ℝ |
          eventCountBeforeTimeVector times time = selected.val} :=
      measurable_eventCountBeforeTimeVector time (measurableSet_singleton selected.val)
    simpa only [hSelected, true_and] using hFiber
  · simp [hSelected]

/-- Strictly-before state selection is measurable on every fixed-count history slice. -/
theorem measurable_stateBeforeTimeVector [MeasurableSpace State]
    {eventCount : ℕ} (time : ℝ) :
    Measurable fun data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
      stateBeforeTimeVector data.1 data.2 time := by
  exact measurable_variableFiniteEvaluation measurable_fst
    ((measurable_stateIndexBeforeTimeVector time).comp measurable_snd)

/-- Strictly-before state selection is measurable on the complete unbounded history carrier. -/
theorem measurable_stateBeforeTime [MeasurableSpace State] (time : ℝ) :
    Measurable fun history : FiniteJumpHistory State => history.stateBeforeTime time := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact measurable_stateBeforeTimeVector time

/-- Number of `source -> target` transitions strictly before a fixed physical time on one
fixed-count history slice. -/
def directedTransitionCountBeforeTimeVector
    [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (source target : State) : ℕ :=
  ∑ index, if times index < time ∧ states index.castSucc = source ∧
      states index.succ = target then 1 else 0

/-- Number of `source -> target` transitions strictly before a fixed physical time on a complete
history. -/
def directedTransitionCountBeforeTime [DecidableEq State]
    (history : FiniteJumpHistory State) (time : ℝ) (source target : State) : ℕ :=
  directedTransitionCountBeforeTimeVector
    history.states history.jumpTimes time source target

/-- A strictly-before one-way transition count is measurable on every fixed-count history slice. -/
theorem measurable_directedTransitionCountBeforeTimeVector
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] {eventCount : ℕ} (time : ℝ) (source target : State) :
    Measurable fun data :
        (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
      directedTransitionCountBeforeTimeVector data.1 data.2 time source target := by
  unfold directedTransitionCountBeforeTimeVector
  apply Finset.measurable_sum
  intro index _
  have hTime : MeasurableSet
      {data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) |
        data.2 index < time} :=
    measurableSet_lt ((measurable_pi_apply index).comp measurable_snd) measurable_const
  have hSource : MeasurableSet
      {data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) |
        data.1 index.castSucc = source} :=
    (Measurable.eq
      ((measurable_pi_apply index.castSucc).comp measurable_fst)
      measurable_const).setOf
  have hTarget : MeasurableSet
      {data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) |
        data.1 index.succ = target} :=
    (Measurable.eq
      ((measurable_pi_apply index.succ).comp measurable_fst)
      measurable_const).setOf
  exact Measurable.ite (hTime.inter (hSource.inter hTarget))
    measurable_const measurable_const

/-- A fixed-time strictly-before one-way count is measurable on the complete history carrier. -/
theorem measurable_directedTransitionCountBeforeTime
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] (time : ℝ) (source target : State) :
    Measurable fun history : FiniteJumpHistory State =>
      directedTransitionCountBeforeTime history time source target := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact measurable_directedTransitionCountBeforeTimeVector time source target

/-- Away from every event time, the at-or-before and strictly-before event counts coincide. -/
theorem eventCountAtOrBeforeTimeVector_eq_eventCountBeforeTimeVector_of_forall_ne
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (time : ℝ)
    (hAway : ∀ index, times index ≠ time) :
    eventCountAtOrBeforeTimeVector times time =
      eventCountBeforeTimeVector times time := by
  unfold eventCountAtOrBeforeTimeVector eventCountBeforeTimeVector
  apply Finset.sum_congr rfl
  intro index _
  have hComparison : times index ≤ time ↔ times index < time :=
    ⟨fun hLe => lt_of_le_of_ne hLe (hAway index), le_of_lt⟩
  simp [hComparison]

/-- Away from every event time, càdlàg and strictly-before state selection coincide. -/
theorem stateAtTimeVector_eq_stateBeforeTimeVector_of_forall_ne
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) (time : ℝ)
    (hAway : ∀ index, times index ≠ time) :
    stateAtTimeVector states times time = stateBeforeTimeVector states times time := by
  unfold stateAtTimeVector stateBeforeTimeVector
  apply congrArg states
  apply Fin.ext
  exact eventCountAtOrBeforeTimeVector_eq_eventCountBeforeTimeVector_of_forall_ne
    times time hAway

/-- Away from every event time, the two one-way transition-count conventions coincide. -/
theorem directedTransitionCountAtTimeVector_eq_beforeTime_of_forall_ne
    [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (source target : State) (hAway : ∀ index, times index ≠ time) :
    directedTransitionCountAtTimeVector states times time source target =
      directedTransitionCountBeforeTimeVector states times time source target := by
  unfold directedTransitionCountAtTimeVector directedTransitionCountBeforeTimeVector
  apply Finset.sum_congr rfl
  intro index _
  have hComparison : times index ≤ time ↔ times index < time :=
    ⟨fun hLe => lt_of_le_of_ne hLe (hAway index), le_of_lt⟩
  simp [hComparison]

/-- Càdlàg and strictly-before state selectors agree almost everywhere in physical time. -/
theorem stateAtTime_ae_eq_stateBeforeTime (history : FiniteJumpHistory State) :
    (fun time => history.stateAtTime time) =ᵐ[volume]
      fun time => history.stateBeforeTime time := by
  have hAway : ∀ᵐ time : ℝ ∂volume,
      ∀ index, history.jumpTimes index ≠ time :=
    (Filter.eventually_all.2 fun index =>
      (Measure.ae_ne volume (history.jumpTimes index)).mono fun _ hNe => hNe.symm)
  filter_upwards [hAway] with time hTime
  exact stateAtTimeVector_eq_stateBeforeTimeVector_of_forall_ne
    history.states history.jumpTimes time hTime

/-- At-or-before and strictly-before one-way transition counts agree almost everywhere in physical
time. -/
theorem directedTransitionCountAtTime_ae_eq_beforeTime
    [DecidableEq State] (history : FiniteJumpHistory State) (source target : State) :
    (fun time => history.directedTransitionCountAtTime time source target) =ᵐ[volume]
      fun time => history.directedTransitionCountBeforeTime time source target := by
  have hAway : ∀ᵐ time : ℝ ∂volume,
      ∀ index, history.jumpTimes index ≠ time :=
    (Filter.eventually_all.2 fun index =>
      (Measure.ae_ne volume (history.jumpTimes index)).mono fun _ hNe => hNe.symm)
  filter_upwards [hAway] with time hTime
  exact directedTransitionCountAtTimeVector_eq_beforeTime_of_forall_ne
    history.states history.jumpTimes time source target hTime

end

end FiniteJumpHistory

namespace FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

namespace PositiveFiniteJumpHistoryReplicas

/-- Strictly-before empirical density at a fixed physical time. -/
def empiricalDensityBeforeTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) : ℝ :=
  (∑ replica, FiniteJumpHistory.stateMembershipIndicator
    ((histories replica).stateBeforeTime time) state) / (successorIndex + 1 : ℝ)

/-- Strictly-before cumulative ordered one-way flow per particle. -/
def empiricalSpecificDirectionalFlowBeforeTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) : ℝ :=
  (∑ replica, ((histories replica).directedTransitionCountBeforeTime
    time source target : ℝ)) / (successorIndex + 1 : ℝ)

/-- Published open-interval endpoint convention for empirical density and directional flow. -/
def empiricalDensityDirectionalFlowBeforePath (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    EmpiricalDensityDirectionalFlowPath State :=
  (fun time state => empiricalDensityBeforeTime successorIndex histories time state,
    fun time source target =>
      empiricalSpecificDirectionalFlowBeforeTime
        successorIndex histories time source target)

/-- Componentwise almost-everywhere equality of density and ordered directional-flow paths. -/
def DensityDirectionalFlowPathsAgreeAlmostEverywhere
    (first second : EmpiricalDensityDirectionalFlowPath State) : Prop :=
  (∀ state, (fun time => first.1 time state) =ᵐ[volume]
      fun time => second.1 time state) ∧
    ∀ source target, (fun time => first.2 time source target) =ᵐ[volume]
      fun time => second.2 time source target

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The exact càdlàg and published open-interval empirical paths agree componentwise almost
everywhere in physical time for every positive finite particle family. -/
theorem empiricalDensityDirectionalFlowPath_endpoint_ae
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    DensityDirectionalFlowPathsAgreeAlmostEverywhere
      (empiricalDensityDirectionalFlowPath successorIndex histories)
      (empiricalDensityDirectionalFlowBeforePath successorIndex histories) := by
  constructor
  · intro state
    have hAll : ∀ᵐ time : ℝ ∂volume, ∀ replica,
        (histories replica).stateAtTime time =
          (histories replica).stateBeforeTime time :=
      Filter.eventually_all.2 fun replica =>
        (histories replica).stateAtTime_ae_eq_stateBeforeTime
    filter_upwards [hAll] with time hTime
    change empiricalDensityAtTime successorIndex histories time state =
      empiricalDensityBeforeTime successorIndex histories time state
    unfold empiricalDensityAtTime empiricalDensityBeforeTime
    congr 1
    apply Finset.sum_congr rfl
    intro replica _
    rw [hTime replica]
  · intro source target
    have hAll : ∀ᵐ time : ℝ ∂volume, ∀ replica,
        (histories replica).directedTransitionCountAtTime time source target =
          (histories replica).directedTransitionCountBeforeTime time source target :=
      Filter.eventually_all.2 fun replica =>
        (histories replica).directedTransitionCountAtTime_ae_eq_beforeTime source target
    filter_upwards [hAll] with time hTime
    change empiricalSpecificDirectionalFlowAtTime
        successorIndex histories time source target =
      empiricalSpecificDirectionalFlowBeforeTime
        successorIndex histories time source target
    unfold empiricalSpecificDirectionalFlowAtTime empiricalSpecificDirectionalFlowBeforeTime
    congr 1
    apply Finset.sum_congr rfl
    intro replica _
    rw [hTime replica]

end PositiveFiniteJumpHistoryReplicas

end


end FiniteMarkovProcesses.Probability
