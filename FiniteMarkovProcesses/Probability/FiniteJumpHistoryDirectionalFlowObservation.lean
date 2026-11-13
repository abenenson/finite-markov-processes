/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Linarith
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation

/-!
# Directional-flow observations of finite jump histories

This module counts every ordered state transition at or before a physical observation time.  On a
strictly ordered history it proves the microscopic continuity equation by comparing independently
selected occupied state with incoming and outgoing transition counts.

The two directions are never contracted to a net current in this module.

## Main results

- `FiniteJumpHistory.directedTransitionCountAtTime`: complete-history one-way count.
- `FiniteJumpHistory.measurable_directedTransitionCountAtTime`: fixed-time measurability.
- `FiniteJumpHistory.stateMembershipIndicator_stateAtTime_eq_initial_add_incoming_sub_outgoing`:
  non-tautological microscopic continuity on an ordered history.
-/

@[expose] public section

open MeasureTheory

namespace FiniteJumpHistory

universe u

noncomputable section

variable {State : Type u}

/-- Real indicator that an occupied state equals a selected state. -/
def stateMembershipIndicator [DecidableEq State] (state observed : State) : ℝ :=
  if state = observed then 1 else 0

/-- Membership indicators are measurable on a finite state space with measurable singletons. -/
theorem measurable_stateMembershipIndicator
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State]
    (observed : State) :
    Measurable fun state : State => stateMembershipIndicator state observed :=
  measurable_of_finite _

/-- Number of `source -> target` transitions at or before a fixed physical time on one
fixed-count history slice. -/
def directedTransitionCountAtTimeVector
    [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (source target : State) : ℕ :=
  ∑ index, if times index ≤ time ∧ states index.castSucc = source ∧
      states index.succ = target then 1 else 0

/-- Number of `source -> target` transitions at or before a fixed physical time on a complete
finite jump history. -/
def directedTransitionCountAtTime [DecidableEq State]
    (history : FiniteJumpHistory State) (time : ℝ) (source target : State) : ℕ :=
  directedTransitionCountAtTimeVector history.states history.jumpTimes time source target

/-- One ordered transition count never exceeds the complete number of events on a fixed-count
history slice. -/
theorem directedTransitionCountAtTimeVector_le
    [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (source target : State) :
    directedTransitionCountAtTimeVector states times time source target ≤ eventCount := by
  unfold directedTransitionCountAtTimeVector
  calc
    (∑ index : Fin eventCount,
        if times index ≤ time ∧ states index.castSucc = source ∧
          states index.succ = target then 1 else 0) ≤
        ∑ _index : Fin eventCount, 1 := by
      apply Finset.sum_le_sum
      intro index _hIndex
      split <;> simp
    _ = eventCount := by simp

/-- One ordered transition count never exceeds the complete history's event count. -/
theorem directedTransitionCountAtTime_le_jumpCount
    [DecidableEq State] (history : FiniteJumpHistory State)
    (time : ℝ) (source target : State) :
    history.directedTransitionCountAtTime time source target ≤ history.jumpCount :=
  directedTransitionCountAtTimeVector_le
    history.states history.jumpTimes time source target

/-- A one-way transition count is measurable on every fixed-count history slice. -/
theorem measurable_directedTransitionCountAtTimeVector
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] {eventCount : ℕ} (time : ℝ) (source target : State) :
    Measurable fun data :
        (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
      directedTransitionCountAtTimeVector data.1 data.2 time source target := by
  unfold directedTransitionCountAtTimeVector
  apply Finset.measurable_sum
  intro index _
  have hTime : MeasurableSet
      {data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) |
        data.2 index ≤ time} :=
    measurableSet_le ((measurable_pi_apply index).comp measurable_snd) measurable_const
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

/-- A one-way transition count is jointly measurable in a fixed-count history slice and the
physical observation time. -/
theorem measurable_directedTransitionCountAtTimeVector_uncurry
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] {eventCount : ℕ} (source target : State) :
    Measurable fun data :
        ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ ↦
      directedTransitionCountAtTimeVector
        data.1.1 data.1.2 data.2 source target := by
  unfold directedTransitionCountAtTimeVector
  apply Finset.measurable_sum
  intro index _hIndex
  have hTime : MeasurableSet
      {data : ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ |
        data.1.2 index ≤ data.2} :=
    measurableSet_le
      ((measurable_pi_apply index).comp (measurable_snd.comp measurable_fst))
      measurable_snd
  have hSource : MeasurableSet
      {data : ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ |
        data.1.1 index.castSucc = source} :=
    (Measurable.eq
      ((measurable_pi_apply index.castSucc).comp
        (measurable_fst.comp measurable_fst))
      measurable_const).setOf
  have hTarget : MeasurableSet
      {data : ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ |
        data.1.1 index.succ = target} :=
    (Measurable.eq
      ((measurable_pi_apply index.succ).comp
        (measurable_fst.comp measurable_fst))
      measurable_const).setOf
  exact Measurable.ite (hTime.inter (hSource.inter hTarget))
    measurable_const measurable_const

/-- A fixed-time one-way transition count is measurable on the complete unbounded history
carrier. -/
theorem measurable_directedTransitionCountAtTime
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] (time : ℝ) (source target : State) :
    Measurable fun history : FiniteJumpHistory State =>
      directedTransitionCountAtTime history time source target := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact measurable_directedTransitionCountAtTimeVector time source target

/-- A one-way transition count is jointly measurable in the complete unbounded history and
physical observation time. -/
theorem measurable_directedTransitionCountAtTime_uncurry
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] (source target : State) :
    Measurable fun data : FiniteJumpHistory State × ℝ ↦
      directedTransitionCountAtTime data.1 data.2 source target := by
  apply measurable_finiteJumpHistory_prod_time_of_fixedCount
  intro eventCount
  exact measurable_directedTransitionCountAtTimeVector_uncurry source target

/-- The real-valued one-way transition count is jointly measurable in the complete history and
physical observation time. -/
theorem measurable_real_directedTransitionCountAtTime_uncurry
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] (source target : State) :
    Measurable fun data : FiniteJumpHistory State × ℝ ↦
      (directedTransitionCountAtTime data.1 data.2 source target : ℝ) :=
  (measurable_of_countable fun count : ℕ ↦ (count : ℝ)).comp
    (measurable_directedTransitionCountAtTime_uncurry source target)

/-- The observed-event count is the cardinality of the event-time coordinates below the fixed
threshold. -/
theorem eventCountAtOrBeforeTimeVector_eq_filter_card {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) :
    eventCountAtOrBeforeTimeVector times time =
      (Finset.univ.filter fun index => times index ≤ time).card := by
  unfold eventCountAtOrBeforeTimeVector
  exact (Finset.natCast_card_filter (R := ℕ)
    (fun index : Fin eventCount => times index ≤ time) Finset.univ).symm

/-- On a strictly ordered time vector, an event is observed exactly when its index precedes the
number of observed events. -/
theorem eventTime_le_iff_val_lt_eventCountAtOrBefore
    {eventCount : ℕ} {times : Fin eventCount → ℝ}
    (hTimes : StrictMono times) (time : ℝ) (index : Fin eventCount) :
    times index ≤ time ↔ index.val < eventCountAtOrBeforeTimeVector times time := by
  rw [eventCountAtOrBeforeTimeVector_eq_filter_card]
  constructor
  · intro hObserved
    have hSubset :
        Finset.Iic index ⊆ Finset.univ.filter fun candidate => times candidate ≤ time := by
      intro candidate hCandidate
      simp only [Finset.mem_Iic] at hCandidate
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hTimes.monotone hCandidate).trans hObserved
    have hCard := Finset.card_le_card hSubset
    rw [Fin.card_Iic] at hCard
    omega
  · intro hIndex
    by_contra hNotObserved
    have hSubset :
        (Finset.univ.filter fun candidate => times candidate ≤ time) ⊆
          Finset.Iio index := by
      intro candidate hCandidate
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hCandidate
      simp only [Finset.mem_Iio]
      by_contra hNotBefore
      have hIndexCandidate : index ≤ candidate := le_of_not_gt hNotBefore
      exact hNotObserved ((hTimes.monotone hIndexCandidate).trans hCandidate)
    have hCard := Finset.card_le_card hSubset
    rw [Fin.card_Iio] at hCard
    omega

/-- A real sequence value equals its initial value plus all successive increments up to a finite
count. -/
theorem value_eq_zero_add_sum_increment (value : ℕ → ℝ) (count : ℕ) :
    value count =
      value 0 + ∑ index : Fin count, (value (index.val + 1) - value index.val) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      linarith

/-- State membership telescopes across a prefix of a finite state word. -/
theorem stateMembershipIndicator_prefix_telescoping
    [DecidableEq State] {eventCount observedCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (observed : State) (hObservedCount : observedCount ≤ eventCount) :
    stateMembershipIndicator
        (states ⟨observedCount, Nat.lt_succ_of_le hObservedCount⟩) observed =
      stateMembershipIndicator (states 0) observed +
        ∑ index : Fin observedCount,
          (stateMembershipIndicator
              (states ⟨index.val + 1, by omega⟩) observed -
            stateMembershipIndicator
              (states ⟨index.val, by omega⟩) observed) := by
  let value : ℕ → ℝ := fun index =>
    if hIndex : index < eventCount + 1 then
      stateMembershipIndicator (states ⟨index, hIndex⟩) observed else 0
  have hTelescoping := value_eq_zero_add_sum_increment value observedCount
  have hValueObserved :
      value observedCount =
        stateMembershipIndicator
          (states ⟨observedCount, Nat.lt_succ_of_le hObservedCount⟩) observed := by
    dsimp only [value]
    rw [dite_eq_left (Nat.lt_succ_of_le hObservedCount)]
  have hValueZero : value 0 = stateMembershipIndicator (states 0) observed := by
    simp [value]
  have hValueSucc (index : Fin observedCount) :
      value (index.val + 1) =
        stateMembershipIndicator (states ⟨index.val + 1, by omega⟩) observed := by
    dsimp only [value]
    rw [dite_eq_left (show index.val + 1 < eventCount + 1 by omega)]
  have hValueIndex (index : Fin observedCount) :
      value index.val =
        stateMembershipIndicator (states ⟨index.val, by omega⟩) observed := by
    dsimp only [value]
    rw [dite_eq_left (show index.val < eventCount + 1 by omega)]
  rw [hValueObserved, hValueZero] at hTelescoping
  simpa only [hValueSucc, hValueIndex] using hTelescoping

/-- Restricting a sum over `Fin eventCount` to indices below a smaller count equals the sum over
that smaller `Fin` type. -/
theorem sum_if_fin_val_lt
    {eventCount observedCount : ℕ} (hCount : observedCount ≤ eventCount)
    (summand : Fin eventCount → ℝ) :
    (∑ index : Fin eventCount,
      if index.val < observedCount then summand index else 0) =
      ∑ index : Fin observedCount,
        summand ⟨index.val, lt_of_lt_of_le index.isLt hCount⟩ := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (fun index hIndex =>
      ⟨index.val, (Finset.mem_filter.mp hIndex).2⟩)
  · intro index hIndex
    simp
  · intro first hFirst second hSecond hEqual
    apply Fin.ext
    exact congrArg (fun target : Fin observedCount => target.val) hEqual
  · intro target hTarget
    let source : Fin eventCount :=
      ⟨target.val, lt_of_lt_of_le target.isLt hCount⟩
    have hSource :
        source ∈ Finset.univ.filter fun index => index.val < observedCount := by
      simp [source]
    exact ⟨source, hSource, by apply Fin.ext; rfl⟩
  · intro index hIndex
    rfl

/-- On a strictly ordered time vector, independently selected state membership equals initial
membership plus the sum of all observed transition increments. -/
theorem stateMembershipIndicator_stateAtTimeVector_eq_initial_add_transitionIncrement
    [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (observed : State) (hTimes : StrictMono times) :
    stateMembershipIndicator (stateAtTimeVector states times time) observed =
      stateMembershipIndicator (states 0) observed +
        ∑ index : Fin eventCount,
          if times index ≤ time then
            stateMembershipIndicator (states index.succ) observed -
              stateMembershipIndicator (states index.castSucc) observed
          else 0 := by
  let observedCount := eventCountAtOrBeforeTimeVector times time
  have hCount : observedCount ≤ eventCount :=
    eventCountAtOrBeforeTimeVector_le times time
  have hPrefix := stateMembershipIndicator_prefix_telescoping states observed hCount
  have hSum := sum_if_fin_val_lt hCount
    (fun index : Fin eventCount =>
      stateMembershipIndicator (states index.succ) observed -
        stateMembershipIndicator (states index.castSucc) observed)
  have hObserved (index : Fin eventCount) :
      times index ≤ time ↔ index.val < observedCount :=
    eventTime_le_iff_val_lt_eventCountAtOrBefore hTimes time index
  unfold stateAtTimeVector stateIndexAtTimeVector
  rw [hPrefix]
  congr 1
  have hSum' :
      (∑ index : Fin eventCount,
        if times index ≤ time then
          stateMembershipIndicator (states index.succ) observed -
            stateMembershipIndicator (states index.castSucc) observed
        else 0) =
        ∑ index : Fin observedCount,
          (stateMembershipIndicator (states ⟨index.val + 1, by omega⟩) observed -
            stateMembershipIndicator (states ⟨index.val, by omega⟩) observed) := by
    calc
      _ = ∑ index : Fin eventCount,
          if index.val < observedCount then
            stateMembershipIndicator (states index.succ) observed -
              stateMembershipIndicator (states index.castSucc) observed
          else 0 := by
            apply Fintype.sum_congr
            intro index
            exact if_congr (hObserved index) rfl rfl
      _ = ∑ index : Fin observedCount,
          (stateMembershipIndicator
              (states
                (⟨index.val, lt_of_lt_of_le index.isLt hCount⟩ :
                  Fin eventCount).succ) observed -
            stateMembershipIndicator
              (states
                (⟨index.val, lt_of_lt_of_le index.isLt hCount⟩ :
                  Fin eventCount).castSucc) observed) := hSum
      _ = _ := by rfl
  exact hSum'.symm

/-- Summing one-way arrivals into one state equals the sum of observed arrival indicators. -/
theorem incomingDirectedTransitionCount_eq_stateArrivalSum
    [Fintype State] [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (observed : State) :
    (∑ source : State,
      (directedTransitionCountAtTimeVector states times time source observed : ℝ)) =
      ∑ index : Fin eventCount,
        if times index ≤ time then
          stateMembershipIndicator (states index.succ) observed
        else 0 := by
  simp only [directedTransitionCountAtTimeVector, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro index
  by_cases hTime : times index ≤ time
  · by_cases hObserved : states index.succ = observed
    · simp [hTime, hObserved, stateMembershipIndicator]
    · simp [hTime, hObserved, stateMembershipIndicator]
  · simp [hTime]

/-- Summing one-way departures from one state equals the sum of observed departure indicators. -/
theorem outgoingDirectedTransitionCount_eq_stateDepartureSum
    [Fintype State] [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (observed : State) :
    (∑ target : State,
      (directedTransitionCountAtTimeVector states times time observed target : ℝ)) =
      ∑ index : Fin eventCount,
        if times index ≤ time then
          stateMembershipIndicator (states index.castSucc) observed
        else 0 := by
  simp only [directedTransitionCountAtTimeVector, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro index
  by_cases hTime : times index ≤ time
  · by_cases hObserved : states index.castSucc = observed
    · simp [hTime, hObserved, stateMembershipIndicator]
    · simp [hTime, hObserved, stateMembershipIndicator]
  · simp [hTime]

/-- Microscopic continuity on one strictly ordered fixed-count history slice.  The occupied state
on the left is selected independently from the directed counts on the right. -/
theorem stateMembershipIndicator_stateAtTimeVector_eq_initial_add_incoming_sub_outgoing
    [Fintype State] [DecidableEq State] {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (observed : State) (hTimes : StrictMono times) :
    stateMembershipIndicator (stateAtTimeVector states times time) observed =
      stateMembershipIndicator (states 0) observed +
        ∑ source : State,
          (directedTransitionCountAtTimeVector states times time source observed : ℝ) -
        ∑ target : State,
          (directedTransitionCountAtTimeVector states times time observed target : ℝ) := by
  have hState :=
    stateMembershipIndicator_stateAtTimeVector_eq_initial_add_transitionIncrement
      states times time observed hTimes
  have hNet :
      (∑ index : Fin eventCount,
        if times index ≤ time then
          stateMembershipIndicator (states index.succ) observed -
            stateMembershipIndicator (states index.castSucc) observed
        else 0) =
        (∑ source : State,
          (directedTransitionCountAtTimeVector states times time source observed : ℝ)) -
        ∑ target : State,
          (directedTransitionCountAtTimeVector states times time observed target : ℝ) := by
    rw [incomingDirectedTransitionCount_eq_stateArrivalSum,
      outgoingDirectedTransitionCount_eq_stateDepartureSum,
      ← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro index
    by_cases hTime : times index ≤ time <;> simp [hTime]
  linarith

/-- Microscopic continuity on a complete history whose event times are ordered before the physical
horizon.  Reducedness is not needed for the algebra; physical CTMC laws provide it separately. -/
theorem stateMembershipIndicator_stateAtTime_eq_initial_add_incoming_sub_outgoing
    [Fintype State] [DecidableEq State]
    (history : FiniteJumpHistory State) (duration time : ℝ) (observed : State)
    (hOrdered : history.OrderedBefore duration) :
    stateMembershipIndicator (history.stateAtTime time) observed =
      stateMembershipIndicator history.initialState observed +
        ∑ source : State,
          (history.directedTransitionCountAtTime time source observed : ℝ) -
        ∑ target : State,
          (history.directedTransitionCountAtTime time observed target : ℝ) := by
  rcases history with ⟨eventCount, states, times⟩
  exact stateMembershipIndicator_stateAtTimeVector_eq_initial_add_incoming_sub_outgoing
    states times time observed hOrdered.2

end

end FiniteJumpHistory
