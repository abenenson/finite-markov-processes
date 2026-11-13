/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Data.Finset.Sort
public import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Deleting virtual self-events from finite jump histories

This module defines the canonical compression of a finite event history obtained by retaining
exactly those event indices at which the state changes. The selected event times remain in their
original order, the initial state is retained, and the post-event state word is sampled after each
selected genuine transition.

The deletion map is measurable on the existing unbounded `FiniteJumpHistory` carrier. No law-level
pushforward identity is asserted here.

## Main Results

- `FiniteJumpHistory.genuineEventIndices`: ordered set of state-changing event indices.
- `FiniteJumpHistory.deleteSelfEvents`: canonical self-event deletion map.
- `FiniteJumpHistory.deleteSelfEvents_embedJumpTimes_const`: deletion of a constant virtual word
  is the canonical no-jump history.
- `FiniteJumpHistory.sum_transitionReward_deleteSelfEventsSlice`: exact preservation of every
  zero-diagonal transition reward.
- `FiniteJumpHistory.finalState_deleteSelfEventsSlice`: preservation of the terminal state.
- `FiniteJumpHistory.measurable_deleteSelfEvents`: measurability on the common history carrier.
-/

@[expose] public section

open MeasureTheory

universe u

namespace FiniteJumpHistory

variable {State : Type u}

/-- Event indices at which the occupied state changes. -/
def genuineEventIndices {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) : Finset (Fin n) :=
  Finset.univ.filter fun index ↦ states index.castSucc ≠ states index.succ

/-- Number of state-changing events in one state word. -/
def genuineEventCount {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) : ℕ :=
  (genuineEventIndices states).card

/-- The number of genuine state-changing events cannot exceed the complete event count. -/
theorem genuineEventCount_le {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) :
    genuineEventCount states ≤ n := by
  unfold genuineEventCount
  calc
    (genuineEventIndices states).card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Fintype.card_fin n

/-- The specified state-changing event index, in its original chronological order. -/
def genuineEventIndex {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) (index : Fin (genuineEventCount states)) : Fin n :=
  (genuineEventIndices states).orderEmbOfFin rfl index

/-- The enumerated genuine-event indices are members of the filtered event set. -/
theorem genuineEventIndex_mem {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) (index : Fin (genuineEventCount states)) :
    genuineEventIndex states index ∈ genuineEventIndices states :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Every genuine-event index occurs in the canonical increasing enumeration. -/
theorem exists_genuineEventIndex_eq {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) {eventIndex : Fin n}
    (hGenuine : eventIndex ∈ genuineEventIndices states) :
    ∃ index : Fin (genuineEventCount states),
      genuineEventIndex states index = eventIndex := by
  have hRange :
      eventIndex ∈ Set.range
        ((genuineEventIndices states).orderEmbOfFin
          (rfl : (genuineEventIndices states).card = genuineEventCount states)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hGenuine
  exact hRange

/-- A finite state word is constant across an index interval when every intervening event is a
self-event. -/
theorem state_eq_of_no_change_between {n : ℕ}
    (states : Fin (n + 1) → State) {start finish : Fin (n + 1)}
    (hLe : start ≤ finish)
    (hNoChange : ∀ index : Fin n,
      start.1 ≤ index.1 → index.1 < finish.1 →
        states index.castSucc = states index.succ) :
    states start = states finish := by
  have hLeValue : start.1 ≤ finish.1 := hLe
  have hStep : ∀ offset : ℕ, start.1 + offset ≤ finish.1 →
      ∀ hBound : start.1 + offset < n + 1,
        states start = states ⟨start.1 + offset, hBound⟩ := by
    intro offset hOffset
    induction offset with
    | zero =>
        intro hBound
        congr
    | succ offset inductionHypothesis =>
        intro hBound
        have hPreviousLe : start.1 + offset ≤ finish.1 := by omega
        have hPreviousBound : start.1 + offset < n + 1 := by omega
        have hEventBound : start.1 + offset < n := by omega
        let eventIndex : Fin n := ⟨start.1 + offset, hEventBound⟩
        calc
          states start = states ⟨start.1 + offset, hPreviousBound⟩ :=
            inductionHypothesis hPreviousLe hPreviousBound
          _ = states ⟨start.1 + offset + 1, hBound⟩ := by
            have hAdjacent := hNoChange eventIndex
              (by change start.1 ≤ start.1 + offset; omega)
              (by change start.1 + offset < finish.1; omega)
            have hSource :
                (⟨start.1 + offset, hPreviousBound⟩ : Fin (n + 1)) =
                  eventIndex.castSucc := by
              ext
              rfl
            have hTarget :
                (⟨start.1 + offset + 1, hBound⟩ : Fin (n + 1)) =
                  eventIndex.succ := by
              ext
              rfl
            rw [hSource, hTarget]
            exact hAdjacent
  have hFinishLe : start.1 + (finish.1 - start.1) ≤ finish.1 := by omega
  have hFinishBound : start.1 + (finish.1 - start.1) < n + 1 := by omega
  have hValue := hStep (finish.1 - start.1) hFinishLe hFinishBound
  convert hValue using 1
  apply congrArg states
  apply Fin.ext
  simp
  omega

/-- Delete virtual self-events from one fixed-count history slice. -/
def deleteSelfEventsSlice {n : ℕ} [DecidableEq State]
    (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    FiniteJumpHistory State :=
  ⟨genuineEventCount states,
    Fin.cases (states 0) fun index ↦ states (genuineEventIndex states index).succ,
    fun index ↦ times (genuineEventIndex states index)⟩

/-- Canonical deletion of every repeated-state virtual event from a finite history. -/
def deleteSelfEvents [DecidableEq State] :
    FiniteJumpHistory State → FiniteJumpHistory State
  | ⟨_, states, times⟩ => deleteSelfEventsSlice states times

/-- The compressed history's event count is exactly the number of state-changing input events. -/
@[simp]
theorem jumpCount_deleteSelfEvents [DecidableEq State]
    (history : FiniteJumpHistory State) :
    (deleteSelfEvents history).jumpCount = genuineEventCount history.states := by
  rcases history with ⟨n, states, times⟩
  rfl

/-- Deleting virtual self-events never increases the complete event count. -/
theorem jumpCount_deleteSelfEvents_le [DecidableEq State]
    (history : FiniteJumpHistory State) :
    (deleteSelfEvents history).jumpCount ≤ history.jumpCount := by
  rw [jumpCount_deleteSelfEvents]
  exact genuineEventCount_le history.states

/-- Deleting virtual self-events preserves strict physical time ordering and the open horizon
boundary. -/
theorem OrderedBefore.deleteSelfEvents [DecidableEq State]
    {history : FiniteJumpHistory State} {duration : ℝ}
    (hOrdered : history.OrderedBefore duration) :
    history.deleteSelfEvents.OrderedBefore duration := by
  rcases history with ⟨eventCount, states, times⟩
  change times ∈ orderedJumpTimes eventCount duration at hOrdered
  change (fun index ↦ times (genuineEventIndex states index)) ∈
    orderedJumpTimes (genuineEventCount states) duration
  refine ⟨fun index ↦ hOrdered.1 (genuineEventIndex states index), ?_⟩
  exact hOrdered.2.comp
    ((genuineEventIndices states).orderEmbOfFin
      (rfl : (genuineEventIndices states).card = genuineEventCount states)).strictMono

/-- Self-event deletion preserves the initial state of each fixed history slice. -/
@[simp]
theorem initialState_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    (deleteSelfEventsSlice states times).initialState = states 0 := by
  rfl

/-- Deleting every event from a constant virtual state word gives the canonical no-jump
history, independently of its virtual event count and times. -/
theorem deleteSelfEvents_embedJumpTimes_const [DecidableEq State]
    (state : State) (eventCount : ℕ) (times : Fin eventCount → ℝ) :
    deleteSelfEvents (embedJumpTimes eventCount (fun _ ↦ state) times) = noJumpHistory state := by
  apply eq_noJumpHistory_of_jumpCount_eq_zero
  change genuineEventCount (fun _ : Fin (eventCount + 1) ↦ state) = 0
  simp [genuineEventCount, genuineEventIndices]

/-- The source of every compressed edge is the source of its selected genuine input edge. -/
theorem states_deleteSelfEventsSlice_castSucc [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (index : Fin (genuineEventCount states)) :
    (deleteSelfEventsSlice states times).states index.castSucc =
      states (genuineEventIndex states index).castSucc := by
  by_cases hZero : index.1 = 0
  · have hIndex : index = ⟨0, by omega⟩ := by
      ext
      exact hZero
    rw [hIndex]
    change states 0 = states (genuineEventIndex states ⟨0, _⟩).castSucc
    apply state_eq_of_no_change_between states (Fin.zero_le _)
    intro eventIndex _ hBefore
    have hNotGenuine : eventIndex ∉ genuineEventIndices states := by
      intro hGenuine
      obtain ⟨selectedIndex, hSelected⟩ :=
        exists_genuineEventIndex_eq states hGenuine
      have hZeroLe : (⟨0, by omega⟩ : Fin (genuineEventCount states)) ≤
          selectedIndex := by
        exact Nat.zero_le selectedIndex.1
      have hMonotone :
          genuineEventIndex states ⟨0, by omega⟩ ≤
            genuineEventIndex states selectedIndex :=
        ((genuineEventIndices states).orderEmbOfFin rfl).monotone hZeroLe
      rw [hSelected] at hMonotone
      exact (not_le_of_gt hBefore) hMonotone
    simpa [genuineEventIndices] using hNotGenuine
  · let previous : Fin (genuineEventCount states) :=
      ⟨index.1 - 1, by omega⟩
    have hIndex : index.castSucc = previous.succ := by
      ext
      simp [previous]
      omega
    change (Fin.cases (states 0)
      (fun selectedIndex ↦ states (genuineEventIndex states selectedIndex).succ)
        index.castSucc) =
      states (genuineEventIndex states index).castSucc
    rw [hIndex, Fin.cases_succ]
    have hSelected :
        genuineEventIndex states previous < genuineEventIndex states index := by
      apply ((genuineEventIndices states).orderEmbOfFin rfl).strictMono
      change previous.1 < index.1
      simp [previous]
      omega
    apply state_eq_of_no_change_between states (by
      change (genuineEventIndex states previous).1 + 1 ≤
        (genuineEventIndex states index).1
      omega)
    intro eventIndex hAfter hBefore
    have hNotGenuine : eventIndex ∉ genuineEventIndices states := by
      intro hGenuine
      obtain ⟨selectedIndex, hSelectedIndex⟩ :=
        exists_genuineEventIndex_eq states hGenuine
      have hLeft : previous < selectedIndex := by
        apply (((genuineEventIndices states).orderEmbOfFin rfl).lt_iff_lt).mp
        change genuineEventIndex states previous <
          genuineEventIndex states selectedIndex
        rw [hSelectedIndex]
        change (genuineEventIndex states previous).1 < eventIndex.1
        change (genuineEventIndex states previous).1 + 1 ≤ eventIndex.1 at hAfter
        omega
      have hRight : selectedIndex < index := by
        apply (((genuineEventIndices states).orderEmbOfFin rfl).lt_iff_lt).mp
        change genuineEventIndex states selectedIndex < genuineEventIndex states index
        rw [hSelectedIndex]
        exact hBefore
      change index.1 - 1 < selectedIndex.1 at hLeft
      omega
    simpa [genuineEventIndices] using hNotGenuine

/-- The target of every compressed edge is the target of its selected genuine input edge. -/
theorem states_deleteSelfEventsSlice_succ [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (index : Fin (genuineEventCount states)) :
    (deleteSelfEventsSlice states times).states index.succ =
      states (genuineEventIndex states index).succ := by
  simp [deleteSelfEventsSlice, FiniteJumpHistory.states]

/-- Compressing a state word preserves its final occupied state. -/
theorem finalState_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    (deleteSelfEventsSlice states times).finalState = states (Fin.last n) := by
  let eventCount := genuineEventCount states
  by_cases hZero : eventCount = 0
  · change (Fin.cases (states 0)
      (fun index ↦ states (genuineEventIndex states index).succ)
        (Fin.last eventCount)) = states (Fin.last n)
    have hLastZero : Fin.last eventCount = 0 := by
      apply Fin.ext
      simp [hZero]
    rw [hLastZero, Fin.cases_zero]
    apply state_eq_of_no_change_between states (Fin.zero_le _)
    intro eventIndex _ _
    have hNotGenuine : eventIndex ∉ genuineEventIndices states := by
      intro hGenuine
      obtain ⟨selectedIndex, _⟩ := exists_genuineEventIndex_eq states hGenuine
      exact Fin.elim0 (hZero ▸ selectedIndex)
    simpa [genuineEventIndices] using hNotGenuine
  · have hPositive : 0 < eventCount := Nat.pos_of_ne_zero hZero
    let lastSelected : Fin eventCount :=
      ⟨eventCount - 1, Nat.sub_lt hPositive (Nat.succ_pos 0)⟩
    have hLast : Fin.last eventCount = lastSelected.succ := by
      ext
      simp [lastSelected]
      omega
    change (Fin.cases (states 0)
      (fun index ↦ states (genuineEventIndex states index).succ)
        (Fin.last eventCount)) = states (Fin.last n)
    rw [hLast, Fin.cases_succ]
    apply state_eq_of_no_change_between states (by
      change (genuineEventIndex states lastSelected).1 + 1 ≤ n
      exact Nat.succ_le_iff.mpr (genuineEventIndex states lastSelected).isLt)
    intro eventIndex hAfter _
    have hNotGenuine : eventIndex ∉ genuineEventIndices states := by
      intro hGenuine
      obtain ⟨selectedIndex, hSelectedIndex⟩ :=
        exists_genuineEventIndex_eq states hGenuine
      have hSelectedLe : selectedIndex ≤ lastSelected := by
        change selectedIndex.1 ≤ eventCount - 1
        omega
      have hMonotone :
          genuineEventIndex states selectedIndex ≤
            genuineEventIndex states lastSelected :=
        ((genuineEventIndices states).orderEmbOfFin rfl).monotone hSelectedLe
      rw [hSelectedIndex] at hMonotone
      change (genuineEventIndex states lastSelected).1 + 1 ≤ eventIndex.1 at hAfter
      omega
    simpa [genuineEventIndices] using hNotGenuine

/-- Deleting self-events preserves every transition-reward sum whose diagonal reward vanishes. -/
theorem sum_transitionReward_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (reward : State → State → ℝ) (hSelf : ∀ state, reward state state = 0) :
    (∑ index : Fin (deleteSelfEventsSlice states times).jumpCount,
      reward ((deleteSelfEventsSlice states times).states index.castSucc)
        ((deleteSelfEventsSlice states times).states index.succ)) =
      ∑ index : Fin n, reward (states index.castSucc) (states index.succ) := by
  change (∑ index : Fin (genuineEventCount states),
    reward ((deleteSelfEventsSlice states times).states index.castSucc)
      ((deleteSelfEventsSlice states times).states index.succ)) = _
  simp_rw [states_deleteSelfEventsSlice_castSucc, states_deleteSelfEventsSlice_succ]
  calc
    (∑ index : Fin (genuineEventCount states),
      reward (states (genuineEventIndex states index).castSucc)
        (states (genuineEventIndex states index).succ)) =
        ∑ eventIndex ∈ genuineEventIndices states,
          reward (states eventIndex.castSucc) (states eventIndex.succ) := by
      rw [← Finset.map_orderEmbOfFin_univ
        (genuineEventIndices states)
        (rfl : (genuineEventIndices states).card = genuineEventCount states)]
      rw [Finset.sum_map]
      rfl
    _ = _ := by
      rw [genuineEventIndices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro eventIndex _
      by_cases hGenuine : states eventIndex.castSucc ≠ states eventIndex.succ
      · rw [ite_eq_left hGenuine]
      · rw [ite_eq_right hGenuine]
        simp only [not_ne_iff] at hGenuine
        rw [hGenuine, hSelf]

/-- Deleting self-events preserves every time-dependent transition-reward sum whose diagonal
reward vanishes at every event time. -/
theorem sum_timeTransitionReward_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (reward : ℝ → State → State → ℝ)
    (hSelf : ∀ time state, reward time state state = 0) :
    (∑ index : Fin (deleteSelfEventsSlice states times).jumpCount,
      reward ((deleteSelfEventsSlice states times).jumpTimes index)
        ((deleteSelfEventsSlice states times).states index.castSucc)
        ((deleteSelfEventsSlice states times).states index.succ)) =
      ∑ index : Fin n,
        reward (times index) (states index.castSucc) (states index.succ) := by
  change (∑ index : Fin (genuineEventCount states),
    reward (times (genuineEventIndex states index))
      ((deleteSelfEventsSlice states times).states index.castSucc)
      ((deleteSelfEventsSlice states times).states index.succ)) = _
  simp_rw [states_deleteSelfEventsSlice_castSucc, states_deleteSelfEventsSlice_succ]
  calc
    (∑ index : Fin (genuineEventCount states),
      reward (times (genuineEventIndex states index))
        (states (genuineEventIndex states index).castSucc)
        (states (genuineEventIndex states index).succ)) =
        ∑ eventIndex ∈ genuineEventIndices states,
          reward (times eventIndex)
            (states eventIndex.castSucc) (states eventIndex.succ) := by
      rw [← Finset.map_orderEmbOfFin_univ
        (genuineEventIndices states)
        (rfl : (genuineEventIndices states).card = genuineEventCount states)]
      rw [Finset.sum_map]
      rfl
    _ = _ := by
      rw [genuineEventIndices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro eventIndex _
      by_cases hGenuine : states eventIndex.castSucc ≠ states eventIndex.succ
      · rw [ite_eq_left hGenuine]
      · rw [ite_eq_right hGenuine]
        simp only [not_ne_iff] at hGenuine
        rw [hGenuine, hSelf]

/-- The whole-history form of time-dependent diagonal-zero reward preservation. -/
theorem sum_timeTransitionReward_deleteSelfEvents [DecidableEq State]
    (history : FiniteJumpHistory State) (reward : ℝ → State → State → ℝ)
    (hSelf : ∀ time state, reward time state state = 0) :
    (∑ index : Fin history.deleteSelfEvents.jumpCount,
      reward (history.deleteSelfEvents.jumpTimes index)
        (history.deleteSelfEvents.states index.castSucc)
        (history.deleteSelfEvents.states index.succ)) =
      ∑ index : Fin history.jumpCount,
        reward (history.jumpTimes index)
          (history.states index.castSucc) (history.states index.succ) := by
  rcases history with ⟨eventCount, states, times⟩
  exact sum_timeTransitionReward_deleteSelfEventsSlice states times reward hSelf

/-- Deleting self-events preserves the time-weighted sum of adjacent state-reward differences. -/
theorem sum_jumpTime_mul_stateRewardDifference_deleteSelfEventsSlice [DecidableEq State]
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (stateReward : State → ℝ) :
    (∑ index : Fin (deleteSelfEventsSlice states times).jumpCount,
      (deleteSelfEventsSlice states times).jumpTimes index *
        (stateReward ((deleteSelfEventsSlice states times).states index.castSucc) -
          stateReward ((deleteSelfEventsSlice states times).states index.succ))) =
      ∑ index : Fin n, times index *
        (stateReward (states index.castSucc) - stateReward (states index.succ)) := by
  change (∑ index : Fin (genuineEventCount states),
    times (genuineEventIndex states index) *
      (stateReward ((deleteSelfEventsSlice states times).states index.castSucc) -
        stateReward ((deleteSelfEventsSlice states times).states index.succ))) = _
  simp_rw [states_deleteSelfEventsSlice_castSucc, states_deleteSelfEventsSlice_succ]
  calc
    (∑ index : Fin (genuineEventCount states),
      times (genuineEventIndex states index) *
        (stateReward (states (genuineEventIndex states index).castSucc) -
          stateReward (states (genuineEventIndex states index).succ))) =
        ∑ eventIndex ∈ genuineEventIndices states,
          times eventIndex *
            (stateReward (states eventIndex.castSucc) -
              stateReward (states eventIndex.succ)) := by
      rw [← Finset.map_orderEmbOfFin_univ
        (genuineEventIndices states)
        (rfl : (genuineEventIndices states).card = genuineEventCount states)]
      rw [Finset.sum_map]
      rfl
    _ = _ := by
      rw [genuineEventIndices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro eventIndex _
      by_cases hGenuine : states eventIndex.castSucc ≠ states eventIndex.succ
      · rw [ite_eq_left hGenuine]
      · rw [ite_eq_right hGenuine]
        simp only [not_ne_iff] at hGenuine
        rw [hGenuine, sub_self, mul_zero]

/-- On a fixed state word, deletion is measurable as a function of the event-time vector. -/
theorem measurable_deleteSelfEventsSlice
    [DecidableEq State] [MeasurableSpace State]
    {n : ℕ} (states : Fin (n + 1) → State) :
    Measurable (deleteSelfEventsSlice states) := by
  let eventCount := genuineEventCount states
  let outputStates : Fin (eventCount + 1) → State :=
    Fin.cases (states 0) fun index ↦ states (genuineEventIndex states index).succ
  let outputTimes : (Fin n → ℝ) → Fin eventCount → ℝ :=
    fun times index ↦ times (genuineEventIndex states index)
  have hSigma : Measurable
      (@Sigma.mk ℕ (fun count ↦
        (Fin (count + 1) → State) × (Fin count → ℝ)) eventCount) := by
    apply Measurable.of_comap_le
    exact (MeasurableSpace.comap_mono (iInf_le _ eventCount)).trans
      MeasurableSpace.comap_map_le
  have hOutputTimes : Measurable outputTimes := by
    apply Measurable.of_eval
    intro index
    exact measurable_pi_apply (genuineEventIndex states index)
  change Measurable fun times ↦
    @Sigma.mk ℕ (fun count ↦
      (Fin (count + 1) → State) × (Fin count → ℝ)) eventCount
      (outputStates, outputTimes times)
  exact hSigma.comp <| measurable_const.prodMk hOutputTimes

/-- Self-event deletion is measurable on the unbounded finite-history carrier. -/
theorem measurable_deleteSelfEvents
    [DecidableEq State] [Fintype State] [MeasurableSpace State]
    [MeasurableSingletonClass State] :
    Measurable (deleteSelfEvents : FiniteJumpHistory State → FiniteJumpHistory State) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  exact measurable_deleteSelfEventsSlice states

end FiniteJumpHistory
