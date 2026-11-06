/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Fixed-time observations of finite jump histories

This module defines the occupied state of a finite jump history at a physical observation time.
The state is selected by independently counting event-time coordinates at or before that time.
Strict-before variants support left-limit constructions.  All fixed-time selectors are measurable.

No continuity equation is used in these definitions.

## Main results

- `FiniteJumpHistory.eventCountAtOrBeforeTimeVector`: number of events at or before a time.
- `FiniteJumpHistory.stateAtTimeVector`: selected state on a fixed jump-count slice.
- `FiniteJumpHistory.stateAtTime`: selected state on the complete unbounded history carrier.
- `FiniteJumpHistory.measurable_initialState` and `FiniteJumpHistory.measurable_finalState`:
  measurable endpoint observations.
- `FiniteJumpHistory.measurable_stateAtTime`: fixed-time measurability.
- `FiniteJumpHistory.stateAtTime_eq_finalState_of_orderedBefore`: terminal-time recovery on the
  physical ordered carrier.
-/

open MeasureTheory

namespace FiniteJumpHistory

universe u v

noncomputable section

variable {State : Type u}

/-- The initial-state projection is measurable on the complete unbounded history carrier. -/
theorem measurable_initialState [MeasurableSpace State] :
    Measurable fun history : FiniteJumpHistory State => history.initialState := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact (measurable_pi_apply 0).comp measurable_fst

/-- The final-state projection is measurable on the complete unbounded history carrier. -/
theorem measurable_finalState [MeasurableSpace State] :
    Measurable fun history : FiniteJumpHistory State => history.finalState := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact (measurable_pi_apply (Fin.last eventCount)).comp measurable_fst

/-- Number of event-time coordinates at or before a fixed physical time. -/
def eventCountAtOrBeforeTimeVector {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) : ℕ :=
  ∑ index, if times index ≤ time then 1 else 0

/-- The number of observed events never exceeds the complete event count. -/
theorem eventCountAtOrBeforeTimeVector_le {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) :
    eventCountAtOrBeforeTimeVector times time ≤ eventCount := by
  unfold eventCountAtOrBeforeTimeVector
  calc
    ∑ index : Fin eventCount, (if times index ≤ time then 1 else 0) ≤
        ∑ _index : Fin eventCount, 1 := by
      apply Finset.sum_le_sum
      intro index _
      split <;> simp
    _ = eventCount := by simp

/-- Number of event-time coordinates strictly before a fixed physical time. -/
def eventCountBeforeTimeVector {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) : ℕ :=
  ∑ index, if times index < time then 1 else 0

/-- The number of events strictly before a time never exceeds the complete event count. -/
theorem eventCountBeforeTimeVector_le {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) :
    eventCountBeforeTimeVector times time ≤ eventCount := by
  unfold eventCountBeforeTimeVector
  calc
    ∑ index : Fin eventCount, (if times index < time then 1 else 0) ≤
        ∑ _index : Fin eventCount, 1 := by
      apply Finset.sum_le_sum
      intro index _
      split <;> simp
    _ = eventCount := by simp

/-- State-word index selected by all events at or before a fixed physical time. -/
def stateIndexAtTimeVector {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) : Fin (eventCount + 1) :=
  ⟨eventCountAtOrBeforeTimeVector times time,
    Nat.lt_succ_of_le (eventCountAtOrBeforeTimeVector_le times time)⟩

/-- State-word index selected immediately before a fixed physical time. -/
def stateIndexBeforeTimeVector {eventCount : ℕ}
    (times : Fin eventCount → ℝ) (time : ℝ) : Fin (eventCount + 1) :=
  ⟨eventCountBeforeTimeVector times time,
    Nat.lt_succ_of_le (eventCountBeforeTimeVector_le times time)⟩

/-- Occupied state after all events at or before a fixed physical time. -/
def stateAtTimeVector {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) (time : ℝ) : State :=
  states (stateIndexAtTimeVector times time)

/-- Occupied state immediately before a fixed physical time. -/
def stateBeforeTimeVector {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) (time : ℝ) : State :=
  states (stateIndexBeforeTimeVector times time)

/-- Occupied state of a complete finite jump history at a fixed physical time. -/
def stateAtTime (history : FiniteJumpHistory State) (time : ℝ) : State :=
  stateAtTimeVector history.states history.jumpTimes time

/-- The at-or-before event count is measurable on every fixed-count time-vector slice. -/
theorem measurable_eventCountAtOrBeforeTimeVector {eventCount : ℕ} (time : ℝ) :
    Measurable fun times : Fin eventCount → ℝ =>
      eventCountAtOrBeforeTimeVector times time := by
  unfold eventCountAtOrBeforeTimeVector
  apply Finset.measurable_sum
  intro index _
  have hObserved : MeasurableSet {times : Fin eventCount → ℝ | times index ≤ time} :=
    measurableSet_le (measurable_pi_apply index) measurable_const
  exact Measurable.ite hObserved measurable_const measurable_const

/-- The strict-before event count is measurable on every fixed-count time-vector slice. -/
theorem measurable_eventCountBeforeTimeVector {eventCount : ℕ} (time : ℝ) :
    Measurable fun times : Fin eventCount → ℝ => eventCountBeforeTimeVector times time := by
  unfold eventCountBeforeTimeVector
  apply Finset.measurable_sum
  intro index _
  have hObserved : MeasurableSet {times : Fin eventCount → ℝ | times index < time} :=
    measurableSet_lt (measurable_pi_apply index) measurable_const
  exact Measurable.ite hObserved measurable_const measurable_const

/-- The selected state-word index is measurable on every fixed-count time-vector slice. -/
theorem measurable_stateIndexAtTimeVector {eventCount : ℕ} (time : ℝ) :
    Measurable fun times : Fin eventCount → ℝ => stateIndexAtTimeVector times time := by
  classical
  intro selectedSet _
  have hPreimage :
      (fun times : Fin eventCount → ℝ => stateIndexAtTimeVector times time) ⁻¹' selectedSet =
        ⋃ selected : Fin (eventCount + 1),
          {times | selected ∈ selectedSet ∧
            eventCountAtOrBeforeTimeVector times time = selected.val} := by
    ext times
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hSelected
      exact ⟨stateIndexAtTimeVector times time, hSelected, rfl⟩
    · rintro ⟨selected, hSelected, hCount⟩
      have hIndex : stateIndexAtTimeVector times time = selected := Fin.ext hCount
      exact hIndex.symm ▸ hSelected
  rw [hPreimage]
  apply MeasurableSet.iUnion
  intro selected
  by_cases hSelected : selected ∈ selectedSet
  · have hFiber : MeasurableSet
        {times : Fin eventCount → ℝ |
          eventCountAtOrBeforeTimeVector times time = selected.val} :=
      measurable_eventCountAtOrBeforeTimeVector time (measurableSet_singleton selected.val)
    simpa only [hSelected, true_and] using hFiber
  · simp [hSelected]

/-- Measurability of evaluation at a measurably selected finite coordinate. -/
theorem measurable_variableFiniteEvaluation
    {A : Type v} {Target : Type u} [MeasurableSpace A] [MeasurableSpace Target]
    {eventCount : ℕ} {values : A → Fin (eventCount + 1) → Target}
    {index : A → Fin (eventCount + 1)}
    (hValues : Measurable values) (hIndex : Measurable index) :
    Measurable fun source => values source (index source) := by
  intro event hEvent
  have hPreimage :
      (fun source => values source (index source)) ⁻¹' event =
        ⋃ selected : Fin (eventCount + 1),
          {source | index source = selected} ∩
            {source | values source selected ∈ event} := by
    ext source
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hSource
      exact ⟨index source, rfl, hSource⟩
    · rintro ⟨selected, hSelected, hSource⟩
      simpa [hSelected] using hSource
  rw [hPreimage]
  exact MeasurableSet.iUnion fun selected =>
    (hIndex (measurableSet_singleton selected)).inter
      ((measurable_pi_apply selected).comp hValues hEvent)

/-- Fixed-time state selection is measurable on every fixed-count history slice. -/
theorem measurable_stateAtTimeVector [MeasurableSpace State]
    {eventCount : ℕ} (time : ℝ) :
    Measurable fun data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
      stateAtTimeVector data.1 data.2 time := by
  exact measurable_variableFiniteEvaluation measurable_fst
    ((measurable_stateIndexAtTimeVector time).comp measurable_snd)

/-- The at-or-before event count is jointly measurable in a fixed-count time vector and the
observation time. -/
theorem measurable_eventCountAtOrBeforeTimeVector_uncurry {eventCount : ℕ} :
    Measurable fun data : (Fin eventCount → ℝ) × ℝ ↦
      eventCountAtOrBeforeTimeVector data.1 data.2 := by
  unfold eventCountAtOrBeforeTimeVector
  apply Finset.measurable_sum
  intro index _hIndex
  have hObserved : MeasurableSet
      {data : (Fin eventCount → ℝ) × ℝ | data.1 index ≤ data.2} :=
    measurableSet_le ((measurable_pi_apply index).comp measurable_fst) measurable_snd
  exact Measurable.ite hObserved measurable_const measurable_const

/-- The selected state-word index is jointly measurable in a fixed-count time vector and the
observation time. -/
theorem measurable_stateIndexAtTimeVector_uncurry {eventCount : ℕ} :
    Measurable fun data : (Fin eventCount → ℝ) × ℝ ↦
      stateIndexAtTimeVector data.1 data.2 := by
  classical
  intro selectedSet _hSelectedSet
  have hPreimage :
      (fun data : (Fin eventCount → ℝ) × ℝ ↦
        stateIndexAtTimeVector data.1 data.2) ⁻¹' selectedSet =
        ⋃ selected : Fin (eventCount + 1),
          {data | selected ∈ selectedSet ∧
            eventCountAtOrBeforeTimeVector data.1 data.2 = selected.val} := by
    ext data
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hSelected
      exact ⟨stateIndexAtTimeVector data.1 data.2, hSelected, rfl⟩
    · rintro ⟨selected, hSelected, hCount⟩
      have hIndex : stateIndexAtTimeVector data.1 data.2 = selected := Fin.ext hCount
      exact hIndex.symm ▸ hSelected
  rw [hPreimage]
  apply MeasurableSet.iUnion
  intro selected
  by_cases hSelected : selected ∈ selectedSet
  · have hFiber : MeasurableSet
        {data : (Fin eventCount → ℝ) × ℝ |
          eventCountAtOrBeforeTimeVector data.1 data.2 = selected.val} :=
      measurable_eventCountAtOrBeforeTimeVector_uncurry
        (measurableSet_singleton selected.val)
    simpa only [hSelected, true_and] using hFiber
  · simp [hSelected]

/-- Fixed-count state selection is jointly measurable in the history slice and observation
time. -/
theorem measurable_stateAtTimeVector_uncurry [MeasurableSpace State]
    {eventCount : ℕ} :
    Measurable fun data :
        ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ ↦
      stateAtTimeVector data.1.1 data.1.2 data.2 := by
  let values :
      (((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ) →
        Fin (eventCount + 1) → State := fun data ↦ data.1.1
  let index :
      (((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ) →
        Fin (eventCount + 1) := fun data ↦
      stateIndexAtTimeVector data.1.2 data.2
  exact measurable_variableFiniteEvaluation
    ((measurable_fst.comp measurable_fst) : Measurable values)
    (measurable_stateIndexAtTimeVector_uncurry.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd) : Measurable index)

/-- A history--time observable is jointly measurable when every fixed-count slice is jointly
measurable.  The proof transports the slice family through the natural countable-topological-sum
distribution homeomorphism; it does not truncate the history carrier. -/
theorem measurable_finiteJumpHistory_prod_time_of_fixedCount
    [Fintype State] [_unusedDecidableEqState : DecidableEq State] [MeasurableSpace State]
    [MeasurableSingletonClass State]
    {Target : Type v} [MeasurableSpace Target]
    (observable : FiniteJumpHistory State × ℝ → Target)
    (hObservable : ∀ eventCount : ℕ,
      Measurable fun data :
          ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ ↦
        observable (⟨eventCount, data.1⟩, data.2)) :
    Measurable observable := by
  let : TopologicalSpace State := ⊥
  have : DiscreteTopology State := ⟨rfl⟩
  have : DiscreteMeasurableSpace State := inferInstance
  have : BorelSpace State := inferInstance
  let DistributedHistoryTime :=
    Σ eventCount : ℕ,
      ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ
  have hDistributedHistoryTimeBorel :
      (inferInstance : MeasurableSpace DistributedHistoryTime) =
        borel DistributedHistoryTime := by
    apply le_antisymm
    · intro set hSet
      have hSlices := (measurableSet_sigma_iff set).1 hSet
      let : MeasurableSpace DistributedHistoryTime :=
        borel DistributedHistoryTime
      have : BorelSpace DistributedHistoryTime := ⟨rfl⟩
      have hImages : ∀ eventCount : ℕ,
          MeasurableSet
            (Sigma.mk eventCount '' (Sigma.mk eventCount ⁻¹' set)) := by
        intro eventCount
        exact
          (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image'
            (hSlices eventCount)
      have hUnion :
          set = ⋃ eventCount : ℕ,
            Sigma.mk eventCount '' (Sigma.mk eventCount ⁻¹' set) := by
        ext data
        constructor
        · intro hData
          exact Set.mem_iUnion.2 ⟨data.1, ⟨data.2, hData, rfl⟩⟩
        · intro hData
          rcases Set.mem_iUnion.1 hData with
            ⟨eventCount, value, hValue, hEquality⟩
          simpa [hEquality] using hValue
      rw [hUnion]
      exact MeasurableSet.iUnion hImages
    · apply MeasurableSpace.generateFrom_le
      intro set hOpen
      apply (measurableSet_sigma_iff set).2
      intro eventCount
      exact (isOpen_sigma_iff.1 hOpen eventCount).measurableSet
  let : BorelSpace DistributedHistoryTime :=
    ⟨hDistributedHistoryTimeBorel⟩
  let distributed :
      FiniteJumpHistory State × ℝ ≃ₜ
        DistributedHistoryTime :=
    Homeomorph.sigmaProdDistrib
  let sliced :
      DistributedHistoryTime → Target :=
    fun data ↦ observable (⟨data.1, data.2.1⟩, data.2.2)
  have hSliced : Measurable sliced := by
    rw [measurable_sigma_iff]
    intro eventCount
    exact hObservable eventCount
  exact hSliced.comp distributed.continuous.measurable

/-- State selection is jointly measurable in an unbounded finite history and the physical
observation time. -/
theorem measurable_stateAtTime_uncurry
    [Fintype State] [DecidableEq State] [MeasurableSpace State]
    [MeasurableSingletonClass State] :
    Measurable fun data : FiniteJumpHistory State × ℝ ↦
      data.1.stateAtTime data.2 := by
  apply measurable_finiteJumpHistory_prod_time_of_fixedCount
  intro eventCount
  exact measurable_stateAtTimeVector_uncurry

/-- Fixed-time state selection is measurable on the complete unbounded history carrier. -/
theorem measurable_stateAtTime [MeasurableSpace State] (time : ℝ) :
    Measurable fun history : FiniteJumpHistory State => history.stateAtTime time := by
  rw [measurable_sigma_iff]
  intro eventCount
  exact measurable_stateAtTimeVector time

/-- Exactly `block` event indices precede the corresponding state-word block. -/
theorem sum_eventIndexBeforeStateBlock {eventCount : ℕ}
    (block : Fin (eventCount + 1)) :
    (∑ index : Fin eventCount, if index.val < block.val then 1 else 0) = block.val := by
  induction eventCount with
  | zero => simp
  | succ eventCount inductionHypothesis =>
      refine Fin.cases ?_ (fun preceding : Fin (eventCount + 1) => ?_) block
      · simp
      · rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, ite_true,
          Nat.succ_lt_succ_iff]
        rw [inductionHypothesis preceding]
        omega

/-- Strictly inside one ordered dwell interval, the fixed-time selector returns that interval's
occupied state.  The right endpoint is excluded because the selector is càdlàg. -/
theorem stateAtTimeVector_eq_state_of_mem_dwellInterval {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (duration time : ℝ) (hDuration : 0 ≤ duration)
    (hTimes : times ∈ orderedJumpTimes eventCount duration)
    (block : Fin (eventCount + 1))
    (hLower : boundaryTimeVector duration times block.castSucc ≤ time)
    (hUpper : time < boundaryTimeVector duration times block.succ) :
    stateAtTimeVector states times time = states block := by
  unfold stateAtTimeVector stateIndexAtTimeVector eventCountAtOrBeforeTimeVector
  congr 1
  apply Fin.ext
  have hMonotone :=
    monotone_boundaryTimeVector_of_mem_orderedJumpTimes hDuration hTimes
  have hEvent (index : Fin eventCount) :
      times index ≤ time ↔ index.val < block.val := by
    constructor
    · intro hIndex
      by_contra hNot
      have hOrder : block.succ ≤ index.castSucc.succ := by
        apply Fin.mk_le_mk.mpr
        exact Nat.succ_le_succ (Nat.le_of_not_gt hNot)
      have hBoundary := hMonotone hOrder
      rw [boundaryTimeVector_succ_castSucc] at hBoundary
      linarith
    · intro hIndex
      have hOrder : index.castSucc.succ ≤ block.castSucc := by
        apply Fin.mk_le_mk.mpr
        exact hIndex
      have hBoundary := hMonotone hOrder
      rw [boundaryTimeVector_succ_castSucc] at hBoundary
      linarith
  simp_rw [hEvent]
  exact sum_eventIndexBeforeStateBlock block

/-- Once every jump lies at or before the observation time, fixed-time selection recovers the
final member of the state word. -/
theorem stateAtTimeVector_eq_final_of_forall_le {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (time : ℝ) (hTimes : ∀ index, times index ≤ time) :
    stateAtTimeVector states times time = states (Fin.last eventCount) := by
  unfold stateAtTimeVector stateIndexAtTimeVector
  congr 1
  apply Fin.ext
  simp [eventCountAtOrBeforeTimeVector, hTimes]

/-- At the physical horizon, the càdlàg state selector recovers the complete history's final
state. -/
theorem stateAtTime_eq_finalState_of_orderedBefore
    (history : FiniteJumpHistory State) (duration : ℝ)
    (hOrdered : history.OrderedBefore duration) :
    history.stateAtTime duration = history.finalState := by
  rcases history with ⟨eventCount, states, times⟩
  apply stateAtTimeVector_eq_final_of_forall_le
  intro index
  exact (hOrdered.1 index).2.le

end

end FiniteJumpHistory
