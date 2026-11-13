/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Data.Fin.Rev
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Tactic.Linarith

/-!
# Finite physical-jump histories

This module defines the countable disjoint union of finite state words and ordered jump-time
vectors used as the canonical carrier for finite-horizon Markov jump processes. It also provides
the common counting--Lebesgue base measure and complete time reversal.

The jump count is finite on each history but is not bounded globally. In particular, the carrier
contains the no-jump slice and does not impose a time discretization.

## Main results

- `FiniteJumpHistory`: the unbounded union of finite physical-jump histories.
- `embedJumpTimesOfCountEq`: transport a fixed-count history along an event-count equality.
- `FiniteJumpHistory.noJumpHistory`: the canonical history supported on one state with no jumps.
- `orderedJumpTimes`: the open ordered-time simplex at a fixed horizon.
- `finiteJumpHistoryBaseMeasure`: the common counting--Lebesgue base measure.
- `FiniteJumpHistory.ae_orderedBefore_finiteJumpHistoryBaseMeasure`: the base measure is
  concentrated on the ordered event-time carrier.
- `FiniteJumpHistory.instSigmaFiniteFiniteJumpHistoryBaseMeasure`: sigma-finiteness without a
  jump-count cutoff.
- `FiniteJumpHistory.reverse`: complete state/time reversal at a fixed horizon.
- `FiniteJumpHistory.measurable_reverse`: measurability of reversal.
- `FiniteJumpHistory.abs_dwellTimeVector_le_of_mem_orderedJumpTimes`: every dwell magnitude is
  bounded by the nonnegative observation horizon.
- `FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes`: ordered jump times
  induce a monotone complete boundary vector.
- `FiniteJumpHistory.boundaryTimeVector_castSucc_lt_succ_of_mem_orderedJumpTimes`: every retained
  physical transition strictly separates its preceding and following boundaries.
- `FiniteJumpHistory.dwellTimeVector_nonneg_of_mem_orderedJumpTimes`: every physical dwell is
  nonnegative on the ordered carrier.
- `FiniteJumpHistory.sum_dwellTimeVector`: the complete dwell vector telescopes to the horizon.
- `FiniteJumpHistory.dwellTimeVector_reverseTimes`: reversal permutes the complete dwell vector.
- `FiniteJumpHistory.map_reverse_finiteJumpHistoryBaseMeasure`: the common history base measure
  is invariant under complete time reversal.
-/

@[expose] public section

open MeasureTheory

universe u v

/-- A finite physical-jump history consists of a state word of length `n + 1` and `n` jump
times. The sigma index `n` is unbounded across the carrier. -/
abbrev FiniteJumpHistory (State : Type u) :=
  Σ n : ℕ, (Fin (n + 1) → State) × (Fin n → ℝ)

/-- A function out of a measurable sigma type is measurable exactly when its restriction to
every canonical slice is measurable. -/
theorem measurable_sigma_iff
    {ι : Type u} {β : ι → Type v} {γ : Type*}
    [(i : ι) → MeasurableSpace (β i)] [MeasurableSpace γ]
    {f : (Σ i, β i) → γ} :
    Measurable f ↔ ∀ i, Measurable (f ∘ Sigma.mk i) := by
  constructor
  · intro hf i
    exact hf.comp <| by
      apply Measurable.of_comap_le
      exact (MeasurableSpace.comap_mono (iInf_le _ i)).trans
        MeasurableSpace.comap_map_le
  · intro hf
    apply Measurable.of_comap_le
    apply le_iInf
    intro i
    rw [← MeasurableSpace.comap_le_iff_le_map]
    rw [MeasurableSpace.comap_comp]
    exact (hf i).comap_le

/-- A set in a measurable disjoint union is measurable exactly when its preimage in every
canonical slice is measurable. -/
theorem measurableSet_sigma_iff
    {ι : Type u} {β : ι → Type v} [(ι : ι) → MeasurableSpace (β ι)]
    (set : Set (Sigma β)) :
    MeasurableSet set ↔ ∀ index, MeasurableSet (Sigma.mk index ⁻¹' set) := by
  change @MeasurableSet (Sigma β)
    (⨅ index, MeasurableSpace.map (Sigma.mk index) inferInstance) set ↔ _
  rw [MeasurableSpace.measurableSet_iInf]
  rfl

/-- The open ordered-time simplex for `n` jumps before horizon `T`. -/
def orderedJumpTimes (n : ℕ) (T : ℝ) : Set (Fin n → ℝ) :=
  {times | (∀ i, 0 < times i ∧ times i < T) ∧ StrictMono times}

/-- The ordered-time simplex is Borel measurable. -/
theorem measurableSet_orderedJumpTimes (n : ℕ) (T : ℝ) :
    MeasurableSet (orderedJumpTimes n T) := by
  apply Measurable.setOf
  apply Measurable.and
  · apply Measurable.forall
    intro i
    exact (measurable_const.lt (measurable_pi_apply i)).and
      ((measurable_pi_apply i).lt measurable_const)
  · apply Measurable.forall
    intro i
    apply Measurable.forall
    intro j
    exact measurable_const.imp ((measurable_pi_apply i).lt (measurable_pi_apply j))

/-- Every ordered-time simplex is bounded, including the empty simplex at a nonpositive
horizon. -/
theorem isBounded_orderedJumpTimes (n : ℕ) (T : ℝ) :
    Bornology.IsBounded (orderedJumpTimes n T) := by
  apply (Metric.isBounded_Icc (fun _ : Fin n => min 0 T) (fun _ : Fin n => max 0 T)).subset
  intro times hTimes
  rw [Set.mem_Icc]
  constructor
  · intro i
    exact (min_le_left 0 T).trans (hTimes.1 i).1.le
  · intro i
    exact (hTimes.1 i).2.le.trans (le_max_right 0 T)

/-- Lebesgue measure restricted to one ordered-time simplex is finite. -/
noncomputable instance instIsFiniteMeasureOrderedJumpTimesVolume (n : ℕ) (T : ℝ) :
    IsFiniteMeasure (volume.restrict (orderedJumpTimes n T)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (isBounded_orderedJumpTimes n T).measure_lt_top

/-- Insert a jump-time vector into the slice with fixed jump count and state word. -/
def embedJumpTimes {State : Type u} (n : ℕ) (states : Fin (n + 1) → State)
    (times : Fin n → ℝ) : FiniteJumpHistory State :=
  ⟨n, states, times⟩

/-- Embed a fixed-count history after transporting its state and time coordinates along an
equality of event counts. -/
def embedJumpTimesOfCountEq {State : Type u} {sourceCount targetCount : ℕ}
    (hCount : sourceCount = targetCount)
    (states : Fin (sourceCount + 1) → State) (times : Fin sourceCount → ℝ) :
    FiniteJumpHistory State :=
  embedJumpTimes targetCount
    (fun index ↦ states (Fin.cast (congrArg (· + 1) hCount).symm index))
    (fun index ↦ times (Fin.cast hCount.symm index))

/-- Transporting the coordinates of a fixed-count history does not change the represented
history in the dependent disjoint union. -/
theorem embedJumpTimesOfCountEq_eq {State : Type u} {sourceCount targetCount : ℕ}
    (hCount : sourceCount = targetCount)
    (states : Fin (sourceCount + 1) → State) (times : Fin sourceCount → ℝ) :
    embedJumpTimesOfCountEq hCount states times =
      embedJumpTimes sourceCount states times := by
  subst targetCount
  rfl

/-- Insertion of jump times into a fixed state-word slice is measurable. -/
theorem measurable_embedJumpTimes {State : Type u} [MeasurableSpace State]
    (n : ℕ) (states : Fin (n + 1) → State) :
    Measurable (embedJumpTimes n states) := by
  have hSigma : Measurable
      (@Sigma.mk ℕ (fun k => (Fin (k + 1) → State) × (Fin k → ℝ)) n) := by
    apply Measurable.of_comap_le
    exact (MeasurableSpace.comap_mono (iInf_le _ n)).trans
      MeasurableSpace.comap_map_le
  exact hSigma.comp measurable_prodMk_left

/-- The base measure on one fixed state-word slice: Lebesgue measure restricted to the ordered
time simplex and mapped into the disjoint-union carrier. -/
noncomputable def finiteJumpHistorySliceBaseMeasure
    {State : Type u} [MeasurableSpace State] (T : ℝ) (n : ℕ)
    (states : Fin (n + 1) → State) : Measure (FiniteJumpHistory State) :=
  Measure.map (embedJumpTimes n states) (volume.restrict (orderedJumpTimes n T))

/-- The base measure on all state words with one fixed physical jump count. -/
noncomputable def finiteJumpHistoryCountBaseMeasure
    {State : Type u} [_unusedFintypeState : Fintype State]
    [MeasurableSpace State] (T : ℝ) (n : ℕ) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun states : Fin (n + 1) → State =>
    finiteJumpHistorySliceBaseMeasure T n states

/-- Every fixed state-word slice has finite base mass. -/
noncomputable instance instIsFiniteMeasureFiniteJumpHistorySliceBaseMeasure
    {State : Type u} [MeasurableSpace State] (T : ℝ) (n : ℕ)
    (states : Fin (n + 1) → State) :
    IsFiniteMeasure (finiteJumpHistorySliceBaseMeasure T n states) := by
  unfold finiteJumpHistorySliceBaseMeasure
  exact Measure.isFiniteMeasure_map _ _

/-- The combined base measure at one fixed jump count is finite. -/
noncomputable instance instIsFiniteMeasureFiniteJumpHistoryCountBaseMeasure
    {State : Type u} [Fintype State] [MeasurableSpace State] (T : ℝ) (n : ℕ) :
    IsFiniteMeasure (finiteJumpHistoryCountBaseMeasure (State := State) T n) := by
  refine ⟨?_⟩
  rw [finiteJumpHistoryCountBaseMeasure, Measure.sum_apply _ MeasurableSet.univ,
    tsum_fintype]
  exact ENNReal.sum_lt_top.mpr fun states _ => measure_lt_top _ Set.univ

/-- The common counting--Lebesgue base measure on all finite physical-jump histories. It is a
countable sum over every jump count and state word; no finite jump cutoff is imposed. -/
noncomputable def finiteJumpHistoryBaseMeasure
    (State : Type u) [Fintype State] [MeasurableSpace State] (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun n : ℕ => finiteJumpHistoryCountBaseMeasure T n

namespace FiniteJumpHistory

variable {State : Type u}

/-- Complete boundary times `(0, t_1, ..., t_n, T)` for one jump-time vector. -/
def boundaryTimeVector {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    Fin (n + 2) → ℝ :=
  Fin.cases 0 (Fin.lastCases T times)

/-- The initial member of a complete boundary-time vector is zero. -/
@[simp]
theorem boundaryTimeVector_zero {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    boundaryTimeVector T times 0 = 0 := by
  rfl

/-- Each interior member of a complete boundary-time vector is the corresponding jump time. -/
@[simp]
theorem boundaryTimeVector_succ_castSucc {n : ℕ} (T : ℝ) (times : Fin n → ℝ)
    (index : Fin n) :
    boundaryTimeVector T times index.castSucc.succ = times index := by
  simp [boundaryTimeVector]

/-- The final member of a complete boundary-time vector is the observation horizon. -/
@[simp]
theorem boundaryTimeVector_last {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    boundaryTimeVector T times (Fin.last (n + 1)) = T := by
  rw [boundaryTimeVector]
  change Fin.lastCases T times (Fin.last n) = T
  rw [Fin.lastCases_last]

/-- The `i`th dwell extracted from a complete boundary-time vector. -/
def dwellTimeVector {n : ℕ} (T : ℝ) (times : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  boundaryTimeVector T times i.succ - boundaryTimeVector T times i.castSucc

/-- Every boundary-time coordinate is a measurable function of the jump-time vector. -/
@[fun_prop]
theorem measurable_boundaryTimeVector_apply {n : ℕ} (T : ℝ) (i : Fin (n + 2)) :
    Measurable fun times : Fin n → ℝ => boundaryTimeVector T times i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · convert (measurable_const : Measurable fun _ : Fin n → ℝ => T) using 1
      funext times
      rw [boundaryTimeVector, Fin.cases_succ, Fin.lastCases_last]
    · convert (measurable_pi_apply k : Measurable fun times : Fin n → ℝ => times k) using 1
      funext times
      simp [boundaryTimeVector, Fin.cases_succ]

/-- Every dwell coordinate is a measurable function of the jump-time vector. -/
@[fun_prop]
theorem measurable_dwellTimeVector_apply {n : ℕ} (T : ℝ) (i : Fin (n + 1)) :
    Measurable fun times : Fin n → ℝ => dwellTimeVector T times i :=
  (measurable_boundaryTimeVector_apply T i.succ).sub
    (measurable_boundaryTimeVector_apply T i.castSucc)

/-- Every complete boundary time lies between zero and the horizon on an ordered-time slice. -/
theorem boundaryTimeVector_mem_Icc_of_mem_orderedJumpTimes
    {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes n T)
    (index : Fin (n + 2)) :
    0 ≤ boundaryTimeVector T times index ∧ boundaryTimeVector T times index ≤ T := by
  refine Fin.cases ?_ (fun inner ↦ ?_) index
  · simp [boundaryTimeVector, hT]
  · refine Fin.lastCases ?_ (fun timeIndex ↦ ?_) inner
    · rw [boundaryTimeVector, Fin.cases_succ, Fin.lastCases_last]
      exact ⟨hT, le_rfl⟩
    · simpa [boundaryTimeVector] using
        ⟨(hTimes.1 timeIndex).1.le, (hTimes.1 timeIndex).2.le⟩

/-- The complete boundary-time vector is monotone whenever the physical jump times are ordered
inside a nonnegative horizon. -/
theorem monotone_boundaryTimeVector_of_mem_orderedJumpTimes
    {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes n T) :
    Monotone (boundaryTimeVector T times) := by
  apply Fin.monotone_iff_le_succ.2
  intro index
  cases n with
  | zero =>
      have hIndex : index = 0 := by
        apply Fin.ext
        omega
      subst index
      change boundaryTimeVector T times (0 : Fin 2) ≤
        boundaryTimeVector T times (Fin.last 1)
      rw [boundaryTimeVector_zero, boundaryTimeVector_last]
      exact hT
  | succ n =>
      refine Fin.lastCases ?_ (fun timeIndex ↦ ?_) index
      · have hPredecessor :
            (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ := by
          apply Fin.ext
          rfl
        have hSuccessor :
            (Fin.last (n + 1)).succ = Fin.last (n + 2) := by
          apply Fin.ext
          rfl
        rw [hPredecessor, boundaryTimeVector_succ_castSucc, hSuccessor,
          boundaryTimeVector_last]
        exact (hTimes.1 (Fin.last n)).2.le
      · refine Fin.cases ?_ (fun previous ↦ ?_) timeIndex
        · have hPredecessor :
              (Fin.castSucc (0 : Fin (n + 1))).castSucc = 0 := by
            apply Fin.ext
            rfl
          have hSuccessor :
              (Fin.castSucc (0 : Fin (n + 1))).succ =
                (0 : Fin (n + 1)).castSucc.succ := by
            apply Fin.ext
            rfl
          rw [hPredecessor, boundaryTimeVector_zero, hSuccessor,
            boundaryTimeVector_succ_castSucc]
          exact (hTimes.1 (0 : Fin (n + 1))).1.le
        · have hPredecessor :
              previous.succ.castSucc.castSucc =
                previous.castSucc.castSucc.succ := by
            apply Fin.ext
            rfl
          rw [hPredecessor, boundaryTimeVector_succ_castSucc,
            boundaryTimeVector_succ_castSucc]
          exact (hTimes.2 (Fin.castSucc_lt_succ (i := previous))).le

/-- Every physical transition time lies strictly after the boundary beginning its source dwell. -/
theorem boundaryTimeVector_castSucc_lt_succ_of_mem_orderedJumpTimes
    {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (hTimes : times ∈ orderedJumpTimes n T) (index : Fin n) :
    boundaryTimeVector T times index.castSucc.castSucc <
      boundaryTimeVector T times index.castSucc.succ := by
  cases n with
  | zero => exact Fin.elim0 index
  | succ n =>
      refine Fin.cases ?_ (fun previous ↦ ?_) index
      · have hPredecessor :
            (Fin.castSucc (0 : Fin (n + 1))).castSucc = 0 := by
          apply Fin.ext
          rfl
        have hSuccessor :
            (Fin.castSucc (0 : Fin (n + 1))).succ =
              (0 : Fin (n + 1)).castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hPredecessor, boundaryTimeVector_zero, hSuccessor,
          boundaryTimeVector_succ_castSucc]
        exact (hTimes.1 (0 : Fin (n + 1))).1
      · have hPredecessor :
            previous.succ.castSucc.castSucc =
              previous.castSucc.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hPredecessor, boundaryTimeVector_succ_castSucc,
          boundaryTimeVector_succ_castSucc]
        exact hTimes.2 (Fin.castSucc_lt_succ (i := previous))

/-- Every dwell extracted from an ordered physical jump-time vector is nonnegative. -/
theorem dwellTimeVector_nonneg_of_mem_orderedJumpTimes
    {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes n T)
    (index : Fin (n + 1)) :
    0 ≤ dwellTimeVector T times index := by
  unfold dwellTimeVector
  exact sub_nonneg.mpr <|
    monotone_boundaryTimeVector_of_mem_orderedJumpTimes hT hTimes (Fin.castSucc_le_succ index)

/-- Every dwell magnitude is bounded by the horizon on an ordered-time slice. -/
theorem abs_dwellTimeVector_le_of_mem_orderedJumpTimes
    {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes n T)
    (index : Fin (n + 1)) :
    |dwellTimeVector T times index| ≤ T := by
  have hSuccessor := boundaryTimeVector_mem_Icc_of_mem_orderedJumpTimes
    hT hTimes index.succ
  have hPredecessor := boundaryTimeVector_mem_Icc_of_mem_orderedJumpTimes
    hT hTimes index.castSucc
  unfold dwellTimeVector
  rw [abs_le]
  constructor <;> linarith

/-- The complete dwell vector telescopes to the observation horizon. -/
theorem sum_dwellTimeVector {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    ∑ index : Fin (n + 1), dwellTimeVector T times index = T := by
  unfold dwellTimeVector
  rw [Finset.sum_sub_distrib]
  have hSucc := Fin.sum_univ_succ (boundaryTimeVector T times)
  have hCast := Fin.sum_univ_castSucc (boundaryTimeVector T times)
  have hZero : boundaryTimeVector T times 0 = 0 := by
    simp [boundaryTimeVector]
  have hBoundarySucc (index : Fin (n + 1)) :
      boundaryTimeVector T times index.succ = Fin.lastCases T times index := by
    simp [boundaryTimeVector]
  have hLast : boundaryTimeVector T times (Fin.last (n + 1)) = T := by
    have hIndex : Fin.last (n + 1) = (Fin.last n).succ := by rfl
    rw [hIndex, hBoundarySucc]
    simp
  rw [hZero] at hSucc
  rw [hLast] at hCast
  linarith

/-- The number of physical jumps in a finite history. -/
def jumpCount (history : FiniteJumpHistory State) : ℕ :=
  history.1

/-- The physical jump-count observable is measurable. -/
@[fun_prop]
theorem measurable_jumpCount [MeasurableSpace State] :
    Measurable (jumpCount : FiniteJumpHistory State → ℕ) := by
  rw [measurable_sigma_iff]
  intro n
  exact measurable_const

/-- Histories whose physical jump count is at most `cutoff`. This set is used only to prove
sigma-finiteness; no production law truncates to it. -/
def jumpCountAtMost (cutoff : ℕ) : Set (FiniteJumpHistory State) :=
  {history | history.jumpCount ≤ cutoff}

/-- Every bounded jump-count carrier segment is measurable. -/
theorem measurableSet_jumpCountAtMost [MeasurableSpace State] (cutoff : ℕ) :
    MeasurableSet (jumpCountAtMost (State := State) cutoff) :=
  measurable_jumpCount (State := State) measurableSet_Iic

/-- The complete state word of a finite history. -/
def states (history : FiniteJumpHistory State) :
    Fin (history.jumpCount + 1) → State :=
  history.2.1

/-- The ordered jump-time vector of a finite history. -/
def jumpTimes (history : FiniteJumpHistory State) :
    Fin history.jumpCount → ℝ :=
  history.2.2

/-- The initial state of a finite history. -/
def initialState (history : FiniteJumpHistory State) : State :=
  history.states 0

/-- The canonical finite history that remains in one state and has no jump times. -/
def noJumpHistory (state : State) : FiniteJumpHistory State :=
  embedJumpTimes 0 (fun _ ↦ state) Fin.elim0

/-- A history with zero jump count is the canonical no-jump history at its initial state. -/
theorem eq_noJumpHistory_of_jumpCount_eq_zero
    (history : FiniteJumpHistory State) (hCount : history.jumpCount = 0) :
    history = noJumpHistory history.initialState := by
  rcases history with ⟨eventCount, states, times⟩
  change eventCount = 0 at hCount
  subst eventCount
  unfold noJumpHistory embedJumpTimes initialState
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · funext index
      change states index = states 0
      apply congrArg states
      apply Fin.ext
      change index.1 = 0
      have hIndex := index.isLt
      change index.1 < 1 at hIndex
      omega
    · funext index
      exact Fin.elim0 index

/-- The final state of a finite history. -/
def finalState (history : FiniteJumpHistory State) : State :=
  history.states (Fin.last history.jumpCount)

/-- The boundary-time vector `(0, t_1, ..., t_n, T)` of a finite history. -/
def boundaryTime (history : FiniteJumpHistory State) (T : ℝ) :
    Fin (history.jumpCount + 2) → ℝ :=
  boundaryTimeVector T history.jumpTimes

/-- The dwell time in the `i`th visited state, including the terminal dwell at `i = n`. -/
def dwellTime (history : FiniteJumpHistory State) (T : ℝ)
    (i : Fin (history.jumpCount + 1)) : ℝ :=
  dwellTimeVector T history.jumpTimes i

/-- Whether a history lies in the physical ordered-time slice at horizon `T`. -/
def OrderedBefore (history : FiniteJumpHistory State) (T : ℝ) : Prop :=
  history.jumpTimes ∈ orderedJumpTimes history.jumpCount T

/-- Histories with no virtual jump between equal adjacent occupied states. -/
def Reduced (history : FiniteJumpHistory State) : Prop :=
  ∀ index : Fin history.jumpCount,
    history.states index.castSucc ≠ history.states index.succ

/-- The physical carrier at horizon `T`: strictly ordered event times and genuine state changes. -/
def PhysicalAt (history : FiniteJumpHistory State) (T : ℝ) : Prop :=
  history.OrderedBefore T ∧ history.Reduced

/-- Ordered-before-horizon histories form a measurable subset of the unbounded history carrier. -/
theorem measurableSet_orderedBefore [MeasurableSpace State] (T : ℝ) :
    MeasurableSet {history : FiniteJumpHistory State | history.OrderedBefore T} := by
  apply (measurableSet_sigma_iff _).2
  intro jumpCount
  exact (measurableSet_orderedJumpTimes jumpCount T).preimage measurable_snd

/-- Reduced histories form a measurable subset for a countable state space with measurable
singletons. -/
theorem measurableSet_reduced [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State] :
    MeasurableSet {history : FiniteJumpHistory State | history.Reduced} := by
  apply (measurableSet_sigma_iff _).2
  intro jumpCount
  change MeasurableSet
    {data : (Fin (jumpCount + 1) → State) × (Fin jumpCount → ℝ) |
      ∀ index : Fin jumpCount, data.1 index.castSucc ≠ data.1 index.succ}
  exact (Measurable.forall fun index ↦ Measurable.not <| Measurable.eq
    ((measurable_pi_apply index.castSucc).comp measurable_fst)
    ((measurable_pi_apply index.succ).comp measurable_fst)).setOf

/-- The physical ordered reduced history carrier is measurable. -/
theorem measurableSet_physicalAt [MeasurableSpace State] [Countable State]
    [MeasurableSingletonClass State]
    (T : ℝ) :
    MeasurableSet {history : FiniteJumpHistory State | history.PhysicalAt T} :=
  (measurableSet_orderedBefore T).inter measurableSet_reduced

/-- The canonical counting--Lebesgue history base measure is concentrated on histories whose
event times are strictly ordered before the observation horizon. -/
theorem ae_orderedBefore_finiteJumpHistoryBaseMeasure [Fintype State] [MeasurableSpace State]
    (T : ℝ) :
    ∀ᵐ history ∂ finiteJumpHistoryBaseMeasure State T, history.OrderedBefore T := by
  rw [ae_iff]
  have hMeas : MeasurableSet
      {history : FiniteJumpHistory State | ¬ history.OrderedBefore T} :=
    (measurableSet_orderedBefore T).compl
  unfold finiteJumpHistoryBaseMeasure finiteJumpHistoryCountBaseMeasure
  rw [Measure.sum_apply _ hMeas]
  apply ENNReal.tsum_eq_zero.mpr
  intro jumpCount
  rw [Measure.sum_apply _ hMeas]
  apply ENNReal.tsum_eq_zero.mpr
  intro states
  rw [finiteJumpHistorySliceBaseMeasure,
    Measure.map_apply (measurable_embedJumpTimes jumpCount states) hMeas]
  rw [Measure.restrict_apply
    (hMeas.preimage (measurable_embedJumpTimes jumpCount states))]
  have hEmpty :
      embedJumpTimes jumpCount states ⁻¹'
          {history : FiniteJumpHistory State | ¬ history.OrderedBefore T} ∩
        orderedJumpTimes jumpCount T = ∅ := by
    ext times
    change (¬ times ∈ orderedJumpTimes jumpCount T ∧
      times ∈ orderedJumpTimes jumpCount T) ↔ False
    constructor
    · rintro ⟨hNotOrdered, hOrdered⟩
      exact hNotOrdered hOrdered
    · exact False.elim
  rw [hEmpty, measure_empty]

/-- Reverse a jump-time vector around horizon `T`. -/
def reverseTimes {n : ℕ} (T : ℝ) (times : Fin n → ℝ) : Fin n → ℝ :=
  fun i => T - times i.rev

/-- Reverse the complete state word and reflect all jump times around horizon `T`. -/
def reverse (T : ℝ) : FiniteJumpHistory State → FiniteJumpHistory State
  | ⟨n, stateWord, times⟩ =>
      ⟨n, fun i => stateWord i.rev, reverseTimes T times⟩

/-- Reversing twice returns the original physical history. -/
@[simp]
theorem reverse_reverse (T : ℝ) (history : FiniteJumpHistory State) :
    (history.reverse T).reverse T = history := by
  rcases history with ⟨n, stateWord, times⟩
  simp only [reverse]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp [reverseTimes]

/-- Time reflection preserves the open ordered-time simplex. -/
theorem reverseTimes_mem_orderedJumpTimes {n : ℕ} {T : ℝ} {times : Fin n → ℝ}
    (h : times ∈ orderedJumpTimes n T) :
    reverseTimes T times ∈ orderedJumpTimes n T := by
  rcases h with ⟨hbounds, hmono⟩
  constructor
  · intro i
    constructor
    · dsimp [reverseTimes]
      linarith [hbounds i.rev]
    · dsimp [reverseTimes]
      linarith [hbounds i.rev]
  · intro i j hij
    have hrev : j.rev < i.rev := (Fin.rev_lt_rev).mpr hij
    have htime := hmono hrev
    dsimp [reverseTimes]
    linarith

/-- The complete boundary-time vector is reflected and reversed coordinatewise. -/
theorem boundaryTimeVector_reverseTimes {n : ℕ} (T : ℝ)
    (times : Fin n → ℝ) (i : Fin (n + 2)) :
    boundaryTimeVector T (reverseTimes T times) i =
      T - boundaryTimeVector T times i.rev := by
  unfold boundaryTimeVector
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cases_zero, Fin.rev_zero]
    change 0 = T - Fin.cases 0 (Fin.lastCases T times) (Fin.last n).succ
    rw [Fin.cases_succ, Fin.lastCases_last]
    ring
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.cases_succ, Fin.lastCases_last, Fin.rev_succ, Fin.rev_last]
      change T = T - Fin.cases 0 (Fin.lastCases T times) 0
      rw [Fin.cases_zero]
      ring
    · rw [Fin.cases_succ, Fin.lastCases_castSucc, reverseTimes,
        Fin.rev_succ, Fin.rev_castSucc, Fin.castSucc_succ,
        Fin.cases_succ, Fin.lastCases_castSucc]

/-- Complete reversal permutes the dwell vector by finite-index reversal. -/
theorem dwellTimeVector_reverseTimes {n : ℕ} (T : ℝ)
    (times : Fin n → ℝ) (i : Fin (n + 1)) :
    dwellTimeVector T (reverseTimes T times) i =
      dwellTimeVector T times i.rev := by
  unfold dwellTimeVector
  rw [boundaryTimeVector_reverseTimes, boundaryTimeVector_reverseTimes,
    Fin.rev_succ, Fin.rev_castSucc]
  ring

/-- Complete reversal preserves physical orderedness at the same horizon. -/
theorem orderedBefore_reverse_iff (T : ℝ) (history : FiniteJumpHistory State) :
    (history.reverse T).OrderedBefore T ↔ history.OrderedBefore T := by
  rcases history with ⟨n, stateWord, times⟩
  constructor
  · intro h
    change reverseTimes T times ∈ orderedJumpTimes n T at h
    have twice := reverseTimes_mem_orderedJumpTimes h
    have hreverse : reverseTimes T (reverseTimes T times) = times := by
      funext i
      simp [reverseTimes]
    rw [hreverse] at twice
    change times ∈ orderedJumpTimes n T
    exact twice
  · intro h
    change times ∈ orderedJumpTimes n T at h
    change reverseTimes T times ∈ orderedJumpTimes n T
    exact reverseTimes_mem_orderedJumpTimes h

/-- Complete reversal preserves the absence of virtual jumps. -/
theorem reduced_reverse (T : ℝ) (history : FiniteJumpHistory State)
    (hReduced : history.Reduced) :
    (history.reverse T).Reduced := by
  rcases history with ⟨n, states, times⟩
  intro i hEqual
  change states i.castSucc.rev = states i.succ.rev at hEqual
  rw [Fin.rev_castSucc, Fin.rev_succ] at hEqual
  exact hReduced i.rev hEqual.symm

/-- A history is reduced exactly when its complete reversal is reduced. -/
theorem reduced_reverse_iff (T : ℝ) (history : FiniteJumpHistory State) :
    (history.reverse T).Reduced ↔ history.Reduced := by
  constructor
  · intro hReduced
    have hTwice := reduced_reverse T (history.reverse T) hReduced
    simpa using hTwice
  · exact reduced_reverse T history

/-- Complete reversal preserves the physical history carrier at a fixed horizon. -/
theorem physicalAt_reverse_iff (T : ℝ) (history : FiniteJumpHistory State) :
    (history.reverse T).PhysicalAt T ↔ history.PhysicalAt T := by
  exact and_congr (orderedBefore_reverse_iff T history)
    (reduced_reverse_iff T history)

/-- Complete reversal is measurable on the sigma/disjoint-union history space. -/
theorem measurable_reverse [MeasurableSpace State] (T : ℝ) :
    Measurable (reverse (State := State) T) := by
  rw [measurable_sigma_iff]
  intro n
  have hSigma : Measurable
      (@Sigma.mk ℕ (fun k => (Fin (k + 1) → State) × (Fin k → ℝ)) n) := by
    apply Measurable.of_comap_le
    exact (MeasurableSpace.comap_mono (iInf_le _ n)).trans
      MeasurableSpace.comap_map_le
  apply hSigma.comp
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply i.rev).comp measurable_fst
  · apply Measurable.of_eval
    intro i
    exact measurable_const.sub <| (measurable_pi_apply i.rev).comp measurable_snd

/-- Reverse a finite state word. This involution is used to reindex the counting component of
the common history base measure. -/
def reverseStateWordEquiv (n : ℕ) :
    (Fin (n + 1) → State) ≃ (Fin (n + 1) → State) where
  toFun states i := states i.rev
  invFun states i := states i.rev
  left_inv states := by
    funext i
    simp
  right_inv states := by
    funext i
    simp

/-- Reflection and coordinate reversal preserve finite-dimensional Lebesgue measure. -/
theorem measurePreserving_reverseTimes {n : ℕ} (T : ℝ) :
    MeasurePreserving (reverseTimes (n := n) T)
      (volume : Measure (Fin n → ℝ)) volume := by
  have hPermute :
      MeasurePreserving (fun times : Fin n → ℝ => fun i : Fin n => times i.rev)
        volume volume := by
    convert volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => ℝ) (Fin.revPerm : Equiv.Perm (Fin n)) using 1
    funext times i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hSubtract :
      MeasurePreserving (fun times : Fin n → ℝ => fun i : Fin n => T - times i)
        volume volume := by
    exact volume_preserving_pi
      (fun _ : Fin n => Measure.measurePreserving_sub_left (volume : Measure ℝ) T)
  have hCompose :
      (fun times : Fin n → ℝ => fun i : Fin n => T - times i) ∘
        (fun times : Fin n → ℝ => fun i : Fin n => times i.rev) =
      reverseTimes (n := n) T := by
    funext times i
    rfl
  rw [← hCompose]
  exact hSubtract.comp hPermute

/-- Time reflection belongs to the ordered simplex exactly when the original vector does. -/
theorem reverseTimes_mem_orderedJumpTimes_iff {n : ℕ} {T : ℝ}
    (times : Fin n → ℝ) :
    reverseTimes T times ∈ orderedJumpTimes n T ↔ times ∈ orderedJumpTimes n T := by
  constructor
  · intro hTimes
    have hTwice := reverseTimes_mem_orderedJumpTimes hTimes
    have hReverse : reverseTimes T (reverseTimes T times) = times := by
      funext i
      simp [reverseTimes]
    rwa [hReverse] at hTwice
  · exact reverseTimes_mem_orderedJumpTimes

/-- Time reflection preserves Lebesgue measure restricted to the ordered open simplex. -/
theorem map_reverseTimes_restrict_orderedJumpTimes {n : ℕ} (T : ℝ) :
    Measure.map (reverseTimes (n := n) T)
        (volume.restrict (orderedJumpTimes n T)) =
      volume.restrict (orderedJumpTimes n T) := by
  have hMap := Measure.restrict_map
    (μ := (volume : Measure (Fin n → ℝ)))
    (measurePreserving_reverseTimes (n := n) T).measurable
    (measurableSet_orderedJumpTimes n T)
  rw [(measurePreserving_reverseTimes (n := n) T).map_eq] at hMap
  have hPreimage :
      reverseTimes (n := n) T ⁻¹' orderedJumpTimes n T = orderedJumpTimes n T := by
    ext times
    exact reverseTimes_mem_orderedJumpTimes_iff times
  rw [hPreimage] at hMap
  exact hMap.symm

/-- Complete reversal carries one fixed state-word slice to its reversed state-word slice. -/
theorem map_reverse_finiteJumpHistorySliceBaseMeasure [MeasurableSpace State]
    (T : ℝ) (n : ℕ) (states : Fin (n + 1) → State) :
    Measure.map (reverse (State := State) T)
        (finiteJumpHistorySliceBaseMeasure T n states) =
      finiteJumpHistorySliceBaseMeasure T n (reverseStateWordEquiv n states) := by
  unfold finiteJumpHistorySliceBaseMeasure
  rw [Measure.map_map (measurable_reverse T) (measurable_embedJumpTimes n states)]
  have hComposition :
      reverse (State := State) T ∘ embedJumpTimes n states =
        embedJumpTimes n (reverseStateWordEquiv n states) ∘ reverseTimes T := by
    funext times
    rfl
  rw [hComposition]
  rw [← Measure.map_map
    (measurable_embedJumpTimes n (reverseStateWordEquiv n states))
    (measurePreserving_reverseTimes (n := n) T).measurable]
  rw [map_reverseTimes_restrict_orderedJumpTimes]

/-- Complete reversal preserves the common base measure at one fixed jump count. -/
theorem map_reverse_finiteJumpHistoryCountBaseMeasure [Fintype State]
    [MeasurableSpace State] (T : ℝ) (n : ℕ) :
    Measure.map (reverse (State := State) T)
        (finiteJumpHistoryCountBaseMeasure (State := State) T n) =
      finiteJumpHistoryCountBaseMeasure T n := by
  unfold finiteJumpHistoryCountBaseMeasure
  rw [Measure.map_sum (measurable_reverse T).aemeasurable]
  simp_rw [map_reverse_finiteJumpHistorySliceBaseMeasure]
  apply Measure.ext
  intro event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  exact (reverseStateWordEquiv (State := State) n).tsum_eq
    (fun states => finiteJumpHistorySliceBaseMeasure T n states event)

/-- The unbounded counting--Lebesgue history base measure is invariant under complete time
reversal. -/
theorem map_reverse_finiteJumpHistoryBaseMeasure [Fintype State] [MeasurableSpace State]
    (T : ℝ) :
    Measure.map (reverse (State := State) T) (finiteJumpHistoryBaseMeasure State T) =
      finiteJumpHistoryBaseMeasure State T := by
  unfold finiteJumpHistoryBaseMeasure
  rw [Measure.map_sum (measurable_reverse T).aemeasurable]
  exact Measure.sum_congr fun n => map_reverse_finiteJumpHistoryCountBaseMeasure T n

/-- A fixed-count base measure gives no mass to a jump-count bound below its own count. -/
theorem finiteJumpHistoryCountBaseMeasure_jumpCountAtMost_eq_zero
    [Fintype State] [MeasurableSpace State]
    (T : ℝ) {n cutoff : ℕ} (hCutoff : cutoff < n) :
    finiteJumpHistoryCountBaseMeasure (State := State) T n
        (jumpCountAtMost (State := State) cutoff) = 0 := by
  rw [finiteJumpHistoryCountBaseMeasure,
    Measure.sum_apply _ (measurableSet_jumpCountAtMost cutoff)]
  rw [ENNReal.tsum_eq_zero]
  intro states
  rw [finiteJumpHistorySliceBaseMeasure,
    Measure.map_apply (measurable_embedJumpTimes n states)
      (measurableSet_jumpCountAtMost cutoff)]
  have hPreimage :
      embedJumpTimes n states ⁻¹' jumpCountAtMost (State := State) cutoff = ∅ := by
    ext times
    simp [embedJumpTimes, jumpCountAtMost, jumpCount, hCutoff.not_ge]
  rw [hPreimage, measure_empty]

/-- The unbounded base measure has finite mass on every bounded jump-count carrier segment. -/
theorem finiteJumpHistoryBaseMeasure_jumpCountAtMost_lt_top
    [Fintype State] [MeasurableSpace State] (T : ℝ) (cutoff : ℕ) :
    finiteJumpHistoryBaseMeasure State T
        (jumpCountAtMost (State := State) cutoff) < ⊤ := by
  rw [finiteJumpHistoryBaseMeasure,
    Measure.sum_apply _ (measurableSet_jumpCountAtMost cutoff)]
  rw [tsum_eq_sum (s := Finset.range (cutoff + 1))]
  · refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    calc
      finiteJumpHistoryCountBaseMeasure (State := State) T n
          (jumpCountAtMost (State := State) cutoff) ≤
          finiteJumpHistoryCountBaseMeasure (State := State) T n Set.univ :=
        measure_mono (Set.subset_univ _)
      _ < ⊤ := measure_lt_top _ Set.univ
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    exact finiteJumpHistoryCountBaseMeasure_jumpCountAtMost_eq_zero T
      (Nat.lt_of_succ_le hn)

/-- The common counting--Lebesgue base measure is sigma-finite despite its unbounded jump count. -/
noncomputable instance instSigmaFiniteFiniteJumpHistoryBaseMeasure
    [Fintype State] [MeasurableSpace State] (T : ℝ) :
    SigmaFinite (finiteJumpHistoryBaseMeasure State T) := by
  refine ⟨⟨⟨fun cutoff => jumpCountAtMost (State := State) cutoff,
    fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro cutoff
    exact finiteJumpHistoryBaseMeasure_jumpCountAtMost_lt_top T cutoff
  · apply Set.eq_univ_of_forall
    intro history
    simp only [Set.mem_iUnion, jumpCountAtMost, Set.mem_ofPred_eq]
    exact ⟨history.jumpCount, le_rfl⟩

/-- The natural countable-sum topology on finite histories generates exactly their existing
measurable sigma algebra whenever the finite state space carries its discrete Borel topology. -/
theorem measurableSpace_finiteJumpHistory_eq_borel
    [Countable State] [MeasurableSpace State] [_unusedSingleton : MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] :
    (inferInstance : MeasurableSpace (FiniteJumpHistory State)) =
      borel (FiniteJumpHistory State) := by
  apply le_antisymm
  · intro set hSet
    have hSlices := (measurableSet_sigma_iff set).1 hSet
    let : MeasurableSpace (FiniteJumpHistory State) :=
      borel (FiniteJumpHistory State)
    have : BorelSpace (FiniteJumpHistory State) := ⟨rfl⟩
    have hImages : ∀ jumpCount : ℕ,
        MeasurableSet
          (Sigma.mk jumpCount '' (Sigma.mk jumpCount ⁻¹' set)) := by
      intro jumpCount
      exact
        (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image'
          (hSlices jumpCount)
    have hUnion :
        set = ⋃ jumpCount : ℕ,
          Sigma.mk jumpCount '' (Sigma.mk jumpCount ⁻¹' set) := by
      ext history
      constructor
      · intro hHistory
        exact Set.mem_iUnion.2
          ⟨history.1, ⟨history.2, hHistory, rfl⟩⟩
      · intro hHistory
        rcases Set.mem_iUnion.1 hHistory with
          ⟨jumpCount, value, hValue, hEquality⟩
        simpa [hEquality] using hValue
    rw [hUnion]
    exact MeasurableSet.iUnion hImages
  · apply MeasurableSpace.generateFrom_le
    intro set hOpen
    apply (measurableSet_sigma_iff set).2
    intro jumpCount
    exact (isOpen_sigma_iff.1 hOpen jumpCount).measurableSet

/-- The natural topological-sum history topology is Borel-compatible whenever the state topology
is discrete and Borel-compatible. -/
instance instBorelSpaceFiniteJumpHistoryNatural
    [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] :
    BorelSpace (FiniteJumpHistory State) :=
  ⟨measurableSpace_finiteJumpHistory_eq_borel⟩

/-- Finite-jump histories over a countable measurable state space form a standard Borel space.
The compatible Polish topology is the countable topological sum of the fixed-count slices; it is
used only to certify the existing measurable structure and does not discretize jump times. -/
noncomputable instance instStandardBorelSpaceFiniteJumpHistory
    [Countable State] [MeasurableSpace State] [MeasurableSingletonClass State] :
    StandardBorelSpace (FiniteJumpHistory State) := by
  let : TopologicalSpace State := ⊥
  have : DiscreteTopology State := ⟨rfl⟩
  have : DiscreteMeasurableSpace State := inferInstance
  have : BorelSpace State := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace
      (FiniteJumpHistory State) := inferInstance
  have : SecondCountableTopology (FiniteJumpHistory State) := inferInstance
  infer_instance

end FiniteJumpHistory
