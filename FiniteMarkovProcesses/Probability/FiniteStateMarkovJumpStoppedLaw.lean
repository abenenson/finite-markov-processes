/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpStopping

/-!
# Normalized stopped laws for finite-state Markov jump processes

This module passes from the normalized infinite Gillespie tape to the unbounded finite-history
carrier. It partitions the tape by the first dwell endpoint that reaches the observation horizon,
maps each measurable partition slice through a fixed-jump-count history map, and sums the
resulting pushforwards.

The construction does not impose a jump-count cutoff and does not rely on a proof-dependent total
stopping map. Almost-sure finite-horizon crossing makes the countable stopped measure exactly
normalized. Identification with the canonical counting--Lebesgue density is a subsequent
slice-by-slice theorem.

## Main results

- `FirstCrossesJumpHorizonAt`: measurable first-crossing partition event.
- `finiteStateMarkovStoppedHistoryAt`: measurable fixed-count history map.
- `finiteStateMarkovStoppedHistoryMeasure`: countable stopped-tape pushforward.
- `finiteStateMarkovStoppedHistoryMeasure_univ`: exact normalization without a jump cutoff.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u

/-- The cumulative endpoint at coordinate `jumpCount` reaches the horizon, while every earlier
endpoint remains below it. -/
def FirstCrossesJumpHorizonAt {State : Type u}
    (tape : ℕ → State × ℝ) (T : ℝ) (jumpCount : ℕ) : Prop :=
  T ≤ timedStateCumulativeTime tape (jumpCount + 1) ∧
    ∀ earlier < jumpCount, timedStateCumulativeTime tape (earlier + 1) < T

namespace FiniteStateMarkovStoppedLaw

open Finset Function FiniteMarkovProcesses.Probability ProbabilityTheory Set

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Every fixed first-crossing event is measurable on the timed-state tape. -/
theorem measurableSet_firstCrossesJumpHorizonAt (T : ℝ) (jumpCount : ℕ) :
    MeasurableSet
      {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T jumpCount} := by
  unfold FirstCrossesJumpHorizonAt
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const
      (TimedStateTrajectory.measurable_cumulativeTime (jumpCount + 1))
  · exact (Measurable.forall fun earlier =>
      measurable_const.imp
        ((TimedStateTrajectory.measurable_cumulativeTime (earlier + 1)).lt
          measurable_const)).setOf

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Distinct natural indices cannot both be the first horizon-crossing coordinate. -/
theorem firstCrossesJumpHorizonAt_disjoint {T : ℝ} {first second : ℕ}
    (hNe : first ≠ second) :
    Disjoint
      {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T first}
      {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T second} := by
  rw [Set.disjoint_left]
  intro tape hFirst hSecond
  rcases lt_or_gt_of_ne hNe with hFirstSecond | hSecondFirst
  · exact (not_lt_of_ge hFirst.1) (hSecond.2 first hFirstSecond)
  · exact (not_lt_of_ge hSecond.1) (hFirst.2 second hSecondFirst)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The union of all first-crossing slices is exactly the finite-horizon crossing event. -/
theorem iUnion_firstCrossesJumpHorizonAt (T : ℝ) :
    (⋃ jumpCount : ℕ,
        {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T jumpCount}) =
      {tape | CrossesJumpHorizon tape T} := by
  ext tape
  constructor
  · intro hUnion
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hUnion
    obtain ⟨jumpCount, hCrossing⟩ := hUnion
    exact ⟨jumpCount, hCrossing.1⟩
  · intro hCrosses
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    let first := Nat.find hCrosses
    refine ⟨first, Nat.find_spec hCrosses, ?_⟩
    intro earlier hEarlier
    exact lt_of_not_ge (Nat.find_min hCrosses hEarlier)

/-- Fixed-count stopped history obtained from the tape's occupied states and cumulative dwell
endpoints before the crossing dwell. -/
def finiteStateMarkovStoppedHistoryAt
    (jumpCount : ℕ) (tape : ℕ → State × ℝ) : FiniteJumpHistory State :=
  ⟨jumpCount,
    (fun index => (tape index.1).1),
    (fun index => timedStateCumulativeTime tape (index.1 + 1))⟩

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The stopped-history map at one fixed jump count is measurable. -/
theorem measurable_finiteStateMarkovStoppedHistoryAt (jumpCount : ℕ) :
    Measurable (finiteStateMarkovStoppedHistoryAt (State := State) jumpCount) := by
  have hSigma : Measurable
      (@Sigma.mk ℕ (fun count =>
        (Fin (count + 1) → State) × (Fin count → ℝ)) jumpCount) := by
    apply Measurable.of_comap_le
    exact (MeasurableSpace.comap_mono (iInf_le _ jumpCount)).trans
      MeasurableSpace.comap_map_le
  apply hSigma.comp
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro index
    exact (measurable_pi_apply index.1).fst
  · apply Measurable.of_eval
    intro index
    exact TimedStateTrajectory.measurable_cumulativeTime (index.1 + 1)

/-- The first `jumpCount + 1` occupied states on a tape equal a prescribed state word. -/
def TapeHasStateWord
    (jumpCount : ℕ) (states : Fin (jumpCount + 1) → State)
    (tape : ℕ → State × ℝ) : Prop :=
  ∀ index, (tape index.1).1 = states index

omit [Fintype State] in
/-- A fixed finite tape state-word event is measurable. -/
theorem measurableSet_tapeHasStateWord
    (jumpCount : ℕ) (states : Fin (jumpCount + 1) → State) :
    MeasurableSet {tape : ℕ → State × ℝ | TapeHasStateWord jumpCount states tape} := by
  unfold TapeHasStateWord
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro index
  exact ((measurable_pi_apply index.1 :
    Measurable (fun tape : ℕ → State × ℝ => tape index.1)).fst)
      (measurableSet_singleton (states index))

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Distinct prescribed state words define disjoint tape events. -/
theorem tapeHasStateWord_disjoint
    {jumpCount : ℕ} {first second : Fin (jumpCount + 1) → State}
    (hNe : first ≠ second) :
    Disjoint
      {tape : ℕ → State × ℝ | TapeHasStateWord jumpCount first tape}
      {tape : ℕ → State × ℝ | TapeHasStateWord jumpCount second tape} := by
  rw [Set.disjoint_left]
  intro tape hFirst hSecond
  apply hNe
  funext index
  exact (hFirst index).symm.trans (hSecond index)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Fixed state-word tape events exhaust the complete tape space. -/
theorem iUnion_tapeHasStateWord (jumpCount : ℕ) :
    (⋃ states : Fin (jumpCount + 1) → State,
        {tape : ℕ → State × ℝ | TapeHasStateWord jumpCount states tape}) = Set.univ := by
  ext tape
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨(fun index => (tape index.1).1), fun index => rfl⟩

/-- Cumulative jump-time vector extracted from the first `jumpCount` tape waits. -/
def finiteStateMarkovCumulativeJumpTimesAt
    (jumpCount : ℕ) (tape : ℕ → State × ℝ) : Fin jumpCount → ℝ :=
  fun index => timedStateCumulativeTime tape (index.1 + 1)

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The fixed-count cumulative jump-time map is measurable. -/
theorem measurable_finiteStateMarkovCumulativeJumpTimesAt (jumpCount : ℕ) :
    Measurable (finiteStateMarkovCumulativeJumpTimesAt (State := State) jumpCount) := by
  apply Measurable.of_eval
  intro index
  exact TimedStateTrajectory.measurable_cumulativeTime (index.1 + 1)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a fixed state-word event, the stopped-history map factors through the cumulative-time map
and the canonical state-word slice embedding. -/
theorem finiteStateMarkovStoppedHistoryAt_eq_embedJumpTimes
    (jumpCount : ℕ) (states : Fin (jumpCount + 1) → State)
    (tape : ℕ → State × ℝ) (hWord : TapeHasStateWord jumpCount states tape) :
    finiteStateMarkovStoppedHistoryAt jumpCount tape =
      embedJumpTimes jumpCount states
        (finiteStateMarkovCumulativeJumpTimesAt jumpCount tape) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · funext index
      exact hWord index
    · rfl

/-- Countable stopped-tape pushforward on the unbounded finite-history carrier. Each summand is
the pushforward of the tape law restricted to one measurable first-crossing slice. -/
noncomputable def finiteStateMarkovStoppedHistoryMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun jumpCount : ℕ =>
    Measure.map (finiteStateMarkovStoppedHistoryAt jumpCount)
      ((finiteStateMarkovJumpTapeMeasure initial generator T).restrict
        {tape | FirstCrossesJumpHorizonAt tape T jumpCount})

/-- Decompose the stopped physical-history law into exact jump-count and state-word slices. The
remaining measure on each slice is the cumulative-time pushforward of the corresponding tape
partition. -/
theorem finiteStateMarkovStoppedHistoryMeasure_eq_sum_stateWordSlices
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovStoppedHistoryMeasure initial generator T =
      Measure.sum fun jumpCount : ℕ =>
        Measure.sum fun states : Fin (jumpCount + 1) → State =>
          Measure.map (embedJumpTimes jumpCount states)
            (Measure.map (finiteStateMarkovCumulativeJumpTimesAt jumpCount)
              ((finiteStateMarkovJumpTapeMeasure initial generator T).restrict
                ({tape | FirstCrossesJumpHorizonAt tape T jumpCount} ∩
                  {tape | TapeHasStateWord jumpCount states tape}))) := by
  unfold finiteStateMarkovStoppedHistoryMeasure
  congr 1
  funext jumpCount
  let crossingSet :=
    {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T jumpCount}
  let wordSet := fun states : Fin (jumpCount + 1) → State =>
    {tape : ℕ → State × ℝ | TapeHasStateWord jumpCount states tape}
  have hCrossingSet : MeasurableSet crossingSet :=
    measurableSet_firstCrossesJumpHorizonAt T jumpCount
  have hWordSet (states : Fin (jumpCount + 1) → State) : MeasurableSet (wordSet states) :=
    measurableSet_tapeHasStateWord jumpCount states
  have hPartition : crossingSet = ⋃ states, crossingSet ∩ wordSet states := by
    rw [← Set.inter_iUnion]
    rw [iUnion_tapeHasStateWord, Set.inter_univ]
  have hDisjoint : Pairwise (Disjoint on fun states => crossingSet ∩ wordSet states) := by
    intro first second hNe
    exact (tapeHasStateWord_disjoint hNe).mono Set.inter_subset_right Set.inter_subset_right
  have hRestrict :
      (finiteStateMarkovJumpTapeMeasure initial generator T).restrict crossingSet =
        Measure.sum fun states : Fin (jumpCount + 1) → State =>
          (finiteStateMarkovJumpTapeMeasure initial generator T).restrict
            (crossingSet ∩ wordSet states) := by
    calc
      (finiteStateMarkovJumpTapeMeasure initial generator T).restrict crossingSet =
          (finiteStateMarkovJumpTapeMeasure initial generator T).restrict
            (⋃ states, crossingSet ∩ wordSet states) := by
        exact congrArg
          (fun set => (finiteStateMarkovJumpTapeMeasure initial generator T).restrict set)
          hPartition
      _ = Measure.sum fun states : Fin (jumpCount + 1) → State =>
          (finiteStateMarkovJumpTapeMeasure initial generator T).restrict
            (crossingSet ∩ wordSet states) :=
        Measure.restrict_iUnion hDisjoint fun states => hCrossingSet.inter (hWordSet states)
  rw [hRestrict]
  rw [Measure.map_sum
    (measurable_finiteStateMarkovStoppedHistoryAt jumpCount).aemeasurable]
  congr 1
  funext states
  let stateWordMeasure :=
    (finiteStateMarkovJumpTapeMeasure initial generator T).restrict
      (crossingSet ∩ wordSet states)
  calc
    Measure.map (finiteStateMarkovStoppedHistoryAt jumpCount) stateWordMeasure =
        Measure.map
          (embedJumpTimes jumpCount states ∘
            finiteStateMarkovCumulativeJumpTimesAt jumpCount) stateWordMeasure := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hCrossingSet.inter (hWordSet states))] with tape hTape
      exact finiteStateMarkovStoppedHistoryAt_eq_embedJumpTimes
        jumpCount states tape hTape.2
    _ = Measure.map (embedJumpTimes jumpCount states)
        (Measure.map (finiteStateMarkovCumulativeJumpTimesAt jumpCount) stateWordMeasure) := by
      rw [Measure.map_map (measurable_embedJumpTimes jumpCount states)
        (measurable_finiteStateMarkovCumulativeJumpTimesAt jumpCount)]

/-- The stopped-tape construction is exactly normalized at every nonnegative finite horizon. -/
theorem finiteStateMarkovStoppedHistoryMeasure_univ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    finiteStateMarkovStoppedHistoryMeasure initial generator T Set.univ = 1 := by
  rw [finiteStateMarkovStoppedHistoryMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.map_apply
    (measurable_finiteStateMarkovStoppedHistoryAt (State := State) _)
    MeasurableSet.univ]
  simp_rw [preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [← measure_iUnion]
  · rw [iUnion_firstCrossesJumpHorizonAt]
    have hCrossingAE :=
      FiniteStateMarkovJumpTrajectory.ae_crossesJumpHorizon_finiteStateMarkovJumpTapeMeasure
        initial generator T hT
    rw [ae_iff] at hCrossingAE
    have hCrossingCompl :
        finiteStateMarkovJumpTapeMeasure initial generator T
          {tape | CrossesJumpHorizon tape T}ᶜ = 0 := by
      have hComplement :
          ({tape : ℕ → State × ℝ | CrossesJumpHorizon tape T}ᶜ :
            Set (ℕ → State × ℝ)) =
              {tape | ¬CrossesJumpHorizon tape T} := by
        ext tape
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      rw [hComplement]
      exact hCrossingAE
    rw [measure_of_measure_compl_eq_zero hCrossingCompl, measure_univ]
  · intro first second hNe
    exact firstCrossesJumpHorizonAt_disjoint hNe
  · intro jumpCount
    exact measurableSet_firstCrossesJumpHorizonAt T jumpCount

/-- The normalized stopped finite-history law as a bundled probability measure. -/
noncomputable def finiteStateMarkovStoppedHistoryProbabilityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) : ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateMarkovStoppedHistoryMeasure initial generator T,
    ⟨finiteStateMarkovStoppedHistoryMeasure_univ initial generator T hT⟩⟩

/-- Bundling the stopped law as a probability measure leaves its underlying measure unchanged. -/
@[simp]
theorem finiteStateMarkovStoppedHistoryProbabilityMeasure_toMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    (finiteStateMarkovStoppedHistoryProbabilityMeasure initial generator T hT).toMeasure =
      finiteStateMarkovStoppedHistoryMeasure initial generator T :=
  rfl

end FiniteStateMarkovStoppedLaw
