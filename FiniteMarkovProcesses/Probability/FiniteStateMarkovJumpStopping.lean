/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpTrajectory

/-!
# Stopping timed-state trajectories at a finite horizon

This module isolates the deterministic stopping map needed to pass from an infinite Gillespie
tape to the physical finite-jump carrier. The first dwell whose cumulative endpoint reaches the
horizon determines the finite physical jump count. Earlier cumulative endpoints become the
strictly ordered physical jump times.

No probabilistic nonexplosion claim is hidden in the construction: `CrossesJumpHorizon` is an
explicit premise. A subsequent theorem must prove that premise almost surely under
`finiteStateMarkovJumpTapeMeasure` before the stopped map can identify the physical density law.

## Main results

- `timedStateCumulativeTime`: cumulative dwell time before a tape coordinate.
- `CrossesJumpHorizon`: explicit finite-horizon crossing predicate.
- `finiteStateMarkovStoppedHistory`: physical history cut at the first crossing.
- `finiteStateMarkovStoppedHistory_orderedBefore`: exact ordered-simplex membership.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

universe u

/-- Cumulative duration of the first `n` dwells on an infinite timed-state tape. -/
def timedStateCumulativeTime {State : Type u} (tape : ℕ → State × ℝ) (n : ℕ) : ℝ :=
  ∑ index ∈ Finset.range n, (tape index).2

/-- Every dwell duration on a timed-state tape is strictly positive. -/
def HasPositiveWaitingTimes {State : Type u} (tape : ℕ → State × ℝ) : Prop :=
  ∀ index, 0 < (tape index).2

/-- Every dwell duration on a timed-state tape is strictly shorter than a fixed block length. -/
def HasShortWaitingTimes {State : Type u}
    (blockLength : ℝ) (tape : ℕ → State × ℝ) : Prop :=
  ∀ index, (tape index).2 < blockLength

/-- Some finite cumulative dwell endpoint reaches the observation horizon. This is the exact
samplewise nonexplosion premise consumed by the stopping map. -/
def CrossesJumpHorizon {State : Type u} (tape : ℕ → State × ℝ) (T : ℝ) : Prop :=
  ∃ index, T ≤ timedStateCumulativeTime tape (index + 1)

namespace TimedStateTrajectory

variable {State : Type u}

/-- The empty cumulative duration is zero. -/
@[simp]
theorem cumulativeTime_zero (tape : ℕ → State × ℝ) :
    timedStateCumulativeTime tape 0 = 0 := by
  simp [timedStateCumulativeTime]

/-- Appending one dwell adds exactly its duration. -/
theorem cumulativeTime_succ (tape : ℕ → State × ℝ) (n : ℕ) :
    timedStateCumulativeTime tape (n + 1) =
      timedStateCumulativeTime tape n + (tape n).2 := by
  simp [timedStateCumulativeTime, Finset.sum_range_succ]

/-- Positive dwells make cumulative time strictly increasing. -/
theorem cumulativeTime_strictMono {tape : ℕ → State × ℝ}
    (hPositive : HasPositiveWaitingTimes tape) :
    StrictMono (timedStateCumulativeTime tape) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [cumulativeTime_succ]
  linarith [hPositive n]

variable [MeasurableSpace State]

/-- Every fixed cumulative-time coordinate is measurable on the tape carrier. -/
@[fun_prop]
theorem measurable_cumulativeTime (n : ℕ) :
    Measurable (fun tape : ℕ → State × ℝ => timedStateCumulativeTime tape n) := by
  unfold timedStateCumulativeTime
  fun_prop

/-- Strict positivity of every waiting coordinate is a measurable tape event. -/
theorem measurableSet_hasPositiveWaitingTimes :
    MeasurableSet {tape : ℕ → State × ℝ | HasPositiveWaitingTimes tape} := by
  unfold HasPositiveWaitingTimes
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt measurable_const ((measurable_pi_apply n).snd)

/-- Uniform strict boundedness of every waiting coordinate is a measurable tape event. -/
theorem measurableSet_hasShortWaitingTimes (blockLength : ℝ) :
    MeasurableSet {tape : ℕ → State × ℝ | HasShortWaitingTimes blockLength tape} := by
  unfold HasShortWaitingTimes
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt ((measurable_pi_apply n).snd) measurable_const

/-- Finite-horizon crossing is a measurable tape event. -/
theorem measurableSet_crossesJumpHorizon (T : ℝ) :
    MeasurableSet {tape : ℕ → State × ℝ | CrossesJumpHorizon tape T} := by
  unfold CrossesJumpHorizon
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_le measurable_const (measurable_cumulativeTime (n + 1))

end TimedStateTrajectory

namespace FiniteStateMarkovJumpTrajectory

open Finset Function FiniteMarkovProcesses.Probability ProbabilityTheory Set

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Every timed coordinate in a finite trajectory prefix has a positive dwell. -/
def HasPositivePrefixWaitingTimes
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) : Prop :=
  ∀ index, 0 < (history index).2

/-- Every timed coordinate in a finite trajectory prefix is shorter than a fixed block length. -/
def HasShortPrefixWaitingTimes
    (blockLength : ℝ) (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) : Prop :=
  ∀ index, (history index).2 < blockLength

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Positivity of all waits in a finite trajectory prefix is measurable. -/
theorem measurableSet_hasPositivePrefixWaitingTimes (n : ℕ) :
    MeasurableSet
      {history : (i : Finset.Iic n) → State × ℝ |
        HasPositivePrefixWaitingTimes n history} := by
  unfold HasPositivePrefixWaitingTimes
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro index
  exact measurableSet_lt measurable_const ((measurable_pi_apply index).snd)

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Boundedness of all waits in a finite trajectory prefix is measurable. -/
theorem measurableSet_hasShortPrefixWaitingTimes (blockLength : ℝ) (n : ℕ) :
    MeasurableSet
      {history : (i : Finset.Iic n) → State × ℝ |
        HasShortPrefixWaitingTimes blockLength n history} := by
  unfold HasShortPrefixWaitingTimes
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro index
  exact measurableSet_lt ((measurable_pi_apply index).snd) measurable_const

omit [Fintype State] [MeasurableSingletonClass State] in
/-- A successor prefix is uniformly short exactly when its old prefix and new wait are both
short. -/
theorem hasShortPrefixWaitingTimes_IicProdIoc_iff
    (blockLength : ℝ) (n : ℕ)
    (history : (i : Finset.Iic n) → State × ℝ) (next : State × ℝ) :
    HasShortPrefixWaitingTimes blockLength (n + 1)
        ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => State × ℝ) (Nat.le_succ n))
          (history,
            MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n next)) ↔
      HasShortPrefixWaitingTimes blockLength n history ∧ next.2 < blockLength := by
  constructor
  · intro hSuccessor
    constructor
    · intro index
      have hIndex : index.1 ≤ n := Finset.mem_Iic.mp index.2
      simpa [MeasurableEquiv.IicProdIoc, hIndex] using
        hSuccessor ⟨index.1,
          Finset.mem_Iic.mpr (hIndex.trans (Nat.le_succ n))⟩
    · have hIndex : ¬n + 1 ≤ n := Nat.not_succ_le_self n
      simpa [finiteTrajectoryCurrentIndex, MeasurableEquiv.IicProdIoc,
        MeasurableEquiv.piSingleton, hIndex] using
        hSuccessor (finiteTrajectoryCurrentIndex (n + 1))
  · rintro ⟨hPrefix, hNext⟩ index
    by_cases hIndex : index.1 ≤ n
    · simpa [MeasurableEquiv.IicProdIoc, hIndex] using
        hPrefix ⟨index.1, Finset.mem_Iic.mpr hIndex⟩
    · simpa [MeasurableEquiv.IicProdIoc, hIndex,
        MeasurableEquiv.piSingleton] using hNext

/-- One Ionescu--Tulcea successor is a uniformly short prefix exactly by retaining a short old
prefix and drawing one short new wait. -/
theorem partialTraj_succ_shortPrefix_apply
    (generator : FiniteStateMarkovGenerator State) (T blockLength : ℝ)
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) :
    Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) n (n + 1) history
        {extended | HasShortPrefixWaitingTimes blockLength (n + 1) extended} =
      Set.indicator
        {oldHistory | HasShortPrefixWaitingTimes blockLength n oldHistory}
        (fun _ => finiteStateTimedStepKernel generator T
          (finiteTimedTrajectoryCurrentState n history)
          {next | next.2 < blockLength}) history := by
  let combine := IicProdIoc (X := fun _ : ℕ => State × ℝ) n (n + 1)
  have hCombineMeasurable : Measurable combine :=
    measurable_IicProdIoc (X := fun _ : ℕ => State × ℝ)
  have hSuccessorSet : MeasurableSet
      {extended | HasShortPrefixWaitingTimes blockLength (n + 1) extended} :=
    measurableSet_hasShortPrefixWaitingTimes (State := State) blockLength (n + 1)
  have hFixedPrefixSet : MeasurableSet
      {singleton |
        HasShortPrefixWaitingTimes blockLength (n + 1)
          (combine (history, singleton))} :=
    (hSuccessorSet.preimage hCombineMeasurable).preimage measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hCombineMeasurable]
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  rw [Measure.map_apply hCombineMeasurable hSuccessorSet]
  rw [Measure.map_apply measurable_prodMk_left
    (hSuccessorSet.preimage hCombineMeasurable)]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => State × ℝ) n).measurable]
  change (Measure.map
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n)
      ((finiteStateMarkovJumpTrajectoryStepKernel generator T n) history))
      {singleton |
        HasShortPrefixWaitingTimes blockLength (n + 1)
          (combine (history, singleton))} = _
  rw [Measure.map_apply
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => State × ℝ) n).measurable hFixedPrefixSet]
  rw [finiteStateMarkovJumpTrajectoryStepKernel, Kernel.comap_apply]
  by_cases hPrefix : HasShortPrefixWaitingTimes blockLength n history
  · rw [Set.indicator_of_mem hPrefix]
    congr 1
    ext next
    change HasShortPrefixWaitingTimes blockLength (n + 1)
        (combine (history,
          MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n next)) ↔
      next.2 < blockLength
    simpa [combine, MeasurableEquiv.coe_IicProdIoc, hPrefix] using
      hasShortPrefixWaitingTimes_IicProdIoc_iff blockLength n history next
  · rw [Set.indicator_of_notMem hPrefix]
    have hSet :
        {next |
          HasShortPrefixWaitingTimes blockLength (n + 1)
            (combine (history,
              MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n next))} =
          (∅ : Set (State × ℝ)) := by
      ext next
      simpa [combine, MeasurableEquiv.coe_IicProdIoc, hPrefix] using
        hasShortPrefixWaitingTimes_IicProdIoc_iff blockLength n history next
    change finiteStateTimedStepKernel generator T
        (finiteTimedTrajectoryCurrentState n history)
        {next |
          HasShortPrefixWaitingTimes blockLength (n + 1)
            (combine (history,
              MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n next))} = 0
    rw [hSet, measure_empty]

/-- At one extension step, a short successor prefix costs at most one uniform geometric
short-wait factor, and costs zero when the old prefix was already long. -/
theorem partialTraj_succ_horizonShortPrefix_le
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) :
    Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) n (n + 1) history
        {extended |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) (n + 1) extended} ≤
      Set.indicator
        {oldHistory |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n oldHistory}
        (fun _ => finiteStateShortWaitBound generator T) history := by
  rw [partialTraj_succ_shortPrefix_apply]
  by_cases hPrefix :
      HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history
  · have hMem : history ∈
        {oldHistory |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n oldHistory} :=
      hPrefix
    rw [Set.indicator_of_mem hMem, Set.indicator_of_mem hMem]
    exact finiteStateTimedStepKernel_shortWait_le generator T
      (finiteTimedTrajectoryCurrentState n history)
  · have hNotMem : history ∉
        {oldHistory |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n oldHistory} :=
      hPrefix
    rw [Set.indicator_of_notMem hNotMem, Set.indicator_of_notMem hNotMem]

/-- The probability that every coordinate through `n` remains short is bounded by the `n`th
power of the uniform one-step factor, with zero mass when the supplied seed is not short. -/
theorem partialTraj_horizonShortPrefix_le_indicatorPow
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (seed : (i : Finset.Iic 0) → State × ℝ)
    (n : ℕ) :
    Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed
        {history |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history} ≤
      Set.indicator
        {initialSeed |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 initialSeed}
        (fun _ => finiteStateShortWaitBound generator T ^ n) seed := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply]
      rw [Measure.dirac_apply' _
        (measurableSet_hasShortPrefixWaitingTimes (State := State)
          (finiteJumpHorizonBlockLength T) 0)]
      exact le_rfl
  | succ n inductionHypothesis =>
      have hPrefixSet : MeasurableSet
          {history : (i : Finset.Iic n) → State × ℝ |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history} :=
        measurableSet_hasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) n
      have hSuccessorSet : MeasurableSet
          {history : (i : Finset.Iic (n + 1)) → State × ℝ |
            HasShortPrefixWaitingTimes
              (finiteJumpHorizonBlockLength T) (n + 1) history} :=
        measurableSet_hasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) (n + 1)
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]
      rw [Kernel.comp_apply' _ _ _ hSuccessorSet]
      calc
        (∫⁻ history,
            Kernel.partialTraj (X := fun _ => State × ℝ)
              (finiteStateMarkovJumpTrajectoryStepKernel generator T)
              n (n + 1) history
              {extended |
                HasShortPrefixWaitingTimes
                  (finiteJumpHorizonBlockLength T) (n + 1) extended}
            ∂Kernel.partialTraj (X := fun _ => State × ℝ)
              (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed) ≤
            ∫⁻ history,
              Set.indicator
                {oldHistory |
                  HasShortPrefixWaitingTimes
                    (finiteJumpHorizonBlockLength T) n oldHistory}
                (fun _ => finiteStateShortWaitBound generator T) history
              ∂Kernel.partialTraj (X := fun _ => State × ℝ)
                (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed :=
          lintegral_mono fun history =>
            partialTraj_succ_horizonShortPrefix_le generator T n history
        _ = finiteStateShortWaitBound generator T *
            Kernel.partialTraj (X := fun _ => State × ℝ)
              (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed
              {history |
                HasShortPrefixWaitingTimes
                  (finiteJumpHorizonBlockLength T) n history} := by
          rw [lintegral_indicator_const hPrefixSet]
        _ ≤ finiteStateShortWaitBound generator T *
            Set.indicator
              {initialSeed |
                HasShortPrefixWaitingTimes
                  (finiteJumpHorizonBlockLength T) 0 initialSeed}
              (fun _ => finiteStateShortWaitBound generator T ^ n) seed :=
          (mul_le_mul_right inductionHypothesis) (finiteStateShortWaitBound generator T)
        _ = Set.indicator
            {initialSeed |
              HasShortPrefixWaitingTimes
                (finiteJumpHorizonBlockLength T) 0 initialSeed}
            (fun _ => finiteStateShortWaitBound generator T ^ (n + 1)) seed := by
          by_cases hSeed :
              HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed
          · have hMem : seed ∈
                {initialSeed |
                  HasShortPrefixWaitingTimes
                    (finiteJumpHorizonBlockLength T) 0 initialSeed} :=
              hSeed
            rw [Set.indicator_of_mem hMem, Set.indicator_of_mem hMem, pow_succ, mul_comm]
          · have hNotMem : seed ∉
                {initialSeed |
                  HasShortPrefixWaitingTimes
                    (finiteJumpHorizonBlockLength T) 0 initialSeed} :=
              hSeed
            rw [Set.indicator_of_notMem hNotMem, Set.indicator_of_notMem hNotMem, mul_zero]

/-- Starting from a short seed, the probability that every coordinate through `n` remains
short is bounded by the `n`th power of the uniform one-step factor. -/
theorem partialTraj_horizonShortPrefix_le_pow
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (seed : (i : Finset.Iic 0) → State × ℝ)
    (hSeed : HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed)
    (n : ℕ) :
    Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed
        {history |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history} ≤
      finiteStateShortWaitBound generator T ^ n := by
  have hMem : seed ∈
      {initialSeed |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 initialSeed} :=
    hSeed
  simpa only [Set.indicator_of_mem hMem] using
    partialTraj_horizonShortPrefix_le_indicatorPow generator T seed n

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The singleton seed prefix is short exactly when its embedded timed state is short. -/
theorem hasShortPrefixWaitingTimes_finiteStateMarkovJumpTrajectorySeed_iff
    (T : ℝ) (timedState : State × ℝ) :
    HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0
        (finiteStateMarkovJumpTrajectorySeed timedState) ↔
      timedState.2 < finiteJumpHorizonBlockLength T := by
  constructor
  · intro hShort
    exact hShort (finiteTrajectoryCurrentIndex 0)
  · intro hShort index
    exact hShort

/-- The normalized trajectory seed is short with probability at most one uniform geometric
factor. -/
theorem finiteStateMarkovJumpTrajectorySeedMeasure_horizonShort_le
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpTrajectorySeedMeasure initial generator T
        {seed |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed} ≤
      finiteStateShortWaitBound generator T := by
  have hSeedSet : MeasurableSet
      {seed : (i : Finset.Iic 0) → State × ℝ |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed} :=
    measurableSet_hasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0
  rw [finiteStateMarkovJumpTrajectorySeedMeasure]
  rw [Measure.map_apply measurable_finiteStateMarkovJumpTrajectorySeed hSeedSet]
  change finiteStateInitialTimedStateMeasure initial generator T
      {timedState |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0
          (finiteStateMarkovJumpTrajectorySeed timedState)} ≤
    finiteStateShortWaitBound generator T
  have hSet :
      {timedState : State × ℝ |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0
          (finiteStateMarkovJumpTrajectorySeed timedState)} =
        {timedState : State × ℝ | timedState.2 < finiteJumpHorizonBlockLength T} := by
    ext timedState
    exact hasShortPrefixWaitingTimes_finiteStateMarkovJumpTrajectorySeed_iff T timedState
  rw [hSet]
  exact finiteStateInitialTimedStateMeasure_shortWait_le initial generator T

/-- Every finite cylinder in which all Gillespie waits through coordinate `n` are shorter than
the horizon block has probability at most the corresponding `(n + 1)`st geometric power. -/
theorem finiteStateMarkovJumpTapeMeasure_horizonShortPrefix_le_pow
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    finiteStateMarkovJumpTapeMeasure initial generator T
        {tape |
          HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n
            (Preorder.frestrictLe n tape)} ≤
      finiteStateShortWaitBound generator T ^ (n + 1) := by
  have hPrefixSet : MeasurableSet
      {history : (i : Finset.Iic n) → State × ℝ |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history} :=
    measurableSet_hasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n
  have hTapeSet : MeasurableSet
      {tape : ℕ → State × ℝ |
        HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n
          (Preorder.frestrictLe n tape)} :=
    hPrefixSet.preimage (Preorder.measurable_frestrictLe n)
  rw [finiteStateMarkovJumpTapeMeasure]
  rw [Measure.bind_apply hTapeSet (Kernel.aemeasurable _)]
  have hTrajectoryApply (seed : (i : Finset.Iic 0) → State × ℝ) :
      Kernel.traj (X := fun _ => State × ℝ)
          (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 seed
          {tape |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n
              (Preorder.frestrictLe n tape)} =
        Kernel.partialTraj (X := fun _ => State × ℝ)
          (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed
          {history |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history} := by
    change Kernel.traj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 seed
        (Preorder.frestrictLe n ⁻¹'
          {history |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history}) = _
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe n) hPrefixSet]
    rw [Kernel.traj_map_frestrictLe_apply]
  simp_rw [hTrajectoryApply]
  calc
    (∫⁻ seed,
        Kernel.partialTraj (X := fun _ => State × ℝ)
          (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed
          {history |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n history}
        ∂finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) ≤
        ∫⁻ seed,
          Set.indicator
            {initialSeed |
              HasShortPrefixWaitingTimes
                (finiteJumpHorizonBlockLength T) 0 initialSeed}
            (fun _ => finiteStateShortWaitBound generator T ^ n) seed
          ∂finiteStateMarkovJumpTrajectorySeedMeasure initial generator T :=
      lintegral_mono fun seed =>
        partialTraj_horizonShortPrefix_le_indicatorPow generator T seed n
    _ = finiteStateShortWaitBound generator T ^ n *
        finiteStateMarkovJumpTrajectorySeedMeasure initial generator T
          {seed |
            HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed} := by
      rw [lintegral_indicator_const
        (measurableSet_hasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) 0)]
    _ ≤ finiteStateShortWaitBound generator T ^ n *
        finiteStateShortWaitBound generator T :=
      (mul_le_mul_right
        (finiteStateMarkovJumpTrajectorySeedMeasure_horizonShort_le
          initial generator T)) (finiteStateShortWaitBound generator T ^ n)
    _ = finiteStateShortWaitBound generator T ^ (n + 1) := by
      rw [pow_succ]

/-- The event that every coordinate of the infinite Gillespie tape is shorter than the horizon
block has probability zero. This is the quantitative finite-state nonexplosion estimate. -/
theorem finiteStateMarkovJumpTapeMeasure_allHorizonWaitsShort
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpTapeMeasure initial generator T
        {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} = 0 := by
  have hMeasureLe (n : ℕ) :
      finiteStateMarkovJumpTapeMeasure initial generator T
          {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} ≤
        finiteStateShortWaitBound generator T ^ (n + 1) := by
    calc
      finiteStateMarkovJumpTapeMeasure initial generator T
          {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} ≤
          finiteStateMarkovJumpTapeMeasure initial generator T
            {tape |
              HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) n
                (Preorder.frestrictLe n tape)} := by
        apply measure_mono
        intro tape hAll index
        simpa [HasShortWaitingTimes, Preorder.frestrictLe_apply] using hAll index.1
      _ ≤ finiteStateShortWaitBound generator T ^ (n + 1) :=
        finiteStateMarkovJumpTapeMeasure_horizonShortPrefix_le_pow
          initial generator T n
  apply le_antisymm
  · have hMeasureLePow (n : ℕ) :
        finiteStateMarkovJumpTapeMeasure initial generator T
            {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} ≤
          finiteStateShortWaitBound generator T ^ n := by
      refine (hMeasureLe n).trans ?_
      rw [pow_succ]
      calc
        finiteStateShortWaitBound generator T ^ n *
            finiteStateShortWaitBound generator T ≤
            finiteStateShortWaitBound generator T ^ n * 1 :=
          (mul_le_mul_right
            (finiteStateShortWaitBound_lt_one generator T).le)
            (finiteStateShortWaitBound generator T ^ n)
        _ = finiteStateShortWaitBound generator T ^ n := by
          rw [mul_one]
    exact ge_of_tendsto'
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (finiteStateShortWaitBound_lt_one generator T)) hMeasureLePow
  · exact bot_le

/-- Almost every normalized Gillespie tape contains a wait at least as long as the horizon
block. -/
theorem ae_exists_horizonBlock_le_wait_finiteStateMarkovJumpTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ∀ᵐ tape ∂finiteStateMarkovJumpTapeMeasure initial generator T,
      ∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2 := by
  rw [ae_iff]
  change finiteStateMarkovJumpTapeMeasure initial generator T
      {tape | ¬∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2} = 0
  have hSet :
      {tape : ℕ → State × ℝ |
        ¬∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2} =
        {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} := by
    ext tape
    simp only [Set.mem_ofPred_eq, not_exists, not_le, HasShortWaitingTimes]
  rw [hSet]
  exact finiteStateMarkovJumpTapeMeasure_allHorizonWaitsShort initial generator T

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Positive waits together with one horizon-block-sized wait force a finite cumulative-time
crossing. -/
theorem crossesJumpHorizon_of_exists_horizonBlock_le_wait
    {tape : ℕ → State × ℝ} {T : ℝ}
    (hPositive : HasPositiveWaitingTimes tape)
    (hLong : ∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2) :
    CrossesJumpHorizon tape T := by
  obtain ⟨index, hIndex⟩ := hLong
  refine ⟨index, ?_⟩
  rw [TimedStateTrajectory.cumulativeTime_succ]
  have hPrior : 0 ≤ timedStateCumulativeTime tape index := by
    unfold timedStateCumulativeTime
    exact Finset.sum_nonneg fun waitIndex _ => (hPositive waitIndex).le
  have hBlock : T < finiteJumpHorizonBlockLength T := by
    unfold finiteJumpHorizonBlockLength
    linarith [le_max_left T 0]
  linarith

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Combining a positive prefix with one positive new wait produces a positive successor
prefix. -/
theorem hasPositivePrefixWaitingTimes_IicProdIoc
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) (next : State × ℝ)
    (hPrefix : HasPositivePrefixWaitingTimes n history) (hNext : 0 < next.2) :
    HasPositivePrefixWaitingTimes (n + 1)
      ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => State × ℝ) (Nat.le_succ n))
        (history,
          MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n next)) := by
  intro index
  by_cases hIndex : index.1 ≤ n
  · simpa [MeasurableEquiv.IicProdIoc, hIndex] using
      hPrefix ⟨index.1, Finset.mem_Iic.mpr hIndex⟩
  · simpa [MeasurableEquiv.IicProdIoc, hIndex,
      MeasurableEquiv.piSingleton] using hNext

/-- One Ionescu--Tulcea extension step preserves positivity of every prefix wait almost surely. -/
theorem ae_hasPositivePrefixWaitingTimes_partialTraj_succ
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ)
    (hPrefix : HasPositivePrefixWaitingTimes n history) :
    ∀ᵐ extended ∂Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) n (n + 1) history,
      HasPositivePrefixWaitingTimes (n + 1) extended := by
  let combine := IicProdIoc (X := fun _ : ℕ => State × ℝ) n (n + 1)
  have hCombineMeasurable : Measurable combine :=
    measurable_IicProdIoc (X := fun _ : ℕ => State × ℝ)
  have hCombinedSet : MeasurableSet
      {pair | HasPositivePrefixWaitingTimes (n + 1) (combine pair)} :=
    (measurableSet_hasPositivePrefixWaitingTimes (State := State) (n + 1)).preimage
      hCombineMeasurable
  have hFixedPrefixSet : MeasurableSet
      {singleton | HasPositivePrefixWaitingTimes (n + 1) (combine (history, singleton))} :=
    hCombinedSet.preimage measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _
    (measurable_IicProdIoc (X := fun _ : ℕ => State × ℝ))]
  apply (ae_map_iff hCombineMeasurable.aemeasurable
    (measurableSet_hasPositivePrefixWaitingTimes (State := State) (n + 1))).2
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable hCombinedSet).2
  rw [Kernel.map_apply _
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => State × ℝ) n).measurable]
  apply (ae_map_iff
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ => State × ℝ) n).measurable.aemeasurable hFixedPrefixSet).2
  filter_upwards [FiniteMarkovProcesses.Probability.ae_positive_finiteStateTimedStepKernel
    generator T hT
    (finiteTimedTrajectoryCurrentState n history)] with next hNext
  exact hasPositivePrefixWaitingTimes_IicProdIoc n history next hPrefix hNext

/-- Starting from a positive seed, every finite trajectory marginal has positive waits almost
surely. -/
theorem ae_hasPositivePrefixWaitingTimes_partialTraj
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T)
    (seed : (i : Finset.Iic 0) → State × ℝ)
    (hSeed : HasPositivePrefixWaitingTimes 0 seed) (n : ℕ) :
    ∀ᵐ history ∂Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed,
      HasPositivePrefixWaitingTimes n history := by
  induction n with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.id_apply]
      exact (ae_dirac_iff
        (measurableSet_hasPositivePrefixWaitingTimes (State := State) 0)).2 hSeed
  | succ n inductionHypothesis =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]
      change ∀ᵐ extended ∂Kernel.partialTraj (X := fun _ => State × ℝ)
          (finiteStateMarkovJumpTrajectoryStepKernel generator T) n (n + 1) ∘ₘ
            Kernel.partialTraj (X := fun _ => State × ℝ)
              (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n seed,
        HasPositivePrefixWaitingTimes (n + 1) extended
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_hasPositivePrefixWaitingTimes (State := State) (n + 1))
      filter_upwards [inductionHypothesis] with history hPrefix
      exact ae_hasPositivePrefixWaitingTimes_partialTraj_succ
        generator T hT n history hPrefix

/-- A positive one-coordinate seed generates an infinite trajectory with positive waits at every
coordinate almost surely. -/
theorem ae_hasPositiveWaitingTimes_traj
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T)
    (seed : (i : Finset.Iic 0) → State × ℝ)
    (hSeed : HasPositivePrefixWaitingTimes 0 seed) :
    ∀ᵐ tape ∂Kernel.traj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 seed,
      HasPositiveWaitingTimes tape := by
  apply ae_all_iff.2
  intro n
  have hPrefix :=
    (ae_hasPositivePrefixWaitingTimes_partialTraj generator T hT seed hSeed n).mono
      (fun history hPositive => hPositive (finiteTrajectoryCurrentIndex n))
  rw [← Kernel.traj_map_frestrictLe_apply] at hPrefix
  have hTape := (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
    (measurable_const.lt
      ((measurable_pi_apply (finiteTrajectoryCurrentIndex n)).snd)).setOf).1 hPrefix
  simpa [HasPositiveWaitingTimes, Preorder.frestrictLe_apply,
    finiteTrajectoryCurrentIndex] using hTape

/-- The normalized initial seed has a positive unique wait almost surely. -/
theorem ae_hasPositivePrefixWaitingTimes_seedMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ seed ∂finiteStateMarkovJumpTrajectorySeedMeasure initial generator T,
      HasPositivePrefixWaitingTimes 0 seed := by
  rw [finiteStateMarkovJumpTrajectorySeedMeasure]
  apply (ae_map_iff
    measurable_finiteStateMarkovJumpTrajectorySeed.aemeasurable
    (measurableSet_hasPositivePrefixWaitingTimes (State := State) 0)).2
  filter_upwards [FiniteMarkovProcesses.Probability.ae_positive_finiteStateInitialTimedStateMeasure
    initial generator T hT] with
    timedState hTimedState
  intro index
  exact hTimedState

/-- Every waiting coordinate on the normalized infinite Gillespie tape is strictly positive
almost surely. -/
theorem ae_hasPositiveWaitingTimes_finiteStateMarkovJumpTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ tape ∂finiteStateMarkovJumpTapeMeasure initial generator T,
      HasPositiveWaitingTimes tape := by
  rw [finiteStateMarkovJumpTapeMeasure]
  apply Measure.ae_comp_of_ae_ae TimedStateTrajectory.measurableSet_hasPositiveWaitingTimes
  filter_upwards [ae_hasPositivePrefixWaitingTimes_seedMeasure initial generator T hT] with
    seed hSeed
  exact ae_hasPositiveWaitingTimes_traj generator T hT seed hSeed

/-- Every normalized finite-state Gillespie tape crosses every nonnegative finite observation
horizon almost surely. -/
theorem ae_crossesJumpHorizon_finiteStateMarkovJumpTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ tape ∂finiteStateMarkovJumpTapeMeasure initial generator T,
      CrossesJumpHorizon tape T := by
  filter_upwards
    [ae_hasPositiveWaitingTimes_finiteStateMarkovJumpTapeMeasure
      initial generator T hT,
    ae_exists_horizonBlock_le_wait_finiteStateMarkovJumpTapeMeasure
      initial generator T] with tape hPositive hLong
  exact crossesJumpHorizon_of_exists_horizonBlock_le_wait hPositive hLong

end FiniteStateMarkovJumpTrajectory

/-- Index of the first dwell endpoint that reaches the observation horizon. -/
noncomputable def firstJumpHorizonCrossingIndex {State : Type u}
    (tape : ℕ → State × ℝ) (T : ℝ) (hCrosses : CrossesJumpHorizon tape T) : ℕ :=
  Nat.find hCrosses

/-- Stop an infinite timed-state tape immediately before its first horizon-crossing dwell. The
earlier dwell endpoints are the physical jump times, and the occupied states through the crossing
dwell form the complete state word. -/
noncomputable def finiteStateMarkovStoppedHistory {State : Type u}
    (tape : ℕ → State × ℝ) (T : ℝ) (hCrosses : CrossesJumpHorizon tape T) :
    FiniteJumpHistory State :=
  let jumpCount := firstJumpHorizonCrossingIndex tape T hCrosses
  ⟨jumpCount,
    (fun index => (tape index.1).1),
    (fun index => timedStateCumulativeTime tape (index.1 + 1))⟩

namespace FiniteStateMarkovStoppedHistory

variable {State : Type u}

/-- The stopped history's jump count is the first crossing index. -/
@[simp]
theorem jumpCount (tape : ℕ → State × ℝ) (T : ℝ)
    (hCrosses : CrossesJumpHorizon tape T) :
    (finiteStateMarkovStoppedHistory tape T hCrosses).1 =
      firstJumpHorizonCrossingIndex tape T hCrosses :=
  rfl

/-- Cumulative time reaches the horizon at the selected crossing dwell. -/
theorem cumulativeTime_crossing (tape : ℕ → State × ℝ) (T : ℝ)
    (hCrosses : CrossesJumpHorizon tape T) :
    T ≤ timedStateCumulativeTime tape
      (firstJumpHorizonCrossingIndex tape T hCrosses + 1) :=
  Nat.find_spec hCrosses

/-- Every dwell endpoint before the selected crossing lies strictly below the horizon. -/
theorem cumulativeTime_lt_of_lt_crossing (tape : ℕ → State × ℝ) (T : ℝ)
    (hCrosses : CrossesJumpHorizon tape T) {index : ℕ}
    (hIndex : index < firstJumpHorizonCrossingIndex tape T hCrosses) :
    timedStateCumulativeTime tape (index + 1) < T := by
  exact lt_of_not_ge (Nat.find_min hCrosses hIndex)

/-- Positive waits and finite crossing put the stopped jump-time vector in the exact open ordered
simplex frozen for the physical finite-history carrier. -/
theorem orderedBefore {tape : ℕ → State × ℝ} {T : ℝ}
    (hPositive : HasPositiveWaitingTimes tape)
    (hCrosses : CrossesJumpHorizon tape T) :
    (finiteStateMarkovStoppedHistory tape T hCrosses).2.2 ∈
      orderedJumpTimes (firstJumpHorizonCrossingIndex tape T hCrosses) T := by
  have hCumulative : StrictMono (timedStateCumulativeTime tape) :=
    TimedStateTrajectory.cumulativeTime_strictMono hPositive
  constructor
  · intro index
    constructor
    · calc
        0 = timedStateCumulativeTime tape 0 :=
          (TimedStateTrajectory.cumulativeTime_zero tape).symm
        _ < timedStateCumulativeTime tape (index.1 + 1) :=
          hCumulative (Nat.zero_lt_succ index.1)
    · exact cumulativeTime_lt_of_lt_crossing tape T hCrosses index.2
  · intro first second hFirstSecond
    exact hCumulative
      (Nat.add_lt_add_right (Fin.val_strictMono hFirstSecond) 1)

/-- The stopped history satisfies the carrier's named ordered-before predicate. -/
theorem orderedBeforePredicate {tape : ℕ → State × ℝ} {T : ℝ}
    (hPositive : HasPositiveWaitingTimes tape)
    (hCrosses : CrossesJumpHorizon tape T) :
    FiniteJumpHistory.OrderedBefore
      (finiteStateMarkovStoppedHistory tape T hCrosses) T :=
  orderedBefore hPositive hCrosses

end FiniteStateMarkovStoppedHistory
