/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedStoppedLaw
public import FiniteMarkovProcesses.Probability.TimedStateTrajectoryGeometricCrossing

/-!
# Finite-horizon crossing of uniformized finite-state trajectories

This module proves nonexplosion of the normalized uniformized timed tape. A common exponential
clock gives a strict geometric contraction for the event that every wait stays below one fixed
horizon block. The geometric trajectory theorem then makes the all-short event null. Since
all waits are positive almost surely, one block-sized wait forces finite-horizon crossing.

The result proves the almost-sure crossing needed to normalize the stopped virtual-history law.
The histories at this stage retain virtual self-events.

## Main Results

- `finiteStateUniformizedTapeMeasure_allHorizonWaitsShort`: the all-short event has zero mass.
- `ae_hasPositiveWaitingTimes_finiteStateUniformizedTapeMeasure`: all waits are positive almost
  surely.
- `ae_crossesJumpHorizon_finiteStateUniformizedTapeMeasure`: exact finite-horizon crossing.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

universe u

namespace FiniteStateMarkovUniformizedTrajectory

open FiniteStateMarkovJumpTrajectory

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Probability bound for one common-clock wait to remain shorter than the horizon block. -/
noncomputable def finiteStateUniformizedShortWaitProbability
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (1 - Real.exp
      (-((generator.uniformizationRate : ℝ) * finiteJumpHorizonBlockLength T)))

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The uniformized short-wait probability is strictly below one. -/
theorem finiteStateUniformizedShortWaitProbability_lt_one
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedShortWaitProbability generator T < 1 := by
  rw [finiteStateUniformizedShortWaitProbability, ENNReal.ofReal_lt_one]
  linarith [Real.exp_pos
    (-((generator.uniformizationRate : ℝ) * finiteJumpHorizonBlockLength T))]

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The common exponential holding law has the exact horizon-block short-wait probability. -/
theorem finiteStateUniformizedHoldingTimeMeasure_Iio
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedHoldingTimeMeasure generator
        (Set.Iio (finiteJumpHorizonBlockLength T)) =
      finiteStateUniformizedShortWaitProbability generator T := by
  unfold finiteStateUniformizedHoldingTimeMeasure
    finiteStateUniformizedShortWaitProbability
  have hRate : 0 < (generator.uniformizationRate : ℝ) := by
    exact_mod_cast generator.uniformizationRate_pos
  let := isProbabilityMeasure_expMeasure hRate
  calc
    expMeasure (generator.uniformizationRate : ℝ)
        (Set.Iio (finiteJumpHorizonBlockLength T)) =
        expMeasure (generator.uniformizationRate : ℝ)
          (Set.Iic (finiteJumpHorizonBlockLength T)) :=
      measure_congr Iio_ae_eq_Iic
    _ = ENNReal.ofReal
        (1 - Real.exp
          (-((generator.uniformizationRate : ℝ) * finiteJumpHorizonBlockLength T))) := by
      rw [← ofReal_cdf, cdf_expMeasure_eq hRate,
        ite_eq_left (finiteJumpHorizonBlockLength_pos T).le]

/-- Every uniformized timed step is shorter than the horizon block with the common exact
probability. -/
theorem finiteStateUniformizedTimedStepKernel_horizonShort
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State) :
    finiteStateUniformizedTimedStepKernel generator state
        {timedState | timedState.2 < finiteJumpHorizonBlockLength T} =
      finiteStateUniformizedShortWaitProbability generator T := by
  rw [finiteStateUniformizedTimedStepKernel, Kernel.compProd_apply
    (measurableSet_lt measurable_snd measurable_const)]
  calc
    (∫⁻ target,
        ((finiteStateUniformizedHoldingTimeKernel generator).comap
          Prod.snd measurable_snd) (state, target)
          (Prod.mk target ⁻¹'
            {timedState | timedState.2 < finiteJumpHorizonBlockLength T})
        ∂finiteStateUniformizedTransitionKernel generator state) =
        ∫⁻ _target,
          finiteStateUniformizedHoldingTimeMeasure generator
            (Set.Iio (finiteJumpHorizonBlockLength T))
          ∂finiteStateUniformizedTransitionKernel generator state := by
      rfl
    _ = ∫⁻ _target, finiteStateUniformizedShortWaitProbability generator T
          ∂finiteStateUniformizedTransitionKernel generator state := by
      rw [finiteStateUniformizedHoldingTimeMeasure_Iio]
    _ = finiteStateUniformizedShortWaitProbability generator T := by simp

omit [DecidableEq State] in
/-- The normalized initial timed state has the same exact short-wait probability. -/
theorem finiteStateUniformizedInitialTimedStateMeasure_horizonShort
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedInitialTimedStateMeasure initial generator
        {timedState | timedState.2 < finiteJumpHorizonBlockLength T} =
      finiteStateUniformizedShortWaitProbability generator T := by
  rw [finiteStateUniformizedInitialTimedStateMeasure, Measure.compProd_apply
    (measurableSet_lt measurable_snd measurable_const)]
  calc
    (∫⁻ state,
        finiteStateUniformizedHoldingTimeKernel generator state
          (Prod.mk state ⁻¹'
            {timedState | timedState.2 < finiteJumpHorizonBlockLength T})
        ∂initial.toMeasure) =
        ∫⁻ _state,
          finiteStateUniformizedHoldingTimeMeasure generator
            (Set.Iio (finiteJumpHorizonBlockLength T)) ∂initial.toMeasure := by
      rfl
    _ = ∫⁻ _state, finiteStateUniformizedShortWaitProbability generator T
          ∂initial.toMeasure := by
      rw [finiteStateUniformizedHoldingTimeMeasure_Iio]
    _ = finiteStateUniformizedShortWaitProbability generator T := by simp

/-- One uniformized Ionescu--Tulcea successor is all-short exactly when the old prefix is
all-short and the new common-clock wait is short. -/
theorem partialTraj_succ_horizonShortPrefix_apply
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) :
    Kernel.partialTraj (X := fun _ ↦ State × ℝ)
        (finiteStateUniformizedTrajectoryStepKernel generator) n (n + 1) history
        {extended |
          FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
            (finiteJumpHorizonBlockLength T) (n + 1) extended} =
      Set.indicator
        {oldHistory |
          FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
            (finiteJumpHorizonBlockLength T) n oldHistory}
        (fun _ ↦ finiteStateUniformizedShortWaitProbability generator T) history := by
  let combine := IicProdIoc (X := fun _ : ℕ ↦ State × ℝ) n (n + 1)
  have hCombineMeasurable : Measurable combine :=
    measurable_IicProdIoc (X := fun _ : ℕ ↦ State × ℝ)
  have hSuccessorSet : MeasurableSet
      {extended |
        FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) (n + 1) extended} :=
    FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
      (State := State) (finiteJumpHorizonBlockLength T) (n + 1)
  have hFixedPrefixSet : MeasurableSet
      {singleton |
        FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) (n + 1)
            (combine (history, singleton))} :=
    (hSuccessorSet.preimage hCombineMeasurable).preimage measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hCombineMeasurable]
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  rw [Measure.map_apply hCombineMeasurable hSuccessorSet]
  rw [Measure.map_apply measurable_prodMk_left
    (hSuccessorSet.preimage hCombineMeasurable)]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ State × ℝ) n).measurable]
  change (Measure.map
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ State × ℝ) n)
      ((finiteStateUniformizedTrajectoryStepKernel generator n) history))
      {singleton |
        FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
          (finiteJumpHorizonBlockLength T) (n + 1)
            (combine (history, singleton))} = _
  rw [Measure.map_apply
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ ↦ State × ℝ) n).measurable hFixedPrefixSet]
  rw [finiteStateUniformizedTrajectoryStepKernel, Kernel.comap_apply]
  by_cases hPrefix :
      FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
        (finiteJumpHorizonBlockLength T) n history
  · rw [Set.indicator_of_mem hPrefix]
    have hSet :
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ State × ℝ) n) ⁻¹'
            {singleton |
              HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) (n + 1)
                (combine (history, singleton))} =
          {next : State × ℝ | next.2 < finiteJumpHorizonBlockLength T} := by
      ext next
      simpa [combine, MeasurableEquiv.coe_IicProdIoc, hPrefix] using
        (hasShortPrefixWaitingTimes_IicProdIoc_iff
          (State := State) (finiteJumpHorizonBlockLength T) n history next)
    rw [hSet]
    exact finiteStateUniformizedTimedStepKernel_horizonShort generator T
      (finiteTimedTrajectoryCurrentState n history)
  · rw [Set.indicator_of_notMem hPrefix]
    have hSet :
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ State × ℝ) n) ⁻¹'
            {singleton |
              HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) (n + 1)
                (combine (history, singleton))} =
          (∅ : Set (State × ℝ)) := by
      ext next
      simpa [combine, MeasurableEquiv.coe_IicProdIoc, hPrefix] using
        (hasShortPrefixWaitingTimes_IicProdIoc_iff
          (State := State) (finiteJumpHorizonBlockLength T) n history next)
    rw [hSet, measure_empty]

/-- The event that every uniform-clock wait is shorter than the horizon block has probability
zero. -/
theorem finiteStateUniformizedTapeMeasure_allHorizonWaitsShort
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedTapeMeasure initial generator
        {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} = 0 := by
  change timedStateTrajectoryMeasure
      (finiteStateUniformizedTrajectoryStepKernel generator)
      (finiteStateUniformizedTrajectorySeedMeasure initial generator)
      {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} = 0
  apply timedStateTrajectoryMeasure_allWaitingTimesShort_eq_zero
    (step := finiteStateUniformizedTrajectoryStepKernel generator)
    (seed := finiteStateUniformizedTrajectorySeedMeasure initial generator)
    (blockLength := finiteJumpHorizonBlockLength T)
    (contraction := finiteStateUniformizedShortWaitProbability generator T)
  · exact finiteStateUniformizedShortWaitProbability_lt_one generator T
  · intro n history
    exact le_of_eq <| partialTraj_succ_horizonShortPrefix_apply
      generator T n history
  · have hSeedSet : MeasurableSet
        {seed : (i : Finset.Iic 0) → State × ℝ |
          FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
            (finiteJumpHorizonBlockLength T) 0 seed} :=
      FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
        (finiteJumpHorizonBlockLength T) 0
    rw [finiteStateUniformizedTrajectorySeedMeasure]
    rw [Measure.map_apply measurable_finiteStateMarkovJumpTrajectorySeed hSeedSet]
    have hSet :
        finiteStateMarkovJumpTrajectorySeed ⁻¹'
            {seed |
              HasShortPrefixWaitingTimes (finiteJumpHorizonBlockLength T) 0 seed} =
          {timedState : State × ℝ |
            timedState.2 < finiteJumpHorizonBlockLength T} := by
      ext timedState
      exact hasShortPrefixWaitingTimes_finiteStateMarkovJumpTrajectorySeed_iff T timedState
    rw [hSet, finiteStateUniformizedInitialTimedStateMeasure_horizonShort]

/-- One uniformized trajectory extension preserves positive prefix waits almost surely. -/
theorem ae_hasPositivePrefixWaitingTimes_partialTraj_succ
    (generator : FiniteStateMarkovGenerator State)
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ)
    (hPrefix :
      FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes n history) :
    ∀ᵐ extended ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
        (finiteStateUniformizedTrajectoryStepKernel generator) n (n + 1) history,
      FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes
        (n + 1) extended := by
  let combine := IicProdIoc (X := fun _ : ℕ ↦ State × ℝ) n (n + 1)
  have hCombineMeasurable : Measurable combine :=
    measurable_IicProdIoc (X := fun _ : ℕ ↦ State × ℝ)
  have hCombinedSet : MeasurableSet
      {pair |
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes
          (n + 1) (combine pair)} :=
    (FiniteStateMarkovJumpTrajectory.measurableSet_hasPositivePrefixWaitingTimes
      (State := State) (n + 1)).preimage hCombineMeasurable
  have hFixedPrefixSet : MeasurableSet
      {singleton |
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes
          (n + 1) (combine (history, singleton))} :=
    hCombinedSet.preimage measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hCombineMeasurable]
  apply (ae_map_iff hCombineMeasurable.aemeasurable
    (FiniteStateMarkovJumpTrajectory.measurableSet_hasPositivePrefixWaitingTimes
      (State := State) (n + 1))).2
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable hCombinedSet).2
  rw [Kernel.map_apply _
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ State × ℝ) n).measurable]
  apply (ae_map_iff
    (MeasurableEquiv.piSingleton
      (X := fun _ : ℕ ↦ State × ℝ) n).measurable.aemeasurable hFixedPrefixSet).2
  filter_upwards [ae_positive_finiteStateUniformizedTimedStepKernel generator
    (finiteTimedTrajectoryCurrentState n history)] with next hNext
  exact FiniteStateMarkovJumpTrajectory.hasPositivePrefixWaitingTimes_IicProdIoc
    n history next hPrefix hNext

/-- Every waiting coordinate on the infinite uniformized tape is positive almost surely. -/
theorem ae_hasPositiveWaitingTimes_finiteStateUniformizedTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) :
    ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
      HasPositiveWaitingTimes tape := by
  change ∀ᵐ tape ∂timedStateTrajectoryMeasure
      (finiteStateUniformizedTrajectoryStepKernel generator)
      (finiteStateUniformizedTrajectorySeedMeasure initial generator),
    HasPositiveWaitingTimes tape
  apply ae_hasPositiveWaitingTimes_timedStateTrajectoryMeasure
  · intro n history hPrefix
    exact ae_hasPositivePrefixWaitingTimes_partialTraj_succ
      generator n history hPrefix
  · rw [finiteStateUniformizedTrajectorySeedMeasure]
    apply (ae_map_iff
      measurable_finiteStateMarkovJumpTrajectorySeed.aemeasurable
      (FiniteStateMarkovJumpTrajectory.measurableSet_hasPositivePrefixWaitingTimes
        (State := State) 0)).2
    filter_upwards [ae_positive_finiteStateUniformizedInitialTimedStateMeasure
      initial generator] with timedState hTimedState
    intro index
    exact hTimedState

/-- Almost every uniformized tape contains a wait at least as long as the horizon block. -/
theorem ae_exists_horizonBlock_le_wait_finiteStateUniformizedTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
      ∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2 := by
  rw [ae_iff]
  change finiteStateUniformizedTapeMeasure initial generator
      {tape | ¬∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2} = 0
  have hSet :
      {tape : ℕ → State × ℝ |
        ¬∃ index, finiteJumpHorizonBlockLength T ≤ (tape index).2} =
        {tape | HasShortWaitingTimes (finiteJumpHorizonBlockLength T) tape} := by
    ext tape
    simp only [Set.mem_ofPred_eq, not_exists, not_le, HasShortWaitingTimes]
  rw [hSet]
  exact finiteStateUniformizedTapeMeasure_allHorizonWaitsShort initial generator T

/-- Every normalized uniformized tape crosses every finite observation horizon almost surely. -/
theorem ae_crossesJumpHorizon_finiteStateUniformizedTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
      CrossesJumpHorizon tape T := by
  filter_upwards
    [ae_hasPositiveWaitingTimes_finiteStateUniformizedTapeMeasure initial generator,
    ae_exists_horizonBlock_le_wait_finiteStateUniformizedTapeMeasure
      initial generator T] with tape hPositive hLong
  exact FiniteStateMarkovJumpTrajectory.crossesJumpHorizon_of_exists_horizonBlock_le_wait
    hPositive hLong

end FiniteStateMarkovUniformizedTrajectory

namespace FiniteStateMarkovUniformizedStoppedLaw

open FiniteStateMarkovUniformizedTrajectory

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- The stopped uniformized history law is exactly normalized at every finite horizon. -/
theorem finiteStateUniformizedStoppedHistoryMeasure_univ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedStoppedHistoryMeasure initial generator T Set.univ = 1 :=
  finiteStateUniformizedStoppedHistoryMeasure_univ_of_ae_crosses
    initial generator T <|
      ae_crossesJumpHorizon_finiteStateUniformizedTapeMeasure initial generator T

end FiniteStateMarkovUniformizedStoppedLaw

end FiniteMarkovProcesses.Probability
