/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpStopping

/-!
# Geometric crossing for timed-state trajectories

This module proves a geometric criterion for finite-horizon nonexplosion. If the
probability of extending an all-short timed prefix contracts by a uniform factor below one, and
the seed measure obeys the same bound, then the Ionescu--Tulcea trajectory mixture assigns zero
mass to the event that every wait is short.

The theorem depends only on timed-state trajectory kernels. It is independent of any Markov jump
generator and can be shared by physical Gillespie and virtual uniformization constructions.

## Main Results

- `timedStateTrajectoryMeasure_allWaitingTimesShort_eq_zero`: geometric extinction of the
  all-short-waits event.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

universe u

/-- The infinite timed-state trajectory obtained by mixing an Ionescu--Tulcea kernel over its
one-coordinate seed law. -/
noncomputable def timedStateTrajectoryMeasure
    {State : Type u} [MeasurableSpace State]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → State × ℝ) (State × ℝ))
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → State × ℝ)) :
    Measure (ℕ → State × ℝ) :=
  Kernel.traj (X := fun _ ↦ State × ℝ) step 0 ∘ₘ seed

/-- A uniform one-step contraction of all-short prefix probabilities and the stated seed bound
force the infinite all-short-waits event to have measure zero. The seed is any measure satisfying
the bound. -/
theorem timedStateTrajectoryMeasure_allWaitingTimesShort_eq_zero
    {State : Type u} [MeasurableSpace State]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → State × ℝ) (State × ℝ))
    [hStepMarkov : ∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → State × ℝ))
    (blockLength : ℝ) (contraction : ℝ≥0∞) (hContraction : contraction < 1)
    (hStep : ∀ n history,
      Kernel.partialTraj (X := fun _ ↦ State × ℝ)
          step n (n + 1) history
          {extended |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength (n + 1) extended} ≤
        Set.indicator
          {oldHistory |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength n oldHistory}
          (fun _ ↦ contraction) history)
    (hSeed :
      seed
          {initialSeed |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength 0 initialSeed} ≤
        contraction) :
    timedStateTrajectoryMeasure step seed
        {tape | HasShortWaitingTimes blockLength tape} = 0 := by
  have hPartial (initialSeed : (i : Finset.Iic 0) → State × ℝ) (n : ℕ) :
      Kernel.partialTraj (X := fun _ ↦ State × ℝ) step 0 n initialSeed
          {history |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength n history} ≤
        Set.indicator
          {seedHistory |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength 0 seedHistory}
          (fun _ ↦ contraction ^ n) initialSeed := by
    induction n with
    | zero =>
        rw [Kernel.partialTraj_self, Kernel.id_apply]
        rw [Measure.dirac_apply' _
          (FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
            (State := State) blockLength 0)]
        simp [Set.indicator]
    | succ n inductionHypothesis =>
        have hPrefixSet : MeasurableSet
            {history : (i : Finset.Iic n) → State × ℝ |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n history} :=
          FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
            blockLength n
        have hSuccessorSet : MeasurableSet
            {history : (i : Finset.Iic (n + 1)) → State × ℝ |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength (n + 1) history} :=
          FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
            blockLength (n + 1)
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]
        rw [Kernel.comp_apply' _ _ _ hSuccessorSet]
        calc
          (∫⁻ history,
              Kernel.partialTraj (X := fun _ ↦ State × ℝ)
                step n (n + 1) history
                {extended |
                  FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                    blockLength (n + 1) extended}
              ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
                step 0 n initialSeed) ≤
              ∫⁻ history,
                Set.indicator
                  {oldHistory |
                    FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                      blockLength n oldHistory}
                  (fun _ ↦ contraction) history
                ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
                  step 0 n initialSeed :=
            lintegral_mono fun history ↦ hStep n history
          _ = contraction *
              Kernel.partialTraj (X := fun _ ↦ State × ℝ)
                step 0 n initialSeed
                {history |
                  FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                    blockLength n history} := by
            rw [lintegral_indicator_const hPrefixSet]
          _ ≤ contraction *
              Set.indicator
                {seedHistory |
                  FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                    blockLength 0 seedHistory}
                (fun _ ↦ contraction ^ n) initialSeed :=
            (mul_le_mul_right inductionHypothesis) contraction
          _ = Set.indicator
              {seedHistory |
                FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                  blockLength 0 seedHistory}
              (fun _ ↦ contraction ^ (n + 1)) initialSeed := by
            by_cases hInitial :
                FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                  blockLength 0 initialSeed
            · rw [Set.indicator_of_mem hInitial, Set.indicator_of_mem hInitial,
                pow_succ, mul_comm]
            · rw [Set.indicator_of_notMem hInitial, Set.indicator_of_notMem hInitial,
                mul_zero]
  have hPrefix (n : ℕ) :
      timedStateTrajectoryMeasure step seed
          {tape |
            FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
              blockLength n (Preorder.frestrictLe n tape)} ≤
        contraction ^ (n + 1) := by
    have hPrefixSet : MeasurableSet
        {history : (i : Finset.Iic n) → State × ℝ |
          FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
            blockLength n history} :=
      FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
        blockLength n
    have hTapeSet : MeasurableSet
        {tape : ℕ → State × ℝ |
          FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
            blockLength n (Preorder.frestrictLe n tape)} :=
      hPrefixSet.preimage (Preorder.measurable_frestrictLe n)
    rw [timedStateTrajectoryMeasure]
    rw [Measure.bind_apply hTapeSet (Kernel.aemeasurable _)]
    have hTrajectoryApply (initialSeed : (i : Finset.Iic 0) → State × ℝ) :
        Kernel.traj (X := fun _ ↦ State × ℝ) step 0 initialSeed
            {tape |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n (Preorder.frestrictLe n tape)} =
          Kernel.partialTraj (X := fun _ ↦ State × ℝ)
            step 0 n initialSeed
            {history |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n history} := by
      change Kernel.traj (X := fun _ ↦ State × ℝ) step 0 initialSeed
          (Preorder.frestrictLe n ⁻¹'
            {history |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n history}) = _
      rw [← Measure.map_apply (Preorder.measurable_frestrictLe n) hPrefixSet]
      rw [Kernel.traj_map_frestrictLe_apply]
    simp_rw [hTrajectoryApply]
    calc
      (∫⁻ initialSeed,
          Kernel.partialTraj (X := fun _ ↦ State × ℝ)
            step 0 n initialSeed
            {history |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n history}
          ∂seed) ≤
          ∫⁻ initialSeed,
            Set.indicator
              {seedHistory |
                FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                  blockLength 0 seedHistory}
              (fun _ ↦ contraction ^ n) initialSeed
            ∂seed :=
        lintegral_mono fun initialSeed ↦ hPartial initialSeed n
      _ = contraction ^ n *
          seed
            {initialSeed |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength 0 initialSeed} := by
        rw [lintegral_indicator_const
          (FiniteStateMarkovJumpTrajectory.measurableSet_hasShortPrefixWaitingTimes
            blockLength 0)]
      _ ≤ contraction ^ n * contraction :=
        (mul_le_mul_right hSeed) (contraction ^ n)
      _ = contraction ^ (n + 1) := by rw [pow_succ]
  have hMeasureLe (n : ℕ) :
      timedStateTrajectoryMeasure step seed
          {tape | HasShortWaitingTimes blockLength tape} ≤
        contraction ^ n := by
    calc
      timedStateTrajectoryMeasure step seed
          {tape | HasShortWaitingTimes blockLength tape} ≤
          timedStateTrajectoryMeasure step seed
            {tape |
              FiniteStateMarkovJumpTrajectory.HasShortPrefixWaitingTimes
                blockLength n (Preorder.frestrictLe n tape)} := by
        apply measure_mono
        intro tape hAll index
        simpa [HasShortWaitingTimes, Preorder.frestrictLe_apply] using hAll index.1
      _ ≤ contraction ^ (n + 1) := hPrefix n
      _ ≤ contraction ^ n := by
        rw [pow_succ]
        exact ((mul_le_mul_right hContraction.le) (contraction ^ n)).trans_eq (mul_one _)
  apply le_antisymm
  · exact ge_of_tendsto'
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hContraction) hMeasureLe
  · exact bot_le

/-- If the seed has a positive wait almost surely and every one-step extension preserves positive
prefix waits almost surely, then every wait on the mixed infinite trajectory is positive almost
surely. This holds for an arbitrary seed measure. -/
theorem ae_hasPositiveWaitingTimes_timedStateTrajectoryMeasure
    {State : Type u} [MeasurableSpace State]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → State × ℝ) (State × ℝ))
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → State × ℝ))
    (hStep : ∀ n history,
      FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes n history →
        ∀ᵐ extended ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
            step n (n + 1) history,
          FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes
            (n + 1) extended)
    (hSeed :
      ∀ᵐ initialSeed ∂seed,
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes 0 initialSeed) :
    ∀ᵐ tape ∂timedStateTrajectoryMeasure step seed,
      HasPositiveWaitingTimes tape := by
  have hPartial (initialSeed : (i : Finset.Iic 0) → State × ℝ)
      (hInitial :
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes 0 initialSeed)
      (n : ℕ) :
      ∀ᵐ history ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
          step 0 n initialSeed,
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes n history := by
    induction n with
    | zero =>
        rw [Kernel.partialTraj_self, Kernel.id_apply]
        exact (ae_dirac_iff
          (FiniteStateMarkovJumpTrajectory.measurableSet_hasPositivePrefixWaitingTimes
            (State := State) 0)).2 hInitial
    | succ n inductionHypothesis =>
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n)]
        change ∀ᵐ extended ∂Kernel.partialTraj (X := fun _ ↦ State × ℝ)
            step n (n + 1) ∘ₘ
              Kernel.partialTraj (X := fun _ ↦ State × ℝ)
                step 0 n initialSeed,
          FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes
            (n + 1) extended
        apply Measure.ae_comp_of_ae_ae
          (FiniteStateMarkovJumpTrajectory.measurableSet_hasPositivePrefixWaitingTimes
            (State := State) (n + 1))
        filter_upwards [inductionHypothesis] with history hPositive
        exact hStep n history hPositive
  have hTrajectory (initialSeed : (i : Finset.Iic 0) → State × ℝ)
      (hInitial :
        FiniteStateMarkovJumpTrajectory.HasPositivePrefixWaitingTimes 0 initialSeed) :
      ∀ᵐ tape ∂Kernel.traj (X := fun _ ↦ State × ℝ) step 0 initialSeed,
        HasPositiveWaitingTimes tape := by
    apply ae_all_iff.2
    intro n
    have hPrefix := (hPartial initialSeed hInitial n).mono fun history hPositive ↦
      hPositive (finiteTrajectoryCurrentIndex n)
    rw [← Kernel.traj_map_frestrictLe_apply] at hPrefix
    have hTape := (ae_map_iff (Preorder.measurable_frestrictLe n).aemeasurable
      (measurable_const.lt
        ((measurable_pi_apply (finiteTrajectoryCurrentIndex n)).snd)).setOf).1 hPrefix
    simpa [HasPositiveWaitingTimes, Preorder.frestrictLe_apply,
      finiteTrajectoryCurrentIndex] using hTape
  rw [timedStateTrajectoryMeasure]
  apply Measure.ae_comp_of_ae_ae
    TimedStateTrajectory.measurableSet_hasPositiveWaitingTimes
  filter_upwards [hSeed] with initialSeed hInitial
  exact hTrajectory initialSeed hInitial

end FiniteMarkovProcesses.Probability
