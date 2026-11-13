/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovFutureWordErasure
public import FiniteMarkovProcesses.Probability.OrderedJumpTimesMarkedDisintegration

/-!
# Future erasure after one marked time-dependent Markov transition

This module isolates the finite Markov algebra at a marked virtual event.  Summing every complete
state word with a prescribed source and target at that event erases all later state coordinates,
leaving the earlier endpoint word weight times the marked transition probability.

## Main result

- `sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_markedTransition`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- State-word coordinate immediately before the marked event. -/
def finiteStateTimeDependentMarkovMarkedSourceIndex
    (earlierCount laterCount : ℕ) : Fin (earlierCount + 1 + laterCount + 1) :=
  ⟨earlierCount, by omega⟩

/-- State-word coordinate immediately after the marked event. -/
def finiteStateTimeDependentMarkovMarkedTargetIndex
    (earlierCount laterCount : ℕ) : Fin (earlierCount + 1 + laterCount + 1) :=
  ⟨earlierCount + 1, by omega⟩

/-- Event-time coordinate of the marked event. -/
def finiteStateTimeDependentMarkovMarkedTimeIndex
    (earlierCount laterCount : ℕ) : Fin (earlierCount + 1 + laterCount) :=
  ⟨earlierCount, by omega⟩

/-- Event times strictly preceding the marked event. -/
def finiteStateTimeDependentMarkovMarkedEarlierTimes
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ) : Fin earlierCount → ℝ :=
  fun index ↦ times ⟨index.val, by omega⟩

omit [Fintype State] [DecidableEq State] in
/-- Appending a final state leaves the state at the marked source index unchanged. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedSourceIndex_snoc
    (earlierCount laterCount : ℕ)
    (priorStates : Fin (earlierCount + 1 + laterCount + 1) → State)
    (finalState : State) :
    (@Fin.snoc (earlierCount + 1 + laterCount + 1) (fun _ ↦ State)
      priorStates finalState)
        (finiteStateTimeDependentMarkovMarkedSourceIndex
          earlierCount (laterCount + 1)) =
      priorStates (finiteStateTimeDependentMarkovMarkedSourceIndex
        earlierCount laterCount) := by
  have hIndex : finiteStateTimeDependentMarkovMarkedSourceIndex
      earlierCount (laterCount + 1) =
        (finiteStateTimeDependentMarkovMarkedSourceIndex
          earlierCount laterCount).castSucc := by
    apply Fin.ext
    rfl
  rw [hIndex]
  rw [Fin.snoc_castSucc]

omit [Fintype State] [DecidableEq State] in
/-- Appending a final state leaves the state at the marked target index unchanged. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedTargetIndex_snoc
    (earlierCount laterCount : ℕ)
    (priorStates : Fin (earlierCount + 1 + laterCount + 1) → State)
    (finalState : State) :
    (@Fin.snoc (earlierCount + 1 + laterCount + 1) (fun _ ↦ State)
      priorStates finalState)
        (finiteStateTimeDependentMarkovMarkedTargetIndex
          earlierCount (laterCount + 1)) =
      priorStates (finiteStateTimeDependentMarkovMarkedTargetIndex
        earlierCount laterCount) := by
  have hIndex : finiteStateTimeDependentMarkovMarkedTargetIndex
      earlierCount (laterCount + 1) =
        (finiteStateTimeDependentMarkovMarkedTargetIndex
          earlierCount laterCount).castSucc := by
    apply Fin.ext
    rfl
  rw [hIndex]
  rw [Fin.snoc_castSucc]

/-- `Fin.init` preserves the times preceding the marked event. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedEarlierTimes_init
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount + 1) → ℝ) :
    finiteStateTimeDependentMarkovMarkedEarlierTimes
        earlierCount laterCount (Fin.init times) =
      finiteStateTimeDependentMarkovMarkedEarlierTimes
        earlierCount (laterCount + 1) times := by
  funext index
  rfl

/-- `Fin.init` preserves the time read at the marked-event index. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedTimeIndex_init
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount + 1) → ℝ) :
    Fin.init times (finiteStateTimeDependentMarkovMarkedTimeIndex
        earlierCount laterCount) =
      times (finiteStateTimeDependentMarkovMarkedTimeIndex
        earlierCount (laterCount + 1)) := by
  rfl

/-- The earlier-time projection of joined marked coordinates is the supplied earlier block. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedEarlierTimes_markedJoin
    (earlierCount laterCount : ℕ) (markedTime : ℝ)
    (earlierTimes : Fin earlierCount → ℝ)
    (laterTimes : Fin laterCount → ℝ) :
    finiteStateTimeDependentMarkovMarkedEarlierTimes earlierCount laterCount
        (orderedJumpTimesMarkedJoin earlierCount laterCount
          ((markedTime, earlierTimes), laterTimes)) =
      earlierTimes := by
  funext index
  have hCoordinates := congrArg (fun coordinates ↦ coordinates.1.2 index)
    (orderedJumpTimesMarkedSplit_join earlierCount laterCount
      ((markedTime, earlierTimes), laterTimes))
  simpa only [finiteStateTimeDependentMarkovMarkedEarlierTimes,
    orderedJumpTimesMarkedSplit_earlier_apply] using! hCoordinates

/-- The marked-time projection of joined marked coordinates is the supplied marked time. -/
@[simp]
theorem finiteStateTimeDependentMarkovMarkedTime_markedJoin
    (earlierCount laterCount : ℕ) (markedTime : ℝ)
    (earlierTimes : Fin earlierCount → ℝ)
    (laterTimes : Fin laterCount → ℝ) :
    orderedJumpTimesMarkedJoin earlierCount laterCount
        ((markedTime, earlierTimes), laterTimes)
        (finiteStateTimeDependentMarkovMarkedTimeIndex earlierCount laterCount) =
      markedTime := by
  have hCoordinates := congrArg (fun coordinates ↦ coordinates.1.1)
    (orderedJumpTimesMarkedSplit_join earlierCount laterCount
      ((markedTime, earlierTimes), laterTimes))
  simpa only [finiteStateTimeDependentMarkovMarkedTimeIndex,
    orderedJumpTimesMarkedSplit_markedTime] using! hCoordinates

/-- Summing complete state words with one prescribed marked edge erases all future states. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_markedTransition
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ)
    (source target : State) :
    (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
      if states (finiteStateTimeDependentMarkovMarkedSourceIndex
            earlierCount laterCount) = source ∧
          states (finiteStateTimeDependentMarkovMarkedTargetIndex
            earlierCount laterCount) = target then
        finiteStateTimeDependentMarkovUniformizedStateWordWeight
          initial rates times states
      else 0) =
      finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates
            (finiteStateTimeDependentMarkovMarkedEarlierTimes
              earlierCount laterCount times) source *
        (rates.uniformizedTransitionPMF
          (times (finiteStateTimeDependentMarkovMarkedTimeIndex
            earlierCount laterCount)) source target).toReal := by
  induction laterCount with
  | zero =>
      rw [← (Fin.snocEquiv
        (fun _ : Fin (earlierCount + 2) ↦ State)).sum_comp]
      rw [Fintype.sum_prod_type]
      have hSnocEquiv (finalState : State)
          (priorStates : Fin (earlierCount + 1) → State) :
          (Fin.snocEquiv (fun _ : Fin (earlierCount + 2) ↦ State))
              (finalState, priorStates) =
            Fin.snoc priorStates finalState := by
        rfl
      simp_rw [hSnocEquiv]
      have hSourceIndex :
          finiteStateTimeDependentMarkovMarkedSourceIndex earlierCount 0 =
            (Fin.last earlierCount).castSucc := by
        apply Fin.ext
        rfl
      have hTargetIndex :
          finiteStateTimeDependentMarkovMarkedTargetIndex earlierCount 0 =
            Fin.last (earlierCount + 1) := by
        apply Fin.ext
        rfl
      simp_rw [hSourceIndex, hTargetIndex, Fin.snoc_castSucc, Fin.snoc_last]
      change
        (∑ finalState : State,
          ∑ priorStates : Fin (earlierCount + 1) → State,
            if priorStates (Fin.last earlierCount) = source ∧ finalState = target then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                initial rates times (Fin.snoc priorStates finalState)
            else 0) = _
      rw [Finset.sum_eq_single target]
      · simp only [and_true]
        simp_rw [finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc]
        have hFactor (priorStates : Fin (earlierCount + 1) → State) :
            (if priorStates (Fin.last earlierCount) = source then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                  initial rates (Fin.init times) priorStates *
                (rates.uniformizedTransitionPMF
                  (times (Fin.last earlierCount))
                  (priorStates (Fin.last earlierCount)) target).toReal
            else 0) =
              (if priorStates (Fin.last earlierCount) = source then
                finiteStateTimeDependentMarkovUniformizedStateWordWeight
                  initial rates (Fin.init times) priorStates
              else 0) *
                (rates.uniformizedTransitionPMF
                  (times (Fin.last earlierCount)) source target).toReal := by
          by_cases hSource : priorStates (Fin.last earlierCount) = source
          · simp [hSource]
          · simp [hSource]
        simp_rw [hFactor]
        rw [← Finset.sum_mul]
        unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        rfl
      · intro finalState _hFinalState hNe
        simp only [hNe, and_false, ite_false, Finset.sum_const_zero]
      · simp
  | succ laterCount inductionHypothesis =>
      rw [← (Fin.snocEquiv
        (fun _ : Fin (earlierCount + 1 + (laterCount + 1) + 1) ↦ State)).sum_comp]
      rw [Fintype.sum_prod_type]
      have hSnocEquiv (finalState : State)
          (priorStates : Fin (earlierCount + 1 + laterCount + 1) → State) :
          (Fin.snocEquiv
            (fun _ : Fin (earlierCount + 1 + (laterCount + 1) + 1) ↦ State))
              (finalState, priorStates) =
            Fin.snoc priorStates finalState := by
        rfl
      simp_rw [hSnocEquiv]
      change
        (∑ finalState : State,
          ∑ priorStates : Fin (earlierCount + 1 + laterCount + 1) → State,
            if (@Fin.snoc (earlierCount + 1 + laterCount + 1) (fun _ ↦ State)
                  priorStates finalState)
                  (finiteStateTimeDependentMarkovMarkedSourceIndex
                    earlierCount (laterCount + 1)) = source ∧
                (@Fin.snoc (earlierCount + 1 + laterCount + 1) (fun _ ↦ State)
                  priorStates finalState)
                  (finiteStateTimeDependentMarkovMarkedTargetIndex
                    earlierCount (laterCount + 1)) = target then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                initial rates times
                  (@Fin.snoc (earlierCount + 1 + laterCount + 1) (fun _ ↦ State)
                    priorStates finalState)
            else 0) = _
      simp_rw [finiteStateTimeDependentMarkovMarkedSourceIndex_snoc,
        finiteStateTimeDependentMarkovMarkedTargetIndex_snoc,
        finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc]
      rw [Finset.sum_comm]
      have hErase
          (priorStates : Fin (earlierCount + 1 + laterCount + 1) → State) :
          (∑ finalState : State,
            if priorStates (finiteStateTimeDependentMarkovMarkedSourceIndex
                    earlierCount laterCount) = source ∧
                priorStates (finiteStateTimeDependentMarkovMarkedTargetIndex
                    earlierCount laterCount) = target then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                  initial rates (Fin.init times) priorStates *
                (rates.uniformizedTransitionPMF
                  (times (Fin.last (earlierCount + 1 + laterCount)))
                  (priorStates (Fin.last (earlierCount + 1 + laterCount)))
                  finalState).toReal
            else 0) =
          if priorStates (finiteStateTimeDependentMarkovMarkedSourceIndex
                  earlierCount laterCount) = source ∧
              priorStates (finiteStateTimeDependentMarkovMarkedTargetIndex
                  earlierCount laterCount) = target then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates (Fin.init times) priorStates
          else 0 := by
        by_cases hMarked :
            priorStates (finiteStateTimeDependentMarkovMarkedSourceIndex
                  earlierCount laterCount) = source ∧
              priorStates (finiteStateTimeDependentMarkovMarkedTargetIndex
                  earlierCount laterCount) = target
        · simp only [hMarked.1, hMarked.2, true_and, ite_true]
          rw [← Finset.mul_sum, PMF.sum_toReal, mul_one]
        · simp only [hMarked, ite_false, Finset.sum_const_zero]
      calc
        _ = ∑ priorStates : Fin (earlierCount + 1 + laterCount + 1) → State,
            if priorStates (finiteStateTimeDependentMarkovMarkedSourceIndex
                    earlierCount laterCount) = source ∧
                priorStates (finiteStateTimeDependentMarkovMarkedTargetIndex
                    earlierCount laterCount) = target then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                initial rates (Fin.init times) priorStates
            else 0 := by
          apply Finset.sum_congr rfl
          intro priorStates _hPriorStates
          exact hErase priorStates
        _ = _ := by
          have hInduction := inductionHypothesis (Fin.init times)
          simpa only [finiteStateTimeDependentMarkovMarkedEarlierTimes_init,
            finiteStateTimeDependentMarkovMarkedTimeIndex_init] using hInduction

/-- At fixed complete event times, the marked-edge state-word sum leaves the common clock factor,
the earlier endpoint word weight, and the marked transition probability. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ)
    (source target : State) :
    (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
      if states (finiteStateTimeDependentMarkovMarkedSourceIndex
            earlierCount laterCount) = source ∧
          states (finiteStateTimeDependentMarkovMarkedTargetIndex
            earlierCount laterCount) = target then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
      ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates
            (finiteStateTimeDependentMarkovMarkedEarlierTimes
              earlierCount laterCount times) source *
        (rates.uniformizedTransitionPMF
          (times (finiteStateTimeDependentMarkovMarkedTimeIndex
            earlierCount laterCount)) source target).toReal := by
  let clockFactor :=
    (rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
      Real.exp (-((rates.uniformizationRate : ℝ) * duration))
  calc
    _ = ∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
        clockFactor *
          (if states (finiteStateTimeDependentMarkovMarkedSourceIndex
                earlierCount laterCount) = source ∧
              states (finiteStateTimeDependentMarkovMarkedTargetIndex
                earlierCount laterCount) = target then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates times states
          else 0) := by
      apply Finset.sum_congr rfl
      intro states _hStates
      by_cases hMarked :
          states (finiteStateTimeDependentMarkovMarkedSourceIndex
                earlierCount laterCount) = source ∧
            states (finiteStateTimeDependentMarkovMarkedTargetIndex
                earlierCount laterCount) = target
      · simp only [hMarked.1, hMarked.2, true_and, ite_true,
          finiteStateTimeDependentMarkovUniformizedSliceDensity, clockFactor]
      · simp only [hMarked, ite_false, mul_zero]
    _ = clockFactor *
        ∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
          (if states (finiteStateTimeDependentMarkovMarkedSourceIndex
                earlierCount laterCount) = source ∧
              states (finiteStateTimeDependentMarkovMarkedTargetIndex
                earlierCount laterCount) = target then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates times states
          else 0) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_markedTransition]
      dsimp only [clockFactor]
      ring

end

end FiniteMarkovProcesses.Probability
