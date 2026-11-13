/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointWordWeight

/-!
# Future-word erasure for time-dependent uniformized chains

Summing over every state continuation after a fixed event index leaves exactly the endpoint
weight of the preceding state word.  This finite identity is the discrete Markov component of
intermediate-time marginalization; time-simplex disintegration is handled separately.

## Main results

- `finiteStateTimeDependentMarkovPrefixTimes`: the first block of a complete time vector.
- `finiteStateTimeDependentMarkovCutStateIndex`: the state occupied after that block.
- `sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_cutState`: exact erasure of all
  later state coordinates.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The first `earlierCount` coordinates of a time vector with a later block. -/
def finiteStateTimeDependentMarkovPrefixTimes
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) : Fin earlierCount → ℝ :=
  fun index ↦ times (Fin.castAdd laterCount index)

/-- State-word index occupied after the first `earlierCount` events. -/
def finiteStateTimeDependentMarkovCutStateIndex
    (earlierCount laterCount : ℕ) : Fin (earlierCount + laterCount + 1) :=
  ⟨earlierCount, by omega⟩

/-- Removing the final time coordinate does not change the preceding time block. -/
@[simp]
theorem finiteStateTimeDependentMarkovPrefixTimes_init
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount + 1) → ℝ) :
    finiteStateTimeDependentMarkovPrefixTimes earlierCount laterCount (Fin.init times) =
      finiteStateTimeDependentMarkovPrefixTimes earlierCount (laterCount + 1) times := by
  funext index
  rfl

omit [Fintype State] [DecidableEq State] in
/-- The cut-state coordinate of a snoc state word lies in its preceding word. -/
@[simp]
theorem finiteStateTimeDependentMarkovCutStateIndex_snoc
    (earlierCount laterCount : ℕ)
    (priorStates : Fin (earlierCount + laterCount + 1) → State)
    (finalState : State) :
    (@Fin.snoc (earlierCount + laterCount + 1) (fun _ ↦ State)
        priorStates finalState : Fin (earlierCount + laterCount + 2) → State)
        ⟨earlierCount, by omega⟩ =
      priorStates ⟨earlierCount, by omega⟩ := by
  change (@Fin.snoc (earlierCount + laterCount + 1) (fun _ ↦ State)
      priorStates finalState)
      (⟨earlierCount, by omega⟩ : Fin (earlierCount + laterCount + 1)).castSucc = _
  rw [Fin.snoc_castSucc]

/-- Summing every state continuation after a fixed event index leaves the endpoint weight of the
preceding state word. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_cutState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) (observed : State) :
    (∑ states : Fin (earlierCount + laterCount + 1) → State,
      if states (finiteStateTimeDependentMarkovCutStateIndex
          earlierCount laterCount) = observed then
        finiteStateTimeDependentMarkovUniformizedStateWordWeight
          initial rates times states
      else 0) =
      finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates
          (finiteStateTimeDependentMarkovPrefixTimes
            earlierCount laterCount times) observed := by
  induction laterCount with
  | zero =>
      unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        finiteStateTimeDependentMarkovPrefixTimes
        finiteStateTimeDependentMarkovCutStateIndex
      rfl
  | succ laterCount inductionHypothesis =>
      simp only [Nat.add_succ]
      rw [← (Fin.snocEquiv
        (fun _ : Fin (earlierCount + laterCount + 2) ↦ State)).sum_comp]
      rw [Fintype.sum_prod_type]
      change
        (∑ finalState : State,
          ∑ priorStates : Fin (earlierCount + laterCount + 1) → State,
            if (@Fin.snoc (earlierCount + laterCount + 1) (fun _ ↦ State)
                priorStates finalState)
                (finiteStateTimeDependentMarkovCutStateIndex
                  earlierCount (laterCount + 1)) = observed then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                initial rates times
                  (@Fin.snoc (earlierCount + laterCount + 1) (fun _ ↦ State)
                    priorStates finalState)
            else 0) = _
      simp only [finiteStateTimeDependentMarkovCutStateIndex]
      simp_rw [finiteStateTimeDependentMarkovCutStateIndex_snoc]
      simp_rw [finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc]
      rw [Finset.sum_comm]
      have hErase (priorStates : Fin (earlierCount + laterCount + 1) → State) :
          (∑ finalState : State,
            if priorStates ⟨earlierCount, by omega⟩ = observed then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                  initial rates (Fin.init times) priorStates *
                (rates.uniformizedTransitionPMF
                  (times (Fin.last (earlierCount + laterCount)))
                  (priorStates (Fin.last (earlierCount + laterCount)))
                  finalState).toReal
            else 0) =
          if priorStates ⟨earlierCount, by omega⟩ = observed then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates (Fin.init times) priorStates
          else 0 := by
        by_cases hObserved : priorStates ⟨earlierCount, by omega⟩ = observed
        · simp only [hObserved, ite_true]
          rw [← Finset.mul_sum]
          rw [PMF.sum_toReal]
          exact mul_one _
        · simp only [hObserved, ite_false, Finset.sum_const_zero]
      calc
        _ = ∑ priorStates : Fin (earlierCount + laterCount + 1) → State,
            if priorStates ⟨earlierCount, by omega⟩ = observed then
              finiteStateTimeDependentMarkovUniformizedStateWordWeight
                initial rates (Fin.init times) priorStates
            else 0 := by
          apply Finset.sum_congr rfl
          intro priorStates _hPriorStates
          exact hErase priorStates
        _ = _ := by
          have hInduction := inductionHypothesis (Fin.init times)
          simpa only [finiteStateTimeDependentMarkovCutStateIndex,
            finiteStateTimeDependentMarkovPrefixTimes_init] using! hInduction

end

end FiniteMarkovProcesses.Probability
