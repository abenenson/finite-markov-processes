/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovInitialStateMarginal

/-!
# Endpoint word weights for time-dependent uniformized chains

This module isolates the finite algebra behind the time-dependent forward equation.  Appending
one final state factors a complete common-clock word weight into its prior word weight and the
last time-dependent transition probability.  Summing that identity gives the exact endpoint
recursion at every fixed ordered event-time vector.

No time integration, compensator, or path large-deviation claim is made here.

## Main results

- `finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc`.
- `finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_succ`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Total fixed-time-vector word weight whose final occupied state is one specified state. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (observed : State) : ℝ :=
  ∑ states : Fin (eventCount + 1) → State,
    if states (Fin.last eventCount) = observed then
      finiteStateTimeDependentMarkovUniformizedStateWordWeight
        initial rates times states
    else 0

/-- Appending one final state factors the complete time-dependent word weight at its last
transition. -/
theorem finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin (eventCount + 1) → ℝ)
    (priorStates : Fin (eventCount + 1) → State) (target : State) :
    finiteStateTimeDependentMarkovUniformizedStateWordWeight initial rates times
        (Fin.snoc priorStates target) =
      finiteStateTimeDependentMarkovUniformizedStateWordWeight initial rates
          (Fin.init times) priorStates *
        (rates.uniformizedTransitionPMF (times (Fin.last eventCount))
          (priorStates (Fin.last eventCount)) target).toReal := by
  unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
    finiteStateTimeDependentMarkovContinuationWeight
  simp only [Fin.cons_self_tail]
  rw [Fin.prod_univ_castSucc]
  have hSuccessor (index : Fin eventCount) :
      index.castSucc.succ = index.succ.castSucc := by
    rfl
  simp_rw [hSuccessor, Fin.snoc_castSucc]
  simp only [Fin.init]
  have hLast : (Fin.last eventCount).succ = Fin.last (eventCount + 1) := by
    rfl
  rw [hLast, Fin.snoc_last]
  have hZero :
      (0 : Fin (eventCount + 2)) = (0 : Fin (eventCount + 1)).castSucc := by
    rfl
  rw [hZero, Fin.snoc_castSucc]
  ring

/-- With no virtual events, the endpoint word weight is exactly the supplied initial mass. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_zero
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (times : Fin 0 → ℝ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates times observed =
      (initial observed).toReal := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  simpa only [Fin.last_zero] using
    sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_initialState
      initial rates times observed

/-- Exact last-event endpoint recursion at one fixed virtual event-time vector. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_succ
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin (eventCount + 1) → ℝ) (target : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates times target =
      ∑ source : State,
        finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
            initial rates (Fin.init times) source *
          (rates.uniformizedTransitionPMF (times (Fin.last eventCount))
            source target).toReal := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  rw [← (Fin.snocEquiv (fun _ : Fin (eventCount + 2) ↦ State)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hSnocEquiv (finalState : State)
      (priorStates : Fin (eventCount + 1) → State) :
      (Fin.snocEquiv (fun _ : Fin (eventCount + 2) ↦ State))
          (finalState, priorStates) =
        Fin.snoc priorStates finalState := by
    rfl
  simp_rw [hSnocEquiv, Fin.snoc_last]
  change (∑ finalState : State, ∑ priorStates : Fin (eventCount + 1) → State,
    if finalState = target then
      finiteStateTimeDependentMarkovUniformizedStateWordWeight initial rates times
        (Fin.snoc priorStates finalState)
    else 0) = _
  rw [Finset.sum_eq_single target]
  · simp only [ite_true]
    simp_rw [finiteStateTimeDependentMarkovUniformizedStateWordWeight_snoc]
    symm
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro priorStates _hPriorStates
    rw [Finset.sum_eq_single (priorStates (Fin.last eventCount))]
    · simp
    · intro source _hSource hNe
      simp only [hNe.symm, ite_false, zero_mul]
    · simp
  · intro finalState _hFinalState hNe
    simp only [hNe, ite_false]
    exact Finset.sum_const_zero
  · simp

end

end FiniteMarkovProcesses.Probability
