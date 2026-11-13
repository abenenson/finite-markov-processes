/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowObservation
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCountMoment

/-!
# State-observation moments for bounded time-dependent Markov histories

The occupied-state membership indicator at one physical time is a measurable Bernoulli-valued
observable on the complete finite-history carrier.  Under every normalized bounded
time-dependent physical source it has a finite second moment and variance at most one, uniformly
in the initial PMF, rate profile, state, and observation time.

## Main declarations

- `finiteJumpHistoryStateMembershipAtTime`.
- `memLp_two_finiteJumpHistoryStateMembershipAtTime`.
- `variance_finiteJumpHistoryStateMembershipAtTime_le_one`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Indicator that a finite history occupies the selected state at the selected physical time. -/
def finiteJumpHistoryStateMembershipAtTime
    (time : ℝ) (observed : State) (history : FiniteJumpHistory State) : ℝ :=
  FiniteJumpHistory.stateMembershipIndicator (history.stateAtTime time) observed

/-- Fixed-time state membership is measurable on the complete finite-history carrier. -/
theorem measurable_finiteJumpHistoryStateMembershipAtTime
    (time : ℝ) (observed : State) :
    Measurable (finiteJumpHistoryStateMembershipAtTime time observed :
      FiniteJumpHistory State → ℝ) :=
  (FiniteJumpHistory.measurable_stateMembershipIndicator observed).comp
    (FiniteJumpHistory.measurable_stateAtTime time)

/-- State membership is jointly measurable in the complete unbounded history and physical
observation time. -/
theorem measurable_finiteJumpHistoryStateMembershipAtTime_uncurry
    (observed : State) :
    Measurable fun data : FiniteJumpHistory State × ℝ ↦
      finiteJumpHistoryStateMembershipAtTime data.2 observed data.1 :=
  (FiniteJumpHistory.measurable_stateMembershipIndicator observed).comp
    FiniteJumpHistory.measurable_stateAtTime_uncurry

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A state-membership observation always lies in the closed unit interval. -/
theorem finiteJumpHistoryStateMembershipAtTime_mem_Icc
    (time : ℝ) (observed : State) (history : FiniteJumpHistory State) :
    finiteJumpHistoryStateMembershipAtTime time observed history ∈ Set.Icc (0 : ℝ) 1 := by
  unfold finiteJumpHistoryStateMembershipAtTime
    FiniteJumpHistory.stateMembershipIndicator
  split <;> simp

/-- Every fixed-time state-membership observation has a finite second moment. -/
theorem memLp_two_finiteJumpHistoryStateMembershipAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (observed : State) :
    MemLp (finiteJumpHistoryStateMembershipAtTime time observed :
      FiniteJumpHistory State → ℝ) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  exact MemLp.of_bound
    (measurable_finiteJumpHistoryStateMembershipAtTime time observed).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun history ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (finiteJumpHistoryStateMembershipAtTime_mem_Icc time observed history).1]
      exact (finiteJumpHistoryStateMembershipAtTime_mem_Icc time observed history).2)

/-- Fixed-time state-membership variance is uniformly bounded by one. -/
theorem variance_finiteJumpHistoryStateMembershipAtTime_le_one
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (observed : State) :
    variance (finiteJumpHistoryStateMembershipAtTime time observed :
      FiniteJumpHistory State → ℝ)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤ 1 := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  calc
    variance (finiteJumpHistoryStateMembershipAtTime time observed :
        FiniteJumpHistory State → ℝ) law ≤
      ∫ history : FiniteJumpHistory State,
        (finiteJumpHistoryStateMembershipAtTime time observed history) ^ 2 ∂law :=
      variance_le_expectation_sq
        (measurable_finiteJumpHistoryStateMembershipAtTime
          time observed).aestronglyMeasurable
    _ ≤ ∫ _history : FiniteJumpHistory State, (1 : ℝ) ∂law := by
      apply integral_mono
      · exact (memLp_two_finiteJumpHistoryStateMembershipAtTime
          initial rates duration time observed).integrable_sq
      · exact integrable_const 1
      · intro history
        rcases
          finiteJumpHistoryStateMembershipAtTime_mem_Icc time observed history
          with ⟨hNonnegative, hUpper⟩
        change
          (finiteJumpHistoryStateMembershipAtTime time observed history) ^ 2 ≤ 1
        nlinarith [sq_nonneg
          (finiteJumpHistoryStateMembershipAtTime time observed history)]
    _ = 1 := by simp

end

end FiniteMarkovProcesses.Probability
