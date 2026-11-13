/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowObservation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpReplication

/-!
# Empirical density and directional flow of finite jump histories

This module aggregates a nonempty finite family of complete jump histories into empirical state
density and normalized one-way transition counts.  Actual occupied-state density and the density
reconstructed from directional flow are defined independently, then identified by microscopic
continuity on the ordered physical carrier.

The published density--directional-flow path is kept distinct from the richer finite sufficient
statistic containing the sample size, duration, endpoint data, total directional counts, and
occupation times.  Net current and empirical traffic are derived projections; neither replaces the
two ordered flow coordinates.

## Main results

- `PositiveFiniteJumpHistoryReplicas.measurable_empiricalDensityDirectionalFlowPath`:
  measurability of the published observation surface.
- `PositiveFiniteJumpHistoryReplicas.empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime`:
  non-tautological empirical continuity.
- `PositiveFiniteJumpHistoryReplicas.measurable_empiricalCompleteSufficientStatistic`:
  measurability of the separate exact finite-action statistic.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace FiniteJumpHistory

universe u

noncomputable section

variable {State : Type u}

/-- Total time spent in one state over a complete finite jump history. -/
def occupationTimeInState [DecidableEq State]
    (history : FiniteJumpHistory State) (duration : ℝ) (state : State) : ℝ :=
  ∑ index : Fin (history.jumpCount + 1),
    if history.states index = state then history.dwellTime duration index else 0

/-- Fixed-duration occupation time in one state is measurable on the complete history carrier. -/
theorem measurable_occupationTimeInState
    [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    [DecidableEq State] (duration : ℝ) (state : State) :
    Measurable fun history : FiniteJumpHistory State =>
      history.occupationTimeInState duration state := by
  rw [measurable_sigma_iff]
  intro eventCount
  change Measurable fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
    ∑ index : Fin (eventCount + 1),
      if data.1 index = state then dwellTimeVector duration data.2 index else 0
  apply Finset.measurable_sum
  intro index _
  have hState : MeasurableSet
      {data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) |
        data.1 index = state} :=
    (Measurable.eq ((measurable_pi_apply index).comp measurable_fst)
      measurable_const).setOf
  exact Measurable.ite hState
    ((measurable_dwellTimeVector_apply duration index).comp measurable_snd)
    measurable_const

/-- Weighting state indicators and summing over the finite state space selects the occupied
state's weight. -/
theorem sum_stateMembershipIndicator_mul
    [Fintype State] [DecidableEq State] (state : State) (weight : State → ℝ) :
    (∑ observed, stateMembershipIndicator state observed * weight observed) = weight state := by
  rw [Finset.sum_eq_single state]
  · simp [stateMembershipIndicator]
  · intro observed _ hObserved
    simp [stateMembershipIndicator, Ne.symm hObserved]
  · simp

/-- On an ordered history, weighting cumulative directional counts and summing over ordered state
pairs recovers the corresponding sum over the complete transition word. -/
theorem sum_directedTransitionCountAtTime_mul
    [Fintype State] [DecidableEq State]
    (history : FiniteJumpHistory State) (duration : ℝ)
    (weight : State → State → ℝ) (hOrdered : history.OrderedBefore duration) :
    (∑ source, ∑ target,
      (history.directedTransitionCountAtTime duration source target : ℝ) *
        weight source target) =
      ∑ index : Fin history.jumpCount,
        weight (history.states index.castSucc) (history.states index.succ) := by
  rcases history with ⟨eventCount, states, times⟩
  change (∑ source, ∑ target,
    (directedTransitionCountAtTimeVector states times duration source target : ℝ) *
      weight source target) =
    ∑ index : Fin eventCount, weight (states index.castSucc) (states index.succ)
  change times ∈ orderedJumpTimes eventCount duration at hOrdered
  simp only [directedTransitionCountAtTimeVector, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun target index =>
    (if times index ≤ duration ∧ states index.castSucc = _ ∧
      states index.succ = target then 1 else 0) * weight _ target)]
  rw [Finset.sum_comm (f := fun source index =>
    ∑ target, (if times index ≤ duration ∧ states index.castSucc = source ∧
      states index.succ = target then 1 else 0) * weight source target)]
  apply Fintype.sum_congr
  intro index
  have hTime : times index ≤ duration := (hOrdered.1 index).2.le
  simp only [hTime, true_and]
  rw [Finset.sum_eq_single (states index.castSucc)]
  · rw [Finset.sum_eq_single (states index.succ)]
    · simp
    · intro target _ hTarget
      simp [Ne.symm hTarget]
    · simp
  · intro source _ hSource
    simp [Ne.symm hSource]
  · simp

/-- Weighting occupation coordinates and summing over states recovers the dwell-weighted complete
state word. -/
theorem sum_occupationTimeInState_mul
    [Fintype State] [DecidableEq State]
    (history : FiniteJumpHistory State) (duration : ℝ) (weight : State → ℝ) :
    (∑ state, history.occupationTimeInState duration state * weight state) =
      ∑ index : Fin (history.jumpCount + 1),
        history.dwellTime duration index * weight (history.states index) := by
  rcases history with ⟨eventCount, states, times⟩
  change (∑ state, (∑ index : Fin (eventCount + 1),
    if states index = state then dwellTimeVector duration times index else 0) * weight state) =
    ∑ index : Fin (eventCount + 1),
      dwellTimeVector duration times index * weight (states index)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro index
  rw [Finset.sum_eq_single (states index)]
  · simp
  · intro state _ hState
    simp [Ne.symm hState]
  · simp

end

end FiniteJumpHistory

namespace FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

/-- A nonempty finite family of complete jump histories, indexed so that its cardinality is the
successor particle count used by the empirical normalization and later LDP speed. -/
abbrev PositiveFiniteJumpHistoryReplicas (State : Type u) (successorIndex : ℕ) :=
  Fin (successorIndex + 1) → FiniteJumpHistory State

/-- The published observation surface: actual empirical density path and cumulative normalized
one-way-flow path. -/
abbrev EmpiricalDensityDirectionalFlowPath (State : Type u) :=
  (ℝ → State → ℝ) × (ℝ → State → State → ℝ)

/-- The richer finite-action statistic.  It records, in order, positive particle count, duration,
the complete published density--directional-flow path, the redundantly reconstructed continuity
density path, initial density, occupation, and terminal density. -/
abbrev FiniteJumpEmpiricalCompleteSufficientStatistic (State : Type u) :=
  ℕ × ℝ × EmpiricalDensityDirectionalFlowPath State × (ℝ → State → ℝ) ×
    (State → ℝ) × (State → ℝ) × (State → ℝ)

namespace PositiveFiniteJumpHistoryReplicas

/-- Empirical density of initial particle states. -/
def empiricalInitialDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) : ℝ :=
  (∑ replica, FiniteJumpHistory.stateMembershipIndicator
    (histories replica).initialState state) / (successorIndex + 1 : ℝ)

/-- Actual empirical density obtained from independently selected particle states at a physical
time. -/
def empiricalDensityAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) : ℝ :=
  (∑ replica, FiniteJumpHistory.stateMembershipIndicator
    ((histories replica).stateAtTime time) state) / (successorIndex + 1 : ℝ)

/-- Cumulative number of ordered `source -> target` jumps per particle at a physical time. -/
def empiricalSpecificDirectionalFlowAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) : ℝ :=
  (∑ replica, ((histories replica).directedTransitionCountAtTime
    time source target : ℝ)) / (successorIndex + 1 : ℝ)

/-- Density reconstructed from initial density and the divergence of cumulative one-way flow. -/
def empiricalContinuityDensityAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) : ℝ :=
  empiricalInitialDensity successorIndex histories state +
    ∑ source, empiricalSpecificDirectionalFlowAtTime
      successorIndex histories time source state -
    ∑ target, empiricalSpecificDirectionalFlowAtTime
      successorIndex histories time state target

/-- Total occupation time in one state per particle. -/
def empiricalOccupationTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State) : ℝ :=
  (∑ replica, (histories replica).occupationTimeInState duration state) /
    (successorIndex + 1 : ℝ)

/-- Empirical density of the complete histories' final state words. -/
def empiricalFinalDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) : ℝ :=
  (∑ replica, FiniteJumpHistory.stateMembershipIndicator
    (histories replica).finalState state) / (successorIndex + 1 : ℝ)

/-- Empirical terminal density selected at the physical duration. -/
def empiricalTerminalDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State) : ℝ :=
  empiricalDensityAtTime successorIndex histories duration state

/-- Net empirical current obtained by antisymmetrizing the two one-way flows. -/
def empiricalCurrentAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) : ℝ :=
  empiricalSpecificDirectionalFlowAtTime successorIndex histories time source target -
    empiricalSpecificDirectionalFlowAtTime successorIndex histories time target source

/-- Empirical traffic obtained by symmetrizing the two one-way flows.  This count-level observable
is distinct from generator reactivity. -/
def empiricalTrafficAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) : ℝ :=
  empiricalSpecificDirectionalFlowAtTime successorIndex histories time source target +
    empiricalSpecificDirectionalFlowAtTime successorIndex histories time target source

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Current together with count traffic recovers the forward ordered one-way-flow coordinate.
Current alone does not supply this inversion. -/
theorem empiricalSpecificDirectionalFlowAtTime_eq_traffic_add_current_div_two
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) :
    empiricalSpecificDirectionalFlowAtTime successorIndex histories time source target =
      (empiricalTrafficAtTime successorIndex histories time source target +
        empiricalCurrentAtTime successorIndex histories time source target) / 2 := by
  unfold empiricalTrafficAtTime empiricalCurrentAtTime
  ring

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Current together with count traffic recovers the reverse ordered one-way-flow coordinate. -/
theorem empiricalSpecificDirectionalFlowAtTime_reverse_eq_traffic_sub_current_div_two
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) :
    empiricalSpecificDirectionalFlowAtTime successorIndex histories time target source =
      (empiricalTrafficAtTime successorIndex histories time source target -
        empiricalCurrentAtTime successorIndex histories time source target) / 2 := by
  unfold empiricalTrafficAtTime empiricalCurrentAtTime
  ring

/-- Published density--directional-flow path, with no finite-action-only coordinates added. -/
def empiricalDensityDirectionalFlowPath (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    EmpiricalDensityDirectionalFlowPath State :=
  (fun time state => empiricalDensityAtTime successorIndex histories time state,
    fun time source target =>
      empiricalSpecificDirectionalFlowAtTime successorIndex histories time source target)

/-- Complete empirical statistic used by finite action factorization.  This is intentionally not
the published LDP observation carrier: it contains that path as a named recoverable coordinate and
adds the finite-action and redundant continuity data separately. -/
def empiricalCompleteSufficientStatistic (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    FiniteJumpEmpiricalCompleteSufficientStatistic State :=
  (successorIndex + 1, duration,
    empiricalDensityDirectionalFlowPath successorIndex histories,
    fun time state =>
      empiricalContinuityDensityAtTime successorIndex histories time state,
    empiricalInitialDensity successorIndex histories,
    empiricalOccupationTime successorIndex histories duration,
    empiricalTerminalDensity successorIndex histories duration)

/-- Recover the exact published observation path from the richer finite statistic. -/
def completeSufficientStatisticDensityDirectionalFlowPath
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) :
    EmpiricalDensityDirectionalFlowPath State :=
  statistic.2.2.1

/-- Recover the independently reconstructed continuity-density path from the richer finite
statistic. -/
def completeSufficientStatisticContinuityDensityPath
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : ℝ → State → ℝ :=
  statistic.2.2.2.1

/-- Recover the positive particle count from the richer finite statistic. -/
def completeSufficientStatisticParticleCount
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : ℕ :=
  statistic.1

/-- Recover the physical observation duration from the richer finite statistic. -/
def completeSufficientStatisticDuration
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : ℝ :=
  statistic.2.1

/-- Recover initial empirical density from the richer finite statistic. -/
def completeSufficientStatisticInitialDensity
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : State → ℝ :=
  statistic.2.2.2.2.1

/-- Recover empirical occupation time from the richer finite statistic. -/
def completeSufficientStatisticOccupation
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : State → ℝ :=
  statistic.2.2.2.2.2.1

/-- Recover empirical terminal density from the richer finite statistic. -/
def completeSufficientStatisticTerminalDensity
    (statistic : FiniteJumpEmpiricalCompleteSufficientStatistic State) : State → ℝ :=
  statistic.2.2.2.2.2.2

/-- Empirical initial density is measurable on the nonempty replica carrier. -/
theorem measurable_empiricalInitialDensity (successorIndex : ℕ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalInitialDensity successorIndex histories state := by
  unfold empiricalInitialDensity
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _
  exact (FiniteJumpHistory.measurable_stateMembershipIndicator state).comp
    (FiniteJumpHistory.measurable_initialState.comp (measurable_pi_apply replica))

/-- Actual empirical density at a fixed time is measurable on the replica carrier. -/
theorem measurable_empiricalDensityAtTime
    (successorIndex : ℕ) (time : ℝ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalDensityAtTime successorIndex histories time state := by
  unfold empiricalDensityAtTime
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _
  exact (FiniteJumpHistory.measurable_stateMembershipIndicator state).comp
    ((FiniteJumpHistory.measurable_stateAtTime time).comp (measurable_pi_apply replica))

/-- Empirical one-way flow at a fixed time and ordered state pair is measurable. -/
theorem measurable_empiricalSpecificDirectionalFlowAtTime
    (successorIndex : ℕ) (time : ℝ) (source target : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalSpecificDirectionalFlowAtTime
        successorIndex histories time source target := by
  unfold empiricalSpecificDirectionalFlowAtTime
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _
  exact (measurable_of_countable fun count : ℕ => (count : ℝ)).comp
    ((FiniteJumpHistory.measurable_directedTransitionCountAtTime
      time source target).comp (measurable_pi_apply replica))

/-- Continuity-reconstructed density at a fixed time is measurable. -/
theorem measurable_empiricalContinuityDensityAtTime
    (successorIndex : ℕ) (time : ℝ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalContinuityDensityAtTime successorIndex histories time state := by
  unfold empiricalContinuityDensityAtTime
  apply Measurable.sub
  · apply Measurable.add
    · exact measurable_empiricalInitialDensity successorIndex state
    · exact Finset.measurable_sum _ fun source _ =>
        measurable_empiricalSpecificDirectionalFlowAtTime
          successorIndex time source state
  · exact Finset.measurable_sum _ fun target _ =>
      measurable_empiricalSpecificDirectionalFlowAtTime
        successorIndex time state target

/-- Empirical occupation time is measurable on the nonempty replica carrier. -/
theorem measurable_empiricalOccupationTime
    (successorIndex : ℕ) (duration : ℝ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalOccupationTime successorIndex histories duration state := by
  unfold empiricalOccupationTime
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _
  exact (FiniteJumpHistory.measurable_occupationTimeInState duration state).comp
    (measurable_pi_apply replica)

/-- Empirical final-state density is measurable on the nonempty replica carrier. -/
theorem measurable_empiricalFinalDensity (successorIndex : ℕ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalFinalDensity successorIndex histories state := by
  unfold empiricalFinalDensity
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _
  exact (FiniteJumpHistory.measurable_stateMembershipIndicator state).comp
    (FiniteJumpHistory.measurable_finalState.comp (measurable_pi_apply replica))

/-- Empirical terminal density is measurable on the nonempty replica carrier. -/
theorem measurable_empiricalTerminalDensity
    (successorIndex : ℕ) (duration : ℝ) (state : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalTerminalDensity successorIndex histories duration state :=
  measurable_empiricalDensityAtTime successorIndex duration state

/-- Empirical net current at a fixed time is measurable. -/
theorem measurable_empiricalCurrentAtTime
    (successorIndex : ℕ) (time : ℝ) (source target : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalCurrentAtTime successorIndex histories time source target :=
  (measurable_empiricalSpecificDirectionalFlowAtTime
    successorIndex time source target).sub
      (measurable_empiricalSpecificDirectionalFlowAtTime
        successorIndex time target source)

/-- Empirical traffic at a fixed time is measurable. -/
theorem measurable_empiricalTrafficAtTime
    (successorIndex : ℕ) (time : ℝ) (source target : State) :
    Measurable fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalTrafficAtTime successorIndex histories time source target :=
  (measurable_empiricalSpecificDirectionalFlowAtTime
    successorIndex time source target).add
      (measurable_empiricalSpecificDirectionalFlowAtTime
        successorIndex time target source)

/-- The exact published density--directional-flow path is measurable. -/
theorem measurable_empiricalDensityDirectionalFlowPath (successorIndex : ℕ) :
    Measurable
      (empiricalDensityDirectionalFlowPath (State := State) successorIndex) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun time => Measurable.of_eval fun state =>
      measurable_empiricalDensityAtTime successorIndex time state
  · exact Measurable.of_eval fun time => Measurable.of_eval fun source =>
      Measurable.of_eval fun target =>
        measurable_empiricalSpecificDirectionalFlowAtTime
          successorIndex time source target

/-- The richer exact finite-action statistic is measurable separately from the published path. -/
theorem measurable_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ) :
    Measurable
      (empiricalCompleteSufficientStatistic (State := State) successorIndex duration) := by
  apply Measurable.prodMk measurable_const
  apply Measurable.prodMk measurable_const
  apply Measurable.prodMk
  · exact measurable_empiricalDensityDirectionalFlowPath successorIndex
  apply Measurable.prodMk
  · exact Measurable.of_eval fun time => Measurable.of_eval fun state =>
      measurable_empiricalContinuityDensityAtTime successorIndex time state
  apply Measurable.prodMk
  · exact Measurable.of_eval fun state =>
      measurable_empiricalInitialDensity successorIndex state
  apply Measurable.prodMk
  · exact Measurable.of_eval fun state =>
      measurable_empiricalOccupationTime successorIndex duration state
  · exact Measurable.of_eval fun state =>
      measurable_empiricalTerminalDensity successorIndex duration state

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The projection from the richer finite statistic to the exact published observation path is
measurable. -/
theorem measurable_completeSufficientStatisticDensityDirectionalFlowPath :
    Measurable
      (completeSufficientStatisticDensityDirectionalFlowPath (State := State)) :=
  measurable_fst.comp <| measurable_snd.comp measurable_snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The projection from the richer finite statistic to its redundant continuity-density path is
measurable. -/
theorem measurable_completeSufficientStatisticContinuityDensityPath :
    Measurable
      (completeSufficientStatisticContinuityDensityPath (State := State)) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp measurable_snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The particle-count projection from the richer finite statistic is measurable. -/
theorem measurable_completeSufficientStatisticParticleCount :
    Measurable (completeSufficientStatisticParticleCount (State := State)) :=
  measurable_fst

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The duration projection from the richer finite statistic is measurable. -/
theorem measurable_completeSufficientStatisticDuration :
    Measurable (completeSufficientStatisticDuration (State := State)) :=
  measurable_fst.comp measurable_snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The initial-density projection from the richer finite statistic is measurable. -/
theorem measurable_completeSufficientStatisticInitialDensity :
    Measurable (completeSufficientStatisticInitialDensity (State := State)) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp measurable_snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The occupation projection from the richer finite statistic is measurable. -/
theorem measurable_completeSufficientStatisticOccupation :
    Measurable (completeSufficientStatisticOccupation (State := State)) :=
  measurable_fst.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp measurable_snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] in
/-- The terminal-density projection from the richer finite statistic is measurable. -/
theorem measurable_completeSufficientStatisticTerminalDensity :
    Measurable (completeSufficientStatisticTerminalDensity (State := State)) :=
  measurable_snd.comp <| measurable_snd.comp <| measurable_snd.comp <|
    measurable_snd.comp <| measurable_snd.comp measurable_snd

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Constructing the richer statistic and projecting its published coordinate recovers the exact
density--directional-flow observation definitionally. -/
@[simp]
theorem completeSufficientStatisticDensityDirectionalFlowPath_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticDensityDirectionalFlowPath
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      empiricalDensityDirectionalFlowPath successorIndex histories :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Constructing the richer statistic and projecting its redundant coordinate recovers the
independently defined continuity-density path definitionally. -/
@[simp]
theorem completeSufficientStatisticContinuityDensityPath_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticContinuityDensityPath
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      fun time state =>
        empiricalContinuityDensityAtTime successorIndex histories time state :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generated statistic records the exact positive particle count. -/
@[simp]
theorem completeSufficientStatisticParticleCount_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticParticleCount
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      successorIndex + 1 :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generated statistic records the supplied physical duration. -/
@[simp]
theorem completeSufficientStatisticDuration_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticDuration
        (empiricalCompleteSufficientStatistic successorIndex duration histories) = duration :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generated statistic records its independently counted initial density. -/
@[simp]
theorem completeSufficientStatisticInitialDensity_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticInitialDensity
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      empiricalInitialDensity successorIndex histories :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generated statistic records its empirical occupation coordinate. -/
@[simp]
theorem completeSufficientStatisticOccupation_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticOccupation
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      empiricalOccupationTime successorIndex histories duration :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generated statistic records its empirical terminal density. -/
@[simp]
theorem completeSufficientStatisticTerminalDensity_empiricalCompleteSufficientStatistic
    (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    completeSufficientStatisticTerminalDensity
        (empiricalCompleteSufficientStatistic successorIndex duration histories) =
      empiricalTerminalDensity successorIndex histories duration :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical initial density is normalized for every nonempty history family. -/
theorem sum_empiricalInitialDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    ∑ state, empiricalInitialDensity successorIndex histories state = 1 := by
  unfold empiricalInitialDensity
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [FiniteJumpHistory.stateMembershipIndicator]
  positivity

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Actual empirical density is normalized at every time, independently of physicality. -/
theorem sum_empiricalDensityAtTime (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) (time : ℝ) :
    ∑ state, empiricalDensityAtTime successorIndex histories time state = 1 := by
  unfold empiricalDensityAtTime
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [FiniteJumpHistory.stateMembershipIndicator]
  positivity

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical final-state density is normalized for every nonempty history family. -/
theorem sum_empiricalFinalDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    ∑ state, empiricalFinalDensity successorIndex histories state = 1 := by
  unfold empiricalFinalDensity
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [FiniteJumpHistory.stateMembershipIndicator]
  positivity

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical terminal density is normalized for every nonempty history family. -/
theorem sum_empiricalTerminalDensity (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) (duration : ℝ) :
    ∑ state, empiricalTerminalDensity successorIndex histories duration state = 1 :=
  sum_empiricalDensityAtTime successorIndex histories duration

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Multiplying a weighted empirical initial-density sum by particle count recovers the sum of
the corresponding initial-state weights over replicas. -/
theorem particleCount_mul_sum_empiricalInitialDensity_mul
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (weight : State → ℝ) :
    (successorIndex + 1 : ℝ) *
        ∑ state, empiricalInitialDensity successorIndex histories state * weight state =
      ∑ replica, weight (histories replica).initialState := by
  unfold empiricalInitialDensity
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro replica
  exact FiniteJumpHistory.sum_stateMembershipIndicator_mul
    (histories replica).initialState weight

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Multiplying a weighted empirical directional-flow sum by particle count recovers the complete
transition-word weight summed over replicas. -/
theorem particleCount_mul_sum_empiricalSpecificDirectionalFlowAtTime_mul
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (weight : State → State → ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    (successorIndex + 1 : ℝ) *
        ∑ source, ∑ target,
          empiricalSpecificDirectionalFlowAtTime successorIndex histories duration source target *
            weight source target =
      ∑ replica, ∑ index : Fin (histories replica).jumpCount,
        weight ((histories replica).states index.castSucc)
          ((histories replica).states index.succ) := by
  unfold empiricalSpecificDirectionalFlowAtTime
  simp_rw [div_mul_eq_mul_div]
  simp_rw [← Finset.sum_div]
  field_simp
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_comm (f := fun target replica =>
    ((histories replica).directedTransitionCountAtTime duration _ target : ℝ) *
      weight _ target)]
  rw [Finset.sum_comm (f := fun source replica =>
    ∑ target, ((histories replica).directedTransitionCountAtTime duration source target : ℝ) *
      weight source target)]
  apply Fintype.sum_congr
  intro replica
  exact FiniteJumpHistory.sum_directedTransitionCountAtTime_mul
    (histories replica) duration weight (hOrdered replica)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Multiplying a weighted empirical occupation sum by particle count recovers the dwell-weighted
complete state words summed over replicas. -/
theorem particleCount_mul_sum_empiricalOccupationTime_mul
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (weight : State → ℝ) :
    (successorIndex + 1 : ℝ) *
        ∑ state, empiricalOccupationTime successorIndex histories duration state * weight state =
      ∑ replica, ∑ index : Fin ((histories replica).jumpCount + 1),
        (histories replica).dwellTime duration index *
          weight ((histories replica).states index) := by
  unfold empiricalOccupationTime
  simp_rw [div_mul_eq_mul_div]
  simp_rw [← Finset.sum_div]
  field_simp
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro replica
  exact FiniteJumpHistory.sum_occupationTimeInState_mul
    (histories replica) duration weight

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On ordered physical histories, terminal-time selection equals the recorded final-state
density. -/
theorem empiricalTerminalDensity_eq_empiricalFinalDensity
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalTerminalDensity successorIndex histories duration state =
      empiricalFinalDensity successorIndex histories state := by
  unfold empiricalTerminalDensity empiricalDensityAtTime empiricalFinalDensity
  congr 1
  apply Fintype.sum_congr
  intro replica
  rw [FiniteJumpHistory.stateAtTime_eq_finalState_of_orderedBefore
    (histories replica) duration (hOrdered replica)]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Independently observed empirical density equals continuity-reconstructed density on every
family of histories ordered before the common physical duration. -/
theorem empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration time : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalDensityAtTime successorIndex histories time state =
      empiricalContinuityDensityAtTime successorIndex histories time state := by
  have hReplica (replica : Fin (successorIndex + 1)) :=
    FiniteJumpHistory.stateMembershipIndicator_stateAtTime_eq_initial_add_incoming_sub_outgoing
      (histories replica) duration time state (hOrdered replica)
  have hIncoming :
      (∑ replica, ∑ source : State,
        ((histories replica).directedTransitionCountAtTime time source state : ℝ)) =
        ∑ source : State, ∑ replica,
          ((histories replica).directedTransitionCountAtTime time source state : ℝ) :=
    Finset.sum_comm
  have hOutgoing :
      (∑ replica, ∑ target : State,
        ((histories replica).directedTransitionCountAtTime time state target : ℝ)) =
        ∑ target : State, ∑ replica,
          ((histories replica).directedTransitionCountAtTime time state target : ℝ) :=
    Finset.sum_comm
  unfold empiricalDensityAtTime empiricalContinuityDensityAtTime
    empiricalInitialDensity empiricalSpecificDirectionalFlowAtTime
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [← add_div, ← sub_div]
  congr 1
  calc
    _ = ∑ replica, (FiniteJumpHistory.stateMembershipIndicator
          (histories replica).initialState state +
        ∑ source : State,
          ((histories replica).directedTransitionCountAtTime time source state : ℝ) -
        ∑ target : State,
          ((histories replica).directedTransitionCountAtTime time state target : ℝ)) := by
      apply Fintype.sum_congr
      intro replica
      exact hReplica replica
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hIncoming, hOutgoing]

end PositiveFiniteJumpHistoryReplicas

end

end FiniteMarkovProcesses.Probability
