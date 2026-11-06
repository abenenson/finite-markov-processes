/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalStepL1Path
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryHybridBVObservation

/-!
# Explicit hybrid-BV observation of finite jump histories

This module makes the finite empirical density--directional-flow lift constructive.  Each
microscopic event contributes one normalized density increment and, on an off-diagonal
transition, one normalized ordered-flow increment.  The strong-`L1` component is the literal
finite sum of right-continuous event steps, while every distributional derivative is the matching
finite sum of physically restricted weighted Dirac measures.

## Main declarations

- `empiricalDensityDirectionalFlowEventIncrement`: normalized event contribution to every tagged
  macroscopic coordinate;
- `enorm_empiricalDensityDirectionalFlowInitialL1Value`: the tagged initial density has exact
  `l1` norm one;
- `sum_abs_empiricalDensityDirectionalFlowEventIncrement_eq_three_div`: every physical event has
  exact tagged `l1` mass `3 / N`;
- `sum_abs_empiricalDensityDirectionalFlowEventIncrement_le_three_div`: every event has tagged
  `l1` mass at most `3 / N`, including zero-mass self-events;
- `empiricalContinuityDensityDirectionalFlowL1ValueAtTime`: the total path using continuity-
  reconstructed density;
- `empiricalDensityDirectionalFlowExplicitHybridBVPath`: the explicit graph-valued observation.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open FiniteMarkovProcesses.FiniteIntervalBVAlgebra
open scoped BigOperators ENNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Distinct source and target indicators have exact `l1` distance two. -/
theorem sum_abs_stateMembershipIndicator_sub
    (source target : State) (hTransition : source ≠ target) :
    (∑ state : State,
      |FiniteJumpHistory.stateMembershipIndicator target state -
        FiniteJumpHistory.stateMembershipIndicator source state|) = 2 := by
  classical
  calc
    (∑ state : State,
      |FiniteJumpHistory.stateMembershipIndicator target state -
        FiniteJumpHistory.stateMembershipIndicator source state|) =
        ∑ state : State,
          (FiniteJumpHistory.stateMembershipIndicator target state +
            FiniteJumpHistory.stateMembershipIndicator source state) := by
      apply Finset.sum_congr rfl
      intro state _hState
      by_cases hTarget : target = state
      · have hSource : source ≠ state := by
          intro hSource
          exact hTransition (hSource.trans hTarget.symm)
        simp [FiniteJumpHistory.stateMembershipIndicator,
          hTarget, hSource]
      · by_cases hSource : source = state
        · simp [FiniteJumpHistory.stateMembershipIndicator,
            hTarget, hSource]
        · simp [FiniteJumpHistory.stateMembershipIndicator,
            hTarget, hSource]
    _ = (∑ state : State,
          FiniteJumpHistory.stateMembershipIndicator target state) +
        ∑ state : State,
          FiniteJumpHistory.stateMembershipIndicator source state :=
      Finset.sum_add_distrib
    _ = 1 + 1 := by
      have hTargetSum :
          (∑ state : State,
            FiniteJumpHistory.stateMembershipIndicator target state) = 1 := by
        simpa using FiniteJumpHistory.sum_stateMembershipIndicator_mul
          target (fun _state : State => (1 : ℝ))
      have hSourceSum :
          (∑ state : State,
            FiniteJumpHistory.stateMembershipIndicator source state) = 1 := by
        simpa using FiniteJumpHistory.sum_stateMembershipIndicator_mul
          source (fun _state : State => (1 : ℝ))
      rw [hTargetSum, hSourceSum]
    _ = 2 := by norm_num

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Exactly one ordered off-diagonal edge matches a distinct source--target pair. -/
theorem sum_offDiagonalTransitionIndicator
    (source target : State) (hTransition : source ≠ target) :
    (∑ edge : FiniteStateOffDiagonalEdge State,
      if source = edge.val.1 ∧ target = edge.val.2 then (1 : ℝ) else 0) = 1 := by
  classical
  let matching : FiniteStateOffDiagonalEdge State :=
    ⟨(source, target), hTransition⟩
  rw [Finset.sum_eq_single matching]
  · simp [matching]
  · intro edge _hEdge hEdge
    by_cases hMatches : source = edge.val.1 ∧ target = edge.val.2
    · exfalso
      apply hEdge
      apply Subtype.ext
      exact Prod.ext hMatches.1.symm hMatches.2.symm
    · simp [hMatches]
  · simp

namespace PositiveFiniteJumpHistoryReplicas

/-- Tagged initial value: empirical initial density and zero cumulative ordered flow. -/
def empiricalDensityDirectionalFlowInitialL1Value
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      match coordinate with
      | Sum.inl state => empiricalInitialDensity successorIndex histories state
      | Sum.inr _edge => 0

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Initial density-coordinate recovery. -/
@[simp]
theorem empiricalDensityDirectionalFlowInitialL1Value_density
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) :
    empiricalDensityDirectionalFlowInitialL1Value
      successorIndex histories (Sum.inl state) =
        empiricalInitialDensity successorIndex histories state := by
  simp [empiricalDensityDirectionalFlowInitialL1Value]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Initial ordered-flow coordinates vanish. -/
@[simp]
theorem empiricalDensityDirectionalFlowInitialL1Value_flow
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (edge : FiniteStateOffDiagonalEdge State) :
    empiricalDensityDirectionalFlowInitialL1Value
      successorIndex histories (Sum.inr edge) = 0 := by
  simp [empiricalDensityDirectionalFlowInitialL1Value]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The tagged initial empirical density has exact `l1` norm one. -/
theorem enorm_empiricalDensityDirectionalFlowInitialL1Value
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    ‖empiricalDensityDirectionalFlowInitialL1Value
      successorIndex histories‖ₑ = 1 := by
  have hNonnegative (state : State) :
      0 ≤ empiricalInitialDensity successorIndex histories state := by
    unfold empiricalInitialDensity
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro replica _hReplica
      unfold FiniteJumpHistory.stateMembershipIndicator
      positivity
    · positivity
  rw [← ofReal_norm, PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
  simp only [Real.norm_eq_abs,
    empiricalDensityDirectionalFlowInitialL1Value_density,
    empiricalDensityDirectionalFlowInitialL1Value_flow,
    abs_zero, Finset.sum_const_zero, add_zero]
  simp_rw [abs_of_nonneg (hNonnegative _)]
  rw [sum_empiricalInitialDensity]
  norm_num

/-- Normalized contribution of one microscopic transition to one tagged macroscopic coordinate. -/
def empiricalDensityDirectionalFlowEventIncrement
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) : ℝ :=
  match coordinate with
  | Sum.inl state =>
      (FiniteJumpHistory.stateMembershipIndicator
          (history.states index.succ) state -
        FiniteJumpHistory.stateMembershipIndicator
          (history.states index.castSucc) state) /
        (successorIndex + 1 : ℝ)
  | Sum.inr edge =>
      (if history.states index.castSucc = edge.val.1 ∧
          history.states index.succ = edge.val.2 then 1 else 0) /
        (successorIndex + 1 : ℝ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every genuine microscopic transition contributes exact tagged `l1` mass `3 / N`: two density
coordinates and one ordered-flow coordinate. -/
theorem sum_abs_empiricalDensityDirectionalFlowEventIncrement_eq_three_div
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount)
    (hTransition :
      history.states index.castSucc ≠ history.states index.succ) :
    (∑ coordinate : EmpiricalDensityDirectionalFlowCoordinate State,
      |empiricalDensityDirectionalFlowEventIncrement
        successorIndex history index coordinate|) =
      3 / (successorIndex + 1 : ℝ) := by
  classical
  have hDenominator : 0 < (successorIndex + 1 : ℝ) := by positivity
  rw [Fintype.sum_sum_type]
  simp only [empiricalDensityDirectionalFlowEventIncrement, abs_div,
    abs_of_pos hDenominator, abs_ite, abs_one, abs_zero]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [sum_abs_stateMembershipIndicator_sub _ _ hTransition,
    sum_offDiagonalTransitionIndicator _ _ hTransition]
  ring

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every microscopic event contributes tagged `l1` mass at most `3 / N`; a self-event contributes
zero. This form applies on the total ordered carrier before reduced physical support is imposed. -/
theorem sum_abs_empiricalDensityDirectionalFlowEventIncrement_le_three_div
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount) :
    (∑ coordinate : EmpiricalDensityDirectionalFlowCoordinate State,
      |empiricalDensityDirectionalFlowEventIncrement
        successorIndex history index coordinate|) ≤
      3 / (successorIndex + 1 : ℝ) := by
  classical
  by_cases hTransition :
      history.states index.castSucc ≠ history.states index.succ
  · exact le_of_eq
      (sum_abs_empiricalDensityDirectionalFlowEventIncrement_eq_three_div
        successorIndex history index hTransition)
  · have hSelf :
        history.states index.castSucc = history.states index.succ :=
      not_ne_iff.mp hTransition
    have hIncrementZero
        (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
        empiricalDensityDirectionalFlowEventIncrement
          successorIndex history index coordinate = 0 := by
      rcases coordinate with state | edge
      · simp [empiricalDensityDirectionalFlowEventIncrement, hSelf]
      · have hNoMatchingEdge :
            ¬(history.states index.castSucc = edge.val.1 ∧
              history.states index.succ = edge.val.2) := by
          rintro ⟨hSource, hTarget⟩
          exact edge.property (hSource.symm.trans (hSelf.trans hTarget))
        simp [empiricalDensityDirectionalFlowEventIncrement,
          hNoMatchingEdge]
    simp_rw [hIncrementZero, abs_zero, Finset.sum_const_zero]
    positivity

/-- The tagged finite-`l1` increment contributed by one microscopic event. -/
def empiricalDensityDirectionalFlowEventIncrementL1Value
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate => empiricalDensityDirectionalFlowEventIncrement
      successorIndex history index coordinate

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Coordinate recovery from one tagged microscopic event increment. -/
@[simp]
theorem empiricalDensityDirectionalFlowEventIncrementL1Value_apply
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    empiricalDensityDirectionalFlowEventIncrementL1Value
      successorIndex history index coordinate =
        empiricalDensityDirectionalFlowEventIncrement
          successorIndex history index coordinate := by
  simp [empiricalDensityDirectionalFlowEventIncrementL1Value]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Multiplying the tagged event increment by a unit scalar step is exactly the coordinatewise
weighted event step. -/
theorem scalarRightEventStep_smul_empiricalDensityDirectionalFlowEventIncrementL1Value
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (index : Fin history.jumpCount) (time : ℝ) :
    scalarRightEventStep (history.jumpTimes index) 1 time •
        empiricalDensityDirectionalFlowEventIncrementL1Value
          successorIndex history index =
      (PiLp.continuousLinearEquiv 1 ℝ
        (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
        (fun coordinate => scalarRightEventStep (history.jumpTimes index)
          (empiricalDensityDirectionalFlowEventIncrement
            successorIndex history index coordinate) time) := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  simp only [PiLp.continuousLinearEquiv_apply]
  unfold scalarRightEventStep
  by_cases hObserved : history.jumpTimes index ≤ time <;> simp [hObserved]

/-- Microscopic-event index of a fixed positive replica family. -/
abbrev EmpiricalDensityDirectionalFlowEventIndex
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :=
  Σ replica : Fin (successorIndex + 1), Fin (histories replica).jumpCount

/-- Explicit strong-`L1` observation: initial tagged density plus every vector-valued event
step, with no quotient representative chosen nonconstructively. -/
def empiricalDensityDirectionalFlowExplicitL1Path
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) :
    FiniteIntervalL1Path (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  finiteIntervalConstantL1Path duration
      (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories) +
    finiteCoordinateVectorEventStepL1PathSum duration
      (fun event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories =>
        (histories event.1).jumpTimes event.2)
      (fun event => empiricalDensityDirectionalFlowEventIncrementL1Value
        successorIndex (histories event.1) event.2)

/-- Literal finite-step path reconstructed from initial density and all microscopic events. -/
def empiricalDensityDirectionalFlowEventStepL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  empiricalDensityDirectionalFlowInitialL1Value successorIndex histories +
    ∑ replica, ∑ index : Fin (histories replica).jumpCount,
      (PiLp.continuousLinearEquiv 1 ℝ
        (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
          fun coordinate => scalarRightEventStep
            ((histories replica).jumpTimes index)
            (empiricalDensityDirectionalFlowEventIncrement
              successorIndex (histories replica) index coordinate) time

/-- Tagged observation using continuity-reconstructed density and the unchanged ordered flow. -/
def empiricalContinuityDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      match coordinate with
      | Sum.inl state => empiricalContinuityDensityAtTime
          successorIndex histories time state
      | Sum.inr edge => empiricalSpecificDirectionalFlowAtTime
          successorIndex histories time edge.val.1 edge.val.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Coordinate formula for the literal event-step reconstruction. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories time coordinate =
      empiricalDensityDirectionalFlowInitialL1Value
          successorIndex histories coordinate +
        ∑ replica, ∑ index : Fin (histories replica).jumpCount,
          scalarRightEventStep ((histories replica).jumpTimes index)
            (empiricalDensityDirectionalFlowEventIncrement
              successorIndex (histories replica) index coordinate) time := by
  let coordinateEquivalence := PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
  change (coordinateEquivalence
    (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories +
      ∑ replica, ∑ index : Fin (histories replica).jumpCount,
        coordinateEquivalence.symm
          (fun query => scalarRightEventStep
            ((histories replica).jumpTimes index)
            (empiricalDensityDirectionalFlowEventIncrement
              successorIndex (histories replica) index query) time))) coordinate = _
  rw [map_add, map_sum]
  simp only [map_sum, coordinateEquivalence,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [Pi.add_apply, PiLp.continuousLinearEquiv_apply]
  simp only [Finset.sum_apply]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- One ordered-flow coordinate of the event-step reconstruction is the exact empirical
cumulative one-way flow. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_flow
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (edge : FiniteStateOffDiagonalEdge State) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories time (Sum.inr edge) =
        empiricalSpecificDirectionalFlowAtTime successorIndex histories time
          edge.val.1 edge.val.2 := by
  rw [empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply]
  simp only [empiricalDensityDirectionalFlowInitialL1Value_flow,
    zero_add, empiricalDensityDirectionalFlowEventIncrement,
    scalarRightEventStep]
  unfold empiricalSpecificDirectionalFlowAtTime
    FiniteJumpHistory.directedTransitionCountAtTime
    FiniteJumpHistory.directedTransitionCountAtTimeVector
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ replica, ∑ index : Fin (histories replica).jumpCount,
        if (histories replica).jumpTimes index ≤ time then
          (if (histories replica).states index.castSucc = edge.val.1 ∧
              (histories replica).states index.succ = edge.val.2 then 1 else 0) /
            (successorIndex + 1 : ℝ)
        else 0) =
        ∑ replica, ∑ index : Fin (histories replica).jumpCount,
          (if (histories replica).jumpTimes index ≤ time ∧
              (histories replica).states index.castSucc = edge.val.1 ∧
              (histories replica).states index.succ = edge.val.2 then 1 else 0) /
            (successorIndex + 1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro replica _hReplica
      apply Finset.sum_congr rfl
      intro index _hIndex
      by_cases hTime : (histories replica).jumpTimes index ≤ time <;> simp [hTime]
    _ = ∑ replica,
        (∑ index : Fin (histories replica).jumpCount,
          if (histories replica).jumpTimes index ≤ time ∧
              (histories replica).states index.castSucc = edge.val.1 ∧
              (histories replica).states index.succ = edge.val.2 then 1 else 0) /
            (successorIndex + 1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro replica _hReplica
      rw [Finset.sum_div]
    _ = _ := by rw [Finset.sum_div]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- One density coordinate of the event-step reconstruction is the exact continuity-reconstructed
empirical density. -/
theorem sum_empiricalDensityDirectionalFlowEventIncrement_density
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (time : ℝ) (state : State) :
    (∑ index : Fin history.jumpCount,
      scalarRightEventStep (history.jumpTimes index)
        (empiricalDensityDirectionalFlowEventIncrement
          successorIndex history index (Sum.inl state)) time) =
      ((∑ source : State,
          (history.directedTransitionCountAtTime time source state : ℝ)) -
        ∑ target : State,
          (history.directedTransitionCountAtTime time state target : ℝ)) /
        (successorIndex + 1 : ℝ) := by
  rcases history with ⟨eventCount, states, times⟩
  unfold empiricalDensityDirectionalFlowEventIncrement scalarRightEventStep
    FiniteJumpHistory.directedTransitionCountAtTime
    FiniteJumpHistory.jumpTimes FiniteJumpHistory.states FiniteJumpHistory.jumpCount
  calc
    (∑ index : Fin eventCount,
        if times index ≤ time then
          (FiniteJumpHistory.stateMembershipIndicator (states index.succ) state -
            FiniteJumpHistory.stateMembershipIndicator
              (states index.castSucc) state) /
            (successorIndex + 1 : ℝ)
        else 0) =
        (∑ index : Fin eventCount,
          if times index ≤ time then
            FiniteJumpHistory.stateMembershipIndicator (states index.succ) state -
              FiniteJumpHistory.stateMembershipIndicator
                (states index.castSucc) state
          else 0) / (successorIndex + 1 : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro index _hIndex
      by_cases hTime : times index ≤ time <;> simp [hTime]
    _ = _ := by
      congr 1
      rw [FiniteJumpHistory.incomingDirectedTransitionCount_eq_stateArrivalSum,
        FiniteJumpHistory.outgoingDirectedTransitionCount_eq_stateDepartureSum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro index _hIndex
      by_cases hTime : times index ≤ time <;> simp [hTime]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- One density coordinate of the event-step reconstruction is the exact continuity-reconstructed
empirical density. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_density
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories time (Sum.inl state) =
        empiricalContinuityDensityAtTime successorIndex histories time state := by
  rw [empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply]
  simp only [empiricalDensityDirectionalFlowInitialL1Value_density,
    sum_empiricalDensityDirectionalFlowEventIncrement_density]
  unfold empiricalContinuityDensityAtTime
    empiricalSpecificDirectionalFlowAtTime
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sub_div]
  rw [Finset.sum_comm (f := fun replica source =>
      ((histories replica).directedTransitionCountAtTime time source state : ℝ)),
    Finset.sum_comm (f := fun replica target =>
      ((histories replica).directedTransitionCountAtTime time state target : ℝ))]
  simp_rw [Finset.sum_div]
  ring

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal finite event-step reconstruction equals the tagged continuity observation. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_continuity
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories time =
        empiricalContinuityDensityDirectionalFlowL1ValueAtTime
          successorIndex histories time := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  cases coordinate with
  | inl state =>
      simpa only [empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        ContinuousLinearEquiv.apply_symm_apply,
        PiLp.continuousLinearEquiv_apply, WithLp.equiv,
        PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using
        empiricalDensityDirectionalFlowEventStepL1ValueAtTime_density
          successorIndex histories time state
  | inr edge =>
      simpa only [empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        ContinuousLinearEquiv.apply_symm_apply,
        PiLp.continuousLinearEquiv_apply, WithLp.equiv,
        PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using
        empiricalDensityDirectionalFlowEventStepL1ValueAtTime_flow
          successorIndex histories time edge

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit strong-`L1` observation has the literal event-step reconstruction as a
representative. -/
theorem empiricalDensityDirectionalFlowExplicitL1Path_represents
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) :
    FiniteIntervalL1Path.Represents
      (empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration)
      (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories) := by
  let eventTime :
      EmpiricalDensityDirectionalFlowEventIndex successorIndex histories → ℝ :=
    fun event => (histories event.1).jumpTimes event.2
  let eventValue : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories →
      FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
    fun event => empiricalDensityDirectionalFlowEventIncrementL1Value
      successorIndex (histories event.1) event.2
  have hInitial := finiteIntervalConstantL1Path_eventuallyEq duration
    (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories)
  have hEvents := finiteCoordinateVectorEventStepL1PathSum_eventuallyEq
    (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
    duration eventTime eventValue
  have hAdd := Lp.coeFn_add
    (finiteIntervalConstantL1Path duration
      (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories))
    (finiteCoordinateVectorEventStepL1PathSum duration eventTime eventValue)
  have hRepresentative :
      (empiricalDensityDirectionalFlowExplicitL1Path
          successorIndex histories duration :
            ℝ → FiniteCoordinateL1Value
              (EmpiricalDensityDirectionalFlowCoordinate State))
        =ᵐ[finiteOpenIntervalVolume duration]
          empiricalDensityDirectionalFlowEventStepL1ValueAtTime
            successorIndex histories := by
    filter_upwards [hInitial, hEvents, hAdd] with time hInitialTime hEventsTime hAddTime
    rw [empiricalDensityDirectionalFlowEventStepL1ValueAtTime]
    change (((finiteIntervalConstantL1Path duration
      (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories) +
        finiteCoordinateVectorEventStepL1PathSum duration eventTime eventValue) :
          FiniteIntervalL1Path
            (EmpiricalDensityDirectionalFlowCoordinate State) duration) :
              ℝ → FiniteCoordinateL1Value
                (EmpiricalDensityDirectionalFlowCoordinate State)) time =
      empiricalDensityDirectionalFlowInitialL1Value successorIndex histories + _
    rw [hAddTime, Pi.add_apply, hInitialTime, hEventsTime]
    simp only [eventTime, eventValue, Fintype.sum_sigma]
    apply congrArg (empiricalDensityDirectionalFlowInitialL1Value
      successorIndex histories + ·)
    apply Finset.sum_congr rfl
    intro replica _hReplica
    apply Finset.sum_congr rfl
    intro index _hIndex
    exact scalarRightEventStep_smul_empiricalDensityDirectionalFlowEventIncrementL1Value
      successorIndex (histories replica) index time
  have hMemLp : MemLp
      (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories) 1 (finiteOpenIntervalVolume duration) :=
    (Lp.memLp (empiricalDensityDirectionalFlowExplicitL1Path
      successorIndex histories duration)).ae_eq hRepresentative
  exact (FiniteIntervalL1Path.represents_iff_eventuallyEq
    (empiricalDensityDirectionalFlowExplicitL1Path
      successorIndex histories duration)
    (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories) hMemLp).2 hRepresentative.symm

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On the ordered physical domain, the continuity-reconstructed tagged path is the native
empirical density--directional-flow observation. -/
theorem empiricalContinuityDensityDirectionalFlowL1ValueAtTime_eq_empirical
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration time : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalContinuityDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time =
      empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  cases coordinate with
  | inl state =>
      simpa only [empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        empiricalDensityDirectionalFlowL1ValueAtTime,
        ContinuousLinearEquiv.apply_symm_apply] using
        (empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime
          successorIndex histories duration time state hOrdered).symm
  | inr edge =>
      simp only [empiricalContinuityDensityDirectionalFlowL1ValueAtTime,
        empiricalDensityDirectionalFlowL1ValueAtTime,
        ContinuousLinearEquiv.apply_symm_apply]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal event-step path is the native empirical observation on ordered histories. -/
theorem empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration time : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories time =
      empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time :=
  (empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_continuity
    successorIndex histories time).trans
      (empiricalContinuityDensityDirectionalFlowL1ValueAtTime_eq_empirical
        successorIndex histories duration time hOrdered)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal event-step representative has bounded variation on every ordered physical
replica family. -/
theorem boundedVariationOn_empiricalDensityDirectionalFlowEventStepL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    BoundedVariationOn
      (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories) (Ioo 0 duration) := by
  have hPath :
      empiricalDensityDirectionalFlowEventStepL1ValueAtTime
          successorIndex histories =
        empiricalDensityDirectionalFlowL1ValueAtTime
          successorIndex histories := by
    funext time
    exact empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
      successorIndex histories duration time hOrdered
  rw [hPath]
  exact boundedVariationOn_empiricalDensityDirectionalFlowL1ValueAtTime
    successorIndex histories duration hOrdered

/-- Explicit scalar Stieltjes witness for one tagged coordinate of the empirical event-step
observation. -/
def empiricalDensityDirectionalFlowCoordinateDerivativeWitness
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    ScalarFiniteIntervalCadlagDerivativeWitness
      (fun time => empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories time coordinate) duration := by
  let eventPath
      (event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories) :=
    fun time => scalarRightEventStep
      ((histories event.1).jumpTimes event.2)
      (empiricalDensityDirectionalFlowEventIncrement
        successorIndex (histories event.1) event.2 coordinate) time
  let eventWitness := ScalarFiniteIntervalCadlagDerivativeWitness.fintypeSum
    eventPath fun event => scalarRightEventStepDerivativeWitness
      ((histories event.1).jumpTimes event.2)
      (empiricalDensityDirectionalFlowEventIncrement
        successorIndex (histories event.1) event.2 coordinate) duration
  let totalWitness :=
    (ScalarFiniteIntervalCadlagDerivativeWitness.constant
      (empiricalDensityDirectionalFlowInitialL1Value
        successorIndex histories coordinate) duration).add eventWitness
  have hPath :
      (fun time => empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories time coordinate) =
      (fun _time => empiricalDensityDirectionalFlowInitialL1Value
        successorIndex histories coordinate) +
        fun time => ∑ event : EmpiricalDensityDirectionalFlowEventIndex
            successorIndex histories, eventPath event time := by
    funext time
    rw [empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply]
    simp only [eventPath, Fintype.sum_sigma, Pi.add_apply]
  exact hPath.symm ▸ totalWitness

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The scalar witness retains the literal event-step representative pointwise, not merely in
the open-interval almost-everywhere class. -/
@[simp]
theorem empiricalDensityDirectionalFlowCoordinateDerivativeWitness_modification
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
      successorIndex histories duration coordinate).modification =
      fun time => empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories time coordinate := by
  funext time
  simp [empiricalDensityDirectionalFlowCoordinateDerivativeWitness,
    ScalarFiniteIntervalCadlagDerivativeWitness.constant,
    ScalarFiniteIntervalCadlagDerivativeWitness.add,
    ScalarFiniteIntervalCadlagDerivativeWitness.fintypeSum,
    scalarRightEventStepDerivativeWitness,
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply,
    Fintype.sum_sigma]

/-- Explicit graph-valued empirical observation on the ordered finite-rate carrier.  Its strong
`L1` coordinate and every Stieltjes derivative are supplied by finite event formulas. -/
def empiricalDensityDirectionalFlowExplicitHybridBVPath
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  FiniteIntervalHybridBVPath.ofScalarDerivativeWitnesses
    (empiricalDensityDirectionalFlowExplicitL1Path
      successorIndex histories duration)
    (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories)
    (empiricalDensityDirectionalFlowExplicitL1Path_represents
      successorIndex histories duration)
    (FiniteIntervalL1Path.hasBoundedVariation_of_represents
      (empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration)
      (empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories)
      (empiricalDensityDirectionalFlowExplicitL1Path_represents
        successorIndex histories duration)
      (boundedVariationOn_empiricalDensityDirectionalFlowEventStepL1ValueAtTime
        successorIndex histories duration hOrdered))
    (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
      successorIndex histories duration)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit graph observation retains the constructively summed strong-`L1` path. -/
@[simp]
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    (empiricalDensityDirectionalFlowExplicitHybridBVPath
      successorIndex histories duration hOrdered).toDerivativePath.toL1Path =
        empiricalDensityDirectionalFlowExplicitL1Path
          successorIndex histories duration := by
  simp [empiricalDensityDirectionalFlowExplicitHybridBVPath]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal event-step reconstruction is an explicit càdlàg representative of the hybrid
observation, including its separately represented boundary traces. -/
def empiricalDensityDirectionalFlowExplicitCadlagRepresentative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    FiniteIntervalCadlagRepresentative
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered).toDerivativePath.toL1Path where
  representative :=
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime successorIndex histories
  represents := by
    rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path]
    exact empiricalDensityDirectionalFlowExplicitL1Path_represents
      successorIndex histories duration
  rightContinuous := by
    intro time _hTime
    let coordinateEquivalence := PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
    apply coordinateEquivalence.symm.continuous.continuousAt.comp_continuousWithinAt
    exact continuousWithinAt_pi.mpr fun coordinate => by
      simpa only [coordinateEquivalence,
        empiricalDensityDirectionalFlowCoordinateDerivativeWitness_modification,
        PiLp.continuousLinearEquiv_apply, WithLp.equiv,
        empiricalDensityDirectionalFlowEventStepL1ValueAtTime,
        WithLp.ofLp_add] using
        (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
          successorIndex histories duration coordinate).rightContinuous time
  hasLeftLimit := by
    intro time _hTime
    choose coordinateTrace hCoordinateTrace using fun coordinate =>
      (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
        successorIndex histories duration coordinate).hasLeftLimit time
    let coordinateEquivalence := PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
    refine ⟨coordinateEquivalence.symm coordinateTrace, ?_⟩
    apply coordinateEquivalence.symm.continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr fun coordinate => by
      simpa only [coordinateEquivalence,
        empiricalDensityDirectionalFlowCoordinateDerivativeWitness_modification,
        PiLp.continuousLinearEquiv_apply, WithLp.equiv,
        empiricalDensityDirectionalFlowEventStepL1ValueAtTime,
        WithLp.ofLp_add] using hCoordinateTrace coordinate

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit hybrid observation's canonical initial trace is its literal empirical initial
density together with zero cumulative directional flow. -/
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_initialTrace
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    (empiricalDensityDirectionalFlowExplicitHybridBVPath
      successorIndex histories duration hOrdered).initialTrace =
        empiricalDensityDirectionalFlowInitialL1Value successorIndex histories := by
  rw [(empiricalDensityDirectionalFlowExplicitHybridBVPath
    successorIndex histories duration hOrdered).initialTrace_eq_of_cadlagRepresentative
      (empiricalDensityDirectionalFlowExplicitCadlagRepresentative
        successorIndex histories duration hOrdered) hDuration]
  change empiricalDensityDirectionalFlowEventStepL1ValueAtTime
      successorIndex histories 0 =
    empiricalDensityDirectionalFlowInitialL1Value successorIndex histories
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  rw [PiLp.continuousLinearEquiv_apply,
    empiricalDensityDirectionalFlowEventStepL1ValueAtTime_apply]
  have hEventZero (replica : Fin (successorIndex + 1))
      (index : Fin (histories replica).jumpCount) :
      scalarRightEventStep ((histories replica).jumpTimes index)
        (empiricalDensityDirectionalFlowEventIncrement
          successorIndex (histories replica) index coordinate) 0 = 0 := by
    simp [scalarRightEventStep,
      not_le.mpr ((hOrdered replica).1 index).1]
  simp_rw [hEventZero]
  simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every derivative coordinate of the explicit graph observation is the matching constructive
finite-event Stieltjes witness. -/
@[simp]
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (empiricalDensityDirectionalFlowExplicitHybridBVPath
      successorIndex histories duration hOrdered).toDerivativePath.derivative coordinate =
        (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
          successorIndex histories duration coordinate).derivative := by
  simp [empiricalDensityDirectionalFlowExplicitHybridBVPath]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Each constructive coordinate derivative is the finite sum of physically restricted weighted
Dirac atoms carried by the microscopic events. -/
theorem empiricalDensityDirectionalFlowCoordinateDerivativeWitness_derivative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (empiricalDensityDirectionalFlowCoordinateDerivativeWitness
      successorIndex histories duration coordinate).derivative =
        finiteRestrictedWeightedDiracVagueSignedMeasure duration
          (fun event : EmpiricalDensityDirectionalFlowEventIndex
              successorIndex histories =>
            (histories event.1).jumpTimes event.2)
          (fun event => empiricalDensityDirectionalFlowEventIncrement
            successorIndex (histories event.1) event.2 coordinate) := by
  classical
  simp only [empiricalDensityDirectionalFlowCoordinateDerivativeWitness,
    ScalarFiniteIntervalCadlagDerivativeWitness.derivative_transport]
  unfold ScalarFiniteIntervalCadlagDerivativeWitness.constant
    ScalarFiniteIntervalCadlagDerivativeWitness.add
    ScalarFiniteIntervalCadlagDerivativeWitness.fintypeSum
    scalarRightEventStepDerivativeWitness
    restrictedWeightedDiracVagueSignedMeasure
    finiteRestrictedWeightedDiracVagueSignedMeasure
  simp only [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure, zero_add]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit graph observation exposes the finite restricted-Dirac derivative formula on
every tagged coordinate. -/
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative_eq_finiteRestricted
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (empiricalDensityDirectionalFlowExplicitHybridBVPath
      successorIndex histories duration hOrdered).toDerivativePath.derivative coordinate =
        finiteRestrictedWeightedDiracVagueSignedMeasure duration
          (fun event : EmpiricalDensityDirectionalFlowEventIndex
              successorIndex histories =>
            (histories event.1).jumpTimes event.2)
          (fun event => empiricalDensityDirectionalFlowEventIncrement
            successorIndex (histories event.1) event.2 coordinate) := by
  rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative,
    empiricalDensityDirectionalFlowCoordinateDerivativeWitness_derivative]

end PositiveFiniteJumpHistoryReplicas

end


end FiniteMarkovProcesses.Probability
