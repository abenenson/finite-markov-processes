/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowEndpointConvention

/-!
# Hybrid-BV observation of finite jump histories

This module lifts the exact finite-replica empirical density and both ordered one-way flows into
the finite-interval hybrid bounded-variation carrier.  Density coordinates and ordered-flow
coordinates remain separately tagged; no current contraction is used.

## Main declarations

- `EmpiricalDensityDirectionalFlowCoordinate`: tagged density and ordered-flow coordinates;
- `PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime`: native finite
  `l1` observation value;
- `PositiveFiniteJumpHistoryReplicas.exists_empiricalDensityDirectionalFlowHybridBVPath`: exact
  lift into the hybrid BV derivative graph.
-/

open MeasureTheory Set
open FiniteMarkovProcesses.FiniteIntervalBVAlgebra
open scoped BigOperators ENNReal Topology

namespace FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

/-- Ordered off-diagonal edge of a finite state space. -/
abbrev FiniteStateOffDiagonalEdge (State : Type u) :=
  {edge : State × State // edge.1 ≠ edge.2}

/-- Tagged coordinates of the macroscopic empirical observation: density at one state or
cumulative one-way flow on one ordered off-diagonal state pair. -/
abbrev EmpiricalDensityDirectionalFlowCoordinate (State : Type u) :=
  Sum State (FiniteStateOffDiagonalEdge State)

/-- Pointwise physical support and boundary rules for a finite-state density and cumulative
ordered off-diagonal flow.  Absolute continuity is a separate finite-rate-domain condition. -/
structure FiniteStateDensityDirectionalFlowConstraints
    (density : ℝ → State → ℝ)
    (directionalFlow : ℝ → FiniteStateOffDiagonalEdge State → ℝ) : Prop where
  /-- Density coordinates are nonnegative. -/
  densityNonnegative : ∀ time state, 0 ≤ density time state
  /-- Density lies in the probability simplex at every time. -/
  densityNormalized : ∀ time, ∑ state, density time state = 1
  /-- Ordered one-way-flow coordinates are nonnegative. -/
  directionalFlowNonnegative : ∀ time edge, 0 ≤ directionalFlow time edge
  /-- Cumulative flow starts at zero. -/
  directionalFlowInitiallyZero : ∀ edge, directionalFlow 0 edge = 0
  /-- Exact microscopic continuity with divergence oriented incoming minus outgoing. -/
  continuityEquation : ∀ time state,
    density time state = density 0 state +
      ∑ source : {source : State // source ≠ state},
        directionalFlow time ⟨(source, state), source.property⟩ -
      ∑ target : {target : State // target ≠ state},
        directionalFlow time ⟨(state, target), target.property.symm⟩

namespace PositiveFiniteJumpHistoryReplicas

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A single history's cumulative ordered-transition count is monotone in observation time. -/
theorem monotone_directedTransitionCountAtTime
    (history : FiniteJumpHistory State) (source target : State) :
    Monotone fun time => history.directedTransitionCountAtTime time source target := by
  intro firstTime secondTime hTime
  unfold FiniteJumpHistory.directedTransitionCountAtTime
    FiniteJumpHistory.directedTransitionCountAtTimeVector
  apply Finset.sum_le_sum
  intro index _hIndex
  by_cases hFirst : history.jumpTimes index ≤ firstTime ∧
      history.states index.castSucc = source ∧ history.states index.succ = target
  · have hSecond : history.jumpTimes index ≤ secondTime ∧
        history.states index.castSucc = source ∧ history.states index.succ = target :=
      ⟨hFirst.1.trans hTime, hFirst.2⟩
    simp [hFirst, hSecond]
  · simp [hFirst]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The empirical cumulative ordered one-way flow is monotone in observation time. -/
theorem monotone_empiricalSpecificDirectionalFlowAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (source target : State) :
    Monotone fun time => empiricalSpecificDirectionalFlowAtTime
      successorIndex histories time source target := by
  intro firstTime secondTime hTime
  unfold empiricalSpecificDirectionalFlowAtTime
  apply div_le_div_of_nonneg_right
  · apply Finset.sum_le_sum
    intro replica _hReplica
    exact_mod_cast monotone_directedTransitionCountAtTime
      (histories replica) source target hTime
  · positivity

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A fixed history's cumulative ordered-transition count is measurable as a function of
observation time. -/
theorem measurable_directedTransitionCountAtTime_time
    (history : FiniteJumpHistory State) (source target : State) :
    Measurable fun time =>
      (history.directedTransitionCountAtTime time source target : ℝ) := by
  unfold FiniteJumpHistory.directedTransitionCountAtTime
    FiniteJumpHistory.directedTransitionCountAtTimeVector
  simp_rw [Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.measurable_sum
  intro index _hIndex
  have hEventTime : MeasurableSet {time : ℝ | history.jumpTimes index ≤ time} :=
    measurableSet_Ici
  by_cases hTransition : history.states index.castSucc = source ∧
      history.states index.succ = target
  · have hSummand : (fun time : ℝ =>
        if history.jumpTimes index ≤ time ∧
            history.states index.castSucc = source ∧
            history.states index.succ = target then (1 : ℝ) else 0) =
        fun time => if history.jumpTimes index ≤ time then 1 else 0 := by
      funext time
      simp [hTransition]
    rw [hSummand]
    exact Measurable.ite hEventTime measurable_const measurable_const
  · have hNever : ∀ time : ℝ, ¬(history.jumpTimes index ≤ time ∧
        history.states index.castSucc = source ∧ history.states index.succ = target) :=
      fun _ hEvent => hTransition hEvent.2
    simp only [hNever, ↓reduceIte]
    exact measurable_const

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical ordered one-way flow is measurable as a function of observation time. -/
theorem measurable_empiricalSpecificDirectionalFlowAtTime_time
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (source target : State) :
    Measurable fun time => empiricalSpecificDirectionalFlowAtTime
      successorIndex histories time source target := by
  unfold empiricalSpecificDirectionalFlowAtTime
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro replica _hReplica
  exact measurable_directedTransitionCountAtTime_time
    (histories replica) source target

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical density is measurable in physical time on an ordered physical family. -/
theorem measurable_empiricalDensityAtTime_time
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    Measurable fun time => empiricalDensityAtTime successorIndex histories time state := by
  have hContinuity : (fun time =>
      empiricalDensityAtTime successorIndex histories time state) =
      fun time => empiricalContinuityDensityAtTime
        successorIndex histories time state := by
    funext time
    exact empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime
      successorIndex histories duration time state hOrdered
  rw [hContinuity]
  unfold empiricalContinuityDensityAtTime
  apply Measurable.sub
  · apply Measurable.add measurable_const
    apply Finset.measurable_sum
    intro source _hSource
    exact measurable_empiricalSpecificDirectionalFlowAtTime_time
      successorIndex histories source state
  · apply Finset.measurable_sum
    intro target _hTarget
    exact measurable_empiricalSpecificDirectionalFlowAtTime_time
      successorIndex histories state target

/-- Native finite-`l1` value containing empirical density and every ordered one-way flow at one
physical time. -/
def empiricalDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      match coordinate with
      | Sum.inl state => empiricalDensityAtTime successorIndex histories time state
      | Sum.inr edge => empiricalSpecificDirectionalFlowAtTime
          successorIndex histories time edge.val.1 edge.val.2

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Coordinate recovery for empirical density. -/
@[simp]
theorem empiricalDensityDirectionalFlowL1ValueAtTime_density
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) :
    empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories time (Sum.inl state) =
        empiricalDensityAtTime successorIndex histories time state := by
  simp [empiricalDensityDirectionalFlowL1ValueAtTime]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Coordinate recovery for one ordered empirical flow. -/
@[simp]
theorem empiricalDensityDirectionalFlowL1ValueAtTime_flow
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) (hOffDiagonal : source ≠ target) :
    empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories time (Sum.inr ⟨(source, target), hOffDiagonal⟩) =
        empiricalSpecificDirectionalFlowAtTime
          successorIndex histories time source target := by
  simp [empiricalDensityDirectionalFlowL1ValueAtTime]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The native finite-`l1` empirical observation is strongly measurable in physical time. -/
theorem stronglyMeasurable_empiricalDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    StronglyMeasurable fun time =>
      empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time := by
  have hCoordinateMeasurable : Measurable
      (fun time : ℝ =>
        (fun coordinate : EmpiricalDensityDirectionalFlowCoordinate State =>
          match coordinate with
          | Sum.inl state => empiricalDensityAtTime successorIndex histories time state
          | Sum.inr edge => empiricalSpecificDirectionalFlowAtTime
              successorIndex histories time edge.val.1 edge.val.2) :
          ℝ → (EmpiricalDensityDirectionalFlowCoordinate State → ℝ)) := by
    apply Measurable.of_eval
    intro coordinate
    cases coordinate with
    | inl state =>
        exact measurable_empiricalDensityAtTime_time
          successorIndex histories duration state hOrdered
    | inr edge =>
        exact measurable_empiricalSpecificDirectionalFlowAtTime_time
          successorIndex histories edge.val.1 edge.val.2
  exact (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm.continuous
      |>.comp_stronglyMeasurable hCoordinateMeasurable.stronglyMeasurable

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Each ordered empirical flow coordinate has bounded variation on the open physical interval. -/
theorem boundedVariationOn_empiricalSpecificDirectionalFlowAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (source target : State) :
    BoundedVariationOn
      (fun time => empiricalSpecificDirectionalFlowAtTime
        successorIndex histories time source target)
      (Ioo 0 duration) :=
  boundedVariationOn_Ioo_of_monotone
    (monotone_empiricalSpecificDirectionalFlowAtTime
      successorIndex histories source target) 0 duration

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Each empirical density coordinate has bounded variation because the microscopic continuity
identity expresses it as initial density plus finite sums of incoming and outgoing ordered flows. -/
theorem boundedVariationOn_empiricalDensityAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    BoundedVariationOn
      (fun time => empiricalDensityAtTime successorIndex histories time state)
      (Ioo 0 duration) := by
  have hIdentity : (fun time =>
      empiricalDensityAtTime successorIndex histories time state) =
      fun time => empiricalContinuityDensityAtTime
        successorIndex histories time state := by
    funext time
    exact empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime
      successorIndex histories duration time state hOrdered
  rw [hIdentity]
  unfold empiricalContinuityDensityAtTime
  apply boundedVariationOn_sub
  · apply boundedVariationOn_add
    · exact boundedVariationOn_const
        (empiricalInitialDensity successorIndex histories state) (Ioo 0 duration)
    · exact boundedVariationOn_finite_sum
        (fun source time => empiricalSpecificDirectionalFlowAtTime
          successorIndex histories time source state) (Ioo 0 duration)
        (fun source => boundedVariationOn_empiricalSpecificDirectionalFlowAtTime
          successorIndex histories duration source state)
  · exact boundedVariationOn_finite_sum
      (fun target time => empiricalSpecificDirectionalFlowAtTime
        successorIndex histories time state target) (Ioo 0 duration)
      (fun target => boundedVariationOn_empiricalSpecificDirectionalFlowAtTime
        successorIndex histories duration state target)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete tagged density/ordered-flow empirical path has bounded variation in the native
finite `l1` norm. -/
theorem boundedVariationOn_empiricalDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    BoundedVariationOn
      (empiricalDensityDirectionalFlowL1ValueAtTime successorIndex histories)
      (Ioo 0 duration) := by
  apply boundedVariationOn_finiteCoordinateL1Value_of_coordinate
  intro coordinate
  cases coordinate with
  | inl state =>
      simpa only [empiricalDensityDirectionalFlowL1ValueAtTime_density] using
        boundedVariationOn_empiricalDensityAtTime
          successorIndex histories duration state hOrdered
  | inr edge =>
      rcases edge with ⟨⟨source, target⟩, hOffDiagonal⟩
      simpa only [empiricalDensityDirectionalFlowL1ValueAtTime_flow] using
        boundedVariationOn_empiricalSpecificDirectionalFlowAtTime
          successorIndex histories duration source target

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Empirical density is nonnegative at every physical time and state. -/
theorem empiricalDensityAtTime_nonnegative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (state : State) :
    0 ≤ empiricalDensityAtTime successorIndex histories time state := by
  unfold empiricalDensityAtTime
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro replica _hReplica
    unfold FiniteJumpHistory.stateMembershipIndicator
    split <;> positivity
  · positivity

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every ordered empirical one-way-flow coordinate is nonnegative. -/
theorem empiricalSpecificDirectionalFlowAtTime_nonnegative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (source target : State) :
    0 ≤ empiricalSpecificDirectionalFlowAtTime
      successorIndex histories time source target := by
  unfold empiricalSpecificDirectionalFlowAtTime
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro replica _hReplica
    exact Nat.cast_nonneg
      ((histories replica).directedTransitionCountAtTime time source target)
  · exact add_nonneg (Nat.cast_nonneg successorIndex) zero_le_one

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On histories ordered strictly after time zero, every empirical ordered flow starts at zero. -/
theorem empiricalSpecificDirectionalFlowAtTime_zero
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (source target : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalSpecificDirectionalFlowAtTime
      successorIndex histories 0 source target = 0 := by
  unfold empiricalSpecificDirectionalFlowAtTime
  have hReplica (replica : Fin (successorIndex + 1)) :
      (histories replica).directedTransitionCountAtTime 0 source target = 0 := by
    unfold FiniteJumpHistory.directedTransitionCountAtTime
      FiniteJumpHistory.directedTransitionCountAtTimeVector
    apply Finset.sum_eq_zero
    intro index _hIndex
    have hPositive : 0 < (histories replica).jumpTimes index :=
      (hOrdered replica).1 index |>.1
    simp [not_le_of_gt hPositive]
  simp only [hReplica, Nat.cast_zero, Finset.sum_const_zero, zero_div]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Microscopic continuity written on the exact off-diagonal ordered-flow carrier.  Diagonal
self-transition counts cancel before the subtype restriction and are not macroscopic coordinates. -/
theorem empiricalDensityAtTime_eq_initial_add_offDiagonalIncoming_sub_outgoing
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration time : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalDensityAtTime successorIndex histories time state =
      empiricalInitialDensity successorIndex histories state +
        ∑ source : {source : State // source ≠ state},
          empiricalSpecificDirectionalFlowAtTime
            successorIndex histories time source state -
        ∑ target : {target : State // target ≠ state},
          empiricalSpecificDirectionalFlowAtTime
            successorIndex histories time state target := by
  rw [empiricalDensityAtTime_eq_empiricalContinuityDensityAtTime
    successorIndex histories duration time state hOrdered]
  unfold empiricalContinuityDensityAtTime
  rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
    Fintype.sum_eq_add_sum_subtype_ne _ state]
  ring

/-- Empirical cumulative flow restricted to the exact ordered off-diagonal carrier. -/
def empiricalOffDiagonalDirectionalFlowAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (time : ℝ) (edge : FiniteStateOffDiagonalEdge State) : ℝ :=
  empiricalSpecificDirectionalFlowAtTime
    successorIndex histories time edge.val.1 edge.val.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Before the first strictly positive event, empirical density equals the initial empirical
density. -/
theorem empiricalDensityAtTime_zero_eq_empiricalInitialDensity
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (state : State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalDensityAtTime successorIndex histories 0 state =
      empiricalInitialDensity successorIndex histories state := by
  have hContinuity :=
    empiricalDensityAtTime_eq_initial_add_offDiagonalIncoming_sub_outgoing
      successorIndex histories duration 0 state hOrdered
  simp only [empiricalSpecificDirectionalFlowAtTime_zero
    successorIndex histories duration _ _ hOrdered,
    Finset.sum_const_zero, add_zero, sub_zero] at hContinuity
  exact hContinuity

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every ordered finite empirical observation satisfies the exact simplex, off-diagonal support,
initial-flow boundary, and microscopic continuity constraints. -/
theorem empiricalDensityDirectionalFlow_constraints
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    FiniteStateDensityDirectionalFlowConstraints
      (empiricalDensityAtTime successorIndex histories)
      (empiricalOffDiagonalDirectionalFlowAtTime successorIndex histories) := by
  refine
    { densityNonnegative := empiricalDensityAtTime_nonnegative successorIndex histories
      densityNormalized := sum_empiricalDensityAtTime successorIndex histories
      directionalFlowNonnegative := ?_
      directionalFlowInitiallyZero := ?_
      continuityEquation := ?_ }
  · intro time edge
    exact empiricalSpecificDirectionalFlowAtTime_nonnegative
      successorIndex histories time edge.val.1 edge.val.2
  · intro edge
    exact empiricalSpecificDirectionalFlowAtTime_zero
      successorIndex histories duration edge.val.1 edge.val.2 hOrdered
  · intro time state
    rw [empiricalDensityAtTime_zero_eq_empiricalInitialDensity
      successorIndex histories duration state hOrdered]
    exact empiricalDensityAtTime_eq_initial_add_offDiagonalIncoming_sub_outgoing
      successorIndex histories duration time state hOrdered

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete empirical path belongs to `L1` on every positive physical interval. -/
theorem memLp_empiricalDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    MemLp (empiricalDensityDirectionalFlowL1ValueAtTime successorIndex histories)
      1 (finiteOpenIntervalVolume duration) := by
  have : IsFiniteMeasure (finiteOpenIntervalVolume duration) := by
    dsimp only [finiteOpenIntervalVolume]
    infer_instance
  let path := empiricalDensityDirectionalFlowL1ValueAtTime successorIndex histories
  let base : FiniteCoordinateL1Value
      (EmpiricalDensityDirectionalFlowCoordinate State) := path (duration / 2)
  let variation := eVariationOn path (Ioo 0 duration)
  have hVariation : variation ≠ ∞ :=
    boundedVariationOn_empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories duration hOrdered
  have hNormBound : ∀ time ∈ Ioo 0 duration,
      ‖path time‖ ≤ ‖base‖ + variation.toReal := by
    intro time hTime
    have hBaseTime : duration / 2 ∈ Ioo (0 : ℝ) duration := by
      constructor <;> linarith
    have hPathVariation : BoundedVariationOn path (Ioo 0 duration) := hVariation
    exact norm_le_norm_add_const_of_dist_le
      (hPathVariation.dist_le hTime hBaseTime)
  apply MemLp.of_bound (C := ‖base‖ + variation.toReal)
  · exact (stronglyMeasurable_empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories duration hOrdered).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    exact hNormBound time hTime

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Exact lift of every ordered positive finite replica family into the hybrid BV derivative
graph.  The path quotient is literally built from the tagged empirical density and both ordered
flows. -/
theorem exists_empiricalDensityDirectionalFlowHybridBVPath
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    ∃ hybridPath : FiniteIntervalHybridBVPath
        (EmpiricalDensityDirectionalFlowCoordinate State) duration,
      hybridPath.toDerivativePath.toL1Path =
        FiniteIntervalL1Path.ofFunction
          (empiricalDensityDirectionalFlowL1ValueAtTime successorIndex histories)
          (memLp_empiricalDensityDirectionalFlowL1ValueAtTime
            successorIndex histories duration hDuration hOrdered) := by
  let empiricalPath :=
    empiricalDensityDirectionalFlowL1ValueAtTime successorIndex histories
  let hMemLp := memLp_empiricalDensityDirectionalFlowL1ValueAtTime
    successorIndex histories duration hDuration hOrdered
  let quotientPath := FiniteIntervalL1Path.ofFunction empiricalPath hMemLp
  have hRepresents : FiniteIntervalL1Path.Represents quotientPath empiricalPath :=
    ⟨hMemLp, rfl⟩
  have hQuotientVariation : FiniteIntervalL1Path.HasBoundedVariation quotientPath :=
    FiniteIntervalL1Path.hasBoundedVariation_of_represents quotientPath empiricalPath
      hRepresents
      (boundedVariationOn_empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories duration hOrdered)
  simpa only [quotientPath, empiricalPath, hMemLp] using
    FiniteIntervalHybridBVPath.exists_with_toL1Path_eq
      quotientPath hDuration hQuotientVariation

end PositiveFiniteJumpHistoryReplicas

end

end FiniteMarkovProcesses.Probability
