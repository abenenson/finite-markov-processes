/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservationMeasurability
import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalDensityL1Concentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Strong-L1 concentration of empirical density--directional-flow paths

This module constructs the exact mean density--cumulative-flow path as a genuine
strong-`L1` quotient and lifts the coordinatewise integrated replica deviations to the existing
total hybrid-BV observation.

No time discretization, history-count truncation, or replacement carrier is introduced.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Exact heterogeneous source mean of the normalized empirical density and cumulative ordered
flow at one physical time. -/
noncomputable def finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      match coordinate with
      | Sum.inl state =>
          (∑ replica,
            finiteStateTimeDependentMarkovMeanDensityAt
              (PMF.pure (initialConfiguration replica)) rates duration time state) /
            (successorIndex + 1 : ℝ)
      | Sum.inr edge =>
          (∑ replica,
            finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
              (PMF.pure (initialConfiguration replica)) rates duration time
                edge.val.1 edge.val.2) /
            (successorIndex + 1 : ℝ)

omit [MeasurableSingletonClass State] in
/-- Density-coordinate formula for the heterogeneous source mean path. -/
@[simp]
theorem finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration time (Sum.inl state) =
      (∑ replica,
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure (initialConfiguration replica)) rates duration time state) /
        (successorIndex + 1 : ℝ) := by
  simp [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime]

omit [MeasurableSingletonClass State] in
/-- Directional-flow-coordinate formula for the heterogeneous source mean path. -/
@[simp]
theorem finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (edge : FiniteStateOffDiagonalEdge State) :
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration time (Sum.inr edge) =
      (∑ replica,
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          (PMF.pure (initialConfiguration replica)) rates duration time
            edge.val.1 edge.val.2) /
        (successorIndex + 1 : ℝ) := by
  simp [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime]

omit [MeasurableSingletonClass State] in
/-- The pointwise `l1` distance from the empirical path to its exact heterogeneous mean is the
sum of the normalized microscopic count deviations.  This is the algebraic bridge from the
coordinate concentration estimates to the topology of the genuine strong-`L1` carrier. -/
theorem norm_empiricalDensityDirectionalFlowL1ValueAtTime_sub_mean_eq
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) (time : ℝ) :
    ‖PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime
        successorIndex histories time -
        finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
          successorIndex initialConfiguration rates duration time‖ =
      (∑ state,
          finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
            initialConfiguration rates duration state histories time) /
          (successorIndex + 1 : ℝ) +
        (∑ edge : FiniteStateOffDiagonalEdge State,
          finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration edge.val.1 edge.val.2 histories time) /
          (successorIndex + 1 : ℝ) := by
  rw [PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro state _hState
    rw [PiLp.sub_apply,
      PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime_density,
      finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density,
      Real.norm_eq_abs]
    unfold PositiveFiniteJumpHistoryReplicas.empiricalDensityAtTime
      finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
      finiteJumpHistoryStateMembershipAtTime
    rw [← sub_div, abs_div, abs_of_pos (by positivity :
        (0 : ℝ) < successorIndex + 1)]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro edge _hEdge
    rw [PiLp.sub_apply]
    change
      ‖PositiveFiniteJumpHistoryReplicas.empiricalSpecificDirectionalFlowAtTime
          successorIndex histories time
          edge.val.1 edge.val.2 -
        (∑ replica,
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            (PMF.pure (initialConfiguration replica)) rates duration time
              edge.val.1 edge.val.2) /
          (successorIndex + 1 : ℝ)‖ = _
    rw [Real.norm_eq_abs]
    unfold PositiveFiniteJumpHistoryReplicas.empiricalSpecificDirectionalFlowAtTime
      finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
    rw [← sub_div, abs_div, abs_of_pos (by positivity :
      (0 : ℝ) < successorIndex + 1)]

/-- Strong-`l1` deviation of the empirical density--directional-flow value from its exact source
mean at one physical time. -/
noncomputable def finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) (time : ℝ) : ℝ :=
  ‖PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories time -
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration time‖

/-- The strong-`l1` hybrid deviation is jointly integrable under the exact replica law and
physical-time volume. -/
theorem integrable_finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime_uncurry
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    Integrable
      (fun data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ ↦
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration data.1 data.2)
      ((finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates duration).toMeasure.prod
        (finiteOpenIntervalVolume (duration : ℝ))) := by
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  have hState (state : State) : Integrable
      (fun data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ ↦
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration state data.1 data.2)
      (law.prod physicalTime) :=
    integrable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
      initialConfiguration rates duration state
  have hFlow (edge : FiniteStateOffDiagonalEdge State) : Integrable
      (fun data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ ↦
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration edge.val.1 edge.val.2 data.1 data.2)
      (law.prod physicalTime) :=
    integrable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
      initialConfiguration rates duration edge.val.1 edge.val.2
  have hStateSum := integrable_finsetSum Finset.univ fun state _hState ↦ hState state
  have hFlowSum := integrable_finsetSum Finset.univ fun edge _hEdge ↦ hFlow edge
  have hRight := (hStateSum.div_const (successorIndex + 1 : ℝ)).add
    (hFlowSum.div_const (successorIndex + 1 : ℝ))
  apply hRight.congr
  filter_upwards [] with data
  simpa only [finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime,
    Pi.add_apply] using
    (norm_empiricalDensityDirectionalFlowL1ValueAtTime_sub_mean_eq
      successorIndex initialConfiguration rates duration data.1 data.2).symm

/-- Explicit finite-particle expected strong-`L1` deviation bound.  Its density and one-way-flow
terms retain their distinct cardinalities and the latter's common-clock moment constant. -/
noncomputable def finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
    (successorIndex : ℕ) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) : ℝ :=
  (duration : ℝ) *
    ((Fintype.card State : ℝ) * Real.sqrt (successorIndex + 1 : ℝ) +
      (Fintype.card (FiniteStateOffDiagonalEdge State) : ℝ) *
        Real.sqrt
          ((successorIndex + 1 : ℝ) *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1))))) /
    (successorIndex + 1 : ℝ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit expectation bound is a fixed coefficient divided by the square root of the
positive replica count. -/
theorem finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound_eq_div_sqrt
    (successorIndex : ℕ) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
        (State := State) successorIndex rates duration =
      ((duration : ℝ) *
        ((Fintype.card State : ℝ) +
          (Fintype.card (FiniteStateOffDiagonalEdge State) : ℝ) *
            Real.sqrt
              (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp 1 - 1))))) /
        Real.sqrt (successorIndex + 1 : ℝ) := by
  unfold finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ successorIndex + 1)]
  have hSquare :
      Real.sqrt (successorIndex + 1 : ℝ) *
          Real.sqrt (successorIndex + 1 : ℝ) =
        (successorIndex + 1 : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hSquarePow :
      Real.sqrt (successorIndex + 1 : ℝ) ^ 2 =
        (successorIndex + 1 : ℝ) := by
    simpa only [pow_two] using hSquare
  field_simp [show (successorIndex + 1 : ℝ) ≠ 0 by positivity,
    show Real.sqrt (successorIndex + 1 : ℝ) ≠ 0 by positivity]
  rw [hSquarePow]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- At fixed source rates and horizon, the exact expectation bound vanishes as the particle
count diverges. -/
theorem tendsto_finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound_zero
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    Tendsto
      (fun successorIndex ↦
        finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
          (State := State) successorIndex rates duration)
      atTop (𝓝 0) := by
  have hReplicaCount : Tendsto (fun successorIndex : ℕ ↦
      (successorIndex + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hSqrt : Tendsto (fun successorIndex : ℕ ↦
      Real.sqrt (successorIndex + 1 : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp hReplicaCount
  simpa only [
    finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound_eq_div_sqrt]
    using tendsto_const_nhds.div_atTop hSqrt

/-- The exact expected strong-`L1` hybrid-path deviation has the explicit square-root replica
bound.  The estimate is on the actual untruncated history carrier and physical-time interval. -/
theorem integral_integral_finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime_le
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration histories time
          ∂finiteOpenIntervalVolume (duration : ℝ) ∂law) ≤
      finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
        (State := State) successorIndex rates duration := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  let stateDeviation (state : State)
      (data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ) :=
    finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
      initialConfiguration rates duration state data.1 data.2
  let flowDeviation (edge : FiniteStateOffDiagonalEdge State)
      (data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ) :=
    finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
      initialConfiguration rates duration edge.val.1 edge.val.2 data.1 data.2
  have hHybrid :=
    integrable_finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime_uncurry
      successorIndex initialConfiguration rates duration
  have hState (state : State) : Integrable (stateDeviation state) (law.prod physicalTime) :=
    integrable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
      initialConfiguration rates duration state
  have hFlow (edge : FiniteStateOffDiagonalEdge State) :
      Integrable (flowDeviation edge) (law.prod physicalTime) :=
    integrable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
      initialConfiguration rates duration edge.val.1 edge.val.2
  have hStateSum : Integrable (fun data ↦ ∑ state, stateDeviation state data)
      (law.prod physicalTime) :=
    integrable_finsetSum Finset.univ fun state _hState ↦ hState state
  have hFlowSum : Integrable (fun data ↦ ∑ edge, flowDeviation edge data)
      (law.prod physicalTime) :=
    integrable_finsetSum Finset.univ fun edge _hEdge ↦ hFlow edge
  have hPointwise (data : PositiveFiniteJumpHistoryReplicas State successorIndex × ℝ) :
      finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration data.1 data.2 =
        (∑ state, stateDeviation state data) / (successorIndex + 1 : ℝ) +
          (∑ edge, flowDeviation edge data) / (successorIndex + 1 : ℝ) := by
    exact norm_empiricalDensityDirectionalFlowL1ValueAtTime_sub_mean_eq
      successorIndex initialConfiguration rates duration data.1 data.2
  calc
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration histories time
          ∂physicalTime ∂law) =
        ∫ data,
          finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
            successorIndex initialConfiguration rates duration data.1 data.2
          ∂law.prod physicalTime := integral_integral hHybrid
    _ = ∫ data,
        (∑ state, stateDeviation state data) / (successorIndex + 1 : ℝ) +
          (∑ edge, flowDeviation edge data) / (successorIndex + 1 : ℝ)
        ∂law.prod physicalTime := integral_congr_ae
          (Filter.Eventually.of_forall hPointwise)
    _ = (∑ state, ∫ data, stateDeviation state data ∂law.prod physicalTime) /
          (successorIndex + 1 : ℝ) +
        (∑ edge, ∫ data, flowDeviation edge data ∂law.prod physicalTime) /
          (successorIndex + 1 : ℝ) := by
      rw [integral_add (hStateSum.div_const _) (hFlowSum.div_const _),
        integral_div, integral_div,
        integral_finsetSum Finset.univ (fun state _hState ↦ hState state),
        integral_finsetSum Finset.univ (fun edge _hEdge ↦ hFlow edge)]
    _ ≤ ((∑ _state : State,
          (duration : ℝ) * Real.sqrt (successorIndex + 1 : ℝ)) /
          (successorIndex + 1 : ℝ)) +
        ((∑ _edge : FiniteStateOffDiagonalEdge State,
          (duration : ℝ) *
            Real.sqrt
              ((successorIndex + 1 : ℝ) *
                (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                  (Real.exp 1 - 1))))) /
          (successorIndex + 1 : ℝ)) := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro state _hState
        rw [integral_prod (stateDeviation state) (hState state)]
        simpa only [stateDeviation, law, physicalTime, Nat.cast_add, Nat.cast_one] using
          integral_integral_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le
            initialConfiguration rates duration state
      · apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro edge _hEdge
        rw [integral_prod (flowDeviation edge) (hFlow edge)]
        simpa only [flowDeviation, law, physicalTime, Nat.cast_add, Nat.cast_one] using
          integral_integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le
            initialConfiguration rates duration edge.val.1 edge.val.2
    _ = finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
        (State := State) successorIndex rates duration := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
      ring

/-- The exact heterogeneous source mean path is strongly measurable on physical time. -/
theorem stronglyMeasurable_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    StronglyMeasurable
      (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration) := by
  apply Measurable.stronglyMeasurable
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm.continuous.measurable.comp
  rw [measurable_pi_iff]
  intro coordinate
  cases coordinate with
  | inl state =>
      exact (Finset.measurable_sum Finset.univ fun replica _hReplica ↦
        measurable_finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure (initialConfiguration replica)) rates duration state).div_const _
  | inr edge =>
      exact (Finset.measurable_sum Finset.univ fun replica _hReplica ↦
        measurable_finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          (PMF.pure (initialConfiguration replica)) rates duration
            edge.val.1 edge.val.2).div_const _

/-- Average expected complete physical jump count of the heterogeneous replica family. -/
noncomputable def finiteStateTimeDependentMarkovMeanReplicaJumpCount
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) : ℝ :=
  (∑ replica, ∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ)
    ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure (initialConfiguration replica)) rates duration) /
    (successorIndex + 1 : ℝ)

omit [MeasurableSingletonClass State] in
/-- The heterogeneous mean replica jump count is nonnegative. -/
theorem finiteStateTimeDependentMarkovMeanReplicaJumpCount_nonneg
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    0 ≤ finiteStateTimeDependentMarkovMeanReplicaJumpCount
      successorIndex initialConfiguration rates duration := by
  unfold finiteStateTimeDependentMarkovMeanReplicaJumpCount
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro replica _hReplica
    exact integral_nonneg fun history ↦ Nat.cast_nonneg history.jumpCount
  · positivity

/-- Every density coordinate of the heterogeneous source mean lies in the unit interval. -/
theorem finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density_mem_Icc
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration time (Sum.inl state) ∈
      Set.Icc (0 : ℝ) 1 := by
  rw [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun replica _hReplica ↦
      (finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
        (PMF.pure (initialConfiguration replica)) rates duration time state).1) (by positivity)
  · rw [div_le_one (by positivity)]
    calc
      (∑ replica,
          finiteStateTimeDependentMarkovMeanDensityAt
            (PMF.pure (initialConfiguration replica)) rates duration time state) ≤
          ∑ _replica : Fin (successorIndex + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro replica _hReplica
        exact (finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
          (PMF.pure (initialConfiguration replica)) rates duration time state).2
      _ = (successorIndex + 1 : ℝ) := by simp

/-- Every cumulative-flow coordinate of the heterogeneous source mean is nonnegative and bounded
by the average expected complete physical jump count. -/
theorem finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow_mem_Icc
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (edge : FiniteStateOffDiagonalEdge State) :
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration time (Sum.inr edge) ∈
      Set.Icc 0
        (finiteStateTimeDependentMarkovMeanReplicaJumpCount
          successorIndex initialConfiguration rates duration) := by
  rw [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow]
  unfold finiteStateTimeDependentMarkovMeanReplicaJumpCount
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun replica _hReplica ↦
      (finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_mem_Icc_jumpCountMean
        (PMF.pure (initialConfiguration replica)) rates duration time
          edge.val.1 edge.val.2).1) (by positivity)
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun replica _hReplica ↦
        (finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_mem_Icc_jumpCountMean
          (PMF.pure (initialConfiguration replica)) rates duration time
            edge.val.1 edge.val.2).2)
      (by positivity)

/-- The exact heterogeneous source mean belongs to the genuine strong-`L1` path carrier. -/
theorem memLp_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    MemLp
      (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration)
      1 (finiteOpenIntervalVolume (duration : ℝ)) := by
  have hMeanStronglyMeasurable :=
    stronglyMeasurable_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration
  apply MemLp.of_eval_piLp
  intro coordinate
  cases coordinate with
  | inl state =>
      have hCoordinateStronglyMeasurable : StronglyMeasurable fun time : ℝ ↦
          finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
            successorIndex initialConfiguration rates duration time (Sum.inl state) :=
        (PiLp.proj (𝕜 := ℝ) (p := 1)
          (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
          (Sum.inl state)).continuous.comp_stronglyMeasurable
            hMeanStronglyMeasurable
      apply MemLp.of_bound
        hCoordinateStronglyMeasurable.aestronglyMeasurable
        1
      filter_upwards [] with time
      rw [Real.norm_eq_abs, abs_of_nonneg
        (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density_mem_Icc
          successorIndex initialConfiguration rates duration time state).1]
      exact
        (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density_mem_Icc
          successorIndex initialConfiguration rates duration time state).2
  | inr edge =>
      have hCoordinateStronglyMeasurable : StronglyMeasurable fun time : ℝ ↦
          finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
            successorIndex initialConfiguration rates duration time (Sum.inr edge) :=
        (PiLp.proj (𝕜 := ℝ) (p := 1)
          (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
          (Sum.inr edge)).continuous.comp_stronglyMeasurable
            hMeanStronglyMeasurable
      apply MemLp.of_bound
        hCoordinateStronglyMeasurable.aestronglyMeasurable
        (finiteStateTimeDependentMarkovMeanReplicaJumpCount
          successorIndex initialConfiguration rates duration)
      filter_upwards [] with time
      rw [Real.norm_eq_abs, abs_of_nonneg
        (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow_mem_Icc
          successorIndex initialConfiguration rates duration time edge).1]
      exact
        (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow_mem_Icc
          successorIndex initialConfiguration rates duration time edge).2

/-- Exact mean path in the genuine strong-`L1` quotient. -/
noncomputable def finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    FiniteIntervalL1Path
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ) :=
  FiniteIntervalL1Path.ofFunction
    (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration)
    (memLp_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration)

/-- The raw exact mean is a representative of the strong-`L1` path. -/
theorem finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path_represents
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    FiniteIntervalL1Path.Represents
      (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
        successorIndex initialConfiguration rates duration)
      (finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
        successorIndex initialConfiguration rates duration) := by
  exact
    ⟨memLp_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration, rfl⟩

/-- On the ordered physical carrier, the strong-`L1` distance from the explicit empirical path
to the exact source mean is the physical-time integral of the pointwise `l1` distance. -/
theorem norm_empiricalDensityDirectionalFlowExplicitL1Path_sub_mean_eq_integral
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore (duration : ℝ)) :
    ‖PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowExplicitL1Path
          successorIndex histories (duration : ℝ) -
        finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
          successorIndex initialConfiguration rates duration‖ =
      ∫ time,
        ‖PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime
            successorIndex histories time -
          finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
            successorIndex initialConfiguration rates duration time‖
        ∂finiteOpenIntervalVolume (duration : ℝ) := by
  let actual :=
    PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories
  let mean := finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
    successorIndex initialConfiguration rates duration
  have hActual : MemLp actual 1 (finiteOpenIntervalVolume (duration : ℝ)) :=
    PositiveFiniteJumpHistoryReplicas.memLp_empiricalDensityDirectionalFlowL1ValueAtTime
      successorIndex histories duration hDuration hOrdered
  have hMean : MemLp mean 1 (finiteOpenIntervalVolume (duration : ℝ)) :=
    memLp_finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime
      successorIndex initialConfiguration rates duration
  rcases
      PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowExplicitL1Path_represents
        successorIndex histories duration with ⟨hEventStep, hEventStepQuotient⟩
  have hActualQuotient :
      hActual.toLp actual =
        PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowExplicitL1Path
          successorIndex histories duration := by
    calc
      hActual.toLp actual = hEventStep.toLp
          (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowEventStepL1ValueAtTime
            successorIndex histories) := by
        apply hActual.toLp_congr hEventStep
        filter_upwards [] with time
        exact
          (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
            successorIndex histories duration time hOrdered).symm
      _ = _ := hEventStepQuotient
  change
    ‖PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowExplicitL1Path
          successorIndex histories duration -
        hMean.toLp mean‖ = ∫ time, ‖actual time - mean time‖
          ∂finiteOpenIntervalVolume (duration : ℝ)
  rw [← hActualQuotient, ← hActual.toLp_sub hMean, Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm (hActual.sub hMean).aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm (hActual.sub hMean).aestronglyMeasurable]
  simp only [Pi.sub_apply]

section TotalObservation

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Strong-`L1` distance between the measurable total hybrid observation and the exact source
mean path.  The totalization differs from the physical path only on the unordered null set. -/
noncomputable def finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) : ℝ :=
  ‖(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath.toL1Path -
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
      successorIndex initialConfiguration rates duration‖

/-- The total strong-`L1` path deviation is Borel measurable on the complete history carrier. -/
theorem measurable_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal) :
    Measurable
      (finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
        successorIndex initialConfiguration rates duration) := by
  unfold finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
  exact (continuous_norm.comp
    (FiniteIntervalHybridBVPath.continuous_toL1Path.sub continuous_const)).measurable.comp
      (PositiveFiniteJumpHistoryReplicas.measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration)

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On ordered physical histories, the total path deviation is exactly the physical-time
integral of the microscopic hybrid deviation. -/
theorem finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_eq_integral_of_ordered
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore (duration : ℝ)) :
    finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
        successorIndex initialConfiguration rates duration histories =
      ∫ time,
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration histories time
        ∂finiteOpenIntervalVolume (duration : ℝ) := by
  unfold finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
  rw
    [PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
      successorIndex duration histories hOrdered]
  simp only
    [PositiveFiniteJumpHistoryReplicas.orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation,
    PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path]
  simpa only [finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime] using!
    norm_empiricalDensityDirectionalFlowExplicitL1Path_sub_mean_eq_integral
      successorIndex initialConfiguration rates duration histories hDuration hOrdered

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The measurable total hybrid observation inherits the explicit expected strong-`L1` bound;
the fallback contributes nothing because unordered histories have zero source probability. -/
theorem integral_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_le
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories,
        finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
          successorIndex initialConfiguration rates duration histories ∂law) ≤
      finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
        (State := State) successorIndex rates duration := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  calc
    (∫ histories,
        finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
          successorIndex initialConfiguration rates duration histories ∂law) =
      ∫ histories, ∫ time,
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration histories time
          ∂finiteOpenIntervalVolume (duration : ℝ) ∂law := by
        apply integral_congr_ae
        filter_upwards [
          ae_orderedBefore_finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration rates duration] with histories hOrdered
        exact
          finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_eq_integral_of_ordered
            successorIndex initialConfiguration rates duration histories hDuration hOrdered
    _ ≤ _ :=
      integral_integral_finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime_le
        successorIndex initialConfiguration rates duration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The total strong-`L1` path deviation is integrable under the exact replica law. -/
theorem integrable_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration) :
    Integrable
      (finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
        successorIndex initialConfiguration rates duration)
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure := by
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  have hJoint :=
    integrable_finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime_uncurry
      successorIndex initialConfiguration rates duration
  have hIntegrated : Integrable
      (fun histories ↦ ∫ time,
        finiteStateTimeDependentMarkovEmpiricalHybridL1DeviationAtTime
          successorIndex initialConfiguration rates duration histories time
        ∂finiteOpenIntervalVolume (duration : ℝ)) law := hJoint.integral_prod_left
  apply hIntegrated.congr
  filter_upwards [
    ae_orderedBefore_finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration] with histories hOrdered
  exact
    (finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_eq_integral_of_ordered
      successorIndex initialConfiguration rates duration histories hDuration hOrdered).symm

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Finite-particle Markov concentration in the genuine strong-`L1` topology.  The left side is
the exact real probability of leaving the closed radius-`deviation` ball, multiplied by its
radius; the right side is the explicit `O(N⁻¹ᐟ²)` expectation bound. -/
theorem deviation_mul_measureReal_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_ge_le
    (successorIndex : ℕ) (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration) (deviation : ℝ) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    deviation * law.real
        {histories |
          deviation ≤ finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
            successorIndex initialConfiguration rates duration histories} ≤
      finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound
        (State := State) successorIndex rates duration := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  calc
    deviation * law.real
        {histories |
          deviation ≤ finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
            successorIndex initialConfiguration rates duration histories} ≤
      ∫ histories,
        finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
          successorIndex initialConfiguration rates duration histories ∂law :=
        mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall fun histories ↦ by
            exact norm_nonneg _)
          (integrable_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
            successorIndex initialConfiguration rates duration hDuration)
          deviation
    _ ≤ _ :=
      integral_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_le
        successorIndex initialConfiguration rates duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- For any fixed positive radius, the exact probability of leaving the strong-`L1` ball around
the mean path converges to zero as the particle count diverges. -/
theorem tendsto_measureReal_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_ge_zero
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (hDuration : 0 < duration) (deviation : ℝ) (hDeviation : 0 < deviation) :
    Tendsto
      (fun successorIndex ↦
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real
          {histories |
            deviation ≤ finiteStateTimeDependentMarkovTotalHybridL1PathDeviation
              successorIndex (initialConfiguration successorIndex) rates duration histories})
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro successorIndex
    exact measureReal_nonneg
  · intro successorIndex
    apply (le_div_iff₀ hDeviation).2
    simpa only [mul_comm] using
      deviation_mul_measureReal_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_ge_le
        successorIndex (initialConfiguration successorIndex) rates duration
          hDuration deviation
  · have hBound :=
      tendsto_finiteStateTimeDependentMarkovEmpiricalHybridL1ExpectedDeviationBound_zero
        (State := State) rates duration
    simpa only [zero_div] using hBound.div_const deviation

end TotalObservation

end

end FiniteMarkovProcesses.Probability
