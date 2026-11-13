/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDirectionalFlowExpectation
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalHybridL1Concentration
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanHybridBVPath
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureWithDensityPairing

/-!
# Hybrid-topology concentration of empirical Markov jump paths

This module identifies the derivative tests in the exact strong-`L1` plus open-interval vague
hybrid topology with the bounded weighted jump sums controlled by the finite-replica source.
It then assembles those finite-coordinate controls with strong-`L1` concentration.

No metric is imposed on the complete derivative-test family.  Arbitrary neighborhoods enter only
through their finite-cylinder reduction.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction CompactlySupported ENNReal NNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- One finite common bound for a family of compactly supported continuous real tests. -/
noncomputable def finiteCompactlySupportedContinuousRealTestFamilyBound
    {TestIndex : Type*} [Fintype TestIndex] (test : TestIndex → C_c(ℝ, ℝ)) : ℝ :=
  ∑ index,
    ‖ofCompactSupport (test index) (test index).continuous
      (test index).hasCompactSupport‖

/-- The finite common test-family bound is nonnegative. -/
theorem finiteCompactlySupportedContinuousRealTestFamilyBound_nonnegative
    {TestIndex : Type*} [Fintype TestIndex] (test : TestIndex → C_c(ℝ, ℝ)) :
    0 ≤ finiteCompactlySupportedContinuousRealTestFamilyBound test :=
  Finset.sum_nonneg fun _index _hIndex => norm_nonneg _

/-- Every member of a finite compact-test family is pointwise bounded by the common family
bound. -/
theorem abs_compactlySupportedContinuousRealTest_le_familyBound
    {TestIndex : Type*} [Fintype TestIndex] (test : TestIndex → C_c(ℝ, ℝ))
    (index : TestIndex) (time : ℝ) :
    |test index time| ≤ finiteCompactlySupportedContinuousRealTestFamilyBound test := by
  let boundedTest : ℝ →ᵇ ℝ :=
    ofCompactSupport (test index) (test index).continuous (test index).hasCompactSupport
  calc
    |test index time| = ‖boundedTest time‖ := by
      rfl
    _ ≤ ‖boundedTest‖ := boundedTest.norm_coe_le_norm time
    _ ≤ _ := by
      unfold finiteCompactlySupportedContinuousRealTestFamilyBound
      exact Finset.single_le_sum
        (fun otherIndex _hOtherIndex => norm_nonneg
          (ofCompactSupport (test otherIndex) (test otherIndex).continuous
            (test otherIndex).hasCompactSupport))
        (Finset.mem_univ index)

namespace PositiveFiniteJumpHistoryReplicas

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
private theorem sum_ne_state_indicator_eq_one
    (value state : State) (hNe : value ≠ state) :
    (∑ other : {other : State // other ≠ state},
      if value = other then (1 : ℝ) else 0) = 1 := by
  classical
  let matching : {other : State // other ≠ state} := ⟨value, hNe⟩
  rw [Finset.sum_eq_single matching]
  · simp [matching]
  · intro other _hOther hOther
    have hValueNe : value ≠ (other : State) := by
      intro hValue
      apply hOther
      apply Subtype.ext
      simpa only [matching] using hValue.symm
    simp [hValueNe]
  · simp

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A directional-flow derivative test of the empirical hybrid path is exactly the normalized
sum of the corresponding weighted microscopic ordered jumps. -/
theorem empiricalDensityDirectionalFlowFullDerivative_flow_continuousTestIntegral_eq
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (edge : FiniteStateOffDiagonalEdge State)
    (test : C_c(ℝ, ℝ)) :
    (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
      (Sum.inr edge)).continuousTestIntegral test =
      (∑ replica,
        finiteJumpHistoryDirectedTransitionWeightSum
          test edge.val.1 edge.val.2 (histories replica)) /
        (successorIndex + 1 : ℝ) := by
  classical
  rw [empiricalDensityDirectionalFlowFullDerivative_eq_finiteWeighted,
    finiteWeightedDiracVagueSignedMeasure_continuousTestIntegral]
  rw [Fintype.sum_sigma, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro replica _hReplica
  unfold finiteJumpHistoryDirectedTransitionWeightSum
    finiteJumpHistoryTransitionTestSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro eventIndex _hEventIndex
  simp only [empiricalDensityDirectionalFlowEventIncrement,
    finiteStateDirectedTransitionWeightTest]
  by_cases hEdge :
      (histories replica).states eventIndex.castSucc = edge.val.1 ∧
        (histories replica).states eventIndex.succ = edge.val.2
  · simp [hEdge]
    ring
  · simp [hEdge]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- One microscopic event satisfies the tagged density/ordered-flow continuity equation before
any summation over histories or tests. -/
theorem empiricalDensityDirectionalFlowEventIncrement_density_eq_flow_balance
    (successorIndex : ℕ) (history : FiniteJumpHistory State)
    (eventIndex : Fin history.jumpCount) (state : State) :
    empiricalDensityDirectionalFlowEventIncrement
        successorIndex history eventIndex (Sum.inl state) =
      (∑ source : {source : State // source ≠ state},
          empiricalDensityDirectionalFlowEventIncrement successorIndex history eventIndex
            (Sum.inr ⟨(source, state), source.property⟩)) -
        ∑ target : {target : State // target ≠ state},
          empiricalDensityDirectionalFlowEventIncrement successorIndex history eventIndex
            (Sum.inr ⟨(state, target), target.property.symm⟩) := by
  classical
  unfold empiricalDensityDirectionalFlowEventIncrement
  simp only [FiniteJumpHistory.stateMembershipIndicator]
  by_cases hTarget : history.states eventIndex.succ = state
  · by_cases hSource : history.states eventIndex.castSucc = state
    · simp [hTarget, hSource]
    · simp only [hTarget, hSource, ↓reduceIte, and_true, false_and, sub_zero, one_div]
      rw [← Finset.sum_div, sum_ne_state_indicator_eq_one _ _ hSource]
      simp
  · by_cases hSource : history.states eventIndex.castSucc = state
    · simp only [hTarget, hSource, ↓reduceIte, true_and, and_false, zero_sub]
      simp only [Finset.sum_const_zero, zero_div]
      rw [← Finset.sum_div, sum_ne_state_indicator_eq_one _ _ hTarget]
      ring
    · simp [hTarget, hSource]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A density-derivative test is the incoming weighted-flow sum minus the outgoing weighted-flow
sum.  This is the microscopic continuity equation at the exact finite-replica level. -/
theorem empiricalDensityDirectionalFlowFullDerivative_density_continuousTestIntegral_eq
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) (test : C_c(ℝ, ℝ)) :
    (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
      (Sum.inl state)).continuousTestIntegral test =
      (∑ source : {source : State // source ≠ state},
          (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
            (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test) -
        ∑ target : {target : State // target ≠ state},
          (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
            (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test := by
  classical
  rw [empiricalDensityDirectionalFlowFullDerivative_eq_finiteWeighted,
    finiteWeightedDiracVagueSignedMeasure_continuousTestIntegral]
  simp_rw [empiricalDensityDirectionalFlowFullDerivative_eq_finiteWeighted,
    finiteWeightedDiracVagueSignedMeasure_continuousTestIntegral]
  calc
    (∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
        empiricalDensityDirectionalFlowEventIncrement successorIndex
            (histories event.1) event.2 (Sum.inl state) *
          test ((histories event.1).jumpTimes event.2)) =
        ∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
          ((∑ source : {source : State // source ≠ state},
              empiricalDensityDirectionalFlowEventIncrement successorIndex
                (histories event.1) event.2
                (Sum.inr ⟨(source, state), source.property⟩)) -
            ∑ target : {target : State // target ≠ state},
              empiricalDensityDirectionalFlowEventIncrement successorIndex
                (histories event.1) event.2
                (Sum.inr ⟨(state, target), target.property.symm⟩)) *
            test ((histories event.1).jumpTimes event.2) := by
      apply Finset.sum_congr rfl
      intro event _hEvent
      rw [empiricalDensityDirectionalFlowEventIncrement_density_eq_flow_balance]
    _ = (∑ source : {source : State // source ≠ state},
          ∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
            empiricalDensityDirectionalFlowEventIncrement successorIndex
                (histories event.1) event.2
                (Sum.inr ⟨(source, state), source.property⟩) *
              test ((histories event.1).jumpTimes event.2)) -
        ∑ target : {target : State // target ≠ state},
          ∑ event : EmpiricalDensityDirectionalFlowEventIndex successorIndex histories,
            empiricalDensityDirectionalFlowEventIncrement successorIndex
                (histories event.1) event.2
                (Sum.inr ⟨(state, target), target.property.symm⟩) *
              test ((histories event.1).jumpTimes event.2) := by
      simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      congr 1 <;> rw [Finset.sum_comm]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The error of one empirical density-derivative test against any continuity-compatible center
is bounded by the sum of the incoming and outgoing ordered-flow test errors. -/
theorem abs_empiricalDensityDerivativeTest_sub_flowBalance_le
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) (test : C_c(ℝ, ℝ))
    (flowCenter : FiniteStateOffDiagonalEdge State → ℝ) :
    |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
          (Sum.inl state)).continuousTestIntegral test -
        ((∑ source : {source : State // source ≠ state},
            flowCenter ⟨(source, state), source.property⟩) -
          ∑ target : {target : State // target ≠ state},
            flowCenter ⟨(state, target), target.property.symm⟩)| ≤
      (∑ source : {source : State // source ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test -
            flowCenter ⟨(source, state), source.property⟩|) +
        ∑ target : {target : State // target ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test -
            flowCenter ⟨(state, target), target.property.symm⟩| := by
  classical
  rw [empiricalDensityDirectionalFlowFullDerivative_density_continuousTestIntegral_eq]
  calc
    |((∑ source : {source : State // source ≠ state},
          (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
            (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test) -
        ∑ target : {target : State // target ≠ state},
          (empiricalDensityDirectionalFlowFullDerivative successorIndex histories
            (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test) -
        ((∑ source : {source : State // source ≠ state},
            flowCenter ⟨(source, state), source.property⟩) -
          ∑ target : {target : State // target ≠ state},
            flowCenter ⟨(state, target), target.property.symm⟩)| =
      |(∑ source : {source : State // source ≠ state},
          ((empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test -
            flowCenter ⟨(source, state), source.property⟩)) -
        ∑ target : {target : State // target ≠ state},
          ((empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test -
            flowCenter ⟨(state, target), target.property.symm⟩)| := by
        congr 1
        simp only [Finset.sum_sub_distrib]
        ring
    _ ≤ |∑ source : {source : State // source ≠ state},
          ((empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test -
            flowCenter ⟨(source, state), source.property⟩)| +
        |∑ target : {target : State // target ≠ state},
          ((empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test -
            flowCenter ⟨(state, target), target.property.symm⟩)| := abs_sub _ _
    _ ≤ _ := add_le_add (Finset.abs_sum_le_sum_abs _ _)
      (Finset.abs_sum_le_sum_abs _ _)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Uniform control of every ordered-flow test controls the corresponding density-derivative
test with an explicit finite-state slack. -/
theorem abs_empiricalDensityDerivativeTest_sub_flowBalance_lt_of_flow_lt
    [Nonempty State]
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (state : State) (test : C_c(ℝ, ℝ))
    (flowCenter : FiniteStateOffDiagonalEdge State → ℝ)
    {tolerance : ℝ} (hTolerance : 0 < tolerance)
    (hFlow : ∀ edge : FiniteStateOffDiagonalEdge State,
      |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
          (Sum.inr edge)).continuousTestIntegral test - flowCenter edge| <
        tolerance / (4 * Fintype.card State : ℝ)) :
    |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
          (Sum.inl state)).continuousTestIntegral test -
        ((∑ source : {source : State // source ≠ state},
            flowCenter ⟨(source, state), source.property⟩) -
          ∑ target : {target : State // target ≠ state},
            flowCenter ⟨(state, target), target.property.symm⟩)| < tolerance := by
  classical
  let flowTolerance := tolerance / (4 * Fintype.card State : ℝ)
  have hCardPositive : (0 : ℝ) < Fintype.card State := by
    exact_mod_cast Fintype.card_pos
  have hFlowToleranceNonnegative : 0 ≤ flowTolerance := by
    dsimp only [flowTolerance]
    positivity
  have hSubtypeCardLe (fixed : State) :
      Fintype.card {other : State // other ≠ fixed} ≤ Fintype.card State :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hIncoming :
      (∑ source : {source : State // source ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test -
            flowCenter ⟨(source, state), source.property⟩|) ≤
        (Fintype.card State : ℝ) * flowTolerance := by
    calc
      _ ≤ ∑ _source : {source : State // source ≠ state}, flowTolerance := by
        apply Finset.sum_le_sum
        intro source _hSource
        exact (hFlow ⟨(source, state), source.property⟩).le
      _ = (Fintype.card {source : State // source ≠ state} : ℝ) *
          flowTolerance := by simp
      _ ≤ (Fintype.card State : ℝ) * flowTolerance := by
        gcongr
        exact_mod_cast hSubtypeCardLe state
  have hOutgoing :
      (∑ target : {target : State // target ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test -
            flowCenter ⟨(state, target), target.property.symm⟩|) ≤
        (Fintype.card State : ℝ) * flowTolerance := by
    calc
      _ ≤ ∑ _target : {target : State // target ≠ state}, flowTolerance := by
        apply Finset.sum_le_sum
        intro target _hTarget
        exact (hFlow ⟨(state, target), target.property.symm⟩).le
      _ = (Fintype.card {target : State // target ≠ state} : ℝ) *
          flowTolerance := by simp
      _ ≤ (Fintype.card State : ℝ) * flowTolerance := by
        gcongr
        exact_mod_cast hSubtypeCardLe state
  calc
    _ ≤ (∑ source : {source : State // source ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test -
            flowCenter ⟨(source, state), source.property⟩|) +
        ∑ target : {target : State // target ≠ state},
          |(empiricalDensityDirectionalFlowFullDerivative successorIndex histories
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test -
            flowCenter ⟨(state, target), target.property.symm⟩| :=
      abs_empiricalDensityDerivativeTest_sub_flowBalance_le
        successorIndex histories state test flowCenter
    _ ≤ 2 * (Fintype.card State : ℝ) * flowTolerance := by linarith
    _ = tolerance / 2 := by
      dsimp only [flowTolerance]
      field_simp
      ring
    _ < tolerance := by linarith

end PositiveFiniteJumpHistoryReplicas

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The directional-flow derivative test of the mean hybrid path is exactly the
occupation--rate mean used by the microscopic compensator. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (edge : FiniteStateOffDiagonalEdge State)
    (test : C_c(ℝ, ℝ)) :
    ((finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
        |>.derivative (Sum.inr edge)).continuousTestIntegral test =
      finiteStateTimeDependentMarkovDirectedTransitionWeightMean
        initial rates duration test edge.val.1 edge.val.2 := by
  have hEndpointMeasurable : Measurable fun markedTime : ℝ ↦
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime edge.val.1 := by
    unfold finiteStateTimeDependentMarkovEndpointProbability
    have hSurvival : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) := by
      fun_prop
    exact hSurvival.mul
      (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates edge.val.1)
  have hRateMeasurable : Measurable fun markedTime : ℝ ↦
      (rates.rate markedTime edge.val.1 edge.val.2 : ℝ) :=
    NNReal.continuous_coe.measurable.comp
      (rates.measurable_rate edge.val.1 edge.val.2)
  have hDensityMeasurable : Measurable fun markedTime : ℝ ↦
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime edge.val.1).toReal *
        (rates.rate markedTime edge.val.1 edge.val.2 : ℝ) :=
    hEndpointMeasurable.ennreal_toReal.mul hRateMeasurable
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_derivative]
  rw [VagueSignedMeasure.continuousTestIntegral_withDensity
    (finiteOpenIntervalVolume (duration : ℝ))
    (fun markedTime : ℝ ↦
      finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates markedTime (Sum.inr edge))]
  · unfold finiteStateTimeDependentMarkovDirectedTransitionWeightMean
      finiteOpenIntervalVolume
    simp only [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue]
    apply integral_congr_ae
    filter_upwards [] with markedTime
    ring
  · simpa only [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue] using
      hDensityMeasurable
  · exact integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
      initial rates duration (Sum.inr edge)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The pointwise mean continuity equation lifts exactly to every open-interval continuous
derivative test. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_density_continuousTestIntegral_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (state : State) (test : C_c(ℝ, ℝ)) :
    (FiniteIntervalL1DerivativePath.derivative
      (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
        (Sum.inl state)).continuousTestIntegral test =
      (∑ source : {source : State // source ≠ state},
          (FiniteIntervalL1DerivativePath.derivative
            (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test) -
        ∑ target : {target : State // target ≠ state},
          (FiniteIntervalL1DerivativePath.derivative
            (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test := by
  have hFlowMeasurable (edge : FiniteStateOffDiagonalEdge State) :
      Measurable fun markedTime : ℝ ↦
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
          initial rates markedTime (Sum.inr edge) := by
    have hEndpointMeasurable : Measurable fun markedTime : ℝ ↦
        finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime edge.val.1 := by
      unfold finiteStateTimeDependentMarkovEndpointProbability
      have hSurvival : Measurable fun markedTime : ℝ ↦
          ENNReal.ofReal
            (Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) := by
        fun_prop
      exact hSurvival.mul
        (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
          initial rates edge.val.1)
    exact hEndpointMeasurable.ennreal_toReal.mul <|
      NNReal.continuous_coe.measurable.comp
        (rates.measurable_rate edge.val.1 edge.val.2)
  have hDensityMeasurable : Measurable fun markedTime : ℝ ↦
      finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates markedTime (Sum.inl state) := by
    rw [show (fun markedTime : ℝ ↦
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
          initial rates markedTime (Sum.inl state)) =
      fun markedTime =>
        (∑ source : {source : State // source ≠ state},
            finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue initial rates markedTime
              (Sum.inr ⟨(source, state), source.property⟩)) -
          ∑ target : {target : State // target ≠ state},
            finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue initial rates markedTime
              (Sum.inr ⟨(state, target), target.property.symm⟩) by
      funext markedTime
      exact finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue_density_eq_flowBalance
        initial rates markedTime state]
    exact
      (Finset.measurable_sum Finset.univ
        fun (source : {source : State // source ≠ state}) _hSource =>
          hFlowMeasurable ⟨(source, state), source.property⟩).sub
        (Finset.measurable_sum Finset.univ
          fun (target : {target : State // target ≠ state}) _hTarget =>
          hFlowMeasurable ⟨(state, target), target.property.symm⟩)
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_derivative]
  rw [VagueSignedMeasure.continuousTestIntegral_withDensity
    (finiteOpenIntervalVolume (duration : ℝ))
    (fun markedTime : ℝ ↦
      finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates markedTime (Sum.inl state))
    hDensityMeasurable
    (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
      initial rates duration (Sum.inl state))]
  simp_rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]
  unfold finiteStateTimeDependentMarkovDirectedTransitionWeightMean
  rw [← integral_finsetSum, ← integral_finsetSum, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards [] with markedTime
    rw [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue_density_eq_flowBalance]
    simp only [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
      Finset.mul_sum, mul_sub, mul_assoc]
  · exact integrable_finsetSum Finset.univ fun source _hSource =>
      by simpa only [finiteOpenIntervalVolume,
          finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue, mul_assoc] using
        integrable_compactlySupportedContinuousMap_mul_of_integrable_right test
          (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
            initial rates duration
              (Sum.inr ⟨(source, state), source.property⟩))
  · exact integrable_finsetSum Finset.univ fun target _hTarget =>
      by simpa only [finiteOpenIntervalVolume,
          finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue, mul_assoc] using
        integrable_compactlySupportedContinuousMap_mul_of_integrable_right test
          (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
            initial rates duration
              (Sum.inr ⟨(state, target), target.property.symm⟩))
  · intro target _hTarget
    simpa only [finiteOpenIntervalVolume,
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue, mul_assoc] using
      integrable_compactlySupportedContinuousMap_mul_of_integrable_right test
        (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
          initial rates duration
            (Sum.inr ⟨(state, target), target.property.symm⟩))
  · intro source _hSource
    simpa only [finiteOpenIntervalVolume,
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue, mul_assoc] using
      integrable_compactlySupportedContinuousMap_mul_of_integrable_right test
        (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
          initial rates duration
            (Sum.inr ⟨(source, state), source.property⟩))

/-- Exact heterogeneous replica center on the ambient hybrid carrier.  Its strong-`L1` component
is the previously constructed heterogeneous mean path, while every derivative is the normalized
finite sum of the corresponding pure-initial source derivatives. -/
noncomputable def finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0) :
    FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ) where
  toL1Path := finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
    successorIndex initialConfiguration rates duration
  derivative coordinate := VagueSignedMeasure.realScalarMultiple
    ((successorIndex + 1 : ℝ)⁻¹) <| VagueSignedMeasure.ofSignedMeasure <|
      ∑ replica,
        ((finiteStateTimeDependentMarkovMeanHybridBVPath
          (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath
            |>.derivative coordinate).toSignedMeasure

/-- The heterogeneous center's strong-`L1` component is definitionally the exact source mean
used by strong-`L1` concentration. -/
@[simp]
theorem finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_toL1Path
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0) :
    (finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
      successorIndex initialConfiguration rates duration).toL1Path =
        finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
          successorIndex initialConfiguration rates duration := rfl

/-- Every directional-flow test of the heterogeneous ambient center is exactly the average of
the pure-initial occupation--rate means appearing in the microscopic concentration theorem. -/
theorem
finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (edge : FiniteStateOffDiagonalEdge State) (test : C_c(ℝ, ℝ)) :
    ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex initialConfiguration rates duration).derivative
          (Sum.inr edge)).continuousTestIntegral test =
      (∑ replica,
        finiteStateTimeDependentMarkovDirectedTransitionWeightMean
          (PMF.pure (initialConfiguration replica)) rates duration
          test edge.val.1 edge.val.2) / (successorIndex + 1 : ℝ) := by
  unfold finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
  rw [VagueSignedMeasure.continuousTestIntegral_realScalarMultiple]
  rw [show
      (VagueSignedMeasure.ofSignedMeasure
        (∑ replica,
          ((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath
              |>.derivative (Sum.inr edge)).toSignedMeasure)).continuousTestIntegral test =
        ∑ replica,
          ((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath
              |>.derivative (Sum.inr edge)).continuousTestIntegral test by
    simpa only using VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
      (fun replica =>
        (finiteStateTimeDependentMarkovMeanHybridBVPath
          (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath.derivative
            (Sum.inr edge)) test]
  simp_rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]
  rw [div_eq_mul_inv, mul_comm]

/-- The exact heterogeneous center preserves the density/ordered-flow continuity equation against
every derivative test. -/
theorem
finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_density_continuousTestIntegral_eq
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (state : State) (test : C_c(ℝ, ℝ)) :
    ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex initialConfiguration rates duration).derivative
          (Sum.inl state)).continuousTestIntegral test =
      (∑ source : {source : State // source ≠ state},
          ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
            successorIndex initialConfiguration rates duration).derivative
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test) -
        ∑ target : {target : State // target ≠ state},
          ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
            successorIndex initialConfiguration rates duration).derivative
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral test := by
  simp_rw
    [finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq]
  unfold finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
  rw [VagueSignedMeasure.continuousTestIntegral_realScalarMultiple]
  rw [show
      (VagueSignedMeasure.ofSignedMeasure
        (∑ replica,
          ((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath
              |>.derivative (Sum.inl state)).toSignedMeasure)).continuousTestIntegral test =
        ∑ replica,
          ((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath
              |>.derivative (Sum.inl state)).continuousTestIntegral test by
    simpa only using VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
      (fun replica =>
        (finiteStateTimeDependentMarkovMeanHybridBVPath
          (PMF.pure (initialConfiguration replica)) rates duration).toDerivativePath.derivative
            (Sum.inl state)) test]
  simp_rw [finiteStateTimeDependentMarkovMeanHybridBVPath_density_continuousTestIntegral_eq]
  simp_rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  rw [mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]

/-- One empirical directional-flow derivative test concentrates around the exact heterogeneous
source mean.  The displayed threshold is normalized per particle while the right side retains
the finite-product variance estimate at its native summed scale. -/
theorem finiteStateTimeDependentMarkovDeterministicReplica_flowDerivativeTestDeviation_le
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (edge : FiniteStateOffDiagonalEdge State)
    (test : C_c(ℝ, ℝ)) {tolerance : ℝ} (hTolerance : 0 < tolerance) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories |
        tolerance ≤
          |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
              successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
            (∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                test edge.val.1 edge.val.2) / (successorIndex + 1 : ℝ)|} ≤
      ENNReal.ofReal
        (((successorIndex + 1 : ℕ) : ℝ) *
          (‖ofCompactSupport
              test test.continuous test.hasCompactSupport‖ ^ 2 *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1)))) /
          (((successorIndex + 1 : ℕ) : ℝ) * tolerance) ^ 2) := by
  dsimp only
  let boundedTest : ℝ →ᵇ ℝ :=
    ofCompactSupport test test.continuous test.hasCompactSupport
  have hParticleCount : (0 : ℝ) < successorIndex + 1 := by positivity
  have hDeviation : 0 < (successorIndex + 1 : ℝ) * tolerance :=
    mul_pos hParticleCount hTolerance
  have hTestBound (time : ℝ) : |test time| ≤ ‖boundedTest‖ := by
    simpa only [boundedTest, Real.norm_eq_abs] using! boundedTest.norm_coe_le_norm time
  have hConcentration :=
    finiteStateTimeDependentMarkovDeterministicReplica_directedFlowTestDeviation_le
      initialConfiguration rates duration edge.property test test.continuous.measurable
      (norm_nonneg boundedTest) hTestBound hDeviation
  have hEvent :
      {histories |
        tolerance ≤
          |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
              successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
            (∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                test edge.val.1 edge.val.2) / (successorIndex + 1 : ℝ)|} =
        {histories |
          (successorIndex + 1 : ℝ) * tolerance ≤
            |∑ replica,
                finiteJumpHistoryDirectedTransitionWeightSum
                  test edge.val.1 edge.val.2 (histories replica) -
              ∑ replica,
                finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                  (PMF.pure (initialConfiguration replica)) rates duration
                  test edge.val.1 edge.val.2|} := by
    ext histories
    simp only [Set.mem_ofPred_eq,
      PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative_flow_continuousTestIntegral_eq]
    rw [← sub_div, abs_div, abs_of_pos hParticleCount]
    simpa only [mul_comm] using (le_div_iff₀ hParticleCount)
  rw [hEvent]
  simpa only [boundedTest, Nat.cast_add, Nat.cast_one] using hConcentration

/-- A finite family of empirical directional-flow derivative tests concentrates jointly around
its exact heterogeneous source means.  This is the finite-cylinder estimate used by the hybrid
open-neighborhood lower route. -/
theorem
finiteStateTimeDependentMarkovDeterministicReplica_finiteFlowDerivativeTestFamilyDeviation_le
    {TestIndex : Type*} [Fintype TestIndex]
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (edge : TestIndex → FiniteStateOffDiagonalEdge State)
    (test : TestIndex → C_c(ℝ, ℝ))
    {tolerance : ℝ} (hTolerance : 0 < tolerance) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories | ∃ index,
        tolerance ≤
          |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
              successorIndex histories (Sum.inr (edge index))).continuousTestIntegral
                (test index) -
            (∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                (test index) (edge index).val.1 (edge index).val.2) /
              (successorIndex + 1 : ℝ)|} ≤
      (Fintype.card TestIndex : ℝ≥0∞) *
        ENNReal.ofReal
          (((successorIndex + 1 : ℕ) : ℝ) *
            (finiteCompactlySupportedContinuousRealTestFamilyBound test ^ 2 *
              (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp 1 - 1)))) /
            (((successorIndex + 1 : ℕ) : ℝ) * tolerance) ^ 2) := by
  dsimp only
  have hParticleCount : (0 : ℝ) < successorIndex + 1 := by positivity
  have hDeviation : 0 < (successorIndex + 1 : ℝ) * tolerance :=
    mul_pos hParticleCount hTolerance
  have hConcentration :=
    finiteStateTimeDependentMarkovDeterministicReplica_finiteFlowTestFamilyDeviation_le
      initialConfiguration rates duration
      (fun index => (edge index).val.1) (fun index => (edge index).val.2)
      (fun index => (edge index).property) (fun index time => test index time)
      (fun index => (test index).continuous.measurable)
      (finiteCompactlySupportedContinuousRealTestFamilyBound_nonnegative test)
      (abs_compactlySupportedContinuousRealTest_le_familyBound test)
      hDeviation
  have hEvent :
      {histories | ∃ index,
        tolerance ≤
          |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
              successorIndex histories (Sum.inr (edge index))).continuousTestIntegral
                (test index) -
            (∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                (test index) (edge index).val.1 (edge index).val.2) /
              (successorIndex + 1 : ℝ)|} =
        {histories | ∃ index,
          (successorIndex + 1 : ℝ) * tolerance ≤
            |∑ replica,
                finiteJumpHistoryDirectedTransitionWeightSum
                  (test index) (edge index).val.1 (edge index).val.2
                    (histories replica) -
              ∑ replica,
                finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                  (PMF.pure (initialConfiguration replica)) rates duration
                  (test index) (edge index).val.1 (edge index).val.2|} := by
    ext histories
    simp only [Set.mem_ofPred_eq]
    apply exists_congr
    intro index
    rw
      [PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative_flow_continuousTestIntegral_eq,
      ← sub_div, abs_div, abs_of_pos hParticleCount]
    simpa only [mul_comm] using (le_div_iff₀ hParticleCount)
  rw [hEvent]
  simpa only [Nat.cast_add, Nat.cast_one] using hConcentration

universe v w

/-- Strong-`L1` concentration and concentration of every fixed derivative test imply
concentration in every open neighborhood of a convergent hybrid center.  The sample carrier and
law may vary with the particle index; only finite-cylinder failure probabilities enter. -/
theorem tendsto_measureReal_hybridObservation_not_mem_open_zero
    {Coordinate : Type v} [Fintype Coordinate] {duration : ℝ}
    (Sample : ℕ → Type w) [∀ index, MeasurableSpace (Sample index)]
    (law : ∀ index, Measure (Sample index)) [∀ index, IsFiniteMeasure (law index)]
    (observation : ∀ index,
      Sample index → FiniteIntervalL1DerivativePath Coordinate duration)
    (center : ℕ → FiniteIntervalL1DerivativePath Coordinate duration)
    (target : FiniteIntervalL1DerivativePath Coordinate duration)
    (hCenter : Tendsto center atTop (𝓝 target))
    (hL1 : ∀ tolerance : ℝ, 0 < tolerance →
      Tendsto (fun index => (law index).real
        {sample | tolerance ≤
          ‖(observation index sample).toL1Path - (center index).toL1Path‖})
        atTop (𝓝 0))
    (hDerivative : ∀ coordinate
        (test : FiniteOpenIntervalVanishingContinuousTest duration)
        (tolerance : ℝ), 0 < tolerance →
      Tendsto (fun index => (law index).real
        {sample | tolerance ≤
          |((observation index sample).derivative coordinate).continuousTestIntegral test.1 -
            ((center index).derivative coordinate).continuousTestIntegral test.1|})
        atTop (𝓝 0))
    {openSet : Set (FiniteIntervalL1DerivativePath Coordinate duration)}
    (hOpen : IsOpen openSet) (hTarget : target ∈ openSet) :
    Tendsto (fun index => (law index).real
      {sample | observation index sample ∉ openSet}) atTop (𝓝 0) := by
  classical
  obtain ⟨l1Tolerance, hL1Tolerance, selectedTests, derivativeTolerance,
      hDerivativeTolerance, hCylinderSubset⟩ :=
    FiniteIntervalL1DerivativePath.exists_finiteDerivativeTestCylinder_subset_of_mem_nhds
      target (hOpen.mem_nhds hTarget)
  let SelectedTest := {selectedTest // selectedTest ∈ selectedTests}
  have hHalfL1 : 0 < l1Tolerance / 2 := half_pos hL1Tolerance
  have hHalfDerivative (selectedTest : SelectedTest) :
      0 < derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2 :=
    half_pos (hDerivativeTolerance selectedTest.1 selectedTest.2)
  have hCenterL1 : Tendsto
      (fun index => ‖(center index).toL1Path - target.toL1Path‖)
      atTop (𝓝 0) := by
    have hContinuous : Continuous fun path :
        FiniteIntervalL1DerivativePath Coordinate duration =>
          ‖path.toL1Path - target.toL1Path‖ :=
      continuous_norm.comp
        (FiniteIntervalL1DerivativePath.continuous_toL1Path.sub continuous_const)
    simpa [Function.comp_def] using hContinuous.continuousAt.tendsto.comp hCenter
  have hCenterL1Eventually : ∀ᶠ index in atTop,
      ‖(center index).toL1Path - target.toL1Path‖ < l1Tolerance / 2 :=
    hCenterL1.eventually (Iio_mem_nhds hHalfL1)
  have hCenterDerivativeEventually : ∀ᶠ index in atTop,
      ∀ selectedTest : SelectedTest,
        |((center index).derivative selectedTest.1.1).continuousTestIntegral
              selectedTest.1.2.1 -
          (target.derivative selectedTest.1.1).continuousTestIntegral
              selectedTest.1.2.1| <
            derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2 := by
    apply Filter.eventually_all.2
    intro selectedTest
    have hContinuous : Continuous fun path :
        FiniteIntervalL1DerivativePath Coordinate duration =>
          |(path.derivative selectedTest.1.1).continuousTestIntegral
                selectedTest.1.2.1 -
            (target.derivative selectedTest.1.1).continuousTestIntegral
                selectedTest.1.2.1| :=
      continuous_abs.comp
        ((FiniteIntervalL1DerivativePath.continuous_derivativeTestIntegral
          selectedTest.1.1 selectedTest.1.2).sub continuous_const)
    have hTendsto : Tendsto (fun index =>
        |((center index).derivative selectedTest.1.1).continuousTestIntegral
              selectedTest.1.2.1 -
          (target.derivative selectedTest.1.1).continuousTestIntegral
              selectedTest.1.2.1|) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hContinuous.continuousAt.tendsto.comp hCenter
    exact hTendsto.eventually (Iio_mem_nhds (hHalfDerivative selectedTest))
  have hFailureUpper : ∀ᶠ index in atTop,
      (law index).real {sample | observation index sample ∉ openSet} ≤
        (law index).real {sample | l1Tolerance / 2 ≤
          ‖(observation index sample).toL1Path - (center index).toL1Path‖} +
        ∑ selectedTest : SelectedTest, (law index).real {sample |
          derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2 ≤
            |((observation index sample).derivative
                  selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1 -
              ((center index).derivative
                  selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1|} := by
    filter_upwards [hCenterL1Eventually, hCenterDerivativeEventually] with
      index hCenterL1Index hCenterDerivativeIndex
    let l1Bad : Set (Sample index) := {sample | l1Tolerance / 2 ≤
      ‖(observation index sample).toL1Path - (center index).toL1Path‖}
    let derivativeBad (selectedTest : SelectedTest) : Set (Sample index) := {sample |
      derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2 ≤
        |((observation index sample).derivative
              selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1 -
          ((center index).derivative
              selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1|}
    have hFailureSubset : {sample | observation index sample ∉ openSet} ⊆
        l1Bad ∪ ⋃ selectedTest : SelectedTest, derivativeBad selectedTest := by
      intro sample hSample
      by_contra hNotBad
      have hGood : sample ∉ l1Bad ∧
          ∀ selectedTest : SelectedTest, sample ∉ derivativeBad selectedTest := by
        simpa only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] using hNotBad
      apply hSample
      apply hCylinderSubset
      constructor
      · calc
          ‖(observation index sample).toL1Path - target.toL1Path‖ =
              ‖((observation index sample).toL1Path - (center index).toL1Path) +
                ((center index).toL1Path - target.toL1Path)‖ := by
            congr 1
            abel
          _ ≤
              ‖(observation index sample).toL1Path - (center index).toL1Path‖ +
                ‖(center index).toL1Path - target.toL1Path‖ := by
            exact norm_add_le _ _
          _ < l1Tolerance / 2 + l1Tolerance / 2 :=
            add_lt_add (lt_of_not_ge hGood.1) hCenterL1Index
          _ = l1Tolerance := by ring
      · intro selectedTest hSelectedTest
        let typedTest : SelectedTest := ⟨selectedTest, hSelectedTest⟩
        calc
          |((observation index sample).derivative selectedTest.1).continuousTestIntegral
                selectedTest.2.1 -
            (target.derivative selectedTest.1).continuousTestIntegral selectedTest.2.1| =
              |(((observation index sample).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1 -
                ((center index).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1) +
               (((center index).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1 -
                (target.derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1)| := by
            congr 1
            ring
          _ ≤
              |((observation index sample).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1 -
                ((center index).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1| +
              |((center index).derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1 -
                (target.derivative selectedTest.1).continuousTestIntegral
                    selectedTest.2.1| := abs_add_le _ _
          _ < derivativeTolerance selectedTest.1 selectedTest.2 / 2 +
                derivativeTolerance selectedTest.1 selectedTest.2 / 2 := by
            exact add_lt_add (lt_of_not_ge (hGood.2 typedTest))
              (hCenterDerivativeIndex typedTest)
          _ = derivativeTolerance selectedTest.1 selectedTest.2 := by ring
    calc
      (law index).real {sample | observation index sample ∉ openSet} ≤
          (law index).real
            (l1Bad ∪ ⋃ selectedTest : SelectedTest, derivativeBad selectedTest) :=
        measureReal_mono hFailureSubset
      _ ≤ (law index).real l1Bad +
          (law index).real (⋃ selectedTest : SelectedTest, derivativeBad selectedTest) :=
        measureReal_union_le _ _
      _ ≤ (law index).real l1Bad +
          ∑ selectedTest : SelectedTest, (law index).real (derivativeBad selectedTest) := by
        gcongr
        exact measureReal_iUnion_fintype_le _
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun index => measureReal_nonneg
  · exact hFailureUpper
  · have hL1Tendsto := hL1 (l1Tolerance / 2) hHalfL1
    have hDerivativeTendsto : Tendsto (fun index =>
        ∑ selectedTest : SelectedTest, (law index).real {sample |
          derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2 ≤
            |((observation index sample).derivative
                  selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1 -
              ((center index).derivative
                  selectedTest.1.1).continuousTestIntegral selectedTest.1.2.1|})
        atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ fun selectedTest _hSelectedTest =>
          hDerivative selectedTest.1.1 selectedTest.1.2
            (derivativeTolerance selectedTest.1.1 selectedTest.1.2 / 2)
            (hHalfDerivative selectedTest)
    simpa only [zero_add] using hL1Tendsto.add hDerivativeTendsto

end

end FiniteMarkovProcesses.Probability
