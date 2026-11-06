/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalHybridTopologyConcentration

/-!
# Open-set concentration of empirical Markov jump paths

This module turns the explicit finite-replica derivative-test estimates into asymptotic
concentration for the measurable total hybrid observation.  It then composes those estimates
with strong-`L1` concentration and the finite-cylinder description of the hybrid topology.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction CompactlySupported ENNReal NNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Every fixed empirical ordered-flow derivative test converges in probability to its exact
heterogeneous source mean. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_flowDerivativeTestDeviation_zero
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (edge : FiniteStateOffDiagonalEdge State) (test : C_c(ℝ, ℝ))
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          tolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
              (∑ replica,
                finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                  (PMF.pure (initialConfiguration successorIndex replica)) rates duration
                  test edge.val.1 edge.val.2) / (successorIndex + 1 : ℝ)|})
      atTop (𝓝 0) := by
  let varianceBound : ℝ :=
    ‖ofCompactSupport test test.continuous test.hasCompactSupport‖ ^ 2 *
      (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
        (Real.exp 1 - 1)))
  have hVarianceBound : 0 ≤ varianceBound := by
    dsimp only [varianceBound]
    positivity
  have hParticleCount : Tendsto
      (fun successorIndex : ℕ => (((successorIndex + 1 : ℕ) : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hRealBound : Tendsto
      (fun successorIndex : ℕ =>
        (varianceBound / tolerance ^ 2) /
          (((successorIndex + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hParticleCount
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _successorIndex => measureReal_nonneg
  · exact Filter.Eventually.of_forall fun successorIndex => by
      let law :=
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          (initialConfiguration successorIndex) rates duration).toMeasure
      let badEvent : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
        {histories |
          tolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
              (∑ replica,
                finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                  (PMF.pure (initialConfiguration successorIndex replica)) rates duration
                  test edge.val.1 edge.val.2) / (successorIndex + 1 : ℝ)|}
      have hFiniteBound :=
        finiteStateTimeDependentMarkovDeterministicReplica_flowDerivativeTestDeviation_le
          successorIndex (initialConfiguration successorIndex) rates duration edge test
            hTolerance
      have hParticlePositive : (0 : ℝ) < successorIndex + 1 := by positivity
      change law.real badEvent ≤
        (varianceBound / tolerance ^ 2) / (((successorIndex + 1 : ℕ) : ℝ))
      rw [measureReal_def]
      calc
        (law badEvent).toReal ≤
            (ENNReal.ofReal
              ((((successorIndex + 1 : ℕ) : ℝ) * varianceBound) /
                (((successorIndex + 1 : ℕ) : ℝ) * tolerance) ^ 2)).toReal := by
          apply ENNReal.toReal_mono
          · simp
          · simpa only [law, badEvent, varianceBound] using hFiniteBound
        _ = ((((successorIndex + 1 : ℕ) : ℝ) * varianceBound) /
              (((successorIndex + 1 : ℕ) : ℝ) * tolerance) ^ 2) := by
          rw [ENNReal.toReal_ofReal]
          positivity
        _ = (varianceBound / tolerance ^ 2) /
              (((successorIndex + 1 : ℕ) : ℝ)) := by
          field_simp
  · exact hRealBound

/-- Every fixed empirical density-derivative test converges in probability to its exact
heterogeneous source mean.  The proof uses the microscopic continuity equation to reduce density
failure to a finite union of ordered-flow failures. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_densityDerivativeTestDeviation_zero
    [Nonempty State]
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (state : State) (test : C_c(ℝ, ℝ))
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          tolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inl state)).continuousTestIntegral test -
              ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
                successorIndex (initialConfiguration successorIndex) rates duration).derivative
                  (Sum.inl state)).continuousTestIntegral test|})
      atTop (𝓝 0) := by
  classical
  let flowTolerance := tolerance / (4 * Fintype.card State : ℝ)
  have hCardPositive : (0 : ℝ) < Fintype.card State := by
    exact_mod_cast Fintype.card_pos
  have hFlowTolerance : 0 < flowTolerance := by
    dsimp only [flowTolerance]
    positivity
  have hFlowTendsto (edge : FiniteStateOffDiagonalEdge State) : Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          flowTolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
              ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
                successorIndex (initialConfiguration successorIndex) rates duration).derivative
                  (Sum.inr edge)).continuousTestIntegral test|})
      atTop (𝓝 0) := by
    simpa only [
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq]
      using
        tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_flowDerivativeTestDeviation_zero
          initialConfiguration rates duration edge test flowTolerance hFlowTolerance
  have hFlowSumTendsto : Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        ∑ edge : FiniteStateOffDiagonalEdge State, law.real {histories |
          flowTolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
              ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
                successorIndex (initialConfiguration successorIndex) rates duration).derivative
                  (Sum.inr edge)).continuousTestIntegral test|})
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ fun edge _hEdge => hFlowTendsto edge
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _successorIndex => measureReal_nonneg
  · exact Filter.Eventually.of_forall fun successorIndex => by
      let law :=
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          (initialConfiguration successorIndex) rates duration).toMeasure
      let center :=
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration
      let densityBad : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
        {histories |
          tolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inl state)).continuousTestIntegral test -
              (center.derivative (Sum.inl state)).continuousTestIntegral test|}
      let flowBad (edge : FiniteStateOffDiagonalEdge State) :
          Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
        {histories |
          flowTolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
              (center.derivative (Sum.inr edge)).continuousTestIntegral test|}
      change law.real densityBad ≤ ∑ edge, law.real (flowBad edge)
      calc
        law.real densityBad ≤ law.real (⋃ edge, flowBad edge) := by
          refine measureReal_mono ?_ ?_
          · intro histories hDensityBad
            by_contra hNoFlowBad
            have hFlowGood : ∀ edge : FiniteStateOffDiagonalEdge State,
                |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                    successorIndex histories (Sum.inr edge)).continuousTestIntegral test -
                  (center.derivative (Sum.inr edge)).continuousTestIntegral test| <
                    tolerance / (4 * Fintype.card State : ℝ) := by
              intro edge
              have hNotMember : histories ∉ flowBad edge := by
                intro hMember
                apply hNoFlowBad
                exact Set.mem_iUnion.2 ⟨edge, hMember⟩
              exact lt_of_not_ge hNotMember
            have hDensityGood :=
              PositiveFiniteJumpHistoryReplicas.abs_empiricalDensityDerivativeTest_sub_flowBalance_lt_of_flow_lt
                successorIndex histories state test
                (fun edge => (center.derivative (Sum.inr edge)).continuousTestIntegral test)
                hTolerance hFlowGood
            rw [←
              finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_density_continuousTestIntegral_eq]
              at hDensityGood
            exact (not_lt_of_ge hDensityBad) hDensityGood
          · dsimp only [law]
            finiteness
        _ ≤ ∑ edge, law.real (flowBad edge) := measureReal_iUnion_fintype_le _
  · exact hFlowSumTendsto

/-- Every fixed coordinate and compact derivative test of the empirical full derivative
converges in probability to the heterogeneous source mean. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_fullDerivativeTestDeviation_zero
    [Nonempty State]
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (test : C_c(ℝ, ℝ)) (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          tolerance ≤
            |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
                successorIndex histories coordinate).continuousTestIntegral test -
              ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
                successorIndex (initialConfiguration successorIndex) rates duration).derivative
                  coordinate).continuousTestIntegral test|})
      atTop (𝓝 0) := by
  cases coordinate with
  | inl state =>
      exact
        tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_densityDerivativeTestDeviation_zero
          initialConfiguration rates duration state test tolerance hTolerance
  | inr edge =>
      simpa only [
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq]
        using
          tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_flowDerivativeTestDeviation_zero
            initialConfiguration rates duration edge test tolerance hTolerance

/-- Every fixed derivative test of the measurable total hybrid observation converges in
probability to the heterogeneous source mean.  Totalization changes only the unordered null set,
so this is an exact almost-sure transport of full-derivative concentration. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalDerivativeTestDeviation_zero
    [TopologicalSpace State] [_unusedDiscreteTopology : DiscreteTopology State]
    [_unusedBorelSpace : BorelSpace State] [Nonempty State]
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (test : C_c(ℝ, ℝ)) (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          tolerance ≤
            |((PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
                successorIndex duration histories).toDerivativePath.derivative
                  coordinate).continuousTestIntegral test -
              ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
                successorIndex (initialConfiguration successorIndex) rates duration).derivative
                  coordinate).continuousTestIntegral test|})
      atTop (𝓝 0) := by
  have hFull :=
    tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_fullDerivativeTestDeviation_zero
      initialConfiguration rates duration coordinate test tolerance hTolerance
  apply hFull.congr'
  exact Filter.Eventually.of_forall fun successorIndex => by
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        (initialConfiguration successorIndex) rates duration).toMeasure
    let center :=
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex (initialConfiguration successorIndex) rates duration
    apply measureReal_congr
    filter_upwards [
      ae_orderedBefore_finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        (initialConfiguration successorIndex) rates duration] with histories hOrdered
    symm
    change
      (tolerance ≤
        |((PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath.derivative
              coordinate).continuousTestIntegral test -
          (center.derivative coordinate).continuousTestIntegral test|) =
        (tolerance ≤
          |(PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowFullDerivative
              successorIndex histories coordinate).continuousTestIntegral test -
            (center.derivative coordinate).continuousTestIntegral test|)
    rw
      [PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
      successorIndex duration histories hOrdered]
    have hDerivative :=
      PositiveFiniteJumpHistoryReplicas.orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_derivative
        successorIndex (duration : ℝ)
        (fun replica => ⟨histories replica, hOrdered replica⟩) coordinate
    simpa only [PositiveFiniteJumpHistoryReplicas.orderedReplicaHistories] using!
      congrArg (fun derivative : VagueSignedMeasure ℝ =>
        tolerance ≤ |derivative.continuousTestIntegral test -
          (center.derivative coordinate).continuousTestIntegral test|) hDerivative

/-- Once the heterogeneous deterministic source centers converge to a target hybrid path, the
measurable total empirical observations concentrate in every open neighborhood of that target.
This is the full topology-side lower-bound input; no metricization of the vague derivative family
is used. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalHybridObservation_not_mem_open_zero
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hDuration : 0 < duration)
    (target : FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ))
    (hCenter : Tendsto
      (fun successorIndex =>
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration)
      atTop (𝓝 target))
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ))}
    (hOpen : IsOpen openSet) (hTarget : target ∈ openSet) :
    Tendsto
      (fun successorIndex =>
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (initialConfiguration successorIndex) rates duration).toMeasure
        law.real {histories |
          (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath ∉ openSet})
      atTop (𝓝 0) := by
  apply tendsto_measureReal_hybridObservation_not_mem_open_zero
    (Sample := fun successorIndex =>
      PositiveFiniteJumpHistoryReplicas State successorIndex)
    (law := fun successorIndex =>
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        (initialConfiguration successorIndex) rates duration).toMeasure)
    (observation := fun successorIndex histories =>
      (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath)
    (center := fun successorIndex =>
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex (initialConfiguration successorIndex) rates duration)
    target hCenter
  · intro tolerance hTolerance
    simpa only [
      finiteStateTimeDependentMarkovTotalHybridL1PathDeviation,
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_toL1Path] using
      tendsto_measureReal_finiteStateTimeDependentMarkovTotalHybridL1PathDeviation_ge_zero
        initialConfiguration rates duration hDuration tolerance hTolerance
  · intro coordinate test tolerance hTolerance
    exact
      tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalDerivativeTestDeviation_zero
        initialConfiguration rates duration coordinate test.1 tolerance hTolerance
  · exact hOpen
  · exact hTarget

end

end FiniteMarkovProcesses.Probability
