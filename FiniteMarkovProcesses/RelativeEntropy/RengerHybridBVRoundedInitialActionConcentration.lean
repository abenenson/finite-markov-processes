/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetOpenSetConcentration
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetActionExpectation
import Mathlib.MeasureTheory.Measure.Real

/-!
# Rounded-initial action concentration for Renger target regularizations

At one fixed canonical positive regularization, the average of the pure-initial expected complete
jump actions under a rounded deterministic initial configuration converges to the exact expectation
under the requested initial PMF.  The corresponding summed replica action concentrates at
particle speed around that heterogeneous mean.

No regularization limit, change of measure, or open lower bound is asserted here.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- At fixed regularization, coordinatewise convergence of deterministic empirical initial
densities makes the average pure-initial action expectation converge to the exact target-initial
action expectation. -/
theorem
tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialExpectedJumpLogActionAverage_of_empiricalInitial_weight_tendsto
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ)
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ))) :
    Tendsto
      (fun successorIndex ↦
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        (∑ replica, ∫ history,
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
              generator path index history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration successorIndex replica)) rates
            ⟨duration, hDuration.le⟩) / (successorIndex + 1 : ℝ))
      atTop
      (nhds
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path))) := by
  let rates :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index
  let value : State → ℝ := fun state ↦
    ∫ history,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index history
    ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure state) rates ⟨duration, hDuration.le⟩
  have hTarget :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path) =
        ∑ state,
          ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ) *
            value state := by
    rw [← integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_eq_expected
      generator hDuration path index (rengerDirectionalFlowHybridBVTargetInitialPMF path)]
    rw (transparency := .default)
      [integral_finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_mul_pure]
    · rfl
    · intro state
      let : MeasureTheory.IsProbabilityMeasure
          (finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure state) rates ⟨duration, hDuration.le⟩) :=
        ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
          (PMF.pure state) rates ⟨duration, hDuration.le⟩⟩
      exact
        (memLp_two_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator hDuration path index (PMF.pure state)).integrable one_le_two
  rw [hTarget]
  have hSum := tendsto_finsetSum Finset.univ fun state _hState ↦
    (hWeight state).mul_const (value state)
  change Tendsto
    (fun successorIndex ↦
      (∑ replica,
        value (initialConfiguration successorIndex replica)) / (successorIndex + 1 : ℝ))
    atTop
    (nhds (∑ state,
      ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ) *
        value state))
  rw [show (fun successorIndex ↦
      (∑ replica,
        value (initialConfiguration successorIndex replica)) / (successorIndex + 1 : ℝ)) =
      fun successorIndex ↦ ∑ state,
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ) * value state by
    funext successorIndex
    exact sum_div_eq_sum_finiteIIDEmpiricalProbabilityDensity_weight_mul
      successorIndex (initialConfiguration successorIndex) value]
  exact hSum

/-- The canonical rounded deterministic configurations satisfy the generic empirical-initial
action convergence theorem. -/
theorem
tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRoundedInitialExpectedJumpLogActionAverage
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    Tendsto
      (fun successorIndex ↦
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        let initialConfiguration :=
          finiteStateProbabilityDensityRoundedInitialConfiguration
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path)
            successorIndex
        (∑ replica, ∫ history,
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
              generator path index history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates
            ⟨duration, hDuration.le⟩) / (successorIndex + 1 : ℝ))
      atTop
      (nhds
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index (rengerDirectionalFlowHybridBVTargetInitialPMF path))) := by
  apply
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialExpectedJumpLogActionAverage_of_empiricalInitial_weight_tendsto
  intro state
  simpa only [finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration] using
    finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) state

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The heterogeneous replica action used by the finite-product likelihood ratio is exactly the
sum of the canonical target actions.  The common initial law cancels pointwise in every
coordinate. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction_eq_sum
    {replicaCount : ℕ} (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initialConfiguration : Fin replicaCount → State)
    (histories : Fin replicaCount → FiniteJumpHistory State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
        generator path index initialConfiguration histories =
      ∑ replica,
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index (histories replica) := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
    finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
  apply Finset.sum_congr rfl
  intro replica _hReplica
  exact congrFun
    (finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq
      (PMF.pure (initialConfiguration replica))
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      generator.toTimeDependentMarkovRate duration)
    (histories replica)

/-- At fixed regularization, any deterministic replica action misses its exact heterogeneous
expectation by a positive particle-speed tolerance with probability tending to zero. -/
theorem
tendsto_measureReal_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplicaJumpLogActionParticleSpeedDeviation_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ)
    (initialConfigurations : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex ↦
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        let initialConfiguration := initialConfigurations successorIndex
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
        law.real {histories |
          (successorIndex + 1 : ℝ) * tolerance ≤
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
                generator path index initialConfiguration histories -
              ∑ replica, ∫ history,
                rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                  generator path index history
                ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                  (PMF.pure (initialConfiguration replica)) rates
                  ⟨duration, hDuration.le⟩|})
      atTop (nhds 0) := by
  let varianceBound :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
      generator path index
  have hVarianceBound : 0 ≤ varianceBound := by
    unfold varianceBound
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
    exact Finset.sum_nonneg fun state _hState ↦ variance_nonneg _ _
  have hParticleCount : Tendsto
      (fun successorIndex : ℕ ↦ ((successorIndex + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hRealBound : Tendsto
      (fun successorIndex : ℕ ↦
        (varianceBound / tolerance ^ 2) /
          ((successorIndex + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hParticleCount
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _successorIndex ↦
      MeasureTheory.measureReal_nonneg
  · exact Filter.Eventually.of_forall fun successorIndex ↦ by
      let rates :=
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index
      let initialConfiguration := initialConfigurations successorIndex
      let law :=
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
      let badActionEvent : Set (PositiveFiniteJumpHistoryReplicas State successorIndex) :=
        {histories |
          (successorIndex + 1 : ℝ) * tolerance ≤
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
                generator path index initialConfiguration histories -
              ∑ replica, ∫ history,
                rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                  generator path index history
                ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                  (PMF.pure (initialConfiguration replica)) rates
                  ⟨duration, hDuration.le⟩|}
      have hFiniteBound :=
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogActionParticleSpeedDeviation_le
          (Nat.succ_pos successorIndex) generator hDuration path index
          initialConfiguration hTolerance
      have hParticlePositive : (0 : ℝ) < successorIndex + 1 := by positivity
      change law.real badActionEvent ≤
        (varianceBound / tolerance ^ 2) / ((successorIndex + 1 : ℕ) : ℝ)
      rw [MeasureTheory.measureReal_def]
      calc
        (law badActionEvent).toReal ≤
            (ENNReal.ofReal
              (varianceBound /
                (((successorIndex + 1 : ℕ) : ℝ) * tolerance ^ 2))).toReal := by
          apply ENNReal.toReal_mono
          · simp
          · dsimp only [law, badActionEvent, rates, varianceBound]
            simp only [
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction_eq_sum]
            convert hFiniteBound using 1
            all_goals norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        _ = varianceBound /
              (((successorIndex + 1 : ℕ) : ℝ) * tolerance ^ 2) := by
          rw [ENNReal.toReal_ofReal]
          positivity
        _ = (varianceBound / tolerance ^ 2) /
              ((successorIndex + 1 : ℕ) : ℝ) := by
          field_simp
  · exact hRealBound

/-- The canonical rounded deterministic configurations satisfy the generic replica-action
concentration theorem. -/
theorem
tendsto_measureReal_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRoundedInitialReplicaJumpLogActionParticleSpeedDeviation_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    Tendsto
      (fun successorIndex ↦
        let rates :=
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index
        let initialConfiguration :=
          finiteStateProbabilityDensityRoundedInitialConfiguration
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path)
            successorIndex
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
        law.real {histories |
          (successorIndex + 1 : ℝ) * tolerance ≤
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
                generator path index initialConfiguration histories -
              ∑ replica, ∫ history,
                rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                  generator path index history
                ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                  (PMF.pure (initialConfiguration replica)) rates
                  ⟨duration, hDuration.le⟩|})
      atTop (nhds 0) := by
  exact
    tendsto_measureReal_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDeterministicInitialReplicaJumpLogActionParticleSpeedDeviation_zero
      generator hDuration path index
      (fun successorIndex ↦
        finiteStateProbabilityDensityRoundedInitialConfiguration
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) successorIndex)
      tolerance hTolerance

end

end FiniteMarkovProcesses.InformationTheory
