/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVSourceKinematicSupport
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservation

/-!
# Finite jump histories lie in Renger source-kinematic support

The explicit empirical density--directional-flow observation has positive atomic ordered-flow
derivatives, exact microscopic continuity, and the open-interval simplex constraints.  It is not
finite-rate admissible when a jump occurs because those derivatives are singular.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability
open FiniteMarkovProcesses.Probability.PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every ordered explicit empirical hybrid observation satisfies the exact integrated
density--cumulative-flow continuity law, including its independently counted initial density. -/
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_integratedContinuity
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    RengerDirectionalFlowHybridBVIntegratedContinuity
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered) := by
  let path := empiricalDensityDirectionalFlowExplicitHybridBVPath
    successorIndex histories duration hOrdered
  let explicitRepresentative :=
    empiricalDensityDirectionalFlowExplicitCadlagRepresentative
      successorIndex histories duration hOrdered
  have hRepresentativeEquality : Set.EqOn
      path.cadlagRepresentative.representative
      explicitRepresentative.representative (Ico 0 duration) :=
    FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
      path.cadlagRepresentative explicitRepresentative
  have hConstraints := empiricalDensityDirectionalFlow_constraints
    successorIndex histories duration hOrdered
  have hValueAtTime (time : ℝ) (hTime : time ∈ Ico 0 duration) :
      path.cadlagRepresentative.representative time =
        empiricalDensityDirectionalFlowL1ValueAtTime
          successorIndex histories time := by
    rw [hRepresentativeEquality hTime]
    exact empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
      successorIndex histories duration time hOrdered
  intro state time hTime
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVCumulativeFlowValue
  rw [hValueAtTime time hTime]
  rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_initialTrace
    successorIndex histories duration hDuration hOrdered]
  simp only [empiricalDensityDirectionalFlowL1ValueAtTime_density,
    empiricalDensityDirectionalFlowL1ValueAtTime_flow,
    empiricalDensityDirectionalFlowInitialL1Value_density]
  simpa only [empiricalOffDiagonalDirectionalFlowAtTime,
    empiricalDensityAtTime_zero_eq_empiricalInitialDensity
      successorIndex histories duration state hOrdered] using
    hConstraints.continuityEquation time state

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every ordered explicit empirical hybrid observation belongs to the topology-closed
source-kinematic support class. -/
theorem empiricalDensityDirectionalFlowExplicitHybridBVPath_sourceKinematicSupport
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    RengerDirectionalFlowHybridBVSourceKinematicSupport
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered) hDuration := by
  classical
  let path := empiricalDensityDirectionalFlowExplicitHybridBVPath
    successorIndex histories duration hOrdered
  let explicitRepresentative :=
    empiricalDensityDirectionalFlowExplicitCadlagRepresentative
      successorIndex histories duration hOrdered
  have hRepresentativeEquality : Set.EqOn
      path.cadlagRepresentative.representative
      explicitRepresentative.representative (Ico 0 duration) :=
    FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
      path.cadlagRepresentative explicitRepresentative
  have hConstraints := empiricalDensityDirectionalFlow_constraints
    successorIndex histories duration hOrdered
  have hValueAtTime (time : ℝ) (hTime : time ∈ Ico 0 duration) :
      path.cadlagRepresentative.representative time =
        empiricalDensityDirectionalFlowL1ValueAtTime
          successorIndex histories time := by
    rw [hRepresentativeEquality hTime]
    exact empiricalDensityDirectionalFlowEventStepL1ValueAtTime_eq_empirical
      successorIndex histories duration time hOrdered
  have hIntegratedContinuity :=
    empiricalDensityDirectionalFlowExplicitHybridBVPath_integratedContinuity
      successorIndex histories duration hDuration hOrdered
  refine
    { densityNonnegativeAE := ?_
      densityNormalizedAE := ?_
      cumulativeFlowNonnegativeAE := ?_
      flowDerivativeMeasureNonnegative := ?_
      derivativeContinuity :=
        rengerDirectionalFlowHybridBVDerivativeContinuity_of_integratedContinuity
          hIntegratedContinuity }
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro state
    unfold rengerDirectionalFlowHybridBVDensityValue
    rw [hValueAtTime time ⟨hTime.1.le, hTime.2⟩]
    simpa only [empiricalDensityDirectionalFlowL1ValueAtTime_density] using
      hConstraints.densityNonnegative time state
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    unfold rengerDirectionalFlowHybridBVDensityValue
    rw [hValueAtTime time ⟨hTime.1.le, hTime.2⟩]
    simpa only [empiricalDensityDirectionalFlowL1ValueAtTime_density] using
      hConstraints.densityNormalized time
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro transition
    unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rw [hValueAtTime time ⟨hTime.1.le, hTime.2⟩]
    simpa only [empiricalDensityDirectionalFlowL1ValueAtTime_flow] using!
      hConstraints.directionalFlowNonnegative time transition
  · intro transition
    rw [show path.toDerivativePath.derivative (Sum.inr transition) =
        finiteRestrictedWeightedDiracVagueSignedMeasure duration
          (fun event : EmpiricalDensityDirectionalFlowEventIndex
              successorIndex histories =>
            (histories event.1).jumpTimes event.2)
          (fun event => empiricalDensityDirectionalFlowEventIncrement
            successorIndex (histories event.1) event.2 (Sum.inr transition)) by
      exact empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative_eq_finiteRestricted
        successorIndex histories duration hOrdered (Sum.inr transition)]
    unfold finiteRestrictedWeightedDiracVagueSignedMeasure
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    apply Finset.sum_nonneg
    intro event _
    let coefficient := empiricalDensityDirectionalFlowEventIncrement
      successorIndex (histories event.1) event.2 (Sum.inr transition)
    have hCoefficient : 0 ≤ coefficient := by
      unfold coefficient empiricalDensityDirectionalFlowEventIncrement
      positivity
    let coefficientNNReal : NNReal := ⟨coefficient, hCoefficient⟩
    change 0 ≤ (coefficientNNReal : ℝ) •
      ((Measure.dirac ((histories event.1).jumpTimes event.2)).restrict
        (Ioo 0 duration)).toSignedMeasure
    rw [← NNReal.smul_def, ← Measure.toSignedMeasure_smul]
    exact Measure.zero_le_toSignedMeasure _

end

end FiniteMarkovProcesses.InformationTheory
