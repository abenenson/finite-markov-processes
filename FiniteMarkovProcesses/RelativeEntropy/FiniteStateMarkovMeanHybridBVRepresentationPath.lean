/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRepresentationDomain
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanHybridBVPath

/-!
# Finite-state Markov mean as an admissible hybrid-BV representation path

This module packages the existing arbitrary-initial-PMF Markov mean path directly in the Renger
density--directional-flow representation domain.  The resulting object is the actual mean path:
its underlying hybrid path is definitionally
`finiteStateTimeDependentMarkovMeanHybridBVPath initial generator.toTimeDependentMarkovRate`.

No stationary law, comparison generator, large-deviation theorem, or source-specific action is
used here.

## Main declaration

- `finiteStateMarkovMeanHybridBVRepresentationPath`.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- The genuine Markov mean hybrid path from an arbitrary initial PMF is an admissible Renger
representation path.  No supplied density/flow witness is introduced. -/
noncomputable def finiteStateMarkovMeanHybridBVRepresentationPath
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration := by
  let meanPath :=
    finiteStateTimeDependentMarkovMeanHybridBVPath initial
      generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
  refine ⟨meanPath, ?_⟩
  refine
    { absolutelyContinuousDerivative :=
        finiteStateTimeDependentMarkovMeanHybridBVPath_hasAbsolutelyContinuousDerivative
          initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      densityNonnegativeAE := ?_
      densityNormalizedAE := ?_
      cumulativeFlowNonnegativeAE := ?_
      flowDerivativeNonnegativeAE := ?_
      continuityEquationAE := ?_
      initialDensityNormalized := ?_
      initialDensityNonnegative := ?_
      cumulativeFlowInitiallyZero := ?_
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro state
    unfold rengerDirectionalFlowHybridBVDensityValue
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        ⟨hTime.1.le, hTime.2⟩,
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        hTime.1.le hTime.2.le state]
    exact ENNReal.toReal_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    change ∑ state, meanPath.cadlagRepresentative.representative time (Sum.inl state) = 1
    rw [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        ⟨hTime.1.le, hTime.2⟩]
    change ∑ state, finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial generator.toTimeDependentMarkovRate duration
      time (Sum.inl state) = 1
    calc
      _ = ∑ state, (finiteStateTimeDependentMarkovEndpointProbability initial
          generator.toTimeDependentMarkovRate time state).toReal := by
        apply Finset.sum_congr rfl
        intro state _hState
        exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
          initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
          hTime.1.le hTime.2.le state
      _ = 1 := PMF.sum_toReal <|
        finiteStateTimeDependentMarkovEndpointPMF initial
          generator.toTimeDependentMarkovRate ⟨time, hTime.1.le⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro transition
    unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        ⟨hTime.1.le, hTime.2⟩]
    exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow_nonnegative
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      hTime.1.le transition
  · rw [ae_all_iff]
    intro transition
    have hFlow :=
      ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        (Sum.inr transition)
    filter_upwards [hFlow] with time hFlowAt
    unfold rengerDirectionalFlowHybridBVFlowDerivative
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      hFlowAt]
    unfold finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
    exact mul_nonneg ENNReal.toReal_nonneg
      (generator.rate transition.val.1 transition.val.2).coe_nonneg
  · rw [ae_all_iff]
    intro state
    have hDensity :=
      ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        (Sum.inl state)
    have hFlow :
        ∀ᵐ time ∂finiteOpenIntervalVolume duration,
          ∀ transition,
            meanPath.derivativeDensity (Sum.inr transition) time =
              finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue initial
                generator.toTimeDependentMarkovRate time (Sum.inr transition) := by
      rw [ae_all_iff]
      intro transition
      simpa only [meanPath] using!
        ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
          initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
          (Sum.inr transition)
    filter_upwards [hDensity, hFlow] with time hDensityAt hFlowAt
    simp only [meanPath] at hFlowAt
    unfold rengerDirectionalFlowHybridBVDensityDerivative
      rengerDirectionalFlowHybridBVFlowDerivative
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      hDensityAt,
      finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue_density_eq_flowBalance]
    apply congrArg₂ (fun incoming outgoing : ℝ => incoming - outgoing)
    · apply Finset.sum_congr rfl
      intro source _hSource
      exact (hFlowAt ⟨(source, state), source.property⟩).symm
    · apply Finset.sum_congr rfl
      intro target _hTarget
      exact (hFlowAt ⟨(state, target), target.property.symm⟩).symm
  · rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change ∑ state, (initial state).toReal = 1
    exact PMF.sum_toReal initial
  · intro state
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change 0 ≤ (initial state).toReal
    exact ENNReal.toReal_nonneg
  · intro transition
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    simp [finiteStateTimeDependentMarkovMeanHybridBVInitialValue]
  · rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    change ∑ state, finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial generator.toTimeDependentMarkovRate duration
      duration (Sum.inl state) = 1
    calc
      _ = ∑ state, (finiteStateTimeDependentMarkovEndpointProbability initial
          generator.toTimeDependentMarkovRate duration state).toReal := by
        apply Finset.sum_congr rfl
        intro state _hState
        exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
          initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
          hDuration.le le_rfl state
      _ = 1 := PMF.sum_toReal <|
        finiteStateTimeDependentMarkovEndpointPMF initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
  · intro state
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    have hValue :=
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
        (show 0 ≤ ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) by positivity) le_rfl state
    exact hValue.symm ▸ ENNReal.toReal_nonneg
  · intro transition
    rw (transparency := .default)
      [show meanPath = finiteStateTimeDependentMarkovMeanHybridBVPath initial
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ by rfl,
      finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace _ _
        (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
    exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow_nonnegative
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      (show 0 ≤ ((⟨duration, hDuration.le⟩ : ℝ≥0) : ℝ) by positivity) transition

/-- Forgetting the admissibility proof recovers the existing arbitrary-PMF Markov mean path
definitionally. -/
@[simp]
theorem finiteStateMarkovMeanHybridBVRepresentationPath_toHybridBVPath
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    (finiteStateMarkovMeanHybridBVRepresentationPath initial generator hDuration).1 =
      finiteStateTimeDependentMarkovMeanHybridBVPath initial
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ :=
  rfl

/-- The recovered initial-density coordinate is exactly the supplied initial PMF coordinate. -/
theorem finiteStateMarkovMeanHybridBVRepresentationPath_initialDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (state : State) :
    rengerDirectionalFlowHybridBVInitialDensity
        (finiteStateMarkovMeanHybridBVRepresentationPath
          initial generator hDuration).1 state =
      Real.toNNReal (initial state).toReal := by
  unfold rengerDirectionalFlowHybridBVInitialDensity
  rw (transparency := .default) [finiteStateMarkovMeanHybridBVRepresentationPath_toHybridBVPath,
    finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace _ _
      (show 0 < (⟨duration, hDuration.le⟩ : ℝ≥0) by exact_mod_cast hDuration)]
  rfl

end

end FiniteMarkovProcesses.InformationTheory
