/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVL1ConstraintClosure
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVBoundaryTrace

/-!
# Value-constraint closure for Renger hybrid paths

This module closes the pointwise-value and recovered-boundary sectors of the finite-rate Renger
representation domain under hybrid convergence with one uniform finite dynamic-rate level.
Strong `L1` convergence supplies almost-everywhere convergence of selected representatives along
a subsequence, while bounded-rate endpoint control supplies convergence of both recovered traces.

Derivative positivity, the continuity equation, absolute continuity, converse dual
representation, and lower semicontinuity are deliberately outside this module.

## Main declarations

* `RengerDirectionalFlowHybridBVValueConstraints` collects exactly the value and boundary fields
  of finite-rate admissibility.
* `rengerDirectionalFlowHybridBVValueConstraints_of_tendsto_of_uniformlyBoundedDynamicRate`
  proves that these constraints survive a bounded-rate hybrid limit.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The open-interval value and recovered-boundary sectors of finite-rate Renger admissibility. -/
structure RengerDirectionalFlowHybridBVValueConstraints
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) : Prop where
  /-- Open-interval density coordinates are nonnegative almost everywhere. -/
  densityNonnegativeAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue path time state
  /-- Open-interval density coordinates sum to one almost everywhere. -/
  densityNormalizedAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∑ state, rengerDirectionalFlowHybridBVDensityValue path time state = 1
  /-- Open-interval cumulative one-way flows are nonnegative almost everywhere. -/
  cumulativeFlowNonnegativeAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ transition,
        0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition
  /-- The recovered initial density lies in the finite simplex. -/
  initialDensityNormalized :
    ∑ state, path.initialTrace (Sum.inl state) = 1
  /-- The recovered initial density has no negative coordinate. -/
  initialDensityNonnegative :
    ∀ state, 0 ≤ path.initialTrace (Sum.inl state)
  /-- Recovered cumulative directional flow starts at zero. -/
  cumulativeFlowInitiallyZero :
    ∀ transition, path.initialTrace (Sum.inr transition) = 0
  /-- The recovered terminal density lies in the finite simplex. -/
  terminalDensityNormalized :
    ∑ state, path.terminalTrace hDuration (Sum.inl state) = 1
  /-- The recovered terminal density has no negative coordinate. -/
  terminalDensityNonnegative :
    ∀ state, 0 ≤ path.terminalTrace hDuration (Sum.inl state)
  /-- Recovered terminal cumulative directional flows remain nonnegative. -/
  terminalCumulativeFlowNonnegative :
    ∀ transition, 0 ≤ path.terminalTrace hDuration (Sum.inr transition)

/-- Finite-rate admissibility supplies all open-interval value and recovered-boundary
constraints. -/
theorem RengerDirectionalFlowHybridBVAdmissible.valueConstraints
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (admissible : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    RengerDirectionalFlowHybridBVValueConstraints path hDuration where
  densityNonnegativeAE := admissible.densityNonnegativeAE
  densityNormalizedAE := admissible.densityNormalizedAE
  cumulativeFlowNonnegativeAE := admissible.cumulativeFlowNonnegativeAE
  initialDensityNormalized := admissible.initialDensityNormalized
  initialDensityNonnegative := admissible.initialDensityNonnegative
  cumulativeFlowInitiallyZero := admissible.cumulativeFlowInitiallyZero
  terminalDensityNormalized := admissible.terminalDensityNormalized
  terminalDensityNonnegative := admissible.terminalDensityNonnegative
  terminalCumulativeFlowNonnegative := admissible.terminalCumulativeFlowNonnegative

private theorem finiteCoordinateL1Value_coordinate_tendsto
    {Coordinate : Type*}
    {values : ℕ → FiniteCoordinateL1Value Coordinate}
    {limit : FiniteCoordinateL1Value Coordinate}
    (hTendsto : Tendsto values atTop (nhds limit)) (coordinate : Coordinate) :
    Tendsto (fun sequenceIndex => values sequenceIndex coordinate)
      atTop (nhds (limit coordinate)) := by
  have hProjection :=
    (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).continuous
      |>.continuousAt.tendsto.comp hTendsto
  simpa only [PiLp.proj_apply] using! hProjection

private theorem eq_of_tendsto_of_forall_eq
    {values : ℕ → ℝ} {limit constant : ℝ}
    (hTendsto : Tendsto values atTop (nhds limit))
    (hValues : ∀ sequenceIndex, values sequenceIndex = constant) :
    limit = constant := by
  apply tendsto_nhds_unique hTendsto
  exact tendsto_const_nhds.congr'
    (Filter.Eventually.of_forall fun sequenceIndex => (hValues sequenceIndex).symm)

/-- Hybrid convergence with one uniform finite dynamic-rate level preserves every pointwise-value
and recovered-boundary constraint in the Renger representation domain. -/
theorem
    rengerDirectionalFlowHybridBVValueConstraints_of_tendsto_of_uniformlyBoundedDynamicRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto paths atTop (nhds limitPath)) :
    RengerDirectionalFlowHybridBVValueConstraints limitPath hDuration := by
  have hL1Tendsto := (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).1
  obtain ⟨subsequence, _hSubsequenceMonotone, hRepresentativeTendsto⟩ :=
    exists_subsequence_tendsto_cadlagRepresentative_ae_of_tendsto_toL1Path
      paths limitPath hL1Tendsto
  have hSequenceValueConstraints :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ sequenceIndex,
        (∀ state,
          0 ≤ rengerDirectionalFlowHybridBVDensityValue
            (paths sequenceIndex) time state) ∧
        (∑ state,
          rengerDirectionalFlowHybridBVDensityValue
            (paths sequenceIndex) time state = 1) ∧
        ∀ transition,
          0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue
            (paths sequenceIndex) time transition := by
    rw [ae_all_iff]
    intro sequenceIndex
    filter_upwards [(hPaths sequenceIndex).densityNonnegativeAE,
      (hPaths sequenceIndex).densityNormalizedAE,
      (hPaths sequenceIndex).cumulativeFlowNonnegativeAE] with
      time hDensityNonnegative hDensityNormalized hFlowNonnegative
    exact ⟨hDensityNonnegative, hDensityNormalized, hFlowNonnegative⟩
  have hLimitValueConstraints :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        (∀ state,
          0 ≤ rengerDirectionalFlowHybridBVDensityValue limitPath time state) ∧
        (∑ state,
          rengerDirectionalFlowHybridBVDensityValue limitPath time state = 1) ∧
        ∀ transition,
          0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue
            limitPath time transition := by
    filter_upwards [hRepresentativeTendsto, hSequenceValueConstraints] with
      time hTimeTendsto hTimeConstraints
    have hCoordinateTendsto :=
      finiteCoordinateL1Value_coordinate_tendsto hTimeTendsto
    refine ⟨fun state => ?_, ?_, fun transition => ?_⟩
    · change 0 ≤ limitPath.cadlagRepresentative.representative time (Sum.inl state)
      apply ge_of_tendsto' (hCoordinateTendsto (Sum.inl state))
      exact fun sequenceIndex => (hTimeConstraints (subsequence sequenceIndex)).1 state
    · have hSumTendsto : Tendsto
          (fun sequenceIndex =>
            ∑ state,
              (paths (subsequence sequenceIndex)).cadlagRepresentative.representative
                time (Sum.inl state))
          atTop
          (nhds (∑ state,
            limitPath.cadlagRepresentative.representative time (Sum.inl state))) :=
        tendsto_finsetSum Finset.univ fun state _ => hCoordinateTendsto (Sum.inl state)
      exact eq_of_tendsto_of_forall_eq hSumTendsto fun sequenceIndex =>
        (hTimeConstraints (subsequence sequenceIndex)).2.1
    · change 0 ≤ limitPath.cadlagRepresentative.representative time (Sum.inr transition)
      apply ge_of_tendsto' (hCoordinateTendsto (Sum.inr transition))
      exact fun sequenceIndex => (hTimeConstraints (subsequence sequenceIndex)).2.2 transition
  have hInitialTendsto :=
    rengerDirectionalFlowHybridBVTendstoInitialTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hL1Tendsto
  have hInitialCoordinateTendsto :=
    finiteCoordinateL1Value_coordinate_tendsto hInitialTendsto
  have hTerminalTendsto :=
    rengerDirectionalFlowHybridBVTendstoTerminalTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hL1Tendsto
  have hTerminalCoordinateTendsto :=
    finiteCoordinateL1Value_coordinate_tendsto hTerminalTendsto
  refine
    { densityNonnegativeAE := hLimitValueConstraints.mono fun _ hTime => hTime.1
      densityNormalizedAE := hLimitValueConstraints.mono fun _ hTime => hTime.2.1
      cumulativeFlowNonnegativeAE := hLimitValueConstraints.mono fun _ hTime => hTime.2.2
      initialDensityNormalized := ?_
      initialDensityNonnegative := ?_
      cumulativeFlowInitiallyZero := ?_
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · have hSumTendsto : Tendsto
        (fun sequenceIndex => ∑ state, (paths sequenceIndex).initialTrace (Sum.inl state))
        atTop (nhds (∑ state, limitPath.initialTrace (Sum.inl state))) :=
      tendsto_finsetSum Finset.univ fun state _ => hInitialCoordinateTendsto (Sum.inl state)
    exact eq_of_tendsto_of_forall_eq hSumTendsto fun sequenceIndex =>
      (hPaths sequenceIndex).initialDensityNormalized
  · intro state
    apply ge_of_tendsto' (hInitialCoordinateTendsto (Sum.inl state))
    exact fun sequenceIndex => (hPaths sequenceIndex).initialDensityNonnegative state
  · intro transition
    exact eq_of_tendsto_of_forall_eq (hInitialCoordinateTendsto (Sum.inr transition))
      fun sequenceIndex => (hPaths sequenceIndex).cumulativeFlowInitiallyZero transition
  · have hSumTendsto : Tendsto
        (fun sequenceIndex =>
          ∑ state, (paths sequenceIndex).terminalTrace hDuration (Sum.inl state))
        atTop
        (nhds (∑ state, limitPath.terminalTrace hDuration (Sum.inl state))) :=
      tendsto_finsetSum Finset.univ fun state _ => hTerminalCoordinateTendsto (Sum.inl state)
    exact eq_of_tendsto_of_forall_eq hSumTendsto fun sequenceIndex =>
      (hPaths sequenceIndex).terminalDensityNormalized
  · intro state
    apply ge_of_tendsto' (hTerminalCoordinateTendsto (Sum.inl state))
    exact fun sequenceIndex => (hPaths sequenceIndex).terminalDensityNonnegative state
  · intro transition
    apply ge_of_tendsto' (hTerminalCoordinateTendsto (Sum.inr transition))
    exact fun sequenceIndex =>
      (hPaths sequenceIndex).terminalCumulativeFlowNonnegative transition

end

end FiniteMarkovProcesses.InformationTheory
