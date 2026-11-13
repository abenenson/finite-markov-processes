/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVExtendedDualSupport
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVSourceKinematicSupport
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation

/-!
# Classification of Renger source-kinematic support

On source-kinematic support, failure of finite-rate admissibility has only two relevant forms:
a positive singular ordered-flow derivative, or a positive recovered initial cumulative-flow
offset.  The first already has infinite ambient dual cost; the second is the separately controlled
initial-boundary escape sector.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

private theorem finiteCoordinateL1Value_coordinate_continuousWithinAt
    {Coordinate : Type*}
    {Domain : Type*} [TopologicalSpace Domain]
    {values : Domain → FiniteCoordinateL1Value Coordinate}
    {set : Set Domain} {point : Domain}
    (hContinuous : ContinuousWithinAt values set point) (coordinate : Coordinate) :
    ContinuousWithinAt (fun domainPoint => values domainPoint coordinate) set point := by
  have hProjection :=
    (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).continuous
      |>.continuousAt.comp_continuousWithinAt hContinuous
  simpa only [Function.comp_def, PiLp.proj_apply] using! hProjection

private theorem finiteCoordinateL1Value_coordinate_tendsto
    {Coordinate : Type*}
    {Source : Type*} {sourceFilter : Filter Source}
    {values : Source → FiniteCoordinateL1Value Coordinate}
    {limit : FiniteCoordinateL1Value Coordinate}
    (hTendsto : Tendsto values sourceFilter (nhds limit)) (coordinate : Coordinate) :
    Tendsto (fun source => values source coordinate)
      sourceFilter (nhds (limit coordinate)) := by
  have hProjection :=
    (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).continuous
      |>.continuousAt.tendsto.comp hTendsto
  simpa only [Function.comp_def, PiLp.proj_apply] using! hProjection

/-- Source support makes every density coordinate nonnegative at each physical half-open time,
including the recovered initial trace. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.densityValueNonnegative
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (time : ℝ) (hTime : time ∈ Ico 0 duration) (state : State) :
    0 ≤ rengerDirectionalFlowHybridBVDensityValue path time state := by
  let value : ℝ → ℝ := fun point =>
    rengerDirectionalFlowHybridBVDensityValue path point state
  let clamped : ℝ → ℝ := fun point => max (value point) 0
  have hValueRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt value (Ici point) point := by
    intro point hPoint
    exact finiteCoordinateL1Value_coordinate_continuousWithinAt
      (path.cadlagRepresentative.rightContinuous point hPoint) (Sum.inl state)
  have hClampedRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt clamped (Ici point) point := by
    intro point hPoint
    exact (hValueRight point hPoint).max continuousWithinAt_const
  have hEventually : value =ᵐ[finiteOpenIntervalVolume duration] clamped :=
    support.densityNonnegativeAE.mono fun point hPoint => by
      unfold value clamped
      rw [max_eq_left (hPoint state)]
  have hEquality :=
    FiniteIntervalCadlagRepresentative.eqOn_Ico_of_rightContinuous_of_ae_eq
      hValueRight hClampedRight hEventually hTime
  unfold clamped at hEquality
  change 0 ≤ value time
  rw [hEquality]
  exact le_max_right _ _

/-- Source support makes the density sum exactly one at each physical half-open time. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.densityValueNormalized
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (time : ℝ) (hTime : time ∈ Ico 0 duration) :
    ∑ state, rengerDirectionalFlowHybridBVDensityValue path time state = 1 := by
  let value : ℝ → ℝ := fun point =>
    ∑ state, rengerDirectionalFlowHybridBVDensityValue path point state
  have hValueRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt value (Ici point) point := by
    intro point hPoint
    apply tendsto_finsetSum
    intro state _
    exact finiteCoordinateL1Value_coordinate_continuousWithinAt
      (path.cadlagRepresentative.rightContinuous point hPoint) (Sum.inl state)
  have hConstantRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt (fun _ : ℝ => (1 : ℝ)) (Ici point) point :=
    fun _ _ => continuousWithinAt_const
  exact FiniteIntervalCadlagRepresentative.eqOn_Ico_of_rightContinuous_of_ae_eq
    hValueRight hConstantRight support.densityNormalizedAE hTime

/-- Source support makes every cumulative ordered flow nonnegative at each physical half-open
time, including its recovered initial trace. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.cumulativeFlowValueNonnegative
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (time : ℝ) (hTime : time ∈ Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition := by
  let value : ℝ → ℝ := fun point =>
    rengerDirectionalFlowHybridBVCumulativeFlowValue path point transition
  let clamped : ℝ → ℝ := fun point => max (value point) 0
  have hValueRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt value (Ici point) point := by
    intro point hPoint
    exact finiteCoordinateL1Value_coordinate_continuousWithinAt
      (path.cadlagRepresentative.rightContinuous point hPoint) (Sum.inr transition)
  have hClampedRight : ∀ point ∈ Ico 0 duration,
      ContinuousWithinAt clamped (Ici point) point := by
    intro point hPoint
    exact (hValueRight point hPoint).max continuousWithinAt_const
  have hEventually : value =ᵐ[finiteOpenIntervalVolume duration] clamped :=
    support.cumulativeFlowNonnegativeAE.mono fun point hPoint => by
      unfold value clamped
      rw [max_eq_left (hPoint transition)]
  have hEquality :=
    FiniteIntervalCadlagRepresentative.eqOn_Ico_of_rightContinuous_of_ae_eq
      hValueRight hClampedRight hEventually hTime
  unfold clamped at hEquality
  change 0 ≤ value time
  rw [hEquality]
  exact le_max_right _ _

/-- If recovered initial cumulative flow is zero, source support supplies all value and boundary
fields of finite-rate admissibility. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.valueConstraintsOfInitialFlowZero
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (hInitialFlow : ∀ transition, path.initialTrace (Sum.inr transition) = 0) :
    RengerDirectionalFlowHybridBVValueConstraints path hDuration := by
  have hInitialTime : (0 : ℝ) ∈ Ico 0 duration := ⟨le_rfl, hDuration⟩
  have hTerminalCoordinateTendsto
      (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
      Tendsto
        (fun time => path.cadlagRepresentative.representative time coordinate)
        (nhdsWithin duration (Iio duration))
        (nhds (path.terminalTrace hDuration coordinate)) :=
    finiteCoordinateL1Value_coordinate_tendsto
      (path.cadlagRepresentative.tendsto_terminalTrace hDuration) coordinate
  have hEventuallyPhysical :
      ∀ᶠ time in nhdsWithin duration (Iio duration), time ∈ Ico 0 duration := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Ici_mem_nhds hDuration)] with
      time hUpper hLower
    exact ⟨hLower, hUpper⟩
  refine
    { densityNonnegativeAE := support.densityNonnegativeAE
      densityNormalizedAE := support.densityNormalizedAE
      cumulativeFlowNonnegativeAE := support.cumulativeFlowNonnegativeAE
      initialDensityNormalized := support.densityValueNormalized 0 hInitialTime
      initialDensityNonnegative := fun state =>
        support.densityValueNonnegative 0 hInitialTime state
      cumulativeFlowInitiallyZero := hInitialFlow
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · have hSumTendsto : Tendsto
        (fun time => ∑ state,
          path.cadlagRepresentative.representative time (Sum.inl state))
        (nhdsWithin duration (Iio duration))
        (nhds (∑ state, path.terminalTrace hDuration (Sum.inl state))) := by
      apply tendsto_finsetSum
      intro state _
      exact hTerminalCoordinateTendsto (Sum.inl state)
    apply tendsto_nhds_unique hSumTendsto
    exact tendsto_const_nhds.congr' <| hEventuallyPhysical.mono fun time hTime =>
      (support.densityValueNormalized time hTime).symm
  · intro state
    apply ge_of_tendsto (hTerminalCoordinateTendsto (Sum.inl state))
    exact hEventuallyPhysical.mono fun time hTime =>
      support.densityValueNonnegative time hTime state
  · intro transition
    apply ge_of_tendsto (hTerminalCoordinateTendsto (Sum.inr transition))
    exact hEventuallyPhysical.mono fun time hTime =>
      support.cumulativeFlowValueNonnegative time hTime transition

/-- Absolute continuity of every ordered-flow derivative and exact derivative continuity force
absolute continuity of every density derivative. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.densityDerivativeAbsolutelyContinuous
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (hFlowAbsolutelyContinuous : ∀ transition,
      MeasureTheory.VectorMeasure.AbsolutelyContinuous
        (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
        (finiteOpenIntervalVolume duration).toENNRealVectorMeasure)
    (state : State) :
    MeasureTheory.VectorMeasure.AbsolutelyContinuous
      (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
      (finiteOpenIntervalVolume duration).toENNRealVectorMeasure := by
  rw [support.derivativeContinuity state]
  apply MeasureTheory.VectorMeasure.AbsolutelyContinuous.sub
  · apply MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk
    intro event hEvent hEventZero
    rw [signedMeasure_fintypeSum_apply]
    apply Finset.sum_eq_zero
    intro source _
    exact hFlowAbsolutelyContinuous ⟨(source, state), source.property⟩ hEventZero
  · apply MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk
    intro event hEvent hEventZero
    rw [signedMeasure_fintypeSum_apply]
    apply Finset.sum_eq_zero
    intro target _
    exact hFlowAbsolutelyContinuous ⟨(state, target), target.property.symm⟩ hEventZero

/-- Source support with zero initial flow and absolutely continuous ordered flows is exactly
finite-rate admissible. -/
theorem RengerDirectionalFlowHybridBVSourceKinematicSupport.admissibleOfInitialFlowZeroOfFlowAC
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (hInitialFlow : ∀ transition, path.initialTrace (Sum.inr transition) = 0)
    (hFlowAbsolutelyContinuous : ∀ transition,
      MeasureTheory.VectorMeasure.AbsolutelyContinuous
        (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
        (finiteOpenIntervalVolume duration).toENNRealVectorMeasure) :
    RengerDirectionalFlowHybridBVAdmissible path hDuration := by
  classical
  have hValues := support.valueConstraintsOfInitialFlowZero hInitialFlow
  have hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative := by
    intro coordinate
    cases coordinate with
    | inl state =>
        exact support.densityDerivativeAbsolutelyContinuous
          hFlowAbsolutelyContinuous state
    | inr transition => exact hFlowAbsolutelyContinuous transition
  have hFlowDerivativeNonnegativeAE :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        ∀ transition,
          0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path time transition := by
    apply Filter.eventually_all.2
    intro transition
    exact MeasureTheory.SignedMeasure.rnDeriv_nonnegative_of_zero_le
      (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
      (finiteOpenIntervalVolume duration)
      (support.flowDerivativeMeasureNonnegative transition)
  have hContinuityEquationAE :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        ∀ state,
          rengerDirectionalFlowHybridBVDensityDerivative path time state =
            (∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(source, state), source.property⟩) -
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(state, target), target.property.symm⟩ := by
    apply Filter.eventually_all.2
    intro state
    let densityDerivative :=
      (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
    let incomingDerivative : MeasureTheory.SignedMeasure ℝ :=
      ∑ source : {source : State // source ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure
    let outgoingDerivative : MeasureTheory.SignedMeasure ℝ :=
      ∑ target : {target : State // target ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure
    have hDerivativeIdentity :
        densityDerivative = incomingDerivative - outgoingDerivative :=
      support.derivativeContinuity state
    have hDerivativeRNIdentity := congrArg
      (fun signedMeasure : MeasureTheory.SignedMeasure ℝ =>
        signedMeasure.rnDeriv (finiteOpenIntervalVolume duration))
      hDerivativeIdentity
    have hIncomingRN := MeasureTheory.SignedMeasure.rnDeriv_fintypeSum
      (fun source : {source : State // source ≠ state} =>
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure)
      (finiteOpenIntervalVolume duration)
    have hOutgoingRN := MeasureTheory.SignedMeasure.rnDeriv_fintypeSum
      (fun target : {target : State // target ≠ state} =>
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure)
      (finiteOpenIntervalVolume duration)
    have hSubRN := MeasureTheory.SignedMeasure.rnDeriv_sub
      incomingDerivative outgoingDerivative
      (finiteOpenIntervalVolume duration)
    filter_upwards [hIncomingRN, hOutgoingRN, hSubRN] with
      time hIncomingTime hOutgoingTime hSubTime
    change densityDerivative.rnDeriv (finiteOpenIntervalVolume duration) time =
      (∑ source : {source : State // source ≠ state},
        ((path.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure.rnDeriv
            (finiteOpenIntervalVolume duration) time)) -
      ∑ target : {target : State // target ≠ state},
        ((path.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure.rnDeriv
            (finiteOpenIntervalVolume duration) time)
    calc
      densityDerivative.rnDeriv (finiteOpenIntervalVolume duration) time =
          (incomingDerivative - outgoingDerivative).rnDeriv
            (finiteOpenIntervalVolume duration) time :=
        congrFun hDerivativeRNIdentity time
      _ = incomingDerivative.rnDeriv (finiteOpenIntervalVolume duration) time -
          outgoingDerivative.rnDeriv (finiteOpenIntervalVolume duration) time := hSubTime
      _ = _ := by rw [hIncomingTime, hOutgoingTime]
  exact
    { absolutelyContinuousDerivative := hAbsolutelyContinuous
      densityNonnegativeAE := hValues.densityNonnegativeAE
      densityNormalizedAE := hValues.densityNormalizedAE
      cumulativeFlowNonnegativeAE := hValues.cumulativeFlowNonnegativeAE
      flowDerivativeNonnegativeAE := hFlowDerivativeNonnegativeAE
      continuityEquationAE := hContinuityEquationAE
      initialDensityNormalized := hValues.initialDensityNormalized
      initialDensityNonnegative := hValues.initialDensityNonnegative
      cumulativeFlowInitiallyZero := hValues.cumulativeFlowInitiallyZero
      terminalDensityNormalized := hValues.terminalDensityNormalized
      terminalDensityNonnegative := hValues.terminalDensityNonnegative
      terminalCumulativeFlowNonnegative := hValues.terminalCumulativeFlowNonnegative }

namespace RengerDirectionalFlowHybridBVSourceKinematicSupport

/-- Exact source-support classification used by the complete upper bound: either the ambient
dual already equals the dynamic rate, or one recovered initial ordered-flow coordinate is
strictly positive. -/
theorem finiteRateOrSingularFlow_or_initialFlowPos
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (support : RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration) :
    RengerDirectionalFlowHybridBVFiniteRateOrSingularFlow path hDuration ∨
      ∃ transition : FiniteStateOrderedOffDiagonalTransition State,
        0 < path.initialTrace (Sum.inr transition) := by
  by_cases hInitialFlow : ∀ transition,
      path.initialTrace (Sum.inr transition) = 0
  · by_cases hFlowAbsolutelyContinuous : ∀ transition,
        MeasureTheory.VectorMeasure.AbsolutelyContinuous
          (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
          (finiteOpenIntervalVolume duration).toENNRealVectorMeasure
    · exact Or.inl <| Or.inl <|
        support.admissibleOfInitialFlowZeroOfFlowAC
          hInitialFlow hFlowAbsolutelyContinuous
    · push Not at hFlowAbsolutelyContinuous
      obtain ⟨transition, hSingular⟩ := hFlowAbsolutelyContinuous
      exact Or.inl <| Or.inr ⟨transition,
        support.flowDerivativeMeasureNonnegative transition,
        support.densityNonnegativeAE.mono fun _ hTime => hTime transition.1.1,
        hSingular⟩
  · push Not at hInitialFlow
    obtain ⟨transition, hNonzero⟩ := hInitialFlow
    exact Or.inr ⟨transition, lt_of_le_of_ne
      (support.cumulativeFlowValueNonnegative 0 ⟨le_rfl, hDuration⟩ transition)
      (Ne.symm hNonzero)⟩

end RengerDirectionalFlowHybridBVSourceKinematicSupport

end

end FiniteMarkovProcesses.InformationTheory
