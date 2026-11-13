/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVValueConstraintClosure

/-!
# Kinematic closure for Renger hybrid paths

This module closes the finite-state continuity law under bounded-rate hybrid convergence.  On an
admissible path, the almost-everywhere derivative equation first yields an exact signed-measure
identity and hence the integrated density--cumulative-flow balance.  That balance survives the
strong-`L1` representative subsequence and recovered initial-trace convergence.  Right continuity
then promotes the limiting almost-everywhere identity to the whole physical half-open interval,
and finite-interval signed-measure extensionality recovers the limiting derivative equation.

Absolute continuity and nonnegativity of the limiting instantaneous flow remain separate gates.

## Main declarations

* `RengerDirectionalFlowHybridBVKinematicConstraints` collects the closed value and
  signed-measure continuity sectors.
* `rengerDirectionalFlowHybridBVKinematicConstraints_of_tendsto_of_uniformlyBoundedDynamicRate`
  proves their preservation under bounded-rate hybrid convergence.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The exact signed-measure continuity equation carried by one Renger hybrid path. -/
def RengerDirectionalFlowHybridBVDerivativeContinuity
    (path : RengerDirectionalFlowHybridBVPath State duration) : Prop :=
  ∀ state,
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure =
      (∑ source : {source : State // source ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure) -
      ∑ target : {target : State // target ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure

/-- The integrated density--cumulative-flow continuity law on the physical half-open interval. -/
def RengerDirectionalFlowHybridBVIntegratedContinuity
    (path : RengerDirectionalFlowHybridBVPath State duration) : Prop :=
  ∀ state time, time ∈ Ico 0 duration →
    rengerDirectionalFlowHybridBVDensityValue path time state =
      path.initialTrace (Sum.inl state) +
        (∑ source : {source : State // source ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue path time
            ⟨(source, state), source.property⟩) -
        ∑ target : {target : State // target ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue path time
            ⟨(state, target), target.property.symm⟩

/-- The value and signed-measure conservation sectors of the finite-rate representation domain. -/
structure RengerDirectionalFlowHybridBVKinematicConstraints
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) : Prop where
  /-- Open-interval and recovered-boundary value constraints. -/
  valueConstraints : RengerDirectionalFlowHybridBVValueConstraints path hDuration
  /-- Exact continuity of the carried signed derivative measures. -/
  derivativeContinuity : RengerDirectionalFlowHybridBVDerivativeContinuity path

/-- Evaluation of a finite sum of signed measures is the sum of their evaluations. -/
theorem signedMeasure_fintypeSum_apply
    {Index : Type*} [Fintype Index]
    (measures : Index → SignedMeasure ℝ) (event : Set ℝ) :
    (∑ index, measures index) event = ∑ index, measures index event := by
  classical
  let evaluation : SignedMeasure ℝ →+ ℝ :=
    { toFun := fun measure => measure event
      map_zero' := _root_.zero_apply event
      map_add' := fun first second => _root_.add_apply first second event }
  exact map_sum evaluation measures Finset.univ

/-- The almost-everywhere derivative continuity equation on an admissible path is equivalent to
an exact identity of its absolutely continuous signed derivative measures. -/
theorem rengerDirectionalFlowHybridBVDerivativeContinuity_of_admissible
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (admissible : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    RengerDirectionalFlowHybridBVDerivativeContinuity path := by
  classical
  intro state
  apply VectorMeasure.ext
  intro event hEvent
  rw [← path.withDensity_derivativeDensity_eq_derivative
    admissible.absolutelyContinuousDerivative (Sum.inl state)]
  simp_rw [← path.withDensity_derivativeDensity_eq_derivative
    admissible.absolutelyContinuousDerivative (Sum.inr _)]
  rw [_root_.sub_apply, signedMeasure_fintypeSum_apply,
    signedMeasure_fintypeSum_apply]
  unfold FiniteIntervalHybridBVPath.derivativeDensity
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hEvent]
  simp_rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hEvent]
  have hIncomingIntegrable : Integrable
      (fun time =>
        ∑ source : {source : State // source ≠ state},
          rengerDirectionalFlowHybridBVFlowDerivative path time
            ⟨(source, state), source.property⟩)
      (finiteOpenIntervalVolume duration) := by
    apply integrable_finsetSum
    intro source _
    exact SignedMeasure.integrable_rnDeriv _ _
  have hOutgoingIntegrable : Integrable
      (fun time =>
        ∑ target : {target : State // target ≠ state},
          rengerDirectionalFlowHybridBVFlowDerivative path time
            ⟨(state, target), target.property.symm⟩)
      (finiteOpenIntervalVolume duration) := by
    apply integrable_finsetSum
    intro target _
    exact SignedMeasure.integrable_rnDeriv _ _
  calc
    ∫ time in event,
        rengerDirectionalFlowHybridBVDensityDerivative path time state
        ∂finiteOpenIntervalVolume duration =
      ∫ time in event,
        ((∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩) -
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩)
        ∂finiteOpenIntervalVolume duration := by
      apply integral_congr_ae
      exact ae_restrict_of_ae <| admissible.continuityEquationAE.mono
        fun time hTime => hTime state
    _ = (∫ time in event,
          ∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩
          ∂finiteOpenIntervalVolume duration) -
        ∫ time in event,
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩
          ∂finiteOpenIntervalVolume duration :=
      integral_sub hIncomingIntegrable.integrableOn hOutgoingIntegrable.integrableOn
    _ = (∑ source : {source : State // source ≠ state},
          ∫ time in event,
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩
            ∂finiteOpenIntervalVolume duration) -
        ∑ target : {target : State // target ≠ state},
          ∫ time in event,
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩
            ∂finiteOpenIntervalVolume duration := by
      rw [integral_finsetSum, integral_finsetSum]
      · intro source _
        exact (SignedMeasure.integrable_rnDeriv _ _).integrableOn
      · intro target _
        exact (SignedMeasure.integrable_rnDeriv _ _).integrableOn

/-- Exact derivative continuity integrates to the density--cumulative-flow balance when the
initial cumulative flow is zero. -/
theorem rengerDirectionalFlowHybridBVIntegratedContinuity_of_admissible
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (admissible : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    RengerDirectionalFlowHybridBVIntegratedContinuity path := by
  classical
  intro state time hTime
  have hMeasure := congrArg (fun measure : SignedMeasure ℝ => measure (Ioc 0 time))
    (rengerDirectionalFlowHybridBVDerivativeContinuity_of_admissible admissible state)
  rw [_root_.sub_apply, signedMeasure_fintypeSum_apply,
    signedMeasure_fintypeSum_apply] at hMeasure
  simp_rw [path.derivative_apply_Ioc_eq_cadlagRepresentative_sub _
    le_rfl hTime.1 hTime.2] at hMeasure
  change path.cadlagRepresentative.representative time (Sum.inl state) =
    path.cadlagRepresentative.representative 0 (Sum.inl state) +
      (∑ source : {source : State // source ≠ state},
        path.cadlagRepresentative.representative time
          (Sum.inr ⟨(source, state), source.property⟩)) -
      ∑ target : {target : State // target ≠ state},
        path.cadlagRepresentative.representative time
          (Sum.inr ⟨(state, target), target.property.symm⟩)
  change path.cadlagRepresentative.representative time (Sum.inl state) -
      path.cadlagRepresentative.representative 0 (Sum.inl state) = _ at hMeasure
  have hInitialFlow (transition : FiniteStateOrderedOffDiagonalTransition State) :
      path.cadlagRepresentative.representative 0 (Sum.inr transition) = 0 :=
    admissible.cumulativeFlowInitiallyZero transition
  simp_rw [hInitialFlow] at hMeasure
  simp only [sub_zero] at hMeasure
  linarith

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
  simpa only [Function.comp_def, PiLp.proj_apply] using! hProjection

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

/-- An integrated continuity law determines the exact continuity identity of the supported
signed derivative measures. -/
theorem rengerDirectionalFlowHybridBVDerivativeContinuity_of_integratedContinuity
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hContinuity : RengerDirectionalFlowHybridBVIntegratedContinuity path) :
    RengerDirectionalFlowHybridBVDerivativeContinuity path := by
  classical
  intro state
  let densityDerivative :=
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
  let flowDerivative : FiniteStateOrderedOffDiagonalTransition State → SignedMeasure ℝ :=
    fun transition =>
      (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
  let balanceDerivative : SignedMeasure ℝ :=
    (∑ source : {source : State // source ≠ state},
      flowDerivative ⟨(source, state), source.property⟩) -
    ∑ target : {target : State // target ≠ state},
      flowDerivative ⟨(state, target), target.property.symm⟩
  have hDensitySupport : densityDerivative.restrict (Ioo 0 duration) = densityDerivative :=
    (Classical.choose_spec path.hasCadlagDerivativeRealization).1 (Sum.inl state)
  have hFlowSupport (transition : FiniteStateOrderedOffDiagonalTransition State) :
      (flowDerivative transition).restrict (Ioo 0 duration) = flowDerivative transition :=
    (Classical.choose_spec path.hasCadlagDerivativeRealization).1 (Sum.inr transition)
  have hBalanceSupport : balanceDerivative.restrict (Ioo 0 duration) = balanceDerivative := by
    dsimp only [balanceDerivative]
    change (VectorMeasure.restrictGm (Ioo 0 duration))
        ((∑ source : {source : State // source ≠ state},
          flowDerivative ⟨(source, state), source.property⟩) -
        ∑ target : {target : State // target ≠ state},
          flowDerivative ⟨(state, target), target.property.symm⟩) = _
    rw [map_sub, map_sum, map_sum]
    simp_rw [VectorMeasure.restrictGm_apply, hFlowSupport]
  apply signedMeasure_eq_of_apply_Ioc_eq_of_restrict_openInterval
    densityDerivative balanceDerivative hDensitySupport hBalanceSupport
  intro start finish hStart hOrder hFinish
  have hStartMembership : start ∈ Ico 0 duration :=
    ⟨hStart, hOrder.trans_lt hFinish⟩
  have hFinishMembership : finish ∈ Ico 0 duration :=
    ⟨hStart.trans hOrder, hFinish⟩
  have hStartContinuity := hContinuity state start hStartMembership
  have hFinishContinuity := hContinuity state finish hFinishMembership
  change
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
        (Ioc start finish) = _
  rw [path.derivative_apply_Ioc_eq_cadlagRepresentative_sub (Sum.inl state)
      hStart hOrder hFinish]
  dsimp only [balanceDerivative, flowDerivative]
  rw [_root_.sub_apply, signedMeasure_fintypeSum_apply,
    signedMeasure_fintypeSum_apply]
  simp_rw [path.derivative_apply_Ioc_eq_cadlagRepresentative_sub (Sum.inr _)
    hStart hOrder hFinish]
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVCumulativeFlowValue at hStartContinuity hFinishContinuity
  simp only [Finset.sum_sub_distrib]
  linarith

/-- Bounded-rate hybrid convergence preserves the integrated continuity law and therefore the
exact signed-measure conservation equation. -/
theorem
    rengerDirectionalFlowHybridBVKinematicConstraints_of_tendsto_of_uniformlyBoundedDynamicRate
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
    RengerDirectionalFlowHybridBVKinematicConstraints limitPath hDuration := by
  classical
  have hL1Tendsto := (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).1
  obtain ⟨subsequence, _hSubsequenceMonotone, hRepresentativeTendsto⟩ :=
    exists_subsequence_tendsto_cadlagRepresentative_ae_of_tendsto_toL1Path
      paths limitPath hL1Tendsto
  have hInitialTendsto :=
    rengerDirectionalFlowHybridBVTendstoInitialTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hL1Tendsto
  have hInitialCoordinateTendsto :=
    finiteCoordinateL1Value_coordinate_tendsto hInitialTendsto
  have hSequenceContinuity (sequenceIndex : ℕ) :=
    rengerDirectionalFlowHybridBVIntegratedContinuity_of_admissible
      (hPaths sequenceIndex)
  have hLimitContinuityAE :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ state,
        rengerDirectionalFlowHybridBVDensityValue limitPath time state =
          limitPath.initialTrace (Sum.inl state) +
            (∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
                ⟨(source, state), source.property⟩) -
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
                ⟨(state, target), target.property.symm⟩ := by
    filter_upwards [hRepresentativeTendsto,
      ae_restrict_mem measurableSet_Ioo] with time hTimeTendsto hTime
    intro state
    have hCoordinateTendsto :=
      finiteCoordinateL1Value_coordinate_tendsto hTimeTendsto
    have hIncomingTendsto : Tendsto
        (fun sequenceIndex =>
          ∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVCumulativeFlowValue
              (paths (subsequence sequenceIndex)) time
              ⟨(source, state), source.property⟩)
        atTop
        (nhds (∑ source : {source : State // source ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
            ⟨(source, state), source.property⟩)) := by
      apply tendsto_finsetSum
      intro source _
      simpa only [rengerDirectionalFlowHybridBVCumulativeFlowValue] using
        hCoordinateTendsto (Sum.inr ⟨(source, state), source.property⟩)
    have hOutgoingTendsto : Tendsto
        (fun sequenceIndex =>
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVCumulativeFlowValue
              (paths (subsequence sequenceIndex)) time
              ⟨(state, target), target.property.symm⟩)
        atTop
        (nhds (∑ target : {target : State // target ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
            ⟨(state, target), target.property.symm⟩)) := by
      apply tendsto_finsetSum
      intro target _
      simpa only [rengerDirectionalFlowHybridBVCumulativeFlowValue] using
        hCoordinateTendsto (Sum.inr ⟨(state, target), target.property.symm⟩)
    have hLeftTendsto : Tendsto
        (fun sequenceIndex =>
          rengerDirectionalFlowHybridBVDensityValue
            (paths (subsequence sequenceIndex)) time state)
        atTop
        (nhds (rengerDirectionalFlowHybridBVDensityValue limitPath time state)) := by
      simpa only [rengerDirectionalFlowHybridBVDensityValue] using
        hCoordinateTendsto (Sum.inl state)
    have hRightTendsto :=
      (hInitialCoordinateTendsto (Sum.inl state)).comp
          _hSubsequenceMonotone.tendsto_atTop
        |>.add hIncomingTendsto |>.sub hOutgoingTendsto
    apply tendsto_nhds_unique hLeftTendsto
    apply hRightTendsto.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex =>
      (hSequenceContinuity (subsequence sequenceIndex) state time
        ⟨hTime.1.le, hTime.2⟩).symm
  have hLimitIntegratedContinuity :
      RengerDirectionalFlowHybridBVIntegratedContinuity limitPath := by
    intro state
    let density : ℝ → ℝ := fun time =>
      rengerDirectionalFlowHybridBVDensityValue limitPath time state
    let balance : ℝ → ℝ := fun time =>
      limitPath.initialTrace (Sum.inl state) +
        (∑ source : {source : State // source ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
            ⟨(source, state), source.property⟩) -
        ∑ target : {target : State // target ≠ state},
          rengerDirectionalFlowHybridBVCumulativeFlowValue limitPath time
            ⟨(state, target), target.property.symm⟩
    have hDensityRight : ∀ time ∈ Ico 0 duration,
        ContinuousWithinAt density (Ici time) time := by
      intro time hTime
      unfold density rengerDirectionalFlowHybridBVDensityValue
      exact finiteCoordinateL1Value_coordinate_continuousWithinAt
        (limitPath.cadlagRepresentative.rightContinuous time hTime) (Sum.inl state)
    have hBalanceRight : ∀ time ∈ Ico 0 duration,
        ContinuousWithinAt balance (Ici time) time := by
      intro time hTime
      unfold balance rengerDirectionalFlowHybridBVCumulativeFlowValue
      have hCoordinateRight (coordinate :
          State ⊕ FiniteStateOrderedOffDiagonalTransition State) :
          ContinuousWithinAt
            (fun point => limitPath.cadlagRepresentative.representative point coordinate)
            (Ici time) time :=
        finiteCoordinateL1Value_coordinate_continuousWithinAt
          (limitPath.cadlagRepresentative.rightContinuous time hTime) coordinate
      have hIncomingRight : ContinuousWithinAt
          (fun point =>
            ∑ source : {source : State // source ≠ state},
              limitPath.cadlagRepresentative.representative point
                (Sum.inr ⟨(source, state), source.property⟩))
          (Ici time) time := by
        apply tendsto_finsetSum
        intro source _
        exact hCoordinateRight (Sum.inr ⟨(source, state), source.property⟩)
      have hOutgoingRight : ContinuousWithinAt
          (fun point =>
            ∑ target : {target : State // target ≠ state},
              limitPath.cadlagRepresentative.representative point
                (Sum.inr ⟨(state, target), target.property.symm⟩))
          (Ici time) time := by
        apply tendsto_finsetSum
        intro target _
        exact hCoordinateRight (Sum.inr ⟨(state, target), target.property.symm⟩)
      exact (continuousWithinAt_const.add hIncomingRight).sub hOutgoingRight
    have hEventually : density =ᵐ[finiteOpenIntervalVolume duration] balance :=
      hLimitContinuityAE.mono fun time hTime => hTime state
    exact FiniteIntervalCadlagRepresentative.eqOn_Ico_of_rightContinuous_of_ae_eq
      hDensityRight hBalanceRight hEventually
  exact
    { valueConstraints :=
        rengerDirectionalFlowHybridBVValueConstraints_of_tendsto_of_uniformlyBoundedDynamicRate
          generator hDuration paths limitPath hPaths hLevel hRates hTendsto
      derivativeContinuity :=
        rengerDirectionalFlowHybridBVDerivativeContinuity_of_integratedContinuity
          hLimitIntegratedContinuity }

end

end FiniteMarkovProcesses.InformationTheory
