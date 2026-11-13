/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVConstantTranslation
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVLinearCombination
public import FiniteMarkovProcesses.Probability.FiniteUniformPMF
public import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRepresentationDomain

/-!
# Uniform static Renger representation path

This module constructs the source-neutral admissible path with uniform density and zero cumulative
directional flow.  It is built on the existing hybrid carrier by zeroing any representation path
and translating only its density coordinates.  The construction supplies a coordinate-positive,
finite-action interior anchor without introducing a new microscopic source.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] [Nonempty State]
  {duration : ℝ}

/-- Coordinate vector with the uniform probability density and zero cumulative flow. -/
noncomputable def rengerDirectionalFlowHybridBVUniformDensityVector :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
      (fun coordinate => Sum.elim
        (fun state => (finiteUniformPMF State state).toReal)
        (fun _transition => 0) coordinate)

omit [DecidableEq State] in
/-- The uniform vector evaluates to the uniform PMF on density coordinates. -/
@[simp]
theorem rengerDirectionalFlowHybridBVUniformDensityVector_density (state : State) :
    rengerDirectionalFlowHybridBVUniformDensityVector (State := State) (Sum.inl state) =
      (finiteUniformPMF State state).toReal := by
  simp [rengerDirectionalFlowHybridBVUniformDensityVector]

/-- The uniform vector vanishes on cumulative-flow coordinates. -/
@[simp]
theorem rengerDirectionalFlowHybridBVUniformDensityVector_flow
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVUniformDensityVector (State := State) (Sum.inr transition) =
      0 := by
  simp [rengerDirectionalFlowHybridBVUniformDensityVector]

omit [DecidableEq State] in
/-- The real uniform density coordinates sum to one. -/
theorem sum_rengerDirectionalFlowHybridBVUniformDensityVector_density :
    ∑ state : State, (finiteUniformPMF State state).toReal = 1 := by
  rw [← ENNReal.toReal_sum
    (fun state _hState => (finiteUniformPMF State).apply_ne_top state)]
  rw [show ∑ state : State, finiteUniformPMF State state = 1 by
    simpa only [tsum_fintype] using (finiteUniformPMF State).tsum_coe]
  simp

/-- Static uniform density and zero cumulative flow on the exact hybrid carrier. -/
noncomputable def rengerDirectionalFlowHybridBVUniformStaticPath
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    RengerDirectionalFlowHybridBVPath State duration :=
  (FiniteIntervalHybridBVPath.linearCombination 0 0 path path).constantTranslate
    rengerDirectionalFlowHybridBVUniformDensityVector

/-- The static path has the uniform density at every physical half-open time. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_densityValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityValue
        (rengerDirectionalFlowHybridBVUniformStaticPath path) time state =
      (finiteUniformPMF State state).toReal := by
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_cadlagRepresentative_eq _ _ hTime,
    FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq _ _ _ _ hTime]
  simp

/-- The static path has zero cumulative directional flow at every physical half-open time. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_cumulativeFlowValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVCumulativeFlowValue
        (rengerDirectionalFlowHybridBVUniformStaticPath path) time transition = 0 := by
  unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_cadlagRepresentative_eq _ _ hTime,
    FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq _ _ _ _ hTime]
  simp

/-- Every carried derivative of the static path is the zero signed measure. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_derivative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).toDerivativePath.derivative coordinate =
      VagueSignedMeasure.ofSignedMeasure (0 : SignedMeasure ℝ) := by
  unfold rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_derivative,
    FiniteIntervalHybridBVPath.linearCombination_derivative]
  simp

/-- Every Radon--Nikodym derivative density of the static path vanishes. -/
@[simp]
theorem rengerDirectionalFlowHybridBVUniformStaticPath_derivativeDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).derivativeDensity coordinate = 0 := by
  unfold FiniteIntervalHybridBVPath.derivativeDensity
  rw [rengerDirectionalFlowHybridBVUniformStaticPath_derivative]
  funext time
  simp [SignedMeasure.rnDeriv_def, SignedMeasure.toJordanDecomposition_zero]

/-- The recovered initial density of the static path is the uniform PMF. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_initialDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) (state : State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).initialTrace (Sum.inl state) =
      (finiteUniformPMF State state).toReal := by
  unfold rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_initialTrace _ _ hDuration,
    FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
  simp

/-- Every recovered initial cumulative flow of the static path is zero. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_initialCumulativeFlow
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).initialTrace
        (Sum.inr transition) = 0 := by
  unfold rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_initialTrace _ _ hDuration,
    FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
  simp

/-- The recovered terminal left density of the static path is the uniform PMF. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_terminalDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) (state : State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).terminalTrace hDuration
        (Sum.inl state) =
      (finiteUniformPMF State state).toReal := by
  unfold rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_terminalTrace _ _ hDuration,
    FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
  simp

/-- Every recovered terminal cumulative flow of the static path is zero. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_terminalCumulativeFlow
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (rengerDirectionalFlowHybridBVUniformStaticPath path).terminalTrace hDuration
        (Sum.inr transition) = 0 := by
  unfold rengerDirectionalFlowHybridBVUniformStaticPath
  rw [FiniteIntervalHybridBVPath.constantTranslate_terminalTrace _ _ hDuration,
    FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
  simp

/-- The uniform static path is a genuine admissible representation path. -/
noncomputable def rengerDirectionalFlowHybridBVUniformStaticRepresentationPath
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration := by
  let staticPath := rengerDirectionalFlowHybridBVUniformStaticPath path.1
  refine ⟨staticPath, ?_⟩
  refine
    { absolutelyContinuousDerivative := ?_
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
  · intro coordinate
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_derivative]
    exact VectorMeasure.AbsolutelyContinuous.zero _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro state
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_densityValue path.1
        ⟨hTime.1.le, hTime.2⟩ state]
    exact ENNReal.toReal_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl]
    simp_rw [rengerDirectionalFlowHybridBVUniformStaticPath_densityValue path.1
      ⟨hTime.1.le, hTime.2⟩]
    exact sum_rengerDirectionalFlowHybridBVUniformDensityVector_density
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    intro transition
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_cumulativeFlowValue path.1
        ⟨hTime.1.le, hTime.2⟩ transition]
  · exact Filter.Eventually.of_forall fun _time transition => by
      rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl]
      simp [rengerDirectionalFlowHybridBVFlowDerivative]
  · exact Filter.Eventually.of_forall fun _time state => by
      rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl]
      simp [rengerDirectionalFlowHybridBVDensityDerivative,
        rengerDirectionalFlowHybridBVFlowDerivative]
  · rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl]
    simp_rw [rengerDirectionalFlowHybridBVUniformStaticPath_initialDensity path.1 hDuration]
    exact sum_rengerDirectionalFlowHybridBVUniformDensityVector_density
  · intro state
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_initialDensity path.1 hDuration state]
    exact ENNReal.toReal_nonneg
  · intro transition
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_initialCumulativeFlow
        path.1 hDuration transition]
  · rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl]
    simp_rw [rengerDirectionalFlowHybridBVUniformStaticPath_terminalDensity path.1 hDuration]
    exact sum_rengerDirectionalFlowHybridBVUniformDensityVector_density
  · intro state
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_terminalDensity path.1 hDuration state]
    exact ENNReal.toReal_nonneg
  · intro transition
    rw [show staticPath = rengerDirectionalFlowHybridBVUniformStaticPath path.1 by rfl,
      rengerDirectionalFlowHybridBVUniformStaticPath_terminalCumulativeFlow
        path.1 hDuration transition]

/-- Every recovered initial density coordinate of the static anchor is strictly positive. -/
theorem rengerDirectionalFlowHybridBVUniformStaticRepresentationPath_initialDensity_pos
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (state : State) :
    0 < rengerDirectionalFlowHybridBVInitialDensity
      (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1 state := by
  unfold rengerDirectionalFlowHybridBVInitialDensity
  change 0 < Real.toNNReal
    ((rengerDirectionalFlowHybridBVUniformStaticPath path.1).initialTrace (Sum.inl state))
  rw [rengerDirectionalFlowHybridBVUniformStaticPath_initialDensity path.1 hDuration state]
  simpa [finiteUniformPMF_apply] using (Fintype.card_pos : 0 < Fintype.card State)

/-- The nonnegative density coordinate of the static path is the uniform PMF coordinate. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_densityAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityAt
        (rengerDirectionalFlowHybridBVUniformStaticPath path) time state =
      (finiteUniformPMF State state).toNNReal := by
  unfold rengerDirectionalFlowHybridBVDensityAt
  rw [rengerDirectionalFlowHybridBVUniformStaticPath_densityValue path hTime state]
  exact ENNReal.toNNReal_toReal_eq _

/-- Every nonnegative instantaneous directional-flow coordinate of the static path is zero. -/
@[simp]
theorem rengerDirectionalFlowHybridBVUniformStaticPath_flowDerivativeAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVFlowDerivativeAt
        (rengerDirectionalFlowHybridBVUniformStaticPath path) time transition = 0 := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
    rengerDirectionalFlowHybridBVFlowDerivative
  rw [rengerDirectionalFlowHybridBVUniformStaticPath_derivativeDensity]
  simp

/-- The static local action is exactly its uniform expected total jump intensity. -/
theorem rengerDirectionalFlowHybridBVUniformStaticPath_localRate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt
          (rengerDirectionalFlowHybridBVUniformStaticPath path) time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt
          (rengerDirectionalFlowHybridBVUniformStaticPath path) time) =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ((finiteUniformPMF State transition.val.1).toNNReal : ENNReal) *
          generator.rate transition.val.1 transition.val.2 := by
  unfold rengerDirectionalFlowLocalRateRaw
  apply Finset.sum_congr rfl
  intro transition _hTransition
  rw [rengerDirectionalFlowHybridBVUniformStaticPath_flowDerivativeAt,
    rengerDirectionalFlowHybridBVUniformStaticPath_densityAt path hTime,
    rengerExtendedPoissonRateCost_zero_left]
  rfl

/-- The complete dynamic action of the uniform static anchor is finite. -/
theorem rengerDirectionalFlowHybridBVUniformStaticRepresentationPath_dynamicRate_ne_top
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1 ≠ ⊤ := by
  rw [rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible generator hDuration
    (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).2]
  have hLocal : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt
            (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt
            (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1 time) =
        ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ((finiteUniformPMF State transition.val.1).toNNReal : ENNReal) *
            generator.rate transition.val.1 transition.val.2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    exact rengerDirectionalFlowHybridBVUniformStaticPath_localRate
      generator path.1 ⟨hTime.1.le, hTime.2⟩
  apply ne_of_lt
  rw [lintegral_congr_ae hLocal, lintegral_const,
    finiteOpenIntervalVolume_apply_univ]
  exact ENNReal.mul_lt_top
    (ENNReal.sum_lt_top.2 fun _transition _hTransition =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)
    ENNReal.ofReal_lt_top

end

end FiniteMarkovProcesses.InformationTheory
