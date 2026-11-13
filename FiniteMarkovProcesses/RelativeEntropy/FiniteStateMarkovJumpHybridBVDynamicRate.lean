/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateJumpDirectionalFlowLDPBoundary
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryHybridBVObservation

/-!
# Hybrid-BV dynamic directional-flow rate for finite-state jump processes

This module instantiates the published density--directional-flow action on the genuine hybrid
bounded-variation carrier.  Path values come from a selected càdlàg representative of the strong
`L1` class, boundary values come from separately recovered traces, and time derivatives come from
the Radon--Nikodym densities of the carried signed derivative measures.

Finite-rate admissibility is deliberately stricter than carrier membership: all coordinate
derivatives must be absolutely continuous, density values must remain in the simplex, cumulative
and instantaneous ordered flows must be nonnegative, cumulative flow starts at zero, and the
distributional continuity equation holds almost everywhere.  Thus finite empirical observations,
whose derivatives are generally atomic, live measurably in the same carrier without being
misclassified as finite-action limit paths.

No compact-sublevel or large-deviation theorem is asserted here.

## Main declarations

- `RengerDirectionalFlowHybridBVPath`: the exact finite-state hybrid carrier.
- `RengerDirectionalFlowHybridBVAdmissible`: the finite-rate physical and continuity domain.
- `rengerDirectionalFlowHybridBVDynamicRateData`: the dynamic path-rate data with explicit
  zero initial and boundary sectors.
- `rengerDirectionalFlowHybridBVDynamicRate`: the continuity-gated dynamic action.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The exact hybrid bounded-variation carrier for a finite-state empirical density and every
ordered off-diagonal cumulative flow coordinate. -/
abbrev RengerDirectionalFlowHybridBVPath (State : Type u)
    [Fintype State] [DecidableEq State] (duration : ℝ) :=
  FiniteIntervalHybridBVPath
    (EmpiricalDensityDirectionalFlowCoordinate State) duration

/-- Raw density coordinate of the selected càdlàg representative. -/
noncomputable def rengerDirectionalFlowHybridBVDensityValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (state : State) : ℝ :=
  path.cadlagRepresentative.representative time (Sum.inl state)

/-- Raw cumulative ordered-flow coordinate of the selected càdlàg representative. -/
noncomputable def rengerDirectionalFlowHybridBVCumulativeFlowValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State) : ℝ :=
  path.cadlagRepresentative.representative time (Sum.inr transition)

/-- Radon--Nikodym time derivative of one density coordinate. -/
noncomputable def rengerDirectionalFlowHybridBVDensityDerivative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (state : State) : ℝ :=
  path.derivativeDensity (Sum.inl state) time

/-- Radon--Nikodym time derivative of one cumulative ordered-flow coordinate. -/
noncomputable def rengerDirectionalFlowHybridBVFlowDerivative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State) : ℝ :=
  path.derivativeDensity (Sum.inr transition) time

/-- Nonnegative density coordinates supplied to the local rate.  On the admissible domain the
`ofReal` coercion loses no information almost everywhere. -/
noncomputable def rengerDirectionalFlowHybridBVDensityAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (state : State) : NNReal :=
  Real.toNNReal (rengerDirectionalFlowHybridBVDensityValue path time state)

/-- Nonnegative instantaneous ordered-flow coordinates supplied to the local rate.  On the
admissible domain the `ofReal` coercion loses no information almost everywhere. -/
noncomputable def rengerDirectionalFlowHybridBVFlowDerivativeAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (transition : FiniteStateOrderedOffDiagonalTransition State) : NNReal :=
  Real.toNNReal (rengerDirectionalFlowHybridBVFlowDerivative path time transition)

/-- Density coordinate of the separately recovered initial trace. -/
noncomputable def rengerDirectionalFlowHybridBVInitialDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (state : State) : NNReal :=
  Real.toNNReal (path.initialTrace (Sum.inl state))

/-- Density coordinate of the separately recovered terminal left trace. -/
noncomputable def rengerDirectionalFlowHybridBVTerminalDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) (state : State) : NNReal :=
  Real.toNNReal (path.terminalTrace hDuration (Sum.inl state))

/-- Finite-rate physical and continuity constraints on one hybrid path.  The pointwise carrier
constraints are imposed almost everywhere on the open physical interval, while both boundary
traces are checked separately. -/
structure RengerDirectionalFlowHybridBVAdmissible
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) : Prop where
  /-- Every carried signed derivative has a Lebesgue density. -/
  absolutelyContinuousDerivative : path.HasAbsolutelyContinuousDerivative
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
  /-- Every instantaneous one-way flow is nonnegative almost everywhere. -/
  flowDerivativeNonnegativeAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ transition,
        0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path time transition
  /-- The derivative continuity equation is oriented as density change equals incoming minus
  outgoing flow. -/
  continuityEquationAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state,
        rengerDirectionalFlowHybridBVDensityDerivative path time state =
          (∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩) -
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩
  /-- The recovered initial density lies in the finite simplex. -/
  initialDensityNormalized :
    ∑ state, path.initialTrace (Sum.inl state) = 1
  /-- The recovered initial density has no negative coordinate. -/
  initialDensityNonnegative :
    ∀ state, 0 ≤ path.initialTrace (Sum.inl state)
  /-- Cumulative directional flow starts at zero in the recovered initial trace. -/
  cumulativeFlowInitiallyZero :
    ∀ transition, path.initialTrace (Sum.inr transition) = 0
  /-- The recovered terminal left density remains in the finite simplex. -/
  terminalDensityNormalized :
    ∑ state, path.terminalTrace hDuration (Sum.inl state) = 1
  /-- The recovered terminal left density has no negative coordinate. -/
  terminalDensityNonnegative :
    ∀ state, 0 ≤ path.terminalTrace hDuration (Sum.inl state)
  /-- Recovered terminal cumulative directional flows remain nonnegative. -/
  terminalCumulativeFlowNonnegative :
    ∀ transition, 0 ≤ path.terminalTrace hDuration (Sum.inr transition)

/-- The finite-coordinate density map is almost-everywhere measurable on the physical interval. -/
theorem aemeasurable_rengerDirectionalFlowHybridBVDensityAt
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    AEMeasurable (rengerDirectionalFlowHybridBVDensityAt path)
      (finiteOpenIntervalVolume duration) := by
  have hRepresentative :
      MemLp path.cadlagRepresentative.representative 1
        (finiteOpenIntervalVolume duration) :=
    Classical.choose path.cadlagRepresentative.represents
  have hRaw :
      AEStronglyMeasurable path.cadlagRepresentative.representative
        (finiteOpenIntervalVolume duration) :=
    hRepresentative.aestronglyMeasurable
  unfold rengerDirectionalFlowHybridBVDensityAt
    rengerDirectionalFlowHybridBVDensityValue
  fun_prop

/-- The finite-coordinate instantaneous-flow map is measurable, hence almost-everywhere
measurable for the physical interval measure. -/
theorem aemeasurable_rengerDirectionalFlowHybridBVFlowDerivativeAt
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    AEMeasurable (rengerDirectionalFlowHybridBVFlowDerivativeAt path)
      (finiteOpenIntervalVolume duration) := by
  apply Measurable.aemeasurable
  rw [measurable_pi_iff]
  intro transition
  exact measurable_real_toNNReal.comp
    (path.measurable_derivativeDensity (Sum.inr transition))

/-- The exact local density--flow action is almost-everywhere measurable along every hybrid path,
even before finite-rate admissibility is imposed. -/
theorem aemeasurable_rengerDirectionalFlowHybridBVLocalRate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    AEMeasurable (fun time =>
      rengerDirectionalFlowLocalRateRaw generator
        (rengerDirectionalFlowHybridBVDensityAt path time)
        (rengerDirectionalFlowHybridBVFlowDerivativeAt path time))
      (finiteOpenIntervalVolume duration) := by
  have hInput : AEMeasurable (fun time =>
      (rengerDirectionalFlowHybridBVDensityAt path time,
        rengerDirectionalFlowHybridBVFlowDerivativeAt path time))
      (finiteOpenIntervalVolume duration) :=
    (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path).prodMk
      (aemeasurable_rengerDirectionalFlowHybridBVFlowDerivativeAt path)
  have hFunction :
      ((fun input : (State → NNReal) ×
          (FiniteStateOrderedOffDiagonalTransition State → NNReal) =>
        rengerDirectionalFlowLocalRateRaw generator input.1 input.2) ∘
        (fun time : ℝ =>
          (rengerDirectionalFlowHybridBVDensityAt path time,
            rengerDirectionalFlowHybridBVFlowDerivativeAt path time))) =
      (fun time : ℝ =>
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)) := by
    funext time
    rfl
  rw [← hFunction]
  exact (measurable_rengerDirectionalFlowLocalRateRaw generator).comp_aemeasurable hInput

/-- Dynamic directional-flow path-rate data on the exact hybrid carrier.  Initial and terminal
cost sectors are literally zero here; theorem-specific initial regimes are added separately. -/
noncomputable def rengerDirectionalFlowHybridBVDynamicRateData
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    DensityFluxPathRateData
      (RengerDirectionalFlowHybridBVPath State duration) ℝ
      (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal) where
  densityAt := rengerDirectionalFlowHybridBVDensityAt
  fluxAt := rengerDirectionalFlowHybridBVFlowDerivativeAt
  terminalDensity := fun path =>
    rengerDirectionalFlowHybridBVTerminalDensity path hDuration
  timeMeasure := finiteOpenIntervalVolume duration
  localAction := rengerDirectionalFlowLocalRateRaw generator
  localAction_aemeasurable :=
    aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator
  initialCost := fun _path => 0
  boundaryCost := fun _path => 0
  continuityAdmissible := fun path =>
    RengerDirectionalFlowHybridBVAdmissible path hDuration

/-- Continuity-gated dynamic directional-flow action on the exact hybrid carrier. -/
noncomputable def rengerDirectionalFlowHybridBVDynamicRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  (rengerDirectionalFlowHybridBVDynamicRateData generator hDuration).pathRate path

/-- On the finite-rate domain, the dynamic rate is exactly the integral of the ordered-channel
extended Poisson costs. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path =
      ∫⁻ time,
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)
        ∂finiteOpenIntervalVolume duration := by
  rw [rengerDirectionalFlowHybridBVDynamicRate,
    DensityFluxPathRateData.pathRate_eq_of_continuityAdmissible _ hPath]
  simp [rengerDirectionalFlowHybridBVDynamicRateData]

/-- Every path outside the named finite-rate physical domain has infinite dynamic rate. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : ¬RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path = ∞ := by
  exact DensityFluxPathRateData.pathRate_eq_top_of_not_continuityAdmissible
    (rengerDirectionalFlowHybridBVDynamicRateData generator hDuration) hPath

end

end FiniteMarkovProcesses.InformationTheory
