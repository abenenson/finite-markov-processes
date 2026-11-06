/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMean
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTruncatedTargetDynamicRateRecovery
import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Stability
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovForwardDerivative

/-!
# Flow-defect stability for a physical regularization of a Renger hybrid target

The physical source and the finite-action target begin at the same density.  Their coordinate
error has an exact almost-everywhere derivative: Markov transport of the current error plus the
divergence of the generated-target-flow defect.  The first term is the one controlled by finite-
state `L1` dissipation; only the second term must vanish with the regularization.

No source-to-target convergence or large-deviation lower bound is asserted in this module.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- Real density error between the canonical physical regularization and the selected target
coordinate. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (state : State) : ℝ :=
  (finiteStateTimeDependentMarkovEndpointProbability
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      time state).toReal -
    rengerDirectionalFlowHybridBVDensityValue path.1 time state

/-- Generated target-density flow minus the target's raw real ordered flow on one channel. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (source target : State) : ℝ :=
  rengerDirectionalFlowHybridBVDensityValue path.1 time source *
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate time source target : ℝ) -
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue
      path.1 time source target

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The physical and target densities have zero coordinate error at the initial boundary. -/
@[simp]
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_zero
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (state : State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
      generator path index 0 state = 0 := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
  have hEndpointPMF := congrArg (fun law : PMF State ↦ law state)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetEndpointPMF_zero
      generator path index)
  have hEndpointProbability :
      finiteStateTimeDependentMarkovEndpointProbability
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          0 state =
        rengerDirectionalFlowHybridBVTargetInitialPMF path state := by
    simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetEndpointPMF,
      finiteStateTimeDependentMarkovEndpointPMF_apply] using! hEndpointPMF
  rw [hEndpointProbability]
  rw [rengerDirectionalFlowHybridBVTargetInitialPMF_apply]
  rw [ENNReal.coe_toReal]
  change (rengerDirectionalFlowHybridBVInitialDensity path.1 state : ℝ) -
    path.1.initialTrace (Sum.inl state) = 0
  exact sub_eq_zero.mpr <| Real.coe_toNNReal _ (path.2.initialDensityNonnegative state)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Pointwise source drift minus target divergence splits into rate-transported density error and
the divergence of the generated-target-flow defect. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetDrift_sub_targetDivergence_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovEndpointProbabilityDrift
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          time state -
        rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state =
      finiteStateRateErrorDivergence
          ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index).rate time)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
            generator path index time)
          state +
        finiteStateFlowDivergence
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
            generator path index time)
          state := by
  rw [finiteStateTimeDependentMarkovEndpointProbabilityDrift_eq_flowDivergence,
    rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence]
  simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError,
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect] using!
    finiteStateFlowDivergence_probabilityRate_sub_targetFlow_eq
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate time)
      (fun observed ↦
        (finiteStateTimeDependentMarkovEndpointProbability
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          time observed).toReal)
      (rengerDirectionalFlowHybridBVDensityValue path.1 time)
      (rengerDirectionalFlowHybridBVRawFlowDerivativeValue path.1 time)
      state

/-- Almost everywhere on the physical interval, the exact source-minus-target density error has
the dissipative Markov transport plus target-flow-defect divergence as its classical derivative. -/
theorem ae_hasDerivAt_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      HasDerivAt
        (fun horizon ↦
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
            generator path index horizon state)
        (finiteStateRateErrorDivergence
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time)
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
              generator path index time)
            state +
          finiteStateFlowDivergence
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
              generator path index time)
            state)
        time := by
  have hSourceDerivative :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        HasDerivAt
          (fun horizon ↦
            (finiteStateTimeDependentMarkovEndpointProbability
              (rengerDirectionalFlowHybridBVTargetInitialPMF path)
              (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                generator path.1 index)
              horizon state).toReal)
          (finiteStateTimeDependentMarkovEndpointProbabilityDrift
            (rengerDirectionalFlowHybridBVTargetInitialPMF path)
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index)
            time state)
          time := by
    simpa only [finiteOpenIntervalVolume] using!
      ae_hasDerivAt_finiteStateTimeDependentMarkovEndpointProbability
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩ state
  filter_upwards [hSourceDerivative,
    ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue hDuration path state] with
      time hSource hTarget
  have hErrorDerivative := hSource.sub hTarget
  rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetDrift_sub_targetDivergence_eq]
    at hErrorDerivative
  simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError] using!
    hErrorDerivative

/-- On every strict subhorizon, the physical-minus-target density error is absolutely continuous.
Both coordinates retain their independently established forward integral equations. -/
theorem
  absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) {horizon : ℝ} (hHorizonNonnegative : 0 ≤ horizon)
    (hHorizon : horizon < duration) (state : State) :
    AbsolutelyContinuousOnInterval
      (fun time ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index time state)
      0 horizon := by
  let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    generator path.1 index
  let initial := rengerDirectionalFlowHybridBVTargetInitialPMF path
  let source := fun time ↦
    (finiteStateTimeDependentMarkovEndpointProbability initial rates time state).toReal
  let target := fun time ↦
    rengerDirectionalFlowHybridBVDensityValue path.1 time state
  let sourceDrift := fun time ↦
    finiteStateTimeDependentMarkovEndpointProbabilityDrift initial rates time state
  let targetDivergence := fun time ↦
    rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state
  have hSourceDriftIntegrable :
      IntervalIntegrable sourceDrift MeasureTheory.volume 0 horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hHorizonNonnegative]
    exact integrableOn_finiteStateTimeDependentMarkovEndpointProbabilityDrift
      initial rates ⟨horizon, hHorizonNonnegative⟩ state
  have hSourcePrimitiveContinuous : AbsolutelyContinuousOnInterval
      (fun time ↦ (initial state).toReal + ∫ point in 0..time, sourceDrift point)
      0 horizon :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.const_add (initial state).toReal <|
      FiniteMarkovProcesses.intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
        hSourceDriftIntegrable (by
          rw [uIcc_of_le hHorizonNonnegative]
          exact ⟨le_rfl, hHorizonNonnegative⟩)
  have hSourceContinuous : AbsolutelyContinuousOnInterval source 0 horizon := by
    apply FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.congr_on
      (function := fun time ↦
        (initial state).toReal + ∫ point in 0..time, sourceDrift point)
      (replacement := source) ?_ hSourcePrimitiveContinuous
    intro time hTime
    rw [uIcc_of_le hHorizonNonnegative] at hTime
    have hEquation :=
      finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_integral_drift
        initial rates ⟨time, hTime.1⟩ state
    change source time = (initial state).toReal +
      ∫ point in Ioo 0 time, sourceDrift point at hEquation
    calc
      (initial state).toReal + ∫ point in 0..time, sourceDrift point =
          (initial state).toReal + ∫ point in Ioo 0 time, sourceDrift point := by
        rw [intervalIntegral.integral_of_le hTime.1,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = source time := hEquation.symm
  have hTargetDivergenceIntegrable :
      IntervalIntegrable targetDivergence MeasureTheory.volume 0 horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hHorizonNonnegative]
    have hIntervalSubset : Ioo 0 horizon ⊆ Ioo 0 duration := by
      intro time hTime
      exact ⟨hTime.1, lt_of_lt_of_le hTime.2 hHorizon.le⟩
    exact (integrable_rengerDirectionalFlowHybridBVTargetFlowDivergence
      path.1 state).mono_measure <|
        MeasureTheory.Measure.restrict_mono
          hIntervalSubset
          (le_refl MeasureTheory.volume)
  have hTargetPrimitiveContinuous : AbsolutelyContinuousOnInterval
      (fun time ↦ path.1.initialTrace (Sum.inl state) +
        ∫ point in 0..time, targetDivergence point)
      0 horizon :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.const_add
      (path.1.initialTrace (Sum.inl state)) <|
        FiniteMarkovProcesses.intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
          hTargetDivergenceIntegrable (by
            rw [uIcc_of_le hHorizonNonnegative]
            exact ⟨le_rfl, hHorizonNonnegative⟩)
  have hTargetContinuous : AbsolutelyContinuousOnInterval target 0 horizon := by
    apply FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.congr_on
      (function := fun time ↦ path.1.initialTrace (Sum.inl state) +
        ∫ point in 0..time, targetDivergence point)
      (replacement := target) ?_ hTargetPrimitiveContinuous
    intro time hTime
    rw [uIcc_of_le hHorizonNonnegative] at hTime
    have hEquation :=
      rengerDirectionalFlowHybridBVDensityValue_eq_initial_add_integral_flowDivergence
        hDuration path ⟨hTime.1, lt_of_le_of_lt hTime.2 hHorizon⟩ state
    change target time = path.1.initialTrace (Sum.inl state) +
      ∫ point in Ioo 0 time, targetDivergence point at hEquation
    calc
      path.1.initialTrace (Sum.inl state) +
          ∫ point in 0..time, targetDivergence point =
        path.1.initialTrace (Sum.inl state) +
          ∫ point in Ioo 0 time, targetDivergence point := by
        rw [intervalIntegral.integral_of_le hTime.1,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = target time := hEquation.symm
  simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError,
    source, target, initial, rates] using hSourceContinuous.fun_sub hTargetContinuous

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Under the pointwise admissible versions, one generated-target-flow defect is exactly the
truncation deficit plus the vanishing reference-floor flow. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (source target : State)
    (hDensityVersion :
      rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time =
        rengerDirectionalFlowHybridBVDensityAt path.1 time)
    (hDensityNonnegative : ∀ state,
      0 ≤ rengerDirectionalFlowHybridBVDensityValue path.1 time state)
    (hFlowNonnegative : ∀ transition,
      0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition)
    (hSupported :
      (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
          generator path.1 index).rate time source target =
        (rengerDirectionalFlowHybridBVTruncatedTargetRate
          path.1 index).rate time source target) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator path index time source target =
      (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
          path.1 index time source target : ℝ) -
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target : ℝ) +
        (1 / ((index : NNReal) + 1) : ℝ) *
          (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target : ℝ) := by
  by_cases hDiagonal : source = target
  · subst target
    unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
      rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    rw [(rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index).rate_self,
      (rengerDirectionalFlowHybridBVTruncatedTargetRate path.1 index).rate_self,
      generator.rate_self]
    simp [rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt]
  · have hDensityReal :
        rengerDirectionalFlowHybridBVDensityValue path.1 time source =
          (rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source : ℝ) := by
      calc
        rengerDirectionalFlowHybridBVDensityValue path.1 time source =
            (rengerDirectionalFlowHybridBVDensityAt path.1 time source : ℝ) :=
          (Real.coe_toNNReal _ (hDensityNonnegative source)).symm
        _ = (rengerDirectionalFlowHybridBVMeasurableDensityAt
              path.1 time source : ℝ) := by
          rw [hDensityVersion]
    have hFlowReal :
        rengerDirectionalFlowHybridBVRawFlowDerivativeValue
            path.1 time source target =
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ℝ) := by
      unfold rengerDirectionalFlowHybridBVRawFlowDerivativeValue
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
      simp_rw [dite_eq_left hDiagonal]
      unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
      exact (Real.coe_toNNReal _ (hFlowNonnegative _)).symm
    rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization,
      rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate,
      hSupported, hDensityReal, hFlowReal]
    unfold rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    push_cast
    ring

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- For a finite-action target, the exact channel-defect decomposition holds almost everywhere
on the physical interval. -/
theorem ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_eq
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target =
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ℝ) -
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ℝ) +
          (1 / ((index : NNReal) + 1) : ℝ) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ℝ) := by
  filter_upwards [ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq path.1,
    path.2.densityNonnegativeAE, path.2.flowDerivativeNonnegativeAE,
    ae_rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_truncatedTargetRate
      generator hDuration path hDynamicRate index source target] with
      time hDensityVersion hDensityNonnegative hFlowNonnegative hSupported
  exact rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_eq
    generator path index time source target hDensityVersion hDensityNonnegative
      hFlowNonnegative hSupported

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Almost everywhere, the absolute generated-target-flow defect is bounded by the removed
target flow plus the positive reference-floor expected flow. -/
theorem ae_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target| ≤
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ℝ) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ℝ) +
          (1 / ((index : NNReal) + 1) : ℝ) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ℝ) := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_eq
      generator hDuration path hDynamicRate index source target] with time hDefect
  by_cases hOffDiagonal : source ≠ target
  · have hTruncatedLe :
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ℝ) ≤
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ℝ) := by
      exact_mod_cast
        rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
          path.1 index time hOffDiagonal
    have hReferenceFlowNonnegative :
        0 ≤ (1 / ((index : NNReal) + 1) : ℝ) *
          (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 time source target : ℝ) := by positivity
    rw [hDefect, abs_le]
    constructor <;> linarith
  · have hDiagonal : source = target := not_ne_iff.mp hOffDiagonal
    subst target
    rw [hDefect]
    unfold rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
      rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
    rw [(rengerDirectionalFlowHybridBVTruncatedTargetRate path.1 index).rate_self,
      generator.rate_self]
    simp [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The channel-defect bound lifted to `ENNReal`, in the exact form consumed by `lintegral`. -/
theorem ae_ofReal_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ENNReal.ofReal
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
            generator path index time source target| ≤
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ENNReal) +
          ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ENNReal) := by
  filter_upwards [
    ae_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le
      generator hDuration path hDynamicRate index source target] with time hBound
  calc
    ENNReal.ofReal
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target| ≤
      ENNReal.ofReal
        ((rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target : ℝ) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 index time source target : ℝ) +
          (1 / ((index : NNReal) + 1) : ℝ) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ℝ)) :=
        ENNReal.ofReal_le_ofReal hBound
    _ ≤ ENNReal.ofReal
          ((rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target : ℝ) -
            (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 index time source target : ℝ)) +
        ENNReal.ofReal
          ((1 / ((index : NNReal) + 1) : ℝ) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ℝ)) :=
        ENNReal.ofReal_add_le
    _ = _ := by
      have hDenominator :
          ENNReal.ofReal ((((index : NNReal) : ℝ) + 1)) =
            ((index : NNReal) : ENNReal) + 1 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp
      rw [ENNReal.ofReal_sub _ (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_div_of_pos (by positivity), hDenominator]
      simp

/-- Integrated absolute generated-target-flow defect on one ordered state pair. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (source target : State) : ENNReal :=
  ∫⁻ time,
    ENNReal.ofReal
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator path index time source target|
    ∂finiteOpenIntervalVolume duration

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A channel's integrated absolute flow defect is bounded by its integrated truncation deficit
plus its vanishing reference-floor expected flow. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
        generator path index source target ≤
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) +
        ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
  calc
    (∫⁻ time,
      ENNReal.ofReal
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target|
      ∂finiteOpenIntervalVolume duration) ≤
      ∫⁻ time,
        ((rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target : ENNReal) -
            (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 index time source target : ENNReal)) +
          ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration :=
      MeasureTheory.lintegral_mono_ae <|
        ae_ofReal_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le
          generator hDuration path hDynamicRate index source target
    _ = _ := by
      rw [MeasureTheory.lintegral_add_left']
      · rw [MeasureTheory.lintegral_const_mul']
        finiteness
      · exact
          ((measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 source target).coe_nnreal_ennreal.sub
            (measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 index source target).coe_nnreal_ennreal).aemeasurable

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The real absolute flow defect on every ordered channel is integrable on the complete physical
interval. -/
theorem integrable_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    MeasureTheory.Integrable
      (fun time ↦
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target|)
      (finiteOpenIntervalVolume duration) := by
  let surrogate : ℝ → ℝ := fun time ↦
    (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path.1 index time source target : ℝ) -
      (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target : ℝ) +
      (1 / ((index : NNReal) + 1) : ℝ) *
        (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
          generator path.1 time source target : ℝ)
  have hSurrogateMeasurable : Measurable surrogate := by
    exact
      ((measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
          path.1 index source target).coe_nnreal_real.sub
        (measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 source target).coe_nnreal_real).add
        (measurable_const.mul
          (measurable_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
            generator path.1 source target).coe_nnreal_real)
  have hDefectAE :
      (fun time ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target) =ᵐ[finiteOpenIntervalVolume duration]
        surrogate := by
    simpa only [surrogate] using!
      ae_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_eq
        generator hDuration path hDynamicRate index source target
  have hAbsDefectMeasurable : MeasureTheory.AEStronglyMeasurable
      (fun time ↦
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target|)
      (finiteOpenIntervalVolume duration) :=
    hSurrogateMeasurable.norm.aestronglyMeasurable.congr <|
      hDefectAE.symm.mono fun _time hEquality ↦ by
        simpa [Real.norm_eq_abs] using congrArg abs hEquality
  have hTargetFlowFinite :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
    by_cases hOffDiagonal : source ≠ target
    · exact
        lintegral_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_ne_top
          generator hDuration path hDynamicRate hOffDiagonal
    · simp [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt,
        not_ne_iff.mp hOffDiagonal]
  have hTruncationFinite :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ :=
    ne_top_of_le_ne_top hTargetFlowFinite <|
      MeasureTheory.lintegral_mono fun _time ↦ tsub_le_self
  have hExpectedFlowFinite :=
    lintegral_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt_ne_top
      generator hDuration path source target
  have hUpperFinite :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal) -
          (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
            path.1 index time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) +
        ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
              generator path.1 time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration ≠ ⊤ := by
    apply ENNReal.add_ne_top.2
    exact ⟨hTruncationFinite,
      ENNReal.mul_ne_top (by simp) hExpectedFlowFinite⟩
  have hDefectFinite :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
        generator path index source target ≠ ⊤ :=
    ne_top_of_le_ne_top hUpperFinite <|
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_le
        generator hDuration path hDynamicRate index source target
  apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAbsDefectMeasurable
    (Filter.Eventually.of_forall fun _time ↦ abs_nonneg _)).mp
  simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect] using
    hDefectFinite

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every channel's integrated absolute generated-target-flow defect vanishes along the canonical
cutoff/reference-floor sequence. -/
theorem tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (source target : State) :
    Tendsto
      (fun index : ℕ ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
          generator path index source target)
      atTop (nhds 0) := by
  by_cases hOffDiagonal : source ≠ target
  · have hTruncation :=
      tendsto_lintegral_rengerDirectionalFlowHybridBVTruncatedTargetFlowError_atTop
        generator hDuration path hDynamicRate hOffDiagonal
    have hReferenceWeight :
        Tendsto
          (fun index : ℕ ↦
            ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal))
          atTop (nhds 0) := by
      simpa using
        (ENNReal.tendsto_coe.2
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal)))
    have hExpectedFinite :=
      lintegral_rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt_ne_top
        generator hDuration path source target
    have hReferenceFlow :
        Tendsto
          (fun index : ℕ ↦
            ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
              ∫⁻ time,
                (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                  generator path.1 time source target : ENNReal)
                ∂finiteOpenIntervalVolume duration)
          atTop (nhds 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul_const hReferenceWeight (Or.inr hExpectedFinite)
    have hUpper :
        Tendsto
          (fun index : ℕ ↦
            (∫⁻ time,
              (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                  path.1 time source target : ENNReal) -
                (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
                  path.1 index time source target : ENNReal)
              ∂finiteOpenIntervalVolume duration) +
              ((1 / ((index : NNReal) + 1) : NNReal) : ENNReal) *
                ∫⁻ time,
                  (rengerDirectionalFlowHybridBVMeasurableExpectedFlowAt
                    generator path.1 time source target : ENNReal)
                  ∂finiteOpenIntervalVolume duration)
          atTop (nhds 0) := by
      simpa only [zero_add] using hTruncation.add hReferenceFlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
    · exact Filter.Eventually.of_forall fun _index ↦ zero_le
    · exact Filter.Eventually.of_forall fun index ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_le
          generator hDuration path hDynamicRate index source target
  · have hDiagonal : source = target := not_ne_iff.mp hOffDiagonal
    subst target
    have hDefectZero (index : ℕ) (time : ℝ) :
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source source = 0 := by
      unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        rengerDirectionalFlowHybridBVRawFlowDerivativeValue
      rw [(rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate_self]
      simp
    simp [rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect,
      hDefectZero]

/-- Complete integrated absolute generated-target-flow defect over all ordered state pairs.
Diagonal terms are included but vanish identically. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) : ENNReal :=
  ∑ source, ∑ target,
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
      generator path index source target

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete finite-state integrated forcing vanishes along the canonical regularization. -/
theorem tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤) :
    Tendsto
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
        generator path)
      atTop (nhds 0) := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ fun source _hSource ↦
      tendsto_finsetSum Finset.univ fun target _hTarget ↦
        tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_atTop
          generator hDuration path hDynamicRate source target)

end

end FiniteMarkovProcesses.InformationTheory
