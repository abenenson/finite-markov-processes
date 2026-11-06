/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetFlowDefectStability

/-!
# Density-error convergence for a physical regularization of a Renger hybrid target

This module converts the exact flow-defect stability estimates into strict-subhorizon density
convergence. It preserves the source-neutral boundary: no large-deviation lower bound is asserted.
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
omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- At every time, the sign pairing of the exact error derivative is bounded solely by twice the
complete instantaneous absolute flow defect. -/
theorem sum_sign_mul_rengerDirectionalFlowHybridBVCanonicalPositiveTargetErrorDerivative_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) :
    (∑ state,
      Real.sign
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
            generator path index time state) *
        (finiteStateRateErrorDivergence
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time)
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
              generator path index time)
            state +
          finiteStateFlowDivergence
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
              generator path index time)
            state)) ≤
      2 * ∑ source, ∑ target,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target| :=
  sum_sign_mul_rateErrorDivergence_add_flowDivergence_le
    ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index).rate time)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
      generator path index time)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
      generator path index time)

/-- On every strict subhorizon, the endpoint density `L1` error is controlled by twice the
integrated complete ordered-flow defect, with no cutoff-dependent Gronwall factor. -/
theorem sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_integral
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) {horizon : ℝ} (hHorizonNonnegative : 0 ≤ horizon)
    (hHorizon : horizon < duration) :
    (∑ state,
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
        generator path index horizon state|) ≤
      ∫ time in 0..horizon, 2 * ∑ source, ∑ target,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target| := by
  let error := fun time state ↦
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
      generator path index time state
  let derivative := fun time state ↦
    finiteStateRateErrorDivergence
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index).rate time)
        (error time) state +
      finiteStateFlowDivergence
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time) state
  let bound := fun time ↦ 2 * ∑ source, ∑ target,
    |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
      generator path index time source target|
  have hIntervalSubset : Ioo 0 horizon ⊆ Ioo 0 duration := by
    intro time hTime
    exact ⟨hTime.1, lt_of_lt_of_le hTime.2 hHorizon.le⟩
  have hRestrictLe :
      MeasureTheory.volume.restrict (Ioo 0 horizon) ≤
        finiteOpenIntervalVolume duration := by
    unfold finiteOpenIntervalVolume
    exact MeasureTheory.Measure.restrict_mono
      hIntervalSubset (le_refl MeasureTheory.volume)
  have hBoundIntegrableFull : MeasureTheory.Integrable bound
      (finiteOpenIntervalVolume duration) := by
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro source _hSource
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro target _hTarget
    exact
      integrable_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator hDuration path hDynamicRate index source target
  have hBoundIntegrable :
      IntervalIntegrable bound MeasureTheory.volume 0 horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hHorizonNonnegative]
    exact hBoundIntegrableFull.mono_measure hRestrictLe
  have hDerivative : ∀ state,
      ∀ᵐ time ∂MeasureTheory.volume.restrict (Ioo 0 horizon),
        HasDerivAt (fun markedTime ↦ error markedTime state)
          (derivative time state) time := by
    intro state
    apply MeasureTheory.ae_mono hRestrictLe
    simpa only [error, derivative] using!
      ae_hasDerivAt_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
        generator hDuration path index state
  have hDerivativeBound :
      ∀ᵐ time ∂MeasureTheory.volume.restrict (Ioo 0 horizon),
        (∑ state, Real.sign (error time state) * derivative time state) ≤
          bound time :=
    Filter.Eventually.of_forall fun time ↦ by
      simpa only [error, derivative, bound] using
        sum_sign_mul_rengerDirectionalFlowHybridBVCanonicalPositiveTargetErrorDerivative_le
          generator path index time
  have hEndpoint :=
    finite_sum_abs_sub_le_intervalIntegral_of_ae_hasDerivAt
      hHorizonNonnegative
      (fun state ↦
        absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator hDuration path index hHorizonNonnegative hHorizon state)
      hDerivative bound hBoundIntegrable hDerivativeBound
  simpa only [error, bound,
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_zero,
    abs_zero, Finset.sum_const_zero, sub_zero] using hEndpoint

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The strict-subhorizon real defect integral is bounded by the complete physical-interval
`ENNReal` defect used by the canonical cutoff convergence theorem. -/
theorem integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le_total
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) {horizon : ℝ} (hHorizonNonnegative : 0 ≤ horizon)
    (hHorizon : horizon < duration) :
    (∫ time in 0..horizon, 2 * ∑ source, ∑ target,
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator path index time source target|) ≤
      2 *
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
          generator path index).toReal := by
  let channel := fun source target time ↦
    |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
      generator path index time source target|
  let bound := fun time ↦ 2 * ∑ source, ∑ target, channel source target time
  have hIntervalSubset : Ioo 0 horizon ⊆ Ioo 0 duration := by
    intro time hTime
    exact ⟨hTime.1, lt_of_lt_of_le hTime.2 hHorizon.le⟩
  have hRestrictLe :
      MeasureTheory.volume.restrict (Ioo 0 horizon) ≤
        finiteOpenIntervalVolume duration := by
    unfold finiteOpenIntervalVolume
    exact MeasureTheory.Measure.restrict_mono
      hIntervalSubset (le_refl MeasureTheory.volume)
  have hChannelIntegrable (source target : State) :
      MeasureTheory.Integrable (channel source target)
        (finiteOpenIntervalVolume duration) := by
    simpa only [channel] using
      integrable_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator hDuration path hDynamicRate index source target
  have hBoundIntegrable : MeasureTheory.Integrable bound
      (finiteOpenIntervalVolume duration) := by
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro source _hSource
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro target _hTarget
    exact hChannelIntegrable source target
  have hIntegralMono :
      (∫ time, bound time ∂MeasureTheory.volume.restrict (Ioo 0 horizon)) ≤
        ∫ time, bound time ∂finiteOpenIntervalVolume duration := by
    apply MeasureTheory.integral_mono_measure hRestrictLe
    · exact Filter.Eventually.of_forall fun _time ↦ by positivity
    · exact hBoundIntegrable
  have hChannelIntegral (source target : State) :
      (∫ time, channel source target time ∂finiteOpenIntervalVolume duration) =
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
          generator path index source target).toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _time ↦ abs_nonneg _)
      (hChannelIntegrable source target).aestronglyMeasurable]
    rfl
  have hChannelFinite (source target : State) :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
        generator path index source target ≠ ⊤ := by
    apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      (hChannelIntegrable source target).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _time ↦ abs_nonneg _)).mpr
    exact hChannelIntegrable source target
  calc
    (∫ time in 0..horizon, 2 * ∑ source, ∑ target,
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator path index time source target|) =
        ∫ time, bound time ∂MeasureTheory.volume.restrict (Ioo 0 horizon) := by
      rw [intervalIntegral.integral_of_le hHorizonNonnegative,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ time, bound time ∂finiteOpenIntervalVolume duration := hIntegralMono
    _ = 2 * ∑ source, ∑ target,
        ∫ time, channel source target time
          ∂finiteOpenIntervalVolume duration := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro source _hSource
        rw [MeasureTheory.integral_finsetSum]
        exact fun target _hTarget ↦ hChannelIntegrable source target
      · exact fun source _hSource ↦
          MeasureTheory.integrable_finsetSum Finset.univ fun target _hTarget ↦
            hChannelIntegrable source target
    _ = 2 * ∑ source, ∑ target,
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
          generator path index source target).toReal := by
      congr 1
      apply Finset.sum_congr rfl
      intro source _hSource
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact hChannelIntegral source target
    _ = 2 *
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
          generator path index).toReal := by
      unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
      rw [ENNReal.toReal_sum]
      · congr 1
        apply Finset.sum_congr rfl
        intro source _hSource
        rw [ENNReal.toReal_sum]
        exact fun target _hTarget ↦ hChannelFinite source target
      · intro source _hSource
        exact ENNReal.sum_ne_top.mpr fun target _hTarget ↦
          hChannelFinite source target

/-- The canonical regularized source mean converges in endpoint density `L1` to every strict
subhorizon coordinate of the finite-action target. -/
theorem tendsto_sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {horizon : ℝ} (hHorizonNonnegative : 0 ≤ horizon)
    (hHorizon : horizon < duration) :
    Tendsto
      (fun index : ℕ ↦ ∑ state,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index horizon state|)
      atTop (nhds 0) := by
  have hUpper (index : ℕ) :
      (∑ state,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index horizon state|) ≤
        2 *
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
            generator path index).toReal :=
    (sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_integral
      generator hDuration path hDynamicRate index hHorizonNonnegative hHorizon).trans <|
        integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le_total
          generator hDuration path hDynamicRate index hHorizonNonnegative hHorizon
  have hTotal :=
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_atTop
      generator hDuration path hDynamicRate
  have hUpperTendsto :
      Tendsto
        (fun index : ℕ ↦
          2 *
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index).toReal)
        atTop (nhds 0) := by
    have hToReal :
        Tendsto
          (fun index : ℕ ↦
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index).toReal)
          atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using!
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTotal
    simpa only [mul_zero] using
      (show Tendsto (fun _index : ℕ ↦ (2 : ℝ)) atTop (nhds 2) from
        tendsto_const_nhds).mul hToReal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpperTendsto
  · exact Filter.Eventually.of_forall fun _index ↦ by positivity
  · exact Filter.Eventually.of_forall hUpper

/-- The canonical physical-source density converges uniformly over every nonnegative strict
subhorizon.  This is the uniform-in-time form needed before a fixed bounded target chart may
multiply the density error in the lower-bound argument. -/
theorem eventually_sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_lt
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {tolerance : ℝ} (hTolerance : 0 < tolerance) :
    ∀ᶠ index : ℕ in atTop, ∀ horizon : ℝ,
      0 ≤ horizon → horizon < duration →
        (∑ state,
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
            generator path index horizon state|) < tolerance := by
  have hTotal :=
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_atTop
      generator hDuration path hDynamicRate
  have hUpperTendsto :
      Tendsto
        (fun index : ℕ ↦
          2 *
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index).toReal)
        atTop (nhds 0) := by
    have hToReal :
        Tendsto
          (fun index : ℕ ↦
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index).toReal)
          atTop (nhds 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using!
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTotal
    simpa only [mul_zero] using
      (show Tendsto (fun _index : ℕ ↦ (2 : ℝ)) atTop (nhds 2) from
        tendsto_const_nhds).mul hToReal
  filter_upwards [hUpperTendsto.eventually (Iio_mem_nhds hTolerance)] with index hIndex
  intro horizon hHorizonNonnegative hHorizon
  exact lt_of_le_of_lt
    ((sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_integral
      generator hDuration path hDynamicRate index hHorizonNonnegative hHorizon).trans <|
        integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le_total
          generator hDuration path hDynamicRate index hHorizonNonnegative hHorizon)
    hIndex

end


end FiniteMarkovProcesses.InformationTheory
