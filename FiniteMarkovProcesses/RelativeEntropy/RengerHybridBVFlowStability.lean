/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVForwardUniqueness
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Stability

/-!
# Forced-flow stability on the hybrid-BV directional-flow carrier

The raw ordered-flow residual measures departure from one fixed Markov generator. Admissible
paths satisfy a forced forward equation, whose sign pairing is dissipative. Consequently the
density error is bounded by its actual initial error plus twice the integrated residual.

## Main results

- `rengerDirectionalFlowHybridBVIntegratedFlowResidual_nonneg`.
- `sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual`.
- `rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_residual`.
- `sum_abs_rengerDirectionalFlowHybridBVTerminalFlow_sub_le_initial_add_residual`.
- `sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_initial_add_residual`.
- `norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_residual`.

All pointwise conclusions concern physical time `[0,T)`. Terminal traces are left traces;
the hybrid carrier itself is not given a subtraction or a norm.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] {duration : ℝ}

/-- The raw ordered flow's defect from density times the fixed generator rate. The diagonal is
zero, and no pointwise nonnegativity convention is imposed on chosen RN values. -/
noncomputable def rengerDirectionalFlowHybridBVFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (source target : State) : ℝ :=
  rengerDirectionalFlowHybridBVRawFlowDerivativeValue path time source target -
    rengerDirectionalFlowHybridBVDensityValue path time source *
      (generator.rate source target : ℝ)

/-- Complete physical-time ordered off-diagonal residual, using the raw density and raw RN
flow derivative. Integrability follows from the carried finite signed measures and density L1. -/
noncomputable def rengerDirectionalFlowHybridBVIntegratedFlowResidual
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ℝ :=
  ∫ time, ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
      rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
        (generator.rate transition.1.1 transition.1.2 : ℝ)|
    ∂finiteOpenIntervalVolume duration

/-- Every raw ordered residual coordinate is integrable, without a finite-action premise. -/
theorem integrable_rengerDirectionalFlowHybridBVFlowDefect
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (source target : State) :
    Integrable (fun time ↦
      rengerDirectionalFlowHybridBVFlowDefect generator path time source target)
      (finiteOpenIntervalVolume duration) := by
  apply Integrable.sub
  · by_cases hDistinct : source ≠ target
    · simpa only [rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
        dite_eq_left hDistinct] using
        integrable_rengerDirectionalFlowHybridBVFlowDerivative path
          ⟨(source, target), hDistinct⟩
    · simp only [rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
        dite_eq_right hDistinct]
      exact integrable_zero _ _ _
  · exact (integrable_rengerDirectionalFlowHybridBVDensityValue path source).mul_const _

/-- The nonnegative finite sum defining the integrated raw flow residual is integrable. -/
theorem integrable_rengerDirectionalFlowHybridBVFlowResidual
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Integrable (fun time ↦ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
        rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
          (generator.rate transition.1.1 transition.1.2 : ℝ)|)
      (finiteOpenIntervalVolume duration) := by
  apply integrable_finsetSum
  intro transition _hTransition
  exact ((integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition).sub
    ((integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1).mul_const
      (generator.rate transition.1.1 transition.1.2 : ℝ))).abs

/-- The integrated raw flow residual is nonnegative, including empty transition families. -/
theorem rengerDirectionalFlowHybridBVIntegratedFlowResidual_nonneg
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    0 ≤ rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path :=
  integral_nonneg fun _time ↦ Finset.sum_nonneg fun _transition _hTransition ↦ abs_nonneg _

private theorem sum_sum_eq_sum_ordered_of_diagonal_zero
    (flow : State → State → ℝ) (hDiagonal : ∀ state, flow state state = 0) :
    (∑ source, ∑ target, flow source target) =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        flow transition.1.1 transition.1.2 := by
  rw [← sum_outgoingTransition_eq_sum_orderedOffDiagonalTransition]
  apply Finset.sum_congr rfl
  intro source _hSource
  rw [Fintype.sum_eq_add_sum_subtype_ne _ source, hDiagonal, zero_add]

/-- Totalizing the raw defect by its zero diagonal preserves the ordered off-diagonal sum. -/
theorem sum_abs_rengerDirectionalFlowHybridBVFlowDefect_eq
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (time : ℝ) :
    (∑ source, ∑ target,
      |rengerDirectionalFlowHybridBVFlowDefect generator path time source target|) =
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
          rengerDirectionalFlowHybridBVDensityValue path time transition.1.1 *
            (generator.rate transition.1.1 transition.1.2 : ℝ)| := by
  rw [sum_sum_eq_sum_ordered_of_diagonal_zero
    (fun source target ↦
      |rengerDirectionalFlowHybridBVFlowDefect generator path time source target|)
    (fun state ↦ by simp [rengerDirectionalFlowHybridBVFlowDefect,
      rengerDirectionalFlowHybridBVRawFlowDerivativeValue, generator.rate_self])]
  apply Finset.sum_congr rfl
  intro transition _hTransition
  simp only [rengerDirectionalFlowHybridBVFlowDefect,
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue, dite_eq_left transition.2]

/-- The fixed-generator density difference satisfies the forward equation with its explicit
raw flow defect as forcing. No uniqueness premise is used. -/
theorem ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_sub
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      HasDerivAt (fun point ↦
        rengerDirectionalFlowHybridBVDensityValue path.1 point state -
          rengerDirectionalFlowHybridBVDensityValue mean.1 point state)
        (finiteStateRateErrorDivergence generator.rate
            (fun observed ↦ rengerDirectionalFlowHybridBVDensityValue path.1 time observed -
              rengerDirectionalFlowHybridBVDensityValue mean.1 time observed) state +
          finiteStateFlowDivergence
            (rengerDirectionalFlowHybridBVFlowDefect generator path.1 time) state) time := by
  filter_upwards [ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue hDuration path state,
    ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow
      generator hDuration mean hMeanFlow state] with time hPath hMean
  convert hPath.sub hMean using 1
  rw [rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence]
  unfold finiteStateFlowDivergence finiteStateRateErrorDivergence
    rengerDirectionalFlowHybridBVFlowDefect
  simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- Every strict-subhorizon density L1 error is bounded by its actual initial error plus twice
the complete integrated flow residual. There is no Gronwall factor or same-initial restriction. -/
theorem sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (∑ state, |rengerDirectionalFlowHybridBVDensityValue path.1 time state -
      rengerDirectionalFlowHybridBVDensityValue mean.1 time state|) ≤
      (∑ state, |path.1.initialTrace (Sum.inl state) -
        mean.1.initialTrace (Sum.inl state)|) +
      2 * rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 := by
  let error := fun time state ↦
    rengerDirectionalFlowHybridBVDensityValue path.1 time state -
      rengerDirectionalFlowHybridBVDensityValue mean.1 time state
  let derivative := fun time state ↦
    finiteStateRateErrorDivergence generator.rate (error time) state +
      finiteStateFlowDivergence
        (rengerDirectionalFlowHybridBVFlowDefect generator path.1 time) state
  let bound := fun time ↦ 2 * ∑ source, ∑ target,
    |rengerDirectionalFlowHybridBVFlowDefect generator path.1 time source target|
  have hRestrict : volume.restrict (Ioo 0 time) ≤ finiteOpenIntervalVolume duration :=
    Measure.restrict_mono (Ioo_subset_Ioo_right hTime.2.le) le_rfl
  have hBoundIntegrable : Integrable bound (finiteOpenIntervalVolume duration) := by
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ fun source _hSource ↦
      integrable_finsetSum Finset.univ fun target _hTarget ↦
        (integrable_rengerDirectionalFlowHybridBVFlowDefect
          generator path.1 source target).abs
  have hIntervalIntegrable : IntervalIntegrable bound volume 0 time := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hTime.1]
    exact hBoundIntegrable.mono_measure hRestrict
  have hDerivative : ∀ state, ∀ᵐ point ∂volume.restrict (Ioo 0 time),
      HasDerivAt (fun horizon ↦ error horizon state) (derivative point state) point := by
    intro state
    exact ae_mono hRestrict
      (ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_sub
        generator hDuration path mean hMeanFlow state)
  have hEndpoint := finite_sum_abs_sub_le_intervalIntegral_of_ae_hasDerivAt hTime.1
    (fun state ↦
      (absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue
        hDuration path hTime state).sub
      (absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue
        hDuration mean hTime state))
    hDerivative bound hIntervalIntegrable
    (Eventually.of_forall fun point ↦
      sum_sign_mul_rateErrorDivergence_add_flowDivergence_le generator.rate (error point)
        (rengerDirectionalFlowHybridBVFlowDefect generator path.1 point))
  have hIntegral : (∫ point in 0..time, bound point) ≤
      2 * rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 := by
    rw [intervalIntegral.integral_of_le hTime.1, integral_Ioc_eq_integral_Ioo]
    calc
      _ ≤ ∫ point, bound point ∂finiteOpenIntervalVolume duration :=
        integral_mono_measure hRestrict
          (Eventually.of_forall fun _point ↦ mul_nonneg (by norm_num)
            (Finset.sum_nonneg fun _source _hSource ↦
              Finset.sum_nonneg fun _target _hTarget ↦ abs_nonneg _)) hBoundIntegrable
      _ = _ := by
        simp only [bound, sum_abs_rengerDirectionalFlowHybridBVFlowDefect_eq,
          integral_const_mul, rengerDirectionalFlowHybridBVIntegratedFlowResidual]
  change (∑ state, |error time state|) - ∑ state, |error 0 state| ≤ _ at hEndpoint
  change (∑ state, |error time state|) ≤ (∑ state, |error 0 state|) + _
  linarith

/-- Complete physical-time L1 distance between the raw ordered-flow derivatives of two paths. -/
noncomputable def rengerDirectionalFlowHybridBVIntegratedFlowDistance
    (path mean : RengerDirectionalFlowHybridBVPath State duration) : ℝ :=
  ∫ time, ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
      rengerDirectionalFlowHybridBVFlowDerivative mean time transition|
    ∂finiteOpenIntervalVolume duration

/-- The integrated actual ordered-flow derivative distance is nonnegative. -/
theorem rengerDirectionalFlowHybridBVIntegratedFlowDistance_nonneg
    (path mean : RengerDirectionalFlowHybridBVPath State duration) :
    0 ≤ rengerDirectionalFlowHybridBVIntegratedFlowDistance path mean :=
  integral_nonneg fun _time ↦ Finset.sum_nonneg fun _transition _hTransition ↦ abs_nonneg _

/-- Differences of raw carried flow derivatives have integrable complete absolute sum. -/
theorem integrable_rengerDirectionalFlowHybridBVFlowDistance
    (path mean : RengerDirectionalFlowHybridBVPath State duration) :
    Integrable (fun time ↦ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |rengerDirectionalFlowHybridBVFlowDerivative path time transition -
        rengerDirectionalFlowHybridBVFlowDerivative mean time transition|)
      (finiteOpenIntervalVolume duration) := by
  exact integrable_finsetSum Finset.univ fun transition _hTransition ↦
    ((integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition).sub
      (integrable_rengerDirectionalFlowHybridBVFlowDerivative mean transition)).abs

private theorem sum_ordered_abs_mul_rate_le
    (generator : FiniteStateMarkovGenerator State) (error : State → ℝ)
    (escapeBound : ℝ) (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |error transition.1.1| * (generator.rate transition.1.1 transition.1.2 : ℝ)) ≤
      escapeBound * ∑ state, |error state| := by
  rw [← sum_sum_eq_sum_ordered_of_diagonal_zero
    (fun source target ↦ |error source| * (generator.rate source target : ℝ))
    (fun state ↦ by simp [generator.rate_self]), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro source _hSource
  rw [← Finset.mul_sum, mul_comm escapeBound]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [FiniteStateMarkovGenerator.escapeRate, NNReal.coe_sum] using hEscape source

/-- Same-generator transport controls the complete actual flow-derivative distance. The explicit
escape bound is multiplied by the original physical duration, with no positivity assumption. -/
theorem rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (escapeBound : ℝ) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    rengerDirectionalFlowHybridBVIntegratedFlowDistance path.1 mean.1 ≤
      (duration * escapeBound) *
          (∑ state, |path.1.initialTrace (Sum.inl state) -
            mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 := by
  let initial := ∑ state, |path.1.initialTrace (Sum.inl state) -
    mean.1.initialTrace (Sum.inl state)|
  let residual := rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1
  let integrand := fun time ↦ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    |rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
      rengerDirectionalFlowHybridBVDensityValue path.1 time transition.1.1 *
        (generator.rate transition.1.1 transition.1.2 : ℝ)|
  have hPointwise : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        |rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
          rengerDirectionalFlowHybridBVFlowDerivative mean.1 time transition|) ≤
        integrand time + escapeBound * (initial + 2 * residual) := by
    filter_upwards [(rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw
      generator hDuration mean.2).mp hMeanFlow,
      ae_restrict_mem measurableSet_Ioo] with time hMean hTime
    let error := fun state ↦ rengerDirectionalFlowHybridBVDensityValue path.1 time state -
      rengerDirectionalFlowHybridBVDensityValue mean.1 time state
    calc
      _ ≤ integrand time +
          ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
            |error transition.1.1| *
              (generator.rate transition.1.1 transition.1.2 : ℝ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro transition _hTransition
        rw [hMean transition]
        calc
          _ = |(rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
              rengerDirectionalFlowHybridBVDensityValue path.1 time transition.1.1 *
                (generator.rate transition.1.1 transition.1.2 : ℝ)) +
              error transition.1.1 *
                (generator.rate transition.1.1 transition.1.2 : ℝ)| := by
            congr 1
            dsimp only [error]
            ring
          _ ≤ _ := by
            simpa only [abs_mul, abs_of_nonneg (generator.rate _ _).coe_nonneg] using
              abs_add_le
                (rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
                  rengerDirectionalFlowHybridBVDensityValue path.1 time transition.1.1 *
                    (generator.rate transition.1.1 transition.1.2 : ℝ))
                (error transition.1.1 *
                  (generator.rate transition.1.1 transition.1.2 : ℝ))
      _ ≤ integrand time + escapeBound * ∑ state, |error state| :=
        add_le_add le_rfl (sum_ordered_abs_mul_rate_le generator error escapeBound hEscape)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual
          generator hDuration path mean hMeanFlow ⟨hTime.1.le, hTime.2⟩)
        hEscapeNonnegative)
  have hBound := integral_mono_ae
    (integrable_rengerDirectionalFlowHybridBVFlowDistance path.1 mean.1)
    ((integrable_rengerDirectionalFlowHybridBVFlowResidual generator path.1).add
      (integrable_const (escapeBound * (initial + 2 * residual)))) hPointwise
  simp only [Pi.add_apply] at hBound
  rw [integral_add
    (integrable_rengerDirectionalFlowHybridBVFlowResidual generator path.1)
    (integrable_const (escapeBound * (initial + 2 * residual))), integral_const] at hBound
  simp only [measureReal_def, finiteOpenIntervalVolume_apply_univ,
    ENNReal.toReal_ofReal hDuration.le, smul_eq_mul] at hBound
  change rengerDirectionalFlowHybridBVIntegratedFlowDistance path.1 mean.1 ≤ _ at hBound
  change rengerDirectionalFlowHybridBVIntegratedFlowDistance path.1 mean.1 ≤
    (duration * escapeBound) * initial + (1 + 2 * (duration * escapeBound)) * residual
  change _ ≤ residual + duration * (escapeBound * (initial + 2 * residual)) at hBound
  nlinarith [hBound]

/-- Cumulative ordered-flow error is controlled by the complete actual derivative L1 distance.
Both cumulative flows begin at the admissibly recovered zero trace. -/
theorem sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_integratedFlowDistance
    (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |rengerDirectionalFlowHybridBVCumulativeFlowValue path.1 time transition -
        rengerDirectionalFlowHybridBVCumulativeFlowValue mean.1 time transition|) ≤
      rengerDirectionalFlowHybridBVIntegratedFlowDistance path.1 mean.1 := by
  let measure := (finiteOpenIntervalVolume duration).restrict (Ioc 0 time)
  have hIntegrable (transition : FiniteStateOrderedOffDiagonalTransition State) :
      Integrable (fun point ↦
        rengerDirectionalFlowHybridBVFlowDerivative path.1 point transition -
          rengerDirectionalFlowHybridBVFlowDerivative mean.1 point transition) measure :=
    ((integrable_rengerDirectionalFlowHybridBVFlowDerivative path.1 transition).sub
      (integrable_rengerDirectionalFlowHybridBVFlowDerivative mean.1 transition)).restrict
  have hPrimitive (transition : FiniteStateOrderedOffDiagonalTransition State) :
      rengerDirectionalFlowHybridBVCumulativeFlowValue path.1 time transition -
          rengerDirectionalFlowHybridBVCumulativeFlowValue mean.1 time transition =
        ∫ point, (rengerDirectionalFlowHybridBVFlowDerivative path.1 point transition -
          rengerDirectionalFlowHybridBVFlowDerivative mean.1 point transition) ∂measure := by
    unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rw [path.1.cadlagRepresentative_eq_initial_add_integral_derivativeDensity
        path.2.absolutelyContinuousDerivative (Sum.inr transition) hTime.1 hTime.2,
      mean.1.cadlagRepresentative_eq_initial_add_integral_derivativeDensity
        mean.2.absolutelyContinuousDerivative (Sum.inr transition) hTime.1 hTime.2]
    change path.1.initialTrace (Sum.inr transition) + _ -
      (mean.1.initialTrace (Sum.inr transition) + _) = _
    rw [path.2.cumulativeFlowInitiallyZero, mean.2.cumulativeFlowInitiallyZero,
      zero_add, zero_add, integral_sub]
    · rfl
    · exact (integrable_rengerDirectionalFlowHybridBVFlowDerivative path.1 transition).restrict
    · exact (integrable_rengerDirectionalFlowHybridBVFlowDerivative mean.1 transition).restrict
  calc
    _ ≤ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ∫ point, |rengerDirectionalFlowHybridBVFlowDerivative path.1 point transition -
          rengerDirectionalFlowHybridBVFlowDerivative mean.1 point transition| ∂measure := by
      apply Finset.sum_le_sum
      intro transition _hTransition
      rw [hPrimitive]
      exact abs_integral_le_integral_abs
    _ = ∫ point, ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        |rengerDirectionalFlowHybridBVFlowDerivative path.1 point transition -
          rengerDirectionalFlowHybridBVFlowDerivative mean.1 point transition| ∂measure := by
      rw [integral_finsetSum]
      exact fun transition _hTransition ↦ (hIntegrable transition).abs
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _point ↦ Finset.sum_nonneg
        fun _transition _hTransition ↦ abs_nonneg _)
      (integrable_rengerDirectionalFlowHybridBVFlowDistance path.1 mean.1)

/-- The cumulative ordered-flow estimate with the physical escape budget `T * L`. -/
theorem sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (escapeBound : ℝ) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |rengerDirectionalFlowHybridBVCumulativeFlowValue path.1 time transition -
        rengerDirectionalFlowHybridBVCumulativeFlowValue mean.1 time transition|) ≤
      (duration * escapeBound) *
          (∑ state, |path.1.initialTrace (Sum.inl state) -
            mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 :=
  (sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_integratedFlowDistance
    hDuration path mean hTime).trans
    (rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_residual
      generator hDuration path mean hMeanFlow escapeBound hEscapeNonnegative hEscape)

private theorem sum_abs_terminalTrace_sub_le
    {Index : Type*} [Fintype Index]
    (hDuration : 0 < duration) (path mean : RengerDirectionalFlowHybridBVPath State duration)
    (coordinate : Index → EmpiricalDensityDirectionalFlowCoordinate State) (bound : ℝ)
    (hBound : ∀ time ∈ Ico 0 duration,
      (∑ index, |path.cadlagRepresentative.representative time (coordinate index) -
        mean.cadlagRepresentative.representative time (coordinate index)|) ≤ bound) :
    (∑ index, |path.terminalTrace hDuration (coordinate index) -
      mean.terminalTrace hDuration (coordinate index)|) ≤ bound := by
  have hLimit : Tendsto (fun time ↦ ∑ index,
      |path.cadlagRepresentative.representative time (coordinate index) -
        mean.cadlagRepresentative.representative time (coordinate index)|)
      (𝓝[<] duration) (𝓝 (∑ index,
        |path.terminalTrace hDuration (coordinate index) -
          mean.terminalTrace hDuration (coordinate index)|)) := by
    exact tendsto_finsetSum Finset.univ fun index _hIndex ↦
      (((PiLp.continuous_apply 1 (fun _ : EmpiricalDensityDirectionalFlowCoordinate State ↦ ℝ)
        (coordinate index)).tendsto _ |>.comp
        (path.tendsto_terminalTrace hDuration)).sub
      ((PiLp.continuous_apply 1 (fun _ : EmpiricalDensityDirectionalFlowCoordinate State ↦ ℝ)
        (coordinate index)).tendsto _ |>.comp
        (mean.tendsto_terminalTrace hDuration))).abs
  apply le_of_tendsto hLimit
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Ici_mem_nhds hDuration)] with time hUpper hLower
  exact hBound time ⟨hLower, hUpper⟩

/-- The density stability estimate passes to the separately recovered terminal left trace. -/
theorem sum_abs_rengerDirectionalFlowHybridBVTerminalDensity_sub_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1) :
    (∑ state, |path.1.terminalTrace hDuration (Sum.inl state) -
      mean.1.terminalTrace hDuration (Sum.inl state)|) ≤
      (∑ state, |path.1.initialTrace (Sum.inl state) -
        mean.1.initialTrace (Sum.inl state)|) +
      2 * rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 := by
  apply sum_abs_terminalTrace_sub_le hDuration path.1 mean.1 Sum.inl
  intro time hTime
  exact sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual
    generator hDuration path mean hMeanFlow hTime

/-- Cumulative ordered-flow error at the terminal left trace retains the original physical
escape budget and the same complete residual. -/
theorem sum_abs_rengerDirectionalFlowHybridBVTerminalFlow_sub_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (escapeBound : ℝ) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      |path.1.terminalTrace hDuration (Sum.inr transition) -
        mean.1.terminalTrace hDuration (Sum.inr transition)|) ≤
      (duration * escapeBound) *
          (∑ state, |path.1.initialTrace (Sum.inl state) -
            mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1 := by
  apply sum_abs_terminalTrace_sub_le hDuration path.1 mean.1 Sum.inr
  intro time hTime
  exact sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_initial_add_residual
    generator hDuration path mean hMeanFlow escapeBound hEscapeNonnegative hEscape hTime

omit [DecidableEq State] in
private theorem sum_abs_flowDivergence_le (flow : State → State → ℝ) :
    (∑ state, |finiteStateFlowDivergence flow state|) ≤
      2 * ∑ source, ∑ target, |flow source target| := by
  calc
    _ ≤ ∑ state, ((∑ source, |flow source state|) + ∑ target, |flow state target|) := by
      apply Finset.sum_le_sum
      intro state _hState
      exact (abs_sub _ _).trans (add_le_add
        (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      ring

private theorem integrable_derivativeDensity_sub
    (path mean : RengerDirectionalFlowHybridBVPath State duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    Integrable (fun time ↦ path.derivativeDensity coordinate time -
      mean.derivativeDensity coordinate time) (finiteOpenIntervalVolume duration) :=
  (SignedMeasure.integrable_rnDeriv _ _).sub (SignedMeasure.integrable_rnDeriv _ _)

/-- The sum of absolute density-derivative errors costs at most twice the full ordered-flow
derivative error, because both admissible paths obey the carried continuity equation. -/
theorem ae_sum_abs_rengerDirectionalFlowHybridBVDensityDerivative_sub_le
    (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (∑ state, |rengerDirectionalFlowHybridBVDensityDerivative path.1 time state -
        rengerDirectionalFlowHybridBVDensityDerivative mean.1 time state|) ≤
        2 * ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          |rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
            rengerDirectionalFlowHybridBVFlowDerivative mean.1 time transition| := by
  filter_upwards [path.2.continuityEquationAE, mean.2.continuityEquationAE]
    with time hPath hMean
  let flow := fun source target ↦
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue path.1 time source target -
      rengerDirectionalFlowHybridBVRawFlowDerivativeValue mean.1 time source target
  have hDrift (state : State) :
      rengerDirectionalFlowHybridBVDensityDerivative path.1 time state -
        rengerDirectionalFlowHybridBVDensityDerivative mean.1 time state =
      finiteStateFlowDivergence flow state := by
    rw [hPath state, hMean state]
    change rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state -
      rengerDirectionalFlowHybridBVTargetFlowDivergence mean.1 time state = _
    rw [rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence,
      rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence]
    unfold finiteStateFlowDivergence
    simp only [flow, Finset.sum_sub_distrib]
    ring
  simp_rw [hDrift]
  convert sum_abs_flowDivergence_le flow using 1
  congr 1
  rw [sum_sum_eq_sum_ordered_of_diagonal_zero (fun source target ↦ |flow source target|)
    (fun state ↦ by simp [flow, rengerDirectionalFlowHybridBVRawFlowDerivativeValue])]
  apply Finset.sum_congr rfl
  intro transition _hTransition
  simp only [flow, rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
    dite_eq_left transition.2]

/-- One actual carried signed derivative difference has total-variation mass equal to the
integrated absolute difference of its raw RN densities. -/
theorem rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_eq_integral
    (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (((path.1.toDerivativePath.derivative coordinate).toSignedMeasure -
      (mean.1.toDerivativePath.derivative coordinate).toSignedMeasure).totalVariation univ).toReal =
      ∫ time, |path.1.derivativeDensity coordinate time -
        mean.1.derivativeDensity coordinate time| ∂finiteOpenIntervalVolume duration := by
  rw [← path.1.withDensity_derivativeDensity_eq_derivative
      path.2.absolutelyContinuousDerivative coordinate,
    ← mean.1.withDensity_derivativeDensity_eq_derivative
      mean.2.absolutelyContinuousDerivative coordinate,
    ← withDensityᵥ_sub' (f := path.1.derivativeDensity coordinate)
      (g := mean.1.derivativeDensity coordinate)
      (SignedMeasure.integrable_rnDeriv _ _) (SignedMeasure.integrable_rnDeriv _ _)]
  rw [SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs
    (density := fun time ↦ path.1.derivativeDensity coordinate time -
      mean.1.derivativeDensity coordinate time)
    ((path.1.measurable_derivativeDensity coordinate).sub
      (mean.1.measurable_derivativeDensity coordinate))
    (integrable_derivativeDensity_sub path.1 mean.1 coordinate)]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _time ↦ abs_nonneg _)
    (integrable_derivativeDensity_sub path.1 mean.1 coordinate).abs.aestronglyMeasurable).symm

/-- Complete carried derivative variation costs at most three times the actual integrated
ordered-flow error: twice for density divergence and once for the flow coordinates themselves. -/
theorem sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_integratedFlowDistance
    (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    (∑ coordinate : EmpiricalDensityDirectionalFlowCoordinate State,
      (((path.1.toDerivativePath.derivative coordinate).toSignedMeasure -
        (mean.1.toDerivativePath.derivative coordinate).toSignedMeasure).totalVariation
          univ).toReal) ≤
      3 * rengerDirectionalFlowHybridBVIntegratedFlowDistance path.1 mean.1 := by
  simp_rw [rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_eq_integral
    hDuration path mean]
  rw [← integral_finsetSum]
  · calc
      _ ≤ ∫ time, 3 * ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          |rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
            rengerDirectionalFlowHybridBVFlowDerivative mean.1 time transition|
          ∂finiteOpenIntervalVolume duration := by
        apply integral_mono_ae
          (integrable_finsetSum Finset.univ fun coordinate _hCoordinate ↦
            (integrable_derivativeDensity_sub path.1 mean.1 coordinate).abs)
          ((integrable_rengerDirectionalFlowHybridBVFlowDistance path.1 mean.1).const_mul 3)
        filter_upwards [ae_sum_abs_rengerDirectionalFlowHybridBVDensityDerivative_sub_le
          hDuration path mean] with time hBound
        rw [Fintype.sum_sum_type]
        change (∑ state, |rengerDirectionalFlowHybridBVDensityDerivative path.1 time state -
          rengerDirectionalFlowHybridBVDensityDerivative mean.1 time state|) +
          (∑ transition, |rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition -
            rengerDirectionalFlowHybridBVFlowDerivative mean.1 time transition|) ≤ _
        linarith
      _ = _ := integral_const_mul _ _
  · exact fun coordinate _hCoordinate ↦
      (integrable_derivativeDensity_sub path.1 mean.1 coordinate).abs

/-- Complete actual carried derivative variation is controlled by the initial density error
and the fixed-generator residual, with the conservative factor three. -/
theorem sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (escapeBound : ℝ) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    (∑ coordinate : EmpiricalDensityDirectionalFlowCoordinate State,
      (((path.1.toDerivativePath.derivative coordinate).toSignedMeasure -
        (mean.1.toDerivativePath.derivative coordinate).toSignedMeasure).totalVariation
          univ).toReal) ≤
      3 * ((duration * escapeBound) *
          (∑ state, |path.1.initialTrace (Sum.inl state) -
            mean.1.initialTrace (Sum.inl state)|) +
        (1 + 2 * (duration * escapeBound)) *
          rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1) :=
  (sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_integratedFlowDistance
    hDuration path mean).trans (mul_le_mul_of_nonneg_left
      (rengerDirectionalFlowHybridBVIntegratedFlowDistance_le_initial_add_residual
        generator hDuration path mean hMeanFlow escapeBound hEscapeNonnegative hEscape)
      (by norm_num))

/-- The difference of the existing strong-L1 projections is bounded by the physical duration
times the uniform density and cumulative-flow estimates. -/
theorem norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_residual
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (path mean : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hMeanFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator mean.1)
    (escapeBound : ℝ) (hEscapeNonnegative : 0 ≤ escapeBound)
    (hEscape : ∀ state, (generator.escapeRate state : ℝ) ≤ escapeBound) :
    ‖path.1.toDerivativePath.toL1Path - mean.1.toDerivativePath.toL1Path‖ ≤
      duration * ((1 + duration * escapeBound) *
          (∑ state, |path.1.initialTrace (Sum.inl state) -
            mean.1.initialTrace (Sum.inl state)|) +
        (3 + 2 * (duration * escapeBound)) *
          rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1) := by
  let initial := ∑ state, |path.1.initialTrace (Sum.inl state) -
    mean.1.initialTrace (Sum.inl state)|
  let residual := rengerDirectionalFlowHybridBVIntegratedFlowResidual generator path.1
  let bound := (1 + duration * escapeBound) * initial +
    (3 + 2 * (duration * escapeBound)) * residual
  let difference := path.1.toDerivativePath.toL1Path - mean.1.toDerivativePath.toL1Path
  obtain ⟨hPathMem, hPathRep⟩ := path.1.cadlagRepresentative.represents
  obtain ⟨hMeanMem, hMeanRep⟩ := mean.1.cadlagRepresentative.represents
  have hPathAE : (path.1.toDerivativePath.toL1Path :
      ℝ → FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State)) =ᵐ[
        finiteOpenIntervalVolume duration] path.1.cadlagRepresentative.representative := by
    have hCoefficient := hPathMem.coeFn_toLp
    rw [hPathRep] at hCoefficient
    exact hCoefficient
  have hMeanAE : (mean.1.toDerivativePath.toL1Path :
      ℝ → FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State)) =ᵐ[
        finiteOpenIntervalVolume duration] mean.1.cadlagRepresentative.representative := by
    have hCoefficient := hMeanMem.coeFn_toLp
    rw [hMeanRep] at hCoefficient
    exact hCoefficient
  have hBound : ∀ᵐ time ∂finiteOpenIntervalVolume duration, ‖difference time‖ ≤ bound := by
    filter_upwards [Lp.coeFn_sub path.1.toDerivativePath.toL1Path
      mean.1.toDerivativePath.toL1Path, hPathAE, hMeanAE,
      ae_restrict_mem measurableSet_Ioo] with time hSub hPath hMean hTime
    change ‖(path.1.toDerivativePath.toL1Path - mean.1.toDerivativePath.toL1Path) time‖ ≤ bound
    rw [hSub, Pi.sub_apply, hPath, hMean, PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    have hDensity :=
      sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual
        generator hDuration path mean hMeanFlow ⟨hTime.1.le, hTime.2⟩
    have hFlow :=
      sum_abs_rengerDirectionalFlowHybridBVCumulativeFlowValue_sub_le_initial_add_residual
        generator hDuration path mean hMeanFlow escapeBound hEscapeNonnegative hEscape
        ⟨hTime.1.le, hTime.2⟩
    change (∑ state, |rengerDirectionalFlowHybridBVDensityValue path.1 time state -
      rengerDirectionalFlowHybridBVDensityValue mean.1 time state|) +
      (∑ transition, |rengerDirectionalFlowHybridBVCumulativeFlowValue path.1 time transition -
        rengerDirectionalFlowHybridBVCumulativeFlowValue mean.1 time transition|) ≤ bound
    dsimp only [bound, initial, residual]
    nlinarith [hDensity, hFlow]
  have hIntegral := integral_mono_ae (L1.integrable_coeFn difference).norm
    (integrable_const bound) hBound
  rw [← L1.norm_eq_integral_norm, integral_const] at hIntegral
  simp only [measureReal_def, finiteOpenIntervalVolume_apply_univ,
    ENNReal.toReal_ofReal hDuration.le, smul_eq_mul] at hIntegral
  exact hIntegral

end

end FiniteMarkovProcesses.InformationTheory
