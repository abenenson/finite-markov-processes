/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateCoercivity
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRepresentationDomain

/-!
# Event coercivity from the Renger hybrid-BV directional-flow rate

This module strengthens the unit-exponent coercivity estimate to every nonnegative exponential
test and localizes it to measurable time events.  The resulting estimate is the quantitative
input for excluding derivative mass that concentrates at the open temporal boundary.

The observation carrier remains the total hybrid-BV space.  Finite-rate and zero-start
hypotheses enter only through the named representation domain; no globally continuous endpoint
trace or independently invented boundary penalty is asserted.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The pathwise reference-rate correction at an arbitrary exponential test scale. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
    (generator : FiniteStateMarkovGenerator State) (exponent : ℝ)
    (path : RengerDirectionalFlowHybridBVPath State duration) (time : ℝ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ENNReal.ofReal ((Real.exp exponent - 1) *
      (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
        generator.rate transition.1.1 transition.1.2 : NNReal))

/-- The path-independent generator correction at an arbitrary exponential test scale. -/
noncomputable def rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent
    (generator : FiniteStateMarkovGenerator State) (exponent : ℝ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ENNReal.ofReal ((Real.exp exponent - 1) *
      (generator.rate transition.1.1 transition.1.2 : ℝ))

/-- Every finite-state generator correction at a finite exponential scale is finite. -/
theorem rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent_ne_top
    (generator : FiniteStateMarkovGenerator State) (exponent : ℝ) :
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent ≠ ∞ := by
  simp [rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent]

/-- A finite extended level divided by a sufficiently large positive finite scale is below any
prescribed positive extended tolerance. -/
theorem exists_nnreal_exponent_level_div_le
    {level epsilon : ENNReal} (hLevel : level ≠ ∞) (hEpsilon : 0 < epsilon) :
    ∃ exponent : NNReal, 0 < exponent ∧ level / (exponent : ENNReal) ≤ epsilon := by
  have hDiv : Tendsto
      (fun natural : ℕ => level / ((natural + 1 : ℕ) : ENNReal)) atTop (𝓝 0) := by
    rw [← ENNReal.coe_toNNReal hLevel]
    have hNNReal : Tendsto
        (fun natural : ℕ => level.toNNReal / (natural + 1 : ℕ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat level.toNNReal).comp
        (tendsto_add_atTop_nat 1)
    simpa [ENNReal.coe_div] using ENNReal.tendsto_coe.mpr hNNReal
  obtain ⟨natural, hNatural⟩ :=
    (ENNReal.tendsto_nhds_zero.mp hDiv epsilon hEpsilon).exists
  exact ⟨natural + 1, by positivity, by simpa using hNatural⟩

/-- Aggregate ordered-flow derivative variation carried by a measurable time event. -/
noncomputable def rengerDirectionalFlowHybridBVFlowDerivativeVariationOn
    (path : RengerDirectionalFlowHybridBVPath State duration) (event : Set ℝ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation event

/-- Aggregate density derivative variation carried by a measurable time event. -/
noncomputable def rengerDirectionalFlowHybridBVDensityDerivativeVariationOn
    (path : RengerDirectionalFlowHybridBVPath State duration) (event : Set ℝ) : ENNReal :=
  ∑ state,
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.totalVariation event

/-- Complete density-plus-flow derivative variation carried by a measurable time event. -/
noncomputable def rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
    (path : RengerDirectionalFlowHybridBVPath State duration) (event : Set ℝ) : ENNReal :=
  rengerDirectionalFlowHybridBVDensityDerivativeVariationOn path event +
    rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event

/-- At any nonnegative exponential scale, the extended Poisson cost controls the scaled observed
flow up to the corresponding reference-rate correction. -/
theorem exponent_mul_flow_le_rengerExtendedPoissonRateCost_add_referenceCorrection
    (flow expected : NNReal) {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    ENNReal.ofReal (exponent * (flow : ℝ)) ≤
      rengerExtendedPoissonRateCost flow expected +
        ENNReal.ofReal ((Real.exp exponent - 1) * (expected : ℝ)) := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · simp [rengerExtendedPoissonRateCost, hFlow]
  have hExpectedPos : 0 < expected := pos_iff_ne_zero.mpr hExpected
  have hDiscriminationNonnegative :
      0 ≤ poissonRateDiscrimination (flow : ℝ) (expected : ℝ) :=
    poissonRateDiscrimination_nonneg (by positivity) (by exact_mod_cast hExpectedPos)
  have hExp : 1 ≤ Real.exp exponent := by
    nlinarith [Real.add_one_le_exp exponent]
  have hCorrectionNonnegative :
      0 ≤ (Real.exp exponent - 1) * (expected : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hExp) (by positivity)
  rw [rengerExtendedPoissonRateCost_of_expected_pos flow hExpectedPos,
    ← ENNReal.ofReal_add hDiscriminationNonnegative hCorrectionNonnegative]
  exact ENNReal.ofReal_le_ofReal (by
    have hFenchel := poissonExponentialDualEvaluation_le_discrimination
      (exponent := exponent)
      (show 0 ≤ (flow : ℝ) by positivity)
      (show 0 < (expected : ℝ) by exact_mod_cast hExpectedPos)
    linarith)

/-- Finite-channel coercivity at an arbitrary nonnegative exponential scale. -/
theorem exponent_mul_totalFlow_le_rengerDirectionalFlowLocalRateRaw_add_referenceCorrection
    (generator : FiniteStateMarkovGenerator State)
    (density : State → NNReal)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    ENNReal.ofReal exponent *
        ∑ transition, (directionalFlowDerivative transition : ENNReal) ≤
      rengerDirectionalFlowLocalRateRaw generator density directionalFlowDerivative +
        ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ENNReal.ofReal ((Real.exp exponent - 1) *
            (density transition.1.1 *
              generator.rate transition.1.1 transition.1.2 : NNReal)) := by
  unfold rengerDirectionalFlowLocalRateRaw
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro transition _hTransition
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hExponent]
  exact exponent_mul_flow_le_rengerExtendedPoissonRateCost_add_referenceCorrection
    _ _ hExponent

/-- Pointwise arbitrary-exponent coercivity along a hybrid path. -/
theorem rengerDirectionalFlowHybridBVExponentMulTotalFlowIntegrand_le_localRate_add_correction
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    ENNReal.ofReal exponent * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time ≤
      rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) +
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
          generator exponent path time := by
  exact exponent_mul_totalFlow_le_rengerDirectionalFlowLocalRateRaw_add_referenceCorrection
    generator (rengerDirectionalFlowHybridBVDensityAt path time)
      (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) hExponent

/-- The arbitrary-exponent pathwise reference correction is almost-everywhere measurable. -/
theorem aemeasurable_rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
    (generator : FiniteStateMarkovGenerator State) (exponent : ℝ)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    AEMeasurable
        (rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
          generator exponent path)
        (finiteOpenIntervalVolume duration) := by
  unfold rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
  apply Finset.aemeasurable_fun_sum
  intro transition _hTransition
  have hDensity : AEMeasurable
      (fun time => rengerDirectionalFlowHybridBVDensityAt path time transition.1.1)
      (finiteOpenIntervalVolume duration) :=
    (measurable_pi_apply transition.1.1).comp_aemeasurable
      (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path)
  have hExpected : AEMeasurable
      (fun time => rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
        generator.rate transition.1.1 transition.1.2)
      (finiteOpenIntervalVolume duration) :=
    hDensity.mul aemeasurable_const
  exact (aemeasurable_const.mul hExpected.coe_nnreal_real).ennreal_ofReal

/-- On the admissible simplex domain, the arbitrary-exponent correction is bounded almost
everywhere by its path-independent generator constant. -/
theorem
    rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent_le_generatorCorrection_ae
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
          generator exponent path time ≤
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent := by
  filter_upwards [rengerDirectionalFlowHybridBVDensityAt_le_one_ae hDuration hPath]
    with time hDensity
  unfold rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent
  apply Finset.sum_le_sum
  intro transition _hTransition
  apply ENNReal.ofReal_le_ofReal
  have hExpected :
      rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
          generator.rate transition.1.1 transition.1.2 ≤
        generator.rate transition.1.1 transition.1.2 := by
    simpa only [one_mul] using mul_le_mul_left
      (hDensity transition.1.1) (generator.rate transition.1.1 transition.1.2)
  have hExp : 0 ≤ Real.exp exponent - 1 := by
    nlinarith [Real.add_one_le_exp exponent]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hExpected) hExp

/-- Restricting time to a measurable event scales the arbitrary-exponent correction by the
event's physical-time volume, not by the whole horizon. -/
theorem
    rengerDirectionalFlowHybridBVReferenceCorrectionIntegralOn_le_generatorCorrection_mul_volume
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) (event : Set ℝ) :
    (∫⁻ time in event,
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
          generator exponent path time ∂finiteOpenIntervalVolume duration) ≤
      rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
        finiteOpenIntervalVolume duration event := by
  have hCorrectionBound :=
    rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent_le_generatorCorrection_ae
      generator hDuration hPath hExponent
  calc
    (∫⁻ time in event,
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
          generator exponent path time ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ _time in event,
          rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent
          ∂finiteOpenIntervalVolume duration := by
      apply lintegral_mono_ae
      exact ae_mono Measure.restrict_le_self hCorrectionBound
    _ = rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
        finiteOpenIntervalVolume duration event := by
      rw [setLIntegral_const]

/-- Event-local coercivity: at every nonnegative exponential scale, the scaled one-way flow on
an arbitrary time event is controlled by the complete dynamic rate plus a correction proportional
to that event's physical-time volume. -/
theorem rengerDirectionalFlowHybridBVExponentMulTotalFlowIntegralOn_le_dynamicRate_add_correction
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {exponent : ℝ} (hExponent : 0 ≤ exponent) (event : Set ℝ) :
    ENNReal.ofReal exponent *
        (∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration) ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event := by
  have hCorrectionIntegral :=
    rengerDirectionalFlowHybridBVReferenceCorrectionIntegralOn_le_generatorCorrection_mul_volume
      generator hDuration hPath hExponent event
  calc
    ENNReal.ofReal exponent *
        (∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration) =
        ∫⁻ time in event,
          ENNReal.ofReal exponent * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration := by
      rw [lintegral_const_mul _
        (measurable_rengerDirectionalFlowHybridBVTotalFlowIntegrand path)]
    _ ≤ ∫⁻ time in event,
        rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) +
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
            generator exponent path time ∂finiteOpenIntervalVolume duration := by
      apply lintegral_mono
      intro time
      exact
        rengerDirectionalFlowHybridBVExponentMulTotalFlowIntegrand_le_localRate_add_correction
          generator path time hExponent
    _ = (∫⁻ time in event,
          rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)
          ∂finiteOpenIntervalVolume duration) +
        ∫⁻ time in event,
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrandAtExponent
            generator exponent path time ∂finiteOpenIntervalVolume duration := by
      rw [lintegral_add_left'
        ((aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path).mono_measure
          Measure.restrict_le_self)]
    _ ≤ (∫⁻ time,
          rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)
          ∂finiteOpenIntervalVolume duration) +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event := by
      exact add_le_add
        (by
          simpa only [setLIntegral_univ] using
            (lintegral_mono_set (μ := finiteOpenIntervalVolume duration)
              (f := fun time =>
                rengerDirectionalFlowLocalRateRaw generator
                  (rengerDirectionalFlowHybridBVDensityAt path time)
                  (rengerDirectionalFlowHybridBVFlowDerivativeAt path time))
              (Set.subset_univ event)))
        hCorrectionIntegral
    _ = rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event := by
      rw [rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible generator hDuration hPath]

/-- Explicit event-local modulus for every finite action sublevel.  Increasing the exponential
scale suppresses the uniform action contribution; shrinking the event suppresses the finite
generator contribution. -/
theorem rengerDirectionalFlowHybridBVTotalFlowIntegralOn_le_finiteRateSublevelModulus
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {level : ENNReal}
    (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤ level)
    {exponent : NNReal} (hExponent : 0 < exponent) (event : Set ℝ) :
    (∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration) ≤
      (level +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event) / (exponent : ENNReal) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.coe_ne_zero.mpr hExponent.ne'))
    (Or.inl ENNReal.coe_ne_top)).2
  rw [mul_comm]
  calc
    (exponent : ENNReal) *
        (∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration) =
        ENNReal.ofReal (exponent : ℝ) *
          (∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
            ∂finiteOpenIntervalVolume duration) := by simp
    _ ≤ rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event :=
      rengerDirectionalFlowHybridBVExponentMulTotalFlowIntegralOn_le_dynamicRate_add_correction
        generator hDuration hPath exponent.coe_nonneg event
    _ ≤ level +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event := add_le_add hRate le_rfl

/-- On a measurable event, an admissible ordered-flow derivative has variation equal to the
restricted integral of its nonnegative Radon--Nikodym density. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_apply
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {event : Set ℝ} (hEvent : MeasurableSet event)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
        event =
      ∫⁻ time in event,
        (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal)
        ∂finiteOpenIntervalVolume duration := by
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hPath.absolutelyContinuousDerivative (Sum.inr transition)]
  change SignedMeasure.totalVariation
      ((finiteOpenIntervalVolume duration).withDensityᵥ
        ((path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.rnDeriv
          (finiteOpenIntervalVolume duration))) event = _
  rw [SignedMeasure.totalVariation_withDensityᵥ_apply_eq_setLIntegral
    (SignedMeasure.integrable_rnDeriv _ _)
    (hPath.flowDerivativeNonnegativeAE.mono fun time hTime => hTime transition) hEvent]
  rfl

/-- Aggregate ordered-flow variation on a measurable event is exactly its restricted total-flow
integral. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_eq_totalFlowIntegralOn
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {event : Set ℝ} (hEvent : MeasurableSet event) :
    rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event =
      ∫⁻ time in event, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeVariationOn
    rengerDirectionalFlowHybridBVTotalFlowIntegrand
  rw [lintegral_finsetSum']
  · apply Finset.sum_congr rfl
    intro transition _hTransition
    exact rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_apply
      hDuration hPath hEvent transition
  · intro transition _hTransition
    exact ((measurable_real_toNNReal.comp
      (path.measurable_derivativeDensity (Sum.inr transition))).coe_nnreal_ennreal.aemeasurable
        |>.mono_measure Measure.restrict_le_self)

/-- On a measurable event, an admissible density derivative has variation equal to the
restricted integral of the absolute Radon--Nikodym density. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeVariationOn_apply
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {event : Set ℝ} (hEvent : MeasurableSet event) (state : State) :
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.totalVariation event =
      ∫⁻ time in event,
        ENNReal.ofReal |rengerDirectionalFlowHybridBVDensityDerivative path time state|
        ∂finiteOpenIntervalVolume duration := by
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hPath.absolutelyContinuousDerivative (Sum.inl state)]
  change SignedMeasure.totalVariation
      ((finiteOpenIntervalVolume duration).withDensityᵥ
        ((path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.rnDeriv
          (finiteOpenIntervalVolume duration))) event = _
  simpa only [rengerDirectionalFlowHybridBVDensityDerivative,
    FiniteIntervalHybridBVPath.derivativeDensity] using
    SignedMeasure.totalVariation_withDensityᵥ_apply_eq_setLIntegral_ofReal_abs
      (path.measurable_derivativeDensity (Sum.inl state))
      (SignedMeasure.integrable_rnDeriv
        (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
        (finiteOpenIntervalVolume duration)) hEvent

/-- Aggregate density variation on a measurable event is controlled by twice the ordered-flow
variation on that same event. -/
theorem
    rengerDirectionalFlowHybridBVDensityDerivativeVariationOn_le_two_mul_flowDerivativeVariationOn
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {event : Set ℝ} (hEvent : MeasurableSet event) :
    rengerDirectionalFlowHybridBVDensityDerivativeVariationOn path event ≤
      2 * rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event := by
  have hDensityDerivativeBound :=
    rengerDirectionalFlowHybridBVDensityDerivativeAbsoluteSum_le_two_mul_totalFlowIntegrand_ae
      hDuration hPath
  unfold rengerDirectionalFlowHybridBVDensityDerivativeVariationOn
  rw [show
    (∑ state,
      (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.totalVariation event) =
      ∑ state, ∫⁻ time in event,
        ENNReal.ofReal |rengerDirectionalFlowHybridBVDensityDerivative path time state|
        ∂finiteOpenIntervalVolume duration by
      apply Finset.sum_congr rfl
      intro state _hState
      exact rengerDirectionalFlowHybridBVDensityDerivativeVariationOn_apply
        hDuration hPath hEvent state]
  rw [← lintegral_finsetSum']
  · rw [rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_eq_totalFlowIntegralOn
      hDuration hPath hEvent]
    calc
      (∫⁻ time in event, ∑ state,
          ENNReal.ofReal |rengerDirectionalFlowHybridBVDensityDerivative path time state|
          ∂finiteOpenIntervalVolume duration) ≤
          ∫⁻ time in event,
            2 * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
            ∂finiteOpenIntervalVolume duration := by
        apply lintegral_mono_ae
        exact ae_mono Measure.restrict_le_self hDensityDerivativeBound
      _ = 2 * ∫⁻ time in event,
          rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration := by
        rw [lintegral_const_mul 2
          (measurable_rengerDirectionalFlowHybridBVTotalFlowIntegrand path)]
  · intro state _hState
    exact (((path.measurable_derivativeDensity
      (Sum.inl state)).norm.ennreal_ofReal).aemeasurable.mono_measure
        Measure.restrict_le_self)

/-- Complete derivative variation on a measurable event is controlled by three times the
ordered-flow variation on that event. -/
theorem rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_three_mul_flowVariationOn
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {event : Set ℝ} (hEvent : MeasurableSet event) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn path event ≤
      3 * rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event := by
  have hDensityVariation :=
    rengerDirectionalFlowHybridBVDensityDerivativeVariationOn_le_two_mul_flowDerivativeVariationOn
      hDuration hPath hEvent
  unfold rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
  calc
    rengerDirectionalFlowHybridBVDensityDerivativeVariationOn path event +
        rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event ≤
      2 * rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event +
        rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event :=
      add_le_add hDensityVariation le_rfl
    _ = 3 * rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event := by
      ring

/-- Every finite action sublevel has one explicit event-local complete-derivative variation
modulus.  The estimate applies to boundary neighborhoods as well as interior events. -/
theorem
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_finiteRateSublevelModulus
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {level : ENNReal}
    (hRate : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤ level)
    {exponent : NNReal} (hExponent : 0 < exponent)
    {event : Set ℝ} (hEvent : MeasurableSet event) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn path event ≤
      3 * ((level +
        rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
          finiteOpenIntervalVolume duration event) / (exponent : ENNReal)) := by
  have hFlow :
      rengerDirectionalFlowHybridBVFlowDerivativeVariationOn path event ≤
        (level +
          rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent *
            finiteOpenIntervalVolume duration event) / (exponent : ENNReal) := by
    rw [rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_eq_totalFlowIntegralOn
      hDuration hPath hEvent]
    exact rengerDirectionalFlowHybridBVTotalFlowIntegralOn_le_finiteRateSublevelModulus
      generator hDuration hPath hRate hExponent event
  exact
    (rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_three_mul_flowVariationOn
      hDuration hPath hEvent).trans (mul_le_mul_right hFlow 3)

/-- Uniformly bounded dynamic action prevents total ordered-flow density from concentrating on
any moving family of time events whose physical-time volume vanishes. -/
theorem
    rengerDirectionalFlowHybridBVTotalFlowIntegralOn_tendsto_zero_of_uniformRate
    {Index : Type*} {indexFilter : Filter Index}
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : Index → RengerDirectionalFlowHybridBVPath State duration)
    (events : Index → Set ℝ)
    (hPaths : ∀ index, RengerDirectionalFlowHybridBVAdmissible (paths index) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ index,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration (paths index) ≤ level)
    (hEventVolume : Tendsto
      (fun index => finiteOpenIntervalVolume duration (events index))
      indexFilter (𝓝 0)) :
    Tendsto
      (fun index => ∫⁻ time in events index,
        rengerDirectionalFlowHybridBVTotalFlowIntegrand (paths index) time
        ∂finiteOpenIntervalVolume duration)
      indexFilter (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon hEpsilon
  have hHalfEpsilon : 0 < epsilon / 2 :=
    ENNReal.div_pos_iff.mpr ⟨hEpsilon.ne', by simp⟩
  obtain ⟨exponent, hExponent, hLevelDiv⟩ :=
    exists_nnreal_exponent_level_div_le hLevel hHalfEpsilon
  let correction :=
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent
  have hCorrectionFinite : correction ≠ ∞ :=
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent_ne_top generator exponent
  have hCorrectionTendsto : Tendsto
      (fun index => correction * finiteOpenIntervalVolume duration (events index) /
        (exponent : ENNReal)) indexFilter (𝓝 0) := by
    have hMul : Tendsto
        (fun index => correction * finiteOpenIntervalVolume duration (events index))
        indexFilter (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hEventVolume (Or.inr hCorrectionFinite)
    simpa using ENNReal.Tendsto.div_const hMul
      (Or.inr (ENNReal.coe_ne_zero.mpr hExponent.ne'))
  have hCorrectionEventually :=
    ENNReal.tendsto_nhds_zero.mp hCorrectionTendsto (epsilon / 2) hHalfEpsilon
  filter_upwards [hCorrectionEventually] with index hCorrection
  calc
    (∫⁻ time in events index,
        rengerDirectionalFlowHybridBVTotalFlowIntegrand (paths index) time
        ∂finiteOpenIntervalVolume duration) ≤
      (level + correction * finiteOpenIntervalVolume duration (events index)) /
        (exponent : ENNReal) := by
      exact rengerDirectionalFlowHybridBVTotalFlowIntegralOn_le_finiteRateSublevelModulus
        generator hDuration (hPaths index) (hRates index) hExponent (events index)
    _ = level / (exponent : ENNReal) +
        correction * finiteOpenIntervalVolume duration (events index) /
          (exponent : ENNReal) := by rw [ENNReal.add_div]
    _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hLevelDiv hCorrection
    _ = epsilon := by
      rw [ENNReal.div_add_div_same, ← two_mul, mul_comm]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by simp)

/-- Under the same bounded-rate hypothesis, the complete density-plus-flow derivative variation
carried by shrinking measurable events vanishes.  This is the precise no-boundary-escape theorem
needed before recovered initial or terminal traces can be closed under hybrid limits. -/
theorem
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_tendsto_zero_of_uniformRate
    {Index : Type*} {indexFilter : Filter Index}
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : Index → RengerDirectionalFlowHybridBVPath State duration)
    (events : Index → Set ℝ)
    (hEvents : ∀ index, MeasurableSet (events index))
    (hPaths : ∀ index, RengerDirectionalFlowHybridBVAdmissible (paths index) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ index,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration (paths index) ≤ level)
    (hEventVolume : Tendsto
      (fun index => finiteOpenIntervalVolume duration (events index))
      indexFilter (𝓝 0)) :
    Tendsto
      (fun index => rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths index) (events index)) indexFilter (𝓝 0) := by
  have hFlowTendsto :=
    rengerDirectionalFlowHybridBVTotalFlowIntegralOn_tendsto_zero_of_uniformRate
      generator hDuration paths events hPaths hLevel hRates hEventVolume
  apply ENNReal.tendsto_nhds_zero.mpr
  intro epsilon hEpsilon
  have hQuarterEpsilon : 0 < epsilon / 4 :=
    ENNReal.div_pos_iff.mpr ⟨hEpsilon.ne', by simp⟩
  have hFlowEventually :=
    ENNReal.tendsto_nhds_zero.mp hFlowTendsto (epsilon / 4) hQuarterEpsilon
  filter_upwards [hFlowEventually] with index hFlow
  calc
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths index) (events index) ≤
      3 * rengerDirectionalFlowHybridBVFlowDerivativeVariationOn
        (paths index) (events index) :=
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_three_mul_flowVariationOn
        hDuration (hPaths index) (hEvents index)
    _ = 3 * ∫⁻ time in events index,
        rengerDirectionalFlowHybridBVTotalFlowIntegrand (paths index) time
        ∂finiteOpenIntervalVolume duration := by
      rw [rengerDirectionalFlowHybridBVFlowDerivativeVariationOn_eq_totalFlowIntegralOn
        hDuration (hPaths index) (hEvents index)]
    _ ≤ 3 * (epsilon / 4) := mul_le_mul_right hFlow 3
    _ ≤ 4 * (epsilon / 4) := by gcongr; norm_num
    _ = epsilon := ENNReal.mul_div_cancel (by norm_num) (by simp)

/-- Uniform finite dynamic rate gives an epsilon--delta modulus from physical-time event volume
to complete derivative variation, uniformly across the whole path family. -/
theorem
    exists_eventVolume_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    {epsilon : ENNReal} (hEpsilon : 0 < epsilon) :
    ∃ delta : ENNReal, 0 < delta ∧
      ∀ sequenceIndex event, MeasurableSet event →
        finiteOpenIntervalVolume duration event ≤ delta →
          rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
            (paths sequenceIndex) event ≤ epsilon := by
  classical
  by_contra hModulus
  push Not at hModulus
  let delta : ℕ → ENNReal := fun natural =>
    ENNReal.ofReal (1 / ((natural : ℝ) + 1))
  have hDeltaPositive (natural : ℕ) : 0 < delta natural := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  choose selectedIndex events hEvents hEventVolume hVariation using
    fun natural => hModulus (delta natural) (hDeltaPositive natural)
  have hDeltaTendsto : Tendsto delta atTop (nhds 0) := by
    simpa only [delta, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun natural : ℕ => 1 / ((natural : ℝ) + 1)) atTop (nhds 0))
  have hEventVolumeTendsto : Tendsto
      (fun natural => finiteOpenIntervalVolume duration (events natural))
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hDeltaTendsto
    · exact Filter.Eventually.of_forall fun _ => zero_le
    · exact Filter.Eventually.of_forall hEventVolume
  have hSelectedVariationTendsto :=
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_tendsto_zero_of_uniformRate
      generator hDuration (fun natural => paths (selectedIndex natural)) events hEvents
        (fun natural => hPaths (selectedIndex natural)) hLevel
        (fun natural => hRates (selectedIndex natural)) hEventVolumeTendsto
  have hVariationEventually :=
    ENNReal.tendsto_nhds_zero.mp hSelectedVariationTendsto epsilon hEpsilon
  obtain ⟨natural, hVariationUpper⟩ := hVariationEventually.exists
  exact (not_lt_of_ge hVariationUpper) (hVariation natural)

end

end FiniteMarkovProcesses.InformationTheory
