/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDynamicRate
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Coercivity of the Renger hybrid-BV directional-flow rate

This module lifts the finite-channel Poisson coercivity estimate through physical time.  The
result controls the integrated total one-way flow by the exact dynamic action plus a visible
reference-rate correction.  It is the quantitative input needed to turn a finite rate sublevel
into a bounded-variation family; no compactness theorem is asserted here.

## Main declarations

- `rengerDirectionalFlowHybridBVTotalFlowIntegrand`: total instantaneous one-way flow.
- `rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand`: explicit generator correction.
- `rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_correction`: integrated
  coercivity on the named finite-rate domain.
- `rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_uniformCorrection`:
  path-independent finite-horizon coercivity.
- `rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_le_dynamicRate_add_uniformCorrection`:
  the exact derivative-measure variation bound needed by hybrid compactness.
- `rengerDirectionalFlowHybridBVTotalDerivativeVariation_le_three_mul_dynamicRateCorrection`:
  action controls the complete density-plus-flow derivative variation.
- `rengerDirectionalFlowHybridBVL1Norm_le_one_add_flowDerivativeTotalVariation_mul_duration`:
  admissibility and derivative variation control the whole strong-`L1` path norm.
- `rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_uniformL1VariationEnvelope`: finite
  action sublevels enter the broad admissibility-free HPR coercive envelope.
- `rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet`: exact reduction
  of finite action sublevels to a bounded coercive set, with no compactness claim.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Total instantaneous one-way flow across all ordered off-diagonal channels. -/
noncomputable def rengerDirectionalFlowHybridBVTotalFlowIntegrand
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal)

/-- The explicit finite generator correction in the Poisson coercivity estimate. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ENNReal.ofReal ((Real.exp 1 - 1) *
      (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
        generator.rate transition.1.1 transition.1.2 : NNReal))

/-- Path-independent generator correction obtained by replacing every probability coordinate by
one. -/
noncomputable def rengerDirectionalFlowHybridBVGeneratorCorrection
    (generator : FiniteStateMarkovGenerator State) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ENNReal.ofReal ((Real.exp 1 - 1) *
      (generator.rate transition.1.1 transition.1.2 : ℝ))

/-- The path-independent finite-state generator correction is genuinely finite. -/
theorem rengerDirectionalFlowHybridBVGeneratorCorrection_ne_top
    (generator : FiniteStateMarkovGenerator State) :
    rengerDirectionalFlowHybridBVGeneratorCorrection generator ≠ ∞ := by
  unfold rengerDirectionalFlowHybridBVGeneratorCorrection
  rw [ENNReal.sum_ne_top]
  exact fun _ _ => ENNReal.ofReal_ne_top

/-- Sum of the total-variation masses of all carried ordered-flow derivative measures. -/
noncomputable def rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
      Set.univ

/-- Sum of the total-variation masses of all carried density derivative measures. -/
noncomputable def rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  ∑ state,
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.totalVariation Set.univ

/-- Total derivative variation of every density and ordered-flow coordinate. -/
noncomputable def rengerDirectionalFlowHybridBVTotalDerivativeVariation
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation path +
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path

/-- The Renger-coordinate total derivative variation is the generic hybrid-BV variation. -/
theorem rengerDirectionalFlowHybridBVTotalDerivativeVariation_eq_generic
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariation path =
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  unfold rengerDirectionalFlowHybridBVTotalDerivativeVariation
    rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation
    finiteIntervalHybridBVDerivativeTotalVariation
  rw [Fintype.sum_sum_type]

/-- Closed-form action sublevel on the exact hybrid carrier.  Compactness and closedness are
properties to prove, not fields of this definition. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :
    Set (RengerDirectionalFlowHybridBVPath State duration) :=
  {path | rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤ level}

/-- The finite-rate domain with one explicit complete-derivative coercive bound.  This set is
neither asserted nor expected to be closed or compact in the hybrid topology: absolute
continuity can converge to an atomic derivative, and an initial-zero boundary layer can escape
through the open-interval derivative tests. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateCoerciveSet
    (hDuration : 0 < duration) (bound : ENNReal) :
    Set (RengerDirectionalFlowHybridBVPath State duration) :=
  {path | RengerDirectionalFlowHybridBVAdmissible path hDuration ∧
    rengerDirectionalFlowHybridBVTotalDerivativeVariation path ≤ 3 * bound}

/-- Every cumulative-flow value before the terminal boundary is controlled by the total
variation of its carried derivative measure.  The zero initial flow is used explicitly. -/
theorem rengerDirectionalFlowHybridBVCumulativeFlowValue_le_derivativeTotalVariation
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hDuration : 0 < duration)
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {time : ℝ} (hTime : time ∈ Set.Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    ENNReal.ofReal
        (rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition) ≤
      (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
        Set.univ := by
  let derivative :=
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
  have hIncrement :
      derivative (Set.Ioc 0 time) =
        rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition := by
    have hInitial := hPath.cumulativeFlowInitiallyZero transition
    change path.cadlagRepresentative.representative 0 (Sum.inr transition) = 0 at hInitial
    rw [show derivative =
        (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure by rfl,
      path.derivative_apply_Ioc_eq_cadlagRepresentative_sub
        (Sum.inr transition) (le_refl 0) hTime.1 hTime.2,
      hInitial, sub_zero]
    rfl
  calc
    ENNReal.ofReal
        (rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition) ≤
      ENNReal.ofReal
        |rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal |derivative (Set.Ioc 0 time)| := by rw [hIncrement]
    _ ≤ derivative.totalVariation (Set.Ioc 0 time) :=
      SignedMeasure.ofReal_abs_apply_le_totalVariation derivative measurableSet_Ioc
    _ ≤ derivative.totalVariation Set.univ := measure_mono (Set.subset_univ _)

/-- At every physical interior point satisfying the almost-everywhere admissibility conditions,
the selected path value has `l1` norm bounded by one plus total ordered-flow variation. -/
theorem
    rengerDirectionalFlowHybridBVCadlagRepresentativeEnorm_le_one_add_flowDerivativeTotalVariation
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hDuration : 0 < duration)
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    {time : ℝ} (hTime : time ∈ Set.Ioo 0 duration)
    (hDensityNonnegative :
      ∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue path time state)
    (hDensityNormalized :
      ∑ state, rengerDirectionalFlowHybridBVDensityValue path time state = 1)
    (hFlowNonnegative :
      ∀ transition,
        0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition) :
    ‖path.cadlagRepresentative.representative time‖ₑ ≤
      1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
  rw [← ofReal_norm, PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
  simp only [Real.norm_eq_abs]
  change ENNReal.ofReal
      ((∑ state, |rengerDirectionalFlowHybridBVDensityValue path time state|) +
        ∑ transition,
          |rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition|) ≤ _
  simp_rw [abs_of_nonneg (hDensityNonnegative _)]
  rw [hDensityNormalized, ENNReal.ofReal_add (by positivity)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  have hFlowSum :
      ENNReal.ofReal
          (∑ transition,
            |rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition|) ≤
        rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
    simp_rw [abs_of_nonneg (hFlowNonnegative _)]
    rw [ENNReal.ofReal_sum_of_nonneg fun transition _ => hFlowNonnegative transition]
    unfold rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation
    exact Finset.sum_le_sum fun transition _ =>
      rengerDirectionalFlowHybridBVCumulativeFlowValue_le_derivativeTotalVariation
        hDuration hPath ⟨hTime.1.le, hTime.2⟩ transition
  simpa only [ENNReal.ofReal_one] using add_le_add (le_refl (1 : ENNReal)) hFlowSum

/-- The pointwise path-norm estimate holds almost everywhere on the physical interval. -/
theorem
    rengerDirectionalFlowHybridBVCadlagRepresentativeEnorm_le_one_add_flowVariation_ae
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hDuration : 0 < duration)
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ‖path.cadlagRepresentative.representative time‖ₑ ≤
        1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
  have hTimeMembership :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, time ∈ Set.Ioo 0 duration := by
    rw [finiteOpenIntervalVolume]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hTimeMembership, hPath.densityNonnegativeAE,
    hPath.densityNormalizedAE, hPath.cumulativeFlowNonnegativeAE]
    with time hTime hDensityNonnegative hDensityNormalized hFlowNonnegative
  exact
    rengerDirectionalFlowHybridBVCadlagRepresentativeEnorm_le_one_add_flowDerivativeTotalVariation
      hDuration hPath hTime hDensityNonnegative hDensityNormalized hFlowNonnegative

/-- The whole strong-`L1` path norm is bounded by physical duration times one plus total
ordered-flow derivative variation. -/
theorem rengerDirectionalFlowHybridBVL1Norm_le_one_add_flowDerivativeTotalVariation_mul_duration
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hDuration : 0 < duration)
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ‖path.toDerivativePath.toL1Path‖ₑ ≤
      (1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path) *
        ENNReal.ofReal duration := by
  let representative := path.cadlagRepresentative.representative
  let hRepresentative : MemLp representative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose path.cadlagRepresentative.represents
  have hRepresents :
      hRepresentative.toLp representative = path.toDerivativePath.toL1Path :=
    Classical.choose_spec path.cadlagRepresentative.represents
  rw [← hRepresents, Lp.enorm_toLp,
    eLpNorm_one_eq_lintegral_enorm hRepresentative.aestronglyMeasurable]
  calc
    (∫⁻ time, ‖representative time‖ₑ ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ _time : ℝ,
          (1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path)
            ∂finiteOpenIntervalVolume duration :=
      lintegral_mono_ae
        (rengerDirectionalFlowHybridBVCadlagRepresentativeEnorm_le_one_add_flowVariation_ae
          hDuration hPath)
    _ = (1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path) *
        finiteOpenIntervalVolume duration Set.univ := by rw [lintegral_const]
    _ = (1 + rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path) *
        ENNReal.ofReal duration := by
      rw [finiteOpenIntervalVolume, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, Real.volume_Ioo]
      simp

/-- The total-flow integrand is measurable for every hybrid path. -/
theorem measurable_rengerDirectionalFlowHybridBVTotalFlowIntegrand
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Measurable (rengerDirectionalFlowHybridBVTotalFlowIntegrand path) := by
  unfold rengerDirectionalFlowHybridBVTotalFlowIntegrand
  apply Finset.measurable_fun_sum
  intro transition _hTransition
  apply Measurable.coe_nnreal_ennreal
  exact measurable_real_toNNReal.comp
    (path.measurable_derivativeDensity (Sum.inr transition))

/-- The reference correction is almost-everywhere measurable along every hybrid path. -/
theorem aemeasurable_rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    AEMeasurable (rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path)
      (finiteOpenIntervalVolume duration) := by
  unfold rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand
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

/-- Pointwise finite-channel coercivity along every hybrid path, before admissibility is used. -/
theorem rengerDirectionalFlowHybridBVTotalFlowIntegrand_le_localRate_add_correction
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) :
    rengerDirectionalFlowHybridBVTotalFlowIntegrand path time ≤
      rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) +
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time := by
  exact sum_flow_le_rengerDirectionalFlowLocalRateRaw_add_referenceCorrection
    generator (rengerDirectionalFlowHybridBVDensityAt path time)
      (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)

/-- Time integration preserves the exact finite-channel coercivity estimate. -/
theorem rengerDirectionalFlowHybridBVTotalFlowIntegral_le_localRate_add_correctionIntegral
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    (∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration) ≤
      ∫⁻ time,
        rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) +
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
        ∂finiteOpenIntervalVolume duration := by
  apply lintegral_mono
  exact rengerDirectionalFlowHybridBVTotalFlowIntegrand_le_localRate_add_correction
    generator path

/-- On the finite-rate domain, integrated total one-way flow is controlled by the exact dynamic
rate plus the explicit integrated reference correction. -/
theorem rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_correction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    (∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration) ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        ∫⁻ time,
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
          ∂finiteOpenIntervalVolume duration := by
  calc
    (∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ time,
          rengerDirectionalFlowLocalRateRaw generator
              (rengerDirectionalFlowHybridBVDensityAt path time)
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) +
            rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
          ∂finiteOpenIntervalVolume duration :=
      rengerDirectionalFlowHybridBVTotalFlowIntegral_le_localRate_add_correctionIntegral
        generator path
    _ = (∫⁻ time,
          rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path time)
          ∂finiteOpenIntervalVolume duration) +
        ∫⁻ time,
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
          ∂finiteOpenIntervalVolume duration := by
      rw [lintegral_add_left'
        (aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path)]
    _ = rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        ∫⁻ time,
          rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
          ∂finiteOpenIntervalVolume duration := by
      rw [rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible generator hDuration hPath]

/-- Every admissible simplex density coordinate is at most one almost everywhere. -/
theorem rengerDirectionalFlowHybridBVDensityAt_le_one_ae
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state, rengerDirectionalFlowHybridBVDensityAt path time state ≤ 1 := by
  filter_upwards [hPath.densityNonnegativeAE, hPath.densityNormalizedAE]
    with time hNonnegative hNormalized
  intro state
  change (Real.toNNReal (rengerDirectionalFlowHybridBVDensityValue path time state) : ℝ) ≤ 1
  rw [Real.coe_toNNReal _ (hNonnegative state)]
  calc
    rengerDirectionalFlowHybridBVDensityValue path time state ≤
        ∑ candidate, rengerDirectionalFlowHybridBVDensityValue path time candidate := by
      exact Finset.single_le_sum
        (fun candidate _hCandidate => hNonnegative candidate) (Finset.mem_univ state)
    _ = 1 := hNormalized

/-- On the admissible simplex domain, the instantaneous reference correction is bounded by one
path-independent finite generator constant. -/
theorem rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand_le_generatorCorrection_ae
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time ≤
        rengerDirectionalFlowHybridBVGeneratorCorrection generator := by
  filter_upwards [rengerDirectionalFlowHybridBVDensityAt_le_one_ae hDuration hPath]
    with time hDensity
  unfold rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand
    rengerDirectionalFlowHybridBVGeneratorCorrection
  apply Finset.sum_le_sum
  intro transition _hTransition
  apply ENNReal.ofReal_le_ofReal
  have hExpected :
      rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
          generator.rate transition.1.1 transition.1.2 ≤
        generator.rate transition.1.1 transition.1.2 := by
    simpa only [one_mul] using mul_le_mul_left
      (hDensity transition.1.1) (generator.rate transition.1.1 transition.1.2)
  have hExp : 0 ≤ Real.exp 1 - 1 := by
    nlinarith [Real.add_one_le_exp 1]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hExpected) hExp

/-- The integrated reference correction is bounded by the physical duration times one explicit
finite generator constant. -/
theorem rengerDirectionalFlowHybridBVReferenceCorrectionIntegral_le_uniformCorrection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    (∫⁻ time,
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
        ∂finiteOpenIntervalVolume duration) ≤
      rengerDirectionalFlowHybridBVGeneratorCorrection generator * ENNReal.ofReal duration := by
  calc
    (∫⁻ time,
        rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand generator path time
        ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ _time : ℝ, rengerDirectionalFlowHybridBVGeneratorCorrection generator
          ∂finiteOpenIntervalVolume duration :=
      lintegral_mono_ae
        (rengerDirectionalFlowHybridBVReferenceCorrectionIntegrand_le_generatorCorrection_ae
          generator hDuration hPath)
    _ = rengerDirectionalFlowHybridBVGeneratorCorrection generator *
        finiteOpenIntervalVolume duration Set.univ := by
      rw [lintegral_const]
    _ = rengerDirectionalFlowHybridBVGeneratorCorrection generator *
        ENNReal.ofReal duration := by
      rw [finiteOpenIntervalVolume, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, Real.volume_Ioo]
      simp

/-- Finite action gives a path-independent bound on integrated total one-way flow.  This is the
quantitative bounded-variation input for the hybrid compact-sublevel theorem. -/
theorem rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_uniformCorrection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    (∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration) ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrection generator *
          ENNReal.ofReal duration := by
  exact (rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_correction
    generator hDuration hPath).trans
      (add_le_add_right
        (rengerDirectionalFlowHybridBVReferenceCorrectionIntegral_le_uniformCorrection
          generator hDuration hPath)
        (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path))

/-- For each admissible ordered channel, the carried derivative-measure variation is exactly the
integral of its nonnegative Radon--Nikodym flow density. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_apply
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
        Set.univ =
      ∫⁻ time,
        (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal)
        ∂finiteOpenIntervalVolume duration := by
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hPath.absolutelyContinuousDerivative (Sum.inr transition)]
  change SignedMeasure.totalVariation
      ((finiteOpenIntervalVolume duration).withDensityᵥ
        ((path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.rnDeriv
          (finiteOpenIntervalVolume duration))) Set.univ = _
  rw [SignedMeasure.totalVariation_withDensityᵥ_apply_univ
    (SignedMeasure.integrable_rnDeriv _ _)
    (hPath.flowDerivativeNonnegativeAE.mono fun time hTime => hTime transition)]
  rfl

/-- On the admissible domain, total ordered-flow derivative variation is exactly integrated total
one-way flow. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_eq_totalFlowIntegral
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path =
      ∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
        ∂finiteOpenIntervalVolume duration := by
  unfold rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation
    rengerDirectionalFlowHybridBVTotalFlowIntegrand
  rw [lintegral_finsetSum']
  · apply Finset.sum_congr rfl
    intro transition _hTransition
    exact rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_apply
      hDuration hPath transition
  · intro transition _hTransition
    exact (measurable_real_toNNReal.comp
      (path.measurable_derivativeDensity (Sum.inr transition))).coe_nnreal_ennreal.aemeasurable

/-- For each admissible density coordinate, the carried derivative-measure variation is exactly
the integral of the absolute Radon--Nikodym density. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_apply
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (state : State) :
    (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.totalVariation Set.univ =
      ∫⁻ time, ENNReal.ofReal
        |rengerDirectionalFlowHybridBVDensityDerivative path time state|
        ∂finiteOpenIntervalVolume duration := by
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hPath.absolutelyContinuousDerivative (Sum.inl state)]
  change SignedMeasure.totalVariation
      ((finiteOpenIntervalVolume duration).withDensityᵥ
        ((path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure.rnDeriv
          (finiteOpenIntervalVolume duration))) Set.univ = _
  simpa only [rengerDirectionalFlowHybridBVDensityDerivative,
    FiniteIntervalHybridBVPath.derivativeDensity] using
    SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs
      (path.measurable_derivativeDensity (Sum.inl state))
      (SignedMeasure.integrable_rnDeriv
        (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
        (finiteOpenIntervalVolume duration))

/-- The continuity equation bounds total instantaneous density variation by twice the total
one-way flow.  Each ordered channel is counted once as incoming and once as outgoing. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeAbsoluteSum_le_two_mul_totalFlowIntegrand_ae
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (∑ state, ENNReal.ofReal
        |rengerDirectionalFlowHybridBVDensityDerivative path time state|) ≤
          2 * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time := by
  filter_upwards [hPath.continuityEquationAE, hPath.flowDerivativeNonnegativeAE]
    with time hContinuity hFlowNonnegative
  calc
    (∑ state, ENNReal.ofReal
        |rengerDirectionalFlowHybridBVDensityDerivative path time state|) =
        ∑ state, ENNReal.ofReal
          |(∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(source, state), source.property⟩) -
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(state, target), target.property.symm⟩| := by
      apply Finset.sum_congr rfl
      intro state _hState
      rw [hContinuity state]
    _ ≤ ∑ state, ENNReal.ofReal
          ((∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(source, state), source.property⟩) +
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path time
                ⟨(state, target), target.property.symm⟩) := by
      apply Finset.sum_le_sum
      intro state _hState
      apply ENNReal.ofReal_le_ofReal
      have hIncomingNonnegative :
          0 ≤ ∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩ := by
        exact Finset.sum_nonneg fun source _hSource => hFlowNonnegative _
      have hOutgoingNonnegative :
          0 ≤ ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩ := by
        exact Finset.sum_nonneg fun target _hTarget => hFlowNonnegative _
      simpa [abs_of_nonneg hIncomingNonnegative, abs_of_nonneg hOutgoingNonnegative] using
        abs_sub
          (∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(source, state), source.property⟩)
          (∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative path time
              ⟨(state, target), target.property.symm⟩)
    _ = ∑ state,
          ((∑ source : {source : State // source ≠ state},
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time
                ⟨(source, state), source.property⟩ : ENNReal)) +
            ∑ target : {target : State // target ≠ state},
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time
                ⟨(state, target), target.property.symm⟩ : ENNReal)) := by
      apply Finset.sum_congr rfl
      intro state _hState
      rw [ENNReal.ofReal_add]
      · congr 1
        · rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro source _hSource
            unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
            rw [Real.toNNReal_of_nonneg (hFlowNonnegative _)]
            exact ENNReal.ofReal_eq_coe_nnreal (hFlowNonnegative _)
          · intro source _hSource
            exact hFlowNonnegative _
        · rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro target _hTarget
            unfold rengerDirectionalFlowHybridBVFlowDerivativeAt
            rw [Real.toNNReal_of_nonneg (hFlowNonnegative _)]
            exact ENNReal.ofReal_eq_coe_nnreal (hFlowNonnegative _)
          · intro target _hTarget
            exact hFlowNonnegative _
      · exact Finset.sum_nonneg fun source _hSource => hFlowNonnegative _
      · exact Finset.sum_nonneg fun target _hTarget => hFlowNonnegative _
    _ = 2 * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time := by
      rw [Finset.sum_add_distrib]
      have hIncoming :
          (∑ target, ∑ source : {source : State // source ≠ target},
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time
                ⟨(source, target), source.property⟩ : ENNReal)) =
            ∑ transition,
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal) := by
        simpa only using
          (sum_incomingTransition_eq_sum_orderedOffDiagonalTransition
            (fun transition =>
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal)))
      have hOutgoing :
          (∑ source, ∑ target : {target : State // target ≠ source},
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time
                ⟨(source, target), target.property.symm⟩ : ENNReal)) =
            ∑ transition,
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal) := by
        simpa only using
          (sum_outgoingTransition_eq_sum_orderedOffDiagonalTransition
            (fun transition =>
              (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition : ENNReal)))
      rw [hIncoming, hOutgoing]
      unfold rengerDirectionalFlowHybridBVTotalFlowIntegrand
      rw [two_mul]

/-- On the admissible domain, total density-derivative variation is the time integral of the sum
of absolute density derivatives. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_eq_absoluteDerivativeIntegral
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation path =
      ∫⁻ time, ∑ state, ENNReal.ofReal
        |rengerDirectionalFlowHybridBVDensityDerivative path time state|
        ∂finiteOpenIntervalVolume duration := by
  unfold rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation
  rw [lintegral_finsetSum']
  · apply Finset.sum_congr rfl
    intro state _hState
    exact rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_apply
      hDuration hPath state
  · intro state _hState
    exact ((path.measurable_derivativeDensity
      (Sum.inl state)).norm.ennreal_ofReal).aemeasurable

/-- The distributional continuity equation gives the sharp finite-state estimate: density
derivative variation is at most twice ordered-flow derivative variation. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_le_two_mul_flowVariation
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation path ≤
      2 * rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
  rw [rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_eq_absoluteDerivativeIntegral
    hDuration hPath,
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_eq_totalFlowIntegral
      hDuration hPath]
  calc
    (∫⁻ time, ∑ state, ENNReal.ofReal
        |rengerDirectionalFlowHybridBVDensityDerivative path time state|
        ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ time, 2 * rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration :=
      lintegral_mono_ae
        (rengerDirectionalFlowHybridBVDensityDerivativeAbsoluteSum_le_two_mul_totalFlowIntegrand_ae
          hDuration hPath)
    _ = 2 * ∫⁻ time, rengerDirectionalFlowHybridBVTotalFlowIntegrand path time
          ∂finiteOpenIntervalVolume duration := by
      rw [lintegral_const_mul 2
        (measurable_rengerDirectionalFlowHybridBVTotalFlowIntegrand path)]

/-- The complete density-plus-flow derivative variation is controlled by three times the ordered-
flow variation.  This is the full BV estimate needed by the broad HPR compact envelope. -/
theorem rengerDirectionalFlowHybridBVTotalDerivativeVariation_le_three_mul_flowVariation
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariation path ≤
      3 * rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
  unfold rengerDirectionalFlowHybridBVTotalDerivativeVariation
  calc
    rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation path +
        rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path ≤
      2 * rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path +
        rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path :=
      add_le_add_left
        (rengerDirectionalFlowHybridBVDensityDerivativeTotalVariation_le_two_mul_flowVariation
          hDuration hPath)
        (rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path)
    _ = 3 * rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path := by
      rw [show (3 : ENNReal) = 2 + 1 by norm_num, add_mul, one_mul]

/-- The exact derivative-measure form of finite-rate coercivity: every dynamic-rate sublevel has a
uniform ordered-flow total-variation bound. -/
theorem
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_le_dynamicRate_add_uniformCorrection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrection generator *
          ENNReal.ofReal duration := by
  rw [rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_eq_totalFlowIntegral
    hDuration hPath]
  exact rengerDirectionalFlowHybridBVTotalFlowIntegral_le_dynamicRate_add_uniformCorrection
    generator hDuration hPath

/-- Finite dynamic action controls the complete density-plus-flow derivative variation, not only
the nonnegative flow sector. -/
theorem rengerDirectionalFlowHybridBVTotalDerivativeVariation_le_three_mul_dynamicRateCorrection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariation path ≤
      3 * (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path +
        rengerDirectionalFlowHybridBVGeneratorCorrection generator * ENNReal.ofReal duration) := by
  have hFlow :=
    rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_le_dynamicRate_add_uniformCorrection
      generator hDuration hPath
  exact (rengerDirectionalFlowHybridBVTotalDerivativeVariation_le_three_mul_flowVariation
    hDuration hPath).trans (mul_le_mul_right hFlow 3)

/-- Every genuinely finite dynamic-rate sublevel lies in one explicit finite-rate coercive set.
This is a quantitative estimate only.  Compact containment must instead pass through a broader
admissibility-free `L1` plus total-variation envelope and lower semicontinuity of the extended
action. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level ⊆
      rengerDirectionalFlowHybridBVFiniteRateCoerciveSet hDuration
        (level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
          ENNReal.ofReal duration) := by
  intro path hPathRate
  have hPathAdmissible :
      RengerDirectionalFlowHybridBVAdmissible path hDuration := by
    by_contra hPathNotAdmissible
    have hTop := rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
      generator hDuration hPathNotAdmissible
    rw [rengerDirectionalFlowHybridBVFiniteRateSublevel, Set.mem_ofPred_eq, hTop] at hPathRate
    exact (not_le_of_gt hLevel) hPathRate
  refine ⟨hPathAdmissible, ?_⟩
  exact
    (rengerDirectionalFlowHybridBVTotalDerivativeVariation_le_three_mul_dynamicRateCorrection
      generator hDuration hPathAdmissible).trans
      (mul_le_mul_right
        (add_le_add_left hPathRate
          (rengerDirectionalFlowHybridBVGeneratorCorrection generator *
            ENNReal.ofReal duration)) 3)

/-- Every genuinely finite dynamic-rate sublevel enters one broad admissibility-free uniform-`L1`
and total-derivative-variation envelope.  This is the exact coercive reduction needed before the
independent HPR compact-closure theorem. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_uniformL1VariationEnvelope
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level ⊆
      finiteIntervalHybridBVUniformL1VariationEnvelope
        ((1 + (level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
          ENNReal.ofReal duration)) * ENNReal.ofReal duration)
        (3 * (level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
          ENNReal.ofReal duration)) := by
  intro path hPathRate
  have hCoercive :=
    rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet
      generator hDuration hLevel hPathRate
  obtain ⟨hPathAdmissible, hTotalVariation⟩ := hCoercive
  rw [mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff]
  constructor
  · have hRateControl :=
      rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation_le_dynamicRate_add_uniformCorrection
        generator hDuration hPathAdmissible
    have hFlowVariation :
        rengerDirectionalFlowHybridBVFlowDerivativeTotalVariation path ≤
          level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
            ENNReal.ofReal duration :=
      hRateControl.trans
        (add_le_add_left hPathRate
          (rengerDirectionalFlowHybridBVGeneratorCorrection generator *
            ENNReal.ofReal duration))
    exact
      (rengerDirectionalFlowHybridBVL1Norm_le_one_add_flowDerivativeTotalVariation_mul_duration
        hDuration hPathAdmissible).trans
        (mul_le_mul_left (add_le_add (le_refl (1 : ENNReal)) hFlowVariation)
          (ENNReal.ofReal duration))
  · rw [← rengerDirectionalFlowHybridBVTotalDerivativeVariation_eq_generic]
    exact hTotalVariation

end

end FiniteMarkovProcesses.InformationTheory
