/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMeanStability
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVReferenceEvolutionPerturbedRate
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVVanishingVariation

/-!
# Source-flow convergence for positive Renger targets

This module upgrades density stability to the directional-flow control required by the hybrid
topology.  The first critical estimate shows that a uniform positive target-density floor gives
one index-independent integrated bound for every canonical target-source rate.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- Explicit statewise density floor carried by a positive reference-evolution perturbation. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (state : State) : NNReal :=
  Real.toNNReal
    ((mixingWeight : ℝ) *
      (Real.exp
          (-((generator.toTimeDependentMarkovRate.uniformizationRate : ℝ) * duration)) *
        (rengerDirectionalFlowHybridBVTargetInitialPMF path state).toReal))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Positive mixing and positive initial mass make the explicit perturbation floor positive. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor_pos
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight) (state : State)
    (hInitial : 0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state) :
    0 < rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor
      generator path mixingWeight state := by
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor,
    Real.toNNReal_pos]
  have hInitialReal :
      0 < (rengerDirectionalFlowHybridBVTargetInitialPMF path state).toReal := by
    rw [rengerDirectionalFlowHybridBVTargetInitialPMF_apply, ENNReal.coe_toReal]
    exact_mod_cast hInitial
  positivity

/-- The genuine perturbed representation carries its explicit density floor almost everywhere
on the complete physical interval. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : NNReal) (hMixingWeightLeOne : mixingWeight ≤ 1)
    (state : State) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor
          generator path mixingWeight state ≤
        rengerDirectionalFlowHybridBVMeasurableDensityAt perturbed.1 time state := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq perturbed.1,
    path.2.densityNonnegativeAE,
    MeasureTheory.ae_restrict_mem measurableSet_Ioo] with time hVersion hNonnegative hTime
  rw [hVersion]
  unfold rengerDirectionalFlowHybridBVDensityAt
  rw [show perturbed.1 =
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path mixingWeight by rfl,
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityValue
      generator path mixingWeight hTime.1.le hTime.2 state,
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor]
  apply Real.toNNReal_le_toNNReal
  exact
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue_uniformLowerBound
      generator path mixingWeight.coe_nonneg
      (by exact_mod_cast hMixingWeightLeOne) hTime.1.le hTime.2.le state
      (hNonnegative state)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A positive lower bound on one target-density coordinate gives an index-independent pointwise
bound on every canonical regularized outgoing rate. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_le_of_densityFloor
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (index : ℕ) (time : ℝ) (source target : State) (densityFloor : NNReal)
    (hDensityFloorPositive : 0 < densityFloor)
    (hDensityFloor :
      densityFloor ≤ rengerDirectionalFlowHybridBVMeasurableDensityAt path time source) :
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).rate time source target ≤
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path time source target / densityFloor +
        generator.rate source target := by
  by_cases hDiagonal : source = target
  · subst target
    rw [(rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path index).rate_self, generator.rate_self]
    simp
  have hSupportedLe :
      (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
          generator path index).rate time source target ≤
        (rengerDirectionalFlowHybridBVTruncatedTargetRate
          path index).rate time source target := by
    change (if generator.rate source target = 0 then 0 else
      (rengerDirectionalFlowHybridBVTruncatedTargetRate
        path index).rate time source target) ≤ _
    split_ifs
    · exact zero_le
    · exact le_rfl
  have hTruncatedLe :
      (rengerDirectionalFlowHybridBVTruncatedTargetRate
          path index).rate time source target ≤
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target /
          rengerDirectionalFlowHybridBVMeasurableDensityAt path time source := by
    rw [rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
      path index time hDiagonal]
    exact min_le_right _ _
  have hRatioLe :
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target /
          rengerDirectionalFlowHybridBVMeasurableDensityAt path time source ≤
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target / densityFloor := by
    gcongr
  rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization,
    rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate]
  apply add_le_add (hSupportedLe.trans <| hTruncatedLe.trans hRatioLe)
  apply mul_le_of_le_one_left (zero_le)
  rw [div_le_one (by positivity)]
  exact le_add_of_nonneg_left (Nat.cast_nonneg index)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A positive almost-everywhere density floor gives one finite-channel rate-mass ceiling that is
uniform over the complete canonical cutoff/reference-floor sequence. -/
theorem
  lintegral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_le_of_densityFloor
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (densityFloor : NNReal) (hDensityFloorPositive : 0 < densityFloor)
    (source target : State)
    (hDensityFloor : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      densityFloor ≤ rengerDirectionalFlowHybridBVMeasurableDensityAt path time source)
    (index : ℕ) :
    (∫⁻ time,
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≤
      ((densityFloor⁻¹ : NNReal) : ENNReal) *
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration +
        (generator.rate source target : ENNReal) * ENNReal.ofReal duration := by
  calc
    (∫⁻ time,
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≤
      ∫⁻ time,
        ((rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target / densityFloor : NNReal) : ENNReal) +
          (generator.rate source target : ENNReal)
        ∂finiteOpenIntervalVolume duration := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hDensityFloor] with time hTime
      exact ENNReal.coe_le_coe.2 <|
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_le_of_densityFloor
          generator path index time source target densityFloor hDensityFloorPositive hTime
    _ = ((densityFloor⁻¹ : NNReal) : ENNReal) *
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration +
        (generator.rate source target : ENNReal) * ENNReal.ofReal duration := by
      rw [MeasureTheory.lintegral_add_left']
      · rw [show (fun time ↦
              ((rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path time source target / densityFloor : NNReal) : ENNReal)) =
            fun time ↦ ((densityFloor⁻¹ : NNReal) : ENNReal) *
              (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path time source target : ENNReal) by
            funext time
            simp [div_eq_inv_mul],
          MeasureTheory.lintegral_const_mul', MeasureTheory.lintegral_const,
          finiteOpenIntervalVolume_apply_univ]
        exact ENNReal.coe_ne_top
      · exact
          ((measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path source target).div measurable_const).coe_nnreal_ennreal.aemeasurable

/-- Physical source-mean ordered flow minus the target ordered flow on one state pair. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (source target : State) : ℝ :=
  (finiteStateTimeDependentMarkovEndpointProbability
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      time source).toReal *
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate time source target : ℝ) -
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue path.1 time source target

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Source-flow error splits exactly into transported density error and the already controlled
generated-target-flow defect. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (time : ℝ) (source target : State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
        generator path index time source target =
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index time source *
          ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index).rate time source target : ℝ) +
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator path index time source target := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
  ring

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every physical source-flow error coordinate is integrable on the complete physical
interval. -/
theorem integrable_rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (source target : State) :
    MeasureTheory.Integrable
      (fun time ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
          generator path index time source target)
      (finiteOpenIntervalVolume duration) := by
  by_cases hOffDiagonal : source ≠ target
  · let transition : FiniteStateOrderedOffDiagonalTransition State :=
      ⟨(source, target), hOffDiagonal⟩
    have hSource :=
      integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩ (Sum.inr transition)
    have hTarget : MeasureTheory.Integrable
        (rengerDirectionalFlowHybridBVFlowDerivative path.1 · transition)
        (finiteOpenIntervalVolume duration) := by
      exact MeasureTheory.SignedMeasure.integrable_rnDeriv
        (path.1.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
        (finiteOpenIntervalVolume duration)
    have hSource' : MeasureTheory.Integrable
        (fun time ↦
          (finiteStateTimeDependentMarkovEndpointProbability
            (rengerDirectionalFlowHybridBVTargetInitialPMF path)
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index) time source).toReal *
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time source target : ℝ))
        (finiteOpenIntervalVolume duration) := by
      simpa only [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
        transition] using! hSource
    have hTarget' : MeasureTheory.Integrable
        (fun time ↦ rengerDirectionalFlowHybridBVRawFlowDerivativeValue
          path.1 time source target)
        (finiteOpenIntervalVolume duration) := by
      rw [show (fun time ↦ rengerDirectionalFlowHybridBVRawFlowDerivativeValue
          path.1 time source target) =
          fun time ↦ rengerDirectionalFlowHybridBVFlowDerivative
            path.1 time transition by
        funext time
        simp [rengerDirectionalFlowHybridBVRawFlowDerivativeValue,
          hOffDiagonal, transition]]
      exact hTarget
    simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError,
      Pi.sub_def] using! hSource'.sub hTarget'
  · have hDiagonal : source = target := not_ne_iff.mp hOffDiagonal
    subst target
    simp [rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError,
      rengerDirectionalFlowHybridBVRawFlowDerivativeValue, hOffDiagonal,
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate_self]

/-- At almost every physical time, each coordinate density error is controlled by twice the
complete integrated target-flow defect. -/
theorem ae_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_totalDefect
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index time state| ≤
        2 *
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
            generator path index).toReal := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with time hTime
  calc
    |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
        generator path index time state| ≤
      ∑ observed,
        |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
          generator path index time observed| :=
      Finset.single_le_sum
        (f := fun observed ↦
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
            generator path index time observed|)
        (fun _observed _hObserved ↦ abs_nonneg _)
        (Finset.mem_univ state)
    _ ≤ 2 *
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
          generator path index).toReal :=
      (sum_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_integral
        generator hDuration path hDynamicRate index hTime.1.le hTime.2).trans <|
          integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect_le_total
            generator hDuration path hDynamicRate index hTime.1.le hTime.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The finite-state total target-flow defect is finite at every canonical index. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_ne_top
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
        generator path index ≠ ⊤ := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
  exact ENNReal.sum_ne_top.mpr fun source _hSource ↦
    ENNReal.sum_ne_top.mpr fun target _hTarget ↦ by
      have hIntegrable :=
        integrable_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
          generator hDuration path hDynamicRate index source target
      rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect]
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hIntegrable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun _time ↦ abs_nonneg _)).mpr hIntegrable

/-- Integrated absolute source-mean flow error on one ordered state pair. -/
noncomputable def
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (source target : State) : ENNReal :=
  ∫⁻ time,
    ENNReal.ofReal
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
        generator path index time source target|
    ∂finiteOpenIntervalVolume duration

/-- Uniform density stability converts the physical source-flow error into the product of the
total forcing defect and target-source rate mass, plus the direct channel forcing defect. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) (source target : State) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
        generator path index source target ≤
      2 *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
            generator path index *
          ∫⁻ time,
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration +
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
          generator path index source target := by
  have hTotalFinite :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_ne_top
      generator hDuration path hDynamicRate index
  have hPointwise : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ENNReal.ofReal
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
            generator path index time source target| ≤
        2 *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index *
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time source target : ENNReal) +
          ENNReal.ofReal
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
              generator path index time source target| := by
    filter_upwards [
      ae_abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError_le_totalDefect
        generator hDuration path hDynamicRate index source] with time hDensity
    let densityError :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetDensityError
        generator path index time source
    let rate : ℝ :=
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate time source target : ℝ)
    let flowDefect :=
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
        generator path index time source target
    have hRateNonnegative : 0 ≤ rate := NNReal.coe_nonneg _
    have hAbsolute : |densityError * rate + flowDefect| ≤
        |densityError| * rate + |flowDefect| := by
      calc
        |densityError * rate + flowDefect| ≤
            |densityError * rate| + |flowDefect| := abs_add_le _ _
        _ = |densityError| * rate + |flowDefect| := by
          rw [abs_mul, abs_of_nonneg hRateNonnegative]
    rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError_eq]
    change ENNReal.ofReal |densityError * rate + flowDefect| ≤ _
    calc
      ENNReal.ofReal |densityError * rate + flowDefect| ≤
          ENNReal.ofReal (|densityError| * rate + |flowDefect|) :=
        ENNReal.ofReal_le_ofReal hAbsolute
      _ = ENNReal.ofReal |densityError| * ENNReal.ofReal rate +
          ENNReal.ofReal |flowDefect| := by
        rw [ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (NNReal.coe_nonneg _))
          (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
      _ ≤ (2 *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index) * ENNReal.ofReal rate +
          ENNReal.ofReal |flowDefect| := by
        gcongr
        calc
          ENNReal.ofReal |densityError| ≤
              ENNReal.ofReal (2 *
                (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                  generator path index).toReal) := ENNReal.ofReal_le_ofReal hDensity
          _ = 2 *
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                generator path index := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
              ENNReal.ofReal_toReal hTotalFinite]
      _ = _ := by
        rw [ENNReal.ofReal_coe_nnreal]
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
  calc
    _ ≤ ∫⁻ time,
        2 *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index *
            ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time source target : ENNReal) +
          ENNReal.ofReal
            |rengerDirectionalFlowHybridBVCanonicalPositiveTargetFlowDefect
              generator path index time source target|
        ∂finiteOpenIntervalVolume duration := MeasureTheory.lintegral_mono_ae hPointwise
    _ = _ := by
      rw [MeasureTheory.lintegral_add_left']
      · rw [MeasureTheory.lintegral_const_mul' _ _ <|
            ENNReal.mul_ne_top (by simp) hTotalFinite,
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect]
      · exact
          ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index).measurable_rate source target).coe_nnreal_ennreal.const_mul
              (2 *
                rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                  generator path index) |>.aemeasurable

/-- With a positive target-density floor, every physical source-mean ordered-flow derivative
converges in complete-interval `L1` to its target derivative. -/
theorem
  tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError_atTop_of_densityFloor
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (densityFloor : NNReal) (hDensityFloorPositive : 0 < densityFloor)
    (source target : State)
    (hDensityFloor : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      densityFloor ≤ rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source) :
    Tendsto
      (fun index : ℕ ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
          generator path index source target)
      atTop (nhds 0) := by
  by_cases hDiagonal : source = target
  · subst target
    have hErrorZero (index : ℕ) (time : ℝ) :
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
          generator path index time source source = 0 := by
      unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetSourceFlowError
        rengerDirectionalFlowHybridBVRawFlowDerivativeValue
      rw [(rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index).rate_self]
      simp
    simp [rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError,
      hErrorZero]
  let rateMassBound : ENNReal :=
    ((densityFloor⁻¹ : NNReal) : ENNReal) *
        ∫⁻ time,
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path.1 time source target : ENNReal)
          ∂finiteOpenIntervalVolume duration +
      (generator.rate source target : ENNReal) * ENNReal.ofReal duration
  have hTargetFlowFinite :
      (∫⁻ time,
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ :=
    lintegral_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_ne_top
      generator hDuration path hDynamicRate hDiagonal
  have hRateMassBoundFinite : rateMassBound ≠ ⊤ := by
    dsimp only [rateMassBound]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hTargetFlowFinite,
        ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top⟩
  have hRateMass (index : ℕ) :
      (∫⁻ time,
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index).rate time source target : ENNReal)
        ∂finiteOpenIntervalVolume duration) ≤ rateMassBound := by
    exact
      lintegral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_le_of_densityFloor
        generator path.1 densityFloor hDensityFloorPositive source target hDensityFloor index
  have hTotal :=
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect_atTop
      generator hDuration path hDynamicRate
  have hChannel :=
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect_atTop
      generator hDuration path hDynamicRate source target
  have hProduct :
      Tendsto
        (fun index : ℕ ↦
          2 *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
              generator path index * rateMassBound)
        atTop (nhds 0) := by
    have hTwoTotal :
        Tendsto
          (fun index : ℕ ↦
            2 *
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                generator path index)
          atTop (nhds 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hTotal (Or.inr (by simp))
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hTwoTotal (Or.inr hRateMassBoundFinite)
  have hUpper :
      Tendsto
        (fun index : ℕ ↦
          2 *
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                generator path index * rateMassBound +
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedFlowDefect
              generator path index source target)
        atTop (nhds 0) := by
    simpa only [zero_add] using hProduct.add hChannel
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpper
  · exact Filter.Eventually.of_forall fun _index ↦ zero_le
  · exact Filter.Eventually.of_forall fun index ↦
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError_le
        generator hDuration path hDynamicRate index source target).trans <|
          add_le_add
            (mul_le_mul_right
              (hRateMass index)
              (2 *
                rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedFlowDefect
                  generator path index)) le_rfl

/-- Every positive reference-evolution perturbation with coordinatewise positive initial law
meets the complete directional-flow source-mean convergence condition. -/
theorem
  tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetIntegratedSourceFlowError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (source target : State) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    Tendsto
      (fun index : ℕ ↦
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
          generator perturbed index source target)
      atTop (nhds 0) := by
  dsimp only
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
      generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
  have hPerturbedDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration perturbed.1 ≠ ⊤ := by
    have hUpper :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_dynamicRate_le
        generator path mixingWeight hMixingWeightLeOne
    have hFinite :
        ((1 - mixingWeight : NNReal) : ENNReal) *
            rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hDynamicRate
    exact ne_top_of_le_ne_top hFinite hUpper
  exact
    tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError_atTop_of_densityFloor
      generator hDuration perturbed hPerturbedDynamicRate
      (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor
        generator path mixingWeight source)
      (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor_pos
        generator path mixingWeight hMixingWeight source (hInitial source))
      source target
      (ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityFloor_le
        generator path mixingWeight hMixingWeightLeOne source)

/-- Complete finite-state integrated physical source-flow error. -/
noncomputable def
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) : ENNReal :=
  ∑ source, ∑ target,
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetIntegratedSourceFlowError
      generator path index source target

/-- The complete finite family of physical source-flow errors vanishes for every positive
reference-evolution perturbation with coordinatewise positive initial law. -/
theorem
  tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetTotalIntegratedSourceFlowError_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (mixingWeight : NNReal) (hMixingWeight : 0 < mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state) :
    let perturbed :=
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
        generator path mixingWeight mixingWeight.coe_nonneg hMixingWeightLeOne
    Tendsto
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
        generator perturbed)
      atTop (nhds 0) := by
  dsimp only
  unfold
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetTotalIntegratedSourceFlowError
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ fun source _hSource ↦
      tendsto_finsetSum Finset.univ fun target _hTarget ↦
        tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedTargetIntegratedSourceFlowError_atTop
          generator hDuration path hDynamicRate mixingWeight hMixingWeight
          hMixingWeightLeOne hInitial source target)

end

end FiniteMarkovProcesses.InformationTheory
