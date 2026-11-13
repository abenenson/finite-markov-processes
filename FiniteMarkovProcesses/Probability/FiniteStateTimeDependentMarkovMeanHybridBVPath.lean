/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalIntegralDerivative
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservation
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovForwardDerivative
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Mean hybrid-BV path of a finite-state time-dependent Markov law

This module packages the arbitrary-initial-PMF endpoint density and integrated ordered jump
intensities as one genuine hybrid-BV path.  Its signed derivatives are the literal
physical-time densities, not opaque bounded-variation witnesses.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Initial coordinate of the mean density--cumulative-directional-flow path. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVInitialValue
    (initial : PMF State)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) : ℝ :=
  match coordinate with
  | Sum.inl state => (initial state).toReal
  | Sum.inr _edge => 0

/-- Instantaneous derivative coordinate of the mean hybrid path: forward drift for density and
occupied-source intensity for one-way flow. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) : ℝ :=
  match coordinate with
  | Sum.inl state =>
      finiteStateTimeDependentMarkovEndpointProbabilityDrift initial rates time state
  | Sum.inr edge =>
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time edge.val.1).toReal *
        (rates.rate time edge.val.1 edge.val.2 : ℝ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The mean derivative satisfies the finite-state continuity equation pointwise:
density drift is incoming generated directional flow minus outgoing generated directional flow. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue_density_eq_flowBalance
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates time (Sum.inl state) =
      (∑ source : {source : State // source ≠ state},
          finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue initial rates time
            (Sum.inr ⟨(source, state), source.property⟩)) -
        ∑ target : {target : State // target ≠ state},
          finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue initial rates time
            (Sum.inr ⟨(state, target), target.property.symm⟩) := by
  rw [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
    finiteStateTimeDependentMarkovEndpointProbabilityDrift_eq_flowDivergence]
  unfold finiteStateFlowDivergence
  rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
    Fintype.sum_eq_add_sum_subtype_ne _ state]
  simp only [finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue,
    rates.rate_self, NNReal.coe_zero, mul_zero, zero_add]

/-- Continuous primitive value of the arbitrary-PMF mean hybrid path. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration time : ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
    fun coordinate =>
      finiteIntervalIntegralPrimitive
        (finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial coordinate)
        duration
        (fun markedTime =>
          finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
            initial rates markedTime coordinate)
        time

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Density-coordinate formula for the mean hybrid primitive. -/
@[simp]
theorem finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inl state) =
      finiteIntervalIntegralPrimitive (initial state).toReal duration
        (fun markedTime =>
          finiteStateTimeDependentMarkovEndpointProbabilityDrift
            initial rates markedTime state)
        time := by
  simp [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime,
    finiteStateTimeDependentMarkovMeanHybridBVInitialValue,
    finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Flow-coordinate formula for the mean hybrid primitive. -/
@[simp]
theorem finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration time : ℝ) (edge : FiniteStateOffDiagonalEdge State) :
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inr edge) =
      finiteIntervalIntegralPrimitive 0 duration
        (fun markedTime =>
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime edge.val.1).toReal *
            (rates.rate markedTime edge.val.1 edge.val.2 : ℝ))
        time := by
  simp [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime,
    finiteStateTimeDependentMarkovMeanHybridBVInitialValue,
    finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every derivative coordinate of the arbitrary-PMF mean path is integrable on physical time. -/
theorem integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    Integrable
      (fun time => finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates time coordinate)
      (finiteOpenIntervalVolume (duration : ℝ)) := by
  cases coordinate with
  | inl state =>
      simpa only [finiteOpenIntervalVolume, IntegrableOn,
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue] using
        integrableOn_finiteStateTimeDependentMarkovEndpointProbabilityDrift
          initial rates duration state
  | inr edge =>
      simpa only [finiteOpenIntervalVolume, IntegrableOn,
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue] using
        integrableOn_endpointProbability_mul_timeDependentMarkovRate
          initial rates duration edge.property

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The arbitrary-PMF mean hybrid primitive is globally continuous. -/
theorem continuous_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    Continuous
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration) := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm.continuous.comp
  rw [continuous_pi_iff]
  intro coordinate
  exact continuous_finiteIntervalIntegralPrimitive
    (finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial coordinate)
    duration
    (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
      initial rates duration coordinate)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The continuous arbitrary-PMF mean primitive belongs to the physical strong-`L1` carrier. -/
theorem memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    MemLp
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration)
      1 (finiteOpenIntervalVolume (duration : ℝ)) := by
  rw [memLp_one_iff_integrable]
  unfold finiteOpenIntervalVolume
  exact (ContinuousOn.integrableOn_compact isCompact_Icc
    (continuous_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration).continuousOn).mono_set Ioo_subset_Icc_self

/-- Strong-`L1` quotient of the arbitrary-PMF mean hybrid primitive. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVL1Path
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalL1Path
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ) :=
  FiniteIntervalL1Path.ofFunction
    (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration)
    (memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The raw mean primitive represents its quotient definitionally. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalL1Path.Represents
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration)
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration) := by
  exact
    ⟨memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration, rfl⟩

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The arbitrary-PMF mean primitive has bounded variation on physical time. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVL1Path_hasBoundedVariation
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalL1Path.HasBoundedVariation
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration) := by
  apply FiniteIntervalL1Path.hasBoundedVariation_of_represents
    (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents
      initial rates duration)
  apply FiniteIntervalBVAlgebra.boundedVariationOn_finiteCoordinateL1Value_of_coordinate
  intro coordinate
  simpa only [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime,
    PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp] using!
    boundedVariationOn_finiteIntervalIntegralPrimitive
      (finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial coordinate)
      (duration : ℝ)
      (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates duration coordinate)

/-- Genuine hybrid-BV path of the arbitrary-PMF Markov mean. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVPath
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ) :=
  FiniteIntervalHybridBVPath.ofScalarDerivativeWitnesses
    (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents
      initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVL1Path_hasBoundedVariation
      initial rates duration)
    fun coordinate => ScalarFiniteIntervalCadlagDerivativeWitness.ofIntegral
      (finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial coordinate)
      (duration : ℝ)
      (fun time => finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates time coordinate)
      (integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
        initial rates duration coordinate)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every signed derivative coordinate is the literal physical-time density measure. -/
@[simp]
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_derivative
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    FiniteIntervalL1DerivativePath.derivative
        (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
        coordinate =
      VagueSignedMeasure.ofSignedMeasure
        ((finiteOpenIntervalVolume (duration : ℝ)).withDensityᵥ
          fun time => finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
            initial rates time coordinate) := by
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The arbitrary-PMF mean hybrid path has absolutely continuous coordinate derivatives. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_hasAbsolutelyContinuousDerivative
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalHybridBVPath.HasAbsolutelyContinuousDerivative
      (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration) := by
  intro coordinate
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_derivative,
    VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
  exact Measure.withDensityᵥ_absolutelyContinuous _ _

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Restricting the physical-time measure to an earlier open interval recovers ordinary
Lebesgue measure there, including at the terminal horizon. -/
theorem finiteOpenIntervalVolume_restrict_Ioo_zero_eq_volume_restrict_Ioo_of_le
    {time duration : ℝ} (hTimeDuration : time ≤ duration) :
    (finiteOpenIntervalVolume duration).restrict (Ioo 0 time) =
      volume.restrict (Ioo 0 time) := by
  unfold finiteOpenIntervalVolume
  rw [Measure.restrict_restrict measurableSet_Ioo]
  congr 1
  apply inter_eq_left.mpr
  intro markedTime hMarkedTime
  exact ⟨hMarkedTime.1, hMarkedTime.2.trans_le hTimeDuration⟩

/-- On the full nonnegative physical interval, the primitive density coordinate is the exact
endpoint probability. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (hTimeDuration : time ≤ duration) (state : State) :
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inl state) =
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time state).toReal := by
  rw [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density,
    finiteIntervalIntegralPrimitive]
  have hForward :
      (finiteStateTimeDependentMarkovEndpointProbability
          initial rates time state).toReal =
        (initial state).toReal +
          ∫ markedTime : ℝ in Ioo 0 time,
            finiteStateTimeDependentMarkovEndpointProbabilityDrift
              initial rates markedTime state := by
    simpa only [NNReal.coe_mk] using!
      finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_integral_drift
        initial rates ⟨time, hTimeNonnegative⟩ state
  rw [hForward]
  congr 1
  rw [intervalIntegral.integral_of_le hTimeNonnegative,
    integral_Ioc_eq_integral_Ioo]
  change
    (∫ markedTime : ℝ,
        finiteStateTimeDependentMarkovEndpointProbabilityDrift
          initial rates markedTime state
      ∂(finiteOpenIntervalVolume (duration : ℝ)).restrict (Ioo 0 time)) =
      ∫ markedTime : ℝ,
        finiteStateTimeDependentMarkovEndpointProbabilityDrift
          initial rates markedTime state
      ∂volume.restrict (Ioo 0 time)
  rw [finiteOpenIntervalVolume_restrict_Ioo_zero_eq_volume_restrict_Ioo_of_le
    hTimeDuration]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every mean cumulative ordered-flow primitive is nonnegative on nonnegative physical time. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow_nonnegative
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (edge : FiniteStateOffDiagonalEdge State) :
    0 ≤ finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration time (Sum.inr edge) := by
  rw [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow,
    finiteIntervalIntegralPrimitive]
  simp only [zero_add]
  exact intervalIntegral.integral_nonneg_of_ae
    (μ := finiteOpenIntervalVolume (duration : ℝ)) hTimeNonnegative
    (Filter.Eventually.of_forall fun markedTime => mul_nonneg ENNReal.toReal_nonneg
      (rates.rate markedTime edge.val.1 edge.val.2).coe_nonneg)

/-- Explicit continuous representative of the arbitrary-PMF mean hybrid path. -/
noncomputable def finiteStateTimeDependentMarkovMeanHybridBVCadlagRepresentative
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    FiniteIntervalCadlagRepresentative
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration) where
  representative :=
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration
  represents := finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents
    initial rates duration
  rightContinuous := by
    intro time _hTime
    exact (continuous_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration).continuousAt.continuousWithinAt
  hasLeftLimit := by
    intro time _hTime
    exact
      ⟨finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
          initial rates duration time,
        (continuous_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
          initial rates duration).continuousAt.continuousWithinAt.tendsto⟩

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The canonical hybrid representative agrees pointwise with the explicit mean primitive on the
physical half-open interval. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTime : time ∈ Ico 0 (duration : ℝ)) :
    FiniteIntervalCadlagRepresentative.representative
        (finiteStateTimeDependentMarkovMeanHybridBVPath
          initial rates duration).cadlagRepresentative time =
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time := by
  exact FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
    (finiteStateTimeDependentMarkovMeanHybridBVPath
      initial rates duration).cadlagRepresentative
    (finiteStateTimeDependentMarkovMeanHybridBVCadlagRepresentative
      initial rates duration) hTime

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The recovered initial trace is exactly the supplied PMF density with zero cumulative flow. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_initialTrace
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ≥0} (hDuration : 0 < duration) :
    (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).initialTrace =
      (PiLp.continuousLinearEquiv 1 ℝ
        (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
          (finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial) := by
  rw [FiniteIntervalHybridBVPath.initialTrace_eq_of_cadlagRepresentative
    (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration)
    (finiteStateTimeDependentMarkovMeanHybridBVCadlagRepresentative
      initial rates duration) (by exact_mod_cast hDuration)]
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).injective
  funext coordinate
  change finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration 0 coordinate =
    finiteStateTimeDependentMarkovMeanHybridBVInitialValue initial coordinate
  simp [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime,
    finiteIntervalIntegralPrimitive]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The recovered terminal trace is the explicit mean primitive at the terminal horizon. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVPath_terminalTrace
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ≥0} (hDuration : 0 < duration) :
    (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).terminalTrace
        (by exact_mod_cast hDuration) =
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration duration := by
  apply tendsto_nhds_unique
    (FiniteIntervalHybridBVPath.tendsto_terminalTrace
      (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration)
      (by exact_mod_cast hDuration))
  apply
    (continuous_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
      initial rates duration).continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by exact_mod_cast hDuration)),
      self_mem_nhdsWithin] with time hTimePositive hTimeUpper
  exact (finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
    initial rates duration ⟨le_of_lt hTimePositive, hTimeUpper⟩).symm

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The Radon--Nikodym derivative of the mean hybrid path recovers the explicit physical
derivative almost everywhere. -/
theorem ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume (duration : ℝ),
      FiniteIntervalHybridBVPath.derivativeDensity
          (finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration)
          coordinate time =
        finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
          initial rates time coordinate := by
  let path := finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration
  have hRNDensity : Integrable (path.derivativeDensity coordinate)
      (finiteOpenIntervalVolume (duration : ℝ)) :=
    SignedMeasure.integrable_rnDeriv
      (path.toDerivativePath.derivative coordinate).toSignedMeasure
      (finiteOpenIntervalVolume (duration : ℝ))
  have hExplicit :=
    integrable_finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
      initial rates duration coordinate
  apply hRNDensity.ae_eq_of_withDensityᵥ_eq hExplicit
  rw [path.withDensity_derivativeDensity_eq_derivative
      (finiteStateTimeDependentMarkovMeanHybridBVPath_hasAbsolutelyContinuousDerivative
        initial rates duration) coordinate,
    show path.toDerivativePath.derivative coordinate =
        VagueSignedMeasure.ofSignedMeasure
          ((finiteOpenIntervalVolume (duration : ℝ)).withDensityᵥ
            fun time => finiteStateTimeDependentMarkovMeanHybridBVDerivativeValue
              initial rates time coordinate) by
      exact finiteStateTimeDependentMarkovMeanHybridBVPath_derivative
        initial rates duration coordinate,
    VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]

end

end FiniteMarkovProcesses.Probability
