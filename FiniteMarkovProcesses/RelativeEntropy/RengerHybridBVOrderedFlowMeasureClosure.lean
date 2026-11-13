/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVKinematicClosure
public import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation
public import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureAbsoluteContinuityClosure

/-!
# Ordered-flow measure closure for Renger hybrid paths

This module upgrades the boundary-blind derivative convergence in the hybrid topology to genuine
vague convergence for every ordered-flow coordinate under one uniform finite dynamic-rate level.
The event-local coercivity modulus prevents variation from escaping through either endpoint, and
the closed positive cone then proves that every limiting ordered-flow derivative is a
nonnegative signed measure.

Absolute continuity of the limiting derivatives with respect to physical-time volume remains a
separate result.

## Main declarations

* `rengerDirectionalFlowHybridBVFlowDerivativeVagueTendstoOfUniformlyBoundedDynamicRate` proves
  full vague convergence of each ordered-flow derivative.
* `rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfUniformRateLimit`
  closes ordered-flow derivative nonnegativity at signed-measure level.
* `rengerDirectionalFlowHybridBVFlowDerivativeAbsolutelyContinuousOfUniformRateLimit` closes
  absolute continuity of each limiting ordered-flow derivative.
* `rengerDirectionalFlowHybridBVAdmissibleOfTendstoOfUniformlyBoundedDynamicRate` proves full
  sequential closure of the finite-rate representation domain inside a bounded action sublevel.
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

/-- One ordered-flow coordinate's derivative variation is bounded by the complete
density-plus-flow derivative variation. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeTotalVariationOn_le_totalDerivativeVariationOn
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (event : Set ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
        event ≤
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn path event := by
  unfold rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
    rengerDirectionalFlowHybridBVFlowDerivativeVariationOn
  calc
    (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.totalVariation
        event ≤
      ∑ candidate : FiniteStateOrderedOffDiagonalTransition State,
        (path.toDerivativePath.derivative (Sum.inr candidate)).toSignedMeasure.totalVariation
          event := by
      exact Finset.single_le_sum
        (fun candidate _ => show (0 : ENNReal) ≤
          (path.toDerivativePath.derivative (Sum.inr candidate)).toSignedMeasure.totalVariation
            event from zero_le)
        (Finset.mem_univ transition)
    _ ≤ rengerDirectionalFlowHybridBVDensityDerivativeVariationOn path event +
        ∑ candidate : FiniteStateOrderedOffDiagonalTransition State,
          (path.toDerivativePath.derivative (Sum.inr candidate)).toSignedMeasure.totalVariation
            event := le_add_of_nonneg_left (zero_le)

/-- An admissible ordered-flow derivative is a nonnegative signed measure. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfAdmissible
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    0 ≤ (path.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure := by
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hPath.absolutelyContinuousDerivative (Sum.inr transition)]
  exact SignedMeasure.zero_le_withDensityᵥ_of_ae_nonnegative
    (SignedMeasure.integrable_rnDeriv _ _)
    (hPath.flowDerivativeNonnegativeAE.mono fun _ hTime => hTime transition)

/-- One uniform finite dynamic-rate level supplies the boundary-variation premise needed to
upgrade a fixed ordered-flow coordinate from relative to genuine vague convergence. -/
theorem
    exists_rengerDirectionalFlowHybridBVFlowDerivativeBoundaryVariationOfUniformRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ margin : ℝ, 0 < margin ∧
      (∀ sequenceIndex,
        ((paths sequenceIndex).toDerivativePath.derivative
          (Sum.inr transition)).toSignedMeasure.totalVariation.real
            (finiteOpenIntervalBoundaryLayer duration margin) ≤ epsilon) ∧
      (limitPath.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure.totalVariation.real
          (finiteOpenIntervalBoundaryLayer duration margin) ≤ epsilon := by
  have hLimitSupport :
      (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure.restrict
          (Set.Ioo 0 duration) =
        (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure :=
    (Classical.choose_spec limitPath.hasCadlagDerivativeRealization).1 (Sum.inr transition)
  obtain ⟨limitMargin, hLimitMargin, hLimitBoundary⟩ :=
    SignedMeasure.exists_positive_margin_totalVariation_real_boundaryLayer_lt
      (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
      hDuration hEpsilon hLimitSupport
  have hMarginTendsto : Tendsto
      (fun eventIndex : ℕ => duration / (eventIndex + 3 : ℕ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp
      (Filter.tendsto_add_atTop_nat 3)
  have hMarginEventually : ∀ᶠ eventIndex : ℕ in atTop,
      duration / (eventIndex + 3 : ℕ) < limitMargin :=
    (tendsto_order.1 hMarginTendsto).2 limitMargin hLimitMargin
  obtain ⟨minimumIndex, hMarginAfter⟩ := eventually_atTop.mp hMarginEventually
  let events : ℕ → Set ℝ := fun eventIndex =>
    finiteOpenIntervalBoundaryLayer duration
      (duration / ((eventIndex + minimumIndex) + 3 : ℕ))
  have hEventVolume : Tendsto
      (fun eventIndex => finiteOpenIntervalVolume duration (events eventIndex))
      atTop (nhds 0) := by
    simpa only [events, Function.comp_def] using!
      (tendsto_finiteOpenIntervalVolume_boundaryLayer_div_nat_zero hDuration).comp
        (Filter.tendsto_add_atTop_nat minimumIndex)
  obtain ⟨eventIndex, hSequenceBoundary⟩ :=
    exists_eventIndex_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
      generator hDuration paths events
        (fun _ => measurableSet_finiteOpenIntervalBoundaryLayer _ _)
        hEventVolume hPaths hLevel hRates (ENNReal.ofReal_pos.mpr hEpsilon)
  let margin := duration / ((eventIndex + minimumIndex) + 3 : ℕ)
  have hMarginOrder : margin < limitMargin := by
    exact hMarginAfter (eventIndex + minimumIndex) (by omega)
  have hMarginPositive : 0 < margin := by
    dsimp only [margin]
    positivity
  refine ⟨margin, hMarginPositive, ?_, ?_⟩
  · intro sequenceIndex
    have hCoordinateENNReal :
        (((paths sequenceIndex).toDerivativePath.derivative (Sum.inr transition))
            |>.toSignedMeasure |>.totalVariation) (events eventIndex) ≤
          ENNReal.ofReal epsilon :=
      (rengerDirectionalFlowHybridBVFlowDerivativeTotalVariationOn_le_totalDerivativeVariationOn
        (paths sequenceIndex) (events eventIndex) transition).trans
          (hSequenceBoundary sequenceIndex)
    have hCoordinateReal :=
      ENNReal.toReal_mono (by simp) hCoordinateENNReal
    simpa only [measureReal_def, events, margin,
      ENNReal.toReal_ofReal hEpsilon.le] using hCoordinateReal
  · have hBoundarySubset :
        finiteOpenIntervalBoundaryLayer duration margin ⊆
          finiteOpenIntervalBoundaryLayer duration limitMargin :=
      finiteOpenIntervalBoundaryLayer_mono hMarginOrder.le
    exact (measureReal_mono hBoundarySubset
      (by simp [SignedMeasure.totalVariation])).trans hLimitBoundary.le

/-- Under bounded-rate hybrid convergence, every ordered-flow derivative converges genuinely
vaguely, not merely against tests vanishing at the temporal boundary. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeVagueTendstoOfUniformlyBoundedDynamicRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto paths atTop (nhds limitPath))
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    Tendsto
      (fun sequenceIndex =>
        (paths sequenceIndex).toDerivativePath.derivative (Sum.inr transition))
      atTop
      (nhds (limitPath.toDerivativePath.derivative (Sum.inr transition))) := by
  apply VagueSignedMeasure.tendsto_of_relative_continuousTestIntegral_of_boundaryVariation
  · exact (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).2 (Sum.inr transition)
  · intro epsilon hEpsilon
    exact
      exists_rengerDirectionalFlowHybridBVFlowDerivativeBoundaryVariationOfUniformRate
        generator hDuration paths limitPath hPaths hLevel hRates transition epsilon hEpsilon

/-- The limiting ordered-flow derivative is nonnegative at signed-measure level under bounded-rate
hybrid convergence. -/
theorem
    rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfUniformRateLimit
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto paths atTop (nhds limitPath))
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    0 ≤ (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure := by
  exact VagueSignedMeasure.zero_le_toSignedMeasure_of_tendsto_of_zero_le
    (rengerDirectionalFlowHybridBVFlowDerivativeVagueTendstoOfUniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hTendsto transition)
    (fun sequenceIndex =>
      rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfAdmissible
        (hPaths sequenceIndex) transition)

/-- Uniform finite dynamic rate prevents an ordered-flow derivative from acquiring a singular
part in the hybrid limit. -/
theorem rengerDirectionalFlowHybridBVFlowDerivativeAbsolutelyContinuousOfUniformRateLimit
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto paths atTop (nhds limitPath))
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure ≪ᵥ
      (finiteOpenIntervalVolume duration).toENNRealVectorMeasure := by
  apply VagueSignedMeasure.absolutelyContinuous_toSignedMeasure_of_tendsto_of_uniformVariation
    (Index := ℕ) (indexFilter := atTop)
    (measures := fun sequenceIndex =>
      (paths sequenceIndex).toDerivativePath.derivative (Sum.inr transition))
    (limit := limitPath.toDerivativePath.derivative (Sum.inr transition))
    (finiteOpenIntervalVolume duration)
  · exact
      rengerDirectionalFlowHybridBVFlowDerivativeVagueTendstoOfUniformlyBoundedDynamicRate
        generator hDuration paths limitPath hPaths hLevel hRates hTendsto transition
  · exact fun sequenceIndex =>
      rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfAdmissible
        (hPaths sequenceIndex) transition
  · intro epsilon hEpsilon
    obtain ⟨delta, hDelta, hVariation⟩ :=
      exists_eventVolume_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
        generator hDuration paths hPaths hLevel hRates hEpsilon
    refine ⟨delta, hDelta, fun sequenceIndex event hEvent hEventVolume => ?_⟩
    exact
      (rengerDirectionalFlowHybridBVFlowDerivativeTotalVariationOn_le_totalDerivativeVariationOn
        (paths sequenceIndex) event transition).trans
          (hVariation sequenceIndex event hEvent hEventVolume)

/-- Once every limiting ordered-flow derivative is absolutely continuous, the exact limiting
signed-measure continuity equation forces every limiting density derivative to be absolutely
continuous as well. -/
theorem rengerDirectionalFlowHybridBVDensityDerivativeAbsolutelyContinuousOfUniformRateLimit
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto paths atTop (nhds limitPath))
    (state : State) :
    (limitPath.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure ≪ᵥ
      (finiteOpenIntervalVolume duration).toENNRealVectorMeasure := by
  have hKinematic :=
    rengerDirectionalFlowHybridBVKinematicConstraints_of_tendsto_of_uniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hTendsto
  rw [hKinematic.derivativeContinuity state]
  apply VectorMeasure.AbsolutelyContinuous.sub
  · apply VectorMeasure.AbsolutelyContinuous.mk
    intro event hEvent hEventZero
    rw [signedMeasure_fintypeSum_apply]
    apply Finset.sum_eq_zero
    intro source _
    exact
      rengerDirectionalFlowHybridBVFlowDerivativeAbsolutelyContinuousOfUniformRateLimit
        generator hDuration paths limitPath hPaths hLevel hRates hTendsto
          ⟨(source, state), source.property⟩ hEventZero
  · apply VectorMeasure.AbsolutelyContinuous.mk
    intro event hEvent hEventZero
    rw [signedMeasure_fintypeSum_apply]
    apply Finset.sum_eq_zero
    intro target _
    exact
      rengerDirectionalFlowHybridBVFlowDerivativeAbsolutelyContinuousOfUniformRateLimit
        generator hDuration paths limitPath hPaths hLevel hRates hTendsto
          ⟨(state, target), target.property.symm⟩ hEventZero

/-- Full finite-rate Renger admissibility is sequentially closed under hybrid convergence inside
one uniformly bounded dynamic-rate sublevel. -/
theorem rengerDirectionalFlowHybridBVAdmissibleOfTendstoOfUniformlyBoundedDynamicRate
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
    RengerDirectionalFlowHybridBVAdmissible limitPath hDuration := by
  classical
  have hKinematic :=
    rengerDirectionalFlowHybridBVKinematicConstraints_of_tendsto_of_uniformlyBoundedDynamicRate
      generator hDuration paths limitPath hPaths hLevel hRates hTendsto
  have hAbsolutelyContinuous : limitPath.HasAbsolutelyContinuousDerivative := by
    intro coordinate
    cases coordinate with
    | inl state =>
        exact
          rengerDirectionalFlowHybridBVDensityDerivativeAbsolutelyContinuousOfUniformRateLimit
            generator hDuration paths limitPath hPaths hLevel hRates hTendsto state
    | inr transition =>
        exact
          rengerDirectionalFlowHybridBVFlowDerivativeAbsolutelyContinuousOfUniformRateLimit
            generator hDuration paths limitPath hPaths hLevel hRates hTendsto transition
  have hFlowDerivativeNonnegativeAE :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        ∀ transition,
          0 ≤ rengerDirectionalFlowHybridBVFlowDerivative limitPath time transition := by
    apply Filter.eventually_all.2
    intro transition
    exact SignedMeasure.rnDeriv_nonnegative_of_zero_le
      (limitPath.toDerivativePath.derivative (Sum.inr transition)).toSignedMeasure
      (finiteOpenIntervalVolume duration)
      (rengerDirectionalFlowHybridBVFlowDerivativeMeasureNonnegativeOfUniformRateLimit
        generator hDuration paths limitPath hPaths hLevel hRates hTendsto transition)
  have hContinuityEquationAE :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        ∀ state,
          rengerDirectionalFlowHybridBVDensityDerivative limitPath time state =
            (∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative limitPath time
                ⟨(source, state), source.property⟩) -
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative limitPath time
                ⟨(state, target), target.property.symm⟩ := by
    apply Filter.eventually_all.2
    intro state
    let densityDerivative :=
      (limitPath.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure
    let incomingDerivative : SignedMeasure ℝ :=
      ∑ source : {source : State // source ≠ state},
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure
    let outgoingDerivative : SignedMeasure ℝ :=
      ∑ target : {target : State // target ≠ state},
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure
    have hDerivativeIdentity :
        densityDerivative = incomingDerivative - outgoingDerivative :=
      hKinematic.derivativeContinuity state
    have hDerivativeRNIdentity := congrArg
      (fun signedMeasure : SignedMeasure ℝ =>
        signedMeasure.rnDeriv (finiteOpenIntervalVolume duration))
      hDerivativeIdentity
    have hIncomingRN := SignedMeasure.rnDeriv_fintypeSum
      (fun source : {source : State // source ≠ state} =>
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure)
      (finiteOpenIntervalVolume duration)
    have hOutgoingRN := SignedMeasure.rnDeriv_fintypeSum
      (fun target : {target : State // target ≠ state} =>
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure)
      (finiteOpenIntervalVolume duration)
    have hSubRN := SignedMeasure.rnDeriv_sub incomingDerivative outgoingDerivative
      (finiteOpenIntervalVolume duration)
    filter_upwards [hIncomingRN, hOutgoingRN, hSubRN] with
      time hIncomingTime hOutgoingTime hSubTime
    change densityDerivative.rnDeriv (finiteOpenIntervalVolume duration) time =
      (∑ source : {source : State // source ≠ state},
        ((limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure.rnDeriv
            (finiteOpenIntervalVolume duration) time)) -
      ∑ target : {target : State // target ≠ state},
        ((limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure.rnDeriv
            (finiteOpenIntervalVolume duration) time)
    calc
      densityDerivative.rnDeriv (finiteOpenIntervalVolume duration) time =
          (incomingDerivative - outgoingDerivative).rnDeriv
            (finiteOpenIntervalVolume duration) time :=
        congrFun hDerivativeRNIdentity time
      _ = incomingDerivative.rnDeriv (finiteOpenIntervalVolume duration) time -
          outgoingDerivative.rnDeriv (finiteOpenIntervalVolume duration) time := hSubTime
      _ = _ := by
        rw [hIncomingTime, hOutgoingTime]
  exact
    { absolutelyContinuousDerivative := hAbsolutelyContinuous
      densityNonnegativeAE := hKinematic.valueConstraints.densityNonnegativeAE
      densityNormalizedAE := hKinematic.valueConstraints.densityNormalizedAE
      cumulativeFlowNonnegativeAE := hKinematic.valueConstraints.cumulativeFlowNonnegativeAE
      flowDerivativeNonnegativeAE := hFlowDerivativeNonnegativeAE
      continuityEquationAE := hContinuityEquationAE
      initialDensityNormalized := hKinematic.valueConstraints.initialDensityNormalized
      initialDensityNonnegative := hKinematic.valueConstraints.initialDensityNonnegative
      cumulativeFlowInitiallyZero := hKinematic.valueConstraints.cumulativeFlowInitiallyZero
      terminalDensityNormalized := hKinematic.valueConstraints.terminalDensityNormalized
      terminalDensityNonnegative := hKinematic.valueConstraints.terminalDensityNonnegative
      terminalCumulativeFlowNonnegative :=
        hKinematic.valueConstraints.terminalCumulativeFlowNonnegative }

end

end FiniteMarkovProcesses.InformationTheory
