/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVTerminalTrace
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVEventCoercivity

/-!
# Boundary traces for Renger hybrid paths

This module specializes source-neutral hybrid-BV boundary-trace closure to the exact finite-rate
Renger representation domain.  One uniform finite dynamic-rate level supplies path-independent
initial- and terminal-neighborhood derivative-variation moduli, which combine with strong `L1`
convergence to recover both separately represented boundary traces.

No ambient continuity of either boundary trace, converse dual representation, lower
semicontinuity, or large-deviation bound is asserted here.

## Main results

* `exists_initialEndpoint_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate`
  gives one initial neighborhood working uniformly across a rate-bounded family.
* `rengerDirectionalFlowHybridBVTendstoInitialTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate`
  closes the initial traces of a strongly `L1`-convergent rate-bounded sequence.
* `rengerDirectionalFlowHybridBVTendstoTerminalTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate`
  supplies the exact terminal counterpart.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.FiniteIntervalHybridBVPath
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The density-plus-flow split of event-local Renger variation is exactly the generic
coordinatewise hybrid-BV variation. -/
theorem rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_eq_generic
    (path : RengerDirectionalFlowHybridBVPath State duration) (event : Set ℝ) :
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn path event =
      finiteIntervalHybridBVDerivativeTotalVariationOn path event := by
  unfold rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
    rengerDirectionalFlowHybridBVDensityDerivativeVariationOn
    rengerDirectionalFlowHybridBVFlowDerivativeVariationOn
    finiteIntervalHybridBVDerivativeTotalVariationOn
  rw [Fintype.sum_sum_type]

/-- Along any measurable event sequence of vanishing physical-time volume, a uniform finite
dynamic-rate level supplies one event that has arbitrarily small complete derivative variation
simultaneously for the whole path family. -/
theorem
    exists_eventIndex_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (events : ℕ → Set ℝ) (hEvents : ∀ eventIndex, MeasurableSet (events eventIndex))
    (hEventVolume : Tendsto
      (fun eventIndex => finiteOpenIntervalVolume duration (events eventIndex))
      atTop (nhds 0))
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    {epsilon : ENNReal} (hEpsilon : 0 < epsilon) :
    ∃ eventIndex, ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths sequenceIndex) (events eventIndex) ≤ epsilon := by
  have hTwelfthEpsilon : 0 < epsilon / 12 :=
    ENNReal.div_pos_iff.mpr ⟨hEpsilon.ne', by norm_num⟩
  obtain ⟨exponent, hExponent, hLevelDiv⟩ :=
    exists_nnreal_exponent_level_div_le hLevel hTwelfthEpsilon
  let correction :=
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent generator exponent
  have hCorrectionFinite : correction ≠ ∞ :=
    rengerDirectionalFlowHybridBVGeneratorCorrectionAtExponent_ne_top generator exponent
  have hCorrectionTendsto : Tendsto
      (fun eventIndex => correction *
        finiteOpenIntervalVolume duration (events eventIndex) /
        (exponent : ENNReal)) atTop (nhds 0) := by
    have hMul : Tendsto
        (fun eventIndex => correction *
          finiteOpenIntervalVolume duration (events eventIndex))
        atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hEventVolume
        (Or.inr hCorrectionFinite)
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hMul
      (Or.inr (ENNReal.coe_ne_zero.mpr hExponent.ne'))
  obtain ⟨eventIndex, hCorrectionEventually⟩ :=
    eventually_atTop.mp
      (ENNReal.tendsto_nhds_zero.mp hCorrectionTendsto (epsilon / 12)
        hTwelfthEpsilon)
  refine ⟨eventIndex, fun sequenceIndex => ?_⟩
  calc
    rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths sequenceIndex) (events eventIndex) ≤
      3 * ((level + correction *
        finiteOpenIntervalVolume duration (events eventIndex)) /
          (exponent : ENNReal)) :=
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_finiteRateSublevelModulus
        generator hDuration (hPaths sequenceIndex) (hRates sequenceIndex) hExponent
          (hEvents eventIndex)
    _ = 3 * (level / (exponent : ENNReal) +
        correction * finiteOpenIntervalVolume duration (events eventIndex) /
          (exponent : ENNReal)) := by
      rw [ENNReal.add_div]
    _ ≤ 3 * (epsilon / 12 + epsilon / 12) :=
      mul_le_mul_right (add_le_add hLevelDiv
        (hCorrectionEventually eventIndex le_rfl)) 3
    _ = 6 * (epsilon / 12) := by ring
    _ ≤ 12 * (epsilon / 12) := by gcongr; norm_num
    _ = epsilon := ENNReal.mul_div_cancel (by norm_num) (by simp)

/-- A uniform finite dynamic-rate level supplies one initial neighborhood on which every path in
the family has arbitrarily small complete derivative variation. -/
theorem
    exists_initialEndpoint_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    {epsilon : ENNReal} (hEpsilon : 0 < epsilon) :
    ∃ endpoint ∈ Set.Ioo 0 duration, ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths sequenceIndex) (Set.Ioc 0 endpoint) ≤ epsilon := by
  let endpoint : ℕ → ℝ := fun index => duration / (index + 2 : ℕ)
  have hEndpoint (index : ℕ) : endpoint index ∈ Set.Ioo 0 duration := by
    have hIndex : 1 < index + 2 := by omega
    refine ⟨by dsimp only [endpoint]; positivity, ?_⟩
    dsimp only [endpoint]
    exact div_lt_self hDuration (by exact_mod_cast hIndex)
  have hEndpointTendsto : Tendsto endpoint atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp
      (tendsto_add_atTop_nat 2)
  have hEventVolume : Tendsto
      (fun index => finiteOpenIntervalVolume duration (Set.Ioc 0 (endpoint index)))
      atTop (nhds 0) := by
    have hOfReal := ENNReal.tendsto_ofReal hEndpointTendsto
    simpa only [ENNReal.ofReal_zero] using hOfReal.congr'
      (Filter.Eventually.of_forall fun index =>
        (finiteOpenIntervalVolume_Ioc_zero (hEndpoint index)).symm)
  obtain ⟨endpointIndex, hVariation⟩ :=
    exists_eventIndex_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
      generator hDuration paths (fun index => Set.Ioc 0 (endpoint index))
        (fun _ => measurableSet_Ioc) hEventVolume hPaths hLevel hRates hEpsilon
  exact ⟨endpoint endpointIndex, hEndpoint endpointIndex, hVariation⟩

/-- On the exact finite-rate representation domain, strong-`L1` convergence forces convergence
of the separately recovered initial traces. -/
theorem
    rengerDirectionalFlowHybridBVTendstoInitialTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limitPath.toDerivativePath.toL1Path)) :
    Tendsto (fun sequenceIndex => (paths sequenceIndex).initialTrace)
      atTop (nhds limitPath.initialTrace) := by
  apply tendsto_initialTrace_of_tendsto_toL1Path_of_uniformInitialDerivativeVariation
    hDuration paths limitPath hTendsto
  intro epsilon hEpsilon
  obtain ⟨endpoint, hEndpoint, hVariation⟩ :=
    exists_initialEndpoint_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
      generator hDuration paths hPaths hLevel hRates hEpsilon
  refine ⟨endpoint, hEndpoint, fun sequenceIndex => ?_⟩
  rw [← rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_eq_generic]
  exact hVariation sequenceIndex

/-- A uniform finite dynamic-rate level supplies one terminal neighborhood on which every path
in the family has arbitrarily small complete derivative variation. -/
theorem
    exists_terminalStart_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    {epsilon : ENNReal} (hEpsilon : 0 < epsilon) :
    ∃ start ∈ Set.Ioo 0 duration, ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVTotalDerivativeVariationOn
        (paths sequenceIndex) (Set.Ioc start duration) ≤ epsilon := by
  let width : ℕ → ℝ := fun index => duration / (index + 2 : ℕ)
  let start : ℕ → ℝ := fun index => duration - width index
  have hWidth (index : ℕ) : width index ∈ Set.Ioo 0 duration := by
    have hIndex : 1 < index + 2 := by omega
    refine ⟨by dsimp only [width]; positivity, ?_⟩
    dsimp only [width]
    exact div_lt_self hDuration (by exact_mod_cast hIndex)
  have hStart (index : ℕ) : start index ∈ Set.Ioo 0 duration := by
    exact ⟨sub_pos.mpr (hWidth index).2,
      sub_lt_self duration (hWidth index).1⟩
  have hWidthTendsto : Tendsto width atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp
      (tendsto_add_atTop_nat 2)
  have hEventVolume : Tendsto
      (fun index => finiteOpenIntervalVolume duration (Set.Ioc (start index) duration))
      atTop (nhds 0) := by
    have hOfReal := ENNReal.tendsto_ofReal hWidthTendsto
    simpa only [ENNReal.ofReal_zero] using hOfReal.congr'
      (Filter.Eventually.of_forall fun index => by
        calc
          ENNReal.ofReal (width index) =
              ENNReal.ofReal (duration - start index) := by
            congr 1
            dsimp only [start]
            ring
          _ = finiteOpenIntervalVolume duration (Set.Ioc (start index) duration) :=
            (finiteOpenIntervalVolume_Ioc_duration (hStart index)).symm)
  obtain ⟨startIndex, hVariation⟩ :=
    exists_eventIndex_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
      generator hDuration paths (fun index => Set.Ioc (start index) duration)
        (fun _ => measurableSet_Ioc) hEventVolume hPaths hLevel hRates hEpsilon
  exact ⟨start startIndex, hStart startIndex, hVariation⟩

/-- On the exact finite-rate representation domain, strong-`L1` convergence forces convergence
of the separately recovered terminal traces. -/
theorem
    rengerDirectionalFlowHybridBVTendstoTerminalTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration)
    {level : ENNReal} (hLevel : level ≠ ∞)
    (hRates : ∀ sequenceIndex,
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (paths sequenceIndex) ≤ level)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limitPath.toDerivativePath.toL1Path)) :
    Tendsto (fun sequenceIndex => (paths sequenceIndex).terminalTrace hDuration)
      atTop (nhds (limitPath.terminalTrace hDuration)) := by
  apply tendsto_terminalTrace_of_tendsto_toL1Path_of_uniformTerminalDerivativeVariation
    hDuration paths limitPath hTendsto
  intro epsilon hEpsilon
  obtain ⟨start, hStart, hVariation⟩ :=
    exists_terminalStart_rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_le_of_uniformRate
      generator hDuration paths hPaths hLevel hRates hEpsilon
  refine ⟨start, hStart, fun sequenceIndex => ?_⟩
  rw [← rengerDirectionalFlowHybridBVTotalDerivativeVariationOn_eq_generic]
  exact hVariation sequenceIndex

end

end FiniteMarkovProcesses.InformationTheory
