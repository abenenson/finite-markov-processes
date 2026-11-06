/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope

/-!
# Initial traces for hybrid bounded-variation paths

This module isolates the source-neutral endpoint mechanism used by finite-rate hybrid path
families.  Strong `L1` convergence alone does not control the recovered initial trace.  It does
so when derivative variation is uniformly unable to escape through shrinking initial-time
neighborhoods.

No global continuity of `FiniteIntervalHybridBVPath.initialTrace` is asserted.

## Main results

* `finiteOpenIntervalVolume_Ioc_zero` computes the physical volume of an initial neighborhood.
* `exists_initialTime_edist_cadlagRepresentatives_le_toL1Path_edist_div` gives the localized
  first-moment comparison needed to recover an initial trace from strong-`L1` convergence and
  endpoint variation control.
* `edist_initialTrace_le_derivativeVariationOn_add_toL1Path_edist_div_add` bounds initial-trace
  separation by local derivative variation, strong-`L1` separation, and one comparison-path
  endpoint modulus.
* In `FiniteIntervalHybridBVPath`,
  `tendsto_initialTrace_of_tendsto_toL1Path_of_uniformInitialDerivativeVariation` recovers trace
  convergence without asserting global trace continuity.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Complete coordinatewise derivative variation carried by one time event. -/
noncomputable def finiteIntervalHybridBVDerivativeTotalVariationOn
    (path : FiniteIntervalHybridBVPath Coordinate duration) (event : Set ℝ) : ENNReal :=
  ∑ coordinate,
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation event

/-- Complete event-local derivative variation is monotone in the observed time event. -/
theorem finiteIntervalHybridBVDerivativeTotalVariationOn_mono
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    {firstEvent secondEvent : Set ℝ} (hEvent : firstEvent ⊆ secondEvent) :
    finiteIntervalHybridBVDerivativeTotalVariationOn path firstEvent ≤
      finiteIntervalHybridBVDerivativeTotalVariationOn path secondEvent := by
  apply Finset.sum_le_sum
  intro coordinate _hCoordinate
  exact measure_mono hEvent

/-- Event-local variation recovers the existing complete variation on the whole time line. -/
theorem finiteIntervalHybridBVDerivativeTotalVariationOn_univ
    (path : FiniteIntervalHybridBVPath Coordinate duration) :
    finiteIntervalHybridBVDerivativeTotalVariationOn path Set.univ =
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  rfl

/-- The physical-time volume of an initial half-open neighborhood is its positive width. -/
theorem finiteOpenIntervalVolume_Ioc_zero
    {endpoint : ℝ} (hEndpoint : endpoint ∈ Set.Ioo 0 duration) :
    finiteOpenIntervalVolume duration (Set.Ioc 0 endpoint) = ENNReal.ofReal endpoint := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply measurableSet_Ioc]
  have hSubset : Set.Ioc 0 endpoint ⊆ Set.Ioo 0 duration := by
    intro time hTime
    exact ⟨hTime.1, hTime.2.trans_lt hEndpoint.2⟩
  rw [inter_eq_left.mpr hSubset, Real.volume_Ioc]
  simp

/-- Two hybrid paths have a common initial-neighborhood time where their selected representative
distance is no larger than their strong-`L1` distance divided by the neighborhood width. -/
theorem exists_initialTime_edist_cadlagRepresentatives_le_toL1Path_edist_div
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    {endpoint : ℝ} (hEndpoint : endpoint ∈ Set.Ioo 0 duration) :
    ∃ time ∈ Set.Ioc 0 endpoint,
      edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) ≤
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal endpoint := by
  let physicalVolume := finiteOpenIntervalVolume duration
  let event := Set.Ioc 0 endpoint
  let firstRepresentative := first.cadlagRepresentative.representative
  let secondRepresentative := second.cadlagRepresentative.representative
  let error := fun time => edist (firstRepresentative time) (secondRepresentative time)
  let hFirst : MemLp firstRepresentative 1 physicalVolume :=
    Classical.choose first.cadlagRepresentative.represents
  let hSecond : MemLp secondRepresentative 1 physicalVolume :=
    Classical.choose second.cadlagRepresentative.represents
  have hFirstRepresents : hFirst.toLp firstRepresentative = first.toDerivativePath.toL1Path :=
    Classical.choose_spec first.cadlagRepresentative.represents
  have hSecondRepresents : hSecond.toLp secondRepresentative =
      second.toDerivativePath.toL1Path :=
    Classical.choose_spec second.cadlagRepresentative.represents
  have hEventVolume : physicalVolume event = ENNReal.ofReal endpoint :=
    finiteOpenIntervalVolume_Ioc_zero hEndpoint
  have hEventVolumePositive : 0 < physicalVolume event := by
    rw [hEventVolume]
    exact ENNReal.ofReal_pos.mpr hEndpoint.1
  have hRestrictedMeasureNonzero : physicalVolume.restrict event ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hEventVolumePositive.ne'
  have hErrorMeasurable : AEMeasurable error (physicalVolume.restrict event) :=
    (hFirst.aestronglyMeasurable.edist hSecond.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hComplementNull : physicalVolume.restrict event eventᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioc.compl, Set.compl_inter_self,
      measure_empty]
  obtain ⟨time, hTime, hTimeAverage⟩ :=
    exists_notMem_null_le_laverage hRestrictedMeasureNonzero
      hErrorMeasurable hComplementNull
  have hGlobalIntegral :
      (∫⁻ point, error point ∂physicalVolume) =
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path := by
    rw [← hFirstRepresents, ← hSecondRepresents, Lp.edist_toLp_toLp,
      eLpNorm_one_eq_lintegral_enorm
        (hFirst.aestronglyMeasurable.sub hSecond.aestronglyMeasurable)]
    simp only [Pi.sub_apply, error, edist_eq_enorm_sub]
  refine ⟨time, Set.notMem_compl_iff.mp hTime, hTimeAverage.trans ?_⟩
  calc
    (⨍⁻ point, error point ∂physicalVolume.restrict event) =
        (∫⁻ point, error point ∂physicalVolume.restrict event) /
          ENNReal.ofReal endpoint := by
      rw [laverage_eq, Measure.restrict_apply_univ, hEventVolume]
    _ ≤ (∫⁻ point, error point ∂physicalVolume) /
        ENNReal.ofReal endpoint := by
      exact ENNReal.div_le_div_right
        (lintegral_mono' Measure.restrict_le_self (le_refl _)) _
    _ = edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
        ENNReal.ofReal endpoint := by
      rw [hGlobalIntegral]

/-- Initial traces are close when the first path has little derivative variation near zero, the
two paths are close in strong `L1`, and the second representative is uniformly close to its own
initial trace on the same neighborhood. -/
theorem edist_initialTrace_le_derivativeVariationOn_add_toL1Path_edist_div_add
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    {endpointError : ENNReal} {realEndpoint : ℝ}
    (hEndpoint : realEndpoint ∈ Set.Ioo 0 duration)
    (hSecondEndpoint : ∀ time ∈ Set.Ioc 0 realEndpoint,
      edist (second.cadlagRepresentative.representative time) second.initialTrace ≤
        endpointError) :
    edist first.initialTrace second.initialTrace ≤
      finiteIntervalHybridBVDerivativeTotalVariationOn first (Set.Ioc 0 realEndpoint) +
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal realEndpoint + endpointError := by
  obtain ⟨time, hTime, hComparison⟩ :=
    exists_initialTime_edist_cadlagRepresentatives_le_toL1Path_edist_div
      first second hEndpoint
  have hTimePhysical : time < duration := hTime.2.trans_lt hEndpoint.2
  have hFirstVariation :
      edist first.initialTrace (first.cadlagRepresentative.representative time) ≤
        finiteIntervalHybridBVDerivativeTotalVariationOn first
          (Set.Ioc 0 realEndpoint) := by
    rw [edist_comm]
    refine (edist_cadlagRepresentative_le_derivativeTotalVariation_Ioc
      first le_rfl hTime.1.le hTimePhysical).trans ?_
    apply Finset.sum_le_sum
    intro coordinate _hCoordinate
    exact measure_mono (Set.Ioc_subset_Ioc_right hTime.2)
  calc
    edist first.initialTrace second.initialTrace ≤
        edist first.initialTrace (first.cadlagRepresentative.representative time) +
          edist (first.cadlagRepresentative.representative time) second.initialTrace :=
      edist_triangle _ _ _
    _ ≤ edist first.initialTrace (first.cadlagRepresentative.representative time) +
        (edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) +
        edist (second.cadlagRepresentative.representative time) second.initialTrace) :=
      add_le_add le_rfl
        (edist_triangle (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) second.initialTrace)
    _ = edist first.initialTrace (first.cadlagRepresentative.representative time) +
        edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) +
        edist (second.cadlagRepresentative.representative time) second.initialTrace := by
      rw [add_assoc]
    _ ≤ finiteIntervalHybridBVDerivativeTotalVariationOn first
          (Set.Ioc 0 realEndpoint) +
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal realEndpoint + endpointError :=
      add_le_add (add_le_add hFirstVariation hComparison)
        (hSecondEndpoint time hTime)

namespace FiniteIntervalHybridBVPath

/-- Strong-`L1` convergence recovers the initial trace when the approximating sequence has
uniformly vanishing derivative variation on some sufficiently small initial neighborhood.  The
limit path needs no rate or admissibility hypothesis: its own right continuity supplies the
remaining endpoint modulus. -/
theorem tendsto_initialTrace_of_tendsto_toL1Path_of_uniformInitialDerivativeVariation
    (hDuration : 0 < duration)
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limitPath : FiniteIntervalHybridBVPath Coordinate duration)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limitPath.toDerivativePath.toL1Path))
    (hVariation : ∀ epsilon : ENNReal, 0 < epsilon →
      ∃ endpoint ∈ Set.Ioo 0 duration, ∀ sequenceIndex,
        finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
          (Set.Ioc 0 endpoint) ≤ epsilon) :
    Tendsto (fun sequenceIndex => (paths sequenceIndex).initialTrace)
      atTop (nhds limitPath.initialTrace) := by
  apply EMetric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  by_cases hEpsilonTop : epsilon = ∞
  · refine ⟨0, fun sequenceIndex _hSequenceIndex => ?_⟩
    rw [hEpsilonTop]
    exact edist_lt_top _ _
  have hQuarterEpsilon : 0 < epsilon / 4 :=
    ENNReal.div_pos_iff.mpr ⟨hEpsilon.ne', by simp⟩
  have hQuarterEpsilonFinite : epsilon / 4 ≠ ∞ :=
    ENNReal.div_ne_top hEpsilonTop (by norm_num)
  obtain ⟨variationEndpoint, hVariationEndpoint, hUniformVariation⟩ :=
    hVariation (epsilon / 4) hQuarterEpsilon
  have hLimitEventually : ∀ᶠ time in nhdsWithin 0 (Set.Ici 0),
      edist (limitPath.cadlagRepresentative.representative time)
        limitPath.initialTrace < epsilon / 4 :=
    EMetric.tendsto_nhds.mp (limitPath.tendsto_initialTrace hDuration)
      (epsilon / 4) hQuarterEpsilon
  obtain ⟨continuityEndpoint, hContinuityEndpoint, hContinuity⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp hLimitEventually
  let endpoint := min variationEndpoint (continuityEndpoint / 2)
  have hHalfContinuityEndpoint : 0 < continuityEndpoint / 2 := by positivity
  have hHalfContinuityEndpointLt : continuityEndpoint / 2 < continuityEndpoint := by
    linarith
  have hEndpointPositive : 0 < endpoint := by
    exact lt_min hVariationEndpoint.1 hHalfContinuityEndpoint
  have hEndpointLeVariation : endpoint ≤ variationEndpoint := min_le_left _ _
  have hEndpointLtContinuity : endpoint < continuityEndpoint :=
    (min_le_right _ _).trans_lt hHalfContinuityEndpointLt
  have hEndpoint : endpoint ∈ Set.Ioo 0 duration :=
    ⟨hEndpointPositive,
      hEndpointLeVariation.trans_lt hVariationEndpoint.2⟩
  have hLimitEndpoint (time : ℝ) (hTime : time ∈ Set.Ioc 0 endpoint) :
      edist (limitPath.cadlagRepresentative.representative time)
        limitPath.initialTrace ≤ epsilon / 4 := by
    exact (hContinuity ⟨hTime.1.le,
      (hTime.2.trans_lt hEndpointLtContinuity).le⟩).le
  have hL1Edist : Tendsto
      (fun sequenceIndex => edist
        (paths sequenceIndex).toDerivativePath.toL1Path
        limitPath.toDerivativePath.toL1Path) atTop (nhds 0) :=
    tendsto_iff_edist_tendsto_0.mp hTendsto
  have hL1Div : Tendsto
      (fun sequenceIndex => edist
        (paths sequenceIndex).toDerivativePath.toL1Path
        limitPath.toDerivativePath.toL1Path / ENNReal.ofReal endpoint)
      atTop (nhds 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hL1Edist
      (Or.inr (ENNReal.ofReal_ne_zero_iff.mpr hEndpointPositive))
  obtain ⟨minimumIndex, hL1Eventually⟩ :=
    eventually_atTop.mp
      (ENNReal.tendsto_nhds_zero.mp hL1Div (epsilon / 4) hQuarterEpsilon)
  refine ⟨minimumIndex, fun sequenceIndex hSequenceIndex => ?_⟩
  have hLocalVariation :
      finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
          (Set.Ioc 0 endpoint) ≤ epsilon / 4 :=
    (finiteIntervalHybridBVDerivativeTotalVariationOn_mono
      (paths sequenceIndex) (Set.Ioc_subset_Ioc_right hEndpointLeVariation)).trans
        (hUniformVariation sequenceIndex)
  have hL1Bound :
      edist (paths sequenceIndex).toDerivativePath.toL1Path
          limitPath.toDerivativePath.toL1Path / ENNReal.ofReal endpoint ≤ epsilon / 4 :=
    hL1Eventually sequenceIndex hSequenceIndex
  calc
    edist (paths sequenceIndex).initialTrace limitPath.initialTrace ≤
        finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
            (Set.Ioc 0 endpoint) +
          edist (paths sequenceIndex).toDerivativePath.toL1Path
              limitPath.toDerivativePath.toL1Path / ENNReal.ofReal endpoint +
          epsilon / 4 :=
      edist_initialTrace_le_derivativeVariationOn_add_toL1Path_edist_div_add
        (paths sequenceIndex) limitPath hEndpoint hLimitEndpoint
    _ ≤ epsilon / 4 + epsilon / 4 + epsilon / 4 :=
      add_le_add (add_le_add hLocalVariation hL1Bound) le_rfl
    _ = 3 * (epsilon / 4) := by ring
    _ < 4 * (epsilon / 4) :=
      ENNReal.mul_lt_mul_left hQuarterEpsilon.ne' hQuarterEpsilonFinite (by norm_num)
    _ = epsilon := ENNReal.mul_div_cancel (by norm_num) (by simp)

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses
