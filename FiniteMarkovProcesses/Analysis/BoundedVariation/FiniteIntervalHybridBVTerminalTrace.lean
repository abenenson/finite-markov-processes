/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVInitialTrace

/-!
# Terminal traces for hybrid bounded-variation paths

This module supplies the right-endpoint counterpart of hybrid-BV initial-trace closure.  The
terminal trace is a separately recovered left limit, not evaluation of the open-interval `L1`
quotient.  Strong `L1` convergence recovers it only when derivative variation is uniformly unable
to escape through shrinking terminal neighborhoods.

No global continuity of `FiniteIntervalHybridBVPath.terminalTrace` is asserted.

## Main results

* `edist_cadlagRepresentative_terminalTrace_le_derivativeTotalVariation_Ioc` controls displacement
  from a physical time to the terminal trace by the remaining derivative variation.
* In `FiniteIntervalHybridBVPath`,
  `tendsto_terminalTrace_of_tendsto_toL1Path_of_uniformTerminalDerivativeVariation` recovers
  terminal-trace convergence under the exact endpoint no-escape premise.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- The physical-time volume of a terminal half-open neighborhood is its positive width. -/
theorem finiteOpenIntervalVolume_Ico_duration
    {start : ℝ} (hStart : start ∈ Set.Ioo 0 duration) :
    finiteOpenIntervalVolume duration (Set.Ico start duration) =
      ENNReal.ofReal (duration - start) := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply measurableSet_Ico]
  have hSubset : Set.Ico start duration ⊆ Set.Ioo 0 duration := by
    intro time hTime
    exact ⟨hStart.1.trans_le hTime.1, hTime.2⟩
  rw [inter_eq_left.mpr hSubset, Real.volume_Ico]

/-- Including the terminal singleton does not change physical-time volume because the carrier
itself remains open at the right endpoint. -/
theorem finiteOpenIntervalVolume_Ioc_duration
    {start : ℝ} (hStart : start ∈ Set.Ioo 0 duration) :
    finiteOpenIntervalVolume duration (Set.Ioc start duration) =
      ENNReal.ofReal (duration - start) := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply measurableSet_Ioc]
  have hIntersection : Set.Ioc start duration ∩ Set.Ioo 0 duration =
      Set.Ioo start duration := by
    ext time
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · intro hTime
      exact ⟨hTime.1.1, hTime.2.2⟩
    · intro hTime
      exact ⟨⟨hTime.1, hTime.2.le⟩, hStart.1.trans hTime.1, hTime.2⟩
  rw [hIntersection, Real.volume_Ioo]

/-- The derivative variation remaining after a physical time controls displacement to the
separately recovered terminal left trace. -/
theorem edist_cadlagRepresentative_terminalTrace_le_derivativeTotalVariation_Ioc
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) {time : ℝ} (hTime : time ∈ Set.Ico 0 duration) :
    edist (path.cadlagRepresentative.representative time)
        (path.terminalTrace hDuration) ≤
      finiteIntervalHybridBVDerivativeTotalVariationOn path (Set.Ioc time duration) := by
  have hEdistTendsto : Tendsto
      (fun finish => edist (path.cadlagRepresentative.representative time)
        (path.cadlagRepresentative.representative finish))
      (nhdsWithin duration (Set.Iio duration))
      (nhds (edist (path.cadlagRepresentative.representative time)
        (path.terminalTrace hDuration))) :=
    Filter.Tendsto.edist tendsto_const_nhds (path.tendsto_terminalTrace hDuration)
  apply le_of_tendsto hEdistTendsto
  filter_upwards [Ioo_mem_nhdsLT hTime.2] with finish hFinish
  refine (show edist (path.cadlagRepresentative.representative time)
      (path.cadlagRepresentative.representative finish) ≤
        ∑ coordinate,
          (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
            (Set.Ioc time finish) by
      rw [edist_comm]
      exact edist_cadlagRepresentative_le_derivativeTotalVariation_Ioc
        path hTime.1 hFinish.1.le hFinish.2).trans ?_
  exact finiteIntervalHybridBVDerivativeTotalVariationOn_mono path
    (Set.Ioc_subset_Ioc_right hFinish.2.le)

/-- Two hybrid paths have a common terminal-neighborhood time where representative distance is no
larger than strong-`L1` distance divided by the neighborhood width. -/
theorem exists_terminalTime_edist_cadlagRepresentatives_le_toL1Path_edist_div
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    {start : ℝ} (hStart : start ∈ Set.Ioo 0 duration) :
    ∃ time ∈ Set.Ico start duration,
      edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) ≤
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal (duration - start) := by
  let physicalVolume := finiteOpenIntervalVolume duration
  let event := Set.Ico start duration
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
  have hEventVolume : physicalVolume event = ENNReal.ofReal (duration - start) :=
    finiteOpenIntervalVolume_Ico_duration hStart
  have hEventVolumePositive : 0 < physicalVolume event := by
    rw [hEventVolume]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hStart.2)
  have hRestrictedMeasureNonzero : physicalVolume.restrict event ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hEventVolumePositive.ne'
  have hErrorMeasurable : AEMeasurable error (physicalVolume.restrict event) :=
    (hFirst.aestronglyMeasurable.edist hSecond.aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hComplementNull : physicalVolume.restrict event eventᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ico.compl, Set.compl_inter_self,
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
          ENNReal.ofReal (duration - start) := by
      rw [laverage_eq, Measure.restrict_apply_univ, hEventVolume]
    _ ≤ (∫⁻ point, error point ∂physicalVolume) /
        ENNReal.ofReal (duration - start) := by
      exact ENNReal.div_le_div_right
        (lintegral_mono' Measure.restrict_le_self (le_refl _)) _
    _ = edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
        ENNReal.ofReal (duration - start) := by
      rw [hGlobalIntegral]

/-- Terminal traces are close when the first path has little remaining derivative variation, the
paths are close in strong `L1`, and the second representative is uniformly close to its terminal
trace on the same neighborhood. -/
theorem edist_terminalTrace_le_derivativeVariationOn_add_toL1Path_edist_div_add
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) {endpointError : ENNReal} {start : ℝ}
    (hStart : start ∈ Set.Ioo 0 duration)
    (hSecondEndpoint : ∀ time ∈ Set.Ico start duration,
      edist (second.cadlagRepresentative.representative time)
        (second.terminalTrace hDuration) ≤ endpointError) :
    edist (first.terminalTrace hDuration) (second.terminalTrace hDuration) ≤
      finiteIntervalHybridBVDerivativeTotalVariationOn first (Set.Ioc start duration) +
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal (duration - start) + endpointError := by
  obtain ⟨time, hTime, hComparison⟩ :=
    exists_terminalTime_edist_cadlagRepresentatives_le_toL1Path_edist_div
      first second hStart
  have hFirstVariation :
      edist (first.terminalTrace hDuration)
          (first.cadlagRepresentative.representative time) ≤
        finiteIntervalHybridBVDerivativeTotalVariationOn first
          (Set.Ioc start duration) := by
    rw [edist_comm]
    exact (edist_cadlagRepresentative_terminalTrace_le_derivativeTotalVariation_Ioc
      first hDuration ⟨hStart.1.le.trans hTime.1, hTime.2⟩).trans
        (finiteIntervalHybridBVDerivativeTotalVariationOn_mono first
          (Set.Ioc_subset_Ioc_left hTime.1))
  calc
    edist (first.terminalTrace hDuration) (second.terminalTrace hDuration) ≤
        edist (first.terminalTrace hDuration)
            (first.cadlagRepresentative.representative time) +
          edist (first.cadlagRepresentative.representative time)
            (second.terminalTrace hDuration) := edist_triangle _ _ _
    _ ≤ edist (first.terminalTrace hDuration)
          (first.cadlagRepresentative.representative time) +
        (edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) +
        edist (second.cadlagRepresentative.representative time)
          (second.terminalTrace hDuration)) :=
      add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist (first.terminalTrace hDuration)
          (first.cadlagRepresentative.representative time) +
        edist (first.cadlagRepresentative.representative time)
          (second.cadlagRepresentative.representative time) +
        edist (second.cadlagRepresentative.representative time)
          (second.terminalTrace hDuration) := by rw [add_assoc]
    _ ≤ finiteIntervalHybridBVDerivativeTotalVariationOn first
          (Set.Ioc start duration) +
        edist first.toDerivativePath.toL1Path second.toDerivativePath.toL1Path /
          ENNReal.ofReal (duration - start) + endpointError :=
      add_le_add (add_le_add hFirstVariation hComparison)
        (hSecondEndpoint time hTime)

namespace FiniteIntervalHybridBVPath

/-- Strong-`L1` convergence recovers the terminal trace when the approximating sequence has
uniformly vanishing derivative variation on some sufficiently small terminal neighborhood. -/
theorem tendsto_terminalTrace_of_tendsto_toL1Path_of_uniformTerminalDerivativeVariation
    (hDuration : 0 < duration)
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limitPath : FiniteIntervalHybridBVPath Coordinate duration)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limitPath.toDerivativePath.toL1Path))
    (hVariation : ∀ epsilon : ENNReal, 0 < epsilon →
      ∃ start ∈ Set.Ioo 0 duration, ∀ sequenceIndex,
        finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
          (Set.Ioc start duration) ≤ epsilon) :
    Tendsto (fun sequenceIndex => (paths sequenceIndex).terminalTrace hDuration)
      atTop (nhds (limitPath.terminalTrace hDuration)) := by
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
  obtain ⟨variationStart, hVariationStart, hUniformVariation⟩ :=
    hVariation (epsilon / 4) hQuarterEpsilon
  have hLimitEventually : ∀ᶠ time in nhdsWithin duration (Set.Iio duration),
      edist (limitPath.cadlagRepresentative.representative time)
        (limitPath.terminalTrace hDuration) < epsilon / 4 :=
    EMetric.tendsto_nhds.mp (limitPath.tendsto_terminalTrace hDuration)
      (epsilon / 4) hQuarterEpsilon
  obtain ⟨continuityStart, hContinuityStart, hContinuity⟩ :=
    mem_nhdsLT_iff_exists_Ico_subset.mp hLimitEventually
  have hContinuityStartLtDuration : continuityStart < duration := hContinuityStart
  let midpoint := (continuityStart + duration) / 2
  have hContinuityStartLtMidpoint : continuityStart < midpoint := by
    dsimp only [midpoint]
    linarith [hContinuityStartLtDuration]
  have hMidpointLtDuration : midpoint < duration := by
    dsimp only [midpoint]
    linarith [hContinuityStartLtDuration]
  let start := max variationStart midpoint
  have hVariationStartLe : variationStart ≤ start := le_max_left _ _
  have hMidpointLe : midpoint ≤ start := le_max_right _ _
  have hContinuityStartLt : continuityStart < start :=
    hContinuityStartLtMidpoint.trans_le hMidpointLe
  have hStart : start ∈ Set.Ioo 0 duration := by
    refine ⟨hVariationStart.1.trans_le hVariationStartLe, ?_⟩
    exact max_lt hVariationStart.2 hMidpointLtDuration
  have hLimitEndpoint (time : ℝ) (hTime : time ∈ Set.Ico start duration) :
      edist (limitPath.cadlagRepresentative.representative time)
        (limitPath.terminalTrace hDuration) ≤ epsilon / 4 := by
    exact (hContinuity ⟨(hContinuityStartLt.trans_le hTime.1).le, hTime.2⟩).le
  have hL1Edist : Tendsto
      (fun sequenceIndex => edist
        (paths sequenceIndex).toDerivativePath.toL1Path
        limitPath.toDerivativePath.toL1Path) atTop (nhds 0) :=
    tendsto_iff_edist_tendsto_0.mp hTendsto
  have hWidthPositive : 0 < duration - start := sub_pos.mpr hStart.2
  have hL1Div : Tendsto
      (fun sequenceIndex => edist
        (paths sequenceIndex).toDerivativePath.toL1Path
        limitPath.toDerivativePath.toL1Path / ENNReal.ofReal (duration - start))
      atTop (nhds 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hL1Edist
      (Or.inr (ENNReal.ofReal_ne_zero_iff.mpr hWidthPositive))
  obtain ⟨minimumIndex, hL1Eventually⟩ :=
    eventually_atTop.mp
      (ENNReal.tendsto_nhds_zero.mp hL1Div (epsilon / 4) hQuarterEpsilon)
  refine ⟨minimumIndex, fun sequenceIndex hSequenceIndex => ?_⟩
  have hLocalVariation :
      finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
          (Set.Ioc start duration) ≤ epsilon / 4 :=
    (finiteIntervalHybridBVDerivativeTotalVariationOn_mono
      (paths sequenceIndex) (Set.Ioc_subset_Ioc_left hVariationStartLe)).trans
        (hUniformVariation sequenceIndex)
  have hL1Bound :
      edist (paths sequenceIndex).toDerivativePath.toL1Path
          limitPath.toDerivativePath.toL1Path /
        ENNReal.ofReal (duration - start) ≤ epsilon / 4 :=
    hL1Eventually sequenceIndex hSequenceIndex
  calc
    edist ((paths sequenceIndex).terminalTrace hDuration)
        (limitPath.terminalTrace hDuration) ≤
      finiteIntervalHybridBVDerivativeTotalVariationOn (paths sequenceIndex)
          (Set.Ioc start duration) +
        edist (paths sequenceIndex).toDerivativePath.toL1Path
            limitPath.toDerivativePath.toL1Path / ENNReal.ofReal (duration - start) +
        epsilon / 4 :=
      edist_terminalTrace_le_derivativeVariationOn_add_toL1Path_edist_div_add
        (paths sequenceIndex) limitPath hDuration hStart hLimitEndpoint
    _ ≤ epsilon / 4 + epsilon / 4 + epsilon / 4 :=
      add_le_add (add_le_add hLocalVariation hL1Bound) le_rfl
    _ = 3 * (epsilon / 4) := by ring
    _ < 4 * (epsilon / 4) :=
      ENNReal.mul_lt_mul_left hQuarterEpsilon.ne' hQuarterEpsilonFinite (by norm_num)
    _ = epsilon := ENNReal.mul_div_cancel (by norm_num) (by simp)

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses
