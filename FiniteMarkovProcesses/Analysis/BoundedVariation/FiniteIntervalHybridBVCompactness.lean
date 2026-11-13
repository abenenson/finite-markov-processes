/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalSampleStepL1Path
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Compactness of finite-interval hybrid bounded-variation envelopes

This module gives the constructive finite-mesh approximation used in the HPR compactness route.
It deliberately starts from the broad quantitative envelope: neither absolute continuity, a
continuity equation, nor boundary traces enter the approximation.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- A metric family is totally bounded when every positive tolerance admits a compact family of
uniform approximants. -/
theorem totallyBounded_of_forall_exists_compact_approx
    {MetricCarrier : Type*} [PseudoMetricSpace MetricCarrier]
    (family : Set MetricCarrier)
    (hApproximation : ∀ ε : ℝ, 0 < ε →
      ∃ compactFamily : Set MetricCarrier,
        IsCompact compactFamily ∧
          ∀ point ∈ family, ∃ approximation ∈ compactFamily,
            dist point approximation < ε) :
    TotallyBounded family := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hHalfEpsilon : 0 < ε / 2 := by linarith
  obtain ⟨compactFamily, hCompactFamily, hApproximationHalf⟩ :=
    hApproximation (ε / 2) hHalfEpsilon
  obtain ⟨net, _hNetSubset, hNetFinite, hNetCover⟩ :=
    Metric.finite_approx_of_totallyBounded hCompactFamily.totallyBounded
      (ε / 2) hHalfEpsilon
  refine ⟨net, hNetFinite, ?_⟩
  intro point hPoint
  obtain ⟨approximation, hApproximationMember, hPointApproximation⟩ :=
    hApproximationHalf point hPoint
  have hApproximationCover := hNetCover hApproximationMember
  rcases Set.mem_iUnion.mp hApproximationCover with ⟨center, hCenterCover⟩
  rcases Set.mem_iUnion.mp hCenterCover with ⟨hCenterNet, hApproximationCenter⟩
  apply Set.mem_iUnion.mpr
  refine ⟨center, Set.mem_iUnion.mpr ⟨hCenterNet, ?_⟩⟩
  have hPointCenter : dist point center < ε := by
    calc
      dist point center ≤ dist point approximation + dist approximation center :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hPointApproximation hApproximationCenter
      _ = ε := add_halves ε
  exact hPointCenter

/-- Total derivative variation assigned to one uniform mesh cell. -/
noncomputable def finiteIntervalHybridBVDerivativeVariationOnUniformCell
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (finalSampleIndex : ℕ) (sampleIndex : Fin (finalSampleIndex + 1)) : ENNReal :=
  ∑ coordinate,
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
      (Set.Ioc
        (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)
        ((sampleIndex.val + 1) * (duration / (finalSampleIndex + 1))))

/-- The variation budgets of all uniform cells sum to at most the complete derivative variation. -/
theorem sum_derivativeVariationOnUniformCell_le
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) (finalSampleIndex : ℕ) :
    ∑ sampleIndex,
        finiteIntervalHybridBVDerivativeVariationOnUniformCell
          path finalSampleIndex sampleIndex ≤
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  classical
  rw [finiteIntervalHybridBVDerivativeTotalVariation]
  simp only [finiteIntervalHybridBVDerivativeVariationOnUniformCell]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro coordinate _hCoordinate
  apply sum_measure_le_measure_univ
  · intro sampleIndex _hSampleIndex
    exact measurableSet_Ioc.nullMeasurableSet
  · intro first _hFirst second _hSecond hDifferent
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.2
    intro time hTimeFirst hTimeSecond
    have hCellWidthNonnegative :
        0 ≤ duration / (finalSampleIndex + 1 : ℝ) := by positivity
    rcases lt_or_gt_of_ne hDifferent with hFirstSecond | hSecondFirst
    · have hSuccessorLe : first.val + 1 ≤ second.val := by omega
      have hUpperLeLower :
          (first.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)) ≤
            second.val * (duration / (finalSampleIndex + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hSuccessorLe)
          hCellWidthNonnegative
      exact (not_lt_of_ge (hTimeFirst.2.trans hUpperLeLower)) hTimeSecond.1
    · have hSuccessorLe : second.val + 1 ≤ first.val := by omega
      have hUpperLeLower :
          (second.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)) ≤
            first.val * (duration / (finalSampleIndex + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hSuccessorLe)
          hCellWidthNonnegative
      exact (not_lt_of_ge (hTimeSecond.2.trans hUpperLeLower)) hTimeFirst.1

/-- Inside one mesh cell, displacement from its left sample is controlled by the derivative
variation assigned to that cell. -/
theorem edist_cadlagRepresentative_uniformSample_le_cellVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) {time : ℝ}
    (hTime : time ∈
      finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) :
    edist (path.cadlagRepresentative.representative time)
        (path.cadlagRepresentative.representative
          (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)) ≤
      finiteIntervalHybridBVDerivativeVariationOnUniformCell
        path finalSampleIndex sampleIndex := by
  classical
  let start := finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex
  let finish := (sampleIndex.val + 1) * (duration / (finalSampleIndex + 1 : ℝ))
  have hStartNonnegative : 0 ≤ start := by
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hTimePhysical : time < duration :=
    (finiteIntervalUniformSampleCell_subset_Ico hDuration finalSampleIndex
      sampleIndex hTime).2
  refine (edist_cadlagRepresentative_le_derivativeTotalVariation_Ioc
    path hStartNonnegative hTime.1 hTimePhysical).trans ?_
  apply Finset.sum_le_sum
  intro coordinate _hCoordinate
  exact measure_mono (Set.Ioc_subset_Ioc_right hTime.2.le)

/-- Values of the canonical càdlàg representative at the left endpoints of a uniform mesh. -/
noncomputable def finiteIntervalHybridBVUniformSampleValue
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (finalSampleIndex : ℕ) :
    Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate :=
  fun sampleIndex => path.cadlagRepresentative.representative
    (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)

/-- The strong-`L1` uniform-mesh step approximation of a hybrid BV path. -/
noncomputable def finiteIntervalHybridBVUniformSampleStepL1Path
    [DecidableEq Coordinate]
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (finalSampleIndex : ℕ) : FiniteIntervalL1Path Coordinate duration :=
  finiteIntervalSampleStepL1Path duration finalSampleIndex
    (finiteIntervalUniformSampleTime duration finalSampleIndex)
    (finiteIntervalHybridBVUniformSampleValue path finalSampleIndex)

/-- On one mesh cell, the integrated approximation error is bounded by cell width times the
derivative variation assigned to that cell. -/
theorem setLIntegral_enorm_cadlagRepresentative_sub_uniformSample_le
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    ∫⁻ time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
        ‖path.cadlagRepresentative.representative time -
          finiteIntervalHybridBVUniformSampleValue path finalSampleIndex sampleIndex‖ₑ
        ∂finiteOpenIntervalVolume duration ≤
      ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
        finiteIntervalHybridBVDerivativeVariationOnUniformCell
          path finalSampleIndex sampleIndex := by
  calc
    (∫⁻ time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
        ‖path.cadlagRepresentative.representative time -
          finiteIntervalHybridBVUniformSampleValue path finalSampleIndex sampleIndex‖ₑ
        ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ _time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
          finiteIntervalHybridBVDerivativeVariationOnUniformCell
            path finalSampleIndex sampleIndex ∂finiteOpenIntervalVolume duration := by
      apply setLIntegral_mono' measurableSet_Ico
      intro time hTime
      let difference := path.cadlagRepresentative.representative time -
        finiteIntervalHybridBVUniformSampleValue path finalSampleIndex sampleIndex
      calc
        ‖difference‖ₑ = ENNReal.ofReal ‖difference‖ :=
          (ofReal_norm difference).symm
        _ = edist (path.cadlagRepresentative.representative time)
            (finiteIntervalHybridBVUniformSampleValue path finalSampleIndex sampleIndex) := by
          rw [edist_dist, dist_eq_norm]
        _ ≤ finiteIntervalHybridBVDerivativeVariationOnUniformCell
            path finalSampleIndex sampleIndex :=
          edist_cadlagRepresentative_uniformSample_le_cellVariation
            path hDuration finalSampleIndex sampleIndex hTime
    _ = finiteIntervalHybridBVDerivativeVariationOnUniformCell
          path finalSampleIndex sampleIndex *
        finiteOpenIntervalVolume duration
          (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) :=
      setLIntegral_const _ _
    _ = ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
        finiteIntervalHybridBVDerivativeVariationOnUniformCell
          path finalSampleIndex sampleIndex := by
      rw [finiteOpenIntervalVolume_uniformSampleCell hDuration]
      exact mul_comm _ _

/-- Uniform left-endpoint sampling approximates every hybrid BV path in strong `L1` at the exact
mesh-width times derivative-variation rate. -/
theorem edist_toL1Path_uniformSampleStepL1Path_le
    [DecidableEq Coordinate]
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) (finalSampleIndex : ℕ) :
    edist path.toDerivativePath.toL1Path
        (finiteIntervalHybridBVUniformSampleStepL1Path path finalSampleIndex) ≤
      ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
        finiteIntervalHybridBVDerivativeTotalVariation path := by
  let physicalVolume := finiteOpenIntervalVolume duration
  let stepPath := finiteIntervalHybridBVUniformSampleStepL1Path path finalSampleIndex
  let errorIntegrand : ℝ → ENNReal := fun time =>
    ‖(path.toDerivativePath.toL1Path : ℝ → FiniteCoordinateL1Value Coordinate) time -
      (stepPath : ℝ → FiniteCoordinateL1Value Coordinate) time‖ₑ
  have hPhysicalRestriction :
      physicalVolume.restrict (Set.Ico 0 duration) = physicalVolume := by
    apply Measure.restrict_eq_self_of_ae_mem
    have hPhysical : ∀ᵐ time ∂physicalVolume, time ∈ Set.Ioo 0 duration := by
      exact ae_restrict_mem measurableSet_Ioo
    exact hPhysical.mono fun _time hTime => ⟨hTime.1.le, hTime.2⟩
  have hCellsPairwise : Pairwise
      (Function.onFun Disjoint
        (finiteIntervalUniformSampleCell duration finalSampleIndex)) := by
    intro first second hDifferent
    exact pairwiseDisjoint_finiteIntervalUniformSampleCell hDuration finalSampleIndex
      (Set.mem_univ first) (Set.mem_univ second) hDifferent
  have hPathEventually :
      (path.toDerivativePath.toL1Path : ℝ → FiniteCoordinateL1Value Coordinate) =ᵐ[
        finiteOpenIntervalVolume duration] path.cadlagRepresentative.representative := by
    obtain ⟨hRepresentative, hQuotient⟩ := path.cadlagRepresentative.represents
    exact ((FiniteIntervalL1Path.represents_iff_eventuallyEq
      path.toDerivativePath.toL1Path path.cadlagRepresentative.representative
      hRepresentative).mp ⟨hRepresentative, hQuotient⟩).symm
  have hCellIntegral (sampleIndex : Fin (finalSampleIndex + 1)) :
      ∫⁻ time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
          errorIntegrand time ∂physicalVolume ≤
        ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
          finiteIntervalHybridBVDerivativeVariationOnUniformCell
            path finalSampleIndex sampleIndex := by
    have hStepEventually :=
      finiteIntervalUniformSampleStepL1Path_eventuallyEq_on_cell
        hDuration finalSampleIndex
          (finiteIntervalHybridBVUniformSampleValue path finalSampleIndex) sampleIndex
    have hErrorEventually :
        errorIntegrand =ᵐ[physicalVolume.restrict
          (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex)]
          fun time => ‖path.cadlagRepresentative.representative time -
            finiteIntervalHybridBVUniformSampleValue path finalSampleIndex sampleIndex‖ₑ := by
      have hPathRestricted := hPathEventually.restrict
        (s := finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex)
      filter_upwards [hPathRestricted, hStepEventually] with time hPathTime hStepTime
      unfold errorIntegrand stepPath finiteIntervalHybridBVUniformSampleStepL1Path
      rw [hPathTime, hStepTime]
    rw [lintegral_congr_ae hErrorEventually]
    exact setLIntegral_enorm_cadlagRepresentative_sub_uniformSample_le
      path hDuration finalSampleIndex sampleIndex
  rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable path.toDerivativePath.toL1Path).sub
      (Lp.aestronglyMeasurable stepPath))]
  change (∫⁻ time, errorIntegrand time ∂physicalVolume) ≤ _
  calc
    (∫⁻ time, errorIntegrand time ∂physicalVolume) =
        ∫⁻ time in Set.Ico 0 duration, errorIntegrand time ∂physicalVolume := by
      rw [hPhysicalRestriction]
    _ = ∫⁻ time in ⋃ sampleIndex : Fin (finalSampleIndex + 1),
          finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
          errorIntegrand time ∂physicalVolume := by
      rw [iUnion_finiteIntervalUniformSampleCell hDuration]
    _ = ∑' sampleIndex : Fin (finalSampleIndex + 1),
        ∫⁻ time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
          errorIntegrand time ∂physicalVolume :=
      lintegral_iUnion (fun _sampleIndex => measurableSet_Ico) hCellsPairwise errorIntegrand
    _ = ∑ sampleIndex : Fin (finalSampleIndex + 1),
        ∫⁻ time in finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex,
          errorIntegrand time ∂physicalVolume := tsum_fintype _
    _ ≤ ∑ sampleIndex : Fin (finalSampleIndex + 1),
        ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
          finiteIntervalHybridBVDerivativeVariationOnUniformCell
            path finalSampleIndex sampleIndex := by
      exact Finset.sum_le_sum fun sampleIndex _hSampleIndex => hCellIntegral sampleIndex
    _ = ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
        ∑ sampleIndex : Fin (finalSampleIndex + 1),
          finiteIntervalHybridBVDerivativeVariationOnUniformCell
            path finalSampleIndex sampleIndex := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
        finiteIntervalHybridBVDerivativeTotalVariation path :=
      mul_le_mul_right
        (sum_derivativeVariationOnUniformCell_le path hDuration finalSampleIndex) _

/-- A uniform mesh time lies in the left-closed physical interval. -/
theorem finiteIntervalUniformSampleTime_mem_Ico
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex ∈
      Set.Ico 0 duration := by
  have hCellWidth : 0 < duration / (finalSampleIndex + 1 : ℝ) := by positivity
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hCellWidth.le
  · calc
      sampleIndex.val * (duration / (finalSampleIndex + 1 : ℝ)) <
          (finalSampleIndex + 1) * (duration / (finalSampleIndex + 1 : ℝ)) := by
        exact mul_lt_mul_of_pos_right (by exact_mod_cast sampleIndex.isLt) hCellWidth
      _ = duration := by field_simp

/-- Every sample array drawn from the broad quantitative envelope belongs to one common finite-
dimensional closed ball. -/
theorem uniformSampleValue_mem_closedBall_of_mem_uniformL1VariationEnvelope
    (hDuration : 0 < duration) {l1Bound variationBound : ENNReal}
    (hL1Bound : l1Bound < ∞) (hVariationBound : variationBound < ∞)
    {path : FiniteIntervalHybridBVPath Coordinate duration}
    (hPath : path ∈
      finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound)
    (finalSampleIndex : ℕ) :
    finiteIntervalHybridBVUniformSampleValue path finalSampleIndex ∈
      Metric.closedBall
        (0 : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
        (l1Bound / ENNReal.ofReal duration + variationBound).toReal := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2
  intro sampleIndex
  rw [← toReal_enorm]
  apply ENNReal.toReal_mono
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top hL1Bound.ne (ENNReal.ofReal_pos.mpr hDuration).ne',
        hVariationBound.ne⟩
  · refine (enorm_cadlagRepresentative_le_l1Average_add_derivativeTotalVariation_of_mem_Ico
      path hDuration (finiteIntervalUniformSampleTime_mem_Ico
        hDuration finalSampleIndex sampleIndex)).trans ?_
    exact add_le_add
      (ENNReal.div_le_div_right hPath.1 _) hPath.2

/-- The strong-`L1` projections of the broad bounded-variation envelope form a totally bounded
family. -/
theorem totallyBounded_toL1Path_image_uniformL1VariationEnvelope
    [DecidableEq Coordinate]
    (hDuration : 0 < duration) {l1Bound variationBound : ENNReal}
    (hL1Bound : l1Bound < ∞) (hVariationBound : variationBound < ∞) :
    TotallyBounded
      ((fun path : FiniteIntervalHybridBVPath Coordinate duration =>
          path.toDerivativePath.toL1Path) ''
        finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound) := by
  let projectedEnvelope : Set (FiniteIntervalL1Path Coordinate duration) :=
    (fun path : FiniteIntervalHybridBVPath Coordinate duration =>
      path.toDerivativePath.toL1Path) ''
        finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound
  apply totallyBounded_of_forall_exists_compact_approx projectedEnvelope
  intro ε hε
  let variationMagnitude := variationBound.toReal
  obtain ⟨finalSampleIndex, hFinalSampleIndex⟩ :=
    exists_nat_gt (2 * duration * variationMagnitude / ε)
  have hScaled :
      2 * duration * variationMagnitude < ε * (finalSampleIndex : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hFinalSampleIndex
  have hDenominator : 0 < (finalSampleIndex + 1 : ℝ) := by positivity
  have hApproximationRate :
      duration / (finalSampleIndex + 1 : ℝ) * variationMagnitude < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDenominator]
    have hVariationMagnitudeNonnegative : 0 ≤ variationMagnitude := ENNReal.toReal_nonneg
    nlinarith
  let sampleRadius :=
    (l1Bound / ENNReal.ofReal duration + variationBound).toReal
  let compactFamily : Set (FiniteIntervalL1Path Coordinate duration) :=
    finiteIntervalSampleStepL1Path duration finalSampleIndex
        (finiteIntervalUniformSampleTime duration finalSampleIndex) ''
      Metric.closedBall
        (0 : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
        sampleRadius
  refine ⟨compactFamily, ?_, ?_⟩
  · exact isCompact_finiteIntervalSampleStepL1Path_image_closedBall
      duration finalSampleIndex
        (finiteIntervalUniformSampleTime duration finalSampleIndex) sampleRadius
  · intro projectedPath hProjectedPath
    rcases hProjectedPath with ⟨path, hPath, rfl⟩
    refine ⟨finiteIntervalHybridBVUniformSampleStepL1Path path finalSampleIndex, ?_, ?_⟩
    · refine ⟨finiteIntervalHybridBVUniformSampleValue path finalSampleIndex, ?_, rfl⟩
      exact uniformSampleValue_mem_closedBall_of_mem_uniformL1VariationEnvelope
        hDuration hL1Bound hVariationBound hPath finalSampleIndex
    · have hEdist := edist_toL1Path_uniformSampleStepL1Path_le
        path hDuration finalSampleIndex
      have hRateFinite :
          ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
              finiteIntervalHybridBVDerivativeTotalVariation path ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (hPath.2.trans_lt hVariationBound).ne
      have hDistance :
          dist path.toDerivativePath.toL1Path
              (finiteIntervalHybridBVUniformSampleStepL1Path path finalSampleIndex) ≤
            (ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
              finiteIntervalHybridBVDerivativeTotalVariation path).toReal := by
        rw [Lp.dist_edist]
        exact ENNReal.toReal_mono hRateFinite hEdist
      refine hDistance.trans_lt ?_
      calc
        (ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) *
            finiteIntervalHybridBVDerivativeTotalVariation path).toReal =
            duration / (finalSampleIndex + 1 : ℝ) *
              (finiteIntervalHybridBVDerivativeTotalVariation path).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
          positivity
        _ ≤ duration / (finalSampleIndex + 1 : ℝ) * variationMagnitude := by
          apply mul_le_mul_of_nonneg_left
          · exact ENNReal.toReal_mono hVariationBound.ne hPath.2
          · positivity
        _ < ε := hApproximationRate

/-- The strong-`L1` closure of the projected quantitative envelope is compact. -/
theorem isCompact_closure_toL1Path_image_uniformL1VariationEnvelope
    [DecidableEq Coordinate]
    (hDuration : 0 < duration) {l1Bound variationBound : ENNReal}
    (hL1Bound : l1Bound < ∞) (hVariationBound : variationBound < ∞) :
    IsCompact
      (closure
        ((fun path : FiniteIntervalHybridBVPath Coordinate duration =>
            path.toDerivativePath.toL1Path) ''
          finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound)) := by
  exact ((totallyBounded_toL1Path_image_uniformL1VariationEnvelope
    hDuration hL1Bound hVariationBound).closure).isCompact_of_isClosed isClosed_closure

/-- A strong-`L1` limit of hybrid paths with one finite uniform derivative-variation budget still
has an essentially bounded-variation representative.  The proof extracts an almost-everywhere
convergent subsequence, uses pointwise lower semicontinuity of total variation on its full-measure
convergence set, and then extends the resulting coordinatewise monotone decomposition globally.
This is the range-closure half of the HPR strong-`L1`-to-hybrid compactness upgrade; convergence of
the derivative test integrals is deliberately a separate theorem. -/
theorem hasBoundedVariation_of_tendsto_toL1Path_of_uniform_derivativeVariation
    (hDuration : 0 < duration)
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limit : FiniteIntervalL1Path Coordinate duration)
    {variationBound : ENNReal} (hVariationBound : variationBound < ∞)
    (hPaths : ∀ index,
      finiteIntervalHybridBVDerivativeTotalVariation (paths index) ≤ variationBound)
    (hTendsto : Tendsto
      (fun index => (paths index).toDerivativePath.toL1Path) atTop (nhds limit)) :
    FiniteIntervalL1Path.HasBoundedVariation limit := by
  let representative : ℕ → ℝ → FiniteCoordinateL1Value Coordinate :=
    fun index => (paths index).cadlagRepresentative.representative
  have hRepresentativeEventually (index : ℕ) :
      representative index =ᵐ[finiteOpenIntervalVolume duration]
        (paths index).toDerivativePath.toL1Path := by
    obtain ⟨hMemLp, hQuotient⟩ := (paths index).cadlagRepresentative.represents
    exact (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (paths index).toDerivativePath.toL1Path (representative index) hMemLp).mp
        ⟨hMemLp, hQuotient⟩
  have hInMeasure : TendstoInMeasure (finiteOpenIntervalVolume duration)
      representative atTop limit := by
    exact (tendstoInMeasure_of_tendsto_Lp hTendsto).congr_left
      (fun index => (hRepresentativeEventually index).symm)
  obtain ⟨subsequence, _hSubsequenceMonotone, hSubsequenceTendsto⟩ :=
    hInMeasure.exists_seq_tendsto_ae
  let convergenceSet : Set ℝ :=
    {time | Tendsto (fun index => representative (subsequence index) time)
      atTop (nhds (limit time))}
  let goodSet : Set ℝ := Set.Ioo 0 duration ∩ convergenceSet
  have hGoodEventually : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      time ∈ goodSet := by
    have hPhysical : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        time ∈ Set.Ioo 0 duration := ae_restrict_mem measurableSet_Ioo
    filter_upwards [hPhysical, hSubsequenceTendsto] with time hTime hTimeTendsto
    exact ⟨hTime, hTimeTendsto⟩
  have hGoodNonempty : goodSet.Nonempty := by
    by_contra hEmpty
    have hGoodEmpty : goodSet = ∅ := not_nonempty_iff_eq_empty.mp hEmpty
    have hComplementZero :
        finiteOpenIntervalVolume duration goodSetᶜ = 0 := by
      exact (ae_iff.mp hGoodEventually)
    rw [hGoodEmpty, compl_empty, finiteOpenIntervalVolume_apply_univ] at hComplementZero
    exact (ENNReal.ofReal_pos.mpr hDuration).ne' hComplementZero
  have hLimitVariation : eVariationOn (fun time => limit time) goodSet ≤ variationBound := by
    apply le_of_not_gt
    intro hBoundStrict
    have hEventuallyStrict := eVariationOn.lowerSemicontinuous_aux
      (F := fun index => representative (subsequence index))
      (p := atTop) (f := fun time => limit time) (s := goodSet)
      (fun time hTime => hTime.2) hBoundStrict
    obtain ⟨index, hIndexStrict⟩ := hEventuallyStrict.exists
    have hSubsequenceVariation :
        eVariationOn (representative (subsequence index)) goodSet ≤ variationBound := by
      calc
        eVariationOn (representative (subsequence index)) goodSet ≤
            eVariationOn (representative (subsequence index)) (Set.Ioo 0 duration) :=
          eVariationOn.mono _ inter_subset_left
        _ ≤ finiteIntervalHybridBVDerivativeTotalVariation
              (paths (subsequence index)) :=
          eVariationOn_cadlagRepresentative_le_derivativeTotalVariation _
        _ ≤ variationBound := hPaths _
    exact (not_lt_of_ge hSubsequenceVariation) hIndexStrict
  have hLimitVariationFinite :
      BoundedVariationOn (fun time => limit time) goodSet :=
    ne_top_of_le_ne_top hVariationBound.ne hLimitVariation
  have hCoordinateVariation (coordinate : Coordinate) :
      BoundedVariationOn (fun time => limit time coordinate) goodSet := by
    simpa only [Function.comp_def, PiLp.proj_apply] using!
      (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).lipschitzWith
        |>.comp_boundedVariationOn hLimitVariationFinite
  choose positivePart negativePart hPositiveMonotone hNegativeMonotone hAgreement using
    fun coordinate =>
      FiniteIntervalCadlagConstruction.exists_global_monotone_decomposition_of_boundedVariationOn
        hGoodNonempty (hCoordinateVariation coordinate)
  let coordinatePath : ℝ → Coordinate → ℝ :=
    fun time coordinate => positivePart coordinate time - negativePart coordinate time
  let coordinateEquivalence :
      FiniteCoordinateL1Value Coordinate ≃L[ℝ] (Coordinate → ℝ) :=
    PiLp.continuousLinearEquiv 1 ℝ fun _ : Coordinate => ℝ
  let limitRepresentative : ℝ → FiniteCoordinateL1Value Coordinate :=
    fun time => coordinateEquivalence.symm (coordinatePath time)
  have hLimitRepresentativeEventually :
      limitRepresentative =ᵐ[finiteOpenIntervalVolume duration] (fun time => limit time) := by
    filter_upwards [hGoodEventually] with time hTime
    apply coordinateEquivalence.injective
    funext coordinate
    change positivePart coordinate time - negativePart coordinate time =
      limit time coordinate
    exact (hAgreement coordinate hTime).symm
  have hLimitRepresentativeVariation :
      BoundedVariationOn limitRepresentative (Set.Ioo 0 duration) := by
    apply FiniteIntervalBVAlgebra.boundedVariationOn_finiteCoordinateL1Value_of_coordinate
    intro coordinate
    change BoundedVariationOn
      (fun time => positivePart coordinate time - negativePart coordinate time)
      (Set.Ioo 0 duration)
    exact FiniteIntervalBVAlgebra.boundedVariationOn_sub
      (FiniteIntervalBVAlgebra.boundedVariationOn_Ioo_of_monotone
        (hPositiveMonotone coordinate) 0 duration)
      (FiniteIntervalBVAlgebra.boundedVariationOn_Ioo_of_monotone
        (hNegativeMonotone coordinate) 0 duration)
  have hLimitRepresentativeMemLp :
      MemLp limitRepresentative 1 (finiteOpenIntervalVolume duration) :=
    (Lp.memLp limit).ae_eq hLimitRepresentativeEventually.symm
  apply FiniteIntervalL1Path.hasBoundedVariation_of_represents
    limit limitRepresentative
  · exact (FiniteIntervalL1Path.represents_iff_eventuallyEq
      limit limitRepresentative hLimitRepresentativeMemLp).mpr
        hLimitRepresentativeEventually
  · exact hLimitRepresentativeVariation

/-- Half-open cell between two consecutive points of a finite interior mesh. -/
def finiteIntervalInteriorMeshCell {cellCount : ℕ}
    (mesh : ℕ → ℝ) (cellIndex : Fin cellCount) : Set ℝ :=
  Set.Ioc (mesh cellIndex.val) (mesh (cellIndex.val + 1))

/-- Left-endpoint finite-step approximation of a continuous derivative test on an interior mesh.
It is zero away from the union of the mesh cells, leaving both boundary tails explicit. -/
noncomputable def finiteIntervalInteriorMeshStepTest {cellCount : ℕ}
    (test : C_c(ℝ, ℝ)) (mesh : ℕ → ℝ) : ℝ → ℝ :=
  VagueSignedMeasure.finiteWeightedIndicator (Finset.univ : Finset (Fin cellCount))
    (finiteIntervalInteriorMeshCell (cellCount := cellCount) mesh)
    (fun cellIndex : Fin cellCount => test (mesh cellIndex.val))

/-- Every interior mesh cell is Borel measurable. -/
theorem measurableSet_finiteIntervalInteriorMeshCell {cellCount : ℕ}
    (mesh : ℕ → ℝ) (cellIndex : Fin cellCount) :
    MeasurableSet (finiteIntervalInteriorMeshCell mesh cellIndex) :=
  measurableSet_Ioc

/-- Consecutive cells of a monotone natural mesh cover exactly the half-open interval between its
first point and its declared final point. -/
theorem iUnion_finiteIntervalInteriorMeshCell {cellCount : ℕ}
    (mesh : ℕ → ℝ) (hMeshMonotone : Monotone mesh) :
    (⋃ cellIndex : Fin cellCount,
      finiteIntervalInteriorMeshCell mesh cellIndex) =
        Set.Ioc (mesh 0) (mesh cellCount) := by
  rw [← hMeshMonotone.biUnion_Ico_Ioc_map_succ 0 cellCount]
  ext time
  simp only [finiteIntervalInteriorMeshCell, Set.mem_iUnion, Set.mem_Ico,
    Order.succ_eq_add_one]
  constructor
  · rintro ⟨cellIndex, hTime⟩
    exact ⟨cellIndex.val, ⟨Nat.zero_le _, cellIndex.isLt⟩, hTime⟩
  · rintro ⟨index, hIndex, hTime⟩
    exact ⟨⟨index, hIndex.2⟩, hTime⟩

/-- Distinct consecutive cells of a monotone natural mesh are disjoint. -/
theorem pairwiseDisjoint_finiteIntervalInteriorMeshCell {cellCount : ℕ}
    (mesh : ℕ → ℝ) (hMeshMonotone : Monotone mesh) :
    Pairwise (Function.onFun Disjoint
      (finiteIntervalInteriorMeshCell (cellCount := cellCount) mesh)) := by
  intro first second hDifferent
  exact hMeshMonotone.pairwise_disjoint_on_Ioc_succ
    (Fin.val_ne_iff.mpr hDifferent)

/-- On one cell of a strictly increasing mesh, the interior step test equals the test evaluated at
that cell's left endpoint. -/
theorem finiteIntervalInteriorMeshStepTest_eq_on_cell {cellCount : ℕ}
    (test : C_c(ℝ, ℝ)) (mesh : ℕ → ℝ) (hMeshMonotone : StrictMono mesh)
    (cellIndex : Fin cellCount) {time : ℝ}
    (hTime : time ∈ finiteIntervalInteriorMeshCell mesh cellIndex) :
    finiteIntervalInteriorMeshStepTest (cellCount := cellCount) test mesh time =
      test (mesh cellIndex.val) := by
  unfold finiteIntervalInteriorMeshStepTest VagueSignedMeasure.finiteWeightedIndicator
  rw [Finset.sum_eq_single cellIndex]
  · simp only [Set.indicator_of_mem hTime]
  · intro otherIndex _hOtherIndex hOtherDifferent
    have hDisjoint := pairwiseDisjoint_finiteIntervalInteriorMeshCell
      mesh hMeshMonotone.monotone hOtherDifferent
    have hOtherNotMem :
        time ∉ finiteIntervalInteriorMeshCell mesh otherIndex := by
      intro hOtherTime
      exact Set.disjoint_left.mp hDisjoint hOtherTime hTime
    simp only [Set.indicator_of_notMem hOtherNotMem]
  · exact fun hNotMem => (hNotMem (Finset.mem_univ cellIndex)).elim

/-- Away from every declared mesh cell, the interior step test is zero. -/
theorem finiteIntervalInteriorMeshStepTest_eq_zero_of_not_mem_iUnion
    {cellCount : ℕ} (test : C_c(ℝ, ℝ)) (mesh : ℕ → ℝ) {time : ℝ}
    (hTime : time ∉ ⋃ cellIndex : Fin cellCount,
      finiteIntervalInteriorMeshCell mesh cellIndex) :
    finiteIntervalInteriorMeshStepTest (cellCount := cellCount) test mesh time = 0 := by
  unfold finiteIntervalInteriorMeshStepTest VagueSignedMeasure.finiteWeightedIndicator
  apply Finset.sum_eq_zero
  intro cellIndex _hCellIndex
  have hCellNotMem : time ∉ finiteIntervalInteriorMeshCell mesh cellIndex := by
    intro hCell
    exact hTime (Set.mem_iUnion.mpr ⟨cellIndex, hCell⟩)
  simp only [Set.indicator_of_notMem hCellNotMem]

/-- Uniform continuity and the zero boundary values of an open-interval derivative test control
its left-endpoint step approximation on any sufficiently fine physical interior mesh.  The two
boundary tails are part of the estimate: no endpoint atom is smuggled into the open-interval
vague topology. -/
theorem exists_scale_for_finiteIntervalInteriorMeshStepTest
    (test : FiniteOpenIntervalVanishingContinuousTest duration) {error : ℝ}
    (hError : 0 < error) :
    ∃ scale > 0, ∀ {cellCount : ℕ} (mesh : ℕ → ℝ),
      (∀ meshIndex ≤ cellCount, mesh meshIndex ∈ Set.Ico 0 duration) →
      StrictMono mesh →
      mesh 0 < scale →
      duration - mesh cellCount < scale →
      (∀ meshIndex < cellCount,
        mesh (meshIndex + 1) - mesh meshIndex < scale) →
      ∀ time,
        |test.1 time - finiteIntervalInteriorMeshStepTest
          (cellCount := cellCount) test.1 mesh time| < error := by
  obtain ⟨scale, hScale, hUniform⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactlySupportedContinuousMapClass.uniformContinuous test.1) error hError
  refine ⟨scale, hScale, ?_⟩
  intro cellCount mesh hMeshPhysical hMeshMonotone hLeftTail hRightTail hMeshFine time
  by_cases hTimeCell : time ∈ ⋃ cellIndex : Fin cellCount,
      finiteIntervalInteriorMeshCell mesh cellIndex
  · obtain ⟨cellIndex, hTime⟩ := Set.mem_iUnion.mp hTimeCell
    rw [finiteIntervalInteriorMeshStepTest_eq_on_cell
      test.1 mesh hMeshMonotone cellIndex hTime]
    have hDistance : dist time (mesh cellIndex.val) < scale := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hTime.1.le)]
      exact lt_of_le_of_lt (sub_le_sub_right hTime.2 _)
        (hMeshFine cellIndex.val cellIndex.isLt)
    simpa only [Real.dist_eq] using hUniform hDistance
  · rw [finiteIntervalInteriorMeshStepTest_eq_zero_of_not_mem_iUnion
      test.1 mesh hTimeCell, sub_zero]
    have hOutsideRange : time ≤ mesh 0 ∨ mesh cellCount < time := by
      rw [iUnion_finiteIntervalInteriorMeshCell mesh hMeshMonotone.monotone] at hTimeCell
      simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hTimeCell
    rcases hOutsideRange with hTimeLeft | hTimeRight
    · by_cases hTimePhysical : time ∈ Set.Ioo 0 duration
      · have hDistance : dist time 0 < scale := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hTimePhysical.1]
          exact lt_of_le_of_lt hTimeLeft hLeftTail
        have hTestDistance := hUniform hDistance
        rw [FiniteOpenIntervalVanishingContinuousTest.leftBoundary_eq_zero test] at hTestDistance
        simpa only [Real.dist_eq, sub_zero] using hTestDistance
      · have hTestZero : test.1 time = 0 := by
          exact test.property (by simpa only [Set.mem_compl_iff] using hTimePhysical)
        simpa only [hTestZero, abs_zero] using hError
    · by_cases hTimePhysical : time ∈ Set.Ioo 0 duration
      · have hDistance : dist time duration < scale := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hTimePhysical.2.le)]
          linarith
        have hTestDistance := hUniform hDistance
        rw [FiniteOpenIntervalVanishingContinuousTest.rightBoundary_eq_zero test] at hTestDistance
        simpa only [Real.dist_eq, sub_zero] using hTestDistance
      · have hTestZero : test.1 time = 0 := by
          exact test.property (by simpa only [Set.mem_compl_iff] using hTimePhysical)
        simpa only [hTestZero, abs_zero] using hError

/-- A set that is dense relative to the open physical interval supplies a finite physical mesh
whose declared points all lie in that set and whose boundary tails and consecutive gaps are
arbitrarily small.  The mesh is extended monotonically on all natural indices so it can be used
directly by the finite-cell signed-measure lemmas. -/
theorem exists_fine_physical_mesh_of_dense_on_openInterval
    (hDuration : 0 < duration) (goodSet : Set ℝ)
    (hDense : Dense {time | time ∈ Set.Ioo 0 duration → time ∈ goodSet})
    {scale : ℝ} (hScale : 0 < scale) :
    ∃ (cellCount : ℕ) (mesh : ℕ → ℝ),
      StrictMono mesh ∧
      (∀ meshIndex ≤ cellCount, mesh meshIndex ∈ Set.Ico 0 duration) ∧
      (∀ meshIndex ≤ cellCount, mesh meshIndex ∈ goodSet) ∧
      mesh 0 < scale ∧
      duration - mesh cellCount < scale ∧
      (∀ meshIndex < cellCount,
        mesh (meshIndex + 1) - mesh meshIndex < scale) := by
  obtain ⟨cellCount, hCellCount⟩ :=
    exists_nat_gt (3 * duration / (2 * scale))
  let denominator : ℝ := cellCount + 1
  let width : ℝ := duration / denominator
  have hDenominator : 0 < denominator := by
    simp only [denominator]
    positivity
  have hWidth : 0 < width := div_pos hDuration hDenominator
  have hWidthIdentity : denominator * width = duration := by
    simp only [width]
    exact mul_div_cancel₀ duration hDenominator.ne'
  have hCellCountScaled : 3 * duration < 2 * scale * (cellCount : ℝ) := by
    have := (div_lt_iff₀ (by positivity : 0 < 2 * scale)).mp hCellCount
    nlinarith
  have hThreeHalfWidth : 3 * width / 2 < scale := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2)]
    have hCellCountDenominator : (cellCount : ℝ) < denominator := by
      simp only [denominator]
      linarith
    nlinarith
  have hMeshIntervalNonempty (meshIndex : ℕ) :
      (meshIndex : ℝ) * width < (meshIndex : ℝ) * width + width / 2 := by
    linarith
  choose mesh hMeshDense hMeshInterval using fun meshIndex =>
    hDense.exists_between (hMeshIntervalNonempty meshIndex)
  have hMeshMonotone : StrictMono mesh := by
    apply strictMono_nat_of_lt_succ
    intro meshIndex
    have hUpper := (hMeshInterval meshIndex).2
    have hNextLower := (hMeshInterval (meshIndex + 1)).1
    norm_num only [Nat.cast_add, Nat.cast_one] at hNextLower
    nlinarith
  have hMeshPhysical : ∀ meshIndex ≤ cellCount,
      mesh meshIndex ∈ Set.Ico 0 duration := by
    intro meshIndex hMeshIndex
    have hLower := (hMeshInterval meshIndex).1
    have hUpper := (hMeshInterval meshIndex).2
    have hIndexCast : (meshIndex : ℝ) ≤ cellCount := by exact_mod_cast hMeshIndex
    constructor
    · exact (mul_nonneg (Nat.cast_nonneg _) hWidth.le).trans hLower.le
    · have hDenominatorCast : denominator = (cellCount : ℝ) + 1 := by
        simp only [denominator]
      nlinarith
  have hMeshGood : ∀ meshIndex ≤ cellCount, mesh meshIndex ∈ goodSet := by
    intro meshIndex hMeshIndex
    exact hMeshDense meshIndex
      ⟨lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg _) hWidth.le)
          (hMeshInterval meshIndex).1,
        (hMeshPhysical meshIndex hMeshIndex).2⟩
  refine ⟨cellCount, mesh, hMeshMonotone, hMeshPhysical, hMeshGood, ?_, ?_, ?_⟩
  · have hUpper := (hMeshInterval 0).2
    norm_num only [Nat.cast_zero, zero_mul, zero_add] at hUpper
    nlinarith
  · have hLower := (hMeshInterval cellCount).1
    have hDenominatorCast : denominator = (cellCount : ℝ) + 1 := by
      simp only [denominator]
    nlinarith
  · intro meshIndex hMeshIndex
    have hLower := (hMeshInterval meshIndex).1
    have hNextUpper := (hMeshInterval (meshIndex + 1)).2
    norm_num only [Nat.cast_add, Nat.cast_one] at hNextUpper
    nlinarith

/-- On a physical strictly increasing mesh, the finite signed cell sum is exactly the finite sum
of canonical càdlàg path increments. -/
theorem derivative_finiteCellSum_eq_cadlagRepresentative_incrementSum
    {cellCount : ℕ}
    (path : FiniteIntervalHybridBVPath Coordinate duration) (coordinate : Coordinate)
    (test : C_c(ℝ, ℝ)) (mesh : ℕ → ℝ)
    (hMeshPhysical : ∀ meshIndex ≤ cellCount, mesh meshIndex ∈ Set.Ico 0 duration)
    (hMeshMonotone : StrictMono mesh) :
    ∑ cellIndex : Fin cellCount,
        test (mesh cellIndex.val) *
          (path.toDerivativePath.derivative coordinate).toSignedMeasure
            (finiteIntervalInteriorMeshCell mesh cellIndex) =
      ∑ cellIndex : Fin cellCount,
        test (mesh cellIndex.val) *
          (path.cadlagRepresentative.representative (mesh (cellIndex.val + 1)) coordinate -
            path.cadlagRepresentative.representative
              (mesh cellIndex.val) coordinate) := by
  apply Finset.sum_congr rfl
  intro cellIndex _hCellIndex
  simp only [finiteIntervalInteriorMeshCell]
  rw [path.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
    (hMeshPhysical cellIndex.val (Nat.le_of_lt cellIndex.isLt)).1
    (hMeshMonotone (Nat.lt_succ_self cellIndex.val)).le
    (hMeshPhysical (cellIndex.val + 1) cellIndex.isLt).2]

/-- A uniform approximation of a derivative test by an interior mesh step test controls the
error between the vague signed integral and the corresponding finite path-increment sum. -/
theorem abs_derivativeTestIntegral_sub_cadlagRepresentative_incrementSum_le
    {cellCount : ℕ}
    (path : FiniteIntervalHybridBVPath Coordinate duration) (coordinate : Coordinate)
    (test : FiniteOpenIntervalVanishingContinuousTest duration)
    (mesh : ℕ → ℝ)
    (hMeshPhysical : ∀ meshIndex ≤ cellCount, mesh meshIndex ∈ Set.Ico 0 duration)
    (hMeshMonotone : StrictMono mesh) {error : ℝ}
    (hError : ∀ time,
      |test.1 time - finiteIntervalInteriorMeshStepTest
        (cellCount := cellCount) test.1 mesh time| ≤ error) :
    |(path.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 -
        ∑ cellIndex : Fin cellCount,
          test.1 (mesh cellIndex.val) *
            (path.cadlagRepresentative.representative (mesh (cellIndex.val + 1)) coordinate -
              path.cadlagRepresentative.representative
                (mesh cellIndex.val) coordinate)| ≤
      error * (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation.real
        Set.univ := by
  rw [← derivative_finiteCellSum_eq_cadlagRepresentative_incrementSum
    path coordinate test.1 mesh hMeshPhysical hMeshMonotone]
  exact VagueSignedMeasure.abs_continuousTestIntegral_sub_finsetSum_apply_le_mul_totalVariation
    (path.toDerivativePath.derivative coordinate) test.1 Finset.univ
      (finiteIntervalInteriorMeshCell (cellCount := cellCount) mesh)
      (fun cellIndex => test.1 (mesh cellIndex.val))
      (fun cellIndex _hCellIndex => measurableSet_finiteIntervalInteriorMeshCell mesh cellIndex)
      hError

/-- On a fixed finite mesh, pointwise convergence of canonical representatives implies convergence
of every finite weighted path-increment sum. -/
theorem tendsto_cadlagRepresentative_incrementSum_of_tendsto_on_mesh
    {cellCount : ℕ}
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limit : FiniteIntervalHybridBVPath Coordinate duration) (coordinate : Coordinate)
    (test : C_c(ℝ, ℝ)) (mesh : ℕ → ℝ)
    (hRepresentativeTendsto : ∀ meshIndex ≤ cellCount,
      Tendsto
        (fun sequenceIndex =>
          (paths sequenceIndex).cadlagRepresentative.representative
            (mesh meshIndex) coordinate)
        atTop
        (nhds (limit.cadlagRepresentative.representative (mesh meshIndex) coordinate))) :
    Tendsto
      (fun sequenceIndex =>
        ∑ cellIndex : Fin cellCount,
          test (mesh cellIndex.val) *
            ((paths sequenceIndex).cadlagRepresentative.representative
                (mesh (cellIndex.val + 1)) coordinate -
              (paths sequenceIndex).cadlagRepresentative.representative
                (mesh cellIndex.val) coordinate))
      atTop
      (nhds
        (∑ cellIndex : Fin cellCount,
          test (mesh cellIndex.val) *
            (limit.cadlagRepresentative.representative
                (mesh (cellIndex.val + 1)) coordinate -
              limit.cadlagRepresentative.representative
                (mesh cellIndex.val) coordinate))) := by
  apply tendsto_finsetSum
  intro cellIndex _hCellIndex
  exact tendsto_const_nhds.mul
    ((hRepresentativeTendsto (cellIndex.val + 1) cellIndex.isLt).sub
      (hRepresentativeTendsto cellIndex.val (Nat.le_of_lt cellIndex.isLt)))

/-- The real total variation of one derivative coordinate is bounded by the complete finite-
coordinate derivative variation whenever the latter is finite. -/
theorem derivativeCoordinateTotalVariationReal_le_totalVariationToReal
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate)
    (hTotalVariationFinite : finiteIntervalHybridBVDerivativeTotalVariation path < ∞) :
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation.real Set.univ ≤
      (finiteIntervalHybridBVDerivativeTotalVariation path).toReal := by
  have hCoordinateLe :
      (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ ≤
        finiteIntervalHybridBVDerivativeTotalVariation path :=
    Finset.single_le_sum
      (fun other _hOther => zero_le
        (a := (path.toDerivativePath.derivative other).toSignedMeasure.totalVariation Set.univ))
      (Finset.mem_univ coordinate)
  have hCoordinateFinite :
      (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ ≠ ∞ :=
    ne_top_of_le_ne_top hTotalVariationFinite.ne hCoordinateLe
  rw [Measure.real, ENNReal.toReal_le_toReal]
  · exact hCoordinateLe
  · exact hCoordinateFinite
  · exact hTotalVariationFinite.ne

/-- Pointwise convergence of canonical representatives on a relatively dense interior set,
together with one uniform derivative-variation budget, implies convergence against every
zero-extended open-interval derivative test.  This is the finite-mesh core of the HPR hybrid
topology upgrade. -/
theorem tendsto_derivativeTestIntegral_of_uniformVariation_of_tendsto_on_dense
    (hDuration : 0 < duration)
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limit : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate)
    (test : FiniteOpenIntervalVanishingContinuousTest duration)
    (goodSet : Set ℝ)
    (hDense : Dense {time | time ∈ Set.Ioo 0 duration → time ∈ goodSet})
    (hRepresentativeTendsto : ∀ time ∈ goodSet,
      Tendsto
        (fun sequenceIndex =>
          (paths sequenceIndex).cadlagRepresentative.representative time coordinate)
        atTop
        (nhds (limit.cadlagRepresentative.representative time coordinate)))
    {variationMagnitude : ℝ} (hVariationMagnitude : 0 ≤ variationMagnitude)
    (hVariation : ∀ sequenceIndex,
      finiteIntervalHybridBVDerivativeTotalVariation (paths sequenceIndex) < ∞ ∧
      (finiteIntervalHybridBVDerivativeTotalVariation
        (paths sequenceIndex)).toReal ≤ variationMagnitude) :
    Tendsto
      (fun sequenceIndex =>
        ((paths sequenceIndex).toDerivativePath.derivative coordinate)
          |>.continuousTestIntegral test.1)
      atTop
      (nhds ((limit.toDerivativePath.derivative coordinate)
        |>.continuousTestIntegral test.1)) := by
  let limitVariation :=
    (limit.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation.real Set.univ
  let approximationBudget := variationMagnitude + limitVariation + 1
  have hLimitVariationNonnegative : 0 ≤ limitVariation := measureReal_nonneg
  have hApproximationBudgetPositive : 0 < approximationBudget := by
    dsimp only [approximationBudget]
    linarith
  rw [Metric.tendsto_nhds]
  intro convergenceError hConvergenceError
  let testError := convergenceError / (4 * approximationBudget)
  have hTestError : 0 < testError := by
    exact div_pos hConvergenceError (mul_pos (by norm_num) hApproximationBudgetPositive)
  have hTestErrorBudget : testError * approximationBudget = convergenceError / 4 := by
    dsimp only [testError]
    field_simp
  obtain ⟨scale, hScale, hTestApproximation⟩ :=
    exists_scale_for_finiteIntervalInteriorMeshStepTest test hTestError
  obtain ⟨cellCount, mesh, hMeshMonotone, hMeshPhysical, hMeshGood,
      hLeftTail, hRightTail, hMeshFine⟩ :=
    exists_fine_physical_mesh_of_dense_on_openInterval
      hDuration goodSet hDense hScale
  have hApproximation (time : ℝ) :
      |test.1 time - finiteIntervalInteriorMeshStepTest
        (cellCount := cellCount) test.1 mesh time| ≤ testError :=
    (hTestApproximation mesh hMeshPhysical hMeshMonotone hLeftTail hRightTail
      hMeshFine time).le
  let incrementSum (path : FiniteIntervalHybridBVPath Coordinate duration) : ℝ :=
    ∑ cellIndex : Fin cellCount,
      test.1 (mesh cellIndex.val) *
        (path.cadlagRepresentative.representative
            (mesh (cellIndex.val + 1)) coordinate -
          path.cadlagRepresentative.representative
            (mesh cellIndex.val) coordinate)
  have hIncrementSumTendsto :
      Tendsto (fun sequenceIndex => incrementSum (paths sequenceIndex)) atTop
        (nhds (incrementSum limit)) := by
    exact tendsto_cadlagRepresentative_incrementSum_of_tendsto_on_mesh
      paths limit coordinate test.1 mesh
        (fun meshIndex hMeshIndex =>
          hRepresentativeTendsto (mesh meshIndex) (hMeshGood meshIndex hMeshIndex))
  have hIncrementSumEventually : ∀ᶠ sequenceIndex in atTop,
      |incrementSum (paths sequenceIndex) - incrementSum limit| < convergenceError / 2 := by
    have := (Metric.tendsto_nhds.mp hIncrementSumTendsto)
      (convergenceError / 2) (by positivity)
    simpa only [Real.dist_eq] using this
  filter_upwards [hIncrementSumEventually] with sequenceIndex hIncrementSum
  let pathIntegral :=
    ((paths sequenceIndex).toDerivativePath.derivative coordinate)
      |>.continuousTestIntegral test.1
  let limitIntegral :=
    (limit.toDerivativePath.derivative coordinate).continuousTestIntegral test.1
  have hPathApproximation :
      |pathIntegral - incrementSum (paths sequenceIndex)| ≤ convergenceError / 4 := by
    calc
      |pathIntegral - incrementSum (paths sequenceIndex)| ≤
          testError *
            (((paths sequenceIndex).toDerivativePath.derivative coordinate)
              |>.toSignedMeasure.totalVariation.real Set.univ) := by
        exact abs_derivativeTestIntegral_sub_cadlagRepresentative_incrementSum_le
          (paths sequenceIndex) coordinate test mesh hMeshPhysical hMeshMonotone hApproximation
      _ ≤ testError * variationMagnitude := by
        apply mul_le_mul_of_nonneg_left
        · exact derivativeCoordinateTotalVariationReal_le_totalVariationToReal
            (paths sequenceIndex) coordinate (hVariation sequenceIndex).1 |>.trans
              (hVariation sequenceIndex).2
        · exact hTestError.le
      _ ≤ testError * approximationBudget := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [approximationBudget]
          linarith
        · exact hTestError.le
      _ = convergenceError / 4 := hTestErrorBudget
  have hLimitApproximation :
      |limitIntegral - incrementSum limit| ≤ convergenceError / 4 := by
    calc
      |limitIntegral - incrementSum limit| ≤ testError * limitVariation := by
        exact abs_derivativeTestIntegral_sub_cadlagRepresentative_incrementSum_le
          limit coordinate test mesh hMeshPhysical hMeshMonotone hApproximation
      _ ≤ testError * approximationBudget := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [approximationBudget]
          linarith
        · exact hTestError.le
      _ = convergenceError / 4 := hTestErrorBudget
  have hLimitApproximationReversed :
      |incrementSum limit - limitIntegral| ≤ convergenceError / 4 := by
    rw [abs_sub_comm]
    exact hLimitApproximation
  change dist pathIntegral limitIntegral < convergenceError
  rw [Real.dist_eq]
  have hFirstTriangle :=
    abs_sub_le pathIntegral (incrementSum (paths sequenceIndex)) (incrementSum limit)
  have hSecondTriangle := abs_sub_le pathIntegral (incrementSum limit) limitIntegral
  nlinarith

end

end FiniteMarkovProcesses
