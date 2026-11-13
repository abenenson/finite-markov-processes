/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1DerivativeTopology
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasurePositiveClosure
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Boundary cutoffs for finite-interval vague signed measures

The hybrid derivative topology tests continuous functions that vanish outside an open physical
interval.  This module supplies the explicit cutoff and localized total-variation estimate needed
to compare that relative test family with genuine vague convergence when boundary variation is
uniformly negligible.

## Main declarations

* `finiteOpenIntervalBoundaryLayer` is the complement of a compact interior core.
* `finiteOpenIntervalCoreCutoff` is a compactly supported continuous cutoff equal to one on that
  core and zero outside the physical interval.
* `tendsto_finiteOpenIntervalVolume_boundaryLayer_div_nat_zero` gives a canonical shrinking
  two-sided boundary family.
* `SignedMeasure.exists_positive_margin_totalVariation_real_boundaryLayer_lt` proves boundary
  tightness for every finite signed measure supported in the physical interval.
* `VagueSignedMeasure.abs_continuousTestIntegral_sub_le_mul_totalVariationOn` localizes test error
  to a measurable event.
* `finiteOpenIntervalCoreCutoffMulTest` turns any compact test into an admissible relative test.
* `VagueSignedMeasure.tendsto_of_relative_continuousTestIntegral_of_boundaryVariation` upgrades
  relative convergence to full vague convergence under uniform boundary control.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open MeasureTheory Set
open scoped CompactlySupported Topology

noncomputable section

/-- The time region omitted by an interior core with the given boundary margin. -/
def finiteOpenIntervalBoundaryLayer (duration margin : ℝ) : Set ℝ :=
  (Set.Ioo margin (duration - margin))ᶜ

/-- The finite-interval boundary layer is Borel measurable. -/
theorem measurableSet_finiteOpenIntervalBoundaryLayer (duration margin : ℝ) :
    MeasurableSet (finiteOpenIntervalBoundaryLayer duration margin) :=
  measurableSet_Ioo.compl

/-- Decreasing the interior margin can only shrink the omitted boundary layer. -/
theorem finiteOpenIntervalBoundaryLayer_mono
    {duration firstMargin secondMargin : ℝ}
    (hMargin : firstMargin ≤ secondMargin) :
    finiteOpenIntervalBoundaryLayer duration firstMargin ⊆
      finiteOpenIntervalBoundaryLayer duration secondMargin := by
  apply Set.compl_subset_compl.mpr
  intro point hPoint
  exact ⟨hMargin.trans_lt hPoint.1, hPoint.2.trans_le (sub_le_sub_left hMargin duration)⟩

/-- A continuous tent cutoff: zero outside `[0, duration]`, linear across each margin, and one on
the compact interior core `[margin, duration - margin]`. -/
noncomputable def finiteOpenIntervalCoreCutoff
    (duration margin : ℝ) (hMargin : 0 < margin) : C_c(ℝ, ℝ) := by
  let cutoffFunction : ℝ → ℝ := fun time =>
    max 0 (min 1 (time / margin)) *
      max 0 (min 1 ((duration - time) / margin))
  have hContinuous : Continuous cutoffFunction := by
    unfold cutoffFunction
    fun_prop
  let cutoffContinuous : C(ℝ, ℝ) := ⟨cutoffFunction, hContinuous⟩
  refine ⟨cutoffContinuous, ?_⟩
  rw [hasCompactSupport_def]
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc 0 duration)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro time hSupport
  by_contra hTime
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hTime
  rcases hTime with hTime | hTime
  · have hRatio : time / margin < 0 :=
      div_neg_of_neg_of_pos hTime hMargin
    apply hSupport
    change cutoffFunction time = 0
    simp [cutoffFunction, hRatio.le]
  · have hDifference : duration - time < 0 := sub_neg.mpr hTime
    have hRatio : (duration - time) / margin < 0 :=
      div_neg_of_neg_of_pos hDifference hMargin
    apply hSupport
    change cutoffFunction time = 0
    simp [cutoffFunction, hRatio.le]

/-- Pointwise formula for the finite-interval core cutoff. -/
@[simp]
theorem finiteOpenIntervalCoreCutoff_apply
    (duration margin : ℝ) (hMargin : 0 < margin) (time : ℝ) :
    finiteOpenIntervalCoreCutoff duration margin hMargin time =
      max 0 (min 1 (time / margin)) *
        max 0 (min 1 ((duration - time) / margin)) :=
  rfl

/-- The core cutoff vanishes off the open physical interval. -/
theorem finiteOpenIntervalCoreCutoff_eq_zero_of_not_mem
    {duration margin time : ℝ} (hMargin : 0 < margin)
    (hTime : time ∉ Set.Ioo 0 duration) :
    finiteOpenIntervalCoreCutoff duration margin hMargin time = 0 := by
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hTime
  rcases hTime with hTime | hTime
  · have hRatio : time / margin ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨hTime, hMargin.le⟩)
    simp [finiteOpenIntervalCoreCutoff_apply, hRatio]
  · have hDifference : duration - time ≤ 0 := sub_nonpos.mpr hTime
    have hRatio : (duration - time) / margin ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨hDifference, hMargin.le⟩)
    simp [finiteOpenIntervalCoreCutoff_apply, hRatio]

/-- The core cutoff equals one away from both boundary margins. -/
theorem finiteOpenIntervalCoreCutoff_eq_one_of_mem_core
    {duration margin time : ℝ} (hMargin : 0 < margin)
    (hTime : time ∈ Set.Icc margin (duration - margin)) :
    finiteOpenIntervalCoreCutoff duration margin hMargin time = 1 := by
  have hLeftRatio : 1 ≤ time / margin :=
    (le_div_iff₀ hMargin).mpr (by simpa using hTime.1)
  have hRightNumerator : margin ≤ duration - time := by linarith [hTime.2]
  have hRightRatio : 1 ≤ (duration - time) / margin :=
    (le_div_iff₀ hMargin).mpr (by simpa using hRightNumerator)
  simp [finiteOpenIntervalCoreCutoff_apply, min_eq_left hLeftRatio,
    min_eq_left hRightRatio]

/-- The core cutoff takes values in the unit interval. -/
theorem finiteOpenIntervalCoreCutoff_mem_Icc
    {duration margin : ℝ} (hMargin : 0 < margin) (time : ℝ) :
    finiteOpenIntervalCoreCutoff duration margin hMargin time ∈ Set.Icc 0 1 := by
  let left := max 0 (min 1 (time / margin))
  let right := max 0 (min 1 ((duration - time) / margin))
  have hLeft : left ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  have hRight : right ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (min_le_left _ _)
  rw [finiteOpenIntervalCoreCutoff_apply]
  change left * right ∈ Set.Icc 0 1
  exact ⟨mul_nonneg hLeft.1 hRight.1,
    (mul_le_of_le_one_left hRight.1 hLeft.2).trans hRight.2⟩

/-- Every compact subset of a nonempty open physical interval lies in one closed interior core. -/
theorem exists_positive_margin_compact_subset_finiteOpenIntervalCore
    {duration : ℝ} (hDuration : 0 < duration)
    {compactSet : Set ℝ} (hCompact : IsCompact compactSet)
    (hSubset : compactSet ⊆ Set.Ioo 0 duration) :
    ∃ margin : ℝ, 0 < margin ∧
      compactSet ⊆ Set.Ioo margin (duration - margin) := by
  rcases compactSet.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨duration / 2, by positivity, ?_⟩
    simp [hEmpty]
  · obtain ⟨left, hLeftMember, hLeftMinimum⟩ :=
      hCompact.exists_isMinOn hNonempty continuousOn_id
    obtain ⟨right, hRightMember, hRightMaximum⟩ :=
      hCompact.exists_isMaxOn hNonempty continuousOn_id
    have hLeftPositive : 0 < left := (hSubset hLeftMember).1
    have hRightGapPositive : 0 < duration - right :=
      sub_pos.mpr (hSubset hRightMember).2
    refine ⟨min left (duration - right) / 2,
      half_pos (lt_min hLeftPositive hRightGapPositive), ?_⟩
    intro point hPoint
    have hLeftOrder : left ≤ point := hLeftMinimum hPoint
    have hRightOrder : point ≤ right := hRightMaximum hPoint
    constructor
    · linarith [min_le_left left (duration - right)]
    · linarith [min_le_right left (duration - right)]

/-- The physical-time volume of the two-sided boundary layer can be made arbitrarily small. -/
theorem exists_positive_margin_finiteOpenIntervalVolume_boundaryLayer_lt
    {duration : ℝ} (hDuration : 0 < duration)
    {epsilon : ENNReal} (hEpsilon : 0 < epsilon) :
    ∃ margin : ℝ, 0 < margin ∧
      finiteOpenIntervalVolume duration
        (finiteOpenIntervalBoundaryLayer duration margin) < epsilon := by
  obtain ⟨compactSet, hCompactSubset, hCompact, hCompactError⟩ :=
    measurableSet_Ioo.exists_isCompact_sdiff_lt
      (measure_ne_top (finiteOpenIntervalVolume duration) (Set.Ioo 0 duration))
      hEpsilon.ne'
  obtain ⟨margin, hMargin, hCompactCore⟩ :=
    exists_positive_margin_compact_subset_finiteOpenIntervalCore
      hDuration hCompact hCompactSubset
  refine ⟨margin, hMargin, ?_⟩
  have hBoundaryMeasurable :=
    measurableSet_finiteOpenIntervalBoundaryLayer duration margin
  have hBoundaryWithinSubset :
      finiteOpenIntervalBoundaryLayer duration margin ∩ Set.Ioo 0 duration ⊆
        Set.Ioo 0 duration \ compactSet := by
    intro point hPoint
    refine ⟨hPoint.2, ?_⟩
    intro hPointCompact
    exact hPoint.1 (hCompactCore hPointCompact)
  rw [finiteOpenIntervalVolume, Measure.restrict_apply hBoundaryMeasurable]
  calc
    volume (finiteOpenIntervalBoundaryLayer duration margin ∩ Set.Ioo 0 duration) ≤
        volume (Set.Ioo 0 duration \ compactSet) :=
      measure_mono hBoundaryWithinSubset
    _ = finiteOpenIntervalVolume duration (Set.Ioo 0 duration \ compactSet) := by
      rw [finiteOpenIntervalVolume,
        Measure.restrict_apply (measurableSet_Ioo.diff hCompact.measurableSet),
        inter_eq_left.mpr sdiff_subset]
    _ < epsilon := hCompactError

/-- Boundary layers at the canonical reciprocal margins have physical-time volume tending to
zero. -/
theorem tendsto_finiteOpenIntervalVolume_boundaryLayer_div_nat_zero
    {duration : ℝ} (hDuration : 0 < duration) :
    Filter.Tendsto
      (fun index : ℕ => finiteOpenIntervalVolume duration
        (finiteOpenIntervalBoundaryLayer duration (duration / (index + 3 : ℕ))))
      Filter.atTop (nhds 0) := by
  let margin : ℕ → ℝ := fun index => duration / (index + 3 : ℕ)
  have hMargin (index : ℕ) : margin index ∈ Set.Ioo 0 (duration / 2) := by
    have hDenominator : 2 < index + 3 := by omega
    constructor
    · dsimp only [margin]
      positivity
    · dsimp only [margin]
      exact (div_lt_div_iff_of_pos_left hDuration (by positivity) (by positivity)).mpr
        (by exact_mod_cast hDenominator)
  have hBoundaryBound (index : ℕ) :
      finiteOpenIntervalVolume duration
          (finiteOpenIntervalBoundaryLayer duration (margin index)) ≤
        ENNReal.ofReal (margin index) + ENNReal.ofReal (margin index) := by
    have hSubset :
        finiteOpenIntervalBoundaryLayer duration (margin index) ∩ Set.Ioo 0 duration ⊆
          Set.Ioc 0 (margin index) ∪
            Set.Ico (duration - margin index) duration := by
      intro point hPoint
      have hOutsideCore :
          ¬(margin index < point ∧ point < duration - margin index) := hPoint.1
      rw [not_and_or, not_lt, not_lt] at hOutsideCore
      rcases hOutsideCore with hLeft | hRight
      · exact Or.inl ⟨hPoint.2.1, hLeft⟩
      · exact Or.inr ⟨hRight, hPoint.2.2⟩
    rw [finiteOpenIntervalVolume,
      Measure.restrict_apply
        (measurableSet_finiteOpenIntervalBoundaryLayer duration (margin index))]
    calc
      volume (finiteOpenIntervalBoundaryLayer duration (margin index) ∩
          Set.Ioo 0 duration) ≤
        volume (Set.Ioc 0 (margin index) ∪
          Set.Ico (duration - margin index) duration) := measure_mono hSubset
      _ ≤ volume (Set.Ioc 0 (margin index)) +
          volume (Set.Ico (duration - margin index) duration) := measure_union_le _ _
      _ = ENNReal.ofReal (margin index) + ENNReal.ofReal (margin index) := by
        rw [Real.volume_Ioc, Real.volume_Ico]
        ring_nf
  have hMarginTendsto : Filter.Tendsto margin Filter.atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat duration).comp
      (Filter.tendsto_add_atTop_nat 3)
  have hUpperTendsto : Filter.Tendsto
      (fun index => ENNReal.ofReal (margin index) + ENNReal.ofReal (margin index))
      Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero, add_zero] using
      (ENNReal.tendsto_ofReal hMarginTendsto).add
        (ENNReal.tendsto_ofReal hMarginTendsto)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpperTendsto
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · exact Filter.Eventually.of_forall hBoundaryBound

/-- Multiplying by the core cutoff converts an arbitrary compact test into a zero-extended test
for the relative open-interval vague topology. -/
noncomputable def finiteOpenIntervalCoreCutoffMulTest
    {duration margin : ℝ} (hMargin : 0 < margin) (test : C_c(ℝ, ℝ)) :
    FiniteOpenIntervalVanishingContinuousTest duration :=
  ⟨test * finiteOpenIntervalCoreCutoff duration margin hMargin, by
    intro time hTime
    simp [finiteOpenIntervalCoreCutoff_eq_zero_of_not_mem hMargin hTime]⟩

namespace SignedMeasure

/-- Restricting a finite signed measure to a measurable carrier also restricts its total
variation to that carrier. -/
theorem totalVariation_restrict_eq_self_of_restrict_eq_self
    {Carrier : Type*} [MeasurableSpace Carrier]
    (measure : SignedMeasure Carrier) {carrier : Set Carrier}
    (hCarrier : MeasurableSet carrier)
    (hSupport : measure.restrict carrier = measure) :
    measure.totalVariation.restrict carrier = measure.totalVariation := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change measure.totalVariation carrierᶜ = 0
  obtain ⟨positiveSet, hPositiveSet, hPositive, hNegative,
      hPositivePart, hNegativePart⟩ := measure.toJordanDecomposition_spec
  have hMeasureZero {event : Set Carrier} (hEvent : MeasurableSet event)
      (hEventSubset : event ⊆ carrierᶜ) : measure event = 0 := by
    have hApply := congrArg (fun restricted : SignedMeasure Carrier => restricted event) hSupport
    change (measure.restrict carrier) event = measure event at hApply
    rw [VectorMeasure.restrict_apply measure hCarrier hEvent] at hApply
    have hDisjoint : Disjoint event carrier :=
      Set.disjoint_left.mpr fun point hPointEvent hPointCarrier =>
        (hEventSubset hPointEvent) hPointCarrier
    rw [hDisjoint.inter_eq, measure.empty] at hApply
    exact hApply.symm
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    hPositivePart, hNegativePart,
    SignedMeasure.toMeasureOfZeroLE_apply measure hPositive hPositiveSet hCarrier.compl,
    SignedMeasure.toMeasureOfLEZero_apply measure hNegative hPositiveSet.compl hCarrier.compl]
  have hPositiveZero : measure (positiveSet ∩ carrierᶜ) = 0 :=
    hMeasureZero (hPositiveSet.inter hCarrier.compl) Set.inter_subset_right
  have hNegativeZero : measure (positiveSetᶜ ∩ carrierᶜ) = 0 :=
    hMeasureZero (hPositiveSet.compl.inter hCarrier.compl) Set.inter_subset_right
  rw [add_eq_zero]
  constructor
  · apply ENNReal.coe_eq_zero.mpr
    exact Subtype.ext hPositiveZero
  · apply ENNReal.coe_eq_zero.mpr
    exact Subtype.ext (neg_eq_zero.mpr hNegativeZero)

/-- A finite signed measure supported in the open physical interval has arbitrarily small total
variation in a sufficiently thin two-sided boundary layer. -/
theorem exists_positive_margin_totalVariation_real_boundaryLayer_lt
    (measure : SignedMeasure ℝ) {duration epsilon : ℝ}
    (hDuration : 0 < duration) (hEpsilon : 0 < epsilon)
    (hSupport : measure.restrict (Set.Ioo 0 duration) = measure) :
    ∃ margin : ℝ, 0 < margin ∧
      measure.totalVariation.real
        (finiteOpenIntervalBoundaryLayer duration margin) < epsilon := by
  let variation := measure.totalVariation
  let : IsFiniteMeasure variation := by
    refine ⟨?_⟩
    unfold variation SignedMeasure.totalVariation
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  have hVariationSupport : variation.restrict (Set.Ioo 0 duration) = variation :=
    totalVariation_restrict_eq_self_of_restrict_eq_self measure measurableSet_Ioo hSupport
  obtain ⟨compactSet, hCompactSubset, hCompact, hCompactError⟩ :=
    measurableSet_Ioo.exists_isCompact_sdiff_lt
      (measure_ne_top variation (Set.Ioo 0 duration))
      (ne_of_gt (ENNReal.ofReal_pos.mpr hEpsilon))
  obtain ⟨margin, hMargin, hCompactCore⟩ :=
    exists_positive_margin_compact_subset_finiteOpenIntervalCore
      hDuration hCompact hCompactSubset
  refine ⟨margin, hMargin, ?_⟩
  have hBoundaryMeasurable :=
    measurableSet_finiteOpenIntervalBoundaryLayer duration margin
  have hBoundaryWithinSubset :
      finiteOpenIntervalBoundaryLayer duration margin ∩ Set.Ioo 0 duration ⊆
        Set.Ioo 0 duration \ compactSet := by
    intro point hPoint
    refine ⟨hPoint.2, ?_⟩
    intro hPointCompact
    exact hPoint.1 (hCompactCore hPointCompact)
  have hBoundaryMeasure :
      variation (finiteOpenIntervalBoundaryLayer duration margin) =
        variation (finiteOpenIntervalBoundaryLayer duration margin ∩ Set.Ioo 0 duration) := by
    calc
      variation (finiteOpenIntervalBoundaryLayer duration margin) =
          variation.restrict (Set.Ioo 0 duration)
            (finiteOpenIntervalBoundaryLayer duration margin) := by
        rw [hVariationSupport]
      _ = variation
          (finiteOpenIntervalBoundaryLayer duration margin ∩ Set.Ioo 0 duration) :=
        Measure.restrict_apply hBoundaryMeasurable
  have hBoundaryENNReal :
      variation (finiteOpenIntervalBoundaryLayer duration margin) <
        ENNReal.ofReal epsilon := by
    rw [hBoundaryMeasure]
    exact (measure_mono hBoundaryWithinSubset).trans_lt hCompactError
  rw [measureReal_def]
  have hBoundaryReal :=
    (ENNReal.toReal_lt_toReal (measure_ne_top variation _) (by simp)).mpr
      hBoundaryENNReal
  simpa [ENNReal.toReal_ofReal hEpsilon.le] using hBoundaryReal

end SignedMeasure

namespace VagueSignedMeasure

universe u

variable {Carrier : Type u} [MeasurableSpace Carrier] [TopologicalSpace Carrier]
  [OpensMeasurableSpace Carrier]

/-- If two compact tests agree off a measurable event, their signed-integral difference is
controlled by their pointwise error on that event times the event-local total variation. -/
theorem abs_continuousTestIntegral_sub_le_mul_totalVariationOn
    (measure : VagueSignedMeasure Carrier)
    (first second : C_c(Carrier, ℝ)) {event : Set Carrier}
    (hEvent : MeasurableSet event) {bound : ℝ}
    (hBound : ∀ point, |first point - second point| ≤ bound)
    (hOutside : Set.EqOn first second eventᶜ) :
    |measure.continuousTestIntegral first -
        measure.continuousTestIntegral second| ≤
      bound * measure.toSignedMeasure.totalVariation.real event := by
  let positive := measure.toSignedMeasure.toJordanDecomposition.posPart
  let negative := measure.toSignedMeasure.toJordanDecomposition.negPart
  let difference : Carrier → ℝ := fun point => first point - second point
  have hDifferenceIndicator : event.indicator difference = difference := by
    funext point
    by_cases hPoint : point ∈ event
    · simp [hPoint]
    · have hAgreement := hOutside (Set.mem_compl hPoint)
      simp [difference, hPoint, hAgreement]
  have hPositive :
      |∫ point, difference point ∂positive| ≤
        bound * positive.real event := by
    rw [← hDifferenceIndicator, integral_indicator hEvent]
    simpa only [Real.norm_eq_abs, measureReal_def,
      Measure.restrict_apply_univ] using
      norm_integral_le_of_norm_le_const
        (μ := positive.restrict event) (f := difference) (C := bound)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hBound point)
  have hNegative :
      |∫ point, difference point ∂negative| ≤
        bound * negative.real event := by
    rw [← hDifferenceIndicator, integral_indicator hEvent]
    simpa only [Real.norm_eq_abs, measureReal_def,
      Measure.restrict_apply_univ] using
      norm_integral_le_of_norm_le_const
        (μ := negative.restrict event) (f := difference) (C := bound)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hBound point)
  have hDifference :
      measure.continuousTestIntegral first -
          measure.continuousTestIntegral second =
        (∫ point, difference point ∂positive) -
          ∫ point, difference point ∂negative := by
    unfold continuousTestIntegral difference
    rw [integral_sub (measure.integrable_continuousTest_posPart first)
        (measure.integrable_continuousTest_posPart second),
      integral_sub (measure.integrable_continuousTest_negPart first)
        (measure.integrable_continuousTest_negPart second)]
    ring
  rw [hDifference]
  calc
    |(∫ point, difference point ∂positive) -
        ∫ point, difference point ∂negative| ≤
      |∫ point, difference point ∂positive| +
        |∫ point, difference point ∂negative| := abs_sub _ _
    _ ≤ bound * positive.real event + bound * negative.real event :=
      add_le_add hPositive hNegative
    _ = bound * measure.toSignedMeasure.totalVariation.real event := by
      rw [SignedMeasure.totalVariation, measureReal_add_apply]
      ring

private theorem exists_positive_continuousTest_bound
    (test : C_c(ℝ, ℝ)) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ point, |test point| ≤ bound := by
  have hBounded : BddAbove ((fun point => |test point|) '' tsupport test) :=
    test.hasCompactSupport.bddAbove_image test.continuous.abs.continuousOn
  obtain ⟨rawBound, hRawBound⟩ := hBounded
  refine ⟨max 1 rawBound,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro point
  by_cases hPoint : point ∈ tsupport test
  · exact (hRawBound ⟨point, hPoint, rfl⟩).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hPoint, abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

/-- A signed measure supported in the open physical interval is nonnegative when it evaluates
every nonnegative test from the relative open-interval family nonnegatively.  No boundary
tightness hypothesis is needed: the conclusion concerns one fixed finite measure, whose own
boundary variation can be removed by an interior cutoff. -/
theorem zero_le_toSignedMeasure_of_restrict_openInterval_of_relativeTest_nonnegative
    {duration : ℝ} (hDuration : 0 < duration)
    (measure : VagueSignedMeasure ℝ)
    (hSupport : measure.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      measure.toSignedMeasure)
    (hNonnegative : ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ point, 0 ≤ test.1 point) →
        0 ≤ measure.continuousTestIntegral test.1) :
    0 ≤ measure.toSignedMeasure := by
  apply zero_le_toSignedMeasure_of_continuousTestIntegral_nonnegative
  intro test hTest
  by_contra hIntegral
  have hIntegralNegative : measure.continuousTestIntegral test < 0 :=
    lt_of_not_ge hIntegral
  obtain ⟨bound, hBound, hTestBound⟩ :=
    exists_positive_continuousTest_bound test
  let variationError : ℝ :=
    -measure.continuousTestIntegral test / (2 * bound)
  have hVariationError : 0 < variationError := by
    dsimp only [variationError]
    exact div_pos (neg_pos.mpr hIntegralNegative) (mul_pos (by norm_num) hBound)
  obtain ⟨margin, hMargin, hBoundaryVariation⟩ :=
    SignedMeasure.exists_positive_margin_totalVariation_real_boundaryLayer_lt
      measure.toSignedMeasure hDuration hVariationError hSupport
  let cutoff := finiteOpenIntervalCoreCutoff duration margin hMargin
  let relativeTest :=
    finiteOpenIntervalCoreCutoffMulTest (duration := duration) hMargin test
  have hCutoffRange (point : ℝ) : cutoff point ∈ Set.Icc (0 : ℝ) 1 :=
    finiteOpenIntervalCoreCutoff_mem_Icc hMargin point
  have hRelativeNonnegative : 0 ≤ measure.continuousTestIntegral relativeTest.1 := by
    apply hNonnegative relativeTest
    intro point
    change 0 ≤ test point * cutoff point
    exact mul_nonneg (hTest point) (hCutoffRange point).1
  have hDifferenceBound (point : ℝ) :
      |test point - (test * cutoff) point| ≤ bound := by
    have hOneSub : |1 - cutoff point| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hCutoffRange point).2)]
      linarith [(hCutoffRange point).1]
    change |test point - test point * cutoff point| ≤ bound
    rw [show test point - test point * cutoff point =
      test point * (1 - cutoff point) by ring, abs_mul]
    exact (mul_le_mul (hTestBound point) hOneSub (abs_nonneg _) hBound.le).trans
      (by rw [mul_one])
  have hOutside : Set.EqOn test (test * cutoff)
      (finiteOpenIntervalBoundaryLayer duration margin)ᶜ := by
    intro point hPoint
    have hCoreOpen : point ∈ Set.Ioo margin (duration - margin) := by
      simpa only [finiteOpenIntervalBoundaryLayer, compl_compl] using hPoint
    have hCutoffOne : cutoff point = 1 :=
      finiteOpenIntervalCoreCutoff_eq_one_of_mem_core hMargin
        ⟨hCoreOpen.1.le, hCoreOpen.2.le⟩
    simp [hCutoffOne]
  have hError :
      |measure.continuousTestIntegral test -
          measure.continuousTestIntegral relativeTest.1| <
        -measure.continuousTestIntegral test / 2 := by
    have hRaw :=
      abs_continuousTestIntegral_sub_le_mul_totalVariationOn
        measure test (test * cutoff)
        (measurableSet_finiteOpenIntervalBoundaryLayer duration margin)
        hDifferenceBound hOutside
    have hStrict :
        bound * measure.toSignedMeasure.totalVariation.real
            (finiteOpenIntervalBoundaryLayer duration margin) <
          bound * variationError :=
      mul_lt_mul_of_pos_left hBoundaryVariation hBound
    have hIdentity : bound * variationError =
        -measure.continuousTestIntegral test / 2 := by
      dsimp only [variationError]
      field_simp
    simpa only [relativeTest, finiteOpenIntervalCoreCutoffMulTest, cutoff,
      hIdentity] using hRaw.trans_lt hStrict
  have hAbsoluteLower :
      -measure.continuousTestIntegral test ≤
        |measure.continuousTestIntegral test -
          measure.continuousTestIntegral relativeTest.1| := by
    have hNegDifference := neg_le_abs
      (measure.continuousTestIntegral test -
        measure.continuousTestIntegral relativeTest.1)
    linarith
  linarith

/-- Relative open-interval convergence preserves nonnegativity for measures whose limiting
signed measure is supported in the physical interval.  Boundary mass may disappear, but it
cannot create a negative interior part. -/
theorem zero_le_toSignedMeasure_of_relativeTestTendsto_of_zero_le
    {Index : Type*} {indexFilter : Filter Index} [indexFilter.NeBot]
    {duration : ℝ} (hDuration : 0 < duration)
    (measures : Index → VagueSignedMeasure ℝ)
    (limit : VagueSignedMeasure ℝ)
    (hLimitSupport : limit.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      limit.toSignedMeasure)
    (hRelative : ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
      Filter.Tendsto
        (fun index => (measures index).continuousTestIntegral test.1)
        indexFilter (nhds (limit.continuousTestIntegral test.1)))
    (hNonnegative : ∀ index, 0 ≤ (measures index).toSignedMeasure) :
    0 ≤ limit.toSignedMeasure := by
  apply zero_le_toSignedMeasure_of_restrict_openInterval_of_relativeTest_nonnegative
    hDuration limit hLimitSupport
  intro test hTest
  apply ge_of_tendsto (hRelative test)
  exact Filter.Eventually.of_forall fun index => by
    rw [continuousTestIntegral_eq_integral_totalVariation_of_zero_le
      (measures index) (hNonnegative index) test.1]
    exact integral_nonneg hTest

/-- Two signed measures supported in the open physical interval are equal when all relative
open-interval test integrals agree. -/
theorem eq_of_restrict_openInterval_of_relativeTestIntegral_eq
    {duration : ℝ} (hDuration : 0 < duration)
    (first second : VagueSignedMeasure ℝ)
    (hFirstSupport : first.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      first.toSignedMeasure)
    (hSecondSupport : second.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      second.toSignedMeasure)
    (hIntegral : ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
      first.continuousTestIntegral test.1 =
        second.continuousTestIntegral test.1) :
    first = second := by
  change first.toSignedMeasure = second.toSignedMeasure
  apply le_antisymm
  · rw [← sub_nonneg]
    let difference := VagueSignedMeasure.add second
      (VagueSignedMeasure.realScalarMultiple (-1) first)
    have hDifference : difference.toSignedMeasure =
        second.toSignedMeasure - first.toSignedMeasure := by
      change second.toSignedMeasure + (-1 : ℝ) • first.toSignedMeasure =
        second.toSignedMeasure - first.toSignedMeasure
      rw [sub_eq_add_neg]
      exact congrArg (fun measure : SignedMeasure ℝ => second.toSignedMeasure + measure)
        (neg_one_smul ℝ first.toSignedMeasure)
    rw [← hDifference]
    apply zero_le_toSignedMeasure_of_restrict_openInterval_of_relativeTest_nonnegative
      hDuration difference
    · rw [hDifference]
      rw [VectorMeasure.restrict_sub, hSecondSupport, hFirstSupport]
    · intro test _hTest
      simp only [difference, continuousTestIntegral_add',
        continuousTestIntegral_realScalarMultiple, neg_mul, one_mul,
        hIntegral test, add_neg_cancel, le_refl]
  · rw [← sub_nonneg]
    let difference := VagueSignedMeasure.add first
      (VagueSignedMeasure.realScalarMultiple (-1) second)
    have hDifference : difference.toSignedMeasure =
        first.toSignedMeasure - second.toSignedMeasure := by
      change first.toSignedMeasure + (-1 : ℝ) • second.toSignedMeasure =
        first.toSignedMeasure - second.toSignedMeasure
      rw [sub_eq_add_neg]
      exact congrArg (fun measure : SignedMeasure ℝ => first.toSignedMeasure + measure)
        (neg_one_smul ℝ second.toSignedMeasure)
    rw [← hDifference]
    apply zero_le_toSignedMeasure_of_restrict_openInterval_of_relativeTest_nonnegative
      hDuration difference
    · rw [hDifference]
      rw [VectorMeasure.restrict_sub, hFirstSupport, hSecondSupport]
    · intro test _hTest
      simp only [difference, continuousTestIntegral_add',
        continuousTestIntegral_realScalarMultiple, neg_mul, one_mul,
        hIntegral test, add_neg_cancel, le_refl]

/-- Relative open-interval test convergence upgrades to genuine vague convergence when the
total variation of both the approximating measures and the limit is uniformly negligible in a
sufficiently thin boundary layer. -/
theorem tendsto_of_relative_continuousTestIntegral_of_boundaryVariation
    {Index : Type*} [SemilatticeSup Index] [Nonempty Index]
    {duration : ℝ} (measures : Index → VagueSignedMeasure ℝ)
    (limit : VagueSignedMeasure ℝ)
    (hRelative : ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
      Filter.Tendsto (fun index => (measures index).continuousTestIntegral test.1)
        Filter.atTop (nhds (limit.continuousTestIntegral test.1)))
    (hBoundaryVariation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ margin : ℝ, 0 < margin ∧
        (∀ index,
          (measures index).toSignedMeasure.totalVariation.real
            (finiteOpenIntervalBoundaryLayer duration margin) ≤ epsilon) ∧
        limit.toSignedMeasure.totalVariation.real
          (finiteOpenIntervalBoundaryLayer duration margin) ≤ epsilon) :
    Filter.Tendsto measures Filter.atTop (nhds limit) := by
  apply tendsto_iff_forall_continuousTestIntegral_tendsto.mpr
  intro test
  obtain ⟨bound, hBoundPositive, hTestBound⟩ :=
    exists_positive_continuousTest_bound test
  apply Metric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  have hBoundaryErrorPositive : 0 < epsilon / (4 * bound) := by positivity
  obtain ⟨margin, hMargin, hSequenceBoundary, hLimitBoundary⟩ :=
    hBoundaryVariation (epsilon / (4 * bound)) hBoundaryErrorPositive
  let cutoff := finiteOpenIntervalCoreCutoff duration margin hMargin
  let relativeTest :=
    finiteOpenIntervalCoreCutoffMulTest (duration := duration) hMargin test
  have hCutoffRange (point : ℝ) : cutoff point ∈ Set.Icc (0 : ℝ) 1 := by
    exact finiteOpenIntervalCoreCutoff_mem_Icc hMargin point
  have hDifferenceBound (point : ℝ) :
      |test point - (test * cutoff) point| ≤ bound := by
    have hOneSub : |1 - cutoff point| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hCutoffRange point).2)]
      linarith [(hCutoffRange point).1]
    change |test point - test point * cutoff point| ≤ bound
    rw [show test point - test point * cutoff point =
      test point * (1 - cutoff point) by ring, abs_mul]
    exact (mul_le_mul (hTestBound point) hOneSub (abs_nonneg _) hBoundPositive.le).trans
      (by rw [mul_one])
  have hOutside : Set.EqOn test (test * cutoff)
      (finiteOpenIntervalBoundaryLayer duration margin)ᶜ := by
    intro point hPoint
    have hCoreOpen : point ∈ Set.Ioo margin (duration - margin) := by
      simpa only [finiteOpenIntervalBoundaryLayer, compl_compl] using hPoint
    have hCutoffOne : cutoff point = 1 :=
      finiteOpenIntervalCoreCutoff_eq_one_of_mem_core hMargin
        ⟨hCoreOpen.1.le, hCoreOpen.2.le⟩
    simp [hCutoffOne]
  have hMiddleTendsto : Filter.Tendsto
      (fun index => (measures index).continuousTestIntegral (test * cutoff))
      Filter.atTop (nhds (limit.continuousTestIntegral (test * cutoff))) := by
    simpa only [relativeTest, finiteOpenIntervalCoreCutoffMulTest, cutoff] using
      hRelative relativeTest
  obtain ⟨minimumIndex, hMiddleEventually⟩ :=
    Metric.tendsto_atTop.mp hMiddleTendsto (epsilon / 2) (by positivity)
  refine ⟨minimumIndex, fun index hIndex => ?_⟩
  have hSequenceCutoff : dist
      ((measures index).continuousTestIntegral test)
      ((measures index).continuousTestIntegral (test * cutoff)) ≤ epsilon / 4 := by
    rw [Real.dist_eq]
    calc
      |(measures index).continuousTestIntegral test -
          (measures index).continuousTestIntegral (test * cutoff)| ≤
        bound * (measures index).toSignedMeasure.totalVariation.real
          (finiteOpenIntervalBoundaryLayer duration margin) :=
        abs_continuousTestIntegral_sub_le_mul_totalVariationOn
          (measures index) test (test * cutoff)
          (measurableSet_finiteOpenIntervalBoundaryLayer duration margin)
          hDifferenceBound hOutside
      _ ≤ bound * (epsilon / (4 * bound)) :=
        mul_le_mul_of_nonneg_left (hSequenceBoundary index) hBoundPositive.le
      _ = epsilon / 4 := by field_simp
  have hLimitCutoff : dist
      (limit.continuousTestIntegral (test * cutoff))
      (limit.continuousTestIntegral test) ≤ epsilon / 4 := by
    rw [Real.dist_eq, abs_sub_comm]
    calc
      |limit.continuousTestIntegral test -
          limit.continuousTestIntegral (test * cutoff)| ≤
        bound * limit.toSignedMeasure.totalVariation.real
          (finiteOpenIntervalBoundaryLayer duration margin) :=
        abs_continuousTestIntegral_sub_le_mul_totalVariationOn
          limit test (test * cutoff)
          (measurableSet_finiteOpenIntervalBoundaryLayer duration margin)
          hDifferenceBound hOutside
      _ ≤ bound * (epsilon / (4 * bound)) :=
        mul_le_mul_of_nonneg_left hLimitBoundary hBoundPositive.le
      _ = epsilon / 4 := by field_simp
  calc
    dist ((measures index).continuousTestIntegral test)
        (limit.continuousTestIntegral test) ≤
      dist ((measures index).continuousTestIntegral test)
          ((measures index).continuousTestIntegral (test * cutoff)) +
        dist ((measures index).continuousTestIntegral (test * cutoff))
          (limit.continuousTestIntegral (test * cutoff)) +
        dist (limit.continuousTestIntegral (test * cutoff))
          (limit.continuousTestIntegral test) :=
      dist_triangle4 _ _ _ _
    _ < epsilon / 4 + epsilon / 2 + epsilon / 4 :=
      add_lt_add_of_lt_of_le
        (add_lt_add_of_le_of_lt hSequenceCutoff
          (hMiddleEventually index hIndex)) hLimitCutoff
    _ = epsilon := by ring

end VagueSignedMeasure

end

end FiniteMarkovProcesses
