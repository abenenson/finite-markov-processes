/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVSourceSupportedUpperBound
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateSublevelCompactness
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpConservationInitialDensity
public import
FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpRandomEmpiricalTypeHybridBVCompactContainment
public import Mathlib.Topology.ShrinkingLemma

/-!
# Joint initial-density and hybrid-path upper bounds

This module combines the configuration-uniform finite-sample dynamic upper estimate with a random
empirical initial type on the exact probability-density/hybrid-path joint law.  The first result is
the rectangle estimate needed before compact finite-cover assembly: a measurable density event
retains its exact initial-law probability while a closed path event contributes the uniform
dynamic exponential cost.

No endpoint trace is asserted continuous.  The joint source remains concentrated on the closed
conservation-recovered initial-density graph.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped ENNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Split a strict complete-rate level into nonnegative real initial and dynamic thresholds.  A
zero threshold is licensed exactly as the boundary alternative; every positive-cost component is
approximated strictly from below by an `ofReal` threshold. -/
theorem exists_nonnegative_real_rate_split_of_ofReal_lt_add
    (level : ℝ) (hLevel : 0 ≤ level) {initialCost dynamicCost : ℝ≥0∞}
    (hCompleteCost : ENNReal.ofReal level < initialCost + dynamicCost) :
    ∃ initialLevel dynamicLevel : ℝ,
      0 ≤ initialLevel ∧ 0 ≤ dynamicLevel ∧ level < initialLevel + dynamicLevel ∧
        (initialLevel = 0 ∨ ENNReal.ofReal initialLevel < initialCost) ∧
        (dynamicLevel = 0 ∨ ENNReal.ofReal dynamicLevel < dynamicCost) := by
  rcases eq_or_ne initialCost 0 with rfl | hInitialCost
  · simp only [zero_add] at hCompleteCost
    obtain ⟨dynamicLevel, hDynamicLevelNonnegative, hLevelDynamic, hDynamicLevelCost⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hCompleteCost
    refine ⟨0, dynamicLevel, le_rfl, hDynamicLevelNonnegative, ?_, Or.inl rfl,
      Or.inr hDynamicLevelCost⟩
    simpa only [zero_add] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLevel).mp hLevelDynamic
  rcases eq_or_ne dynamicCost 0 with rfl | hDynamicCost
  · simp only [add_zero] at hCompleteCost
    obtain ⟨initialLevel, hInitialLevelNonnegative, hLevelInitial, hInitialLevelCost⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hCompleteCost
    refine ⟨initialLevel, 0, hInitialLevelNonnegative, le_rfl, ?_, Or.inr hInitialLevelCost,
      Or.inl rfl⟩
    simpa only [add_zero] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLevel).mp hLevelInitial
  obtain ⟨initialThreshold, hInitialThresholdCost, dynamicThreshold,
      hDynamicThresholdCost, hThresholdSum⟩ :=
    ENNReal.exists_lt_add_of_lt_add hCompleteCost hInitialCost hDynamicCost
  have hInitialThresholdFinite : initialThreshold ≠ ⊤ := hInitialThresholdCost.ne_top
  have hDynamicThresholdFinite : dynamicThreshold ≠ ⊤ := hDynamicThresholdCost.ne_top
  let initialLevel := initialThreshold.toReal
  let dynamicLevel := dynamicThreshold.toReal
  have hInitialLevelNonnegative : 0 ≤ initialLevel := ENNReal.toReal_nonneg
  have hDynamicLevelNonnegative : 0 ≤ dynamicLevel := ENNReal.toReal_nonneg
  have hInitialLevelCost : ENNReal.ofReal initialLevel < initialCost := by
    rw [ENNReal.ofReal_toReal hInitialThresholdFinite]
    exact hInitialThresholdCost
  have hDynamicLevelCost : ENNReal.ofReal dynamicLevel < dynamicCost := by
    rw [ENNReal.ofReal_toReal hDynamicThresholdFinite]
    exact hDynamicThresholdCost
  have hLevelSum : level < initialLevel + dynamicLevel := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLevel).mp
    rw [ENNReal.ofReal_add hInitialLevelNonnegative hDynamicLevelNonnegative,
      ENNReal.ofReal_toReal hInitialThresholdFinite,
      ENNReal.ofReal_toReal hDynamicThresholdFinite]
    exact hThresholdSum
  exact ⟨initialLevel, dynamicLevel, hInitialLevelNonnegative, hDynamicLevelNonnegative,
    hLevelSum, Or.inr hInitialLevelCost, Or.inr hDynamicLevelCost⟩

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- A compact joint target whose complete initial-plus-dynamic cost is strictly above a real level
admits a finite cover by closed density/path rectangles.  Each rectangle carries one explicit
nonnegative initial/dynamic split strictly above that level.  Compact-subtype shrinking is used
because the ambient hybrid-BV carrier is Hausdorff but need not be regular. -/
theorem exists_finite_closed_density_hybridBV_rectangular_rate_cover_of_compact
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (compactTarget : Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget) (hCompactTargetNonempty : compactTarget.Nonempty)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hCompleteCost : ∀ pair ∈ compactTarget,
      ENNReal.ofReal level <
        initialData.initialRate pair.1 +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2) :
    ∃ points : Finset compactTarget,
      points.Nonempty ∧
        ∃ densityTarget : points → Set (FiniteStateProbabilityDensity State),
          ∃ pathTarget : points → Set
              (RengerDirectionalFlowHybridBVPath State duration),
            ∃ initialLevel dynamicLevel : points → ℝ,
              (∀ point, IsClosed (densityTarget point)) ∧
              (∀ point, IsClosed (pathTarget point)) ∧
              compactTarget ⊆ ⋃ point, densityTarget point ×ˢ pathTarget point ∧
              (∀ point, 0 ≤ initialLevel point) ∧
              (∀ point, 0 ≤ dynamicLevel point) ∧
              (∀ point, level < initialLevel point + dynamicLevel point) ∧
              (∀ point, ∀ density ∈ densityTarget point,
                ENNReal.ofReal (initialLevel point) ≤ initialData.initialRate density) ∧
              (∀ point, dynamicLevel point = 0 ∨
                ∀ path ∈ pathTarget point,
                  ENNReal.ofReal (dynamicLevel point) <
                    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) := by
  choose initialLevel dynamicLevel hInitialLevel hDynamicLevel hLevelSplit hInitialSplit
    hDynamicSplit using fun point : compactTarget =>
      exists_nonnegative_real_rate_split_of_ofReal_lt_add level hLevel
        (hCompleteCost point.1 point.2)
  let densityOpen : compactTarget → Set (FiniteStateProbabilityDensity State) := fun point =>
    if initialLevel point = 0 then univ
    else initialData.initialRate ⁻¹' Ioi (ENNReal.ofReal (initialLevel point))
  let pathOpen : compactTarget → Set
      (RengerDirectionalFlowHybridBVPath State duration) := fun point =>
    if dynamicLevel point = 0 then univ
    else (rengerDirectionalFlowHybridBVDynamicRate generator hDuration) ⁻¹'
      Ioi (ENNReal.ofReal (dynamicLevel point))
  have hDensityOpen : ∀ point, IsOpen (densityOpen point) := by
    intro point
    by_cases hPoint : initialLevel point = 0
    · simp [densityOpen, hPoint]
    · simpa only [densityOpen, hPoint, ite_false] using
        initialData.initialRate_good.lowerSemicontinuous.isOpen_preimage
          (ENNReal.ofReal (initialLevel point))
  have hPathOpen : ∀ point, IsOpen (pathOpen point) := by
    intro point
    by_cases hPoint : dynamicLevel point = 0
    · simp [pathOpen, hPoint]
    · simpa only [pathOpen, hPoint, ite_false] using
        (lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration).isOpen_preimage (ENNReal.ofReal (dynamicLevel point))
  have hPointInDensityOpen : ∀ point, point.1.1 ∈ densityOpen point := by
    intro point
    by_cases hPoint : initialLevel point = 0
    · simp [densityOpen, hPoint]
    · simp only [densityOpen, hPoint, ite_false, mem_preimage, mem_Ioi]
      exact (hInitialSplit point).resolve_left hPoint
  have hPointInPathOpen : ∀ point, point.1.2 ∈ pathOpen point := by
    intro point
    by_cases hPoint : dynamicLevel point = 0
    · simp [pathOpen, hPoint]
    · simp only [pathOpen, hPoint, ite_false, mem_preimage, mem_Ioi]
      exact (hDynamicSplit point).resolve_left hPoint
  have hOpenCover : compactTarget ⊆ ⋃ point, densityOpen point ×ˢ pathOpen point := by
    intro pair hPair
    exact mem_iUnion.mpr
      ⟨⟨pair, hPair⟩, hPointInDensityOpen ⟨pair, hPair⟩,
        hPointInPathOpen ⟨pair, hPair⟩⟩
  rcases hCompactTarget.elim_finite_subcover
      (fun point => densityOpen point ×ˢ pathOpen point)
      (fun point => (hDensityOpen point).prod (hPathOpen point)) hOpenCover with
    ⟨points, hPointsCover⟩
  have hPointsNonempty : points.Nonempty := by
    by_contra hPoints
    rw [Finset.not_nonempty_iff_eq_empty.mp hPoints] at hPointsCover
    rcases hCompactTargetNonempty with ⟨pair, hPair⟩
    have hPairCovered := hPointsCover hPair
    simp at hPairCovered
  let : CompactSpace compactTarget := isCompact_iff_compactSpace.mp hCompactTarget
  let subtypeOpen : points → Set compactTarget := fun point =>
    Subtype.val ⁻¹' (densityOpen point.1 ×ˢ pathOpen point.1)
  have hSubtypeOpen : ∀ point, IsOpen (subtypeOpen point) := by
    intro point
    exact ((hDensityOpen point.1).prod (hPathOpen point.1)).preimage continuous_subtype_val
  have hSubtypeOpenCover : ⋃ point, subtypeOpen point = univ := by
    apply eq_univ_of_forall
    intro pair
    have hPair := hPointsCover pair.2
    simp only [mem_iUnion] at hPair ⊢
    rcases hPair with ⟨point, hPointInPoints, hPairOpen⟩
    exact ⟨⟨point, hPointInPoints⟩, hPairOpen⟩
  rcases exists_iUnion_eq_closed_subset hSubtypeOpen (fun pair => Set.toFinite _)
      hSubtypeOpenCover with
    ⟨closedPiece, hClosedPieceCover, hClosedPiece, hClosedPieceSubset⟩
  let densityTarget : points → Set (FiniteStateProbabilityDensity State) := fun point =>
    (fun pair : compactTarget => pair.1.1) '' closedPiece point
  let pathTarget : points → Set
      (RengerDirectionalFlowHybridBVPath State duration) := fun point =>
    (fun pair : compactTarget => pair.1.2) '' closedPiece point
  have hDensityTargetClosed : ∀ point, IsClosed (densityTarget point) := by
    intro point
    exact ((hClosedPiece point).isCompact.image
      (continuous_fst.comp continuous_subtype_val)).isClosed
  have hPathTargetClosed : ∀ point, IsClosed (pathTarget point) := by
    intro point
    exact ((hClosedPiece point).isCompact.image
      (continuous_snd.comp continuous_subtype_val)).isClosed
  have hClosedRectangleCover : compactTarget ⊆
      ⋃ point, densityTarget point ×ˢ pathTarget point := by
    intro pair hPair
    have hPairClosed : (⟨pair, hPair⟩ : compactTarget) ∈ ⋃ point, closedPiece point := by
      rw [hClosedPieceCover]
      exact mem_univ _
    simp only [mem_iUnion] at hPairClosed ⊢
    rcases hPairClosed with ⟨point, hPointClosed⟩
    refine ⟨point, ⟨?_, ?_⟩⟩
    · exact ⟨⟨pair, hPair⟩, hPointClosed, rfl⟩
    · exact ⟨⟨pair, hPair⟩, hPointClosed, rfl⟩
  have hInitialRate : ∀ point, ∀ density ∈ densityTarget point,
      ENNReal.ofReal (initialLevel point.1) ≤ initialData.initialRate density := by
    intro point density hDensity
    rcases hDensity with ⟨pair, hPairClosed, rfl⟩
    have hPairOpen := hClosedPieceSubset point hPairClosed
    change pair.1 ∈ densityOpen point.1 ×ˢ pathOpen point.1 at hPairOpen
    by_cases hPoint : initialLevel point.1 = 0
    · simp [hPoint]
    · have hDensityOpen := hPairOpen.1
      simp only [densityOpen, hPoint, ite_false, mem_preimage, mem_Ioi] at hDensityOpen
      exact hDensityOpen.le
  have hDynamicRate : ∀ point, dynamicLevel point.1 = 0 ∨
      ∀ path ∈ pathTarget point,
        ENNReal.ofReal (dynamicLevel point.1) <
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
    intro point
    by_cases hPoint : dynamicLevel point.1 = 0
    · exact Or.inl hPoint
    · refine Or.inr ?_
      intro path hPath
      rcases hPath with ⟨pair, hPairClosed, rfl⟩
      have hPairOpen := hClosedPieceSubset point hPairClosed
      change pair.1 ∈ densityOpen point.1 ×ˢ pathOpen point.1 at hPairOpen
      simpa only [pathOpen, hPoint, ite_false, mem_preimage, mem_Ioi] using hPairOpen.2
  exact ⟨points, hPointsNonempty, densityTarget, pathTarget,
    fun point => initialLevel point.1, fun point => dynamicLevel point.1,
    hDensityTargetClosed, hPathTargetClosed, hClosedRectangleCover,
    fun point => hInitialLevel point.1, fun point => hDynamicLevel point.1,
    fun point => hLevelSplit point.1, hInitialRate, hDynamicRate⟩

/-- A density rectangle retains the exact initial-law mass while its closed hybrid-path factor
pays the configuration-uniform dynamic exponential cost. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_prod_le_dynamicRate
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (densityTarget : Set (FiniteStateProbabilityDensity State))
    (hDensityTarget : MeasurableSet densityTarget)
    (closedPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedPathTarget : IsClosed closedPathTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ closedPathTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    ∃ prefactor : ℕ, ∀ (successorIndex : ℕ)
      (initialEmpiricalTypeLaw :
        Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
      [IsProbabilityMeasure initialEmpiricalTypeLaw],
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration.le
          (densityTarget ×ˢ closedPathTarget) ≤
        (((prefactor + 1 : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level))) *
        Measure.map
            (FiniteIIDPositiveEmpiricalType.probabilityDensity :
              FiniteIIDPositiveEmpiricalType State successorIndex →
                FiniteStateProbabilityDensity State)
            initialEmpiricalTypeLaw densityTarget := by
  classical
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVClosed_le_dynamicRate
      generator duration hDuration closedPathTarget hClosedPathTarget level hLevel hDynamicRate with
    ⟨prefactor, hConditional⟩
  refine ⟨prefactor, ?_⟩
  intro successorIndex initialEmpiricalTypeLaw _
  let pairMap := fun source :
      FiniteIIDPositiveEmpiricalType State successorIndex ×
        RengerDirectionalFlowHybridBVPath State duration =>
    (source.1.probabilityDensity, source.2)
  have hPairMap : Measurable pairMap :=
    measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
      successorIndex duration
  have hProductMeasurable : MeasurableSet (densityTarget ×ˢ closedPathTarget) :=
    hDensityTarget.prod hClosedPathTarget.measurableSet
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
  rw [Measure.map_apply hPairMap hProductMeasurable]
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
  rw [Measure.compProd_apply (hProductMeasurable.preimage hPairMap)]
  simp only [finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel_apply]
  rw [lintegral_fintype]
  let dynamicFactor : ℝ≥0∞ :=
    ((prefactor + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level))
  let densityTypes : Finset (FiniteIIDPositiveEmpiricalType State successorIndex) :=
    Finset.univ.filter fun empiricalType => empiricalType.probabilityDensity ∈ densityTarget
  have hInitialDensity :
      Measure.map
          (FiniteIIDPositiveEmpiricalType.probabilityDensity :
            FiniteIIDPositiveEmpiricalType State successorIndex →
              FiniteStateProbabilityDensity State)
          initialEmpiricalTypeLaw densityTarget =
        ∑ empiricalType ∈ densityTypes, initialEmpiricalTypeLaw {empiricalType} := by
    rw [Measure.map_apply (measurable_of_finite _) hDensityTarget]
    have hPreimage :
        FiniteIIDPositiveEmpiricalType.probabilityDensity ⁻¹' densityTarget =
          (densityTypes : Set (FiniteIIDPositiveEmpiricalType State successorIndex)) := by
      ext empiricalType
      simp [densityTypes]
    rw [hPreimage, ← sum_measure_singleton]
  have hSectionMem
      (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
      (hDensity : empiricalType.probabilityDensity ∈ densityTarget) :
      Prod.mk empiricalType ⁻¹'
          (pairMap ⁻¹' densityTarget ×ˢ closedPathTarget) = closedPathTarget := by
    ext path
    simp [pairMap, hDensity]
  have hSectionNotMem
      (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
      (hDensity : empiricalType.probabilityDensity ∉ densityTarget) :
      Prod.mk empiricalType ⁻¹'
          (pairMap ⁻¹' densityTarget ×ˢ closedPathTarget) = ∅ := by
    ext path
    simp [pairMap, hDensity]
  change
    (∑ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
              empiricalType generator duration hDuration.le
              (Prod.mk empiricalType ⁻¹'
                (pairMap ⁻¹' densityTarget ×ˢ closedPathTarget)) *
            initialEmpiricalTypeLaw {empiricalType}) ≤
      dynamicFactor *
        Measure.map
          (FiniteIIDPositiveEmpiricalType.probabilityDensity :
            FiniteIIDPositiveEmpiricalType State successorIndex →
              FiniteStateProbabilityDensity State)
          initialEmpiricalTypeLaw densityTarget
  calc
    _ ≤ ∑ empiricalType,
        if empiricalType.probabilityDensity ∈ densityTarget then
          dynamicFactor * initialEmpiricalTypeLaw {empiricalType}
        else 0 := by
      apply Finset.sum_le_sum
      intro empiricalType _hEmpiricalType
      by_cases hDensity : empiricalType.probabilityDensity ∈ densityTarget
      · rw [ite_eq_left hDensity, hSectionMem empiricalType hDensity]
        unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
        exact mul_le_mul_left
          (hConditional successorIndex empiricalType.representative)
          (initialEmpiricalTypeLaw {empiricalType})
      · rw [ite_eq_right hDensity, hSectionNotMem empiricalType hDensity, measure_empty, zero_mul]
    _ = ∑ empiricalType ∈ densityTypes,
        dynamicFactor * initialEmpiricalTypeLaw {empiricalType} := by
      rw [Finset.sum_filter]
    _ = dynamicFactor *
        ∑ empiricalType ∈ densityTypes, initialEmpiricalTypeLaw {empiricalType} := by
      rw [Finset.mul_sum]
    _ = dynamicFactor *
        Measure.map
          (FiniteIIDPositiveEmpiricalType.probabilityDensity :
            FiniteIIDPositiveEmpiricalType State successorIndex →
              FiniteStateProbabilityDensity State)
          initialEmpiricalTypeLaw densityTarget := by rw [hInitialDensity]

/-- Zero dynamic cost requires no strict rate premise: any density/path rectangle is bounded by
its exact initial-density marginal.  This is the boundary case used when the dynamic rate itself
vanishes and the complete cost is carried entirely by the initial law. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_prod_le_initialLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (densityTarget : Set (FiniteStateProbabilityDensity State))
    (hDensityTarget : MeasurableSet densityTarget)
    (pathTarget : Set (RengerDirectionalFlowHybridBVPath State duration)) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration
        (densityTarget ×ˢ pathTarget) ≤
      Measure.map
        (FiniteIIDPositiveEmpiricalType.probabilityDensity :
          FiniteIIDPositiveEmpiricalType State successorIndex →
            FiniteStateProbabilityDensity State)
        initialEmpiricalTypeLaw densityTarget := by
  let jointLaw := finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
    successorIndex initialEmpiricalTypeLaw generator duration hDuration
  have hSubset : densityTarget ×ˢ pathTarget ⊆ Prod.fst ⁻¹' densityTarget := by
    intro densityPath hDensityPath
    exact hDensityPath.1
  calc
    jointLaw (densityTarget ×ˢ pathTarget) ≤ jointLaw (Prod.fst ⁻¹' densityTarget) :=
      measure_mono hSubset
    _ = jointLaw.fst densityTarget := (Measure.fst_apply hDensityTarget).symm
    _ = Measure.map
        (FiniteIIDPositiveEmpiricalType.probabilityDensity :
          FiniteIIDPositiveEmpiricalType State successorIndex →
            FiniteStateProbabilityDensity State)
        initialEmpiricalTypeLaw densityTarget := by
      rw [fst_finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw]

/-- Particle-speed log probability for the exact random-density/hybrid-path joint law. -/
noncomputable def
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
    (initialEmpiricalTypeLaw : (successorIndex : ℕ) →
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) (successorIndex : ℕ)
    (event : Set (FiniteStateProbabilityDensity State ×
      RengerDirectionalFlowHybridBVPath State duration)) : EReal :=
  scaledEventLogProbability
    (fun index =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw index
        (initialEmpiricalTypeLaw index) generator duration hDuration)
    (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex event

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The scaled log probability of a nonempty finite union is bounded by the largest constituent
scaled log plus the explicit logarithmic cardinality overhead. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_biUnion_le
    {Index : Type*}
    (initialEmpiricalTypeLaw : ∀ successorIndex,
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ) (hDuration : 0 ≤ duration)
    (points : Finset Index) (hPoints : points.Nonempty)
    (target : Index → Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration))
    (successorIndex : ℕ) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialEmpiricalTypeLaw generator duration hDuration successorIndex
          (⋃ point ∈ points, target point) ≤
      ((Real.log points.card / (successorIndex + 1 : ℝ) : ℝ) : EReal) +
        points.sup' hPoints (fun point =>
          finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
            initialEmpiricalTypeLaw generator duration hDuration successorIndex
              (target point)) := by
  let law := finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
    (initialEmpiricalTypeLaw successorIndex) generator duration hDuration
  let maximumProbability := points.sup' hPoints fun point => law (target point)
  have hProbability : law (⋃ point ∈ points, target point) ≤
      (points.card : ℝ≥0∞) * maximumProbability := by
    calc
      law (⋃ point ∈ points, target point) ≤ ∑ point ∈ points, law (target point) :=
        measure_biUnion_finset_le points _
      _ ≤ ∑ _point ∈ points, maximumProbability := by
        apply Finset.sum_le_sum
        intro point hPoint
        exact Finset.le_sup' (fun selected => law (target selected)) hPoint
      _ = (points.card : ℝ≥0∞) * maximumProbability := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hCardPositive : 0 < (points.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hPoints
  have hLogMaximumProbability : ENNReal.log maximumProbability =
      points.sup' hPoints (fun point => ENNReal.log (law (target point))) := by
    exact Finset.apply_sup'_eq_sup'_comp hPoints ENNReal.log
      (fun left right => ENNReal.log_monotone.map_sup left right)
  have hScaledMaximumProbability : ENNReal.log maximumProbability /
        ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) =
      points.sup' hPoints (fun point =>
        ENNReal.log (law (target point)) /
          ((((successorIndex + 1 : ℕ) : ℝ) : EReal))) := by
    rw [hLogMaximumProbability]
    exact Finset.apply_sup'_eq_sup'_comp hPoints
      (fun value : EReal => value / ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
      (fun left right =>
        (EReal.monotone_div_right_of_nonneg (by positivity)).map_sup left right)
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
    scaledEventLogProbability
  simp only [preimage_id, finiteIIDPositiveSampleSpeed]
  change ENNReal.log (law (⋃ point ∈ points, target point)) /
      ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) ≤ _
  refine (EReal.monotone_div_right_of_nonneg (by positivity)
    (ENNReal.log_monotone hProbability)).trans_eq ?_
  rw [ENNReal.log_mul_add]
  rw [show (points.card : ℝ≥0∞) = ENNReal.ofReal (points.card : ℝ) by
    simp]
  rw [ENNReal.log_ofReal_of_pos hCardPositive]
  change (((Real.log points.card : ℝ) : EReal) + ENNReal.log maximumProbability) /
      ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) = _
  rw [EReal.add_div_of_nonneg_right (by positivity), hScaledMaximumProbability]
  congr 1
  rw [← EReal.coe_div]
  congr 1
  norm_cast

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Finite unions preserve a common particle-speed limsup bound: the fixed cardinality overhead
vanishes and the limsup of the pointwise finite maximum is the maximum of the constituent
limsups. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJoint_biUnion_limsup_le
    {Index : Type*}
    (initialEmpiricalTypeLaw : ∀ successorIndex,
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ) (hDuration : 0 ≤ duration)
    (points : Finset Index) (hPoints : points.Nonempty)
    (target : Index → Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration))
    (bound : ℝ)
    (hTarget : ∀ point ∈ points,
      limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialEmpiricalTypeLaw generator duration hDuration successorIndex (target point))
        atTop ≤ (bound : EReal)) :
    limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialEmpiricalTypeLaw generator duration hDuration successorIndex
          (⋃ point ∈ points, target point)) atTop ≤ (bound : EReal) := by
  let unionScaledLog : ℕ → EReal := fun successorIndex =>
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      initialEmpiricalTypeLaw generator duration hDuration successorIndex
        (⋃ point ∈ points, target point)
  let targetScaledLog : Index → ℕ → EReal := fun point successorIndex =>
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      initialEmpiricalTypeLaw generator duration hDuration successorIndex (target point)
  let cardinalityOverhead : ℕ → EReal := fun successorIndex =>
    ((Real.log points.card / (successorIndex + 1 : ℝ) : ℝ) : EReal)
  let maximumScaledLog : ℕ → EReal := fun successorIndex =>
    points.sup' hPoints (fun point => targetScaledLog point successorIndex)
  have hUpper : ∀ successorIndex,
      unionScaledLog successorIndex ≤
        cardinalityOverhead successorIndex + maximumScaledLog successorIndex := by
    intro successorIndex
    exact
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_biUnion_le
        initialEmpiricalTypeLaw generator duration hDuration points hPoints target successorIndex
  have hCardinalityOverheadTendsto :
      Tendsto cardinalityOverhead atTop (nhds (0 : EReal)) := by
    apply EReal.tendsto_coe.mpr
    have hCardinalityIdentity : points.card - 1 + 1 = points.card :=
      Nat.sub_add_cancel (Finset.card_pos.mpr hPoints)
    have hRealCardinalityIdentity : ((points.card - 1 : ℕ) : ℝ) + 1 = points.card := by
      exact_mod_cast hCardinalityIdentity
    simpa only [cardinalityOverhead, hRealCardinalityIdentity] using
      fixedFinitePrefactorLog_div_particleCount_tendsto_zero (points.card - 1)
  have hCardinalityOverheadLimsup :
      limsup cardinalityOverhead atTop = (0 : EReal) :=
    hCardinalityOverheadTendsto.limsup_eq
  have hMaximumLimsup : limsup maximumScaledLog atTop =
      points.sup' hPoints (fun point => limsup (targetScaledLog point) atTop) := by
    exact limsup_finset_sup' hPoints
  have hMaximumUpper : limsup maximumScaledLog atTop ≤ (bound : EReal) := by
    rw [hMaximumLimsup]
    apply Finset.sup'_le hPoints
    intro point hPoint
    exact hTarget point hPoint
  have hMaximumLimsupNeTop : limsup maximumScaledLog atTop ≠ ⊤ := by
    exact ne_of_lt (hMaximumUpper.trans_lt (EReal.coe_lt_top bound))
  have hCardinalityOverheadLimsupNeTop :
      limsup cardinalityOverhead atTop ≠ ⊤ := by
    rw [hCardinalityOverheadLimsup]
    exact EReal.coe_ne_top 0
  calc
    limsup unionScaledLog atTop ≤
        limsup (cardinalityOverhead + maximumScaledLog) atTop :=
      limsup_le_limsup (Eventually.of_forall hUpper)
    _ ≤ limsup cardinalityOverhead atTop + limsup maximumScaledLog atTop :=
      EReal.limsup_add_le (.inr hMaximumLimsupNeTop)
        (.inl hCardinalityOverheadLimsupNeTop)
    _ = limsup maximumScaledLog atTop := by
      rw [hCardinalityOverheadLimsup, zero_add]
    _ ≤ (bound : EReal) := hMaximumUpper

/-- The zero-dynamic-cost rectangle bound in particle-speed logarithmic form. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_prod_le_initialLaw
    (initialEmpiricalTypeLaw : (successorIndex : ℕ) →
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (initialEmpiricalTypeLawProbability : ∀ successorIndex,
      IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (densityTarget : Set (FiniteStateProbabilityDensity State))
    (hDensityTarget : MeasurableSet densityTarget)
    (pathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (successorIndex : ℕ) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialEmpiricalTypeLaw generator duration hDuration successorIndex
        (densityTarget ×ˢ pathTarget) ≤
      scaledEventLogProbability
        (fun index => Measure.map
          (FiniteIIDPositiveEmpiricalType.probabilityDensity :
            FiniteIIDPositiveEmpiricalType State index → FiniteStateProbabilityDensity State)
          (initialEmpiricalTypeLaw index))
        (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex densityTarget := by
  let : IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex) :=
    initialEmpiricalTypeLawProbability successorIndex
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
    scaledEventLogProbability
  simp only [preimage_id]
  exact EReal.monotone_div_right_of_nonneg
    (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
    (ENNReal.log_monotone
      (finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_prod_le_initialLaw
        successorIndex (initialEmpiricalTypeLaw successorIndex) generator duration hDuration
          densityTarget hDensityTarget pathTarget))

/-- The rectangle estimate in particle-speed logarithmic form.  Its only finite-sample residual is
the fixed dynamic-cover prefactor; the initial-density event remains its exact scaled log
probability, so its independent LDP cost can be added at the limsup stage. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_prod_le
    (initialEmpiricalTypeLaw : (successorIndex : ℕ) →
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (initialEmpiricalTypeLawProbability : ∀ successorIndex,
      IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (densityTarget : Set (FiniteStateProbabilityDensity State))
    (hDensityTarget : MeasurableSet densityTarget)
    (closedPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedPathTarget : IsClosed closedPathTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ closedPathTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    ∃ prefactor : ℕ, ∀ successorIndex,
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          (densityTarget ×ˢ closedPathTarget) ≤
        ((Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) :
            EReal) +
          scaledEventLogProbability
            (fun index => Measure.map
              (FiniteIIDPositiveEmpiricalType.probabilityDensity :
                FiniteIIDPositiveEmpiricalType State index →
                  FiniteStateProbabilityDensity State)
              (initialEmpiricalTypeLaw index))
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex densityTarget := by
  rcases finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_prod_le_dynamicRate
      generator duration hDuration densityTarget hDensityTarget closedPathTarget hClosedPathTarget
        level hLevel hDynamicRate with
    ⟨prefactor, hProbability⟩
  refine ⟨prefactor, ?_⟩
  intro successorIndex
  let : IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex) :=
    initialEmpiricalTypeLawProbability successorIndex
  let initialDensityProbability : ℝ≥0∞ :=
    Measure.map
      (FiniteIIDPositiveEmpiricalType.probabilityDensity :
        FiniteIIDPositiveEmpiricalType State successorIndex →
          FiniteStateProbabilityDensity State)
      (initialEmpiricalTypeLaw successorIndex) densityTarget
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
    scaledEventLogProbability finiteIIDPositiveSampleSpeed
  simp only [preimage_id]
  refine (EReal.monotone_div_right_of_nonneg
    (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
    (ENNReal.log_monotone
      (hProbability successorIndex (initialEmpiricalTypeLaw successorIndex)))).trans_eq ?_
  have hPrefactorPositive : 0 < (prefactor + 1 : ℝ) := by positivity
  rw [ENNReal.log_mul_add]
  rw [show (((prefactor + 1 : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal (prefactor + 1 : ℝ) by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ENNReal.ofReal_natCast (prefactor + 1)).symm]
  rw [ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos hPrefactorPositive,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  change
    ((((Real.log (prefactor + 1 : ℝ) +
          -(successorIndex + 1 : ℝ) * level : ℝ) : EReal) +
        ENNReal.log initialDensityProbability) /
          ((((successorIndex + 1 : ℕ) : ℝ) : EReal))) = _
  rw [EReal.add_div_of_nonneg_right (by positivity)]
  congr 1
  · rw [← EReal.coe_div]
    congr 1
    field_simp
    push_cast
    ring

/-- Theorem 4.2 rectangle upper bound: a closed initial-density factor contributes its supplied
initial LDP cost, while a closed path factor strictly above a nonnegative dynamic level contributes
that dynamic cost.  This is the first asymptotic theorem in which the two costs are added on one
exact joint law. -/
theorem rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedDensityTarget : Set (FiniteStateProbabilityDensity State))
    (hClosedDensityTarget : IsClosed closedDensityTarget)
    (closedPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedPathTarget : IsClosed closedPathTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ closedPathTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (closedDensityTarget ×ˢ closedPathTarget)) atTop ≤
      ((-level : ℝ) : EReal) +
        -(⨅ density ∈ closedDensityTarget, (initialData.initialRate density : EReal)) := by
  rcases
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_prod_le
        initialData.initialEmpiricalTypeLaw initialData.initialEmpiricalTypeLaw_probability
          generator duration hDuration closedDensityTarget hClosedDensityTarget.measurableSet
            closedPathTarget hClosedPathTarget level hLevel hDynamicRate with
    ⟨prefactor, hPointwise⟩
  let jointScaledLog : ℕ → EReal := fun successorIndex =>
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
        (closedDensityTarget ×ˢ closedPathTarget)
  let initialScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability initialData.initialLaw (fun _ => id)
      finiteIIDPositiveSampleSpeed successorIndex closedDensityTarget
  let dynamicOverhead : ℕ → EReal := fun successorIndex =>
    ((Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) : EReal)
  have hUpper : ∀ successorIndex,
      jointScaledLog successorIndex ≤
        dynamicOverhead successorIndex + initialScaledLog successorIndex := by
    intro successorIndex
    dsimp only [jointScaledLog, dynamicOverhead, initialScaledLog]
    unfold scaledEventLogProbability
    rw [initialData.initialLaw_eq_map_probabilityDensity successorIndex]
    exact hPointwise successorIndex
  have hDynamicOverheadTendsto :
      Tendsto dynamicOverhead atTop (nhds (((-level : ℝ) : EReal))) := by
    apply EReal.tendsto_coe.mpr
    simpa [dynamicOverhead] using
      (fixedFinitePrefactorLog_div_particleCount_tendsto_zero prefactor).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => level) atTop (nhds level))
  have hDynamicOverheadLimsup :
      limsup dynamicOverhead atTop = (((-level : ℝ) : EReal)) :=
    hDynamicOverheadTendsto.limsup_eq
  have hInitialUpper : limsup initialScaledLog atTop ≤
      -(⨅ density ∈ closedDensityTarget, (initialData.initialRate density : EReal)) := by
    exact initialData.initialUpperBound closedDensityTarget hClosedDensityTarget
  have hInitialRateInfimumNonnegative :
      (0 : EReal) ≤
        ⨅ density ∈ closedDensityTarget, (initialData.initialRate density : EReal) := by
    apply le_iInf
    intro density
    apply le_iInf
    intro _hDensity
    exact EReal.coe_ennreal_nonneg _
  have hNegativeInitialRateInfimumNonpositive :
      -(⨅ density ∈ closedDensityTarget,
        (initialData.initialRate density : EReal)) ≤ (0 : EReal) :=
    by simpa only [neg_zero] using
      (EReal.neg_le_neg_iff.mpr hInitialRateInfimumNonnegative)
  have hInitialLimsupNeTop : limsup initialScaledLog atTop ≠ ⊤ := by
    apply ne_of_lt
    exact hInitialUpper.trans_lt
      (hNegativeInitialRateInfimumNonpositive.trans_lt (EReal.coe_lt_top 0))
  have hDynamicLimsupNeTop : limsup dynamicOverhead atTop ≠ ⊤ := by
    rw [hDynamicOverheadLimsup]
    exact EReal.coe_ne_top _
  calc
    limsup jointScaledLog atTop ≤
        limsup (dynamicOverhead + initialScaledLog) atTop :=
      limsup_le_limsup (Eventually.of_forall hUpper)
    _ ≤ limsup dynamicOverhead atTop + limsup initialScaledLog atTop :=
      EReal.limsup_add_le (.inr hInitialLimsupNeTop) (.inl hDynamicLimsupNeTop)
    _ = (((-level : ℝ) : EReal)) + limsup initialScaledLog atTop := by
      rw [hDynamicOverheadLimsup]
    _ ≤ (((-level : ℝ) : EReal)) +
        -(⨅ density ∈ closedDensityTarget,
          (initialData.initialRate density : EReal)) :=
      by simpa only [add_comm] using
        add_le_add_left hInitialUpper (((-level : ℝ) : EReal))

/-- Boundary rectangle limsup when no positive dynamic rate is available: the exact initial LDP
cost remains valid for an arbitrary path factor. -/
theorem rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le_initialRate
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (closedDensityTarget : Set (FiniteStateProbabilityDensity State))
    (hClosedDensityTarget : IsClosed closedDensityTarget)
    (pathTarget : Set (RengerDirectionalFlowHybridBVPath State duration)) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration successorIndex
            (closedDensityTarget ×ˢ pathTarget)) atTop ≤
      -(⨅ density ∈ closedDensityTarget,
        (initialData.initialRate density : EReal)) := by
  let jointScaledLog : ℕ → EReal := fun successorIndex =>
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      initialData.initialEmpiricalTypeLaw generator duration hDuration successorIndex
        (closedDensityTarget ×ˢ pathTarget)
  let initialScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability initialData.initialLaw (fun _ => id)
      finiteIIDPositiveSampleSpeed successorIndex closedDensityTarget
  have hUpper : ∀ successorIndex,
      jointScaledLog successorIndex ≤ initialScaledLog successorIndex := by
    intro successorIndex
    dsimp only [jointScaledLog, initialScaledLog]
    unfold scaledEventLogProbability
    rw [initialData.initialLaw_eq_map_probabilityDensity successorIndex]
    exact
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability_prod_le_initialLaw
        initialData.initialEmpiricalTypeLaw initialData.initialEmpiricalTypeLaw_probability
          generator duration hDuration closedDensityTarget hClosedDensityTarget.measurableSet
            pathTarget successorIndex
  exact (limsup_le_limsup (Eventually.of_forall hUpper)).trans
    (initialData.initialUpperBound closedDensityTarget hClosedDensityTarget)

/-- Closed-rectangle upper bound at an explicit nonnegative initial/dynamic rate split.  The
dynamic-zero branch uses only the exact initial marginal; every positive dynamic threshold uses
the source-supported exponential estimate. -/
theorem rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le_neg_add
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedDensityTarget : Set (FiniteStateProbabilityDensity State))
    (hClosedDensityTarget : IsClosed closedDensityTarget)
    (closedPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedPathTarget : IsClosed closedPathTarget)
    (initialLevel dynamicLevel : ℝ)
    (hInitialLevel : 0 ≤ initialLevel) (hDynamicLevel : 0 ≤ dynamicLevel)
    (hInitialRate : ∀ density ∈ closedDensityTarget,
      ENNReal.ofReal initialLevel ≤ initialData.initialRate density)
    (hDynamicRate : dynamicLevel = 0 ∨ ∀ path ∈ closedPathTarget,
      ENNReal.ofReal dynamicLevel <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (closedDensityTarget ×ˢ closedPathTarget)) atTop ≤
      ((-(initialLevel + dynamicLevel) : ℝ) : EReal) := by
  have hInitialInfimum :
      ((ENNReal.ofReal initialLevel : ENNReal) : EReal) ≤
        ⨅ density ∈ closedDensityTarget,
          (initialData.initialRate density : EReal) := by
    apply le_iInf
    intro density
    apply le_iInf
    intro hDensity
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (hInitialRate density hDensity)
  have hNegativeInitialInfimum :
      -(⨅ density ∈ closedDensityTarget,
          (initialData.initialRate density : EReal)) ≤
        ((-initialLevel : ℝ) : EReal) := by
    calc
      -(⨅ density ∈ closedDensityTarget,
          (initialData.initialRate density : EReal)) ≤
          -((ENNReal.ofReal initialLevel : ENNReal) : EReal) :=
        EReal.neg_le_neg_iff.mpr hInitialInfimum
      _ = ((-initialLevel : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left hInitialLevel, EReal.coe_neg]
  rcases hDynamicRate with rfl | hPositiveDynamicRate
  · simpa only [add_zero] using
      (rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le_initialRate
        initialData generator duration hDuration.le closedDensityTarget hClosedDensityTarget
          closedPathTarget).trans hNegativeInitialInfimum
  · calc
      limsup (fun successorIndex =>
          finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
            initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
              (closedDensityTarget ×ˢ closedPathTarget)) atTop ≤
          ((-dynamicLevel : ℝ) : EReal) +
            -(⨅ density ∈ closedDensityTarget,
              (initialData.initialRate density : EReal)) :=
        rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le
          initialData generator duration hDuration closedDensityTarget hClosedDensityTarget
            closedPathTarget hClosedPathTarget dynamicLevel hDynamicLevel hPositiveDynamicRate
      _ ≤ ((-dynamicLevel : ℝ) : EReal) + ((-initialLevel : ℝ) : EReal) := by
        simpa only [add_comm] using
          add_le_add_left hNegativeInitialInfimum ((-dynamicLevel : ℝ) : EReal)
      _ = ((-(initialLevel + dynamicLevel) : ℝ) : EReal) := by
        norm_cast
        ring

/-- Compact joint upper bound for the exact random-density/hybrid-path law.  The proof composes
compact-subtype shrinking, closed-rectangle initial/dynamic estimates, and the finite-union
principle; it assumes no ambient regularity and no continuity of the raw initial trace. -/
theorem rengerTheoremFourTwoDensityHybridBVJointCompactLimsup_le_neg_level
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (compactTarget : Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hCompleteCost : ∀ pair ∈ compactTarget,
      ENNReal.ofReal level <
        initialData.initialRate pair.1 +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2) :
    limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          compactTarget) atTop ≤ ((-level : ℝ) : EReal) := by
  rcases compactTarget.eq_empty_or_nonempty with rfl | hCompactTargetNonempty
  · have hScaledEmpty : (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex ∅) =
        (fun _ => (⊥ : EReal)) := by
      funext successorIndex
      unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        scaledEventLogProbability
      rw [preimage_id, measure_empty, ENNReal.log_zero]
      exact EReal.bot_div_of_pos_ne_top
        (EReal.coe_pos.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex))
        (EReal.coe_ne_top _)
    rw [hScaledEmpty, limsup_const]
    exact bot_le
  rcases exists_finite_closed_density_hybridBV_rectangular_rate_cover_of_compact
      initialData generator duration hDuration compactTarget hCompactTarget
        hCompactTargetNonempty level hLevel hCompleteCost with
    ⟨points, hPoints, densityTarget, pathTarget, initialLevel, dynamicLevel,
      hDensityTargetClosed, hPathTargetClosed, hRectangleCover,
      hInitialLevel, hDynamicLevel, hLevelSplit, hInitialRate, hDynamicRate⟩
  let rectangleTarget : points → Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration) := fun point =>
    densityTarget point ×ˢ pathTarget point
  have hRectangleLimsup : ∀ point : points,
      limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (rectangleTarget point)) atTop ≤ ((-level : ℝ) : EReal) := by
    intro point
    calc
      limsup (fun successorIndex =>
          finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
            initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
              (rectangleTarget point)) atTop ≤
          ((-(initialLevel point + dynamicLevel point) : ℝ) : EReal) :=
        rengerTheoremFourTwoDensityHybridBVJointClosedRectangleLimsup_le_neg_add
          initialData generator duration hDuration (densityTarget point)
            (hDensityTargetClosed point) (pathTarget point) (hPathTargetClosed point)
            (initialLevel point) (dynamicLevel point) (hInitialLevel point)
            (hDynamicLevel point) (hInitialRate point) (hDynamicRate point)
      _ ≤ ((-level : ℝ) : EReal) := by
        norm_cast
        exact neg_le_neg (hLevelSplit point).le
  have hIndexNonempty : (Finset.univ : Finset points).Nonempty := by
    rcases hPoints with ⟨point, hPoint⟩
    exact ⟨⟨point, hPoint⟩, Finset.mem_univ _⟩
  have hUnionLimsup : limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          (⋃ point : points, rectangleTarget point)) atTop ≤ ((-level : ℝ) : EReal) := by
    simpa only [Finset.mem_univ, iUnion_true] using
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJoint_biUnion_limsup_le
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le
          (Finset.univ : Finset points) hIndexNonempty rectangleTarget (-level)
          (fun point _hPoint => hRectangleLimsup point)
  have hScaledMonotone : ∀ successorIndex,
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            compactTarget ≤
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (⋃ point : points, rectangleTarget point) := by
    intro successorIndex
    unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      scaledEventLogProbability
    simp only [preimage_id]
    exact EReal.monotone_div_right_of_nonneg
      (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
      (ENNReal.log_monotone (measure_mono hRectangleCover))
  exact (limsup_le_limsup (Eventually.of_forall hScaledMonotone)).trans hUnionLimsup

end

end FiniteMarkovProcesses.InformationTheory
