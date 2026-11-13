/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1Path
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Order.Monotone.Extension
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Cadlag representatives of finite-interval bounded-variation paths

This module constructs right-continuous representatives with left limits from genuine
finite-interval `L1` bounded-variation classes.  Boundary traces remain separate from equality in
the open-interval quotient.

The scalar construction is explicit.  A bounded-variation representative is decomposed on the
open interval into its signed variation and residual monotone parts.  Finite total variation
makes both parts bounded, so each admits a global monotone extension.  Taking right limits gives
Stieltjes functions; their difference is right-continuous, has left limits, and agrees with the
original representative away from a countable set.

## Main declarations

- `exists_global_monotone_decomposition_of_boundedVariationOn`: bounded global monotone
  decomposition of a scalar finite-interval BV function;
- `FiniteIntervalCadlagRepresentative`: a raw representative with BV, right continuity, and left
  limits;
- `FiniteIntervalL1Path.exists_cadlagRepresentative`: every essentially BV finite-coordinate
  `L1` path has such a representative.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

universe u

noncomputable section

namespace FiniteIntervalCadlagConstruction

/-- The signed variation from a fixed base point is bounded in absolute value by the complete
variation. -/
theorem abs_variationOnFromTo_le
    {representative : ℝ → ℝ} {interval : Set ℝ} {base point : ℝ}
    (hVariation : BoundedVariationOn representative interval) :
    |variationOnFromTo representative interval base point| ≤
      (eVariationOn representative interval).toReal := by
  rcases le_total base point with hOrder | hOrder
  · rw [variationOnFromTo.eq_of_le _ _ hOrder, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hVariation <|
      eVariationOn.mono representative inter_subset_left
  · rw [variationOnFromTo.eq_of_ge _ _ hOrder, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hVariation <|
      eVariationOn.mono representative inter_subset_left

/-- A scalar bounded-variation function on a nonempty set is, on that set, the difference of two
globally monotone functions.  The global extensions are licensed by the finite total-variation
bound, not by boundedness of the time interval alone. -/
theorem exists_global_monotone_decomposition_of_boundedVariationOn
    {representative : ℝ → ℝ} {interval : Set ℝ}
    (hInterval : interval.Nonempty)
    (hVariation : BoundedVariationOn representative interval) :
    ∃ positivePart negativePart : ℝ → ℝ,
      Monotone positivePart ∧ Monotone negativePart ∧
        EqOn representative (positivePart - negativePart) interval := by
  obtain ⟨base, hBase⟩ := hInterval
  let positiveVariation : ℝ → ℝ :=
    variationOnFromTo representative interval base
  let negativeVariation : ℝ → ℝ := positiveVariation - representative
  have hLocal := hVariation.locallyBoundedVariationOn
  have hPositiveMonotone : MonotoneOn positiveVariation interval := by
    exact variationOnFromTo.monotoneOn hLocal hBase
  have hNegativeMonotone : MonotoneOn negativeVariation interval := by
    exact variationOnFromTo.sub_self_monotoneOn hLocal hBase
  let totalVariation : ℝ := (eVariationOn representative interval).toReal
  have hPositiveBound : ∀ point ∈ interval,
      -totalVariation ≤ positiveVariation point ∧
        positiveVariation point ≤ totalVariation := by
    intro point hPoint
    have hAbsolute := abs_variationOnFromTo_le
      (base := base) (point := point) hVariation
    exact (abs_le.mp hAbsolute)
  have hRepresentativeBound : ∀ point ∈ interval,
      representative base - totalVariation ≤ representative point ∧
        representative point ≤ representative base + totalVariation := by
    intro point hPoint
    have hDistance : dist (representative point) (representative base) ≤ totalVariation := by
      rw [dist_edist]
      exact ENNReal.toReal_mono hVariation
        (eVariationOn.edist_le representative hPoint hBase)
    have hAbsolute := abs_sub_le_iff.mp hDistance
    constructor <;> linarith
  have hNegativeBound : ∀ point ∈ interval,
      -(representative base + 2 * totalVariation) ≤ negativeVariation point ∧
        negativeVariation point ≤ -representative base + 2 * totalVariation := by
    intro point hPoint
    have hPositive := hPositiveBound point hPoint
    have hRepresentative := hRepresentativeBound point hPoint
    constructor
    · change -(representative base + 2 * totalVariation) ≤
        positiveVariation point - representative point
      linarith
    · change positiveVariation point - representative point ≤
        -representative base + 2 * totalVariation
      linarith
  obtain ⟨positivePart, hPositiveGlobal, hPositiveAgreement⟩ :=
    hPositiveMonotone.exists_monotone_extension
      ⟨-totalVariation, by
        rintro value ⟨point, hPoint, rfl⟩
        exact (hPositiveBound point hPoint).1⟩
      ⟨totalVariation, by
        rintro value ⟨point, hPoint, rfl⟩
        exact (hPositiveBound point hPoint).2⟩
  obtain ⟨negativePart, hNegativeGlobal, hNegativeAgreement⟩ :=
    hNegativeMonotone.exists_monotone_extension
      ⟨-(representative base + 2 * totalVariation), by
        rintro value ⟨point, hPoint, rfl⟩
        exact (hNegativeBound point hPoint).1⟩
      ⟨-representative base + 2 * totalVariation, by
        rintro value ⟨point, hPoint, rfl⟩
        exact (hNegativeBound point hPoint).2⟩
  refine ⟨positivePart, negativePart, hPositiveGlobal, hNegativeGlobal, ?_⟩
  intro point hPoint
  rw [Pi.sub_apply, ← hPositiveAgreement hPoint, ← hNegativeAgreement hPoint]
  change representative point =
    positiveVariation point - (positiveVariation point - representative point)
  ring

/-- A scalar BV representative on a nonempty interval has a right-continuous modification with a
left limit at every real time.  The modification agrees with the original function almost
everywhere for every atomless measure; in particular it preserves an open-interval `L1` class. -/
theorem exists_rightContinuousWithLeftLimits_ae_eq
    {representative : ℝ → ℝ} {interval : Set ℝ}
    (hInterval : interval.Nonempty)
    (hVariation : BoundedVariationOn representative interval)
    (measure : Measure ℝ) [NullSingletonClass measure]
    (hMeasurableInterval : MeasurableSet interval) :
    ∃ modification : ℝ → ℝ,
      modification =ᵐ[measure.restrict interval] representative ∧
        (∀ time, ContinuousWithinAt modification (Ici time) time) ∧
          ∀ time, ∃ leftTrace : ℝ,
            Tendsto modification (𝓝[<] time) (𝓝 leftTrace) := by
  obtain ⟨positivePart, negativePart, hPositiveMonotone, hNegativeMonotone,
      hAgreement⟩ :=
    exists_global_monotone_decomposition_of_boundedVariationOn hInterval hVariation
  let positiveCadlag : StieltjesFunction ℝ := hPositiveMonotone.stieltjesFunction
  let negativeCadlag : StieltjesFunction ℝ := hNegativeMonotone.stieltjesFunction
  let modification : ℝ → ℝ := positiveCadlag - negativeCadlag
  let exceptional : Set ℝ :=
    {time | ¬ContinuousAt positivePart time} ∪
      {time | ¬ContinuousAt negativePart time}
  have hExceptional : exceptional.Countable :=
    hPositiveMonotone.countable_not_continuousAt.union
      hNegativeMonotone.countable_not_continuousAt
  have hEventually : modification =ᵐ[measure.restrict interval] representative := by
    filter_upwards [hExceptional.ae_notMem (measure.restrict interval),
      ae_restrict_mem hMeasurableInterval] with time hTime hMembership
    have hPositiveContinuous : ContinuousAt positivePart time := by
      exact Classical.not_not.mp fun hNot => hTime (Or.inl hNot)
    have hNegativeContinuous : ContinuousAt negativePart time := by
      exact Classical.not_not.mp fun hNot => hTime (Or.inr hNot)
    have hPositiveRight : positiveCadlag time = positivePart time := by
      change rightLim positivePart time = positivePart time
      exact hPositiveContinuous.continuousWithinAt.rightLim_eq
    have hNegativeRight : negativeCadlag time = negativePart time := by
      change rightLim negativePart time = negativePart time
      exact hNegativeContinuous.continuousWithinAt.rightLim_eq
    rw [show modification time = positiveCadlag time - negativeCadlag time by rfl,
      hPositiveRight, hNegativeRight, ← Pi.sub_apply, ← hAgreement hMembership]
  refine ⟨modification, hEventually, ?_, ?_⟩
  · intro time
    exact (positiveCadlag.right_continuous time).sub
      (negativeCadlag.right_continuous time)
  · intro time
    refine ⟨leftLim positiveCadlag time - leftLim negativeCadlag time, ?_⟩
    exact (positiveCadlag.mono.tendsto_leftLim time).sub
      (negativeCadlag.mono.tendsto_leftLim time)

end FiniteIntervalCadlagConstruction

/-- A selected right-continuous representative with left limits of one essentially BV
open-interval `L1` path.  Its boundary values are not part of quotient equality. -/
structure FiniteIntervalCadlagRepresentative
    {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}
    (path : FiniteIntervalL1Path Coordinate duration) where
  /-- The selected raw finite-coordinate path. -/
  representative : ℝ → FiniteCoordinateL1Value Coordinate
  /-- The raw path belongs to the supplied almost-everywhere class. -/
  represents : FiniteIntervalL1Path.Represents path representative
  /-- Right continuity on the physical half-open interval. -/
  rightContinuous : ∀ time ∈ Ico 0 duration,
    ContinuousWithinAt representative (Ici time) time
  /-- Existence of a finite left trace at every positive time through the terminal boundary. -/
  hasLeftLimit : ∀ time ∈ Ioc 0 duration,
    ∃ leftTrace : FiniteCoordinateL1Value Coordinate,
      Tendsto representative (𝓝[<] time) (𝓝 leftTrace)

namespace FiniteIntervalCadlagRepresentative

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}
  {path : FiniteIntervalL1Path Coordinate duration}

/-- The initial trace is evaluated separately at the right-continuous boundary representative;
it is not evaluation of the open-interval `L1` quotient. -/
def initialTrace (representative : FiniteIntervalCadlagRepresentative path) :
    FiniteCoordinateL1Value Coordinate :=
  representative.representative 0

/-- The selected terminal left trace.  It is recovered from the representative's left-limit
theorem and is not a value carried by open-interval quotient equality. -/
noncomputable def terminalTrace (representative : FiniteIntervalCadlagRepresentative path)
    (hDuration : 0 < duration) : FiniteCoordinateL1Value Coordinate :=
  Classical.choose (representative.hasLeftLimit duration ⟨hDuration, le_rfl⟩)

/-- The selected representative tends from the left to its recovered terminal trace. -/
theorem tendsto_terminalTrace
    (representative : FiniteIntervalCadlagRepresentative path)
    (hDuration : 0 < duration) :
    Tendsto representative.representative (𝓝[<] duration)
      (𝓝 (representative.terminalTrace hDuration)) :=
  Classical.choose_spec (representative.hasLeftLimit duration ⟨hDuration, le_rfl⟩)

/-- Right continuity recovers the initial trace independently of quotient evaluation. -/
theorem tendsto_initialTrace
    (representative : FiniteIntervalCadlagRepresentative path)
    (hDuration : 0 < duration) :
    Tendsto representative.representative (𝓝[Ici 0] 0)
      (𝓝 representative.initialTrace) :=
  (representative.rightContinuous 0 ⟨le_rfl, hDuration⟩).tendsto

/-- Two right-continuous functions that agree almost everywhere on the open physical interval
agree throughout its half-open closure. -/
theorem eqOn_Ico_of_rightContinuous_of_ae_eq
    {Value : Type*} [TopologicalSpace Value] [T2Space Value]
    {first second : ℝ → Value}
    (hFirstRight : ∀ time ∈ Ico 0 duration,
      ContinuousWithinAt first (Ici time) time)
    (hSecondRight : ∀ time ∈ Ico 0 duration,
      ContinuousWithinAt second (Ici time) time)
    (hEventually : first =ᵐ[finiteOpenIntervalVolume duration] second) :
    Set.EqOn first second (Ico 0 duration) := by
  intro time hTime
  apply tendsto_nhds_unique_of_frequently_eq
  · exact (hFirstRight time hTime).mono_left
      (nhdsWithin_mono time Ioi_subset_Ici_self)
  · exact (hSecondRight time hTime).mono_left
      (nhdsWithin_mono time Ioi_subset_Ici_self)
  · rw [(nhdsGT_basis time).frequently_iff]
    intro upper hUpper
    have hMin : time < min upper duration :=
      lt_min hUpper hTime.2
    have hAE : ∀ᵐ point ∂volume,
        point ∈ Ioo 0 duration → first point = second point :=
      (ae_restrict_iff' measurableSet_Ioo).mp hEventually
    have hDense : Dense {point |
        point ∉ Ioo 0 duration ∨ first point = second point} :=
      volume.dense_of_ae (hAE.mono fun point hPoint => by
        by_cases hInterval : point ∈ Ioo 0 duration
        · exact Or.inr (hPoint hInterval)
        · exact Or.inl hInterval)
    obtain ⟨point, hPointDense, hPointInterval⟩ :=
      hDense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hMin)
    refine ⟨point,
      ⟨hPointInterval.1, hPointInterval.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have hPointPhysical : point ∈ Ioo 0 duration :=
      ⟨hTime.1.trans_lt hPointInterval.1,
        hPointInterval.2.trans_le (min_le_right _ _)⟩
    rcases hPointDense with hOutside | hEquality
    · exact False.elim (hOutside hPointPhysical)
    · exact hEquality

/-- Two càdlàg representatives of the same open-interval `L1` path agree throughout the
physical half-open interval.  The quotient gives almost-everywhere equality on `(0,T)`; right
continuity and positivity of Lebesgue measure on every right neighborhood recover every point of
`[0,T)`, including the separately represented initial trace. -/
theorem eqOn_Ico_of_same_path
    (first second : FiniteIntervalCadlagRepresentative path) :
    Set.EqOn first.representative second.representative (Ico 0 duration) := by
  obtain ⟨hFirstMemLp, hFirstQuotient⟩ := first.represents
  obtain ⟨hSecondMemLp, hSecondQuotient⟩ := second.represents
  have hFirstEventually :
      first.representative =ᵐ[finiteOpenIntervalVolume duration] path :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq path first.representative
      hFirstMemLp).mp ⟨hFirstMemLp, hFirstQuotient⟩
  have hSecondEventually :
      second.representative =ᵐ[finiteOpenIntervalVolume duration] path :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq path second.representative
      hSecondMemLp).mp ⟨hSecondMemLp, hSecondQuotient⟩
  have hRepresentativeEventually :
      first.representative =ᵐ[finiteOpenIntervalVolume duration] second.representative :=
    hFirstEventually.trans hSecondEventually.symm
  exact eqOn_Ico_of_rightContinuous_of_ae_eq
    first.rightContinuous second.rightContinuous hRepresentativeEventually

/-- Càdlàg representatives indexed by propositionally equal open-interval `L1` paths agree on
the physical half-open interval. -/
theorem eqOn_Ico_of_paths_eq
    {firstPath secondPath : FiniteIntervalL1Path Coordinate duration}
    (first : FiniteIntervalCadlagRepresentative firstPath)
    (second : FiniteIntervalCadlagRepresentative secondPath)
    (hPath : firstPath = secondPath) :
    Set.EqOn first.representative second.representative (Ico 0 duration) := by
  subst secondPath
  exact eqOn_Ico_of_same_path first second

end FiniteIntervalCadlagRepresentative

namespace FiniteIntervalL1Path

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Every essentially bounded-variation finite-coordinate `L1` path on a positive open interval
has a right-continuous representative with finite left limits.  The construction is coordinatewise
but returns the native finite `l1` value, so it does not replace the quotient by a raw product
carrier. -/
theorem exists_cadlagRepresentative
    (path : FiniteIntervalL1Path Coordinate duration)
    (hDuration : 0 < duration)
    (hVariation : FiniteIntervalL1Path.HasBoundedVariation path) :
    Nonempty (FiniteIntervalCadlagRepresentative path) := by
  obtain ⟨representative, hRepresents, hRepresentativeVariation⟩ :=
    FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative path |>.mp hVariation
  have hCoordinateVariation (coordinate : Coordinate) :
      BoundedVariationOn (fun time => representative time coordinate) (Ioo 0 duration) := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).lipschitzWith
        |>.comp_boundedVariationOn hRepresentativeVariation
  have hCoordinateModification : ∀ coordinate : Coordinate,
      ∃ modification : ℝ → ℝ,
        modification =ᵐ[finiteOpenIntervalVolume duration]
            (fun time => representative time coordinate) ∧
          (∀ time, ContinuousWithinAt modification (Ici time) time) ∧
            ∀ time, ∃ leftTrace : ℝ,
              Tendsto modification (𝓝[<] time) (𝓝 leftTrace) := by
    intro coordinate
    simpa only [finiteOpenIntervalVolume] using
      (FiniteIntervalCadlagConstruction.exists_rightContinuousWithLeftLimits_ae_eq
        (representative := fun time => representative time coordinate)
        (interval := Ioo 0 duration) (measure := volume)
        (nonempty_Ioo.mpr hDuration) (hCoordinateVariation coordinate) measurableSet_Ioo)
  choose coordinateModification hCoordinateEventually hCoordinateRightContinuous
    hCoordinateLeftLimit using hCoordinateModification
  let coordinatePath : ℝ → Coordinate → ℝ :=
    fun time coordinate => coordinateModification coordinate time
  let coordinateEquivalence :
      FiniteCoordinateL1Value Coordinate ≃L[ℝ] (Coordinate → ℝ) :=
    PiLp.continuousLinearEquiv 1 ℝ fun _ : Coordinate => ℝ
  let modification : ℝ → FiniteCoordinateL1Value Coordinate :=
    fun time => coordinateEquivalence.symm (coordinatePath time)
  have hModificationEventually :
      modification =ᵐ[finiteOpenIntervalVolume duration] representative := by
    filter_upwards [ae_all_iff.mpr hCoordinateEventually] with time hTime
    apply coordinateEquivalence.injective
    change coordinateEquivalence (coordinateEquivalence.symm (coordinatePath time)) =
      coordinateEquivalence (representative time)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    funext coordinate
    change coordinateModification coordinate time = representative time coordinate
    exact hTime coordinate
  obtain ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩ := hRepresents
  have hModificationMemLp :
      MemLp modification 1 (finiteOpenIntervalVolume duration) :=
    hRepresentativeMemLp.ae_eq hModificationEventually.symm
  have hModificationRepresents : FiniteIntervalL1Path.Represents path modification := by
    refine ⟨hModificationMemLp, ?_⟩
    exact hModificationMemLp.toLp_congr hRepresentativeMemLp
      hModificationEventually |>.trans hRepresentativeQuotient
  refine ⟨⟨modification, hModificationRepresents, ?_, ?_⟩⟩
  · intro time _hTime
    apply coordinateEquivalence.symm.continuous.continuousAt.comp_continuousWithinAt
    exact continuousWithinAt_pi.mpr fun coordinate =>
      hCoordinateRightContinuous coordinate time
  · intro time _hTime
    choose coordinateTrace hCoordinateTrace using fun coordinate =>
      hCoordinateLeftLimit coordinate time
    refine ⟨coordinateEquivalence.symm coordinateTrace, ?_⟩
    apply coordinateEquivalence.symm.continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr hCoordinateTrace

end FiniteIntervalL1Path

end

end FiniteMarkovProcesses
