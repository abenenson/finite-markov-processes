/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalStepL1Path
import Mathlib.Order.Interval.Set.Union

/-!
# Finite-sample step paths on a bounded physical interval

This module turns a finite sequence of vector samples into the corresponding right-continuous
step path in the strong `L1` carrier.  The construction is continuous in the samples, so bounded
sample arrays have compact image.  These compact finite-dimensional images are the approximating
families used in bounded-variation compactness.

## Main declarations

- `finiteIntervalSampleIncrement`: initial value followed by successive sample increments;
- `finiteIntervalSampleStepL1Path`: the induced right-continuous strong-`L1` step path;
- `isCompact_finiteIntervalSampleStepL1Path_image_closedBall`: compactness of every bounded
  fixed-time sample family.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] [DecidableEq Coordinate]

/-- Convert a finite value sample into its initial value followed by successive increments. -/
def finiteIntervalSampleIncrement
    (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate) :
    Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate :=
  Fin.cases (value 0) fun index => value index.succ - value index.castSucc

private def finiteIntervalSampleValueAtNat
    (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
    (index : ℕ) : FiniteCoordinateL1Value Coordinate :=
  if hIndex : index < finalSampleIndex + 1 then value ⟨index, hIndex⟩ else 0

omit [Fintype Coordinate] [DecidableEq Coordinate] in
private theorem finiteIntervalSampleIncrement_apply_mk
    (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
    (index : ℕ) (hIndex : index < finalSampleIndex + 1) :
    finiteIntervalSampleIncrement finalSampleIndex value ⟨index, hIndex⟩ =
      if index = 0 then finiteIntervalSampleValueAtNat finalSampleIndex value 0
      else finiteIntervalSampleValueAtNat finalSampleIndex value index -
        finiteIntervalSampleValueAtNat finalSampleIndex value (index - 1) := by
  cases index with
  | zero => simp [finiteIntervalSampleIncrement, finiteIntervalSampleValueAtNat]
  | succ previous =>
      have hPrevious : previous < finalSampleIndex + 1 := by omega
      simp [finiteIntervalSampleIncrement, finiteIntervalSampleValueAtNat, hIndex, hPrevious]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
private theorem sum_finiteIntervalSampleIncrement_to
    (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
    (sampleIndex : ℕ) (hSampleIndex : sampleIndex < finalSampleIndex + 1) :
    (∑ index ∈ Finset.range (sampleIndex + 1),
      if index = 0 then finiteIntervalSampleValueAtNat finalSampleIndex value 0
      else finiteIntervalSampleValueAtNat finalSampleIndex value index -
        finiteIntervalSampleValueAtNat finalSampleIndex value (index - 1)) =
      value ⟨sampleIndex, hSampleIndex⟩ := by
  rw [← Finset.eq_sum_range_sub'
    (finiteIntervalSampleValueAtNat finalSampleIndex value) sampleIndex]
  simp [finiteIntervalSampleValueAtNat, hSampleIndex]

omit [Fintype Coordinate] [DecidableEq Coordinate] in
/-- The initial value and all successive increments through one sample telescope to that sample. -/
theorem sum_finiteIntervalSampleIncrement_le
    (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    (∑ index, if index.val ≤ sampleIndex.val then
      finiteIntervalSampleIncrement finalSampleIndex value index else 0) = value sampleIndex := by
  let activeIncrement : ℕ → FiniteCoordinateL1Value Coordinate := fun index =>
    if hIndex : index < finalSampleIndex + 1 then
      if index ≤ sampleIndex.val then
        finiteIntervalSampleIncrement finalSampleIndex value ⟨index, hIndex⟩ else 0
    else 0
  calc
    (∑ index, if index.val ≤ sampleIndex.val then
        finiteIntervalSampleIncrement finalSampleIndex value index else 0) =
        ∑ index : Fin (finalSampleIndex + 1), activeIncrement index.val := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      simp only [activeIncrement, dite_eq_left index.isLt]
    _ = ∑ index ∈ Finset.range (finalSampleIndex + 1), activeIncrement index :=
      Fin.sum_univ_eq_sum_range activeIncrement (finalSampleIndex + 1)
    _ = ∑ index ∈ Finset.range (sampleIndex.val + 1), activeIncrement index := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.succ_le_iff.mpr sampleIndex.isLt)
      · intro index hIndex hOutside
        have hIndexBound : index < finalSampleIndex + 1 := Finset.mem_range.mp hIndex
        have hIndexAfterSample : sampleIndex.val < index := by
          simp only [Finset.mem_range, not_lt] at hOutside
          omega
        simp [activeIncrement, Nat.not_le.mpr hIndexAfterSample]
    _ = ∑ index ∈ Finset.range (sampleIndex.val + 1),
          (if index = 0 then finiteIntervalSampleValueAtNat finalSampleIndex value 0
          else finiteIntervalSampleValueAtNat finalSampleIndex value index -
            finiteIntervalSampleValueAtNat finalSampleIndex value (index - 1)) := by
      apply Finset.sum_congr rfl
      intro index hIndex
      have hIndexBeforeSample : index ≤ sampleIndex.val :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hIndex)
      have hIndexBound : index < finalSampleIndex + 1 :=
        lt_of_le_of_lt hIndexBeforeSample sampleIndex.isLt
      simp only [activeIncrement, dite_eq_left hIndexBound, ite_eq_left hIndexBeforeSample]
      exact finiteIntervalSampleIncrement_apply_mk finalSampleIndex value index hIndexBound
    _ = value ⟨sampleIndex.val, sampleIndex.isLt⟩ :=
      sum_finiteIntervalSampleIncrement_to
        finalSampleIndex value sampleIndex.val sampleIndex.isLt
    _ = value sampleIndex := by congr

/-- The right-continuous strong-`L1` step path determined by finitely many event-time samples. -/
def finiteIntervalSampleStepL1Path
    (duration : ℝ) (finalSampleIndex : ℕ)
    (eventTime : Fin (finalSampleIndex + 1) → ℝ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path Coordinate duration :=
  finiteCoordinateVectorEventStepL1PathSum duration eventTime
    (finiteIntervalSampleIncrement finalSampleIndex value)

/-- With event times fixed, the finite sampled step path depends continuously on all sample
values. -/
theorem continuous_finiteIntervalSampleStepL1Path
    (duration : ℝ) (finalSampleIndex : ℕ)
    (eventTime : Fin (finalSampleIndex + 1) → ℝ) :
    Continuous
      (finiteIntervalSampleStepL1Path
        (Coordinate := Coordinate) duration finalSampleIndex eventTime) := by
  unfold finiteIntervalSampleStepL1Path finiteCoordinateVectorEventStepL1PathSum
  apply continuous_finsetSum Finset.univ
  intro index _hIndex
  have hIncrement : Continuous fun value :
      Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate =>
        finiteIntervalSampleIncrement finalSampleIndex value index := by
    refine Fin.cases ?_ (fun previous => ?_) index
    · exact continuous_apply 0
    · exact (continuous_apply previous.succ).sub
        (continuous_apply previous.castSucc)
  apply ((finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap
    duration (eventTime index)).continuous.comp hIncrement).congr
  intro value
  exact finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap_apply
    duration (eventTime index) (finiteIntervalSampleIncrement finalSampleIndex value index)

/-- Bounded finite value samples produce a compact family of strong-`L1` step paths. -/
theorem isCompact_finiteIntervalSampleStepL1Path_image_closedBall
    (duration : ℝ) (finalSampleIndex : ℕ)
    (eventTime : Fin (finalSampleIndex + 1) → ℝ) (radius : ℝ) :
    IsCompact
      (finiteIntervalSampleStepL1Path
          (Coordinate := Coordinate) duration finalSampleIndex eventTime ''
        Metric.closedBall
          (0 : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate) radius) :=
  (isCompact_closedBall
      (0 : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate) radius).image
    (continuous_finiteIntervalSampleStepL1Path duration finalSampleIndex eventTime)

/-- The sampled quotient step path recovers the literal sum of its initial value and successive
right-event increments almost everywhere. -/
theorem finiteIntervalSampleStepL1Path_eventuallyEq
    (duration : ℝ) (finalSampleIndex : ℕ)
    (eventTime : Fin (finalSampleIndex + 1) → ℝ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate) :
    (finiteIntervalSampleStepL1Path duration finalSampleIndex eventTime value :
        ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[finiteOpenIntervalVolume duration]
        fun time => ∑ index,
          scalarRightEventStep (eventTime index) 1 time •
            finiteIntervalSampleIncrement finalSampleIndex value index :=
  finiteCoordinateVectorEventStepL1PathSum_eventuallyEq
    duration eventTime (finiteIntervalSampleIncrement finalSampleIndex value)

/-- The equally spaced event time of one sample on the bounded physical interval. -/
def finiteIntervalUniformSampleTime
    (duration : ℝ) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) : ℝ :=
  sampleIndex.val * (duration / (finalSampleIndex + 1))

/-- The left-closed, right-open physical-time cell associated with one uniform sample. -/
def finiteIntervalUniformSampleCell
    (duration : ℝ) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) : Set ℝ :=
  Set.Ico
    (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)
    ((sampleIndex.val + 1) * (duration / (finalSampleIndex + 1)))

/-- Every uniform sample cell lies in the left-closed physical interval. -/
theorem finiteIntervalUniformSampleCell_subset_Ico
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex ⊆
      Set.Ico 0 duration := by
  intro time hTime
  have hCellWidth : 0 < duration / (finalSampleIndex + 1 : ℝ) := by positivity
  constructor
  · exact (mul_nonneg (Nat.cast_nonneg _) hCellWidth.le).trans hTime.1
  · calc
      time < (sampleIndex.val + 1) *
          (duration / (finalSampleIndex + 1 : ℝ)) := hTime.2
      _ ≤ (finalSampleIndex + 1) * (duration / (finalSampleIndex + 1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Nat.succ_le_iff.mpr sampleIndex.isLt
        · exact hCellWidth.le
      _ = duration := by field_simp

/-- Every uniform sample cell has exactly the common mesh width under physical-time volume. -/
theorem finiteOpenIntervalVolume_uniformSampleCell
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    finiteOpenIntervalVolume duration
        (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) =
      ENNReal.ofReal (duration / (finalSampleIndex + 1 : ℝ)) := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply
    (show MeasurableSet
        (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) by
      exact measurableSet_Ico)]
  have hSubset :=
    finiteIntervalUniformSampleCell_subset_Ico hDuration finalSampleIndex sampleIndex
  have hMeasure : volume
      (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex ∩
        Set.Ioo 0 duration) =
      volume (finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) := by
    apply measure_congr
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with time hTime
    apply propext
    constructor
    · exact fun h => h.1
    · intro hCell
      exact ⟨hCell, (hSubset hCell).1.lt_of_ne (Ne.symm hTime), (hSubset hCell).2⟩
  rw [hMeasure]
  unfold finiteIntervalUniformSampleCell finiteIntervalUniformSampleTime
  rw [Real.volume_Ico]
  congr 1
  ring

/-- Distinct uniform sample cells are disjoint. -/
theorem pairwiseDisjoint_finiteIntervalUniformSampleCell
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ) :
    Set.PairwiseDisjoint Set.univ
      (finiteIntervalUniformSampleCell duration finalSampleIndex) := by
  rw [Set.pairwiseDisjoint_iff]
  intro first _hFirst second _hSecond hIntersection
  rcases hIntersection with ⟨time, hTimeFirst, hTimeSecond⟩
  by_contra hDifferent
  have hCellWidth : 0 < duration / (finalSampleIndex + 1 : ℝ) := by positivity
  rcases lt_or_gt_of_ne hDifferent with hFirstSecond | hSecondFirst
  · have hSuccessorLe : first.val + 1 ≤ second.val := by omega
    have hUpperLeLower :
        (first.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)) ≤
          second.val * (duration / (finalSampleIndex + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hSuccessorLe) hCellWidth.le
    exact (not_lt_of_ge (hUpperLeLower.trans hTimeSecond.1)) hTimeFirst.2
  · have hSuccessorLe : second.val + 1 ≤ first.val := by omega
    have hUpperLeLower :
        (second.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)) ≤
          first.val * (duration / (finalSampleIndex + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hSuccessorLe) hCellWidth.le
    exact (not_lt_of_ge (hUpperLeLower.trans hTimeFirst.1)) hTimeSecond.2

/-- The uniform sample cells cover exactly the left-closed physical interval. -/
theorem iUnion_finiteIntervalUniformSampleCell
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ) :
    (⋃ sampleIndex : Fin (finalSampleIndex + 1),
      finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) =
        Set.Ico 0 duration := by
  apply Set.Subset.antisymm
  · intro time hTime
    rcases Set.mem_iUnion.mp hTime with ⟨sampleIndex, hSampleIndex⟩
    exact finiteIntervalUniformSampleCell_subset_Ico hDuration finalSampleIndex
      sampleIndex hSampleIndex
  · intro time hTime
    let meshTime : ℕ → ℝ := fun index =>
      index * (duration / (finalSampleIndex + 1 : ℝ))
    have hStart : meshTime 0 = 0 := by simp [meshTime]
    have hFinish : meshTime (finalSampleIndex + 1) = duration := by
      simp only [meshTime]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
    have hCovered : time ∈ ⋃ index ∈ Finset.range (finalSampleIndex + 1),
        Set.Ico (meshTime index) (meshTime (index + 1)) :=
      Ico_subset_biUnion_Ico (finalSampleIndex + 1) meshTime
        (by simpa only [hStart, hFinish] using hTime)
    rcases Set.mem_iUnion.mp hCovered with ⟨index, hIndexUnion⟩
    rcases Set.mem_iUnion.mp hIndexUnion with ⟨hIndex, hIndexCell⟩
    have hIndexBound : index < finalSampleIndex + 1 := Finset.mem_range.mp hIndex
    apply Set.mem_iUnion.mpr
    refine ⟨⟨index, hIndexBound⟩, ?_⟩
    simpa only [finiteIntervalUniformSampleCell, finiteIntervalUniformSampleTime,
      meshTime, Fin.val_mk, Nat.cast_add, Nat.cast_one] using hIndexCell

/-- Within one uniform mesh cell, an event has occurred exactly when its sample index is no later
than the cell index. -/
theorem finiteIntervalUniformSampleTime_le_iff_of_mem_cell
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (sampleIndex eventIndex : Fin (finalSampleIndex + 1)) {time : ℝ}
    (hTime : time ∈
      finiteIntervalUniformSampleCell duration finalSampleIndex sampleIndex) :
    finiteIntervalUniformSampleTime duration finalSampleIndex eventIndex ≤ time ↔
      eventIndex.val ≤ sampleIndex.val := by
  have hCellWidth : 0 < duration / (finalSampleIndex + 1 : ℝ) := by positivity
  constructor
  · intro hEventTime
    by_contra hNot
    have hSuccessorLe : sampleIndex.val + 1 ≤ eventIndex.val := by omega
    have hUpperLeEvent :
        (sampleIndex.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)) ≤
          eventIndex.val * (duration / (finalSampleIndex + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hSuccessorLe) hCellWidth.le
    exact (not_lt_of_ge (hUpperLeEvent.trans hEventTime)) hTime.2
  · intro hIndex
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hIndex) hCellWidth.le).trans hTime.1

/-- On each uniform mesh cell, the sampled quotient step path is almost everywhere equal to that
cell's sample value. -/
theorem finiteIntervalUniformSampleStepL1Path_eventuallyEq_on_cell
    {duration : ℝ} (hDuration : 0 < duration) (finalSampleIndex : ℕ)
    (value : Fin (finalSampleIndex + 1) → FiniteCoordinateL1Value Coordinate)
    (sampleIndex : Fin (finalSampleIndex + 1)) :
    (finiteIntervalSampleStepL1Path duration finalSampleIndex
        (finiteIntervalUniformSampleTime duration finalSampleIndex) value :
      ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[(finiteOpenIntervalVolume duration).restrict
        (Set.Ico
          (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)
          ((sampleIndex.val + 1) * (duration / (finalSampleIndex + 1))))]
        fun _ => value sampleIndex := by
  let cell := Set.Ico
    (finiteIntervalUniformSampleTime duration finalSampleIndex sampleIndex)
    ((sampleIndex.val + 1) * (duration / (finalSampleIndex + 1 : ℝ)))
  have hStep := (finiteIntervalSampleStepL1Path_eventuallyEq duration finalSampleIndex
    (finiteIntervalUniformSampleTime duration finalSampleIndex) value).restrict (s := cell)
  have hCell : ∀ᵐ time ∂(finiteOpenIntervalVolume duration).restrict cell, time ∈ cell :=
    ae_restrict_mem measurableSet_Ico
  filter_upwards [hStep, hCell] with time hStepTime hTime
  rw [hStepTime]
  simp only [scalarRightEventStep, one_smul, ite_smul, zero_smul]
  convert sum_finiteIntervalSampleIncrement_le finalSampleIndex value sampleIndex using 1
  apply Finset.sum_congr rfl
  intro eventIndex _hEventIndex
  have hOccurred := finiteIntervalUniformSampleTime_le_iff_of_mem_cell
    hDuration finalSampleIndex sampleIndex eventIndex hTime
  by_cases hIndex : eventIndex.val ≤ sampleIndex.val
  · simp [hIndex, hOccurred.mpr hIndex]
  · have hNotOccurred : ¬finiteIntervalUniformSampleTime duration
        finalSampleIndex eventIndex ≤ time := fun hEvent => hIndex (hOccurred.mp hEvent)
    simp [hIndex, hNotOccurred]

end

end FiniteMarkovProcesses
