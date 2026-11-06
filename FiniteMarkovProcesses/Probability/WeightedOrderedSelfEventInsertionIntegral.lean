/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.Measure.PiWithDensity
import FiniteMarkovProcesses.Probability.OrderedSelfEventInsertionVolume
import FiniteMarkovProcesses.Probability.WeightedOrderedJumpTimesIntegral

/-!
# Weighted self-event insertion fibres

This module evaluates a product of time-dependent nonnegative weights over every dwell-wise
ordered self-event insertion coordinate. Finite-product density transport reduces the complete
fibre integral to the product of the one-dwell weighted ordered-simplex integrals.

## Main Result

- `tsum_pi_fin_ennreal`: finite coordinatewise products commute with nonnegative count series.
- `lintegral_weightedOrderedSelfEventInsertions`: exact product of factorial-normalized dwell
  integrals.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Summing a nonnegative product over every finite vector of natural indices factors into the
product of the coordinatewise series. -/
theorem tsum_pi_fin_ennreal {n : ℕ} (weight : Fin n → ℕ → ℝ≥0∞) :
    ∑' indices : Fin n → ℕ, ∏ coordinate, weight coordinate (indices coordinate) =
      ∏ coordinate, ∑' index, weight coordinate index := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      let split : (Fin (n + 1) → ℕ) ≃ (ℕ × (Fin n → ℕ)) := {
        toFun indices := (indices 0, fun coordinate ↦ indices coordinate.succ)
        invFun pair := Fin.cases pair.1 pair.2
        left_inv indices := by
          funext coordinate
          refine Fin.cases ?_ (fun previous ↦ ?_) coordinate
          · rfl
          · rfl
        right_inv pair := by
          rcases pair with ⟨head, tail⟩
          apply Prod.ext
          · rfl
          · funext coordinate
            rfl
      }
      have hProduct (pair : ℕ × (Fin n → ℕ)) :
          (∏ coordinate : Fin (n + 1),
            weight coordinate (split.symm pair coordinate)) =
            weight 0 pair.1 *
              ∏ coordinate : Fin n,
                weight coordinate.succ (pair.2 coordinate) := by
        rw [Fin.prod_univ_succ]
        rfl
      calc
        (∑' indices : Fin (n + 1) → ℕ,
            ∏ coordinate, weight coordinate (indices coordinate)) =
            ∑' pair : ℕ × (Fin n → ℕ),
              ∏ coordinate, weight coordinate (split.symm pair coordinate) :=
          ((split.symm.tsum_eq fun indices ↦
            ∏ coordinate, weight coordinate (indices coordinate))).symm
        _ = ∑' head : ℕ, ∑' tail : Fin n → ℕ,
              weight 0 head *
                ∏ coordinate : Fin n,
                  weight coordinate.succ (tail coordinate) := by
          rw [ENNReal.tsum_prod']
          simp_rw [hProduct]
        _ = (∑' head : ℕ, weight 0 head) *
              ∏ coordinate : Fin n, ∑' index, weight coordinate.succ index := by
          simp_rw [ENNReal.tsum_mul_left]
          rw [inductionHypothesis (fun coordinate ↦ weight coordinate.succ)]
          rw [ENNReal.tsum_mul_right]
        _ = ∏ coordinate : Fin (n + 1), ∑' index, weight coordinate index := by
          rw [Fin.prod_univ_succ]

/-- Product of the block-specific event-time weights over all self-event insertion coordinates. -/
noncomputable def weightedOrderedSelfEventInsertionIntegrand
    {eventCount : ℕ}
    (weight : Fin (eventCount + 1) → ℝ → ℝ)
    (selfEventCounts : Fin (eventCount + 1) → ℕ)
    (insertionTimes :
      (block : Fin (eventCount + 1)) → Fin (selfEventCounts block) → ℝ) : ℝ≥0∞ :=
  ∏ block,
    weightedOrderedJumpTimesIntegrand
      (weight block) (selfEventCounts block) (insertionTimes block)

/-- Measurable block weights give a measurable complete insertion-coordinate weight. -/
theorem measurable_weightedOrderedSelfEventInsertionIntegrand
    {eventCount : ℕ}
    {weight : Fin (eventCount + 1) → ℝ → ℝ}
    (hWeight : ∀ block, Measurable (weight block))
    (selfEventCounts : Fin (eventCount + 1) → ℕ) :
    Measurable
      (weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts) := by
  unfold weightedOrderedSelfEventInsertionIntegrand
  apply Finset.measurable_prod
  intro block _hBlock
  exact (measurable_weightedOrderedJumpTimesIntegrand
    (hWeight block) (selfEventCounts block)).comp (measurable_pi_apply block)

/-- The complete weighted insertion-fibre integral is the product of one exact
factorial-normalized integrated weight for every physical dwell under measurable,
interval-integrable block weights. -/
theorem lintegral_weightedOrderedSelfEventInsertions_of_intervalIntegrable
    {eventCount : ℕ} {T : ℝ} {physicalTimes : Fin eventCount → ℝ}
    {weight : Fin (eventCount + 1) → ℝ → ℝ}
    (hMeasurable : ∀ block, Measurable (weight block))
    (hNonnegative : ∀ block time, 0 ≤ weight block time)
    (selfEventCounts : Fin (eventCount + 1) → ℕ)
    (hT : 0 ≤ T) (hTimes : physicalTimes ∈ orderedJumpTimes eventCount T) :
    (∀ block, IntervalIntegrable (weight block) volume
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ)) →
    ∫⁻ insertionTimes in
        orderedSelfEventInsertions T physicalTimes selfEventCounts,
      weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts insertionTimes =
    ∏ block : Fin (eventCount + 1),
      ENNReal.ofReal
        ((∫ time in Ioo
            (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
            (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ),
              weight block time) ^ selfEventCounts block /
          (selfEventCounts block).factorial) := by
  intro hIntegrable
  let coordinateSet := fun block : Fin (eventCount + 1) ↦
    orderedTimesInInterval (selfEventCounts block)
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ)
  let coordinateDensity := fun block : Fin (eventCount + 1) ↦
    weightedOrderedJumpTimesIntegrand (weight block) (selfEventCounts block)
  let base := fun block : Fin (eventCount + 1) ↦
    (volume : Measure (Fin (selfEventCounts block) → ℝ)).restrict (coordinateSet block)
  have hCoordinateSet (block : Fin (eventCount + 1)) :
      MeasurableSet (coordinateSet block) :=
    measurableSet_orderedTimesInInterval _ _ _
  have hCoordinateDensity (block : Fin (eventCount + 1)) :
      Measurable (coordinateDensity block) :=
    measurable_weightedOrderedJumpTimesIntegrand
      (hMeasurable block) (selfEventCounts block)
  have hDomain :
      orderedSelfEventInsertions T physicalTimes selfEventCounts =
        Set.pi Set.univ coordinateSet := rfl
  have hBase :
      volume.restrict (orderedSelfEventInsertions T physicalTimes selfEventCounts) =
        Measure.pi base := by
    rw [hDomain]
    rw [← MeasureTheory.Measure.restrict_pi_pi
      (fun block : Fin (eventCount + 1) ↦
        (volume : Measure (Fin (selfEventCounts block) → ℝ))) coordinateSet]
    rw [← MeasureTheory.volume_pi]
  have hGlobalDensity :
      weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts =
        fun insertionTimes ↦ ∏ block, coordinateDensity block (insertionTimes block) := rfl
  have hWithDensity :
      (∫⁻ insertionTimes in
          orderedSelfEventInsertions T physicalTimes selfEventCounts,
        weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts insertionTimes) =
        (volume.restrict (orderedSelfEventInsertions T physicalTimes selfEventCounts)
          |>.withDensity
            (weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts)) Set.univ := by
    rw [withDensity_apply _ MeasurableSet.univ]
    simp
  let (block : Fin (eventCount + 1)) :
      IsFiniteMeasure ((base block).withDensity (coordinateDensity block)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    unfold base
    rw [lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
      (hMeasurable block) (hNonnegative block)
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
      (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ)
      (hIntegrable block) (selfEventCounts block)
      (FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
        hT hTimes (Fin.castSucc_le_succ block))]
    exact ENNReal.ofReal_lt_top
  rw [hWithDensity]
  rw [hBase, hGlobalDensity]
  rw [← Measure.pi_withDensity_fin base coordinateDensity hCoordinateDensity]
  rw [Measure.pi_univ]
  apply Finset.prod_congr rfl
  intro block _hBlock
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  unfold base
  exact lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
    (hMeasurable block) (hNonnegative block)
    (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
    (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ)
    (hIntegrable block) (selfEventCounts block)
    (FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hT hTimes (Fin.castSucc_le_succ block))

/-- Continuous block weights satisfy the measurable, interval-integrable insertion-fibre
formula. -/
theorem lintegral_weightedOrderedSelfEventInsertions
    {eventCount : ℕ} {T : ℝ} {physicalTimes : Fin eventCount → ℝ}
    {weight : Fin (eventCount + 1) → ℝ → ℝ}
    (hContinuous : ∀ block, Continuous (weight block))
    (hNonnegative : ∀ block time, 0 ≤ weight block time)
    (selfEventCounts : Fin (eventCount + 1) → ℕ)
    (hT : 0 ≤ T) (hTimes : physicalTimes ∈ orderedJumpTimes eventCount T) :
    ∫⁻ insertionTimes in
        orderedSelfEventInsertions T physicalTimes selfEventCounts,
      weightedOrderedSelfEventInsertionIntegrand weight selfEventCounts insertionTimes =
    ∏ block : Fin (eventCount + 1),
      ENNReal.ofReal
        ((∫ time in Ioo
            (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.castSucc)
            (FiniteJumpHistory.boundaryTimeVector T physicalTimes block.succ),
              weight block time) ^ selfEventCounts block /
          (selfEventCounts block).factorial) := by
  apply lintegral_weightedOrderedSelfEventInsertions_of_intervalIntegrable
    (fun block ↦ (hContinuous block).measurable) hNonnegative selfEventCounts hT hTimes
  intro block
  exact (hContinuous block).intervalIntegrable _ _

end FiniteMarkovProcesses.Probability
