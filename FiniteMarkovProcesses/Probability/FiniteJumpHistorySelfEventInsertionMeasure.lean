/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.MeasureTheory.Measure.PiWithDensity
public import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionOrder
public import FiniteMarkovProcesses.Probability.FinitePiCurryVolume

/-!
# Measure transport for canonical self-event insertion

The canonical merge of independent self-event insertion coordinates and retained physical jump
times is a finite coordinate permutation. This module packages it as a measurable equivalence,
proves its exact unit-Jacobian Lebesgue transport, and identifies the ordered-domain fibres needed
for uniformization deletion.

## Main Results

- `FiniteJumpHistory.selfEventInsertedJumpTimeEquiv`: coordinate equivalence underlying the
  canonical merged jump-time vector.
- `FiniteJumpHistory.volume_measurePreserving_selfEventInsertedJumpTimeEquiv`: exact Lebesgue
  preservation of the merge.
- `FiniteJumpHistory.selfEventInsertedJumpTimeEquiv_mem_orderedJumpTimes_iff`: exact ordered-domain
  characterization of each insertion fibre.
- `FiniteJumpHistory.map_volume_restrict_selfEventInsertionCoordinateDomain`: exact transport of
  the complete product insertion domain to the virtual ordered simplex.
- `FiniteJumpHistory.map_snd_volume_restrict_selfEventInsertionCoordinateDomain`: retained-time
  marginal with the exact product of dwell-simplex fibre volumes.
-/

@[expose] public section

open FiniteMarkovProcesses.Probability MeasureTheory
open scoped BigOperators ENNReal

universe u

namespace FiniteJumpHistory

/-- Coordinate equivalence from per-dwell self-event times and physical jump times to the merged
virtual jump-time vector. -/
noncomputable def selfEventInsertedJumpTimeEquiv {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    (((index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ) ×
        (Fin physicalEventCount → ℝ)) ≃
      (Fin (selfEventInsertedEventCount selfEventCounts) → ℝ) :=
  (((Equiv.piCurry
      (fun (index : Fin (physicalEventCount + 1))
        (_ : Fin (selfEventCounts index)) ↦ ℝ)).symm).prodCongr
      (Equiv.refl (Fin physicalEventCount → ℝ))).trans <|
    ((Equiv.sumPiEquivProdPi
      (fun _ : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount ↦ ℝ)).symm
      |>.trans <|
        Equiv.piCongrLeft (fun _ ↦ ℝ)
          (selfEventInsertedEventCoordinateEquiv selfEventCounts))

/-- The coordinate equivalence evaluates exactly as the canonical merged jump-time function. -/
theorem selfEventInsertedJumpTimeEquiv_apply {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (insertionTimes :
      (index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    selfEventInsertedJumpTimeEquiv selfEventCounts (insertionTimes, physicalTimes) =
      selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes := by
  funext eventIndex
  let coordinate :=
    (selfEventInsertedEventCoordinateEquiv selfEventCounts).symm eventIndex
  have hEvent :
      eventIndex = selfEventInsertedEventCoordinateEquiv selfEventCounts coordinate :=
    (selfEventInsertedEventCoordinateEquiv selfEventCounts).apply_symm_apply eventIndex |>.symm
  rw [hEvent]
  rcases coordinate with ⟨index, selfEventIndex⟩ | index
  · unfold selfEventInsertedJumpTimeEquiv selfEventInsertedJumpTimes
    simp only [Equiv.trans_apply]
    rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
    rfl
  · unfold selfEventInsertedJumpTimeEquiv selfEventInsertedJumpTimes
    simp only [Equiv.trans_apply]
    rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
    rfl

/-- Canonically merging the insertion and retained coordinates preserves Lebesgue volume exactly;
the finite coordinate transformation has unit Jacobian. -/
theorem volume_measurePreserving_selfEventInsertedJumpTimeEquiv
    {physicalEventCount : ℕ}
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    MeasurePreserving (selfEventInsertedJumpTimeEquiv selfEventCounts) := by
  let curryEquiv := Equiv.piCurry
    (fun (index : Fin (physicalEventCount + 1))
      (_ : Fin (selfEventCounts index)) ↦ ℝ)
  let sumEquiv := Equiv.sumPiEquivProdPi
    (fun _ : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount ↦ ℝ)
  let eventEquiv := selfEventInsertedEventCoordinateEquiv selfEventCounts
  have hCurryForward := volume_measurePreserving_piCurry_real
    (fun index : Fin (physicalEventCount + 1) ↦ Fin (selfEventCounts index))
  have hCurry := MeasurePreserving.symm
    (MeasurableEquiv.piCurry
      (fun (index : Fin (physicalEventCount + 1))
        (_ : Fin (selfEventCounts index)) ↦ ℝ)) hCurryForward
  have hPhysical : MeasurePreserving
      (id : (Fin physicalEventCount → ℝ) → Fin physicalEventCount → ℝ) volume volume :=
    MeasurePreserving.id _
  have hProduct := hCurry.prod hPhysical
  have hSumForward := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount ↦ ℝ)
  have hSum := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : SelfEventInsertionCoordinate selfEventCounts ⊕ Fin physicalEventCount ↦ ℝ))
    hSumForward
  have hEvent := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (selfEventInsertedEventCount selfEventCounts) ↦ ℝ) eventEquiv
  exact hEvent.comp <| hSum.comp hProduct

/-- Product-domain carrier consisting of an ordered physical jump-time vector and ordered
self-event insertion times inside every one of its physical dwells. -/
def selfEventInsertionCoordinateDomain {physicalEventCount : ℕ}
    (T : ℝ) (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Set (((index : Fin (physicalEventCount + 1)) →
        Fin (selfEventCounts index) → ℝ) × (Fin physicalEventCount → ℝ)) :=
  {coordinates |
    coordinates.2 ∈ orderedJumpTimes physicalEventCount T ∧
      coordinates.1 ∈
        orderedSelfEventInsertions T coordinates.2 selfEventCounts}

/-- A coordinate pair belongs to the product insertion domain exactly when its canonical merged
time vector belongs to the complete virtual ordered simplex. -/
theorem selfEventInsertedJumpTimeEquiv_mem_orderedJumpTimes_iff
    {physicalEventCount : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (coordinates :
      ((index : Fin (physicalEventCount + 1)) → Fin (selfEventCounts index) → ℝ) ×
        (Fin physicalEventCount → ℝ)) :
    selfEventInsertedJumpTimeEquiv selfEventCounts coordinates ∈
        orderedJumpTimes (selfEventInsertedEventCount selfEventCounts) T ↔
      coordinates ∈ selfEventInsertionCoordinateDomain T selfEventCounts := by
  rcases coordinates with ⟨insertionTimes, physicalTimes⟩
  rw [selfEventInsertedJumpTimeEquiv_apply]
  constructor
  · intro hVirtual
    constructor
    · constructor
      · intro index
        simpa only [selfEventInsertedJumpTimes_physicalTransitionEventIndex] using
          hVirtual.1
            (selfEventInsertedPhysicalTransitionEventIndex selfEventCounts index)
      · intro first second hFirstSecond
        have hTimeOrder := hVirtual.2
          ((strictMono_selfEventInsertedPhysicalTransitionEventIndex selfEventCounts)
            hFirstSecond)
        simpa only [selfEventInsertedJumpTimes_physicalTransitionEventIndex] using hTimeOrder
    · intro block _
      constructor
      · intro selfEventIndex
        constructor
        · by_cases hBlockZero : block = 0
          · subst block
            simpa only [Fin.castSucc_zero, boundaryTimeVector_zero,
              selfEventInsertedJumpTimes_selfEventIndex] using
                (hVirtual.1
                  (selfEventInsertedSelfEventIndex
                    selfEventCounts 0 selfEventIndex)).1
          · let previousPhysicalIndex : Fin physicalEventCount :=
              ⟨block.val - 1, by
                have hBlockBound : block.val < physicalEventCount + 1 := block.isLt
                have hBlockPositive : 0 < block.val := Nat.pos_of_ne_zero <| by
                  intro hValue
                  apply hBlockZero
                  apply Fin.ext
                  exact hValue
                omega⟩
            have hPreviousBlock : previousPhysicalIndex.castSucc < block := by
              change previousPhysicalIndex.val < block.val
              simp only [previousPhysicalIndex]
              have hBlockPositive : 0 < block.val := Nat.pos_of_ne_zero <| by
                intro hValue
                apply hBlockZero
                apply Fin.ext
                exact hValue
              omega
            have hEventOrder :=
              selfEventInsertedPhysicalTransitionEventIndex_lt_selfEventIndex_of_block_lt
                selfEventCounts previousPhysicalIndex block hPreviousBlock selfEventIndex
            have hTimeOrder := hVirtual.2 hEventOrder
            have hBoundaryIndex :
                block.castSucc = previousPhysicalIndex.castSucc.succ := by
              apply Fin.ext
              change block.val = block.val - 1 + 1
              have hBlockPositive : 0 < block.val := Nat.pos_of_ne_zero <| by
                intro hValue
                apply hBlockZero
                apply Fin.ext
                exact hValue
              omega
            rw [hBoundaryIndex, boundaryTimeVector_succ_castSucc]
            simpa only [selfEventInsertedJumpTimes_physicalTransitionEventIndex,
              selfEventInsertedJumpTimes_selfEventIndex] using hTimeOrder
        · by_cases hBlockLast : block = Fin.last physicalEventCount
          · subst block
            rw [show (Fin.last physicalEventCount).succ =
              Fin.last (physicalEventCount + 1) by rfl]
            simpa only [boundaryTimeVector_last,
              selfEventInsertedJumpTimes_selfEventIndex] using
                (hVirtual.1
                  (selfEventInsertedSelfEventIndex selfEventCounts
                    (Fin.last physicalEventCount) selfEventIndex)).2
          · let physicalIndex : Fin physicalEventCount := block.castPred hBlockLast
            have hEventOrder :=
              selfEventInsertedSelfEventIndex_lt_physicalTransitionEventIndex
                selfEventCounts block hBlockLast selfEventIndex
            have hTimeOrder := hVirtual.2 hEventOrder
            have hBoundaryIndex : block.succ = physicalIndex.castSucc.succ := by
              apply Fin.ext
              have hValue := congrArg Fin.val
                (Fin.castSucc_castPred block hBlockLast)
              change block.val + 1 = physicalIndex.val + 1
              change physicalIndex.val = block.val at hValue
              omega
            rw [hBoundaryIndex, boundaryTimeVector_succ_castSucc]
            simpa only [selfEventInsertedJumpTimes_selfEventIndex,
              selfEventInsertedJumpTimes_physicalTransitionEventIndex] using hTimeOrder
      · intro first second hFirstSecond
        have hTimeOrder := hVirtual.2
          ((strictMono_selfEventInsertedSelfEventIndex selfEventCounts block) hFirstSecond)
        simpa only [selfEventInsertedJumpTimes_selfEventIndex] using hTimeOrder
  · rintro ⟨hPhysicalTimes, hInsertionTimes⟩
    exact selfEventInsertedJumpTimes_mem_orderedJumpTimes
      hT hPhysicalTimes hInsertionTimes

/-- The complete product insertion domain is measurable because it is exactly the preimage of
the virtual ordered simplex under a measurable coordinate equivalence. -/
theorem measurableSet_selfEventInsertionCoordinateDomain
    {physicalEventCount : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    MeasurableSet (selfEventInsertionCoordinateDomain T selfEventCounts) := by
  have hSet : selfEventInsertionCoordinateDomain T selfEventCounts =
      selfEventInsertedJumpTimeEquiv selfEventCounts ⁻¹'
        orderedJumpTimes (selfEventInsertedEventCount selfEventCounts) T := by
    ext coordinates
    exact (selfEventInsertedJumpTimeEquiv_mem_orderedJumpTimes_iff
      hT selfEventCounts coordinates).symm
  rw [hSet]
  exact (measurableSet_orderedJumpTimes
    (selfEventInsertedEventCount selfEventCounts) T).preimage
      (volume_measurePreserving_selfEventInsertedJumpTimeEquiv
        selfEventCounts).measurable

/-- The canonical merge pushes restricted product Lebesgue volume on the insertion-coordinate
domain exactly to restricted Lebesgue volume on the complete virtual ordered simplex. -/
theorem map_volume_restrict_selfEventInsertionCoordinateDomain
    {physicalEventCount : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Measure.map (selfEventInsertedJumpTimeEquiv selfEventCounts)
        (volume.restrict (selfEventInsertionCoordinateDomain T selfEventCounts)) =
      volume.restrict
        (orderedJumpTimes (selfEventInsertedEventCount selfEventCounts) T) := by
  let merge := selfEventInsertedJumpTimeEquiv selfEventCounts
  have hMerge := volume_measurePreserving_selfEventInsertedJumpTimeEquiv selfEventCounts
  have hOrdered := measurableSet_orderedJumpTimes
    (selfEventInsertedEventCount selfEventCounts) T
  have hDomain : selfEventInsertionCoordinateDomain T selfEventCounts =
      merge ⁻¹' orderedJumpTimes (selfEventInsertedEventCount selfEventCounts) T := by
    ext coordinates
    exact (selfEventInsertedJumpTimeEquiv_mem_orderedJumpTimes_iff
      hT selfEventCounts coordinates).symm
  rw [hDomain, ← Measure.restrict_map hMerge.measurable hOrdered, hMerge.map_eq]

/-- Forgetting the insertion coordinates weights physical ordered-time volume by the exact
product of per-dwell ordered-simplex volumes. -/
theorem map_snd_volume_restrict_selfEventInsertionCoordinateDomain
    {physicalEventCount : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Measure.map Prod.snd
        (volume.restrict (selfEventInsertionCoordinateDomain T selfEventCounts)) =
      (volume.restrict (orderedJumpTimes physicalEventCount T)).withDensity
        (fun physicalTimes ↦
          ∏ block : Fin (physicalEventCount + 1),
            ENNReal.ofReal
              (dwellTimeVector T physicalTimes block ^ selfEventCounts block /
                (selfEventCounts block).factorial)) := by
  let weight := fun physicalTimes : Fin physicalEventCount → ℝ ↦
    ∏ block : Fin (physicalEventCount + 1),
      ENNReal.ofReal
        (dwellTimeVector T physicalTimes block ^ selfEventCounts block /
          (selfEventCounts block).factorial)
  have hDomain := measurableSet_selfEventInsertionCoordinateDomain hT selfEventCounts
  rw [Measure.volume_eq_prod]
  rw [Measure.map_snd_restrict_eq_withDensity_fibre volume volume
    (selfEventInsertionCoordinateDomain T selfEventCounts) hDomain]
  have hFibreVolume :
      (fun physicalTimes : Fin physicalEventCount → ℝ ↦
        volume ((fun insertionTimes ↦ (insertionTimes, physicalTimes)) ⁻¹'
          selfEventInsertionCoordinateDomain T selfEventCounts)) =
        (orderedJumpTimes physicalEventCount T).indicator weight := by
    funext physicalTimes
    by_cases hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T
    · rw [Set.indicator_of_mem hPhysicalTimes]
      have hFibre :
          (fun insertionTimes ↦ (insertionTimes, physicalTimes)) ⁻¹'
              selfEventInsertionCoordinateDomain T selfEventCounts =
            orderedSelfEventInsertions T physicalTimes selfEventCounts := by
        ext insertionTimes
        simp only [Set.mem_preimage, selfEventInsertionCoordinateDomain,
          Set.mem_ofPred_eq, hPhysicalTimes, true_and]
      rw [hFibre, volume_orderedSelfEventInsertions T physicalTimes
        selfEventCounts hT hPhysicalTimes]
    · rw [Set.indicator_of_notMem hPhysicalTimes]
      have hFibre :
          (fun insertionTimes ↦ (insertionTimes, physicalTimes)) ⁻¹'
              selfEventInsertionCoordinateDomain T selfEventCounts = ∅ := by
        ext insertionTimes
        simp only [Set.mem_preimage, selfEventInsertionCoordinateDomain,
          Set.mem_ofPred_eq, hPhysicalTimes, false_and, Set.notMem_empty]
      rw [hFibre, measure_empty]
  rw [hFibreVolume, withDensity_indicator
    (measurableSet_orderedJumpTimes physicalEventCount T)]

end FiniteJumpHistory
