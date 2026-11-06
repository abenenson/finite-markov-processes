/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.OrderedJumpTimesCutDisintegration
import FiniteMarkovProcesses.Probability.OrderedJumpTimesLastDisintegration

/-!
# Marked-coordinate disintegration of ordered jump times

An ordered vector with `earlierCount + 1 + laterCount` coordinates can be split at one marked
event into its time, the strictly earlier block, and the strictly later block.  This module proves
that the split preserves Lebesgue volume and identifies the exact image region.  The resulting
Tonelli formula is the source-neutral analytic kernel for marked-event compensator identities.

## Main results

- `orderedJumpTimesMarkedSplit` and `orderedJumpTimesMarkedJoin`.
- `volume_preserving_orderedJumpTimesMarkedSplit`.
- `lintegral_orderedJumpTimes_marked`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Split a complete ordered-time coordinate vector into the marked time, its earlier block, and
its later block. -/
def orderedJumpTimesMarkedSplit (earlierCount laterCount : ℕ) :
    (Fin (earlierCount + 1 + laterCount) → ℝ) ≃ᵐ
      (ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ) :=
  (orderedJumpTimesCutSplit (earlierCount + 1) laterCount).trans
    ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (earlierCount + 1) ↦ ℝ) (Fin.last earlierCount)).prodCongr
        (MeasurableEquiv.refl (Fin laterCount → ℝ)))

/-- Rejoin a marked time, its earlier block, and its later block into the complete time vector. -/
def orderedJumpTimesMarkedJoin (earlierCount laterCount : ℕ) :
    ((ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ)) ≃ᵐ
      (Fin (earlierCount + 1 + laterCount) → ℝ) :=
  (orderedJumpTimesMarkedSplit earlierCount laterCount).symm

/-- Splitting and then rejoining a complete time vector is literal identity. -/
@[simp]
theorem orderedJumpTimesMarkedJoin_split
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ) :
    orderedJumpTimesMarkedJoin earlierCount laterCount
        (orderedJumpTimesMarkedSplit earlierCount laterCount times) = times :=
  (orderedJumpTimesMarkedSplit earlierCount laterCount).symm_apply_apply times

/-- Rejoining and then splitting marked coordinates is literal identity. -/
@[simp]
theorem orderedJumpTimesMarkedSplit_join
    (earlierCount laterCount : ℕ)
    (coordinates : (ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ)) :
    orderedJumpTimesMarkedSplit earlierCount laterCount
        (orderedJumpTimesMarkedJoin earlierCount laterCount coordinates) = coordinates :=
  (orderedJumpTimesMarkedSplit earlierCount laterCount).apply_symm_apply coordinates

/-- The marked component of the split is the coordinate after all earlier events. -/
@[simp]
theorem orderedJumpTimesMarkedSplit_markedTime
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ) :
    (orderedJumpTimesMarkedSplit earlierCount laterCount times).1.1 =
      times (Fin.castAdd laterCount (Fin.last earlierCount)) := by
  rfl

/-- The earlier component of the split reads the corresponding initial coordinate. -/
@[simp]
theorem orderedJumpTimesMarkedSplit_earlier_apply
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ)
    (index : Fin earlierCount) :
    (orderedJumpTimesMarkedSplit earlierCount laterCount times).1.2 index =
      times (Fin.castAdd laterCount index.castSucc) := by
  change ((Fin.last earlierCount).removeNth
    (orderedJumpTimesCutSplit (earlierCount + 1) laterCount times).1) index =
      times (Fin.castAdd laterCount index.castSucc)
  rw [Fin.removeNth_last]
  exact orderedJumpTimesCutSplit_fst_apply
    (earlierCount + 1) laterCount times index.castSucc

/-- The later component of the split reads the corresponding final coordinate. -/
@[simp]
theorem orderedJumpTimesMarkedSplit_later_apply
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + 1 + laterCount) → ℝ)
    (index : Fin laterCount) :
    (orderedJumpTimesMarkedSplit earlierCount laterCount times).2 index =
      times (Fin.natAdd (earlierCount + 1) index) := by
  exact orderedJumpTimesCutSplit_snd_apply
    (earlierCount + 1) laterCount times index

/-- The marked-coordinate split preserves finite-product Lebesgue volume. -/
theorem volume_preserving_orderedJumpTimesMarkedSplit
    (earlierCount laterCount : ℕ) :
    MeasurePreserving (orderedJumpTimesMarkedSplit earlierCount laterCount) volume volume := by
  let splitAtMarked := orderedJumpTimesCutSplit (earlierCount + 1) laterCount
  let separateMarked :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (earlierCount + 1) ↦ ℝ) (Fin.last earlierCount)).prodCongr
        (MeasurableEquiv.refl (Fin laterCount → ℝ))
  have hSplitAtMarked : MeasurePreserving splitAtMarked volume volume :=
    volume_preserving_orderedJumpTimesCutSplit (earlierCount + 1) laterCount
  have hSeparateFirst : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (earlierCount + 1) ↦ ℝ) (Fin.last earlierCount)) volume volume :=
    volume_preserving_piFinSuccAbove
      (fun _ : Fin (earlierCount + 1) ↦ ℝ) (Fin.last earlierCount)
  have hSeparateMarked : MeasurePreserving separateMarked volume volume := by
    exact hSeparateFirst.prod (MeasurePreserving.id volume)
  exact hSeparateMarked.comp hSplitAtMarked

/-- Exact coordinate region obtained by splitting the ordered simplex at a marked event. -/
def orderedJumpTimesMarkedRegion (earlierCount laterCount : ℕ) (duration : ℝ) :
    Set ((ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ)) :=
  {coordinates |
    coordinates.1.1 ∈ Ioo 0 duration ∧
      coordinates.1.2 ∈ orderedJumpTimes earlierCount coordinates.1.1 ∧
      coordinates.2 ∈
        orderedTimesInInterval laterCount coordinates.1.1 duration}

/-- The marked-coordinate region is measurable. -/
theorem measurableSet_orderedJumpTimesMarkedRegion
    (earlierCount laterCount : ℕ) (duration : ℝ) :
    MeasurableSet (orderedJumpTimesMarkedRegion earlierCount laterCount duration) := by
  let Coordinate := (ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ)
  have hMarked : Measurable fun coordinates : Coordinate ↦ coordinates.1.1 :=
    measurable_fst.comp measurable_fst
  have hEarlier (index : Fin earlierCount) :
      Measurable fun coordinates : Coordinate ↦ coordinates.1.2 index :=
    (measurable_pi_apply index).comp (measurable_snd.comp measurable_fst)
  have hLater (index : Fin laterCount) :
      Measurable fun coordinates : Coordinate ↦ coordinates.2 index :=
    (measurable_pi_apply index).comp measurable_snd
  unfold orderedJumpTimesMarkedRegion orderedJumpTimes orderedTimesInInterval
  apply Measurable.setOf
  apply Measurable.and
  · exact (measurable_const.lt hMarked).and (hMarked.lt measurable_const)
  apply Measurable.and
  · apply Measurable.and
    · apply Measurable.forall
      intro index
      exact (measurable_const.lt (hEarlier index)).and
        ((hEarlier index).lt hMarked)
    · apply Measurable.forall
      intro first
      apply Measurable.forall
      intro second
      exact measurable_const.imp
        ((hEarlier first).lt (hEarlier second))
  · apply Measurable.and
    · apply Measurable.forall
      intro index
      exact (hMarked.lt (hLater index)).and ((hLater index).lt measurable_const)
    · apply Measurable.forall
      intro first
      apply Measurable.forall
      intro second
      exact measurable_const.imp
        ((hLater first).lt (hLater second))

/-- The marked split sends the complete ordered simplex to exactly the marked-coordinate region. -/
theorem orderedJumpTimesMarkedSplit_preimage_region
    (earlierCount laterCount : ℕ) (duration : ℝ) :
    orderedJumpTimesMarkedSplit earlierCount laterCount ⁻¹'
        orderedJumpTimesMarkedRegion earlierCount laterCount duration =
      orderedJumpTimes (earlierCount + 1 + laterCount) duration := by
  ext times
  let markedIndex : Fin (earlierCount + 1 + laterCount) :=
    Fin.castAdd laterCount (Fin.last earlierCount)
  let earlierIndex (index : Fin earlierCount) :
      Fin (earlierCount + 1 + laterCount) :=
    Fin.castAdd laterCount index.castSucc
  let laterIndex (index : Fin laterCount) :
      Fin (earlierCount + 1 + laterCount) :=
    Fin.natAdd (earlierCount + 1) index
  have hMarkedValue : markedIndex.val = earlierCount := by simp [markedIndex]
  have hEarlierValue (index : Fin earlierCount) :
      (earlierIndex index).val = index.val := by simp [earlierIndex]
  have hLaterValue (index : Fin laterCount) :
      (laterIndex index).val = earlierCount + 1 + index.val := by
    simp [laterIndex]
  constructor
  · intro hRegion
    change orderedJumpTimesMarkedSplit earlierCount laterCount times ∈
      orderedJumpTimesMarkedRegion earlierCount laterCount duration at hRegion
    rcases hRegion with ⟨hMarked, hEarlier, hLater⟩
    constructor
    · intro index
      by_cases hBefore : index.val < earlierCount
      · let localIndex : Fin earlierCount := ⟨index.val, hBefore⟩
        have hIndex : index = earlierIndex localIndex := by
          apply Fin.ext
          simp [earlierIndex, localIndex]
        rw [hIndex, ← orderedJumpTimesMarkedSplit_earlier_apply
          earlierCount laterCount times localIndex]
        exact ⟨(hEarlier.1 localIndex).1,
          (hEarlier.1 localIndex).2.trans hMarked.2⟩
      · by_cases hAtMarked : index.val = earlierCount
        · have hIndex : index = markedIndex := by
            apply Fin.ext
            exact hAtMarked.trans hMarkedValue.symm
          rw [hIndex, ← orderedJumpTimesMarkedSplit_markedTime
            earlierCount laterCount times]
          exact hMarked
        · have hLocalBound : index.val - (earlierCount + 1) < laterCount := by omega
          let localIndex : Fin laterCount :=
            ⟨index.val - (earlierCount + 1), hLocalBound⟩
          have hIndex : index = laterIndex localIndex := by
            apply Fin.ext
            simp [laterIndex, localIndex]
            omega
          rw [hIndex, ← orderedJumpTimesMarkedSplit_later_apply
            earlierCount laterCount times localIndex]
          exact ⟨hMarked.1.trans (hLater.1 localIndex).1,
            (hLater.1 localIndex).2⟩
    · intro first second hFirstSecond
      by_cases hFirstBefore : first.val < earlierCount
      · let firstLocal : Fin earlierCount := ⟨first.val, hFirstBefore⟩
        have hFirst : first = earlierIndex firstLocal := by
          apply Fin.ext
          simp [earlierIndex, firstLocal]
        by_cases hSecondBefore : second.val < earlierCount
        · let secondLocal : Fin earlierCount := ⟨second.val, hSecondBefore⟩
          have hSecond : second = earlierIndex secondLocal := by
            apply Fin.ext
            simp [earlierIndex, secondLocal]
          rw [hFirst, hSecond,
            ← orderedJumpTimesMarkedSplit_earlier_apply
              earlierCount laterCount times firstLocal,
            ← orderedJumpTimesMarkedSplit_earlier_apply
              earlierCount laterCount times secondLocal]
          exact hEarlier.2 (by change first.val < second.val; exact hFirstSecond)
        · rw [hFirst, ← orderedJumpTimesMarkedSplit_earlier_apply
            earlierCount laterCount times firstLocal]
          have hBeforeMarked := (hEarlier.1 firstLocal).2
          by_cases hSecondMarked : second.val = earlierCount
          · have hSecond : second = markedIndex := by
              apply Fin.ext
              exact hSecondMarked.trans hMarkedValue.symm
            rw [hSecond, ← orderedJumpTimesMarkedSplit_markedTime
              earlierCount laterCount times]
            exact hBeforeMarked
          · have hSecondLocalBound :
                second.val - (earlierCount + 1) < laterCount := by omega
            let secondLocal : Fin laterCount :=
              ⟨second.val - (earlierCount + 1), hSecondLocalBound⟩
            have hSecond : second = laterIndex secondLocal := by
              apply Fin.ext
              simp [laterIndex, secondLocal]
              omega
            rw [hSecond, ← orderedJumpTimesMarkedSplit_later_apply
              earlierCount laterCount times secondLocal]
            exact hBeforeMarked.trans (hLater.1 secondLocal).1
      · by_cases hFirstMarked : first.val = earlierCount
        · have hFirst : first = markedIndex := by
            apply Fin.ext
            exact hFirstMarked.trans hMarkedValue.symm
          have hSecondAfter : earlierCount < second.val := by omega
          have hSecondLocalBound :
              second.val - (earlierCount + 1) < laterCount := by omega
          let secondLocal : Fin laterCount :=
            ⟨second.val - (earlierCount + 1), hSecondLocalBound⟩
          have hSecond : second = laterIndex secondLocal := by
            apply Fin.ext
            simp [laterIndex, secondLocal]
            omega
          rw [hFirst, hSecond,
            ← orderedJumpTimesMarkedSplit_markedTime
              earlierCount laterCount times,
            ← orderedJumpTimesMarkedSplit_later_apply
              earlierCount laterCount times secondLocal]
          exact (hLater.1 secondLocal).1
        · have hFirstLocalBound :
              first.val - (earlierCount + 1) < laterCount := by omega
          have hSecondLocalBound :
              second.val - (earlierCount + 1) < laterCount := by omega
          let firstLocal : Fin laterCount :=
            ⟨first.val - (earlierCount + 1), hFirstLocalBound⟩
          let secondLocal : Fin laterCount :=
            ⟨second.val - (earlierCount + 1), hSecondLocalBound⟩
          have hFirst : first = laterIndex firstLocal := by
            apply Fin.ext
            simp [laterIndex, firstLocal]
            omega
          have hSecond : second = laterIndex secondLocal := by
            apply Fin.ext
            simp [laterIndex, secondLocal]
            omega
          rw [hFirst, hSecond,
            ← orderedJumpTimesMarkedSplit_later_apply
              earlierCount laterCount times firstLocal,
            ← orderedJumpTimesMarkedSplit_later_apply
              earlierCount laterCount times secondLocal]
          apply hLater.2
          change first.val - (earlierCount + 1) <
            second.val - (earlierCount + 1)
          omega
  · intro hOrdered
    rcases hOrdered with ⟨hBounds, hStrict⟩
    change orderedJumpTimesMarkedSplit earlierCount laterCount times ∈
      orderedJumpTimesMarkedRegion earlierCount laterCount duration
    constructor
    · rw [orderedJumpTimesMarkedSplit_markedTime]
      exact hBounds markedIndex
    constructor
    · constructor
      · intro index
        rw [orderedJumpTimesMarkedSplit_earlier_apply]
        exact ⟨(hBounds (earlierIndex index)).1,
          hStrict (by
            change (earlierIndex index).val < markedIndex.val
            rw [hEarlierValue, hMarkedValue]
            exact index.isLt)⟩
      · intro first second hFirstSecond
        rw [orderedJumpTimesMarkedSplit_earlier_apply,
          orderedJumpTimesMarkedSplit_earlier_apply]
        apply hStrict
        change (earlierIndex first).val < (earlierIndex second).val
        rw [hEarlierValue, hEarlierValue]
        exact hFirstSecond
    · constructor
      · intro index
        rw [orderedJumpTimesMarkedSplit_later_apply]
        exact ⟨hStrict (by
            change markedIndex.val < (laterIndex index).val
            rw [hMarkedValue, hLaterValue]
            omega),
          (hBounds (laterIndex index)).2⟩
      · intro first second hFirstSecond
        rw [orderedJumpTimesMarkedSplit_later_apply,
          orderedJumpTimesMarkedSplit_later_apply]
        apply hStrict
        change (laterIndex first).val < (laterIndex second).val
        rw [hLaterValue, hLaterValue]
        omega

/-- Tonelli disintegration of an arbitrary nonnegative measurable integrand at one marked
coordinate of the complete ordered simplex. -/
theorem lintegral_orderedJumpTimes_marked
    (earlierCount laterCount : ℕ)
    {integrand : (Fin (earlierCount + 1 + laterCount) → ℝ) → ℝ≥0∞}
    (hIntegrand : Measurable integrand) (duration : ℝ) :
    (∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
        orderedJumpTimes (earlierCount + 1 + laterCount) duration,
      integrand times) =
      ∫⁻ markedTime : ℝ in Ioo 0 duration,
        ∫⁻ earlierTimes : Fin earlierCount → ℝ in
            orderedJumpTimes earlierCount markedTime,
          ∫⁻ laterTimes : Fin laterCount → ℝ in
              orderedTimesInInterval laterCount markedTime duration,
            integrand (orderedJumpTimesMarkedJoin earlierCount laterCount
              ((markedTime, earlierTimes), laterTimes)) := by
  let split := orderedJumpTimesMarkedSplit earlierCount laterCount
  let region := orderedJumpTimesMarkedRegion earlierCount laterCount duration
  have hRegion : MeasurableSet region :=
    measurableSet_orderedJumpTimesMarkedRegion earlierCount laterCount duration
  have hPreserving :=
    volume_preserving_orderedJumpTimesMarkedSplit earlierCount laterCount
  have hMap :
      Measure.map split
          (volume.restrict
            (orderedJumpTimes (earlierCount + 1 + laterCount) duration)) =
        volume.restrict region := by
    calc
      Measure.map split
          (volume.restrict
            (orderedJumpTimes (earlierCount + 1 + laterCount) duration)) =
          Measure.map split (volume.restrict (split ⁻¹' region)) := by
            rw [show split ⁻¹' region =
                orderedJumpTimes (earlierCount + 1 + laterCount) duration by
              exact orderedJumpTimesMarkedSplit_preimage_region
                earlierCount laterCount duration]
      _ = (Measure.map split volume).restrict region := by
        rw [Measure.restrict_map hPreserving.measurable hRegion]
      _ = volume.restrict region := by rw [hPreserving.map_eq]
  let splitIntegrand :
      ((ℝ × (Fin earlierCount → ℝ)) × (Fin laterCount → ℝ)) → ℝ≥0∞ :=
    fun coordinates ↦ integrand (split.symm coordinates)
  have hSplitIntegrand : Measurable splitIntegrand :=
    hIntegrand.comp split.symm.measurable
  let restrictedIntegrand := region.indicator splitIntegrand
  have hRestrictedIntegrand : Measurable restrictedIntegrand :=
    hSplitIntegrand.indicator hRegion
  let markedEarlierIntegrand :
      (ℝ × (Fin earlierCount → ℝ)) → ℝ≥0∞ := fun coordinates ↦
    ∫⁻ laterTimes : Fin laterCount → ℝ,
      restrictedIntegrand (coordinates, laterTimes)
  have hMarkedEarlierIntegrand : Measurable markedEarlierIntegrand :=
    hRestrictedIntegrand.lintegral_prod_right'
  calc
    (∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
        orderedJumpTimes (earlierCount + 1 + laterCount) duration,
      integrand times) =
        ∫⁻ coordinates, splitIntegrand coordinates ∂Measure.map split
          (volume.restrict
            (orderedJumpTimes (earlierCount + 1 + laterCount) duration)) := by
      rw [MeasureTheory.lintegral_map_equiv]
      apply lintegral_congr
      intro times
      simp only [splitIntegrand, MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ coordinates in region, splitIntegrand coordinates := by rw [hMap]
    _ = ∫⁻ coordinates, restrictedIntegrand coordinates := by
      exact (lintegral_indicator hRegion splitIntegrand).symm
    _ = ∫⁻ coordinates : ℝ × (Fin earlierCount → ℝ),
        markedEarlierIntegrand coordinates := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod _ hRestrictedIntegrand.aemeasurable]
    _ = ∫⁻ markedTime : ℝ,
        ∫⁻ earlierTimes : Fin earlierCount → ℝ,
          markedEarlierIntegrand (markedTime, earlierTimes) := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod _ hMarkedEarlierIntegrand.aemeasurable]
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro markedTime
      by_cases hMarked : markedTime ∈ Ioo (0 : ℝ) duration
      · rw [Set.indicator_of_mem hMarked]
        rw [← lintegral_indicator
          (measurableSet_orderedJumpTimes earlierCount markedTime)]
        apply lintegral_congr
        intro earlierTimes
        by_cases hEarlier : earlierTimes ∈ orderedJumpTimes earlierCount markedTime
        · rw [Set.indicator_of_mem hEarlier]
          unfold markedEarlierIntegrand restrictedIntegrand
          rw [← lintegral_indicator
            (measurableSet_orderedTimesInInterval
              laterCount markedTime duration)]
          apply lintegral_congr
          intro laterTimes
          by_cases hLater : laterTimes ∈
              orderedTimesInInterval laterCount markedTime duration
          · rw [Set.indicator_of_mem hLater]
            rw [Set.indicator_of_mem]
            · rfl
            · exact ⟨hMarked, hEarlier, hLater⟩
          · rw [Set.indicator_of_notMem hLater]
            rw [Set.indicator_of_notMem]
            intro hRegionMembership
            exact hLater hRegionMembership.2.2
        · rw [Set.indicator_of_notMem hEarlier]
          unfold markedEarlierIntegrand restrictedIntegrand
          have hZero (laterTimes : Fin laterCount → ℝ) :
              region.indicator splitIntegrand ((markedTime, earlierTimes), laterTimes) = 0 := by
            rw [Set.indicator_of_notMem]
            intro hRegionMembership
            exact hEarlier hRegionMembership.2.1
          simp_rw [hZero]
          simp
      · rw [Set.indicator_of_notMem hMarked]
        have hZero (earlierTimes : Fin earlierCount → ℝ) :
            markedEarlierIntegrand (markedTime, earlierTimes) = 0 := by
          unfold markedEarlierIntegrand restrictedIntegrand
          have hPointwiseZero (laterTimes : Fin laterCount → ℝ) :
              region.indicator splitIntegrand ((markedTime, earlierTimes), laterTimes) = 0 := by
            rw [Set.indicator_of_notMem]
            intro hRegionMembership
            exact hMarked hRegionMembership.1
          simp_rw [hPointwiseZero]
          simp
        simp_rw [hZero]
        simp

end

end FiniteMarkovProcesses.Probability
