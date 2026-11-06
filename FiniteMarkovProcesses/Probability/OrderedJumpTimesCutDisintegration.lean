/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume

/-!
# Cut-time disintegration of ordered event times

An ordered time vector with `earlierCount + laterCount` coordinates can be split at a fixed
physical cut into its first `earlierCount` and last `laterCount` coordinates.  On the sector in
which the first block lies strictly between `lower` and `cut` and the second block lies strictly
between `cut` and `upper`, Lebesgue measure factors exactly into the two ordered-simplex measures.

This is the source-neutral measure-theoretic input for intermediate-time Markov marginals and
marked-event compensator identities.  It does not assert a stochastic independence theorem.

## Main results

- `orderedJumpTimesCutSplit`: measurable split of a finite time vector at a fixed index.
- `orderedJumpTimesCutJoin`: its measurable inverse.
- `orderedJumpTimesCutSector`: the corresponding two-block ordered sector.
- `lintegral_orderedJumpTimesCutSector`: exact Tonelli disintegration on that sector.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Split a finite time vector into its first `earlierCount` and last `laterCount` coordinates. -/
def orderedJumpTimesCutSplit (earlierCount laterCount : ℕ) :
    (Fin (earlierCount + laterCount) → ℝ) ≃ᵐ
      (Fin earlierCount → ℝ) × (Fin laterCount → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (earlierCount + laterCount) ↦ ℝ)
      (finSumFinEquiv (m := earlierCount) (n := laterCount))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin earlierCount ⊕ Fin laterCount ↦ ℝ))

/-- Join an earlier and a later time block into one finite time vector. -/
def orderedJumpTimesCutJoin (earlierCount laterCount : ℕ) :
    ((Fin earlierCount → ℝ) × (Fin laterCount → ℝ)) ≃ᵐ
      (Fin (earlierCount + laterCount) → ℝ) :=
  (orderedJumpTimesCutSplit earlierCount laterCount).symm

/-- Ordered time vectors whose first block lies before the cut and whose second block lies after
the cut.  Both blocks use strict physical endpoints. -/
def orderedJumpTimesCutSector (earlierCount laterCount : ℕ)
    (lower cut upper : ℝ) : Set (Fin (earlierCount + laterCount) → ℝ) :=
  orderedJumpTimesCutSplit earlierCount laterCount ⁻¹'
    (orderedTimesInInterval earlierCount lower cut ×ˢ
      orderedTimesInInterval laterCount cut upper)

/-- The cut sector is measurable. -/
theorem measurableSet_orderedJumpTimesCutSector
    (earlierCount laterCount : ℕ) (lower cut upper : ℝ) :
    MeasurableSet
      (orderedJumpTimesCutSector earlierCount laterCount lower cut upper) := by
  exact ((measurableSet_orderedTimesInInterval earlierCount lower cut).prod
    (measurableSet_orderedTimesInInterval laterCount cut upper)).preimage
      (orderedJumpTimesCutSplit earlierCount laterCount).measurable

/-- Splitting and then rejoining a time vector is literal identity. -/
@[simp]
theorem orderedJumpTimesCutJoin_split (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) :
    orderedJumpTimesCutJoin earlierCount laterCount
        (orderedJumpTimesCutSplit earlierCount laterCount times) =
      times :=
  (orderedJumpTimesCutSplit earlierCount laterCount).symm_apply_apply times

/-- Rejoining and then splitting two time blocks is literal identity. -/
@[simp]
theorem orderedJumpTimesCutSplit_join (earlierCount laterCount : ℕ)
    (blocks : (Fin earlierCount → ℝ) × (Fin laterCount → ℝ)) :
    orderedJumpTimesCutSplit earlierCount laterCount
        (orderedJumpTimesCutJoin earlierCount laterCount blocks) =
      blocks :=
  (orderedJumpTimesCutSplit earlierCount laterCount).apply_symm_apply blocks

/-- The joined vector agrees with the earlier block on its first coordinates. -/
@[simp]
theorem orderedJumpTimesCutJoin_apply_castAdd
    (earlierCount laterCount : ℕ)
    (earlierTimes : Fin earlierCount → ℝ) (laterTimes : Fin laterCount → ℝ)
    (index : Fin earlierCount) :
    orderedJumpTimesCutJoin earlierCount laterCount (earlierTimes, laterTimes)
        (Fin.castAdd laterCount index) =
      earlierTimes index := by
  have hBlocks := congrArg (fun blocks ↦ blocks.1 index)
    (orderedJumpTimesCutSplit_join earlierCount laterCount
      (earlierTimes, laterTimes))
  change orderedJumpTimesCutJoin earlierCount laterCount (earlierTimes, laterTimes)
      (Fin.castAdd laterCount index) = earlierTimes index at hBlocks
  exact hBlocks

/-- The joined vector agrees with the later block on its final coordinates. -/
@[simp]
theorem orderedJumpTimesCutJoin_apply_natAdd
    (earlierCount laterCount : ℕ)
    (earlierTimes : Fin earlierCount → ℝ) (laterTimes : Fin laterCount → ℝ)
    (index : Fin laterCount) :
    orderedJumpTimesCutJoin earlierCount laterCount (earlierTimes, laterTimes)
        (Fin.natAdd earlierCount index) =
      laterTimes index := by
  have hBlocks := congrArg (fun blocks ↦ blocks.2 index)
    (orderedJumpTimesCutSplit_join earlierCount laterCount
      (earlierTimes, laterTimes))
  change orderedJumpTimesCutJoin earlierCount laterCount (earlierTimes, laterTimes)
      (Fin.natAdd earlierCount index) = laterTimes index at hBlocks
  exact hBlocks

/-- The earlier block of a split vector reads the corresponding first coordinate. -/
@[simp]
theorem orderedJumpTimesCutSplit_fst_apply
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) (index : Fin earlierCount) :
    (orderedJumpTimesCutSplit earlierCount laterCount times).1 index =
      times (Fin.castAdd laterCount index) := by
  have hTimes := congrArg
    (fun joinedTimes ↦ joinedTimes (Fin.castAdd laterCount index))
    (orderedJumpTimesCutJoin_split earlierCount laterCount times)
  change orderedJumpTimesCutJoin earlierCount laterCount
      (orderedJumpTimesCutSplit earlierCount laterCount times)
        (Fin.castAdd laterCount index) =
    times (Fin.castAdd laterCount index) at hTimes
  rw [orderedJumpTimesCutJoin_apply_castAdd] at hTimes
  exact hTimes

/-- The later block of a split vector reads the corresponding final coordinate. -/
@[simp]
theorem orderedJumpTimesCutSplit_snd_apply
    (earlierCount laterCount : ℕ)
    (times : Fin (earlierCount + laterCount) → ℝ) (index : Fin laterCount) :
    (orderedJumpTimesCutSplit earlierCount laterCount times).2 index =
      times (Fin.natAdd earlierCount index) := by
  have hTimes := congrArg
    (fun joinedTimes ↦ joinedTimes (Fin.natAdd earlierCount index))
    (orderedJumpTimesCutJoin_split earlierCount laterCount times)
  change orderedJumpTimesCutJoin earlierCount laterCount
      (orderedJumpTimesCutSplit earlierCount laterCount times)
        (Fin.natAdd earlierCount index) =
    times (Fin.natAdd earlierCount index) at hTimes
  rw [orderedJumpTimesCutJoin_apply_natAdd] at hTimes
  exact hTimes

/-- The finite-coordinate cut equivalence preserves Lebesgue volume. -/
theorem volume_preserving_orderedJumpTimesCutSplit
    (earlierCount laterCount : ℕ) :
    MeasurePreserving (orderedJumpTimesCutSplit earlierCount laterCount) volume volume := by
  let reindex := MeasurableEquiv.piCongrLeft
    (fun _ : Fin (earlierCount + laterCount) ↦ ℝ)
    (finSumFinEquiv (m := earlierCount) (n := laterCount))
  let separate := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin earlierCount ⊕ Fin laterCount ↦ ℝ)
  have hReindex : MeasurePreserving reindex volume volume :=
    volume_measurePreserving_piCongrLeft
      (fun _ : Fin (earlierCount + laterCount) ↦ ℝ)
      (finSumFinEquiv (m := earlierCount) (n := laterCount))
  have hSeparate : MeasurePreserving separate volume volume :=
    volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin earlierCount ⊕ Fin laterCount ↦ ℝ)
  exact hSeparate.comp hReindex.symm

/-- Exact Tonelli disintegration of an arbitrary nonnegative measurable integrand on one
cut-time sector. -/
theorem lintegral_orderedJumpTimesCutSector
    (earlierCount laterCount : ℕ) (lower cut upper : ℝ)
    {integrand : (Fin (earlierCount + laterCount) → ℝ) → ℝ≥0∞}
    (hIntegrand : Measurable integrand) :
    (∫⁻ times in orderedJumpTimesCutSector
        earlierCount laterCount lower cut upper,
      integrand times) =
    ∫⁻ earlierTimes in orderedTimesInInterval earlierCount lower cut,
      ∫⁻ laterTimes in orderedTimesInInterval laterCount cut upper,
        integrand (orderedJumpTimesCutJoin earlierCount laterCount
          (earlierTimes, laterTimes)) := by
  let split := orderedJumpTimesCutSplit earlierCount laterCount
  let sectorProduct :=
    orderedTimesInInterval earlierCount lower cut ×ˢ
      orderedTimesInInterval laterCount cut upper
  have hSectorProduct : MeasurableSet sectorProduct :=
    (measurableSet_orderedTimesInInterval earlierCount lower cut).prod
      (measurableSet_orderedTimesInInterval laterCount cut upper)
  have hPreserving := volume_preserving_orderedJumpTimesCutSplit
    earlierCount laterCount
  have hMap :
      Measure.map split
          (volume.restrict (orderedJumpTimesCutSector
            earlierCount laterCount lower cut upper)) =
        volume.restrict sectorProduct := by
    calc
      Measure.map split
          (volume.restrict (orderedJumpTimesCutSector
            earlierCount laterCount lower cut upper)) =
          Measure.map split (volume.restrict (split ⁻¹' sectorProduct)) := by
            rfl
      _ = (Measure.map split volume).restrict sectorProduct := by
        rw [Measure.restrict_map hPreserving.measurable hSectorProduct]
      _ = volume.restrict sectorProduct := by
        rw [hPreserving.map_eq]
  let splitIntegrand :
      (Fin earlierCount → ℝ) × (Fin laterCount → ℝ) → ℝ≥0∞ :=
    fun blocks ↦ integrand (split.symm blocks)
  have hSplitIntegrand : Measurable splitIntegrand :=
    hIntegrand.comp split.symm.measurable
  calc
    (∫⁻ times in orderedJumpTimesCutSector
        earlierCount laterCount lower cut upper,
      integrand times) =
        ∫⁻ blocks, splitIntegrand blocks ∂Measure.map split
          (volume.restrict (orderedJumpTimesCutSector
            earlierCount laterCount lower cut upper)) := by
      rw [MeasureTheory.lintegral_map_equiv]
      apply lintegral_congr
      intro times
      simp only [splitIntegrand, MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ blocks in sectorProduct, splitIntegrand blocks := by rw [hMap]
    _ = _ := by
      rw [Measure.volume_eq_prod]
      rw [← Measure.prod_restrict]
      rw [lintegral_prod _ hSplitIntegrand.aemeasurable]
      rfl

end

end FiniteMarkovProcesses.Probability
