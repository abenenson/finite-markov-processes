/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume

/-!
# Volumes of ordered self-event insertion fibres

Fix a physical jump-time vector and a number of virtual self-events to insert in each physical
dwell. The insertion fibre is a dependent product of ordered simplices, one inside every adjacent
pair of complete boundary times. This module proves that its Lebesgue volume is the product of the
expected dwell powers divided by factorials.

The result is the coordinate-volume kernel needed to identify a uniformized finite-state CTMC
history after self-event deletion. It is independent of any Markov generator or source model.

## Main Results

- `orderedSelfEventInsertions`: dependent product of ordered insertion simplices over all dwells.
- `measurableSet_orderedSelfEventInsertions`: measurability of the complete insertion fibre.
- `volume_orderedSelfEventInsertions`: exact product of dwell-power/factorial volumes.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Ordered virtual self-event times inside every dwell of one physical jump-time vector. -/
def orderedSelfEventInsertions {eventCount : ℕ}
    (T : ℝ) (times : Fin eventCount → ℝ)
    (selfEventCounts : Fin (eventCount + 1) → ℕ) :
    Set ((index : Fin (eventCount + 1)) → Fin (selfEventCounts index) → ℝ) :=
  Set.pi Set.univ fun index ↦
    orderedTimesInInterval (selfEventCounts index)
      (FiniteJumpHistory.boundaryTimeVector T times index.castSucc)
      (FiniteJumpHistory.boundaryTimeVector T times index.succ)

/-- The complete dependent product of ordered self-event insertion simplices is measurable. -/
theorem measurableSet_orderedSelfEventInsertions {eventCount : ℕ}
    (T : ℝ) (times : Fin eventCount → ℝ)
    (selfEventCounts : Fin (eventCount + 1) → ℕ) :
    MeasurableSet (orderedSelfEventInsertions T times selfEventCounts) := by
  apply MeasurableSet.pi Set.countable_univ
  intro index _
  exact measurableSet_orderedTimesInInterval _ _ _

/-- The insertion-fibre volume factors over physical dwells, with one ordered-simplex
coefficient `dwell ^ count / count!` per dwell. -/
theorem volume_orderedSelfEventInsertions {eventCount : ℕ}
    (T : ℝ) (times : Fin eventCount → ℝ)
    (selfEventCounts : Fin (eventCount + 1) → ℕ)
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes eventCount T) :
    volume (orderedSelfEventInsertions T times selfEventCounts) =
      ∏ index : Fin (eventCount + 1),
        ENNReal.ofReal
          (FiniteJumpHistory.dwellTimeVector T times index ^ selfEventCounts index /
            (selfEventCounts index).factorial) := by
  unfold orderedSelfEventInsertions
  rw [volume_pi_pi]
  apply Finset.prod_congr rfl
  intro index _
  rw [volume_orderedTimesInInterval]
  · rfl
  · exact FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hT hTimes (Fin.castSucc_le_succ index)

end FiniteMarkovProcesses.Probability
