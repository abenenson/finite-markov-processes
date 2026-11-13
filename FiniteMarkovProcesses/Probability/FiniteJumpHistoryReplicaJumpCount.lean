/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Total jump count of a finite replica family

This module defines the total physical event count of a finite family of jump histories and proves
its measurability.  The definition is source-neutral and retains the literal sum rather than
normalizing by replica number; particle-speed normalizations belong in the consuming theorem.

## Main declarations

- `finiteJumpHistoryReplicaTotalJumpCount`: total event count across all replicas.
- `measurable_finiteJumpHistoryReplicaTotalJumpCount`: measurability of that statistic.
- `coe_finiteJumpHistoryReplicaTotalJumpCount`: its exact real-valued finite-sum form.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory

universe u v

variable {State : Type u} {Replica : Type v} [Fintype Replica]

/-- The total number of physical events across a finite family of jump histories. -/
def finiteJumpHistoryReplicaTotalJumpCount
    (histories : Replica → FiniteJumpHistory State) : ℕ :=
  ∑ replica, (histories replica).jumpCount

/-- Total replica jump count is measurable on the finite product history carrier. -/
theorem measurable_finiteJumpHistoryReplicaTotalJumpCount
    [MeasurableSpace State] :
    Measurable
      (finiteJumpHistoryReplicaTotalJumpCount :
        (Replica → FiniteJumpHistory State) → ℕ) := by
  apply Finset.measurable_sum Finset.univ
  intro replica _hReplica
  exact FiniteJumpHistory.measurable_jumpCount.comp (measurable_pi_apply replica)

/-- Casting the total count to the reals commutes exactly with the finite replica sum. -/
@[simp]
theorem coe_finiteJumpHistoryReplicaTotalJumpCount
    (histories : Replica → FiniteJumpHistory State) :
    (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) =
      ∑ replica, ((histories replica).jumpCount : ℝ) := by
  simp [finiteJumpHistoryReplicaTotalJumpCount]

end FiniteMarkovProcesses.Probability
