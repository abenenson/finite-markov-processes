/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDensityIdentification
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Reversal laws of finite-state Markov jump processes

This module constructs the complete-history reversal of a normalized finite-state Markov jump
law. The reversed law is defined as an actual measurable pushforward, whether or not it admits a
time-homogeneous forward-generator representation. Its density is the forward density evaluated
on the completely reversed state word and event-time vector.

## Main Results

- `finiteStateMarkovJumpReversalDensityMeasure`: measurable reversal pushforward of the physical
  jump-density measure.
- `finiteStateMarkovJumpReversalDensityMeasure_eq_withDensity`: exact density of the pushforward
  against the unchanged counting--Lebesgue history base.
- `finiteStateMarkovJumpReversalProbabilityMeasure`: normalized reversal probability law.
- `finiteStateMarkovIntegratedEscape_reverse`: complete reversal preserves integrated escape
  after permuting the dwell vector.
- `ae_physicalAt_finiteStateMarkovJumpReversalDensityMeasure`: reversal remains on the exact
  physical history carrier.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped ENNReal

universe u

variable {State : Type u} [Fintype State]

/-- Complete reversal preserves integrated escape after reversing the state and dwell indices. -/
theorem finiteStateMarkovIntegratedEscape_reverse
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    finiteStateMarkovIntegratedEscape generator T
        (fun i => states i.rev) (FiniteJumpHistory.reverseTimes T times) =
      finiteStateMarkovIntegratedEscape generator T states times := by
  unfold finiteStateMarkovIntegratedEscape
  simp_rw [FiniteJumpHistory.dwellTimeVector_reverseTimes]
  exact Equiv.sum_comp Fin.revPerm
    (fun i : Fin (n + 1) =>
      (generator.escapeRate (states i) : ℝ) *
        FiniteJumpHistory.dwellTimeVector T times i)

/-- Complete-history reversal of a finite-state Markov jump-density measure. This definition is
the literal measurable pushforward and does not assume that the reversed process is represented
by a time-homogeneous generator. -/
noncomputable def finiteStateMarkovJumpReversalDensityMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.map (FiniteJumpHistory.reverse T)
    (finiteStateMarkovJumpDensityMeasure initial generator T)

/-- The reversal pushforward has the forward density evaluated on the complete reversal, against
the same counting--Lebesgue history base measure. -/
theorem finiteStateMarkovJumpReversalDensityMeasure_eq_withDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpReversalDensityMeasure initial generator T =
      (finiteJumpHistoryBaseMeasure State T).withDensity
        (finiteStateMarkovJumpDensityENNReal initial generator T ∘
          FiniteJumpHistory.reverse T) := by
  have hTransport := Measure.map_withDensity_comp
    (finiteJumpHistoryBaseMeasure State T)
    (FiniteJumpHistory.measurable_reverse T)
    (finiteStateMarkovJumpDensityENNReal initial generator T ∘
      FiniteJumpHistory.reverse T)
    ((measurable_finiteStateMarkovJumpDensityENNReal initial generator T).comp
      (FiniteJumpHistory.measurable_reverse T))
  have hComposition :
      (finiteStateMarkovJumpDensityENNReal initial generator T ∘
          FiniteJumpHistory.reverse T) ∘
        FiniteJumpHistory.reverse T =
      finiteStateMarkovJumpDensityENNReal initial generator T := by
    funext history
    simp only [Function.comp_apply, FiniteJumpHistory.reverse_reverse]
  rw [hComposition,
    FiniteJumpHistory.map_reverse_finiteJumpHistoryBaseMeasure] at hTransport
  exact hTransport

/-- A finite-state jump reversal density measure is sigma-finite. -/
noncomputable instance instSigmaFiniteFiniteStateMarkovJumpReversalDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    SigmaFinite (finiteStateMarkovJumpReversalDensityMeasure initial generator T) := by
  rw [finiteStateMarkovJumpReversalDensityMeasure_eq_withDensity]
  exact SigmaFinite.withDensity_of_ne_top' fun history => by
    simp [finiteStateMarkovJumpDensityENNReal]

/-- Reversing the reversal density measure recovers the original forward density measure. -/
theorem map_reverse_finiteStateMarkovJumpReversalDensityMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map (FiniteJumpHistory.reverse T)
        (finiteStateMarkovJumpReversalDensityMeasure initial generator T) =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  unfold finiteStateMarkovJumpReversalDensityMeasure
  rw [Measure.map_map (FiniteJumpHistory.measurable_reverse T)
    (FiniteJumpHistory.measurable_reverse T)]
  have hInvolution :
      FiniteJumpHistory.reverse (State := State) T ∘
          FiniteJumpHistory.reverse (State := State) T = id := by
    funext history
    exact FiniteJumpHistory.reverse_reverse T history
  rw [hInvolution, Measure.map_id]

/-- Exact probability promotion of the reversal pushforward at a nonnegative horizon. -/
noncomputable def finiteStateMarkovJumpReversalProbabilityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ProbabilityMeasure (FiniteJumpHistory State) :=
  let forward := finiteStateMarkovJumpProbabilityMeasure initial generator T
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative initial generator T hT)
  ⟨Measure.map (FiniteJumpHistory.reverse T) forward.toMeasure, by
    exact (Measure.isProbabilityMeasure_map_iff
      (μ := forward.toMeasure) (f := FiniteJumpHistory.reverse T)
      (FiniteJumpHistory.measurable_reverse T).aemeasurable).2 inferInstance⟩

/-- Probability promotion leaves the underlying reversal pushforward unchanged. -/
@[simp]
theorem finiteStateMarkovJumpReversalProbabilityMeasure_toMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    (finiteStateMarkovJumpReversalProbabilityMeasure initial generator T hT).toMeasure =
      finiteStateMarkovJumpReversalDensityMeasure initial generator T :=
  rfl

/-- The reversal density measure has total mass one at every nonnegative horizon. -/
theorem finiteStateMarkovJumpReversalDensityMeasure_univ
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    finiteStateMarkovJumpReversalDensityMeasure initial generator T Set.univ = 1 := by
  change (finiteStateMarkovJumpReversalProbabilityMeasure
    initial generator T hT).toMeasure Set.univ = 1
  exact measure_univ

/-- The reversed jump law remains concentrated on the identical fixed-horizon physical carrier. -/
theorem ae_physicalAt_finiteStateMarkovJumpReversalDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) :
    ∀ᵐ history ∂finiteStateMarkovJumpReversalDensityMeasure initial generator T,
      history.PhysicalAt T := by
  unfold finiteStateMarkovJumpReversalDensityMeasure
  apply (ae_map_iff (FiniteJumpHistory.measurable_reverse T).aemeasurable
    (FiniteJumpHistory.measurableSet_physicalAt T)).2
  filter_upwards [
    ae_physicalAt_finiteStateMarkovJumpDensityMeasure initial generator T
  ] with history hPhysical
  exact (FiniteJumpHistory.physicalAt_reverse_iff T history).2 hPhysical

end FiniteMarkovProcesses.Probability
