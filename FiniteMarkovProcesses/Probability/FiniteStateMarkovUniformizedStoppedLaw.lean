/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpStoppedLaw
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedTrajectory

/-!
# Stopped laws of finite-state uniformized trajectories

This module stops the normalized uniformized tape on each measurable first-horizon-crossing slice
and maps it to the existing `FiniteJumpHistory` carrier. The resulting histories retain virtual
self-events. Its total mass is exactly the uniformized-tape probability of finite crossing.

Probability normalization is conditional on almost-sure crossing. The stopped measure is defined
without choosing a stopping value on trajectories that fail to cross the horizon.

## Main Results

- `finiteStateUniformizedStoppedHistoryMeasure`: countable stopped-tape pushforward retaining
  virtual self-events.
- `finiteStateUniformizedStoppedHistoryMeasure_univ_eq_crossing`: exact total-mass identity.
- `finiteStateUniformizedStoppedHistoryProbabilityMeasure`: probability promotion after explicit
  almost-sure crossing.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

open FiniteStateMarkovStoppedLaw

universe u

namespace FiniteStateMarkovUniformizedStoppedLaw

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Stopped uniformized history law on the common finite-history carrier. Repeated adjacent states
are retained as virtual self-events. -/
noncomputable def finiteStateUniformizedStoppedHistoryMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun eventCount : ℕ ↦
    Measure.map (finiteStateMarkovStoppedHistoryAt eventCount)
      ((finiteStateUniformizedTapeMeasure initial generator).restrict
        {tape | FirstCrossesJumpHorizonAt tape T eventCount})

/-- The stopped uniformized law's total mass is exactly the tape probability of crossing the
horizon in finite time. -/
theorem finiteStateUniformizedStoppedHistoryMeasure_univ_eq_crossing
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedStoppedHistoryMeasure initial generator T Set.univ =
      finiteStateUniformizedTapeMeasure initial generator
        {tape | CrossesJumpHorizon tape T} := by
  rw [finiteStateUniformizedStoppedHistoryMeasure,
    Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.map_apply
    (measurable_finiteStateMarkovStoppedHistoryAt (State := State) _)
    MeasurableSet.univ]
  simp_rw [preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [← measure_iUnion]
  · rw [iUnion_firstCrossesJumpHorizonAt]
  · intro first second hNe
    exact firstCrossesJumpHorizonAt_disjoint hNe
  · intro eventCount
    exact measurableSet_firstCrossesJumpHorizonAt T eventCount

/-- Almost-sure crossing promotes the stopped uniformized history measure to total mass one. -/
theorem finiteStateUniformizedStoppedHistoryMeasure_univ_of_ae_crosses
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (hCrosses :
      ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
        CrossesJumpHorizon tape T) :
    finiteStateUniformizedStoppedHistoryMeasure initial generator T Set.univ = 1 := by
  rw [finiteStateUniformizedStoppedHistoryMeasure_univ_eq_crossing]
  rw [ae_iff] at hCrosses
  have hCrossingCompl :
      finiteStateUniformizedTapeMeasure initial generator
        {tape | CrossesJumpHorizon tape T}ᶜ = 0 := by
    simpa only [Set.compl_ofPred] using hCrosses
  rw [measure_of_measure_compl_eq_zero hCrossingCompl, measure_univ]

/-- Bundled stopped uniformized probability law after the explicit almost-sure crossing gate. -/
noncomputable def finiteStateUniformizedStoppedHistoryProbabilityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (hCrosses :
      ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
        CrossesJumpHorizon tape T) :
    ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateUniformizedStoppedHistoryMeasure initial generator T,
    ⟨finiteStateUniformizedStoppedHistoryMeasure_univ_of_ae_crosses
      initial generator T hCrosses⟩⟩

/-- Probability promotion leaves the underlying stopped uniformized measure unchanged. -/
@[simp]
theorem finiteStateUniformizedStoppedHistoryProbabilityMeasure_toMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (hCrosses :
      ∀ᵐ tape ∂finiteStateUniformizedTapeMeasure initial generator,
        CrossesJumpHorizon tape T) :
    (finiteStateUniformizedStoppedHistoryProbabilityMeasure
      initial generator T hCrosses).toMeasure =
      finiteStateUniformizedStoppedHistoryMeasure initial generator T :=
  rfl

end FiniteStateMarkovUniformizedStoppedLaw

end FiniteMarkovProcesses.Probability
