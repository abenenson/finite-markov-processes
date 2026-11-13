/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDensityIdentification

/-!
# Initial-state marginal of a finite-state Markov jump law

This module proves that the complete finite-horizon jump-history law retains its prospectively
specified initial PMF exactly.  The proof first reads the initial coordinate of the normalized
Gillespie tape, then transports that marginal through the countable stopped-history construction
and the exact stopped-law-to-density-law identification.

## Main declarations

- `finiteStateMarkovJumpTapeInitialStateMarginal`: the infinite tape starts from the supplied PMF.
- `finiteStateMarkovStoppedHistoryInitialStateMarginal`: stopping preserves that initial state.
- `finiteStateMarkovJumpDensityMeasureInitialStateMarginal`: the canonical complete-history
  density measure has the supplied initial-state marginal.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Reading the first state of the infinite Gillespie tape recovers the supplied initial PMF. -/
theorem finiteStateMarkovJumpTapeInitialStateMarginal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (duration : ℝ) :
    Measure.map (fun tape : ℕ → State × ℝ => (tape 0).1)
        (finiteStateMarkovJumpTapeMeasure initial generator duration) =
      initial.toMeasure := by
  let readInitial : (Fin 1 → State × ℝ) → State :=
    fun finitePrefix => (finitePrefix 0).1
  have hFactor :
      (fun tape : ℕ → State × ℝ => (tape 0).1) =
        readInitial ∘ finiteStateMarkovTapePrefix 0 := rfl
  rw [hFactor, ← Measure.map_map (by fun_prop : Measurable readInitial)
    (measurable_finiteStateMarkovTapePrefix 0)]
  rw [finiteStateMarkovJumpTapePrefixMeasure_eq_timedPrefixMeasure]
  rw [finiteStateMarkovTimedPrefixMeasure]
  rw [Measure.map_map (by fun_prop : Measurable readInitial)
    measurable_finiteStateMarkovTimedPrefixSeed]
  change (initial.toMeasure ⊗ₘ finiteStateHoldingTimeKernel generator duration).fst =
    initial.toMeasure
  rw [Measure.fst_compProd]

/-- The countable stopped-history construction preserves the supplied initial-state marginal. -/
theorem finiteStateMarkovStoppedHistoryInitialStateMarginal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    Measure.map FiniteJumpHistory.initialState
        (FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
          initial generator duration) =
      initial.toMeasure := by
  let tapeInitialState : (ℕ → State × ℝ) → State := fun tape => (tape 0).1
  let crossingSet : ℕ → Set (ℕ → State × ℝ) :=
    fun jumpCount => {tape | FirstCrossesJumpHorizonAt tape duration jumpCount}
  have hTapeInitialStateMeasurable : Measurable tapeInitialState := by
    fun_prop
  have hStoppedInitialState :
      ∀ jumpCount,
        FiniteJumpHistory.initialState ∘
            FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryAt jumpCount =
          tapeInitialState := by
    intro jumpCount
    funext tape
    rfl
  have hRestrictedSum :
      Measure.sum (fun jumpCount =>
          (finiteStateMarkovJumpTapeMeasure initial generator duration).restrict
            (crossingSet jumpCount)) =
        finiteStateMarkovJumpTapeMeasure initial generator duration := by
    rw [← Measure.restrict_iUnion]
    · rw [FiniteStateMarkovStoppedLaw.iUnion_firstCrossesJumpHorizonAt]
      exact Measure.restrict_eq_self_of_ae_mem
        (FiniteStateMarkovJumpTrajectory.ae_crossesJumpHorizon_finiteStateMarkovJumpTapeMeasure
          initial generator duration hDuration)
    · intro first second hNe
      exact FiniteStateMarkovStoppedLaw.firstCrossesJumpHorizonAt_disjoint hNe
    · intro jumpCount
      exact
        FiniteStateMarkovStoppedLaw.measurableSet_firstCrossesJumpHorizonAt duration jumpCount
  unfold FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_initialState.aemeasurable]
  simp_rw [Measure.map_map FiniteJumpHistory.measurable_initialState
    (FiniteStateMarkovStoppedLaw.measurable_finiteStateMarkovStoppedHistoryAt _)]
  simp_rw [hStoppedInitialState]
  rw [← Measure.map_sum hTapeInitialStateMeasurable.aemeasurable, hRestrictedSum]
  exact finiteStateMarkovJumpTapeInitialStateMarginal initial generator duration

/-- The canonical complete finite-state Markov jump density measure has exactly the supplied
initial-state marginal at every nonnegative observation duration. -/
theorem finiteStateMarkovJumpDensityMeasureInitialStateMarginal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    Measure.map FiniteJumpHistory.initialState
        (finiteStateMarkovJumpDensityMeasure initial generator duration) =
      initial.toMeasure := by
  rw [← finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    initial generator duration hDuration]
  exact finiteStateMarkovStoppedHistoryInitialStateMarginal
    initial generator duration hDuration

end FiniteMarkovProcesses.Probability
