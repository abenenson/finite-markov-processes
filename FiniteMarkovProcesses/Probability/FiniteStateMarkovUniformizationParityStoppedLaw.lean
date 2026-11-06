/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizationParityLift
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedStoppedLaw

/-!
# Stopped-law transport through the uniformization parity lift

This module forgets the auxiliary parity coordinate on finite jump histories. First-horizon
crossing depends only on waits, and fixed-count stopping commutes literally with parity
projection. Therefore the full stopped lifted Gillespie law pushes forward exactly to the
stopped uniformized law, including every retained virtual self-event.

## Main Results

- `finiteStateUniformizationHistoryProjection`: forget parity on a finite event history.
- `map_finiteStateMarkovStoppedHistoryMeasure_uniformizationParityLift`: exact stopped-law
  pushforward from the lifted physical process to the uniformized process.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open FiniteStateMarkovStoppedLaw

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Forget the auxiliary parity coordinate while retaining every event and event time. -/
def finiteStateUniformizationHistoryProjection :
    FiniteJumpHistory (State × Bool) → FiniteJumpHistory State
  | ⟨n, states, times⟩ => ⟨n, fun i ↦ (states i).1, times⟩

omit [Fintype State] [DecidableEq State] [MeasurableSingletonClass State] in
/-- Forgetting parity on finite histories is measurable. -/
theorem measurable_finiteStateUniformizationHistoryProjection :
    Measurable (finiteStateUniformizationHistoryProjection (State := State)) := by
  rw [measurable_sigma_iff]
  intro n
  have hSigma : Measurable
      (@Sigma.mk ℕ (fun count ↦
        (Fin (count + 1) → State) × (Fin count → ℝ)) n) := by
    apply Measurable.of_comap_le
    exact (MeasurableSpace.comap_mono (iInf_le _ n)).trans
      MeasurableSpace.comap_map_le
  apply hSigma.comp
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    exact ((measurable_pi_apply i).comp measurable_fst).fst
  · exact measurable_snd

omit [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State] in
/-- First-horizon crossing is unchanged by forgetting parity. -/
theorem firstCrossesJumpHorizonAt_trajectoryCoordinateMap_projection_iff
    (tape : ℕ → (State × Bool) × ℝ) (T : ℝ) (n : ℕ) :
    FirstCrossesJumpHorizonAt
        (trajectoryCoordinateMap finiteStateUniformizationTimedStateProjection tape) T n ↔
      FirstCrossesJumpHorizonAt tape T n := by
  rfl

omit [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State] in
/-- Fixed-count stopping commutes with forgetting parity. -/
theorem finiteStateUniformizationHistoryProjection_stoppedHistoryAt
    (tape : ℕ → (State × Bool) × ℝ) (n : ℕ) :
    finiteStateUniformizationHistoryProjection
        (finiteStateMarkovStoppedHistoryAt n tape) =
      finiteStateMarkovStoppedHistoryAt n
        (trajectoryCoordinateMap finiteStateUniformizationTimedStateProjection tape) := by
  rfl

/-- Forgetting parity sends the full stopped lifted Gillespie law exactly to the stopped
uniformized law. -/
theorem map_finiteStateMarkovStoppedHistoryMeasure_uniformizationParityLift
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map finiteStateUniformizationHistoryProjection
        (FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T) =
      FiniteStateMarkovUniformizedStoppedLaw.finiteStateUniformizedStoppedHistoryMeasure
        initial generator T := by
  rw [FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure,
    FiniteStateMarkovUniformizedStoppedLaw.finiteStateUniformizedStoppedHistoryMeasure]
  rw [Measure.map_sum
    measurable_finiteStateUniformizationHistoryProjection.aemeasurable]
  congr 1
  funext n
  rw [Measure.map_map measurable_finiteStateUniformizationHistoryProjection
    (measurable_finiteStateMarkovStoppedHistoryAt n)]
  rw [show finiteStateUniformizationHistoryProjection ∘
      finiteStateMarkovStoppedHistoryAt n =
    finiteStateMarkovStoppedHistoryAt n ∘
      trajectoryCoordinateMap finiteStateUniformizationTimedStateProjection by
    funext tape
    exact finiteStateUniformizationHistoryProjection_stoppedHistoryAt tape n]
  rw [← Measure.map_map
    (measurable_finiteStateMarkovStoppedHistoryAt n)
    (measurable_trajectoryCoordinateMap
      finiteStateUniformizationTimedStateProjection
      measurable_finiteStateUniformizationTimedStateProjection)]
  have hEvent :
      (trajectoryCoordinateMap
        (finiteStateUniformizationTimedStateProjection (State := State))) ⁻¹'
          {tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T n} =
        {tape : ℕ → (State × Bool) × ℝ |
          FirstCrossesJumpHorizonAt tape T n} := by
    ext tape
    exact firstCrossesJumpHorizonAt_trajectoryCoordinateMap_projection_iff tape T n
  rw [← hEvent]
  rw [← Measure.restrict_map
    (measurable_trajectoryCoordinateMap
      finiteStateUniformizationTimedStateProjection
      measurable_finiteStateUniformizationTimedStateProjection)
    (measurableSet_firstCrossesJumpHorizonAt T n)]
  rw [map_finiteStateMarkovJumpTapeMeasure_uniformizationParityLift]

end FiniteMarkovProcesses.Probability
