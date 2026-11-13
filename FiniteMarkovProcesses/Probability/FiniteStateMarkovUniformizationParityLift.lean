/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDensityIdentification
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedTrajectory
public import FiniteMarkovProcesses.Probability.IonescuTulceaTrajectoryProjection

/-!
# Parity lift of a uniformized finite-state Markov chain

A common-clock uniformized chain may retain a virtual self-event. This module makes every such
event into a genuine jump by adjoining one Boolean parity bit and flipping it at every clock
event. The resulting object is an ordinary off-diagonal finite-state Markov generator, so the
canonical Gillespie trajectory and density theorems can be reused without duplicating them.

Forgetting parity retains every event and recovers the original uniformized transition and
holding laws. Deleting virtual self-events is a separate later operation.

## Main Results

- `FiniteStateMarkovGenerator.uniformizationParityLift`: the genuine-jump lifted generator.
- `FiniteStateMarkovGenerator.escapeRate_uniformizationParityLift`: its escape rate is the
  common uniformization clock.
- `finiteStateJumpDestinationPMF_uniformizationParityLift_flip`: its destination law is exactly
  the uniformized transition law with deterministic parity flip.
- `finiteStateHoldingTimeMeasure_uniformizationParityLift`: its holding law is the common clock.
- `map_finiteStateTimedStepKernel_uniformizationParityLift`: forgetting parity sends one lifted
  Gillespie step exactly to one uniformized step.
- `map_finiteStateMarkovJumpTapeMeasure_uniformizationParityLift`: forgetting parity sends the
  full lifted Gillespie tape exactly to the uniformized tape.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- Off-diagonal generator obtained by adjoining a parity bit that flips at every uniformized
event. The lifted event rate is the common clock times the corresponding uniformized transition
weight. -/
noncomputable def uniformizationParityLift
    (generator : FiniteStateMarkovGenerator State) :
    FiniteStateMarkovGenerator (State × Bool) where
  rate source target :=
    if target.2 = !source.2 then
      generator.uniformizationRate *
        generator.uniformizedTransitionWeight source.1 target.1
    else 0
  rate_self source := by simp

/-- A parity-flipping lifted rate is the common clock times the uniformized transition weight. -/
@[simp]
theorem uniformizationParityLift_rate_flip
    (generator : FiniteStateMarkovGenerator State) (source : State × Bool) (target : State) :
    (generator.uniformizationParityLift.rate source (target, !source.2)) =
      generator.uniformizationRate *
        generator.uniformizedTransitionWeight source.1 target := by
  simp [uniformizationParityLift]

/-- A transition that does not flip parity has zero lifted rate. -/
theorem uniformizationParityLift_rate_of_not_flip
    (generator : FiniteStateMarkovGenerator State) {source target : State × Bool}
    (hParity : target.2 ≠ !source.2) :
    generator.uniformizationParityLift.rate source target = 0 := by
  simp [uniformizationParityLift, hParity]

/-- Every lifted state has escape rate equal to the common uniformization clock. -/
@[simp]
theorem escapeRate_uniformizationParityLift
    (generator : FiniteStateMarkovGenerator State) (source : State × Bool) :
    generator.uniformizationParityLift.escapeRate source =
      generator.uniformizationRate := by
  classical
  rw [escapeRate]
  change (∑ target : State × Bool,
    if target.2 = !source.2 then
      generator.uniformizationRate *
        generator.uniformizedTransitionWeight source.1 target.1
    else 0) = _
  rw [Fintype.sum_prod_type]
  rw [show (∑ target : State, ∑ parity : Bool,
      if parity = !source.2 then
        generator.uniformizationRate *
          generator.uniformizedTransitionWeight source.1 target
      else 0) =
      ∑ target : State,
        generator.uniformizationRate *
          generator.uniformizedTransitionWeight source.1 target by
    congr with target
    cases source.2 <;> simp]
  rw [← Finset.mul_sum, generator.sum_uniformizedTransitionWeight]
  simp

/-- The lifted destination PMF at the forced opposite parity is exactly the original
uniformized transition PMF. -/
theorem finiteStateJumpDestinationPMF_uniformizationParityLift_flip
    (generator : FiniteStateMarkovGenerator State)
    (source : State × Bool) (target : State) :
    finiteStateJumpDestinationPMF generator.uniformizationParityLift source
        (target, !source.2) =
      generator.uniformizedTransitionPMF source.1 target := by
  rw [finiteStateJumpDestinationPMF_apply_of_ne_zero]
  · rw [generator.escapeRate_uniformizationParityLift]
    rw [generator.uniformizationParityLift_rate_flip]
    rw [mul_div_cancel_left₀]
    exact (generator.uniformizedTransitionPMF_apply source.1 target).symm
    exact generator.uniformizationRate_pos.ne'
  · rw [generator.escapeRate_uniformizationParityLift]
    exact generator.uniformizationRate_pos.ne'

/-- The lifted destination PMF gives zero mass to a parity that did not flip. -/
theorem finiteStateJumpDestinationPMF_uniformizationParityLift_of_not_flip
    (generator : FiniteStateMarkovGenerator State)
    {source target : State × Bool} (hParity : target.2 ≠ !source.2) :
    finiteStateJumpDestinationPMF generator.uniformizationParityLift source target = 0 := by
  rw [finiteStateJumpDestinationPMF_apply_of_ne_zero]
  · rw [generator.uniformizationParityLift_rate_of_not_flip hParity, zero_div]
    rfl
  · rw [generator.escapeRate_uniformizationParityLift]
    exact generator.uniformizationRate_pos.ne'

/-- Forgetting parity in the lifted destination law gives exactly the uniformized transition
law. -/
theorem map_finiteStateJumpDestinationPMF_uniformizationParityLift
    (generator : FiniteStateMarkovGenerator State) (source : State × Bool) :
    (finiteStateJumpDestinationPMF generator.uniformizationParityLift source).map Prod.fst =
      generator.uniformizedTransitionPMF source.1 := by
  ext target
  rw [PMF.map_apply, ENNReal.tsum_prod']
  rw [tsum_eq_single target]
  · simp only [ite_true, tsum_fintype, Fintype.sum_bool]
    rcases source with ⟨source, parity⟩
    cases parity
    · have hFlip :
          finiteStateJumpDestinationPMF generator.uniformizationParityLift
              (source, false) (target, true) =
            generator.uniformizedTransitionPMF source target := by
          simpa using
            finiteStateJumpDestinationPMF_uniformizationParityLift_flip
              generator (source, false) target
      have hSame :
          finiteStateJumpDestinationPMF generator.uniformizationParityLift
              (source, false) (target, false) = 0 := by
        apply finiteStateJumpDestinationPMF_uniformizationParityLift_of_not_flip
        simp
      rw [hFlip, hSame, add_zero]
    · have hSame :
          finiteStateJumpDestinationPMF generator.uniformizationParityLift
              (source, true) (target, true) = 0 := by
        apply finiteStateJumpDestinationPMF_uniformizationParityLift_of_not_flip
        simp
      have hFlip :
          finiteStateJumpDestinationPMF generator.uniformizationParityLift
              (source, true) (target, false) =
            generator.uniformizedTransitionPMF source target := by
          simpa using
            finiteStateJumpDestinationPMF_uniformizationParityLift_flip
              generator (source, true) target
      rw [hSame, hFlip, zero_add]
  · intro other hOther
    simp [hOther.symm]

end FiniteStateMarkovGenerator

/-- Lift an initial law to parity `false`. -/
noncomputable def finiteStateUniformizationParityInitial
    (initial : PMF State) : PMF (State × Bool) :=
  initial.map fun state ↦ (state, false)

omit [Fintype State] in
/-- The lifted initial law agrees with the original law on parity `false`. -/
@[simp]
theorem finiteStateUniformizationParityInitial_apply_false
    (initial : PMF State) (state : State) :
    finiteStateUniformizationParityInitial initial (state, false) = initial state := by
  classical
  rw [finiteStateUniformizationParityInitial, PMF.map_apply, tsum_eq_single state]
  · simp
  · intro other hOther
    simp only [Prod.mk.injEq, and_true, ite_eq_right_iff]
    intro hState
    exact (hOther hState.symm).elim

omit [DecidableEq State] in
/-- The lifted initial law has no mass on parity `true`. -/
@[simp]
theorem finiteStateUniformizationParityInitial_apply_true
    (initial : PMF State) (state : State) :
    finiteStateUniformizationParityInitial initial (state, true) = 0 := by
  rw [finiteStateUniformizationParityInitial, PMF.map_apply]
  simp

/-- Forgetting the fixed initial parity recovers the original initial law. -/
theorem map_finiteStateUniformizationParityInitial
    (initial : PMF State) :
    (finiteStateUniformizationParityInitial initial).map Prod.fst = initial := by
  ext state
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single state]
  · simp
  · intro other hOther
    simp [hOther.symm]

/-- The lifted Gillespie holding law is exactly the original common uniformization clock. -/
theorem finiteStateHoldingTimeMeasure_uniformizationParityLift
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (source : State × Bool) :
    finiteStateHoldingTimeMeasure generator.uniformizationParityLift T source =
      finiteStateUniformizedHoldingTimeMeasure generator := by
  rw [finiteStateHoldingTimeMeasure_eq_expMeasure]
  · rw [generator.escapeRate_uniformizationParityLift]
    rfl
  · rw [generator.escapeRate_uniformizationParityLift]
    exact_mod_cast generator.uniformizationRate_pos

/-- After exposing the lifted transition output, its holding kernel is the constant common-clock
kernel. -/
theorem finiteStateHoldingTimeKernel_uniformizationParityLift_comap
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    (finiteStateHoldingTimeKernel generator.uniformizationParityLift T).comap
        Prod.snd measurable_snd =
      Kernel.const ((State × Bool) × (State × Bool))
        (finiteStateUniformizedHoldingTimeMeasure generator) := by
  ext source waits hWaits
  rw [Kernel.comap_apply, Kernel.const_apply]
  exact congrArg (fun measure : Measure ℝ ↦ measure waits)
    (finiteStateHoldingTimeMeasure_uniformizationParityLift generator T source.2)

/-- One lifted Gillespie step is the product of its parity-flipping destination law and the
common holding clock. -/
theorem finiteStateTimedStepKernel_uniformizationParityLift_eq_prod
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (source : State × Bool) :
    finiteStateTimedStepKernel generator.uniformizationParityLift T source =
      (finiteStateJumpDestinationPMF
        generator.uniformizationParityLift source).toMeasure.prod
          (finiteStateUniformizedHoldingTimeMeasure generator) := by
  rw [finiteStateTimedStepKernel,
    finiteStateHoldingTimeKernel_uniformizationParityLift_comap]
  ext event hEvent
  rw [Kernel.compProd_apply hEvent, Measure.prod_apply hEvent]
  rfl

/-- The original uniformized step also has the destination-times-common-clock product form. -/
theorem finiteStateUniformizedTimedStepKernel_eq_prod
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State) (source : State) :
    finiteStateUniformizedTimedStepKernel generator source =
      (generator.uniformizedTransitionPMF source).toMeasure.prod
        (finiteStateUniformizedHoldingTimeMeasure generator) := by
  have hHoldingKernel :
      (finiteStateUniformizedHoldingTimeKernel generator).comap Prod.snd measurable_snd =
        Kernel.const (State × State)
          (finiteStateUniformizedHoldingTimeMeasure generator) := by
    ext statePair waits hWaits
    rw [Kernel.comap_apply, Kernel.const_apply]
    rfl
  rw [finiteStateUniformizedTimedStepKernel, hHoldingKernel]
  ext event hEvent
  rw [Kernel.compProd_apply hEvent, Measure.prod_apply hEvent]
  rfl

/-- Forget the parity coordinate of one timed lifted state while retaining its wait. -/
def finiteStateUniformizationTimedStateProjection :
    ((State × Bool) × ℝ) → State × ℝ :=
  fun timedState ↦ (timedState.1.1, timedState.2)

omit [Fintype State] [DecidableEq State] in
/-- Forgetting parity from one timed lifted state is measurable. -/
@[fun_prop]
theorem measurable_finiteStateUniformizationTimedStateProjection
    [MeasurableSpace State] :
    Measurable (finiteStateUniformizationTimedStateProjection (State := State)) := by
  unfold finiteStateUniformizationTimedStateProjection
  exact (measurable_fst.comp measurable_fst).prodMk measurable_snd

/-- Forgetting parity maps one lifted Gillespie step exactly to one uniformized step. -/
theorem map_finiteStateTimedStepKernel_uniformizationParityLift
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (source : State × Bool) :
    Measure.map finiteStateUniformizationTimedStateProjection
        (finiteStateTimedStepKernel generator.uniformizationParityLift T source) =
      finiteStateUniformizedTimedStepKernel generator source.1 := by
  rw [finiteStateTimedStepKernel_uniformizationParityLift_eq_prod,
    finiteStateUniformizedTimedStepKernel_eq_prod]
  have hDestination :
      Measure.map (fun liftedState : State × Bool ↦ liftedState.1)
          (finiteStateJumpDestinationPMF
            generator.uniformizationParityLift source).toMeasure =
        (generator.uniformizedTransitionPMF source.1).toMeasure := by
    rw [PMF.toMeasure_map _ _ measurable_fst,
      generator.map_finiteStateJumpDestinationPMF_uniformizationParityLift]
  calc
    Measure.map finiteStateUniformizationTimedStateProjection
        ((finiteStateJumpDestinationPMF
            generator.uniformizationParityLift source).toMeasure.prod
          (finiteStateUniformizedHoldingTimeMeasure generator)) =
      Measure.map (Prod.map (fun liftedState : State × Bool ↦ liftedState.1) id)
        ((finiteStateJumpDestinationPMF
            generator.uniformizationParityLift source).toMeasure.prod
          (finiteStateUniformizedHoldingTimeMeasure generator)) := by
        rfl
    _ = (Measure.map (fun liftedState : State × Bool ↦ liftedState.1)
          (finiteStateJumpDestinationPMF
            generator.uniformizationParityLift source).toMeasure).prod
        (Measure.map id (finiteStateUniformizedHoldingTimeMeasure generator)) := by
      rw [Measure.map_prod_map _ _ measurable_fst measurable_id]
    _ = _ := by rw [hDestination, Measure.map_id]

/-- The lifted initial timed-state law is the product of its parity-fixed state law and the
common holding clock. -/
theorem finiteStateInitialTimedStateMeasure_uniformizationParityLift_eq_prod
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateInitialTimedStateMeasure
        (finiteStateUniformizationParityInitial initial)
        generator.uniformizationParityLift T =
      (finiteStateUniformizationParityInitial initial).toMeasure.prod
        (finiteStateUniformizedHoldingTimeMeasure generator) := by
  have hHolding :
      finiteStateHoldingTimeKernel generator.uniformizationParityLift T =
        Kernel.const (State × Bool)
          (finiteStateUniformizedHoldingTimeMeasure generator) := by
    ext source waits hWaits
    rw [Kernel.const_apply]
    exact congrArg (fun measure : Measure ℝ ↦ measure waits)
      (finiteStateHoldingTimeMeasure_uniformizationParityLift generator T source)
  rw [finiteStateInitialTimedStateMeasure, hHolding, Measure.compProd_const]

omit [DecidableEq State] in
/-- The uniformized initial timed-state law is the product of its initial state law and the
common holding clock. -/
theorem finiteStateUniformizedInitialTimedStateMeasure_eq_prod
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) :
    finiteStateUniformizedInitialTimedStateMeasure initial generator =
      initial.toMeasure.prod
        (finiteStateUniformizedHoldingTimeMeasure generator) := by
  unfold finiteStateUniformizedInitialTimedStateMeasure
  have hHolding :
      finiteStateUniformizedHoldingTimeKernel generator =
        Kernel.const State (finiteStateUniformizedHoldingTimeMeasure generator) := by
    ext source waits hWaits
    rw [Kernel.const_apply]
    rfl
  rw [hHolding, Measure.compProd_const]

/-- Forgetting parity maps the lifted initial timed-state law exactly to the uniformized initial
timed-state law. -/
theorem map_finiteStateInitialTimedStateMeasure_uniformizationParityLift
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map finiteStateUniformizationTimedStateProjection
        (finiteStateInitialTimedStateMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T) =
      finiteStateUniformizedInitialTimedStateMeasure initial generator := by
  rw [finiteStateInitialTimedStateMeasure_uniformizationParityLift_eq_prod,
    finiteStateUniformizedInitialTimedStateMeasure_eq_prod]
  have hInitial :
      Measure.map (fun liftedState : State × Bool ↦ liftedState.1)
          (finiteStateUniformizationParityInitial initial).toMeasure =
        initial.toMeasure := by
    rw [PMF.toMeasure_map _ _ measurable_fst,
      map_finiteStateUniformizationParityInitial]
  calc
    Measure.map finiteStateUniformizationTimedStateProjection
        ((finiteStateUniformizationParityInitial initial).toMeasure.prod
          (finiteStateUniformizedHoldingTimeMeasure generator)) =
      Measure.map (Prod.map (fun liftedState : State × Bool ↦ liftedState.1) id)
        ((finiteStateUniformizationParityInitial initial).toMeasure.prod
          (finiteStateUniformizedHoldingTimeMeasure generator)) := by
        rfl
    _ = (Measure.map (fun liftedState : State × Bool ↦ liftedState.1)
          (finiteStateUniformizationParityInitial initial).toMeasure).prod
        (Measure.map id (finiteStateUniformizedHoldingTimeMeasure generator)) := by
      rw [Measure.map_prod_map _ _ measurable_fst measurable_id]
    _ = _ := by rw [hInitial, Measure.map_id]

/-- Forgetting parity maps the lifted singleton trajectory seed exactly to the uniformized seed. -/
theorem map_finiteStateMarkovJumpTrajectorySeedMeasure_uniformizationParityLift
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map
        (finiteTrajectoryCoordinateMap
          finiteStateUniformizationTimedStateProjection 0)
        (finiteStateMarkovJumpTrajectorySeedMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T) =
      finiteStateUniformizedTrajectorySeedMeasure initial generator := by
  rw [finiteStateMarkovJumpTrajectorySeedMeasure,
    finiteStateUniformizedTrajectorySeedMeasure]
  rw [Measure.map_map
    (measurable_finiteTrajectoryCoordinateMap
      finiteStateUniformizationTimedStateProjection
      measurable_finiteStateUniformizationTimedStateProjection 0)
    measurable_finiteStateMarkovJumpTrajectorySeed]
  rw [show finiteTrajectoryCoordinateMap
      finiteStateUniformizationTimedStateProjection 0 ∘
        finiteStateMarkovJumpTrajectorySeed =
      finiteStateMarkovJumpTrajectorySeed ∘
        finiteStateUniformizationTimedStateProjection by rfl]
  rw [← Measure.map_map
    measurable_finiteStateMarkovJumpTrajectorySeed
    measurable_finiteStateUniformizationTimedStateProjection]
  rw [map_finiteStateInitialTimedStateMeasure_uniformizationParityLift]

/-- Forgetting parity maps every lifted history-dependent Gillespie row exactly to the
corresponding uniformized trajectory row. -/
theorem map_finiteStateMarkovJumpTrajectoryStepKernel_uniformizationParityLift
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (n : ℕ) (history : (i : Finset.Iic n) → (State × Bool) × ℝ) :
    Measure.map finiteStateUniformizationTimedStateProjection
        (finiteStateMarkovJumpTrajectoryStepKernel
          generator.uniformizationParityLift T n history) =
      finiteStateUniformizedTrajectoryStepKernel generator n
        (finiteTrajectoryCoordinateMap
          finiteStateUniformizationTimedStateProjection n history) := by
  rw [finiteStateMarkovJumpTrajectoryStepKernel, Kernel.comap_apply]
  rw [finiteStateUniformizedTrajectoryStepKernel, Kernel.comap_apply]
  change Measure.map finiteStateUniformizationTimedStateProjection
      (finiteStateTimedStepKernel generator.uniformizationParityLift T
        (finiteTimedTrajectoryCurrentState n history)) =
    finiteStateUniformizedTimedStepKernel generator
      (finiteTimedTrajectoryCurrentState n history).1
  exact map_finiteStateTimedStepKernel_uniformizationParityLift
    generator T (finiteTimedTrajectoryCurrentState n history)

/-- Forgetting the auxiliary parity coordinate maps the full normalized lifted Gillespie tape
exactly to the normalized uniformized tape. -/
theorem map_finiteStateMarkovJumpTapeMeasure_uniformizationParityLift
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map
        (trajectoryCoordinateMap finiteStateUniformizationTimedStateProjection)
        (finiteStateMarkovJumpTapeMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T) =
      finiteStateUniformizedTapeMeasure initial generator := by
  change Measure.map
      (trajectoryCoordinateMap finiteStateUniformizationTimedStateProjection)
      (ionescuTulceaTrajectoryMeasure
        (finiteStateMarkovJumpTrajectoryStepKernel
          generator.uniformizationParityLift T)
        (finiteStateMarkovJumpTrajectorySeedMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T)) =
    ionescuTulceaTrajectoryMeasure
      (finiteStateUniformizedTrajectoryStepKernel generator)
      (finiteStateUniformizedTrajectorySeedMeasure initial generator)
  exact map_ionescuTulceaTrajectoryMeasure
    (finiteStateMarkovJumpTrajectoryStepKernel
      generator.uniformizationParityLift T)
    (finiteStateUniformizedTrajectoryStepKernel generator)
    (finiteStateMarkovJumpTrajectorySeedMeasure
      (finiteStateUniformizationParityInitial initial)
      generator.uniformizationParityLift T)
    (finiteStateUniformizedTrajectorySeedMeasure initial generator)
    finiteStateUniformizationTimedStateProjection
    measurable_finiteStateUniformizationTimedStateProjection
    (map_finiteStateMarkovJumpTrajectorySeedMeasure_uniformizationParityLift
      initial generator T)
    (map_finiteStateMarkovJumpTrajectoryStepKernel_uniformizationParityLift
      generator T)

end FiniteMarkovProcesses.Probability
