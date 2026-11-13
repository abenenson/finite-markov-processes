/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Algebra.BigOperators.Fin
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpTimedStateSlice

/-!
# Finite timed-prefix laws for finite-state jump processes

This module gives a recursion-native finite-dimensional marginal of the normalized Gillespie
construction. A prefix is indexed by `Fin (n + 1)`, and the successor law appends one normalized
state-and-wait transition. The carrier is designed for exact fixed-state-word cylinder
calculations before transport to cumulative jump-time coordinates.

## Main results

- `appendFiniteStateTimedState`: append one timed state to a finite trajectory.
- `finiteStateMarkovTimedPrefixMeasure`: the normalized recursive timed-prefix law.
- `finiteStateMarkovTimedPrefixMeasure_isProbabilityMeasure`: exact prefix normalization.
- `finiteStateMarkovStateWordProbability`: the discrete probability of a fixed state word.
- `finiteStateMarkovStateWordProbability_succ`: its exact one-transition recursion.
- `finiteStateMarkovTimedPrefixWaitingTimes_stateWordSlice`: the complete fixed-word waiting-time
  product measure.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Append one timed state to a finite timed trajectory. -/
def appendFiniteStateTimedState {n : ℕ}
    (trajectory : Fin (n + 1) → State × ℝ) (next : State × ℝ) :
    Fin (n + 2) → State × ℝ :=
  Fin.lastCases next trajectory

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Appending one timed state is measurable. -/
theorem measurable_appendFiniteStateTimedState (n : ℕ) :
    Measurable (fun pair : (Fin (n + 1) → State × ℝ) × (State × ℝ) =>
      appendFiniteStateTimedState pair.1 pair.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [appendFiniteStateTimedState] using measurable_snd
  · simpa [appendFiniteStateTimedState, Function.comp_def] using
      (measurable_pi_apply j).comp measurable_fst

/-- State occupied by the last dwell in a finite timed trajectory. -/
def finiteStateTimedPrefixCurrentState (n : ℕ)
    (trajectory : Fin (n + 1) → State × ℝ) : State :=
  (trajectory (Fin.last n)).1

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The current-state readout on a finite timed trajectory is measurable. -/
theorem measurable_finiteStateTimedPrefixCurrentState (n : ℕ) :
    Measurable (finiteStateTimedPrefixCurrentState (State := State) n) :=
  (measurable_pi_apply (Fin.last n)).fst

/-- One normalized timed transition from the current state of a finite timed prefix. -/
noncomputable def finiteStateMarkovTimedPrefixStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ) :
    Kernel (Fin (n + 1) → State × ℝ) (State × ℝ) :=
  (finiteStateTimedStepKernel generator T).comap
    (finiteStateTimedPrefixCurrentState n)
    (measurable_finiteStateTimedPrefixCurrentState n)

/-- The original timed step kernel read from the last state of a finite prefix is Markov. -/
noncomputable instance instIsMarkovKernelFiniteStateMarkovTimedPrefixStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ) :
    IsMarkovKernel (finiteStateMarkovTimedPrefixStepKernel generator T n) := by
  unfold finiteStateMarkovTimedPrefixStepKernel
  infer_instance

/-- Embed one timed state as a one-coordinate `Fin` prefix. -/
def finiteStateMarkovTimedPrefixSeed
    (timedState : State × ℝ) : Fin 1 → State × ℝ :=
  fun _ => timedState

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The one-coordinate `Fin` prefix embedding is measurable. -/
theorem measurable_finiteStateMarkovTimedPrefixSeed :
    Measurable (finiteStateMarkovTimedPrefixSeed (State := State)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_id

/-- Normalized recursive law of the first `n + 1` occupied states and holding durations. -/
noncomputable def finiteStateMarkovTimedPrefixMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    (n : ℕ) → Measure (Fin (n + 1) → State × ℝ)
  | 0 => (finiteStateInitialTimedStateMeasure initial generator T).map
      finiteStateMarkovTimedPrefixSeed
  | n + 1 => Measure.map
      (fun pair => appendFiniteStateTimedState pair.1 pair.2)
      ((finiteStateMarkovTimedPrefixMeasure initial generator T n) ⊗ₘ
        finiteStateMarkovTimedPrefixStepKernel generator T n)

/-- Every finite timed-prefix law is exactly normalized. -/
noncomputable instance finiteStateMarkovTimedPrefixMeasure_isProbabilityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    IsProbabilityMeasure (finiteStateMarkovTimedPrefixMeasure initial generator T n) := by
  induction n with
  | zero =>
      rw [finiteStateMarkovTimedPrefixMeasure]
      exact (Measure.isProbabilityMeasure_map_iff
        measurable_finiteStateMarkovTimedPrefixSeed.aemeasurable).2 inferInstance
  | succ n inductionHypothesis =>
      rw [finiteStateMarkovTimedPrefixMeasure]
      exact (Measure.isProbabilityMeasure_map_iff
        (measurable_appendFiniteStateTimedState n).aemeasurable).2 inferInstance

/-- Measurable state-and-wait rectangle on a finite timed trajectory. -/
def FiniteStateTimedPrefixMatches {n : ℕ}
    (states : Fin (n + 1) → State) (waitSets : Fin (n + 1) → Set ℝ) :
    Set (Fin (n + 1) → State × ℝ) :=
  {trajectory | ∀ i, (trajectory i).1 = states i ∧ (trajectory i).2 ∈ waitSets i}

omit [Fintype State] in
/-- A finite timed state-and-wait rectangle is measurable when every wait set is measurable. -/
theorem measurableSet_finiteStateTimedPrefixMatches {n : ℕ}
    (states : Fin (n + 1) → State) (waitSets : Fin (n + 1) → Set ℝ)
    (hWaitSets : ∀ i, MeasurableSet (waitSets i)) :
    MeasurableSet (FiniteStateTimedPrefixMatches states waitSets) := by
  unfold FiniteStateTimedPrefixMatches
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.inter
  · exact ((measurableSet_singleton (states i)).preimage
      (measurable_pi_apply i).fst)
  · exact (hWaitSets i).preimage (measurable_pi_apply i).snd

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Matching an appended timed trajectory is equivalent to matching the old prefix and the new
last coordinate separately. -/
theorem appendFiniteStateTimedState_mem_matches_iff {n : ℕ}
    (states : Fin (n + 2) → State) (waitSets : Fin (n + 2) → Set ℝ)
    (trajectory : Fin (n + 1) → State × ℝ) (next : State × ℝ) :
    appendFiniteStateTimedState trajectory next ∈
        FiniteStateTimedPrefixMatches states waitSets ↔
      trajectory ∈ FiniteStateTimedPrefixMatches
          (fun i => states i.castSucc) (fun i => waitSets i.castSucc) ∧
        next.1 = states (Fin.last (n + 1)) ∧
          next.2 ∈ waitSets (Fin.last (n + 1)) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [appendFiniteStateTimedState] using h i.castSucc
    · simpa [appendFiniteStateTimedState] using h (Fin.last (n + 1))
  · rintro ⟨hTrajectory, hNext⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendFiniteStateTimedState] using hNext
    · simpa [appendFiniteStateTimedState] using hTrajectory j

/-- Discrete probability of a fixed state word under the normalized jump-destination chain. -/
noncomputable def finiteStateMarkovStateWordProbability
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) : ℝ≥0∞ :=
  initial (states 0) *
    ∏ i : Fin n,
      finiteStateJumpDestinationPMF generator (states i.castSucc) (states i.succ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The state-word probability at length one is the initial point mass. -/
@[simp]
theorem finiteStateMarkovStateWordProbability_zero
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (states : Fin 1 → State) :
    finiteStateMarkovStateWordProbability initial generator states = initial (states 0) := by
  simp [finiteStateMarkovStateWordProbability]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Appending one state multiplies the state-word probability by its physical destination
probability. -/
theorem finiteStateMarkovStateWordProbability_succ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 2) → State) :
    finiteStateMarkovStateWordProbability initial generator states =
      finiteStateMarkovStateWordProbability initial generator
          (fun i : Fin (n + 1) => states i.castSucc) *
        finiteStateJumpDestinationPMF generator
          (states (Fin.last n).castSucc) (states (Fin.last (n + 1))) := by
  simp only [finiteStateMarkovStateWordProbability, Fin.prod_univ_castSucc,
    Fin.castSucc_zero, Fin.succ_last]
  rw [mul_assoc]
  congr 2

/-- Exact fixed-state-word cylinder formula for every finite timed prefix. The discrete state-word
probability and all state-dependent holding-time factors remain visibly separate. -/
theorem finiteStateMarkovTimedPrefixMeasure_matches
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) (states : Fin (n + 1) → State)
    (waitSets : Fin (n + 1) → Set ℝ)
    (hWaitSets : ∀ i, MeasurableSet (waitSets i)) :
    finiteStateMarkovTimedPrefixMeasure initial generator T n
        (FiniteStateTimedPrefixMatches states waitSets) =
      finiteStateMarkovStateWordProbability initial generator states *
        ∏ i, finiteStateHoldingTimeMeasure generator T (states i) (waitSets i) := by
  induction n with
  | zero =>
      have hSlice := finiteStateInitialTimedStateMeasure_stateWaitSet
        initial generator T (states 0) (waitSets 0) (hWaitSets 0)
      rw [finiteStateMarkovTimedPrefixMeasure, Measure.map_apply]
      · convert hSlice using 1
        · congr 1
          ext timedState
          simp only [Set.mem_preimage, FiniteStateTimedPrefixMatches, Set.mem_ofPred_eq,
            finiteStateMarkovTimedPrefixSeed]
          constructor
          · intro h
            simpa using h 0
          · intro h i
            simpa [Fin.eq_zero i] using h
        · simp [finiteStateMarkovStateWordProbability]
      · exact measurable_finiteStateMarkovTimedPrefixSeed
      · exact measurableSet_finiteStateTimedPrefixMatches states waitSets hWaitSets
  | succ n inductionHypothesis =>
      let oldStates : Fin (n + 1) → State := fun i => states i.castSucc
      let oldWaitSets : Fin (n + 1) → Set ℝ := fun i => waitSets i.castSucc
      let lastState := states (Fin.last (n + 1))
      let lastWaitSet := waitSets (Fin.last (n + 1))
      let oldMatch := FiniteStateTimedPrefixMatches oldStates oldWaitSets
      have hOldWaitSets : ∀ i, MeasurableSet (oldWaitSets i) :=
        fun i => hWaitSets i.castSucc
      have hOldMatch : MeasurableSet oldMatch :=
        measurableSet_finiteStateTimedPrefixMatches oldStates oldWaitSets hOldWaitSets
      rw [finiteStateMarkovTimedPrefixMeasure]
      rw [Measure.map_apply (measurable_appendFiniteStateTimedState n)
        (measurableSet_finiteStateTimedPrefixMatches states waitSets hWaitSets)]
      rw [Measure.compProd_apply
        ((measurableSet_finiteStateTimedPrefixMatches states waitSets hWaitSets).preimage
          (measurable_appendFiniteStateTimedState n))]
      have hStep (trajectory : Fin (n + 1) → State × ℝ) :
          finiteStateMarkovTimedPrefixStepKernel generator T n trajectory
              (Prod.mk trajectory ⁻¹'
                ((fun pair => appendFiniteStateTimedState pair.1 pair.2) ⁻¹'
                  FiniteStateTimedPrefixMatches states waitSets)) =
            oldMatch.indicator
              (fun _ => finiteStateJumpDestinationPMF generator
                (oldStates (Fin.last n)) lastState *
                  finiteStateHoldingTimeMeasure generator T lastState lastWaitSet)
              trajectory := by
        by_cases hTrajectory : trajectory ∈ oldMatch
        · rw [Set.indicator_of_mem hTrajectory]
          have hCurrent :
              finiteStateTimedPrefixCurrentState n trajectory = oldStates (Fin.last n) :=
            hTrajectory (Fin.last n) |>.1
          have hPreimage :
              Prod.mk trajectory ⁻¹'
                  ((fun pair => appendFiniteStateTimedState pair.1 pair.2) ⁻¹'
                    FiniteStateTimedPrefixMatches states waitSets) =
                {next | next.1 = lastState ∧ next.2 ∈ lastWaitSet} := by
            ext next
            rw [Set.mem_preimage, Set.mem_preimage]
            rw [appendFiniteStateTimedState_mem_matches_iff]
            simp [hTrajectory, oldMatch, oldStates, oldWaitSets, lastState, lastWaitSet]
          rw [hPreimage]
          unfold finiteStateMarkovTimedPrefixStepKernel
          rw [Kernel.comap_apply]
          rw [hCurrent]
          exact finiteStateTimedStepKernel_stateWaitSet generator T
            (oldStates (Fin.last n)) lastState lastWaitSet
            (hWaitSets (Fin.last (n + 1)))
        · rw [Set.indicator_of_notMem hTrajectory]
          have hPreimage :
              Prod.mk trajectory ⁻¹'
                  ((fun pair => appendFiniteStateTimedState pair.1 pair.2) ⁻¹'
                    FiniteStateTimedPrefixMatches states waitSets) = ∅ := by
            ext next
            simp only [Set.mem_preimage, Set.notMem_empty, iff_false]
            intro hAppend
            apply hTrajectory
            exact (appendFiniteStateTimedState_mem_matches_iff
              states waitSets trajectory next).1 hAppend |>.1
          rw [hPreimage]
          simp
      simp_rw [hStep]
      rw [lintegral_indicator hOldMatch]
      simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      rw [inductionHypothesis oldStates oldWaitSets hOldWaitSets]
      rw [finiteStateMarkovStateWordProbability_succ]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      simp only [oldStates, oldWaitSets, lastState, lastWaitSet]
      ac_rfl

/-- Waiting-time vector extracted from a finite timed trajectory. -/
def finiteStateTimedPrefixWaitingTimes {n : ℕ}
    (trajectory : Fin (n + 1) → State × ℝ) : Fin (n + 1) → ℝ :=
  fun i => (trajectory i).2

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The finite timed-prefix waiting-time readout is measurable. -/
theorem measurable_finiteStateTimedPrefixWaitingTimes (n : ℕ) :
    Measurable (finiteStateTimedPrefixWaitingTimes (State := State) (n := n)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i).snd

/-- Finite timed trajectories with one prescribed complete state word. -/
def FiniteStateTimedPrefixHasStateWord {n : ℕ}
    (states : Fin (n + 1) → State) : Set (Fin (n + 1) → State × ℝ) :=
  {trajectory | ∀ i, (trajectory i).1 = states i}

omit [Fintype State] in
/-- A fixed finite timed-prefix state-word event is measurable. -/
theorem measurableSet_finiteStateTimedPrefixHasStateWord {n : ℕ}
    (states : Fin (n + 1) → State) :
    MeasurableSet (FiniteStateTimedPrefixHasStateWord states) := by
  unfold FiniteStateTimedPrefixHasStateWord
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((measurableSet_singleton (states i)).preimage (measurable_pi_apply i).fst)

/-- On a fixed state word, the complete waiting-time vector has the product of the corresponding
state-dependent holding laws, scaled by the discrete probability of that word. -/
theorem finiteStateMarkovTimedPrefixWaitingTimes_stateWordSlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) (states : Fin (n + 1) → State) :
    Measure.map finiteStateTimedPrefixWaitingTimes
        ((finiteStateMarkovTimedPrefixMeasure initial generator T n).restrict
          (FiniteStateTimedPrefixHasStateWord states)) =
      finiteStateMarkovStateWordProbability initial generator states •
        Measure.pi (fun i => finiteStateHoldingTimeMeasure generator T (states i)) := by
  let coefficient := finiteStateMarkovStateWordProbability initial generator states
  let holding := fun i => finiteStateHoldingTimeMeasure generator T (states i)
  let scaledHolding := fun i : Fin (n + 1) =>
    if i = 0 then coefficient • holding i else holding i
  have hCoefficient : coefficient ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact initial.apply_ne_top (states 0)
    · exact ENNReal.prod_ne_top fun i hi =>
        (finiteStateJumpDestinationPMF generator
          (states i.castSucc)).apply_ne_top (states i.succ)
  let (i : Fin (n + 1)) : IsProbabilityMeasure (holding i) :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T (states i)
  let (i : Fin (n + 1)) : IsFiniteMeasure (scaledHolding i) := by
    by_cases hi : i = 0
    · dsimp [scaledHolding]
      rw [ite_eq_left hi]
      exact (holding i).smul_finite hCoefficient
    · dsimp [scaledHolding]
      rw [ite_eq_right hi]
      infer_instance
  have hSource : Measure.pi scaledHolding =
      Measure.map finiteStateTimedPrefixWaitingTimes
        ((finiteStateMarkovTimedPrefixMeasure initial generator T n).restrict
          (FiniteStateTimedPrefixHasStateWord states)) := by
    apply Measure.pi_eq
    intro waitSets hWaitSets
    have hRectangle : MeasurableSet (Set.univ.pi waitSets) :=
      MeasurableSet.univ_pi hWaitSets
    rw [Measure.map_apply (measurable_finiteStateTimedPrefixWaitingTimes n) hRectangle]
    rw [Measure.restrict_apply
      (hRectangle.preimage (measurable_finiteStateTimedPrefixWaitingTimes n))]
    have hEvent :
        finiteStateTimedPrefixWaitingTimes ⁻¹' (Set.univ.pi waitSets) ∩
            FiniteStateTimedPrefixHasStateWord states =
          FiniteStateTimedPrefixMatches states waitSets := by
      ext trajectory
      constructor
      · rintro ⟨hWaits, hStates⟩ i
        exact ⟨hStates i, hWaits i (Set.mem_univ i)⟩
      · intro h
        exact ⟨fun i _ => (h i).2, fun i => (h i).1⟩
    rw [hEvent]
    rw [finiteStateMarkovTimedPrefixMeasure_matches
      initial generator T n states waitSets hWaitSets]
    rw [Fin.prod_univ_succ]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp [scaledHolding, coefficient, holding, mul_assoc]
  have hTarget : Measure.pi scaledHolding = coefficient • Measure.pi holding := by
    apply Measure.pi_eq
    intro waitSets hWaitSets
    change coefficient * Measure.pi holding (Set.univ.pi waitSets) =
      ∏ i, scaledHolding i (waitSets i)
    rw [Measure.pi_pi]
    rw [Fin.prod_univ_succ]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp [scaledHolding, coefficient, holding, mul_assoc]
  exact hSource.symm.trans hTarget

end FiniteMarkovProcesses.Probability
