/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpPrefixLaw

/-!
# Finite marginals of the normalized jump-process tape

This module exposes the exact finite-dimensional marginals of the infinite normalized Gillespie
tape on the `Fin (n + 1)` carrier used by the recursion-native prefix law. The first theorem
reduces the tape marginal to Mathlib's Ionescu--Tulcea `partialTraj`; the next comparison target is
the recursive `finiteStateMarkovTimedPrefixMeasure`.

## Main results

- `finiteStateMarkovIicToFinPrefix`: canonical reindexing from `Iic n` to `Fin (n + 1)`.
- `finiteStateMarkovTapePrefix`: the first `n + 1` timed coordinates of an infinite tape.
- `finiteStateMarkovJumpTapePrefixMeasure_eq_partialTraj`: exact finite-marginal reduction to
  `Kernel.partialTraj`.
- `finiteStateMarkovJumpTapePrefixMeasure_eq_timedPrefixMeasure`: the infinite tape and recursive
  finite-prefix constructions have literally equal finite-dimensional laws.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Canonically reindex an `Iic n` trajectory as a `Fin (n + 1)` trajectory. -/
def finiteStateMarkovIicToFinPrefix (n : ℕ)
    (trajectory : (i : Finset.Iic n) → State × ℝ) : Fin (n + 1) → State × ℝ :=
  fun i => trajectory ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩

/-- Read the first `n + 1` timed coordinates from an infinite tape. -/
def finiteStateMarkovTapePrefix (n : ℕ)
    (tape : ℕ → State × ℝ) : Fin (n + 1) → State × ℝ :=
  fun i => tape i.1

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Canonical reindexing from `Iic n` to `Fin (n + 1)` is measurable. -/
theorem measurable_finiteStateMarkovIicToFinPrefix (n : ℕ) :
    Measurable (finiteStateMarkovIicToFinPrefix (State := State) n) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The finite-prefix readout from an infinite timed tape is measurable. -/
theorem measurable_finiteStateMarkovTapePrefix (n : ℕ) :
    Measurable (finiteStateMarkovTapePrefix (State := State) n) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply i.1

/-- The `Fin`-indexed tape marginal is exactly Mathlib's Ionescu--Tulcea partial trajectory,
reindexed from `Iic n`. -/
theorem finiteStateMarkovJumpTapePrefixMeasure_eq_partialTraj
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    Measure.map (finiteStateMarkovTapePrefix n)
        (finiteStateMarkovJumpTapeMeasure initial generator T) =
      Measure.map (finiteStateMarkovIicToFinPrefix n)
        (Kernel.partialTraj (X := fun _ => State × ℝ)
            (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
          finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) := by
  have hMap :
      finiteStateMarkovTapePrefix (State := State) n =
        finiteStateMarkovIicToFinPrefix n ∘ Preorder.frestrictLe n := by
    rfl
  rw [hMap]
  rw [← Measure.map_map (measurable_finiteStateMarkovIicToFinPrefix n)
    (Preorder.measurable_frestrictLe n)]
  unfold finiteStateMarkovJumpTapeMeasure
  rw [Measure.map_comp]
  rw [Kernel.traj_map_frestrictLe]
  fun_prop

/-- The Ionescu--Tulcea partial trajectory, mixed over the physical seed and reindexed on the
`Fin (n + 1)` carrier. -/
noncomputable def finiteStateMarkovPartialTrajectoryPrefixMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) : Measure (Fin (n + 1) → State × ℝ) :=
  Measure.map (finiteStateMarkovIicToFinPrefix n)
    (Kernel.partialTraj (X := fun _ => State × ℝ)
        (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
      finiteStateMarkovJumpTrajectorySeedMeasure initial generator T)

/-- At the initial coordinate, the reindexed partial trajectory equals the recursive prefix
law. -/
theorem finiteStateMarkovPartialTrajectoryPrefixMeasure_zero
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovPartialTrajectoryPrefixMeasure initial generator T 0 =
      finiteStateMarkovTimedPrefixMeasure initial generator T 0 := by
  unfold finiteStateMarkovPartialTrajectoryPrefixMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp]
  unfold finiteStateMarkovJumpTrajectorySeedMeasure
  rw [Measure.map_map (measurable_finiteStateMarkovIicToFinPrefix 0)
    measurable_finiteStateMarkovJumpTrajectorySeed]
  rw [finiteStateMarkovTimedPrefixMeasure]
  apply Measure.map_congr
  filter_upwards with timedState
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- One successor partial trajectory is the previous mixed trajectory composition-product with
the next singleton coordinate, mapped through `IicProdIoc`. -/
theorem finiteStateMarkovPartialTrajectoryMeasure_succ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    Kernel.partialTraj (X := fun _ => State × ℝ)
          (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 (n + 1) ∘ₘ
        finiteStateMarkovJumpTrajectorySeedMeasure initial generator T =
      Measure.map (IicProdIoc (X := fun _ : ℕ => State × ℝ) n (n + 1))
        ((Kernel.partialTraj (X := fun _ => State × ℝ)
            (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
          finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) ⊗ₘ
            (finiteStateMarkovJumpTrajectoryStepKernel generator T n).map
              (MeasurableEquiv.piSingleton
                (X := fun _ : ℕ => State × ℝ) n)) := by
  rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n)]
  rw [← Measure.map_comp]
  congr 1
  rw [Measure.compProd_eq_comp_prod]
  rw [← Measure.comp_assoc]
  exact measurable_IicProdIoc

/-- Reindexing the old trajectory coordinate commutes with adjoining one raw timed transition. -/
theorem finiteStateMarkovIicToFinPrefix_map_compProd
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ)
    (μ : Measure ((i : Finset.Iic n) → State × ℝ)) [SFinite μ] :
    Measure.map
        (fun pair => (finiteStateMarkovIicToFinPrefix n pair.1, pair.2))
        (μ ⊗ₘ finiteStateMarkovJumpTrajectoryStepKernel generator T n) =
      (Measure.map (finiteStateMarkovIicToFinPrefix n) μ) ⊗ₘ
        finiteStateMarkovTimedPrefixStepKernel generator T n := by
  ext event hEvent
  have hPairMap : Measurable
      (fun pair : ((i : Finset.Iic n) → State × ℝ) × (State × ℝ) =>
        (finiteStateMarkovIicToFinPrefix n pair.1, pair.2)) :=
    ((measurable_finiteStateMarkovIicToFinPrefix n).comp measurable_fst).prodMk
      measurable_snd
  rw [Measure.map_apply hPairMap hEvent]
  rw [Measure.compProd_apply (hEvent.preimage hPairMap)]
  rw [Measure.compProd_apply hEvent]
  rw [lintegral_map
    (Kernel.measurable_kernel_prodMk_left hEvent)
    (measurable_finiteStateMarkovIicToFinPrefix n)]
  apply lintegral_congr
  intro trajectory
  rw [show finiteStateMarkovTimedPrefixStepKernel generator T n
      (finiteStateMarkovIicToFinPrefix n trajectory) =
        finiteStateMarkovJumpTrajectoryStepKernel generator T n trajectory from rfl]
  congr 1

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Reindexing `IicProdIoc` after inserting the new singleton coordinate is literally finite
trajectory append. -/
theorem finiteStateMarkovIicToFinPrefix_IicProdIoc_piSingleton
    (n : ℕ) (trajectory : (i : Finset.Iic n) → State × ℝ) (next : State × ℝ) :
    finiteStateMarkovIicToFinPrefix (n + 1)
        (IicProdIoc (X := fun _ : ℕ => State × ℝ) n (n + 1)
          (trajectory, MeasurableEquiv.piSingleton
            (X := fun _ : ℕ => State × ℝ) n next)) =
      appendFiniteStateTimedState
        (finiteStateMarkovIicToFinPrefix n trajectory) next := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [finiteStateMarkovIicToFinPrefix, appendFiniteStateTimedState,
      IicProdIoc_def, MeasurableEquiv.piSingleton]
  · have hj : j.1 ≤ n := Nat.le_of_lt_succ j.2
    simp [finiteStateMarkovIicToFinPrefix, appendFiniteStateTimedState,
      IicProdIoc_def, hj]

/-- The reindexed partial-trajectory measure obeys exactly the same successor recursion as the
finite timed-prefix law. -/
theorem finiteStateMarkovPartialTrajectoryPrefixMeasure_succ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    finiteStateMarkovPartialTrajectoryPrefixMeasure initial generator T (n + 1) =
      Measure.map (fun pair => appendFiniteStateTimedState pair.1 pair.2)
        ((finiteStateMarkovPartialTrajectoryPrefixMeasure initial generator T n) ⊗ₘ
          finiteStateMarkovTimedPrefixStepKernel generator T n) := by
  unfold finiteStateMarkovPartialTrajectoryPrefixMeasure
  rw [finiteStateMarkovPartialTrajectoryMeasure_succ]
  rw [Measure.map_map (measurable_finiteStateMarkovIicToFinPrefix (n + 1))
    measurable_IicProdIoc]
  rw [MeasureTheory.Measure.compProd_map
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => State × ℝ) n).measurable]
  rw [Measure.map_map]
  · have hFunctions :
        (finiteStateMarkovIicToFinPrefix (State := State) (n + 1) ∘
              IicProdIoc (X := fun _ : ℕ => State × ℝ) n (n + 1)) ∘
                Prod.map id
                  (MeasurableEquiv.piSingleton
                    (X := fun _ : ℕ => State × ℝ) n) =
          (fun pair => appendFiniteStateTimedState pair.1 pair.2) ∘
            (fun pair => (finiteStateMarkovIicToFinPrefix n pair.1, pair.2)) := by
        funext pair
        exact finiteStateMarkovIicToFinPrefix_IicProdIoc_piSingleton n pair.1 pair.2
    rw [hFunctions]
    let pairMap := fun pair :
        ((i : Finset.Iic n) → State × ℝ) × (State × ℝ) =>
      (finiteStateMarkovIicToFinPrefix n pair.1, pair.2)
    let appendMap := fun pair :
        (Fin (n + 1) → State × ℝ) × (State × ℝ) =>
      appendFiniteStateTimedState pair.1 pair.2
    have hPairMap : Measurable pairMap :=
      ((measurable_finiteStateMarkovIicToFinPrefix n).comp measurable_fst).prodMk
        measurable_snd
    have hAppendMap : Measurable appendMap :=
      measurable_appendFiniteStateTimedState n
    change Measure.map (appendMap ∘ pairMap)
        ((Kernel.partialTraj (X := fun _ => State × ℝ)
            (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
          finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) ⊗ₘ
            finiteStateMarkovJumpTrajectoryStepKernel generator T n) =
      Measure.map appendMap
        ((Measure.map (finiteStateMarkovIicToFinPrefix n)
            (Kernel.partialTraj (X := fun _ => State × ℝ)
                (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
              finiteStateMarkovJumpTrajectorySeedMeasure initial generator T)) ⊗ₘ
          finiteStateMarkovTimedPrefixStepKernel generator T n)
    calc
      Measure.map (appendMap ∘ pairMap)
          ((Kernel.partialTraj (X := fun _ => State × ℝ)
              (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
            finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) ⊗ₘ
              finiteStateMarkovJumpTrajectoryStepKernel generator T n) =
        Measure.map appendMap
          (Measure.map pairMap
            ((Kernel.partialTraj (X := fun _ => State × ℝ)
                (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 n ∘ₘ
              finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) ⊗ₘ
                finiteStateMarkovJumpTrajectoryStepKernel generator T n)) :=
        (Measure.map_map hAppendMap hPairMap).symm
      _ = _ := congrArg (Measure.map appendMap)
        (finiteStateMarkovIicToFinPrefix_map_compProd generator T n _)
  · exact (measurable_finiteStateMarkovIicToFinPrefix (State := State) (n + 1)).comp
      measurable_IicProdIoc
  · fun_prop

/-- The Ionescu--Tulcea partial trajectory and recursion-native finite timed prefix are equal in
every dimension. -/
theorem finiteStateMarkovPartialTrajectoryPrefixMeasure_eq_timedPrefixMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    finiteStateMarkovPartialTrajectoryPrefixMeasure initial generator T n =
      finiteStateMarkovTimedPrefixMeasure initial generator T n := by
  induction n with
  | zero =>
      exact finiteStateMarkovPartialTrajectoryPrefixMeasure_zero initial generator T
  | succ n inductionHypothesis =>
      rw [finiteStateMarkovPartialTrajectoryPrefixMeasure_succ]
      rw [inductionHypothesis]
      rfl

/-- Every finite marginal of the normalized infinite Gillespie tape is literally the recursive
finite timed-prefix law used by the exact cylinder factorization. -/
theorem finiteStateMarkovJumpTapePrefixMeasure_eq_timedPrefixMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (n : ℕ) :
    Measure.map (finiteStateMarkovTapePrefix n)
        (finiteStateMarkovJumpTapeMeasure initial generator T) =
      finiteStateMarkovTimedPrefixMeasure initial generator T n := by
  rw [finiteStateMarkovJumpTapePrefixMeasure_eq_partialTraj]
  exact finiteStateMarkovPartialTrajectoryPrefixMeasure_eq_timedPrefixMeasure
    initial generator T n

end FiniteMarkovProcesses.Probability
