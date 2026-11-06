/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizationParityStoppedLaw
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedHistoryDensity

/-!
# Density identification through the uniformization parity lift

The parity lift turns every common-clock event, including a virtual self-event, into a genuine
physical jump. On each projected state word there is exactly one lifted word with nonzero
physical density: its Boolean coordinate starts at `false` and alternates at every event. Its
physical Gillespie slice density is exactly the uniformized common-clock slice density.

Summing that pointwise identification proves that the normalized stopped uniformized history law
has the common-clock density.

## Main Results

- `finiteStateUniformizationParityWord`: the unique alternating parity word.
- `finiteStateMarkovJumpSliceDensity_uniformizationParityWord`: exact lifted slice density.
- `map_finiteStateMarkovJumpDensityMeasure_uniformizationParityLift`: exact density pushforward.
- `finiteStateUniformizedStoppedHistoryMeasure_eq_densityMeasure`: exact stopped-law density.
- `finiteStateUniformizedStoppedLawHasHistoryDensity_of_nonnegative`: the named density
  obligation at a nonnegative horizon.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Boolean parity after a given number of common-clock events, starting from `false`. -/
def finiteStateUniformizationParityAt : ℕ → Bool
  | 0 => false
  | n + 1 => !finiteStateUniformizationParityAt n

/-- The parity flag starts at `false` before any common-clock event. -/
@[simp]
theorem finiteStateUniformizationParityAt_zero :
    finiteStateUniformizationParityAt 0 = false :=
  rfl

/-- Every common-clock event flips the parity flag. -/
@[simp]
theorem finiteStateUniformizationParityAt_succ (n : ℕ) :
    finiteStateUniformizationParityAt (n + 1) =
      !finiteStateUniformizationParityAt n :=
  rfl

/-- The unique parity-alternating lift of one finite state word. -/
def finiteStateUniformizationParityWord {n : ℕ}
    (states : Fin (n + 1) → State) : Fin (n + 1) → State × Bool :=
  fun index ↦ (states index, finiteStateUniformizationParityAt index)

omit [Fintype State] [DecidableEq State] in
/-- Projecting the parity lift onto its state coordinate recovers the original state word. -/
@[simp]
theorem finiteStateUniformizationParityWord_fst {n : ℕ}
    (states : Fin (n + 1) → State) (index : Fin (n + 1)) :
    (finiteStateUniformizationParityWord states index).1 = states index :=
  rfl

omit [Fintype State] [DecidableEq State] in
/-- The lifted word starts at its original initial state with parity `false`. -/
@[simp]
theorem finiteStateUniformizationParityWord_zero {n : ℕ}
    (states : Fin (n + 1) → State) :
    finiteStateUniformizationParityWord states 0 = (states 0, false) := by
  simp [finiteStateUniformizationParityWord]

omit [Fintype State] [DecidableEq State] in
/-- Each lifted edge advances to the next state and flips the parity flag. -/
theorem finiteStateUniformizationParityWord_succ {n : ℕ}
    (states : Fin (n + 1) → State) (index : Fin n) :
    finiteStateUniformizationParityWord states index.succ =
      (states index.succ,
        !(finiteStateUniformizationParityWord states index.castSucc).2) := by
  simp [finiteStateUniformizationParityWord]

omit [Fintype State] [DecidableEq State] in
/-- A finite Boolean word starting at `false` and flipping at each edge is the canonical parity
word. -/
theorem finiteStateUniformizationParity_eq_of_zero_of_flip {n : ℕ}
    (parity : Fin (n + 1) → Bool) (hZero : parity 0 = false)
    (hFlip : ∀ index : Fin n, parity index.succ = !parity index.castSucc) :
    ∀ index, parity index = finiteStateUniformizationParityAt index := by
  intro index
  induction index using Fin.induction with
  | zero => exact hZero
  | succ index hIndex =>
      rw [hFlip index, hIndex]
      rfl

omit [Fintype State] [DecidableEq State] in
/-- Initial false parity and edgewise flipping characterize the canonical lift of a projected
state word. -/
theorem eq_finiteStateUniformizationParityWord_of_zero_of_flip {n : ℕ}
    (liftedStates : Fin (n + 1) → State × Bool)
    (hZero : (liftedStates 0).2 = false)
    (hFlip : ∀ index : Fin n,
      (liftedStates index.succ).2 = !(liftedStates index.castSucc).2) :
    liftedStates = finiteStateUniformizationParityWord (fun index ↦ (liftedStates index).1) := by
  funext index
  apply Prod.ext
  · rfl
  · exact finiteStateUniformizationParity_eq_of_zero_of_flip
      (fun i ↦ (liftedStates i).2) hZero hFlip index

/-- Every edge intensity along the canonical parity lift is its uniformized event intensity. -/
theorem finiteStateMarkovJumpRate_uniformizationParityWord {n : ℕ}
    (generator : FiniteStateMarkovGenerator State)
    (states : Fin (n + 1) → State) (index : Fin n) :
    (generator.uniformizationParityLift.rate
        (finiteStateUniformizationParityWord states index.castSucc)
        (finiteStateUniformizationParityWord states index.succ) : ℝ) =
      generator.uniformizedTransitionIntensity
        (states index.castSucc) (states index.succ) := by
  rw [finiteStateUniformizationParityWord_succ]
  rw [generator.uniformizationParityLift_rate_flip]
  rw [FiniteStateMarkovGenerator.uniformizedTransitionIntensity]
  rw [generator.uniformizedTransitionPMF_apply]
  norm_cast

/-- The physical jump-rate product of the canonical parity lift is exactly the common-clock
uniformized event-intensity product. -/
theorem finiteStateMarkovJumpRateProduct_uniformizationParityWord {n : ℕ}
    (generator : FiniteStateMarkovGenerator State)
    (states : Fin (n + 1) → State) :
    finiteStateMarkovJumpRateProduct generator.uniformizationParityLift
        (finiteStateUniformizationParityWord states) =
      finiteStateMarkovUniformizedTransitionIntensityProduct generator states := by
  unfold finiteStateMarkovJumpRateProduct
    finiteStateMarkovUniformizedTransitionIntensityProduct
  apply Finset.prod_congr rfl
  intro index _
  exact finiteStateMarkovJumpRate_uniformizationParityWord generator states index

/-- The lifted integrated escape is the common clock times the full horizon. -/
theorem finiteStateMarkovIntegratedEscape_uniformizationParityWord {n : ℕ}
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    finiteStateMarkovIntegratedEscape generator.uniformizationParityLift T
        (finiteStateUniformizationParityWord states) times =
      (generator.uniformizationRate : ℝ) * T := by
  unfold finiteStateMarkovIntegratedEscape
  simp_rw [generator.escapeRate_uniformizationParityLift]
  rw [← Finset.mul_sum]
  rw [FiniteJumpHistory.sum_dwellTimeVector]

/-- The physical Gillespie density on the canonical parity lift is exactly the uniformized
common-clock slice density. -/
theorem finiteStateMarkovJumpSliceDensity_uniformizationParityWord {n : ℕ}
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    finiteStateMarkovJumpSliceDensity
        (finiteStateUniformizationParityInitial initial)
        generator.uniformizationParityLift T
        (finiteStateUniformizationParityWord states) times =
      finiteStateMarkovUniformizedSliceDensity initial generator T states times := by
  unfold finiteStateMarkovJumpSliceDensity finiteStateMarkovUniformizedSliceDensity
  rw [finiteStateUniformizationParityWord_zero]
  rw [finiteStateUniformizationParityInitial_apply_false]
  rw [finiteStateMarkovJumpRateProduct_uniformizationParityWord]
  rw [finiteStateMarkovIntegratedEscape_uniformizationParityWord]

omit [Fintype State] [DecidableEq State] in
/-- Every noncanonical lift either has the wrong initial parity or fails to flip on some edge. -/
theorem finiteStateUniformizationParity_defect_of_ne {n : ℕ}
    (liftedStates : Fin (n + 1) → State × Bool)
    (hNe : liftedStates ≠
      finiteStateUniformizationParityWord (fun index ↦ (liftedStates index).1)) :
    (liftedStates 0).2 = true ∨
      ∃ index : Fin n,
        (liftedStates index.succ).2 ≠ !(liftedStates index.castSucc).2 := by
  by_cases hZero : (liftedStates 0).2 = false
  · right
    by_contra hNoDefect
    apply hNe
    apply eq_finiteStateUniformizationParityWord_of_zero_of_flip liftedStates hZero
    intro index
    by_contra hDefect
    exact hNoDefect ⟨index, hDefect⟩
  · left
    cases hParity : (liftedStates 0).2 <;> simp_all

/-- A lifted word with a parity defect has zero physical jump-rate product. -/
theorem finiteStateMarkovJumpRateProduct_uniformizationParity_defect {n : ℕ}
    (generator : FiniteStateMarkovGenerator State)
    (liftedStates : Fin (n + 1) → State × Bool) (index : Fin n)
    (hDefect :
      (liftedStates index.succ).2 ≠ !(liftedStates index.castSucc).2) :
    finiteStateMarkovJumpRateProduct generator.uniformizationParityLift liftedStates = 0 := by
  unfold finiteStateMarkovJumpRateProduct
  apply Finset.prod_eq_zero (Finset.mem_univ index)
  norm_cast
  exact generator.uniformizationParityLift_rate_of_not_flip hDefect

/-- Every noncanonical parity lift of its projected state word has zero physical slice density. -/
theorem finiteStateMarkovJumpSliceDensity_uniformizationParity_ne {n : ℕ}
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (liftedStates : Fin (n + 1) → State × Bool) (times : Fin n → ℝ)
    (hNe : liftedStates ≠
      finiteStateUniformizationParityWord (fun index ↦ (liftedStates index).1)) :
    finiteStateMarkovJumpSliceDensity
        (finiteStateUniformizationParityInitial initial)
        generator.uniformizationParityLift T liftedStates times = 0 := by
  rcases finiteStateUniformizationParity_defect_of_ne liftedStates hNe with
    hInitial | ⟨index, hDefect⟩
  · unfold finiteStateMarkovJumpSliceDensity
    rw [show liftedStates 0 = ((liftedStates 0).1, true) by
      ext <;> simp [hInitial]]
    rw [finiteStateUniformizationParityInitial_apply_true]
    simp
  · unfold finiteStateMarkovJumpSliceDensity
    rw [finiteStateMarkovJumpRateProduct_uniformizationParity_defect
      generator liftedStates index hDefect]
    simp

omit [Fintype State] [DecidableEq State] in
/-- Split a lifted state word into its state and parity coordinates. -/
def finiteStateUniformizationWordParityEquiv (n : ℕ) :
    (Fin (n + 1) → State × Bool) ≃
      (Fin (n + 1) → State) × (Fin (n + 1) → Bool) where
  toFun word := (fun index ↦ (word index).1, fun index ↦ (word index).2)
  invFun coordinates index := (coordinates.1 index, coordinates.2 index)
  left_inv word := by
    funext index
    rfl
  right_inv coordinates := by
    rcases coordinates with ⟨states, parity⟩
    rfl

omit [Fintype State] [DecidableEq State] in
/-- Combining a state word with the canonical parity coordinate gives its canonical parity
lift. -/
theorem finiteStateUniformizationWordParityEquiv_symm_canonical (n : ℕ)
    (states : Fin (n + 1) → State) :
    (finiteStateUniformizationWordParityEquiv (State := State) n).symm
        (states, fun index ↦ finiteStateUniformizationParityAt index) =
      finiteStateUniformizationParityWord states :=
  rfl

variable [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSingletonClass State] in
/-- Projecting the physical density slice on the canonical parity word gives exactly its
uniformized common-clock density slice. -/
theorem map_finiteStateMarkovJumpDensitySlice_uniformizationParityWord {n : ℕ}
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (states : Fin (n + 1) → State) :
    Measure.map finiteStateUniformizationHistoryProjection
        (Measure.map (embedJumpTimes n (finiteStateUniformizationParityWord states))
          ((volume.restrict (orderedJumpTimes n T)).withDensity
            (fun times ↦ ENNReal.ofReal
              (finiteStateMarkovJumpSliceDensity
                (finiteStateUniformizationParityInitial initial)
                generator.uniformizationParityLift T
                (finiteStateUniformizationParityWord states) times)))) =
      Measure.map (embedJumpTimes n states)
        ((volume.restrict (orderedJumpTimes n T)).withDensity
          (fun times ↦ ENNReal.ofReal
            (finiteStateMarkovUniformizedSliceDensity
              initial generator T states times))) := by
  rw [Measure.map_map measurable_finiteStateUniformizationHistoryProjection
    (measurable_embedJumpTimes n (finiteStateUniformizationParityWord states))]
  rw [show finiteStateUniformizationHistoryProjection ∘
      embedJumpTimes n (finiteStateUniformizationParityWord states) =
    embedJumpTimes n states by
    funext times
    rfl]
  congr 2
  funext times
  rw [finiteStateMarkovJumpSliceDensity_uniformizationParityWord]

omit [MeasurableSingletonClass State] in
/-- Projecting a physical density slice with noncanonical parity gives the zero measure. -/
theorem map_finiteStateMarkovJumpDensitySlice_uniformizationParity_ne {n : ℕ}
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (liftedStates : Fin (n + 1) → State × Bool)
    (hNe : liftedStates ≠
      finiteStateUniformizationParityWord (fun index ↦ (liftedStates index).1)) :
    Measure.map finiteStateUniformizationHistoryProjection
        (Measure.map (embedJumpTimes n liftedStates)
          ((volume.restrict (orderedJumpTimes n T)).withDensity
            (fun times ↦ ENNReal.ofReal
              (finiteStateMarkovJumpSliceDensity
                (finiteStateUniformizationParityInitial initial)
                generator.uniformizationParityLift T liftedStates times)))) = 0 := by
  rw [show (fun times ↦ ENNReal.ofReal
      (finiteStateMarkovJumpSliceDensity
        (finiteStateUniformizationParityInitial initial)
        generator.uniformizationParityLift T liftedStates times)) =
    (0 : (Fin n → ℝ) → ℝ≥0∞) by
      funext times
      rw [finiteStateMarkovJumpSliceDensity_uniformizationParity_ne
        initial generator T liftedStates times hNe]
      simp]
  simp

omit [MeasurableSingletonClass State] in
/-- At a fixed event count, projecting the sum of all lifted physical density slices leaves
exactly the sum of uniformized state-word slices. -/
theorem map_sum_finiteStateMarkovJumpDensitySlices_uniformizationParityLift
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ) :
    Measure.map finiteStateUniformizationHistoryProjection
        (Measure.sum fun liftedStates : Fin (n + 1) → State × Bool ↦
          Measure.map (embedJumpTimes n liftedStates)
            ((volume.restrict (orderedJumpTimes n T)).withDensity
              (fun times ↦ ENNReal.ofReal
                (finiteStateMarkovJumpSliceDensity
                  (finiteStateUniformizationParityInitial initial)
                  generator.uniformizationParityLift T liftedStates times)))) =
      Measure.sum fun states : Fin (n + 1) → State ↦
        Measure.map (embedJumpTimes n states)
          ((volume.restrict (orderedJumpTimes n T)).withDensity
            (fun times ↦ ENNReal.ofReal
              (finiteStateMarkovUniformizedSliceDensity
                initial generator T states times))) := by
  let physicalSlice := fun liftedStates : Fin (n + 1) → State × Bool ↦
    Measure.map (embedJumpTimes n liftedStates)
      ((volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times ↦ ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity
            (finiteStateUniformizationParityInitial initial)
            generator.uniformizationParityLift T liftedStates times)))
  let uniformizedSlice := fun states : Fin (n + 1) → State ↦
    Measure.map (embedJumpTimes n states)
      ((volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times ↦ ENNReal.ofReal
          (finiteStateMarkovUniformizedSliceDensity
            initial generator T states times)))
  change Measure.map finiteStateUniformizationHistoryProjection
      (Measure.sum physicalSlice) = Measure.sum uniformizedSlice
  rw [Measure.map_sum
    measurable_finiteStateUniformizationHistoryProjection.aemeasurable]
  ext event hEvent
  rw [Measure.sum_apply _ hEvent, Measure.sum_apply _ hEvent]
  simp only [tsum_fintype]
  calc
    ∑ liftedStates, (Measure.map finiteStateUniformizationHistoryProjection
        (physicalSlice liftedStates)) event =
      ∑ coordinates :
          (Fin (n + 1) → State) × (Fin (n + 1) → Bool),
        (Measure.map finiteStateUniformizationHistoryProjection
          (physicalSlice
            ((finiteStateUniformizationWordParityEquiv (State := State) n).symm
              coordinates))) event := by
        apply Fintype.sum_equiv
          (finiteStateUniformizationWordParityEquiv (State := State) n)
        intro liftedStates
        rfl
    _ = ∑ states : Fin (n + 1) → State,
        ∑ parity : Fin (n + 1) → Bool,
          (Measure.map finiteStateUniformizationHistoryProjection
            (physicalSlice
              ((finiteStateUniformizationWordParityEquiv (State := State) n).symm
                (states, parity)))) event := by
      rw [Fintype.sum_prod_type]
    _ = ∑ states : Fin (n + 1) → State, (uniformizedSlice states) event := by
      apply Finset.sum_congr rfl
      intro states _
      rw [Fintype.sum_eq_single
        (fun index : Fin (n + 1) ↦ finiteStateUniformizationParityAt index)]
      · dsimp only [physicalSlice, uniformizedSlice]
        rw [finiteStateUniformizationWordParityEquiv_symm_canonical]
        exact congrArg (fun measure : Measure (FiniteJumpHistory State) ↦ measure event)
          (map_finiteStateMarkovJumpDensitySlice_uniformizationParityWord
            initial generator T states)
      · intro parity hParity
        let liftedStates :=
          (finiteStateUniformizationWordParityEquiv (State := State) n).symm
            (states, parity)
        have hNe : liftedStates ≠ finiteStateUniformizationParityWord
            (fun index ↦ (liftedStates index).1) := by
          intro hEqual
          apply hParity
          funext index
          have hParityEqual := congrArg (fun word ↦ (word index).2) hEqual
          exact hParityEqual
        dsimp only [physicalSlice]
        rw [map_finiteStateMarkovJumpDensitySlice_uniformizationParity_ne
          initial generator T liftedStates hNe]
        simp

/-- Forgetting parity sends the complete lifted physical density measure exactly to the
uniformized common-clock density measure. -/
theorem map_finiteStateMarkovJumpDensityMeasure_uniformizationParityLift
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure.map finiteStateUniformizationHistoryProjection
        (finiteStateMarkovJumpDensityMeasure
          (finiteStateUniformizationParityInitial initial)
          generator.uniformizationParityLift T) =
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  rw [finiteStateMarkovJumpDensityMeasure_eq_sum_slices]
  rw [Measure.map_sum
    measurable_finiteStateUniformizationHistoryProjection.aemeasurable]
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices]
  congr 1
  funext n
  exact map_sum_finiteStateMarkovJumpDensitySlices_uniformizationParityLift
    initial generator T n

/-- At every nonnegative horizon, the normalized stopped uniformized history construction is
exactly its explicit common-clock density measure. -/
theorem finiteStateUniformizedStoppedHistoryMeasure_eq_densityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    FiniteStateMarkovUniformizedStoppedLaw.finiteStateUniformizedStoppedHistoryMeasure
        initial generator T =
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  rw [← map_finiteStateMarkovStoppedHistoryMeasure_uniformizationParityLift]
  rw [finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    (finiteStateUniformizationParityInitial initial)
    generator.uniformizationParityLift T hT]
  exact map_finiteStateMarkovJumpDensityMeasure_uniformizationParityLift
    initial generator T

/-- The parity lift discharges the named stopped uniformized history-density obligation at every
nonnegative horizon. -/
theorem finiteStateUniformizedStoppedLawHasHistoryDensity_of_nonnegative
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    FiniteStateUniformizedStoppedLawHasHistoryDensity initial generator T := by
  unfold FiniteStateUniformizedStoppedLawHasHistoryDensity
  exact finiteStateUniformizedStoppedHistoryMeasure_eq_densityMeasure
    initial generator T hT

end FiniteMarkovProcesses.Probability
