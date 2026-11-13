/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw
public import FiniteMarkovProcesses.Probability.PoissonCountSecondMomentBound
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Count moments for bounded time-dependent Markov jump histories

The virtual common-clock event count of a bounded time-dependent finite-state source is exactly
Poisson.  After measurable self-event deletion, the physical jump count is pointwise no larger.
This module derives a uniform finite second moment for the reduced physical count, independently
of the initial PMF and the time profile of the rates.

## Main results

- `map_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure`.
- `memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure`.
- `variance_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSingletonClass State] in
/-- A fixed-word time-dependent virtual slice is concentrated on its defining event count. -/
theorem finiteStateTimeDependentMarkovUniformizedWordSliceMeasure_jumpCount
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount targetCount : ℕ)
    (states : Fin (eventCount + 1) → State) :
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
        initial rates duration eventCount states
        (FiniteJumpHistory.jumpCount ⁻¹' {targetCount}) =
      if eventCount = targetCount then
        finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
          initial rates duration eventCount states Set.univ
      else 0 := by
  unfold finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
  rw [Measure.map_apply (measurable_embedJumpTimes eventCount states)
    (FiniteJumpHistory.measurable_jumpCount
      (State := State) (measurableSet_singleton targetCount))]
  rw [Measure.map_apply (measurable_embedJumpTimes eventCount states)
    MeasurableSet.univ, preimage_univ]
  by_cases hCount : eventCount = targetCount
  · subst targetCount
    rw [ite_eq_left rfl]
    congr 1
    ext times
    simp [FiniteJumpHistory.jumpCount, embedJumpTimes]
  · rw [ite_eq_right hCount]
    have hPreimage :
        embedJumpTimes eventCount states ⁻¹'
            (FiniteJumpHistory.jumpCount ⁻¹' {targetCount}) = ∅ := by
      ext times
      simp [FiniteJumpHistory.jumpCount, embedJumpTimes, hCount]
    rw [hPreimage]
    simp

omit [MeasurableSingletonClass State] in
/-- A fixed-count time-dependent virtual measure assigns its Poisson mass to its defining count
and zero to every other count. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_jumpCount
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (eventCount targetCount : ℕ) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount
        (FiniteJumpHistory.jumpCount ⁻¹' {targetCount}) =
      if eventCount = targetCount then
        poissonCountPMF (rates.uniformizationRate * duration) eventCount
      else 0 := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_jumpCount
      (State := State) (measurableSet_singleton targetCount))]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure_jumpCount]
  by_cases hCount : eventCount = targetCount
  · rw [ite_eq_left hCount]
    simp_rw [ite_eq_left hCount]
    rw [tsum_fintype]
    rw [← finiteStateTimeDependentMarkovUniformizedCountMeasure_univ
      initial rates duration eventCount]
    unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
    rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  · rw [ite_eq_right hCount]
    simp_rw [ite_eq_right hCount, tsum_zero]

omit [MeasurableSingletonClass State] in
/-- The virtual event-count marginal of a bounded time-dependent history source is exactly the
Poisson law of its common clock. -/
theorem map_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    Measure.map FiniteJumpHistory.jumpCount
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration) =
      poissonMeasure (rates.uniformizationRate * duration) := by
  apply Measure.ext_of_singleton
  intro targetCount
  rw [Measure.map_apply FiniteJumpHistory.measurable_jumpCount
    (measurableSet_singleton targetCount)]
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_jumpCount
      (State := State) (measurableSet_singleton targetCount))]
  simp_rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_jumpCount]
  rw [tsum_eq_single targetCount]
  · rw [ite_eq_left rfl]
    rw [poissonMeasure_eq_poissonCountPMF_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton targetCount)]
  · intro eventCount hNe
    rw [ite_eq_right hNe]

omit [MeasurableSingletonClass State] in
/-- The real virtual event count has a finite second moment. -/
theorem memLp_two_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    MemLp (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ)) 2
      (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration) := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
      FiniteJumpHistory.measurable_jumpCount).aestronglyMeasurable).2
  have hMapped : Integrable (fun count : ℕ ↦ (count : ℝ) ^ 2)
      (Measure.map FiniteJumpHistory.jumpCount
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration)) := by
    rw [map_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure]
    exact integrable_sq_poissonCount (rates.uniformizationRate * duration)
  exact (integrable_map_measure hMapped.aestronglyMeasurable
    FiniteJumpHistory.measurable_jumpCount.aemeasurable).mp hMapped

/-- Self-event deletion preserves a finite second moment for the physical jump count. -/
theorem memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    MemLp (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ)) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
      FiniteJumpHistory.measurable_jumpCount).aestronglyMeasurable).2
  rw [finiteStateTimeDependentMarkovReducedHistoryMeasure]
  apply (integrable_map_measure
    ((((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
      FiniteJumpHistory.measurable_jumpCount).pow_const 2).aestronglyMeasurable)
    FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable).2
  have hVirtual :=
    (memLp_two_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration).integrable_sq
  apply hVirtual.mono'
  · exact (((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
      (FiniteJumpHistory.measurable_jumpCount.comp
        FiniteJumpHistory.measurable_deleteSelfEvents)).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with history
    have hCount := FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
    have hCountReal :
        ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) ≤
          ((history.jumpCount : ℕ) : ℝ) := by
      exact_mod_cast hCount
    have hDeletedNonnegative :
        (0 : ℝ) ≤ ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hOriginalNonnegative :
        (0 : ℝ) ≤ ((history.jumpCount : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg
      (sq_nonneg (((history.deleteSelfEvents.jumpCount : ℕ) : ℝ)))]
    nlinarith

/-- The physical jump-count second moment is uniformly controlled by the common-clock Poisson
exponential moment, independently of the initial PMF and detailed time profile. -/
theorem integral_sq_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
        (Real.exp 1 - 1)) := by
  let virtualLaw :=
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration
  have hVirtual : Integrable
      (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ) ^ 2) virtualLaw :=
    (memLp_two_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration).integrable_sq
  have hDeleted : Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.deleteSelfEvents.jumpCount : ℝ) ^ 2) virtualLaw := by
    have hReduced :=
      (memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration).integrable_sq
    rw [finiteStateTimeDependentMarkovReducedHistoryMeasure] at hReduced
    exact (integrable_map_measure hReduced.aestronglyMeasurable
      FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable).mp hReduced
  calc
    (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) =
        ∫ history : FiniteJumpHistory State,
          (history.deleteSelfEvents.jumpCount : ℝ) ^ 2 ∂virtualLaw := by
      unfold finiteStateTimeDependentMarkovReducedHistoryMeasure virtualLaw
      exact integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
        ((((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
          FiniteJumpHistory.measurable_jumpCount).pow_const 2).aestronglyMeasurable)
    _ ≤
        ∫ history : FiniteJumpHistory State,
          (history.jumpCount : ℝ) ^ 2 ∂virtualLaw := by
      apply integral_mono hDeleted hVirtual
      intro history
      have hCount :
          ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) ≤
            ((history.jumpCount : ℕ) : ℝ) := by
        exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
      have hDeletedNonnegative :
          (0 : ℝ) ≤ ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      have hOriginalNonnegative :
          (0 : ℝ) ≤ ((history.jumpCount : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    _ = ∫ count : ℕ, (count : ℝ) ^ 2
          ∂poissonMeasure (rates.uniformizationRate * duration) := by
      rw [← map_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration]
      exact (integral_map FiniteJumpHistory.measurable_jumpCount.aemeasurable
        (measurable_of_countable
          (fun count : ℕ ↦ (count : ℝ) ^ 2)).aestronglyMeasurable).symm
    _ ≤ 2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1)) :=
      integral_sq_poissonCount_le (rates.uniformizationRate * duration)

/-- The physical jump-count variance has the same source-uniform common-clock bound. -/
theorem variance_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    variance (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ))
        (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
        (Real.exp 1 - 1)) := by
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  calc
    variance (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ))
        (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      ∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2
        ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration :=
      variance_le_expectation_sq
        (((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
          FiniteJumpHistory.measurable_jumpCount).aestronglyMeasurable)
    _ ≤ 2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1)) :=
      integral_sq_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le
        initial rates duration

end

end FiniteMarkovProcesses.Probability
