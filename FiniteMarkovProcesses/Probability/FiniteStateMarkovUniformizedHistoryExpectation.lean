/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedSliceExpectation
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Measure-level expectations of finite-state uniformized histories

This module transports an integrable additive transition-plus-dwell reward from the normalized
common-clock density measure to the exact count-slice series. It names the fixed-word and
fixed-count density measures, proves their relation to the unbounded density measure, and applies
Bochner integration through the countable measure sum.

The integral transport theorem requires integrability explicitly. At a nonnegative horizon,
integrability of finite-state additive rewards is proved in this module. The histories retain
virtual self-events.

## Main Results

- `map_jumpCount_finiteStateMarkovUniformizedDensityMeasure`: the exact Poisson event-count
  marginal of the complete virtual-history density.
- `integrable_finiteStateMarkovAdditiveHistoryReward_uniformizedDensity`: unconditional
  integrability of every finite-state additive reward at a nonnegative horizon.
- `integral_finiteStateMarkovAdditiveHistoryReward_wordSlice`: exact fixed-word integral.
- `integral_finiteStateMarkovAdditiveHistoryReward_countMeasure`: exact fixed-count integral.
- `integral_finiteStateMarkovAdditiveHistoryReward_densityMeasure`: unbounded density integral as
  the certified count-slice series.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Additive transition-plus-dwell reward on the full finite-history carrier. -/
noncomputable def finiteStateMarkovAdditiveHistoryReward
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) : FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateMarkovAdditiveSliceReward transitionReward stateReward T states times

omit [DecidableEq State] in
/-- The additive finite-history reward is measurable on a finite discrete state space. -/
theorem measurable_finiteStateMarkovAdditiveHistoryReward
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) :
    Measurable (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  unfold finiteStateMarkovAdditiveHistoryReward finiteStateMarkovAdditiveSliceReward
  fun_prop

omit [Fintype State] [DecidableEq State] in
/-- Inserting a timed state-word slice into the history carrier preserves its additive reward. -/
theorem finiteStateMarkovAdditiveHistoryReward_embedJumpTimes
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) (eventCount : ℕ) (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T
        (embedJumpTimes eventCount states times) =
      finiteStateMarkovAdditiveSliceReward transitionReward stateReward T states times :=
  rfl

/-- Every uniformized slice density is nonnegative. -/
theorem finiteStateMarkovUniformizedSliceDensity_nonneg
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    0 ≤ finiteStateMarkovUniformizedSliceDensity initial generator T states times := by
  unfold finiteStateMarkovUniformizedSliceDensity
    finiteStateMarkovUniformizedTransitionIntensityProduct
    FiniteStateMarkovGenerator.uniformizedTransitionIntensity
  positivity

/-- Density measure on one fixed uniformized state-word slice. -/
noncomputable def finiteStateMarkovUniformizedWordSliceMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (eventCount : ℕ) (states : Fin (eventCount + 1) → State) :
    Measure (FiniteJumpHistory State) :=
  Measure.map (embedJumpTimes eventCount states)
    ((volume.restrict (orderedJumpTimes eventCount T)).withDensity
      (fun times ↦ ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity
          initial generator T states times)))

/-- Uniformized density measure at one fixed virtual-event count. -/
noncomputable def finiteStateMarkovUniformizedCountDensityMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (eventCount : ℕ) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun states : Fin (eventCount + 1) → State ↦
    finiteStateMarkovUniformizedWordSliceMeasure
      initial generator T eventCount states

/-- One fixed state-word slice has its constant density times the exact ordered-simplex
volume. -/
theorem finiteStateMarkovUniformizedWordSliceMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (eventCount : ℕ)
    (states : Fin (eventCount + 1) → State) :
    finiteStateMarkovUniformizedWordSliceMeasure
        initial generator duration eventCount states Set.univ =
      ENNReal.ofReal
          (finiteStateMarkovUniformizedSliceDensity
            initial generator duration states (fun _ ↦ 0)) *
        ENNReal.ofReal ((duration : ℝ) ^ eventCount / eventCount.factorial) := by
  unfold finiteStateMarkovUniformizedWordSliceMeasure
  rw [Measure.map_apply (measurable_embedJumpTimes eventCount states)
    MeasurableSet.univ, preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (∫⁻ _ : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
      ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity
          initial generator duration states (fun _ ↦ 0))) = _
  rw [setLIntegral_const]
  rw [volume_orderedJumpTimes eventCount duration duration.coe_nonneg]

/-- The unbounded uniformized density measure is the sum of its named count measures. -/
theorem finiteStateMarkovUniformizedDensityMeasure_eq_sum_countMeasures
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovUniformizedDensityMeasure initial generator T =
      Measure.sum fun eventCount : ℕ ↦
        finiteStateMarkovUniformizedCountDensityMeasure
          initial generator T eventCount := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices]
  rfl

/-- One word-slice measure is dominated by the complete unbounded density measure. -/
theorem finiteStateMarkovUniformizedWordSliceMeasure_le_densityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (eventCount : ℕ) (states : Fin (eventCount + 1) → State) :
    finiteStateMarkovUniformizedWordSliceMeasure
        initial generator T eventCount states ≤
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_countMeasures]
  exact (Measure.le_sum
    (fun word : Fin (eventCount + 1) → State ↦
      finiteStateMarkovUniformizedWordSliceMeasure
        initial generator T eventCount word) states).trans
    (Measure.le_sum
      (fun count : ℕ ↦
        finiteStateMarkovUniformizedCountDensityMeasure initial generator T count)
      eventCount)

/-- One count measure is dominated by the complete unbounded density measure. -/
theorem finiteStateMarkovUniformizedCountDensityMeasure_le_densityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (eventCount : ℕ) :
    finiteStateMarkovUniformizedCountDensityMeasure initial generator T eventCount ≤
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_countMeasures]
  exact Measure.le_sum
    (fun count : ℕ ↦
      finiteStateMarkovUniformizedCountDensityMeasure initial generator T count)
    eventCount

/-- Each count measure has exactly its Poisson count mass. -/
theorem finiteStateMarkovUniformizedCountDensityMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (eventCount : ℕ) :
    finiteStateMarkovUniformizedCountDensityMeasure
        initial generator duration eventCount Set.univ =
      poissonCountPMF (generator.uniformizationRate * duration) eventCount := by
  unfold finiteStateMarkovUniformizedCountDensityMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp_rw [finiteStateMarkovUniformizedWordSliceMeasure]
  simp_rw [Measure.map_apply (measurable_embedJumpTimes eventCount _)
    MeasurableSet.univ, preimage_univ]
  simp_rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← lintegral_finsetSum]
  · have hOfReal (times : Fin eventCount → ℝ) :
        (∑ states : Fin (eventCount + 1) → State,
          ENNReal.ofReal (finiteStateMarkovUniformizedSliceDensity
            initial generator duration states times)) =
          ENNReal.ofReal (∑ states : Fin (eventCount + 1) → State,
            finiteStateMarkovUniformizedSliceDensity
              initial generator duration states times) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro states _
        exact finiteStateMarkovUniformizedSliceDensity_nonneg
          initial generator duration states times
    simp_rw [hOfReal]
    let totalDensity : (Fin eventCount → ℝ) → ℝ := fun times ↦
      ∑ states : Fin (eventCount + 1) → State,
        finiteStateMarkovUniformizedSliceDensity
          initial generator duration states times
    have hFunction : totalDensity = fun _ ↦
        (generator.uniformizationRate : ℝ) ^ eventCount *
          Real.exp (-((generator.uniformizationRate : ℝ) * (duration : ℝ))) := by
      funext times
      exact sum_finiteStateMarkovUniformizedSliceDensity
        initial generator duration eventCount times
    have hIntegrable : Integrable totalDensity
        (volume.restrict (orderedJumpTimes eventCount duration)) := by
      rw [hFunction]
      exact integrable_const _
    have hNonnegative : 0 ≤ᶠ[
        ae (volume.restrict (orderedJumpTimes eventCount duration))] totalDensity := by
      apply ae_of_all
      intro times
      exact Finset.sum_nonneg fun states _ ↦
        finiteStateMarkovUniformizedSliceDensity_nonneg
          initial generator duration states times
    rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hNonnegative]
    rw [integral_sum_finiteStateMarkovUniformizedSliceDensity]
    rfl
  · intro states _
    unfold finiteStateMarkovUniformizedSliceDensity
    fun_prop

/-- A fixed-word uniformized slice is concentrated on its defining event count. -/
theorem finiteStateMarkovUniformizedWordSliceMeasure_jumpCount
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (eventCount targetCount : ℕ)
    (states : Fin (eventCount + 1) → State) :
    finiteStateMarkovUniformizedWordSliceMeasure initial generator T eventCount states
        (FiniteJumpHistory.jumpCount ⁻¹' {targetCount}) =
      if eventCount = targetCount then
        finiteStateMarkovUniformizedWordSliceMeasure
          initial generator T eventCount states Set.univ
      else 0 := by
  unfold finiteStateMarkovUniformizedWordSliceMeasure
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

/-- A fixed-count uniformized measure assigns its Poisson mass to its defining count and zero to
every other count. -/
theorem finiteStateMarkovUniformizedCountDensityMeasure_jumpCount
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (eventCount targetCount : ℕ) :
    finiteStateMarkovUniformizedCountDensityMeasure initial generator duration eventCount
        (FiniteJumpHistory.jumpCount ⁻¹' {targetCount}) =
      if eventCount = targetCount then
        poissonCountPMF (generator.uniformizationRate * duration) eventCount
      else 0 := by
  unfold finiteStateMarkovUniformizedCountDensityMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_jumpCount
      (State := State) (measurableSet_singleton targetCount))]
  simp_rw [finiteStateMarkovUniformizedWordSliceMeasure_jumpCount]
  by_cases hCount : eventCount = targetCount
  · rw [ite_eq_left hCount]
    simp_rw [ite_eq_left hCount]
    rw [tsum_fintype]
    rw [← finiteStateMarkovUniformizedCountDensityMeasure_univ
      initial generator duration eventCount]
    unfold finiteStateMarkovUniformizedCountDensityMeasure
    rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  · rw [ite_eq_right hCount]
    simp_rw [ite_eq_right hCount, tsum_zero]

/-- The event-count marginal of the complete uniformized history density is exactly Poisson. -/
theorem map_jumpCount_finiteStateMarkovUniformizedDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) :
    Measure.map FiniteJumpHistory.jumpCount
        (finiteStateMarkovUniformizedDensityMeasure initial generator duration) =
      poissonMeasure (generator.uniformizationRate * duration) := by
  apply Measure.ext_of_singleton
  intro targetCount
  rw [Measure.map_apply FiniteJumpHistory.measurable_jumpCount
    (measurableSet_singleton targetCount)]
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_countMeasures]
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_jumpCount
      (State := State) (measurableSet_singleton targetCount))]
  simp_rw [finiteStateMarkovUniformizedCountDensityMeasure_jumpCount]
  rw [tsum_eq_single targetCount]
  · rw [ite_eq_left rfl]
    rw [poissonMeasure_eq_poissonCountPMF_toMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton targetCount)]
  · intro eventCount hNe
    rw [ite_eq_right hNe]

/-- The real event count has a finite first moment under the complete uniformized history
density. -/
theorem integrable_jumpCount_finiteStateMarkovUniformizedDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) :
    Integrable (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ))
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
  have hMapped : Integrable (fun count : ℕ ↦ (count : ℝ))
      (Measure.map FiniteJumpHistory.jumpCount
        (finiteStateMarkovUniformizedDensityMeasure initial generator duration)) := by
    rw [map_jumpCount_finiteStateMarkovUniformizedDensityMeasure]
    exact integrable_poissonCount (generator.uniformizationRate * duration)
  exact (integrable_map_measure hMapped.aestronglyMeasurable
    FiniteJumpHistory.measurable_jumpCount.aemeasurable).mp hMapped

omit [DecidableEq State] in
/-- On an ordered finite history, every additive transition-plus-dwell reward is bounded by an
affine function of the event count. -/
theorem abs_finiteStateMarkovAdditiveHistoryReward_le_jumpCount
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (history : FiniteJumpHistory State)
    (hOrdered : history.OrderedBefore duration) :
    |finiteStateMarkovAdditiveHistoryReward
        transitionReward stateReward duration history| ≤
      (history.jumpCount : ℝ) *
          (∑ source : State, ∑ target : State, |transitionReward source target|) +
        ((history.jumpCount + 1 : ℕ) : ℝ) * (duration : ℝ) *
          (∑ state : State, |stateReward state|) := by
  rcases history with ⟨eventCount, states, times⟩
  let transitionBound : ℝ :=
    ∑ source : State, ∑ target : State, |transitionReward source target|
  let stateBound : ℝ := ∑ state : State, |stateReward state|
  have hTransitionReward (source target : State) :
      |transitionReward source target| ≤ transitionBound := by
    have hInner :
        |transitionReward source target| ≤
          ∑ candidateTarget : State, |transitionReward source candidateTarget| :=
      Finset.single_le_sum
        (fun candidateTarget _ ↦ abs_nonneg (transitionReward source candidateTarget))
        (Finset.mem_univ target)
    have hOuter :
        (∑ candidateTarget : State, |transitionReward source candidateTarget|) ≤
          transitionBound := by
      exact Finset.single_le_sum
        (fun candidateSource _ ↦ Finset.sum_nonneg fun candidateTarget _ ↦
          abs_nonneg (transitionReward candidateSource candidateTarget))
        (Finset.mem_univ source)
    exact hInner.trans hOuter
  have hStateReward (state : State) : |stateReward state| ≤ stateBound := by
    exact Finset.single_le_sum
      (fun candidateState _ ↦ abs_nonneg (stateReward candidateState))
      (Finset.mem_univ state)
  have hTransition :
      |∑ index : Fin eventCount,
          transitionReward (states index.castSucc) (states index.succ)| ≤
        (eventCount : ℝ) * transitionBound := by
    calc
      _ ≤ ∑ index : Fin eventCount,
          |transitionReward (states index.castSucc) (states index.succ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index : Fin eventCount, transitionBound :=
        Finset.sum_le_sum fun index _ ↦
          hTransitionReward (states index.castSucc) (states index.succ)
      _ = (eventCount : ℝ) * transitionBound := by simp
  have hDwellTerm (index : Fin (eventCount + 1)) :
      |FiniteJumpHistory.dwellTimeVector duration times index *
          stateReward (states index)| ≤
        (duration : ℝ) * stateBound := by
    rw [abs_mul]
    exact mul_le_mul
      (FiniteJumpHistory.abs_dwellTimeVector_le_of_mem_orderedJumpTimes
        duration.coe_nonneg hOrdered index)
      (hStateReward (states index))
      (abs_nonneg (stateReward (states index))) duration.coe_nonneg
  have hDwell :
      |∑ index : Fin (eventCount + 1),
          FiniteJumpHistory.dwellTimeVector duration times index *
            stateReward (states index)| ≤
        ((eventCount + 1 : ℕ) : ℝ) * (duration : ℝ) * stateBound := by
    calc
      _ ≤ ∑ index : Fin (eventCount + 1),
          |FiniteJumpHistory.dwellTimeVector duration times index *
            stateReward (states index)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index : Fin (eventCount + 1), (duration : ℝ) * stateBound :=
        Finset.sum_le_sum fun index _ ↦ hDwellTerm index
      _ = ((eventCount + 1 : ℕ) : ℝ) * (duration : ℝ) * stateBound := by
        simp [mul_assoc]
  unfold finiteStateMarkovAdditiveHistoryReward finiteStateMarkovAdditiveSliceReward
  change |_ + _| ≤ _
  calc
    |_ + _| ≤ |_| +
        |∑ index : Fin (eventCount + 1),
          FiniteJumpHistory.dwellTimeVector duration times index *
            stateReward (states index)| := abs_add_le _ _
    _ ≤ (eventCount : ℝ) * transitionBound +
        ((eventCount + 1 : ℕ) : ℝ) * (duration : ℝ) * stateBound :=
      add_le_add hTransition hDwell
    _ = _ := by rfl

/-- Every finite-state additive transition-plus-dwell reward is integrable under the complete
uniformized history density at a nonnegative horizon. -/
theorem integrable_finiteStateMarkovAdditiveHistoryReward_uniformizedDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) :
    Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (finiteStateMarkovUniformizedDensityMeasure initial generator duration) := by
  let historyMeasure :=
    finiteStateMarkovUniformizedDensityMeasure initial generator duration
  let transitionBound : ℝ :=
    ∑ source : State, ∑ target : State, |transitionReward source target|
  let stateBound : ℝ := ∑ state : State, |stateReward state|
  have hProbability : historyMeasure Set.univ = 1 := by
    have hMap := congrArg (fun measure : Measure ℕ ↦ measure Set.univ)
      (map_jumpCount_finiteStateMarkovUniformizedDensityMeasure
        initial generator duration)
    change (Measure.map FiniteJumpHistory.jumpCount
        (finiteStateMarkovUniformizedDensityMeasure initial generator duration)) Set.univ =
      poissonMeasure (generator.uniformizationRate * duration) Set.univ at hMap
    rw [Measure.map_apply FiniteJumpHistory.measurable_jumpCount
      MeasurableSet.univ, preimage_univ] at hMap
    simpa [historyMeasure] using hMap
  let : IsProbabilityMeasure historyMeasure := ⟨hProbability⟩
  have hCount : Integrable
      (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ))
      historyMeasure := by
    exact integrable_jumpCount_finiteStateMarkovUniformizedDensityMeasure
      initial generator duration
  have hAffine : Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.jumpCount : ℝ) * transitionBound +
          ((history.jumpCount + 1 : ℕ) : ℝ) * (duration : ℝ) * stateBound)
      historyMeasure := by
    have hSuccessor : Integrable
        (fun history : FiniteJumpHistory State ↦
          (history.jumpCount : ℝ) + 1) historyMeasure :=
      hCount.add (integrable_const 1)
    convert (hCount.mul_const transitionBound).add
      (hSuccessor.mul_const ((duration : ℝ) * stateBound)) using 1
    funext history
    simp only [Pi.add_apply]
    push_cast
    ring
  apply hAffine.mono'
    (measurable_finiteStateMarkovAdditiveHistoryReward
      transitionReward stateReward duration).aestronglyMeasurable
  have hOrderedBase :=
    FiniteJumpHistory.ae_orderedBefore_finiteJumpHistoryBaseMeasure
      (State := State) (duration : ℝ)
  have hOrdered : ∀ᵐ history ∂historyMeasure, history.OrderedBefore duration := by
    exact (withDensity_absolutelyContinuous
      (finiteJumpHistoryBaseMeasure State duration)
      (finiteStateMarkovUniformizedDensityENNReal initial generator duration)).ae_le
        hOrderedBase
  filter_upwards [hOrdered] with history historyOrdered
  rw [Real.norm_eq_abs]
  exact abs_finiteStateMarkovAdditiveHistoryReward_le_jumpCount
    transitionReward stateReward duration history historyOrdered

/-- Integrating an additive reward on one uniformized word slice is its density-weighted
ordered-time integral. -/
theorem integral_finiteStateMarkovAdditiveHistoryReward_wordSlice
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) (eventCount : ℕ) (states : Fin (eventCount + 1) → State) :
    (∫ history : FiniteJumpHistory State,
      finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T history
      ∂finiteStateMarkovUniformizedWordSliceMeasure
        initial generator T eventCount states) =
      ∫ times : Fin eventCount → ℝ in orderedJumpTimes eventCount T,
        finiteStateMarkovUniformizedSliceDensity initial generator T states times *
          finiteStateMarkovAdditiveSliceReward
            transitionReward stateReward T states times := by
  unfold finiteStateMarkovUniformizedWordSliceMeasure
  rw [integral_map (measurable_embedJumpTimes eventCount states).aemeasurable
    (measurable_finiteStateMarkovAdditiveHistoryReward
      transitionReward stateReward T).aestronglyMeasurable]
  have hDensity : Measurable fun times : Fin eventCount → ℝ ↦
      ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity initial generator T states times) := by
    unfold finiteStateMarkovUniformizedSliceDensity
    fun_prop
  have hTop : ∀ᵐ times : Fin eventCount → ℝ
      ∂volume.restrict (orderedJumpTimes eventCount T),
      ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity initial generator T states times) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hDensity hTop]
  simp_rw [show ∀ times : Fin eventCount → ℝ,
      (ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity initial generator T states times)).toReal =
          finiteStateMarkovUniformizedSliceDensity initial generator T states times from
    fun times ↦ ENNReal.toReal_ofReal <|
      finiteStateMarkovUniformizedSliceDensity_nonneg
        initial generator T states times]
  simp only [smul_eq_mul]
  rfl

/-- Density-weighted reward on one state-word slice is integrable whenever the complete history
reward is integrable under the unbounded density measure. -/
theorem integrable_uniformizedSliceDensity_mul_additiveSliceReward
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (T : ℝ) (eventCount : ℕ) (states : Fin (eventCount + 1) → State)
    (hIntegrable : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T)
      (finiteStateMarkovUniformizedDensityMeasure initial generator T)) :
    Integrable
      (fun times : Fin eventCount → ℝ ↦
        finiteStateMarkovUniformizedSliceDensity initial generator T states times *
          finiteStateMarkovAdditiveSliceReward
            transitionReward stateReward T states times)
      (volume.restrict (orderedJumpTimes eventCount T)) := by
  let density : (Fin eventCount → ℝ) → ℝ≥0∞ := fun times ↦
    ENNReal.ofReal
      (finiteStateMarkovUniformizedSliceDensity initial generator T states times)
  let sourceMeasure := (volume.restrict (orderedJumpTimes eventCount T)).withDensity density
  have hWord : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T)
      (finiteStateMarkovUniformizedWordSliceMeasure
        initial generator T eventCount states) :=
    hIntegrable.mono_measure <|
      finiteStateMarkovUniformizedWordSliceMeasure_le_densityMeasure
        initial generator T eventCount states
  have hPull : Integrable
      ((finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T) ∘
        embedJumpTimes eventCount states) sourceMeasure := by
    apply (integrable_map_measure hWord.aestronglyMeasurable
      (measurable_embedJumpTimes eventCount states).aemeasurable).mp
    exact hWord
  have hDensity : Measurable density := by
    unfold density finiteStateMarkovUniformizedSliceDensity
    fun_prop
  have hTop : ∀ᵐ times ∂volume.restrict (orderedJumpTimes eventCount T),
      density times < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hWeighted :=
    (integrable_withDensity_iff_integrable_smul' hDensity hTop).mp hPull
  have hFunction :
      (fun times : Fin eventCount → ℝ ↦
        (density times).toReal •
          ((finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T) ∘
            embedJumpTimes eventCount states) times) =
        fun times ↦
          finiteStateMarkovUniformizedSliceDensity initial generator T states times *
            finiteStateMarkovAdditiveSliceReward
              transitionReward stateReward T states times := by
    funext times
    unfold density
    rw [ENNReal.toReal_ofReal <|
      finiteStateMarkovUniformizedSliceDensity_nonneg
        initial generator T states times]
    simp only [Function.comp_apply, smul_eq_mul]
    rfl
  rwa [hFunction] at hWeighted

/-- The additive reward integral under one count measure is the named fixed-count slice
integral. -/
theorem integral_finiteStateMarkovAdditiveHistoryReward_countMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (eventCount : ℕ)
    (hIntegrable : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (finiteStateMarkovUniformizedDensityMeasure stationary.pmf generator duration)) :
    (∫ history : FiniteJumpHistory State,
      finiteStateMarkovAdditiveHistoryReward
        transitionReward stateReward duration history
      ∂finiteStateMarkovUniformizedCountDensityMeasure
        stationary.pmf generator duration eventCount) =
      finiteStateMarkovUniformizedCountAdditiveRewardIntegral generator stationary
        transitionReward stateReward duration eventCount := by
  have hCount : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (finiteStateMarkovUniformizedCountDensityMeasure
        stationary.pmf generator duration eventCount) :=
    hIntegrable.mono_measure <|
      finiteStateMarkovUniformizedCountDensityMeasure_le_densityMeasure
        stationary.pmf generator duration eventCount
  unfold finiteStateMarkovUniformizedCountDensityMeasure at hCount ⊢
  rw [integral_sum_measure hCount, tsum_fintype]
  simp_rw [integral_finiteStateMarkovAdditiveHistoryReward_wordSlice]
  unfold finiteStateMarkovUniformizedCountAdditiveRewardIntegral
  rw [integral_finsetSum Finset.univ]
  intro states _
  exact integrable_uniformizedSliceDensity_mul_additiveSliceReward
    stationary.pmf generator transitionReward stateReward duration eventCount states
    hIntegrable

/-- An integrable additive reward under the unbounded density measure is exactly the sum of its
certified fixed-count reward integrals. -/
theorem integral_finiteStateMarkovAdditiveHistoryReward_densityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0)
    (hIntegrable : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (finiteStateMarkovUniformizedDensityMeasure stationary.pmf generator duration)) :
    (∫ history : FiniteJumpHistory State,
      finiteStateMarkovAdditiveHistoryReward
        transitionReward stateReward duration history
      ∂finiteStateMarkovUniformizedDensityMeasure stationary.pmf generator duration) =
      ∑' eventCount : ℕ,
        finiteStateMarkovUniformizedCountAdditiveRewardIntegral generator stationary
          transitionReward stateReward duration eventCount := by
  let countMeasures : ℕ → Measure (FiniteJumpHistory State) := fun eventCount ↦
    finiteStateMarkovUniformizedCountDensityMeasure
      stationary.pmf generator duration eventCount
  have hMeasure :
      finiteStateMarkovUniformizedDensityMeasure stationary.pmf generator duration =
        Measure.sum countMeasures := by
    exact finiteStateMarkovUniformizedDensityMeasure_eq_sum_countMeasures
      stationary.pmf generator duration
  have hIntegrableSum : Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (Measure.sum countMeasures) := by
    rw [← hMeasure]
    exact hIntegrable
  calc
    _ = ∫ history : FiniteJumpHistory State,
        finiteStateMarkovAdditiveHistoryReward
          transitionReward stateReward duration history
        ∂Measure.sum countMeasures := by rw [← hMeasure]
    _ = ∑' eventCount : ℕ,
        ∫ history : FiniteJumpHistory State,
          finiteStateMarkovAdditiveHistoryReward
            transitionReward stateReward duration history
          ∂countMeasures eventCount := integral_sum_measure hIntegrableSum
    _ = _ := by
      apply tsum_congr
      intro eventCount
      exact integral_finiteStateMarkovAdditiveHistoryReward_countMeasure
        generator stationary transitionReward stateReward duration eventCount hIntegrable

end FiniteMarkovProcesses.Probability
