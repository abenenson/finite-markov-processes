/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionMeasure
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedHistoryExpectation
import FiniteMarkovProcesses.Probability.WeightedOrderedSelfEventInsertionIntegral

/-!
# Uniformized densities on canonical self-event insertion fibres

This module combines the canonical self-event insertion coordinates with the common-clock
finite-state Markov density. It factors the virtual transition intensity of one inserted word
into retained physical jump rates and per-dwell self-event rates, then transports its complete
ordered-time measure through self-event deletion.

## Main Results

- `finiteStateMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord`: exact
  physical/self-event factorization of one expanded virtual word.
- `map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordSliceMeasure`: exact retained-time
  density obtained by deleting one fixed vector of inserted self-event counts.
- `map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordFibreMeasure`: all count vectors
  over one reduced physical word resum exactly to its canonical physical CTMC slice.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The virtual transition-intensity product of a canonically expanded reduced word factors into
the retained physical jump-rate product and one self-event-rate power per physical dwell. -/
theorem finiteStateMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord
    (generator : FiniteStateMarkovGenerator State) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    finiteStateMarkovUniformizedTransitionIntensityProduct generator
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts) =
      finiteStateMarkovJumpRateProduct generator states *
        ∏ block : Fin (physicalEventCount + 1),
          (generator.uniformizedSelfEventRate (states block) : ℝ) ^
            selfEventCounts block := by
  unfold finiteStateMarkovUniformizedTransitionIntensityProduct
  rw [← (FiniteJumpHistory.selfEventInsertedEventCoordinateEquiv
    selfEventCounts).prod_comp]
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  rw [mul_comm]
  congr 1
  · unfold finiteStateMarkovJumpRateProduct
    apply Finset.prod_congr rfl
    intro index _
    change generator.uniformizedTransitionIntensity
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).castSucc)
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).succ) = _
    rw [FiniteJumpHistory.selfEventInsertedStateWord_physicalTransitionEventIndex_castSucc,
      FiniteJumpHistory.selfEventInsertedStateWord_physicalTransitionEventIndex_succ]
    exact generator.uniformizedTransitionIntensity_of_ne (hReduced index)
  · apply Finset.prod_congr rfl
    intro block _
    change (∏ selfEventIndex : Fin (selfEventCounts block),
      generator.uniformizedTransitionIntensity
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
          (FiniteJumpHistory.selfEventInsertedSelfEventIndex
            selfEventCounts block selfEventIndex).castSucc)
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
          (FiniteJumpHistory.selfEventInsertedSelfEventIndex
            selfEventCounts block selfEventIndex).succ)) = _
    simp_rw [(FiniteJumpHistory.selfEventInsertedStateWord_selfEventIndex_endpoints
      states selfEventCounts block _).1]
    simp_rw [(FiniteJumpHistory.selfEventInsertedStateWord_selfEventIndex_endpoints
      states selfEventCounts block _).2]
    simp [generator.uniformizedTransitionIntensity_self]

/-- The common-clock slice density of an expanded reduced word is the physical initial/jump
prefactor times common-clock survival and the inserted self-event-rate powers. -/
theorem finiteStateMarkovUniformizedSliceDensity_selfEventInsertedStateWord
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (virtualTimes :
      Fin (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts) → ℝ) :
    finiteStateMarkovUniformizedSliceDensity initial generator T
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts) virtualTimes =
      ((initial (states 0)).toReal * finiteStateMarkovJumpRateProduct generator states) *
        (Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
          ∏ block : Fin (physicalEventCount + 1),
            (generator.uniformizedSelfEventRate (states block) : ℝ) ^
              selfEventCounts block) := by
  unfold finiteStateMarkovUniformizedSliceDensity
  rw [finiteStateMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord
    generator states selfEventCounts hReduced]
  rw [FiniteJumpHistory.selfEventInsertedStateWord_zero]
  ring

/-- On ordered retained times, multiplying the virtual-word density by its insertion-simplex
volume gives the exact independent per-dwell self-event series term used in resummation. -/
theorem finiteStateMarkovUniformizedInsertedWordFibreDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T) :
    ENNReal.ofReal
          (finiteStateMarkovUniformizedSliceDensity initial generator T
            (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
            (fun _ ↦ 0)) *
        ∏ block : Fin (physicalEventCount + 1),
          ENNReal.ofReal
            (FiniteJumpHistory.dwellTimeVector T physicalTimes block ^
                selfEventCounts block /
              (selfEventCounts block).factorial) =
      ENNReal.ofReal
          ((initial (states 0)).toReal * finiteStateMarkovJumpRateProduct generator states) *
        (ENNReal.ofReal (Real.exp (-((generator.uniformizationRate : ℝ) * T))) *
          ∏ block : Fin (physicalEventCount + 1),
            ENNReal.ofReal
              (((generator.uniformizedSelfEventRate (states block) : ℝ) *
                    FiniteJumpHistory.dwellTimeVector T physicalTimes block) ^
                  selfEventCounts block /
                (selfEventCounts block).factorial)) := by
  let initialJump :=
    (initial (states 0)).toReal * finiteStateMarkovJumpRateProduct generator states
  let commonSurvival := Real.exp (-((generator.uniformizationRate : ℝ) * T))
  let selfEventPower := fun block : Fin (physicalEventCount + 1) ↦
    (generator.uniformizedSelfEventRate (states block) : ℝ) ^ selfEventCounts block
  let insertionVolume := fun block : Fin (physicalEventCount + 1) ↦
    FiniteJumpHistory.dwellTimeVector T physicalTimes block ^ selfEventCounts block /
      (selfEventCounts block).factorial
  have hInitialJump : 0 ≤ initialJump := by
    dsimp only [initialJump, finiteStateMarkovJumpRateProduct]
    positivity
  have hSelfEventPower (block : Fin (physicalEventCount + 1)) :
      0 ≤ selfEventPower block := by
    dsimp only [selfEventPower]
    positivity
  have hInsertionVolume (block : Fin (physicalEventCount + 1)) :
      0 ≤ insertionVolume block := by
    dsimp only [insertionVolume]
    have hDwell := FiniteJumpHistory.dwellTimeVector_nonneg_of_mem_orderedJumpTimes
      hT hPhysicalTimes block
    positivity
  rw [finiteStateMarkovUniformizedSliceDensity_selfEventInsertedStateWord
    initial generator T states selfEventCounts hReduced]
  change ENNReal.ofReal
      (initialJump * (commonSurvival * ∏ block, selfEventPower block)) *
        (∏ block, ENNReal.ofReal (insertionVolume block)) = _
  rw [ENNReal.ofReal_mul hInitialJump]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [ENNReal.ofReal_prod_of_nonneg fun block _ ↦ hSelfEventPower block]
  have hProduct :
      (∏ block, ENNReal.ofReal (selfEventPower block)) *
          ∏ block, ENNReal.ofReal (insertionVolume block) =
        ∏ block : Fin (physicalEventCount + 1),
          ENNReal.ofReal
            (((generator.uniformizedSelfEventRate (states block) : ℝ) *
                  FiniteJumpHistory.dwellTimeVector T physicalTimes block) ^
                selfEventCounts block /
              (selfEventCounts block).factorial) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro block _
    rw [← ENNReal.ofReal_mul (hSelfEventPower block)]
    apply congrArg ENNReal.ofReal
    dsimp only [selfEventPower, insertionVolume]
    rw [mul_pow]
    ring
  rw [← hProduct]
  dsimp only [initialJump]
  ac_rfl

/-- Fixed-count density induced on retained physical times by one canonical expanded virtual
word. -/
noncomputable def finiteStateMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (physicalTimes : Fin physicalEventCount → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (finiteStateMarkovUniformizedSliceDensity initial generator T
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
        (fun _ ↦ 0)) *
    ∏ block : Fin (physicalEventCount + 1),
      ENNReal.ofReal
        (FiniteJumpHistory.dwellTimeVector T physicalTimes block ^ selfEventCounts block /
          (selfEventCounts block).factorial)

/-- The fixed-count retained-time coefficient is measurable. -/
theorem measurable_finiteStateMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Measurable (finiteStateMarkovUniformizedInsertedWordFibreCoefficient
      initial generator T states selfEventCounts) := by
  unfold finiteStateMarkovUniformizedInsertedWordFibreCoefficient
  fun_prop

/-- On the physical ordered simplex, summing every self-event count vector gives exactly the
canonical physical CTMC fixed-word density. -/
theorem tsum_finiteStateMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount T) :
    ∑' selfEventCounts : Fin (physicalEventCount + 1) → ℕ,
        finiteStateMarkovUniformizedInsertedWordFibreCoefficient
          initial generator T states selfEventCounts physicalTimes =
      ENNReal.ofReal
        (finiteStateMarkovJumpSliceDensity initial generator T states physicalTimes) := by
  unfold finiteStateMarkovUniformizedInsertedWordFibreCoefficient
  simp_rw [finiteStateMarkovUniformizedInsertedWordFibreDensity
    initial generator hT states _ hReduced physicalTimes hPhysicalTimes]
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_left]
  rw [tsum_pi_fin_ennreal (fun block selfEventCount ↦
    ENNReal.ofReal
      (((generator.uniformizedSelfEventRate (states block) : ℝ) *
            FiniteJumpHistory.dwellTimeVector T physicalTimes block) ^ selfEventCount /
        selfEventCount.factorial))]
  exact
    finiteStateMarkovUniformizedSelfEventFibreWeight_resums_to_jumpSliceDensity_ennreal
      initial generator T states physicalTimes hT hPhysicalTimes

/-- Deleting one canonically expanded virtual-word slice gives the retained physical word with
the exact insertion-simplex density. The scalar is the constant common-clock density of that
virtual word; all time dependence is isolated in the per-dwell simplex-volume product. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordSliceMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedWordSliceMeasure initial generator T
          (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts)
          (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)) =
      ENNReal.ofReal
          (finiteStateMarkovUniformizedSliceDensity initial generator T
            (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
            (fun _ ↦ 0)) •
        Measure.map (embedJumpTimes physicalEventCount states)
          ((volume.restrict (orderedJumpTimes physicalEventCount T)).withDensity
            (fun physicalTimes ↦
              ∏ block : Fin (physicalEventCount + 1),
                ENNReal.ofReal
                  (FiniteJumpHistory.dwellTimeVector T physicalTimes block ^
                      selfEventCounts block /
                    (selfEventCounts block).factorial))) := by
  let virtualEventCount :=
    FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts
  let virtualStates :=
    FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
  let virtualDensity := ENNReal.ofReal
    (finiteStateMarkovUniformizedSliceDensity initial generator T virtualStates
      (fun _ ↦ 0))
  let merge := FiniteJumpHistory.selfEventInsertedJumpTimeEquiv selfEventCounts
  let insertionDomain :=
    FiniteJumpHistory.selfEventInsertionCoordinateDomain T selfEventCounts
  have hVirtualDensity :
      (fun times : Fin virtualEventCount → ℝ ↦
        ENNReal.ofReal
          (finiteStateMarkovUniformizedSliceDensity initial generator T
            virtualStates times)) = fun _ ↦ virtualDensity := by
    rfl
  have hMerge :=
    FiniteJumpHistory.volume_measurePreserving_selfEventInsertedJumpTimeEquiv selfEventCounts
  have hDeleteEmbed : Measurable
      (FiniteJumpHistory.deleteSelfEvents ∘ embedJumpTimes virtualEventCount virtualStates) :=
    FiniteJumpHistory.measurable_deleteSelfEvents.comp
      (measurable_embedJumpTimes virtualEventCount virtualStates)
  have hFunction :
      (FiniteJumpHistory.deleteSelfEvents ∘
          embedJumpTimes virtualEventCount virtualStates) ∘ merge =
        embedJumpTimes physicalEventCount states ∘ Prod.snd := by
    funext coordinates
    rcases coordinates with ⟨insertionTimes, physicalTimes⟩
    have hDeletion :=
      FiniteJumpHistory.deleteSelfEventsSlice_selfEventInsertedStateWord_selfEventInsertedJumpTimes
        states selfEventCounts hReduced insertionTimes physicalTimes
    simpa only [Function.comp_apply, virtualStates, merge,
      FiniteJumpHistory.selfEventInsertedJumpTimeEquiv_apply, embedJumpTimes,
      FiniteJumpHistory.deleteSelfEvents] using hDeletion
  unfold finiteStateMarkovUniformizedWordSliceMeasure
  rw [hVirtualDensity, withDensity_const]
  rw [Measure.map_smul _
    (measurable_embedJumpTimes virtualEventCount virtualStates).aemeasurable]
  rw [Measure.map_smul _ FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  rw [Measure.map_map FiniteJumpHistory.measurable_deleteSelfEvents
    (measurable_embedJumpTimes virtualEventCount virtualStates)]
  rw [← FiniteJumpHistory.map_volume_restrict_selfEventInsertionCoordinateDomain
    hT selfEventCounts]
  rw [Measure.map_map hDeleteEmbed hMerge.measurable]
  rw [hFunction]
  rw [← Measure.map_map (measurable_embedJumpTimes physicalEventCount states) measurable_snd]
  rw [FiniteJumpHistory.map_snd_volume_restrict_selfEventInsertionCoordinateDomain
    hT selfEventCounts]

/-- Equivalent fixed-count form with the constant virtual density absorbed into the retained-time
density coefficient. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordSliceMeasure_eq_density
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedWordSliceMeasure initial generator T
          (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts)
          (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)) =
      Measure.map (embedJumpTimes physicalEventCount states)
        ((volume.restrict (orderedJumpTimes physicalEventCount T)).withDensity
          (finiteStateMarkovUniformizedInsertedWordFibreCoefficient
            initial generator T states selfEventCounts)) := by
  rw [map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordSliceMeasure
    initial generator hT states selfEventCounts hReduced]
  have hInsertionVolume : Measurable
      (fun physicalTimes : Fin physicalEventCount → ℝ ↦
        ∏ block : Fin (physicalEventCount + 1),
          ENNReal.ofReal
            (FiniteJumpHistory.dwellTimeVector T physicalTimes block ^
                selfEventCounts block /
              (selfEventCounts block).factorial)) := by
    fun_prop
  rw [← Measure.map_smul _
    (measurable_embedJumpTimes physicalEventCount states).aemeasurable]
  rw [← withDensity_smul _ hInsertionVolume]
  rfl

/-- Sum of all canonical virtual words obtained by inserting arbitrary self-event counts into one
fixed reduced physical state word. -/
noncomputable def finiteStateMarkovUniformizedInsertedWordFibreMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun selfEventCounts : Fin (physicalEventCount + 1) → ℕ ↦
    finiteStateMarkovUniformizedWordSliceMeasure initial generator T
      (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts)
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)

/-- Deleting the complete canonical insertion fibre over one reduced physical word resums exactly
to that word's canonical physical CTMC slice measure. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordFibreMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedInsertedWordFibreMeasure
          initial generator T states) =
      finiteStateMarkovJumpWordSliceMeasure
        initial generator T physicalEventCount states := by
  unfold finiteStateMarkovUniformizedInsertedWordFibreMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  simp_rw [map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordSliceMeasure_eq_density
    initial generator hT states _ hReduced]
  rw [← Measure.map_sum
    (measurable_embedJumpTimes physicalEventCount states).aemeasurable]
  unfold finiteStateMarkovJumpWordSliceMeasure
  congr 1
  rw [← withDensity_tsum fun selfEventCounts ↦
    measurable_finiteStateMarkovUniformizedInsertedWordFibreCoefficient
      initial generator T states selfEventCounts]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_orderedJumpTimes physicalEventCount T)] with physicalTimes hPhysicalTimes
  rw [ENNReal.tsum_apply]
  exact tsum_finiteStateMarkovUniformizedInsertedWordFibreCoefficient
    initial generator hT states hReduced physicalTimes hPhysicalTimes

end FiniteMarkovProcesses.Probability
