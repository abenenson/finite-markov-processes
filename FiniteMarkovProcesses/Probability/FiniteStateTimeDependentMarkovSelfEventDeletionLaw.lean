/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovSelfEventInsertionFibre

/-!
# Reduced physical law after time-dependent self-event deletion

This module assembles the fixed-word insertion-fibre identity into the complete reduced physical
jump-history measure and proves exact deletion of the uniformized history law.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]
/-- Physical reduced-history measure carried by one fixed state word. -/
noncomputable def finiteStateTimeDependentMarkovJumpWordSliceMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ)
    (states : Fin (eventCount + 1) → State) : Measure (FiniteJumpHistory State) :=
  Measure.map (embedJumpTimes eventCount states)
    ((volume.restrict (orderedJumpTimes eventCount duration)).withDensity
      (fun times ↦ ENNReal.ofReal
        (finiteStateTimeDependentMarkovJumpSliceDensity
          initial rates duration states times)))

/-- Sum of all time-dependent virtual words obtained by inserting arbitrary self-event counts
into one fixed reduced physical state word. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun selfEventCounts : Fin (physicalEventCount + 1) → ℕ ↦
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure initial rates duration
      (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts)
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)

/-- Deleting the complete canonical insertion fibre over one reduced word gives exactly its
time-dependent physical jump-word measure. -/
theorem map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
          initial rates duration states) =
      finiteStateTimeDependentMarkovJumpWordSliceMeasure
        initial rates duration physicalEventCount states := by
  unfold finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  simp_rw [map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedInsertedWordSliceMeasure
    initial rates hDuration states _ hReduced]
  rw [← Measure.map_sum
    (measurable_embedJumpTimes physicalEventCount states).aemeasurable]
  unfold finiteStateTimeDependentMarkovJumpWordSliceMeasure
  congr 1
  rw [← withDensity_tsum fun selfEventCounts ↦
    measurable_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
      initial rates duration states selfEventCounts]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_orderedJumpTimes physicalEventCount duration)] with physicalTimes hPhysicalTimes
  rw [ENNReal.tsum_apply]
  exact tsum_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
    initial rates hDuration states physicalTimes hPhysicalTimes

/-- Complete physical reduced-history density, explicitly summed only over reduced state words. -/
noncomputable def finiteStateTimeDependentMarkovJumpDensityMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun eventCount : ℕ ↦
    Measure.sum fun reducedStates :
        {states : Fin (eventCount + 1) → State //
          ∀ index : Fin eventCount,
            states index.castSucc ≠ states index.succ} ↦
      finiteStateTimeDependentMarkovJumpWordSliceMeasure
        initial rates duration eventCount reducedStates.1

/-- The complete virtual history law is the measure sum over its dependent event-count/state-word
code. -/
theorem finiteStateTimeDependentMarkovUniformizedHistoryMeasure_eq_sum_wordCodeSliceMeasures
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration =
      Measure.sum fun code : (Σ eventCount : ℕ, Fin (eventCount + 1) → State) ↦
        finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
          initial rates duration code.1 code.2 := by
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    finiteStateTimeDependentMarkovUniformizedCountMeasure
  exact (measureSum_sigma fun eventCount states ↦
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
      initial rates duration eventCount states).symm

/-- Canonical virtual submeasure obtained by expanding every reduced state word with every
per-dwell self-event count vector. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun code : FiniteJumpHistory.ReducedSelfEventInsertionWordCode State ↦
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure initial rates duration
      (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).1
      (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).2

/-- The canonical insertion family is a submeasure of the complete time-dependent virtual law. -/
theorem finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure_le_historyMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
        initial rates duration ≤
      finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration := by
  rw [finiteStateTimeDependentMarkovUniformizedHistoryMeasure_eq_sum_wordCodeSliceMeasures]
  unfold finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
  exact measureSum_comp_le_of_injective
    (FiniteJumpHistory.reducedSelfEventInsertionWordCode (State := State))
    FiniteJumpHistory.injective_reducedSelfEventInsertionWordCode
    (fun code : (Σ eventCount : ℕ, Fin (eventCount + 1) → State) ↦
      finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
        initial rates duration code.1 code.2)

/-- Global insertion coverage upgrades the canonical insertion family to the complete virtual
history measure. -/
theorem finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure_eq_historyMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
        initial rates duration =
      finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration := by
  rw [finiteStateTimeDependentMarkovUniformizedHistoryMeasure_eq_sum_wordCodeSliceMeasures]
  unfold finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
  exact measureSum_comp_eq_of_bijective
    (FiniteJumpHistory.reducedSelfEventInsertionWordCode (State := State))
    FiniteJumpHistory.bijective_reducedSelfEventInsertionWordCode
    (fun code : (Σ eventCount : ℕ, Fin (eventCount + 1) → State) ↦
      finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
        initial rates duration code.1 code.2)

/-- Deleting the canonical insertion submeasure gives the complete physical time-dependent jump
density. -/
theorem map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
          initial rates duration) =
      finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration := by
  unfold finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
    finiteStateTimeDependentMarkovJumpDensityMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  let insertedSliceMeasure :=
    fun code : FiniteJumpHistory.ReducedSelfEventInsertionWordCode State ↦
      Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedWordSliceMeasure initial rates duration
          (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).1
          (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).2)
  change Measure.sum insertedSliceMeasure = _
  have hSigma : Measure.sum insertedSliceMeasure =
      Measure.sum fun physicalEventCount : ℕ ↦
        Measure.sum fun pair ↦
          insertedSliceMeasure ⟨physicalEventCount, pair⟩ := by
    simpa only [Sigma.eta] using measureSum_sigma
      (fun physicalEventCount pair ↦
        insertedSliceMeasure ⟨physicalEventCount, pair⟩)
  rw [hSigma]
  congr 1
  funext physicalEventCount
  rw [measureSum_prod (fun reducedStates selfEventCounts ↦
    insertedSliceMeasure
      ⟨physicalEventCount, (reducedStates, selfEventCounts)⟩)]
  congr 1
  funext reducedStates
  rw [← Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  change Measure.map FiniteJumpHistory.deleteSelfEvents
      (finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
        initial rates duration reducedStates.1) = _
  exact map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreMeasure
    initial rates hDuration reducedStates.1 reducedStates.2

/-- Deleting the complete normalized virtual history measure gives its explicit physical
time-dependent jump-density measure. -/
theorem map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration) =
      finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration := by
  rw [← finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure_eq_historyMeasure]
  exact map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedCanonicalInsertionMeasure
    initial rates hDuration

/-- For every bounded measurable rate family, the complete physical density is exactly
normalized. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_univ
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    finiteStateTimeDependentMarkovJumpDensityMeasure
        initial rates duration Set.univ = 1 := by
  rw [← map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    initial rates hDuration,
    Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents
      MeasurableSet.univ, preimage_univ]
  simpa only [NNReal.toReal] using
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure_univ
      initial rates ⟨duration, hDuration⟩

/-- The normalized physical density in particular has total mass at most one. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_univ_le_one
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    finiteStateTimeDependentMarkovJumpDensityMeasure
        initial rates duration Set.univ ≤ 1 := by
  exact (finiteStateTimeDependentMarkovJumpDensityMeasure_univ
    initial rates hDuration).le


end FiniteMarkovProcesses.Probability
