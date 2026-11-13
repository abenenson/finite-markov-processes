/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.MeasureTheory.Measure.Sum
public import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventDeletion
public import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionCode
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedHistoryExpectation
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedSelfEventInsertionDensity
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedSelfEventResummation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizationParityDensity

/-!
# Density identification under deletion of uniformized self-events

This module develops the measure-level reindexing that sends the common-clock uniformized
finite-history density to the canonical physical CTMC jump density. The base calculation treats
constant virtual state words: every such word maps to one canonical no-jump history, while its
ordered-simplex masses resum the unused common-clock rate into physical survival.

## Main Results

- `map_deleteSelfEvents_finiteStateMarkovUniformizedWordSliceMeasure_const`: every constant
  virtual-word measure maps to a scalar Dirac measure at the corresponding no-jump history.
- `finiteStateMarkovUniformizedConstantWordSliceMeasure_univ`: exact mass of one constant-word
  slice in exponential-series form.
- `tsum_finiteStateMarkovUniformizedConstantWordSliceMeasure_univ`: the exact physical no-jump
  mass obtained after resumming all virtual self-event counts.
- `finiteStateMarkovUniformizedNoJumpFibreMeasure`: all constant virtual words over one state.
- `map_deleteSelfEvents_finiteStateMarkovUniformizedNoJumpFibreMeasure`: their pushforward is the
  exact physical no-jump scalar Dirac measure.
- `map_deleteSelfEvents_finiteStateMarkovUniformizedNoJumpFibreMeasure_eq_jumpWordSliceMeasure`:
  the zero-physical-jump deletion fibre is exactly the canonical physical word-slice measure.
- `map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure`: deletion of the complete
  common-clock density is exactly the canonical physical CTMC density measure.
- `finiteStateUniformizedReducedHistoryMeasure_eq_physical_of_nonnegative`: the normalized
  stopped-law pushforward is exactly the canonical physical law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

omit [Fintype State] [DecidableEq State] in
/-- A physical fixed-word jump-rate product vanishes whenever the word contains a repeated-state
edge. -/
theorem finiteStateMarkovJumpRateProduct_eq_zero_of_not_reduced
    (generator : FiniteStateMarkovGenerator State) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (hNotReduced : ¬∀ index : Fin eventCount,
      states index.castSucc ≠ states index.succ) :
    finiteStateMarkovJumpRateProduct generator states = 0 := by
  push Not at hNotReduced
  obtain ⟨index, hSelf⟩ := hNotReduced
  unfold finiteStateMarkovJumpRateProduct
  apply Finset.prod_eq_zero (Finset.mem_univ index)
  rw [hSelf, generator.rate_self]
  rfl

omit [DecidableEq State] in
/-- A canonical physical word-slice measure is zero whenever its state word is not reduced. -/
theorem finiteStateMarkovJumpWordSliceMeasure_eq_zero_of_not_reduced
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (hNotReduced : ¬∀ index : Fin eventCount,
      states index.castSucc ≠ states index.succ) :
    finiteStateMarkovJumpWordSliceMeasure
        initial generator T eventCount states = 0 := by
  have hRate := finiteStateMarkovJumpRateProduct_eq_zero_of_not_reduced
    generator states hNotReduced
  have hDensity :
      (fun times : Fin eventCount → ℝ ↦
        ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity initial generator T states times)) = 0 := by
    funext times
    unfold finiteStateMarkovJumpSliceDensity
    rw [hRate]
    simp
  unfold finiteStateMarkovJumpWordSliceMeasure
  rw [hDensity]
  simp

/-- The physical density decomposes over reduced state words only; every nonreduced word slice
vanishes because physical diagonal rates are zero. -/
theorem finiteStateMarkovJumpDensityMeasure_eq_sum_reducedWordSliceMeasures
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator T =
      Measure.sum fun eventCount : ℕ ↦
        Measure.sum fun states :
            {states : Fin (eventCount + 1) → State //
              ∀ index : Fin eventCount,
                states index.castSucc ≠ states index.succ} ↦
          finiteStateMarkovJumpWordSliceMeasure
            initial generator T eventCount states.1 := by
  rw [finiteStateMarkovJumpDensityMeasure_eq_sum_wordSliceMeasures]
  congr 1
  funext eventCount
  let ReducedWord :=
    {states : Fin (eventCount + 1) → State //
      ∀ index : Fin eventCount,
        states index.castSucc ≠ states index.succ}
  let wordMeasure := fun states : Fin (eventCount + 1) → State ↦
    finiteStateMarkovJumpWordSliceMeasure
      initial generator T eventCount states
  let reducedWordMeasure := fun states : ReducedWord ↦ wordMeasure states.1
  let zeroMeasure := fun _ : Fin (eventCount + 1) → State ↦
    (0 : Measure (FiniteJumpHistory State))
  have hFamily : wordMeasure =
      Function.extend Subtype.val reducedWordMeasure zeroMeasure := by
    funext states
    by_cases hReduced : ∀ index : Fin eventCount,
        states index.castSucc ≠ states index.succ
    · let reducedStates : ReducedWord := ⟨states, hReduced⟩
      have hApply := Subtype.val_injective.extend_apply
        reducedWordMeasure zeroMeasure reducedStates
      simpa only [reducedStates, reducedWordMeasure, wordMeasure,
        Function.comp_apply] using hApply.symm
    · have hNotRange : ¬∃ reducedStates : ReducedWord,
          reducedStates.1 = states := by
        rintro ⟨⟨_, hReduced'⟩, rfl⟩
        exact hReduced hReduced'
      rw [Function.extend_apply' _ _ _ hNotRange]
      simpa only [zeroMeasure, wordMeasure] using
        finiteStateMarkovJumpWordSliceMeasure_eq_zero_of_not_reduced
          initial generator T states hReduced
  change Measure.sum wordMeasure = Measure.sum reducedWordMeasure
  rw [hFamily]
  simpa only [zeroMeasure, Pi.zero_def] using
    Measure.sum_extend_zero Subtype.val_injective reducedWordMeasure

/-- The uniformized transition-intensity product along a constant state word consists exactly
of one virtual self-event rate per event. -/
theorem finiteStateMarkovUniformizedTransitionIntensityProduct_const
    (generator : FiniteStateMarkovGenerator State) (state : State) (eventCount : ℕ) :
    finiteStateMarkovUniformizedTransitionIntensityProduct generator
        (fun _ : Fin (eventCount + 1) ↦ state) =
      (generator.uniformizedSelfEventRate state : ℝ) ^ eventCount := by
  unfold finiteStateMarkovUniformizedTransitionIntensityProduct
  simp [FiniteStateMarkovGenerator.uniformizedTransitionIntensity_self]

/-- Deleting self-events maps a constant virtual-word slice to a scalar Dirac measure at the
canonical no-jump history. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedWordSliceMeasure_const
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (state : State) (eventCount : ℕ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedWordSliceMeasure
          initial generator T eventCount (fun _ ↦ state)) =
      (finiteStateMarkovUniformizedWordSliceMeasure
          initial generator T eventCount (fun _ ↦ state) Set.univ) •
        Measure.dirac (FiniteJumpHistory.noJumpHistory state) := by
  unfold finiteStateMarkovUniformizedWordSliceMeasure
  rw [Measure.map_apply (measurable_embedJumpTimes eventCount (fun _ ↦ state))
    MeasurableSet.univ, preimage_univ]
  rw [Measure.map_map FiniteJumpHistory.measurable_deleteSelfEvents
    (measurable_embedJumpTimes eventCount (fun _ ↦ state))]
  rw [show FiniteJumpHistory.deleteSelfEvents ∘
      embedJumpTimes eventCount (fun _ ↦ state) =
      fun _ ↦ FiniteJumpHistory.noJumpHistory state by
    funext times
    exact FiniteJumpHistory.deleteSelfEvents_embedJumpTimes_const state eventCount times]
  exact Measure.map_const
    ((volume.restrict (orderedJumpTimes eventCount T)).withDensity
      (fun times ↦ ENNReal.ofReal
        (finiteStateMarkovUniformizedSliceDensity
          initial generator T (fun _ ↦ state) times)))
    (FiniteJumpHistory.noJumpHistory state)

/-- Exact mass of a constant virtual state-word slice, written as the common-clock survival
coefficient times one exponential-series term for self-event insertions. -/
theorem finiteStateMarkovUniformizedConstantWordSliceMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) (eventCount : ℕ) :
    finiteStateMarkovUniformizedWordSliceMeasure
        initial generator duration eventCount (fun _ ↦ state) Set.univ =
      ENNReal.ofReal
        ((initial state).toReal *
          Real.exp (-((generator.uniformizationRate : ℝ) * duration)) *
            (((generator.uniformizedSelfEventRate state : ℝ) * duration) ^ eventCount /
              eventCount.factorial)) := by
  rw [finiteStateMarkovUniformizedWordSliceMeasure_univ]
  rw [← ENNReal.ofReal_mul
    (finiteStateMarkovUniformizedSliceDensity_nonneg initial generator duration
      (fun _ : Fin (eventCount + 1) ↦ state) (fun _ ↦ 0))]
  apply congrArg ENNReal.ofReal
  unfold finiteStateMarkovUniformizedSliceDensity
  rw [finiteStateMarkovUniformizedTransitionIntensityProduct_const]
  field_simp
  ring

/-- Summing the constant-word masses over every virtual self-event count converts common-clock
survival into the exact physical no-jump survival coefficient. -/
theorem tsum_finiteStateMarkovUniformizedConstantWordSliceMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) :
    ∑' eventCount : ℕ,
        finiteStateMarkovUniformizedWordSliceMeasure
          initial generator duration eventCount (fun _ ↦ state) Set.univ =
      ENNReal.ofReal
        ((initial state).toReal *
          Real.exp (-((generator.escapeRate state : ℝ) * duration))) := by
  let initialSurvival :=
    (initial state).toReal * Real.exp (-((generator.uniformizationRate : ℝ) * duration))
  let selfEventRate := generator.uniformizedSelfEventRate state
  have hSeries := hasSum_uniformizedSelfEventVolumeWeight
    (selfEventRate : ℝ) duration
  have hWeighted : HasSum
      (fun eventCount : ℕ ↦ initialSurvival *
        (((selfEventRate : ℝ) * duration) ^ eventCount / eventCount.factorial))
      (initialSurvival * Real.exp ((selfEventRate : ℝ) * duration)) :=
    hSeries.mul_left initialSurvival
  have hNonnegative (eventCount : ℕ) :
      0 ≤ initialSurvival *
        (((selfEventRate : ℝ) * duration) ^ eventCount / eventCount.factorial) := by
    dsimp only [initialSurvival, selfEventRate]
    positivity
  simp_rw [finiteStateMarkovUniformizedConstantWordSliceMeasure_univ]
  change (∑' eventCount : ℕ, ENNReal.ofReal
      (initialSurvival *
        (((selfEventRate : ℝ) * duration) ^ eventCount / eventCount.factorial))) = _
  rw [← ENNReal.ofReal_tsum_of_nonneg hNonnegative hWeighted.summable]
  rw [hWeighted.tsum_eq]
  apply congrArg ENNReal.ofReal
  dsimp only [initialSurvival, selfEventRate]
  have hResummation := uniformizedSelfEventResummation generator state (duration : ℝ)
  rw [tsum_uniformizedSelfEventVolumeWeight] at hResummation
  calc
    (initial state).toReal *
          Real.exp (-((generator.uniformizationRate : ℝ) * duration)) *
        Real.exp ((generator.uniformizedSelfEventRate state : ℝ) * duration) =
        (initial state).toReal *
          (Real.exp (-((generator.uniformizationRate : ℝ) * duration)) *
            Real.exp ((generator.uniformizedSelfEventRate state : ℝ) * duration)) := by
          ring
    _ = (initial state).toReal *
        Real.exp (-((generator.escapeRate state : ℝ) * duration)) := by
      rw [hResummation]

/-- Sum of every constant virtual state-word slice over all possible self-event counts. -/
noncomputable def finiteStateMarkovUniformizedNoJumpFibreMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (state : State) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun eventCount : ℕ ↦
    finiteStateMarkovUniformizedWordSliceMeasure
      initial generator T eventCount (fun _ ↦ state)

/-- Deleting all virtual self-events from the complete constant-word fibre gives exactly the
physical no-jump mass at that state. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedNoJumpFibreMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedNoJumpFibreMeasure
          initial generator duration state) =
      ENNReal.ofReal
          ((initial state).toReal *
            Real.exp (-((generator.escapeRate state : ℝ) * duration))) •
        Measure.dirac (FiniteJumpHistory.noJumpHistory state) := by
  unfold finiteStateMarkovUniformizedNoJumpFibreMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  simp_rw [map_deleteSelfEvents_finiteStateMarkovUniformizedWordSliceMeasure_const]
  ext event hEvent
  rw [Measure.sum_apply _ hEvent]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_right]
  rw [tsum_finiteStateMarkovUniformizedConstantWordSliceMeasure_univ]

omit [DecidableEq State] in
/-- The canonical physical no-jump slice has exactly its initial mass times physical survival. -/
theorem finiteStateMarkovJumpNoJumpWordSliceMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) :
    finiteStateMarkovJumpWordSliceMeasure
        initial generator duration 0 (fun _ ↦ state) Set.univ =
      ENNReal.ofReal
        ((initial state).toReal *
          Real.exp (-((generator.escapeRate state : ℝ) * duration))) := by
  unfold finiteStateMarkovJumpWordSliceMeasure
  rw [Measure.map_apply (measurable_embedJumpTimes 0 (fun _ ↦ state))
    MeasurableSet.univ, preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (∫⁻ _ : Fin 0 → ℝ in orderedJumpTimes 0 duration,
      ENNReal.ofReal
        (finiteStateMarkovJumpSliceDensity initial generator duration
          (fun _ : Fin 1 ↦ state) (fun index : Fin 0 ↦ Fin.elim0 index))) = _
  rw [setLIntegral_const]
  rw [volume_orderedJumpTimes 0 duration duration.coe_nonneg]
  simp [finiteStateMarkovJumpSliceDensity, finiteStateMarkovJumpRateProduct,
    finiteStateMarkovIntegratedEscape, FiniteJumpHistory.dwellTimeVector,
    FiniteJumpHistory.boundaryTimeVector]
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.lastCases_last]

omit [DecidableEq State] in
/-- The canonical physical zero-jump word slice is its scalar mass concentrated at the unique
no-jump history. -/
theorem finiteStateMarkovJumpNoJumpWordSliceMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) :
    finiteStateMarkovJumpWordSliceMeasure
        initial generator duration 0 (fun _ ↦ state) =
      ENNReal.ofReal
          ((initial state).toReal *
            Real.exp (-((generator.escapeRate state : ℝ) * duration))) •
        Measure.dirac (FiniteJumpHistory.noJumpHistory state) := by
  calc
    finiteStateMarkovJumpWordSliceMeasure
        initial generator duration 0 (fun _ ↦ state) =
        (finiteStateMarkovJumpWordSliceMeasure
            initial generator duration 0 (fun _ ↦ state) Set.univ) •
          Measure.dirac (FiniteJumpHistory.noJumpHistory state) := by
      unfold finiteStateMarkovJumpWordSliceMeasure
      rw [Measure.map_apply (measurable_embedJumpTimes 0 (fun _ ↦ state))
        MeasurableSet.univ, preimage_univ]
      rw [show embedJumpTimes 0 (fun _ ↦ state) =
          fun _ ↦ FiniteJumpHistory.noJumpHistory state by
        funext times
        apply FiniteJumpHistory.eq_noJumpHistory_of_jumpCount_eq_zero
        rfl]
      exact Measure.map_const
        ((volume.restrict (orderedJumpTimes 0 duration)).withDensity
          (fun times ↦ ENNReal.ofReal
            (finiteStateMarkovJumpSliceDensity
              initial generator duration (fun _ ↦ state) times)))
        (FiniteJumpHistory.noJumpHistory state)
    _ = _ := by
      rw [finiteStateMarkovJumpNoJumpWordSliceMeasure_univ]

/-- The full constant-word deletion fibre over one state is exactly the corresponding canonical
physical no-jump word slice. -/
theorem
    map_deleteSelfEvents_finiteStateMarkovUniformizedNoJumpFibreMeasure_eq_jumpWordSliceMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ≥0) (state : State) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedNoJumpFibreMeasure
          initial generator duration state) =
      finiteStateMarkovJumpWordSliceMeasure
        initial generator duration 0 (fun _ ↦ state) := by
  rw [map_deleteSelfEvents_finiteStateMarkovUniformizedNoJumpFibreMeasure,
    finiteStateMarkovJumpNoJumpWordSliceMeasure]

/-- Dependent code for one event count and one complete finite state word. -/
abbrev FiniteStateWordCode (State : Type u) :=
  Σ eventCount : ℕ, Fin (eventCount + 1) → State

/-- The common-clock density is the sum of its slices over the dependent finite-state-word
code. -/
theorem finiteStateMarkovUniformizedDensityMeasure_eq_sum_wordCodeSliceMeasures
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovUniformizedDensityMeasure initial generator T =
      Measure.sum fun code : FiniteStateWordCode State ↦
        finiteStateMarkovUniformizedWordSliceMeasure
          initial generator T code.1 code.2 := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices]
  exact (measureSum_sigma fun eventCount states ↦
    finiteStateMarkovUniformizedWordSliceMeasure
      initial generator T eventCount states).symm

/-- Canonical submeasure obtained by expanding every reduced physical state word with every
per-dwell self-event count vector. -/
noncomputable def finiteStateMarkovUniformizedCanonicalInsertionMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.sum fun code : FiniteJumpHistory.ReducedSelfEventInsertionWordCode State ↦
    finiteStateMarkovUniformizedWordSliceMeasure
      initial generator T
        (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).1
        (FiniteJumpHistory.reducedSelfEventInsertionWordCode code).2

/-- The canonical reduced-word insertion family is a submeasure of the complete common-clock
density. -/
theorem finiteStateMarkovUniformizedCanonicalInsertionMeasure_le_densityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovUniformizedCanonicalInsertionMeasure initial generator T ≤
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_wordCodeSliceMeasures]
  unfold finiteStateMarkovUniformizedCanonicalInsertionMeasure
  exact measureSum_comp_le_of_injective
    (FiniteJumpHistory.reducedSelfEventInsertionWordCode (State := State))
    FiniteJumpHistory.injective_reducedSelfEventInsertionWordCode
    (fun code : FiniteStateWordCode State ↦
      finiteStateMarkovUniformizedWordSliceMeasure
        initial generator T code.1 code.2)

/-- Deleting the canonical insertion submeasure yields the complete canonical physical CTMC
density. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedCanonicalInsertionMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedCanonicalInsertionMeasure
          initial generator T) =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  rw [finiteStateMarkovJumpDensityMeasure_eq_sum_reducedWordSliceMeasures]
  unfold finiteStateMarkovUniformizedCanonicalInsertionMeasure
  rw [Measure.map_sum FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  let insertedSliceMeasure :=
    fun code : FiniteJumpHistory.ReducedSelfEventInsertionWordCode State ↦
      Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedWordSliceMeasure initial generator T
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
      (finiteStateMarkovUniformizedInsertedWordFibreMeasure
        initial generator T reducedStates.1) = _
  exact map_deleteSelfEvents_finiteStateMarkovUniformizedInsertedWordFibreMeasure
    initial generator hT reducedStates.1 reducedStates.2

/-- The canonical insertion submeasure has total mass one at every nonnegative horizon. -/
theorem finiteStateMarkovUniformizedCanonicalInsertionMeasure_univ
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteStateMarkovUniformizedCanonicalInsertionMeasure
        initial generator T Set.univ = 1 := by
  have hMap := congrArg (fun measure : Measure (FiniteJumpHistory State) ↦
      measure Set.univ)
    (map_deleteSelfEvents_finiteStateMarkovUniformizedCanonicalInsertionMeasure
      initial generator hT)
  change (Measure.map FiniteJumpHistory.deleteSelfEvents
      (finiteStateMarkovUniformizedCanonicalInsertionMeasure
        initial generator T)) Set.univ =
    finiteStateMarkovJumpDensityMeasure initial generator T Set.univ at hMap
  rw [Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents
    MeasurableSet.univ, preimage_univ] at hMap
  exact hMap.trans <|
    finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      initial generator T hT

/-- The complete common-clock density has total mass one at every nonnegative horizon. -/
theorem finiteStateMarkovUniformizedDensityMeasure_univ
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteStateMarkovUniformizedDensityMeasure initial generator T Set.univ = 1 := by
  rw [← finiteStateUniformizedStoppedHistoryMeasure_eq_densityMeasure
    initial generator T hT]
  exact
    FiniteStateMarkovUniformizedStoppedLaw.finiteStateUniformizedStoppedHistoryMeasure_univ
      initial generator T

/-- Normalization upgrades the canonical insertion submeasure inclusion to equality with the
complete common-clock density. -/
theorem finiteStateMarkovUniformizedCanonicalInsertionMeasure_eq_densityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteStateMarkovUniformizedCanonicalInsertionMeasure initial generator T =
      finiteStateMarkovUniformizedDensityMeasure initial generator T := by
  let canonicalMeasure :=
    finiteStateMarkovUniformizedCanonicalInsertionMeasure initial generator T
  have hCanonicalUniv : canonicalMeasure Set.univ = 1 :=
    finiteStateMarkovUniformizedCanonicalInsertionMeasure_univ
      initial generator hT
  let : IsProbabilityMeasure canonicalMeasure := ⟨hCanonicalUniv⟩
  apply Measure.eq_of_le_of_measure_univ_eq
    (finiteStateMarkovUniformizedCanonicalInsertionMeasure_le_densityMeasure
      initial generator T)
  rw [hCanonicalUniv,
    finiteStateMarkovUniformizedDensityMeasure_univ initial generator hT]

/-- Deleting virtual self-events from the complete common-clock density gives exactly the
canonical physical finite-state CTMC density. -/
theorem map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateMarkovUniformizedDensityMeasure initial generator T) =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  rw [← finiteStateMarkovUniformizedCanonicalInsertionMeasure_eq_densityMeasure
    initial generator hT]
  exact map_deleteSelfEvents_finiteStateMarkovUniformizedCanonicalInsertionMeasure
    initial generator hT

/-- The normalized reduced uniformized law is exactly the canonical physical CTMC density at
every nonnegative horizon. -/
theorem finiteStateUniformizedReducedHistoryMeasure_eq_physical_of_nonnegative
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    finiteStateUniformizedReducedHistoryMeasure initial generator T =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  unfold finiteStateUniformizedReducedHistoryMeasure
  rw [finiteStateUniformizedStoppedHistoryMeasure_eq_densityMeasure
    initial generator T hT]
  exact map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator hT

/-- Self-event deletion identifies the normalized uniformized law with the physical CTMC law at
every nonnegative horizon. -/
theorem finiteStateUniformizedDeletionIdentifiesPhysicalLaw_of_nonnegative
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {T : ℝ} (hT : 0 ≤ T) :
    FiniteStateUniformizedDeletionIdentifiesPhysicalLaw initial generator T := by
  exact finiteStateUniformizedReducedHistoryMeasure_eq_physical_of_nonnegative
    initial generator hT

end FiniteMarkovProcesses.Probability
