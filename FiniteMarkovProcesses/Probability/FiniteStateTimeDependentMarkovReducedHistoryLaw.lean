/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovTimeDependentUniformizationRecovery
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovSelfEventDeletion

/-!
# Reduced history laws for bounded time-dependent Markov jump rates

This module defines the physical finite-history source associated with a bounded time-dependent
finite-state jump-rate family.  The source is the measurable self-event-deletion pushforward of
the normalized common-clock virtual history law.  Normalization is inherited directly from that
probability law.  Global insertion coverage and bounded-measurable insertion integration then
identify the same source with the separately constructed explicit physical density.

Constant rates recover the existing normalized finite-state Markov jump law exactly.  This is the
source-neutral probability object needed before constructing independent perturbed replicas,
their law of large numbers, or a pathwise change-of-measure identity.

## Main declarations

- `finiteStateTimeDependentMarkovReducedHistoryMeasure`: physical reduced-history law.
- `finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure`: bundled probability law.
- `finiteStateTimeDependentMarkovJumpDensityMeasure_eq_withDensity`: literal common-base density
  representation.
- `finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure`: exact explicit
  physical density for every bounded measurable rate family.
- `finiteStateTimeDependentMarkovReducedHistoryMeasure_constant`: exact homogeneous recovery.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Physical reduced-history law obtained by deleting virtual self-events from the normalized
bounded time-dependent common-clock source. -/
noncomputable def finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) : Measure (FiniteJumpHistory State) :=
  Measure.map FiniteJumpHistory.deleteSelfEvents
    (finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration)

/-- The reduced time-dependent history law is exactly normalized because it is the measurable
pushforward of the normalized virtual law. -/
theorem finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration Set.univ = 1 := by
  rw [finiteStateTimeDependentMarkovReducedHistoryMeasure,
    Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents
      MeasurableSet.univ, preimage_univ]
  exact finiteStateTimeDependentMarkovUniformizedHistoryMeasure_univ
    initial rates duration

/-- Bundled physical probability law for bounded time-dependent finite-state jump rates. -/
noncomputable def finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) : ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration,
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩⟩

/-- Probability bundling preserves the physical reduced-history measure. -/
@[simp]
theorem finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure_toMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    (finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure
      initial rates duration).toMeasure =
        finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration :=
  rfl

/-- Canonical physical density of a bounded measurable time-dependent rate family on the complete
finite-jump-history carrier. -/
noncomputable def finiteStateTimeDependentMarkovJumpDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateTimeDependentMarkovJumpSliceDensity initial rates duration states times

/-- The complete bounded time-dependent physical jump density is measurable. -/
theorem measurable_finiteStateTimeDependentMarkovJumpDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    Measurable (finiteStateTimeDependentMarkovJumpDensity initial rates duration) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  exact measurable_finiteStateTimeDependentMarkovJumpSliceDensity
    initial rates duration states

/-- Extended-nonnegative version of the complete bounded time-dependent physical density. -/
noncomputable def finiteStateTimeDependentMarkovJumpDensityENNReal
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : FiniteJumpHistory State → ℝ≥0∞ :=
  fun history => ENNReal.ofReal
    (finiteStateTimeDependentMarkovJumpDensity initial rates duration history)

/-- The extended-nonnegative bounded time-dependent physical density is measurable. -/
theorem measurable_finiteStateTimeDependentMarkovJumpDensityENNReal
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    Measurable (finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration) :=
  (measurable_finiteStateTimeDependentMarkovJumpDensity initial rates duration).ennreal_ofReal

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On an embedded state-word slice, the complete density is the corresponding slice density. -/
@[simp]
theorem finiteStateTimeDependentMarkovJumpDensityENNReal_embedJumpTimes
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration
        (embedJumpTimes eventCount states times) =
      ENNReal.ofReal
        (finiteStateTimeDependentMarkovJumpSliceDensity
          initial rates duration states times) :=
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A nonreduced state word has zero product of physical time-dependent jump rates. -/
theorem finiteStateTimeDependentMarkovJumpRateProduct_eq_zero_of_not_reduced
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ)
    (hNotReduced : ¬∀ index : Fin eventCount,
      states index.castSucc ≠ states index.succ) :
    finiteStateTimeDependentMarkovJumpRateProduct rates states times = 0 := by
  simp only [not_forall, not_not] at hNotReduced
  obtain ⟨index, hSelf⟩ := hNotReduced
  unfold finiteStateTimeDependentMarkovJumpRateProduct
  apply Finset.prod_eq_zero (Finset.mem_univ index)
  rw [hSelf, rates.rate_self]
  rfl

omit [MeasurableSingletonClass State] in
/-- Every nonreduced state-word slice has zero physical time-dependent jump measure. -/
theorem finiteStateTimeDependentMarkovJumpWordSliceMeasure_eq_zero_of_not_reduced
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (hNotReduced : ¬∀ index : Fin eventCount,
      states index.castSucc ≠ states index.succ) :
    finiteStateTimeDependentMarkovJumpWordSliceMeasure
        initial rates duration eventCount states = 0 := by
  have hDensity :
      (fun times : Fin eventCount → ℝ =>
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovJumpSliceDensity
            initial rates duration states times)) = 0 := by
    funext times
    unfold finiteStateTimeDependentMarkovJumpSliceDensity
    rw [finiteStateTimeDependentMarkovJumpRateProduct_eq_zero_of_not_reduced
      rates states times hNotReduced]
    simp
  unfold finiteStateTimeDependentMarkovJumpWordSliceMeasure
  rw [hDensity]
  simp

/-- Weighting the common finite-history base by the complete time-dependent physical density is
the sum of all fixed state-word density slices. -/
theorem finiteJumpHistoryBaseMeasure_withDensity_timeDependentMarkovJumpDensity_eq_sum_wordSlices
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    (finiteJumpHistoryBaseMeasure State duration).withDensity
        (finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration) =
      Measure.sum fun eventCount : ℕ =>
        Measure.sum fun states : Fin (eventCount + 1) → State =>
          finiteStateTimeDependentMarkovJumpWordSliceMeasure
            initial rates duration eventCount states := by
  unfold finiteJumpHistoryBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext eventCount
  unfold finiteJumpHistoryCountBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext states
  unfold finiteJumpHistorySliceBaseMeasure
  rw [← Measure.map_withDensity_comp _ (measurable_embedJumpTimes eventCount states)
    (finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration)
    (measurable_finiteStateTimeDependentMarkovJumpDensityENNReal
      initial rates duration)]
  rfl

/-- The explicit bounded time-dependent physical jump measure is literally the common finite-
history base weighted by its complete initial/jump/dwell density. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_eq_withDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration =
      (finiteJumpHistoryBaseMeasure State duration).withDensity
        (finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration) := by
  rw [finiteJumpHistoryBaseMeasure_withDensity_timeDependentMarkovJumpDensity_eq_sum_wordSlices]
  unfold finiteStateTimeDependentMarkovJumpDensityMeasure
  congr 1
  funext eventCount
  let ReducedWord :=
    {states : Fin (eventCount + 1) → State //
      ∀ index : Fin eventCount,
        states index.castSucc ≠ states index.succ}
  let wordMeasure := fun states : Fin (eventCount + 1) → State =>
    finiteStateTimeDependentMarkovJumpWordSliceMeasure
      initial rates duration eventCount states
  let reducedWordMeasure := fun states : ReducedWord => wordMeasure states.1
  let zeroMeasure := fun _ : Fin (eventCount + 1) → State =>
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
        finiteStateTimeDependentMarkovJumpWordSliceMeasure_eq_zero_of_not_reduced
          initial rates duration states hReduced
  change Measure.sum reducedWordMeasure = Measure.sum wordMeasure
  rw [hFamily]
  simpa only [zeroMeasure, Pi.zero_def] using
    (Measure.sum_extend_zero Subtype.val_injective reducedWordMeasure).symm

/-- The deletion-defined normalized physical source equals the explicit initial/jump/dwell
density for every bounded measurable time-dependent rate family. -/
theorem finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration =
      finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  exact map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    initial rates duration.coe_nonneg

/-- The reduced time-dependent source specialized to a constant generator is literally the
existing canonical physical finite-state Markov jump measure. -/
theorem finiteStateTimeDependentMarkovReducedHistoryMeasure_constant
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : NNReal) :
    finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration =
      finiteStateMarkovJumpDensityMeasure initial generator duration := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  exact
    map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant
      initial generator duration.coe_nonneg

/-- The explicit bounded time-dependent physical density specialized to a constant generator is
the existing canonical homogeneous finite-state jump density measure. -/
theorem finiteStateTimeDependentMarkovJumpDensityMeasure_constant
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : NNReal) :
    finiteStateTimeDependentMarkovJumpDensityMeasure
        initial generator.toTimeDependentMarkovRate duration =
      finiteStateMarkovJumpDensityMeasure initial generator duration := by
  rw [← finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure,
    finiteStateTimeDependentMarkovReducedHistoryMeasure_constant]

/-- The bundled reduced time-dependent source specialized to a constant generator has the exact
underlying canonical physical finite-state Markov jump measure. -/
theorem finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure_constant_toMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : NNReal) :
    (finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure
      initial generator.toTimeDependentMarkovRate duration).toMeasure =
        finiteStateMarkovJumpDensityMeasure initial generator duration := by
  rw [finiteStateTimeDependentMarkovReducedHistoryProbabilityMeasure_toMeasure,
    finiteStateTimeDependentMarkovReducedHistoryMeasure_constant]

end

end FiniteMarkovProcesses.Probability
