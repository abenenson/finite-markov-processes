/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.Measure.Sum
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionSurjectivity
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventInsertionMeasure
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovUniformizedHistoryLaw
import FiniteMarkovProcesses.Probability.WeightedOrderedSelfEventInsertionIntegral

/-!
# Self-event insertion fibres for time-dependent finite-state jump rates

This module evaluates the insertion fibres obtained by deleting virtual self-events from a
bounded measurable time-dependent common-clock law. Interval integrability and the absolutely
continuous fundamental theorem integrate and resum the insertion coefficients without imposing
continuity on the physical rates. Complete-history reindexing is in
`FiniteStateTimeDependentMarkovSelfEventDeletionLaw`.

## Main results

- `finiteStateTimeDependentMarkovUniformizedTransitionIntensity`: common-clock transition
  probabilities with the clock denominator restored.
- `finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord`:
  exact retained-jump/self-event factorization on a canonical insertion fibre.
- `finiteStateTimeDependentMarkovUnusedClockResummation_boundedMeasurable`: cancellation of the
  common clock into the physical integrated escape for bounded measurable rates.
- `map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedInsertedWordSliceMeasure`:
  exact measure-level deletion for each fixed vector of self-event counts.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateTimeDependentMarkovRate

/-- Pointwise unused common-clock intensity available for a virtual self-event. -/
noncomputable def unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State)
    (state : State) (time : ℝ) : ℝ :=
  (rates.uniformizationRate : ℝ) - (rates.escapeRate time state : ℝ)

/-- The unused common-clock intensity is nonnegative at every time and state. -/
theorem unusedClockRate_nonneg
    (rates : FiniteStateTimeDependentMarkovRate State)
    (state : State) (time : ℝ) :
    0 ≤ rates.unusedClockRate state time := by
  unfold unusedClockRate
  apply sub_nonneg.mpr
  exact_mod_cast rates.escapeRate_le_uniformizationRate time state

/-- Every unused common-clock row is measurable. -/
theorem measurable_unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State) (state : State) :
    Measurable (rates.unusedClockRate state) := by
  unfold unusedClockRate
  exact measurable_const.sub (rates.measurable_escapeRate state).coe_nnreal_real

/-- Every unused common-clock row is interval integrable on finite endpoints. -/
theorem intervalIntegrable_unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State) (state : State)
    (lower upper : ℝ) :
    IntervalIntegrable (rates.unusedClockRate state) volume lower upper := by
  unfold unusedClockRate
  exact IntervalIntegrable.sub intervalIntegrable_const
    (rates.intervalIntegrable_escapeRate state lower upper)

/-- A continuous escape row gives a continuous unused-clock intensity. -/
theorem continuous_unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State)
    (state : State)
    (hContinuousEscape : Continuous fun time ↦ (rates.escapeRate time state : ℝ)) :
    Continuous (rates.unusedClockRate state) := by
  unfold unusedClockRate
  exact continuous_const.sub hContinuousEscape

/-- The integrated unused-clock intensity on one ordered dwell is the clock mass minus the
integrated physical escape. -/
theorem integral_unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State)
    (state : State)
    (hContinuousEscape : Continuous fun time ↦ (rates.escapeRate time state : ℝ))
    (lower upper : ℝ) :
    (∫ time in lower..upper, rates.unusedClockRate state time) =
      (rates.uniformizationRate : ℝ) * (upper - lower) -
        ∫ time in lower..upper, (rates.escapeRate time state : ℝ) := by
  unfold unusedClockRate
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const]
    rw [smul_eq_mul]
    ring
  · exact intervalIntegrable_const
  · exact hContinuousEscape.intervalIntegrable lower upper

/-- The bounded-measurable unused-clock integral is the clock mass minus integrated physical
escape. -/
theorem integral_unusedClockRate_eq_uniformization_mass_sub_integral_escapeRate
    (rates : FiniteStateTimeDependentMarkovRate State) (state : State)
    (lower upper : ℝ) :
    (∫ time in lower..upper, rates.unusedClockRate state time) =
      (rates.uniformizationRate : ℝ) * (upper - lower) -
        ∫ time in lower..upper, (rates.escapeRate time state : ℝ) := by
  unfold unusedClockRate
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const]
    rw [smul_eq_mul]
    ring
  · exact intervalIntegrable_const
  · exact rates.intervalIntegrable_escapeRate state lower upper

/-- The unused-clock integral between arbitrary measurable endpoints is measurable for every
bounded measurable rate row. -/
theorem measurable_intervalIntegral_unusedClockRate_comp
    {X : Type*} [MeasurableSpace X]
    (rates : FiniteStateTimeDependentMarkovRate State) (state : State)
    {lower upper : X → ℝ} (hLower : Measurable lower) (hUpper : Measurable upper) :
    Measurable fun x ↦ ∫ time in (lower x)..(upper x), rates.unusedClockRate state time := by
  let primitive : ℝ → ℝ := fun endpoint ↦
    ∫ time in (0 : ℝ)..endpoint, (rates.escapeRate time state : ℝ)
  have hPrimitiveContinuous : Continuous primitive :=
    (rates.lipschitzWith_integral_escapeRate state).continuous
  have hIdentity :
      (fun x ↦ ∫ time in (lower x)..(upper x), rates.unusedClockRate state time) =
        fun x ↦
          (rates.uniformizationRate : ℝ) * (upper x - lower x) -
            (primitive (upper x) - primitive (lower x)) := by
    funext x
    rw [rates.integral_unusedClockRate_eq_uniformization_mass_sub_integral_escapeRate]
    rw [show (∫ time in lower x..upper x, (rates.escapeRate time state : ℝ)) =
        primitive (upper x) - primitive (lower x) by
      exact (intervalIntegral.integral_interval_sub_left
        (rates.intervalIntegrable_escapeRate state 0 (upper x))
        (rates.intervalIntegrable_escapeRate state 0 (lower x))).symm]
  rw [hIdentity]
  exact (measurable_const.mul (hUpper.sub hLower)).sub
    ((hPrimitiveContinuous.measurable.comp hUpper).sub
      (hPrimitiveContinuous.measurable.comp hLower))

end FiniteStateTimeDependentMarkovRate

/-- Time-dependent virtual transition intensity obtained by restoring the common-clock factor to
one uniformized transition probability. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedTransitionIntensity
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source target : State) : ℝ :=
  (rates.uniformizationRate : ℝ) *
    (rates.uniformizedTransitionWeight time source target : ℝ)

/-- An off-diagonal virtual transition intensity is exactly its physical jump rate. -/
theorem finiteStateTimeDependentMarkovUniformizedTransitionIntensity_of_ne
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) {source target : State} (hNe : source ≠ target) :
    finiteStateTimeDependentMarkovUniformizedTransitionIntensity
        rates time source target =
      (rates.rate time source target : ℝ) := by
  unfold finiteStateTimeDependentMarkovUniformizedTransitionIntensity
  rw [rates.uniformizedTransitionWeight_of_ne time hNe]
  norm_cast
  field_simp [ne_of_gt rates.uniformizationRate_pos]

/-- A virtual self-event intensity is exactly the unused common-clock rate. -/
theorem finiteStateTimeDependentMarkovUniformizedTransitionIntensity_self
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (state : State) :
    finiteStateTimeDependentMarkovUniformizedTransitionIntensity
        rates time state state =
      rates.unusedClockRate state time := by
  unfold finiteStateTimeDependentMarkovUniformizedTransitionIntensity
    FiniteStateTimeDependentMarkovRate.unusedClockRate
  rw [rates.uniformizedTransitionWeight_self]
  rw [← NNReal.coe_sub (rates.escapeRate_le_uniformizationRate time state)]
  norm_cast
  rw [mul_tsub, mul_one]
  rw [mul_div_cancel₀ _ (ne_of_gt rates.uniformizationRate_pos)]

/-- Product of the restored time-dependent transition intensities along one virtual state word. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  ∏ index : Fin eventCount,
    finiteStateTimeDependentMarkovUniformizedTransitionIntensity rates (times index)
      (states index.castSucc) (states index.succ)

/-- Restoring one clock factor per event rewrites the virtual slice density as the initial mass,
common-clock survival, and the product of restored transition intensities. -/
theorem finiteStateTimeDependentMarkovUniformizedSliceDensity_eq_intensityProduct
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states times =
      (initial (states 0)).toReal *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
          finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct
            rates states times := by
  unfold finiteStateTimeDependentMarkovUniformizedSliceDensity
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
    finiteStateTimeDependentMarkovContinuationWeight
    finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct
    finiteStateTimeDependentMarkovUniformizedTransitionIntensity
  simp only [FiniteStateTimeDependentMarkovRate.uniformizedTransitionPMF_apply,
    ENNReal.coe_toReal, Fin.cons_self_tail]
  have hClockProduct :
      (∏ index : Fin eventCount,
        (rates.uniformizationRate : ℝ) *
          (rates.uniformizedTransitionWeight (times index)
            (states index.castSucc) (states index.succ) : ℝ)) =
        (rates.uniformizationRate : ℝ) ^ eventCount *
          ∏ index : Fin eventCount,
            (rates.uniformizedTransitionWeight (times index)
              (states index.castSucc) (states index.succ) : ℝ) := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hClockProduct]
  ring

/-- The time-dependent virtual intensity product of a canonically expanded reduced word factors
into the retained physical jump rates and the pointwise unused-clock weights of all inserted
self-events. -/
theorem
finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord
    (rates : FiniteStateTimeDependentMarkovRate State) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (insertionTimes :
      (block : Fin (physicalEventCount + 1)) → Fin (selfEventCounts block) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct rates
        (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
        (FiniteJumpHistory.selfEventInsertedJumpTimes
          selfEventCounts insertionTimes physicalTimes) =
      (∏ index : Fin physicalEventCount,
        (rates.rate (physicalTimes index)
          (states index.castSucc) (states index.succ) : ℝ)) *
        ∏ block : Fin (physicalEventCount + 1),
          ∏ selfEventIndex : Fin (selfEventCounts block),
            rates.unusedClockRate (states block)
              (insertionTimes block selfEventIndex) := by
  unfold finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct
  rw [← (FiniteJumpHistory.selfEventInsertedEventCoordinateEquiv
    selfEventCounts).prod_comp]
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  rw [mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro index _hIndex
    change finiteStateTimeDependentMarkovUniformizedTransitionIntensity rates
      (FiniteJumpHistory.selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (FiniteJumpHistory.selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index))
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).castSucc)
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedPhysicalTransitionEventIndex
          selfEventCounts index).succ) = _
    rw [FiniteJumpHistory.selfEventInsertedJumpTimes_physicalTransitionEventIndex,
      FiniteJumpHistory.selfEventInsertedStateWord_physicalTransitionEventIndex_castSucc,
      FiniteJumpHistory.selfEventInsertedStateWord_physicalTransitionEventIndex_succ]
    exact finiteStateTimeDependentMarkovUniformizedTransitionIntensity_of_ne
      rates (physicalTimes index) (hReduced index)
  · apply Finset.prod_congr rfl
    intro block _hBlock
    apply Finset.prod_congr rfl
    intro selfEventIndex _hSelfEventIndex
    change finiteStateTimeDependentMarkovUniformizedTransitionIntensity rates
      (FiniteJumpHistory.selfEventInsertedJumpTimes selfEventCounts insertionTimes physicalTimes
        (FiniteJumpHistory.selfEventInsertedSelfEventIndex
          selfEventCounts block selfEventIndex))
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedSelfEventIndex
          selfEventCounts block selfEventIndex).castSucc)
      (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
        (FiniteJumpHistory.selfEventInsertedSelfEventIndex
          selfEventCounts block selfEventIndex).succ) = _
    rw [FiniteJumpHistory.selfEventInsertedJumpTimes_selfEventIndex]
    rw [(FiniteJumpHistory.selfEventInsertedStateWord_selfEventIndex_endpoints
      states selfEventCounts block selfEventIndex).1]
    rw [(FiniteJumpHistory.selfEventInsertedStateWord_selfEventIndex_endpoints
      states selfEventCounts block selfEventIndex).2]
    exact finiteStateTimeDependentMarkovUniformizedTransitionIntensity_self rates
      (insertionTimes block selfEventIndex) (states block)

/-- Product of the retained time-dependent physical jump rates along one reduced state word. -/
noncomputable def finiteStateTimeDependentMarkovJumpRateProduct
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  ∏ index : Fin eventCount,
    (rates.rate (times index) (states index.castSucc) (states index.succ) : ℝ)

/-- The retained time-dependent physical jump-rate product is measurable in its event times. -/
theorem measurable_finiteStateTimeDependentMarkovJumpRateProduct
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State) :
    Measurable (finiteStateTimeDependentMarkovJumpRateProduct rates states) := by
  unfold finiteStateTimeDependentMarkovJumpRateProduct
  apply Finset.measurable_prod
  intro index _hIndex
  exact (NNReal.continuous_coe.measurable.comp
    (rates.measurable_rate (states index.castSucc) (states index.succ))).comp
      (measurable_pi_apply index)

/-- Integrated physical escape accumulated over every retained-state dwell. -/
noncomputable def finiteStateTimeDependentMarkovIntegratedEscape
    (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  ∑ block : Fin (eventCount + 1),
    ∫ time in
        (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
        (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
      (rates.escapeRate time (states block) : ℝ)

/-- Bounded measurable escape rows make the complete integrated escape measurable in retained
times. -/
theorem measurable_finiteStateTimeDependentMarkovIntegratedEscape
    (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) :
    Measurable (finiteStateTimeDependentMarkovIntegratedEscape rates duration states) := by
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  apply Finset.measurable_sum
  intro block _hBlock
  let primitive : ℝ → ℝ := fun endpoint ↦
    ∫ time in (0 : ℝ)..endpoint,
      (rates.escapeRate time (states block) : ℝ)
  have hPrimitiveContinuous : Continuous primitive :=
    (rates.lipschitzWith_integral_escapeRate (states block)).continuous
  let lower : (Fin eventCount → ℝ) → ℝ := fun times ↦
    FiniteJumpHistory.boundaryTimeVector duration times block.castSucc
  let upper : (Fin eventCount → ℝ) → ℝ := fun times ↦
    FiniteJumpHistory.boundaryTimeVector duration times block.succ
  have hIdentity :
      (fun times : Fin eventCount → ℝ ↦
        ∫ time in lower times..upper times,
          (rates.escapeRate time (states block) : ℝ)) =
        fun times ↦ primitive (upper times) - primitive (lower times) := by
    funext times
    exact (intervalIntegral.integral_interval_sub_left
      (rates.intervalIntegrable_escapeRate (states block) 0 (upper times))
      (rates.intervalIntegrable_escapeRate (states block) 0 (lower times))).symm
  rw [hIdentity]
  exact (hPrimitiveContinuous.measurable.comp
    (FiniteJumpHistory.measurable_boundaryTimeVector_apply duration block.succ)).sub
      (hPrimitiveContinuous.measurable.comp
        (FiniteJumpHistory.measurable_boundaryTimeVector_apply duration block.castSucc))

/-- On an ordered physical time slice, complete integrated escape is nonnegative. -/
theorem finiteStateTimeDependentMarkovIntegratedEscape_nonneg_of_mem_orderedJumpTimes
    (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hTimes : times ∈ orderedJumpTimes eventCount duration) :
    0 ≤ finiteStateTimeDependentMarkovIntegratedEscape rates duration states times := by
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  apply Finset.sum_nonneg
  intro block _hBlock
  apply intervalIntegral.integral_nonneg_of_forall
  · exact FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hDuration hTimes (Fin.castSucc_le_succ block)
  · intro time
    exact NNReal.coe_nonneg (rates.escapeRate time (states block))

/-- On an ordered physical time slice, the declared escape bound times the horizon controls the
complete integrated escape. -/
theorem finiteStateTimeDependentMarkovIntegratedEscape_le_bound_mul_duration_of_ordered
    (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hTimes : times ∈ orderedJumpTimes eventCount duration) :
    finiteStateTimeDependentMarkovIntegratedEscape rates duration states times ≤
      (rates.escapeBound : ℝ) * duration := by
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  calc
    (∑ block : Fin (eventCount + 1),
        ∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
          (rates.escapeRate time (states block) : ℝ)) ≤
      ∑ block : Fin (eventCount + 1),
        (rates.escapeBound : ℝ) *
          FiniteJumpHistory.dwellTimeVector duration times block := by
        apply Finset.sum_le_sum
        intro block _hBlock
        let lower := FiniteJumpHistory.boundaryTimeVector duration times block.castSucc
        let upper := FiniteJumpHistory.boundaryTimeVector duration times block.succ
        have hLowerUpper : lower ≤ upper :=
          FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
            hDuration hTimes (Fin.castSucc_le_succ block)
        calc
          (∫ time in lower..upper, (rates.escapeRate time (states block) : ℝ)) ≤
              |∫ time in lower..upper,
                (rates.escapeRate time (states block) : ℝ)| := le_abs_self _
          _ ≤ (rates.escapeBound : ℝ) * |upper - lower| := by
            rw [← Real.norm_eq_abs]
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro time _hTime
            rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
            exact_mod_cast rates.escapeRate_le_escapeBound time (states block)
          _ = (rates.escapeBound : ℝ) *
              FiniteJumpHistory.dwellTimeVector duration times block := by
            rw [abs_of_nonneg (sub_nonneg.mpr hLowerUpper)]
            rfl
    _ = (rates.escapeBound : ℝ) *
        ∑ block : Fin (eventCount + 1),
          FiniteJumpHistory.dwellTimeVector duration times block := by
      rw [Finset.mul_sum]
    _ = (rates.escapeBound : ℝ) * duration := by
      rw [FiniteJumpHistory.sum_dwellTimeVector]

/-- Canonical physical reduced-word density for a time-dependent finite-state jump process. -/
noncomputable def finiteStateTimeDependentMarkovJumpSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  (initial (states 0)).toReal *
    finiteStateTimeDependentMarkovJumpRateProduct rates states times *
      Real.exp (-finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states times)

/-- Bounded measurable escape rows make every physical reduced-word density measurable. -/
theorem measurable_finiteStateTimeDependentMarkovJumpSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) :
    Measurable (finiteStateTimeDependentMarkovJumpSliceDensity
      initial rates duration states) := by
  unfold finiteStateTimeDependentMarkovJumpSliceDensity
  exact (measurable_const.mul
    (measurable_finiteStateTimeDependentMarkovJumpRateProduct rates states)).mul
      ((measurable_finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states).neg.exp)

/-- Summing the integrated unused-clock intensity over every ordered dwell leaves the complete
common-clock mass minus the physical integrated escape. -/
theorem sum_integral_unusedClockRate
    (rates : FiniteStateTimeDependentMarkovRate State)
    (hContinuousEscape : ∀ state,
      Continuous fun time ↦ (rates.escapeRate time state : ℝ))
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    (∑ block : Fin (eventCount + 1),
      ∫ time in
          (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
          (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
        rates.unusedClockRate (states block) time) =
      (rates.uniformizationRate : ℝ) * duration -
        finiteStateTimeDependentMarkovIntegratedEscape rates duration states times := by
  simp_rw [rates.integral_unusedClockRate (states _) (hContinuousEscape (states _))]
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.mul_sum]
  change (rates.uniformizationRate : ℝ) *
      (∑ block : Fin (eventCount + 1),
        FiniteJumpHistory.dwellTimeVector duration times block) = _
  rw [FiniteJumpHistory.sum_dwellTimeVector]

/-- Bounded measurable rows have the same exact total unused-clock integral decomposition. -/
theorem sum_integral_unusedClockRate_eq_uniformization_mass_sub_integratedEscape
    (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    (∑ block : Fin (eventCount + 1),
      ∫ time in
          (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
          (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
        rates.unusedClockRate (states block) time) =
      (rates.uniformizationRate : ℝ) * duration -
        finiteStateTimeDependentMarkovIntegratedEscape rates duration states times := by
  simp_rw [rates.integral_unusedClockRate_eq_uniformization_mass_sub_integral_escapeRate]
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.mul_sum]
  change (rates.uniformizationRate : ℝ) *
      (∑ block : Fin (eventCount + 1),
        FiniteJumpHistory.dwellTimeVector duration times block) = _
  rw [FiniteJumpHistory.sum_dwellTimeVector]

/-- Exact exponential resummation of all time-dependent virtual self-event counts on one reduced
physical word. -/
theorem finiteStateTimeDependentMarkovUnusedClockResummation
    (rates : FiniteStateTimeDependentMarkovRate State)
    (hContinuousEscape : ∀ state,
      Continuous fun time ↦ (rates.escapeRate time state : ℝ))
    {duration : ℝ} (hDuration : 0 ≤ duration) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ)
    (hTimes : times ∈ orderedJumpTimes eventCount duration) :
    ENNReal.ofReal (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        ∏ block : Fin (eventCount + 1),
          ∑' selfEventCount : ℕ,
            ENNReal.ofReal
              ((∫ time in
                  (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
                  (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                    rates.unusedClockRate (states block) time) ^ selfEventCount /
                selfEventCount.factorial) =
      ENNReal.ofReal
        (Real.exp (-finiteStateTimeDependentMarkovIntegratedEscape
          rates duration states times)) := by
  have hBounds (block : Fin (eventCount + 1)) :
      FiniteJumpHistory.boundaryTimeVector duration times block.castSucc ≤
        FiniteJumpHistory.boundaryTimeVector duration times block.succ :=
    FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hDuration hTimes (Fin.castSucc_le_succ block)
  have hSeries (block : Fin (eventCount + 1)) :
      (∑' selfEventCount : ℕ,
        ENNReal.ofReal
          ((∫ time in
              (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
              (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                rates.unusedClockRate (states block) time) ^ selfEventCount /
            selfEventCount.factorial)) =
        ENNReal.ofReal
          (Real.exp
            (∫ time in
              (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
              (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                rates.unusedClockRate (states block) time)) := by
    have hSetIntegral :
        (∫ time in Ioo
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
              rates.unusedClockRate (states block) time) =
          ∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
              rates.unusedClockRate (states block) time := by
      rw [← integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le (hBounds block)]
    simpa only [lintegral_weightedOrderedTimesInInterval
      (rates.continuous_unusedClockRate
        (states block) (hContinuousEscape (states block)))
      (rates.unusedClockRate_nonneg (states block)) _ _ _ (hBounds block),
      hSetIntegral] using
      tsum_lintegral_weightedOrderedTimesInInterval
        (rates.continuous_unusedClockRate
          (states block) (hContinuousEscape (states block)))
        (rates.unusedClockRate_nonneg (states block))
        (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)
        (FiniteJumpHistory.boundaryTimeVector duration times block.succ)
        (hBounds block)
  simp_rw [hSeries]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply congrArg ENNReal.ofReal
    rw [← Real.exp_sum, ← Real.exp_add]
    rw [sum_integral_unusedClockRate
      rates hContinuousEscape duration states times]
    congr 1
    ring
  · intro block _hBlock
    exact (Real.exp_pos _).le

/-- Exact unused-clock resummation for the full bounded measurable rate class. -/
theorem finiteStateTimeDependentMarkovUnusedClockResummation_boundedMeasurable
    (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ)
    (hTimes : times ∈ orderedJumpTimes eventCount duration) :
    ENNReal.ofReal (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        ∏ block : Fin (eventCount + 1),
          ∑' selfEventCount : ℕ,
            ENNReal.ofReal
              ((∫ time in
                  (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
                  (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                    rates.unusedClockRate (states block) time) ^ selfEventCount /
                selfEventCount.factorial) =
      ENNReal.ofReal
        (Real.exp (-finiteStateTimeDependentMarkovIntegratedEscape
          rates duration states times)) := by
  have hBounds (block : Fin (eventCount + 1)) :
      FiniteJumpHistory.boundaryTimeVector duration times block.castSucc ≤
        FiniteJumpHistory.boundaryTimeVector duration times block.succ :=
    FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hDuration hTimes (Fin.castSucc_le_succ block)
  have hSeries (block : Fin (eventCount + 1)) :
      (∑' selfEventCount : ℕ,
        ENNReal.ofReal
          ((∫ time in
              (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
              (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                rates.unusedClockRate (states block) time) ^ selfEventCount /
            selfEventCount.factorial)) =
        ENNReal.ofReal
          (Real.exp
            (∫ time in
              (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
              (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
                rates.unusedClockRate (states block) time)) := by
    have hSetIntegral :
        (∫ time in Ioo
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
              rates.unusedClockRate (states block) time) =
          ∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
              rates.unusedClockRate (states block) time := by
      rw [← integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le (hBounds block)]
    simpa only [lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
      (rates.measurable_unusedClockRate (states block))
      (rates.unusedClockRate_nonneg (states block))
      (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)
      (FiniteJumpHistory.boundaryTimeVector duration times block.succ)
      (rates.intervalIntegrable_unusedClockRate (states block) _ _) _ (hBounds block),
      hSetIntegral] using
      tsum_lintegral_weightedOrderedTimesInInterval_of_intervalIntegrable
        (rates.measurable_unusedClockRate (states block))
        (rates.unusedClockRate_nonneg (states block))
        (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)
        (FiniteJumpHistory.boundaryTimeVector duration times block.succ)
        (rates.intervalIntegrable_unusedClockRate (states block) _ _)
        (hBounds block)
  simp_rw [hSeries]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply congrArg ENNReal.ofReal
    rw [← Real.exp_sum, ← Real.exp_add]
    rw [sum_integral_unusedClockRate_eq_uniformization_mass_sub_integratedEscape]
    congr 1
    ring
  · intro block _hBlock
    exact (Real.exp_pos _).le

/-- The common-clock density on one canonically inserted word factors in extended-nonnegative
form into its retained physical prefactor and the complete product of unused-clock weights. -/
theorem finiteStateTimeDependentMarkovUniformizedSliceDensity_selfEventInsertedStateWord
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (insertionTimes :
      (block : Fin (physicalEventCount + 1)) → Fin (selfEventCounts block) → ℝ)
    (physicalTimes : Fin physicalEventCount → ℝ) :
    ENNReal.ofReal
        (finiteStateTimeDependentMarkovUniformizedSliceDensity initial rates duration
          (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
          (FiniteJumpHistory.selfEventInsertedJumpTimes
            selfEventCounts insertionTimes physicalTimes)) =
      ENNReal.ofReal
          ((initial (states 0)).toReal *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
              finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes) *
        weightedOrderedSelfEventInsertionIntegrand
          (fun block ↦ rates.unusedClockRate (states block))
          selfEventCounts insertionTimes := by
  rw [finiteStateTimeDependentMarkovUniformizedSliceDensity_eq_intensityProduct]
  rw [finiteStateTimeDependentMarkovUniformizedTransitionIntensityProduct_selfEventInsertedStateWord
    rates states selfEventCounts hReduced insertionTimes physicalTimes]
  rw [FiniteJumpHistory.selfEventInsertedStateWord_zero]
  unfold finiteStateTimeDependentMarkovJumpRateProduct
  let retainedPrefactor :=
    (initial (states 0)).toReal *
      Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
        ∏ index : Fin physicalEventCount,
          (rates.rate (physicalTimes index)
            (states index.castSucc) (states index.succ) : ℝ)
  have hRetainedPrefactor : 0 ≤ retainedPrefactor := by
    dsimp only [retainedPrefactor]
    positivity
  rw [show (initial (states 0)).toReal *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
          ((∏ index : Fin physicalEventCount,
              (rates.rate (physicalTimes index)
                (states index.castSucc) (states index.succ) : ℝ)) *
            ∏ block : Fin (physicalEventCount + 1),
              ∏ selfEventIndex : Fin (selfEventCounts block),
                rates.unusedClockRate (states block)
                  (insertionTimes block selfEventIndex)) =
      retainedPrefactor *
        ∏ block : Fin (physicalEventCount + 1),
          ∏ selfEventIndex : Fin (selfEventCounts block),
            rates.unusedClockRate (states block)
              (insertionTimes block selfEventIndex) by
    dsimp only [retainedPrefactor]
    ring]
  rw [ENNReal.ofReal_mul hRetainedPrefactor]
  congr 1
  unfold weightedOrderedSelfEventInsertionIntegrand
    weightedOrderedJumpTimesIntegrand
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro block _hBlock
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro selfEventIndex _hSelfEventIndex
    exact rates.unusedClockRate_nonneg (states block)
      (insertionTimes block selfEventIndex)
  · intro block _hBlock
    exact Finset.prod_nonneg fun selfEventIndex _hSelfEventIndex ↦
      rates.unusedClockRate_nonneg (states block)
        (insertionTimes block selfEventIndex)

/-- Integrating all insertion coordinates for one fixed count vector gives the retained physical
prefactor times the exact factorial-normalized unused-clock integrals on every dwell. -/
theorem lintegral_finiteStateTimeDependentMarkovUniformizedInsertedWordFibre_boundedMeasurable
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount duration) :
    ∫⁻ insertionTimes in
        orderedSelfEventInsertions duration physicalTimes selfEventCounts,
      ENNReal.ofReal
        (finiteStateTimeDependentMarkovUniformizedSliceDensity initial rates duration
          (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)
          (FiniteJumpHistory.selfEventInsertedJumpTimes
            selfEventCounts insertionTimes physicalTimes)) =
      ENNReal.ofReal
          ((initial (states 0)).toReal *
            finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes) *
        (ENNReal.ofReal
            (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
          ∏ block : Fin (physicalEventCount + 1),
            ENNReal.ofReal
              ((∫ time in
                  (FiniteJumpHistory.boundaryTimeVector
                    duration physicalTimes block.castSucc)..
                  (FiniteJumpHistory.boundaryTimeVector
                    duration physicalTimes block.succ),
                    rates.unusedClockRate (states block) time) ^ selfEventCounts block /
                (selfEventCounts block).factorial)) := by
  simp_rw [finiteStateTimeDependentMarkovUniformizedSliceDensity_selfEventInsertedStateWord
    initial rates duration states selfEventCounts hReduced]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_weightedOrderedSelfEventInsertions_of_intervalIntegrable
    (fun block ↦ rates.measurable_unusedClockRate (states block))
    (fun block time ↦ rates.unusedClockRate_nonneg (states block) time)
    selfEventCounts hDuration hPhysicalTimes
    (fun block ↦ rates.intervalIntegrable_unusedClockRate (states block) _ _)]
  have hSetIntegral (block : Fin (physicalEventCount + 1)) :
      (∫ time in Ioo
          (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.castSucc)
          (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.succ),
            rates.unusedClockRate (states block) time) =
        ∫ time in
          (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.castSucc)..
          (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.succ),
            rates.unusedClockRate (states block) time := by
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le
      (FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
        hDuration hPhysicalTimes (Fin.castSucc_le_succ block))]
  simp_rw [hSetIntegral]
  have hInitialJump :
      0 ≤ (initial (states 0)).toReal *
        finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes := by
    unfold finiteStateTimeDependentMarkovJumpRateProduct
    positivity
  rw [show (initial (states 0)).toReal *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
          finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes =
      ((initial (states 0)).toReal *
        finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes) *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration)) by ring]
  rw [ENNReal.ofReal_mul hInitialJump]
  ring

/-- Retained-time coefficient contributed by one fixed vector of inserted self-event counts. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (physicalTimes : Fin physicalEventCount → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((initial (states 0)).toReal *
        finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes) *
    (ENNReal.ofReal (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
      ∏ block : Fin (physicalEventCount + 1),
        ENNReal.ofReal
          ((∫ time in
              (FiniteJumpHistory.boundaryTimeVector
                duration physicalTimes block.castSucc)..
              (FiniteJumpHistory.boundaryTimeVector
                duration physicalTimes block.succ),
                rates.unusedClockRate (states block) time) ^ selfEventCounts block /
            (selfEventCounts block).factorial))

/-- Every fixed-count retained-time insertion coefficient is measurable for bounded measurable
rate rows. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ) :
    Measurable
      (finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
        initial rates duration states selfEventCounts) := by
  unfold finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
  apply Measurable.mul
  · exact (measurable_const.mul
      (measurable_finiteStateTimeDependentMarkovJumpRateProduct rates states)).ennreal_ofReal
  · apply Measurable.const_mul
    apply Finset.measurable_prod
    intro block _hBlock
    apply Measurable.ennreal_ofReal
    apply Measurable.div_const
    apply Measurable.pow_const
    exact rates.measurable_intervalIntegral_unusedClockRate_comp (states block)
      (FiniteJumpHistory.measurable_boundaryTimeVector_apply
        duration block.castSucc)
      (FiniteJumpHistory.measurable_boundaryTimeVector_apply
        duration block.succ)

/-- On the physical ordered simplex, summing every self-event count vector gives exactly the
canonical time-dependent physical jump-slice density. -/
theorem tsum_finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (physicalTimes : Fin physicalEventCount → ℝ)
    (hPhysicalTimes : physicalTimes ∈ orderedJumpTimes physicalEventCount duration) :
    ∑' selfEventCounts : Fin (physicalEventCount + 1) → ℕ,
        finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
          initial rates duration states selfEventCounts physicalTimes =
      ENNReal.ofReal
        (finiteStateTimeDependentMarkovJumpSliceDensity
          initial rates duration states physicalTimes) := by
  unfold finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_left]
  have hCountFactorization :
      (∑' selfEventCounts : Fin (physicalEventCount + 1) → ℕ,
        ∏ block : Fin (physicalEventCount + 1),
          ENNReal.ofReal
            ((∫ time in
                (FiniteJumpHistory.boundaryTimeVector
                  duration physicalTimes block.castSucc)..
                (FiniteJumpHistory.boundaryTimeVector
                  duration physicalTimes block.succ),
                  rates.unusedClockRate (states block) time) ^ selfEventCounts block /
              (selfEventCounts block).factorial)) =
        ∏ block : Fin (physicalEventCount + 1),
          ∑' selfEventCount : ℕ,
            ENNReal.ofReal
              ((∫ time in
                  (FiniteJumpHistory.boundaryTimeVector
                    duration physicalTimes block.castSucc)..
                  (FiniteJumpHistory.boundaryTimeVector
                    duration physicalTimes block.succ),
                    rates.unusedClockRate (states block) time) ^ selfEventCount /
                selfEventCount.factorial) := by
    exact tsum_pi_fin_ennreal fun block selfEventCount ↦
      ENNReal.ofReal
        ((∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration physicalTimes block.succ),
              rates.unusedClockRate (states block) time) ^ selfEventCount /
          selfEventCount.factorial)
  rw [hCountFactorization]
  rw [finiteStateTimeDependentMarkovUnusedClockResummation_boundedMeasurable
    rates hDuration states physicalTimes hPhysicalTimes]
  have hInitialJump :
      0 ≤ (initial (states 0)).toReal *
        finiteStateTimeDependentMarkovJumpRateProduct rates states physicalTimes := by
    unfold finiteStateTimeDependentMarkovJumpRateProduct
    positivity
  rw [← ENNReal.ofReal_mul hInitialJump]
  apply congrArg ENNReal.ofReal
  unfold finiteStateTimeDependentMarkovJumpSliceDensity
  rfl

/-- Deleting one canonically expanded time-dependent virtual word gives the reduced physical word
with the exact integrated insertion-fibre coefficient. -/
theorem map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedInsertedWordSliceMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {physicalEventCount : ℕ}
    (states : Fin (physicalEventCount + 1) → State)
    (selfEventCounts : Fin (physicalEventCount + 1) → ℕ)
    (hReduced : ∀ index : Fin physicalEventCount,
      states index.castSucc ≠ states index.succ) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedWordSliceMeasure initial rates duration
          (FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts)
          (FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts)) =
      Measure.map (embedJumpTimes physicalEventCount states)
        ((volume.restrict (orderedJumpTimes physicalEventCount duration)).withDensity
          (finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
            initial rates duration states selfEventCounts)) := by
  let virtualEventCount :=
    FiniteJumpHistory.selfEventInsertedEventCount selfEventCounts
  let virtualStates :=
    FiniteJumpHistory.selfEventInsertedStateWord states selfEventCounts
  let virtualDensity : (Fin virtualEventCount → ℝ) → ℝ≥0∞ := fun times ↦
    ENNReal.ofReal
      (finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration virtualStates times)
  let merge := FiniteJumpHistory.selfEventInsertedJumpTimeEquiv selfEventCounts
  let insertionDomain :=
    FiniteJumpHistory.selfEventInsertionCoordinateDomain duration selfEventCounts
  have hVirtualDensity : Measurable virtualDensity := by
    exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration virtualStates).ennreal_ofReal
  have hMerge :=
    FiniteJumpHistory.volume_measurePreserving_selfEventInsertedJumpTimeEquiv selfEventCounts
  have hDomain : MeasurableSet insertionDomain :=
    FiniteJumpHistory.measurableSet_selfEventInsertionCoordinateDomain
      hDuration selfEventCounts
  have hWeightedMerge :
      Measure.map merge
          ((volume.restrict insertionDomain).withDensity (virtualDensity ∘ merge)) =
        (volume.restrict (orderedJumpTimes virtualEventCount duration)).withDensity
          virtualDensity := by
    rw [Measure.map_withDensity_comp _ hMerge.measurable virtualDensity hVirtualDensity]
    rw [FiniteJumpHistory.map_volume_restrict_selfEventInsertionCoordinateDomain
      hDuration selfEventCounts]
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
  unfold finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
  change Measure.map FiniteJumpHistory.deleteSelfEvents
      (Measure.map (embedJumpTimes virtualEventCount virtualStates)
        ((volume.restrict (orderedJumpTimes virtualEventCount duration)).withDensity
          virtualDensity)) = _
  rw [Measure.map_map FiniteJumpHistory.measurable_deleteSelfEvents
    (measurable_embedJumpTimes virtualEventCount virtualStates)]
  rw [← hWeightedMerge]
  rw [Measure.map_map hDeleteEmbed hMerge.measurable]
  rw [hFunction]
  rw [← Measure.map_map (measurable_embedJumpTimes physicalEventCount states) measurable_snd]
  congr 1
  rw [Measure.volume_eq_prod]
  rw [Measure.map_snd_restrict_withDensity_eq_withDensity_setLIntegral
    volume volume insertionDomain hDomain (virtualDensity ∘ merge)
    (hVirtualDensity.comp hMerge.measurable)]
  rw [← withDensity_indicator (measurableSet_orderedJumpTimes
    physicalEventCount duration)]
  congr 1
  funext physicalTimes
  by_cases hPhysicalTimes :
      physicalTimes ∈ orderedJumpTimes physicalEventCount duration
  · rw [Set.indicator_of_mem hPhysicalTimes]
    have hFibre :
        (fun insertionTimes ↦ (insertionTimes, physicalTimes)) ⁻¹' insertionDomain =
          orderedSelfEventInsertions duration physicalTimes selfEventCounts := by
      ext insertionTimes
      simp only [Set.mem_preimage, insertionDomain,
        FiniteJumpHistory.selfEventInsertionCoordinateDomain,
        Set.mem_ofPred_eq, hPhysicalTimes, true_and]
    rw [hFibre]
    unfold finiteStateTimeDependentMarkovUniformizedInsertedWordFibreCoefficient
    simpa only [Function.comp_apply, virtualDensity, merge,
      FiniteJumpHistory.selfEventInsertedJumpTimeEquiv_apply] using
        lintegral_finiteStateTimeDependentMarkovUniformizedInsertedWordFibre_boundedMeasurable
          initial rates hDuration states selfEventCounts hReduced
          physicalTimes hPhysicalTimes
  · rw [Set.indicator_of_notMem hPhysicalTimes]
    have hFibre :
        (fun insertionTimes ↦ (insertionTimes, physicalTimes)) ⁻¹' insertionDomain = ∅ := by
      ext insertionTimes
      simp [insertionDomain, FiniteJumpHistory.selfEventInsertionCoordinateDomain,
        hPhysicalTimes]
    rw [hFibre]
    simp

end FiniteMarkovProcesses.Probability
