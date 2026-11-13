/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw

/-!
# Bounded time-dependent finite-state Markov jump log actions

This module identifies the exact initial, jump-rate, and integrated-escape sectors in the
pointwise log-density ratio of two bounded measurable time-dependent finite-state jump laws.

Measure-level Radon--Nikodym and Girsanov identities are derived in
`FiniteStateTimeDependentMarkovJumpRadonNikodym`; large-deviation lower bounds are separate
results.

## Main results

- `FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport`: pointwise common rate support.
- `finiteStateTimeDependentMarkovJumpSliceLogAction`: complete fixed-word log action.
- `finiteStateTimeDependentMarkovJumpSliceDensity_div_eq_exp_logAction`: exact density ratio.
- `finiteStateTimeDependentMarkovJumpLogAction`: measurable complete-history action.
- `finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBound`: pathwise action cap.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Two bounded measurable time-dependent rate families have identical directed support at every
physical time. -/
def FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) : Prop :=
  ∀ time source target,
    rates.rate time source target = 0 ↔ referenceRates.rate time source target = 0

/-- A time-dependent generator/initial pair assigns positive density to a complete history when
the initial state and every used time-labelled directed edge have positive weight. -/
def FiniteStateTimeDependentMarkovJumpDensityPositiveAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (history : FiniteJumpHistory State) : Prop :=
  0 < (initial history.initialState).toReal ∧
    ∀ index : Fin history.jumpCount,
      0 < (rates.rate (history.jumpTimes index)
        (history.states index.castSucc) (history.states index.succ) : ℝ)

/-- Every bounded time-dependent complete-history density is nonnegative. -/
theorem finiteStateTimeDependentMarkovJumpDensity_nonneg
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (history : FiniteJumpHistory State) :
    0 ≤ finiteStateTimeDependentMarkovJumpDensity initial rates duration history := by
  rcases history with ⟨eventCount, states, times⟩
  unfold finiteStateTimeDependentMarkovJumpDensity
    finiteStateTimeDependentMarkovJumpSliceDensity
    finiteStateTimeDependentMarkovJumpRateProduct
  exact mul_nonneg
    (mul_nonneg ENNReal.toReal_nonneg
      (Finset.prod_nonneg fun index _hIndex =>
        NNReal.coe_nonneg (rates.rate (times index)
          (states index.castSucc) (states index.succ))))
    (Real.exp_pos _).le

/-- A nonzero bounded time-dependent density exposes positive initial weight and every positive
used time-labelled rate. -/
theorem finiteStateTimeDependentMarkovJumpDensityPositiveAt_of_ne_zero
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (history : FiniteJumpHistory State)
    (hDensity :
      finiteStateTimeDependentMarkovJumpDensity initial rates duration history ≠ 0) :
    FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history := by
  rcases history with ⟨eventCount, states, times⟩
  change finiteStateTimeDependentMarkovJumpSliceDensity
    initial rates duration states times ≠ 0 at hDensity
  have hInitial : (initial (states 0)).toReal ≠ 0 := by
    intro hZero
    apply hDensity
    unfold finiteStateTimeDependentMarkovJumpSliceDensity
    rw [hZero, zero_mul, zero_mul]
  have hRate (index : Fin eventCount) :
      (rates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ) ≠ 0 := by
    intro hZero
    apply hDensity
    unfold finiteStateTimeDependentMarkovJumpSliceDensity
      finiteStateTimeDependentMarkovJumpRateProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ index) hZero, mul_zero, zero_mul]
  constructor
  · exact lt_of_le_of_ne ENNReal.toReal_nonneg hInitial.symm
  · intro index
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (hRate index).symm

/-- Positive-density support is exactly positivity of the explicit complete-history density. -/
theorem finiteStateTimeDependentMarkovJumpDensityPositiveAt_iff
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (history : FiniteJumpHistory State) :
    FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history ↔
      0 < finiteStateTimeDependentMarkovJumpDensity initial rates duration history := by
  constructor
  · intro hPositive
    rcases history with ⟨eventCount, states, times⟩
    unfold finiteStateTimeDependentMarkovJumpDensity
      finiteStateTimeDependentMarkovJumpSliceDensity
    exact mul_pos
      (mul_pos hPositive.1 (Finset.prod_pos fun index _hIndex ↦ hPositive.2 index))
      (Real.exp_pos _)
  · intro hDensity
    exact finiteStateTimeDependentMarkovJumpDensityPositiveAt_of_ne_zero
      initial rates duration history hDensity.ne'

/-- Positive-density support is a measurable subset of the finite-history carrier. -/
theorem measurableSet_finiteStateTimeDependentMarkovJumpDensityPositiveAt
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    MeasurableSet
      {history : FiniteJumpHistory State |
        FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history} := by
  rw [show {history : FiniteJumpHistory State |
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history} =
      finiteStateTimeDependentMarkovJumpDensity initial rates duration ⁻¹' Set.Ioi 0 by
    ext history
    exact finiteStateTimeDependentMarkovJumpDensityPositiveAt_iff
      initial rates duration history]
  exact (measurableSet_Ioi.preimage
    (measurable_finiteStateTimeDependentMarkovJumpDensity initial rates duration))

/-- The normalized physical time-dependent jump law is concentrated on histories with positive
initial weight and positive rate on every used time-labelled directed edge. -/
theorem ae_finiteStateTimeDependentMarkovJumpDensityPositiveAt
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    ∀ᵐ history ∂finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration,
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history := by
  rw [finiteStateTimeDependentMarkovJumpDensityMeasure_eq_withDensity]
  rw [ae_withDensity_iff
    (measurable_finiteStateTimeDependentMarkovJumpDensityENNReal initial rates duration)]
  filter_upwards [] with history hDensity
  exact finiteStateTimeDependentMarkovJumpDensityPositiveAt_of_ne_zero
    initial rates duration history (by
      intro hZero
      apply hDensity
      simp [finiteStateTimeDependentMarkovJumpDensityENNReal, hZero])

/-- Complete candidate-to-reference log action on one fixed state-word/time slice. -/
noncomputable def finiteStateTimeDependentMarkovJumpSliceLogAction
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) : ℝ :=
  Real.log ((initial (states 0)).toReal / (referenceInitial (states 0)).toReal) +
    ∑ index : Fin eventCount,
      Real.log
        ((rates.rate (times index)
            (states index.castSucc) (states index.succ) : ℝ) /
          (referenceRates.rate (times index)
            (states index.castSucc) (states index.succ) : ℝ)) +
    (finiteStateTimeDependentMarkovIntegratedEscape
      referenceRates duration states times -
        finiteStateTimeDependentMarkovIntegratedEscape rates duration states times)

/-- The log of a positive fixed-word bounded time-dependent density separates into its initial,
jump, and integrated-escape sectors. -/
theorem log_finiteStateTimeDependentMarkovJumpSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hRates : ∀ index : Fin eventCount,
      0 < (rates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ)) :
    Real.log (finiteStateTimeDependentMarkovJumpSliceDensity
        initial rates duration states times) =
      Real.log (initial (states 0)).toReal +
        ∑ index : Fin eventCount,
          Real.log (rates.rate (times index)
            (states index.castSucc) (states index.succ) : ℝ) -
        finiteStateTimeDependentMarkovIntegratedEscape
          rates duration states times := by
  have hRateProduct : 0 <
      finiteStateTimeDependentMarkovJumpRateProduct rates states times :=
    Finset.prod_pos fun index _hIndex => hRates index
  unfold finiteStateTimeDependentMarkovJumpSliceDensity
  rw [Real.log_mul (mul_ne_zero hInitial.ne' hRateProduct.ne') (Real.exp_ne_zero _),
    Real.log_mul hInitial.ne' hRateProduct.ne', Real.log_exp]
  unfold finiteStateTimeDependentMarkovJumpRateProduct
  rw [Real.log_prod]
  · ring
  · intro index _hIndex
    exact (hRates index).ne'

/-- Positive initial weight and used rates make the complete fixed-word density positive. -/
theorem finiteStateTimeDependentMarkovJumpSliceDensity_pos
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hRates : ∀ index : Fin eventCount,
      0 < (rates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ)) :
    0 < finiteStateTimeDependentMarkovJumpSliceDensity
      initial rates duration states times := by
  unfold finiteStateTimeDependentMarkovJumpSliceDensity
  exact mul_pos
    (mul_pos hInitial (Finset.prod_pos fun index _hIndex => hRates index))
    (Real.exp_pos _)

/-- The log density ratio is exactly the sum of the initial, time-labelled jump-rate, and
integrated-escape sectors. -/
theorem log_finiteStateTimeDependentMarkovJumpSliceDensity_div
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hReferenceInitial : 0 < (referenceInitial (states 0)).toReal)
    (hRates : ∀ index : Fin eventCount,
      0 < (rates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ))
    (hReferenceRates : ∀ index : Fin eventCount,
      0 < (referenceRates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ)) :
    Real.log
        (finiteStateTimeDependentMarkovJumpSliceDensity
            initial rates duration states times /
          finiteStateTimeDependentMarkovJumpSliceDensity
            referenceInitial referenceRates duration states times) =
      finiteStateTimeDependentMarkovJumpSliceLogAction
        initial referenceInitial rates referenceRates duration states times := by
  rw [Real.log_div
    (finiteStateTimeDependentMarkovJumpSliceDensity_pos
      initial rates duration states times hInitial hRates).ne'
    (finiteStateTimeDependentMarkovJumpSliceDensity_pos
      referenceInitial referenceRates duration states times
        hReferenceInitial hReferenceRates).ne',
    log_finiteStateTimeDependentMarkovJumpSliceDensity
      initial rates duration states times hInitial hRates,
    log_finiteStateTimeDependentMarkovJumpSliceDensity
      referenceInitial referenceRates duration states times
        hReferenceInitial hReferenceRates]
  unfold finiteStateTimeDependentMarkovJumpSliceLogAction
  rw [Real.log_div hInitial.ne' hReferenceInitial.ne']
  simp_rw [Real.log_div (hRates _).ne' (hReferenceRates _).ne']
  rw [Finset.sum_sub_distrib]
  ring

/-- The fixed-word density ratio is the exponential of the complete time-dependent action. -/
theorem finiteStateTimeDependentMarkovJumpSliceDensity_div_eq_exp_logAction
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hReferenceInitial : 0 < (referenceInitial (states 0)).toReal)
    (hRates : ∀ index : Fin eventCount,
      0 < (rates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ))
    (hReferenceRates : ∀ index : Fin eventCount,
      0 < (referenceRates.rate (times index)
        (states index.castSucc) (states index.succ) : ℝ)) :
    finiteStateTimeDependentMarkovJumpSliceDensity
          initial rates duration states times /
        finiteStateTimeDependentMarkovJumpSliceDensity
          referenceInitial referenceRates duration states times =
      Real.exp (finiteStateTimeDependentMarkovJumpSliceLogAction
        initial referenceInitial rates referenceRates duration states times) := by
  have hRatio : 0 <
      finiteStateTimeDependentMarkovJumpSliceDensity
          initial rates duration states times /
        finiteStateTimeDependentMarkovJumpSliceDensity
          referenceInitial referenceRates duration states times :=
    div_pos
      (finiteStateTimeDependentMarkovJumpSliceDensity_pos
        initial rates duration states times hInitial hRates)
      (finiteStateTimeDependentMarkovJumpSliceDensity_pos
        referenceInitial referenceRates duration states times
          hReferenceInitial hReferenceRates)
  calc
    _ = Real.exp (Real.log
        (finiteStateTimeDependentMarkovJumpSliceDensity
            initial rates duration states times /
          finiteStateTimeDependentMarkovJumpSliceDensity
            referenceInitial referenceRates duration states times)) :=
      (Real.exp_log hRatio).symm
    _ = _ := by
      rw [log_finiteStateTimeDependentMarkovJumpSliceDensity_div
        initial referenceInitial rates referenceRates duration states times
          hInitial hReferenceInitial hRates hReferenceRates]

/-- Complete candidate-to-reference time-dependent log action on the finite-history carrier. -/
noncomputable def finiteStateTimeDependentMarkovJumpLogAction
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateTimeDependentMarkovJumpSliceLogAction
        initial referenceInitial rates referenceRates duration states times

/-- The complete bounded time-dependent log action is measurable. -/
theorem measurable_finiteStateTimeDependentMarkovJumpLogAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    Measurable (finiteStateTimeDependentMarkovJumpLogAction
      initial referenceInitial rates referenceRates duration) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  unfold finiteStateTimeDependentMarkovJumpLogAction
    finiteStateTimeDependentMarkovJumpSliceLogAction
  exact ((measurable_const.add <| Finset.measurable_sum Finset.univ fun index _hIndex =>
    (((rates.measurable_rate
      (states index.castSucc) (states index.succ)).coe_nnreal_real.comp
        (measurable_pi_apply index)).div
      ((referenceRates.measurable_rate
        (states index.castSucc) (states index.succ)).coe_nnreal_real.comp
          (measurable_pi_apply index))).log)).add
    ((measurable_finiteStateTimeDependentMarkovIntegratedEscape
      referenceRates duration states).sub
      (measurable_finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states))

/-- When candidate and reference start from the same law, the initial log-ratio sector vanishes
pointwise, including zero-mass states under Lean's totalized logarithm.  The resulting dynamic
action is therefore independent of which common initial law was supplied. -/
theorem finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq
    (firstInitial secondInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovJumpLogAction
        firstInitial firstInitial rates referenceRates duration =
      finiteStateTimeDependentMarkovJumpLogAction
        secondInitial secondInitial rates referenceRates duration := by
  funext history
  rcases history with ⟨eventCount, states, times⟩
  change finiteStateTimeDependentMarkovJumpSliceLogAction
      firstInitial firstInitial rates referenceRates duration states times =
    finiteStateTimeDependentMarkovJumpSliceLogAction
      secondInitial secondInitial rates referenceRates duration states times
  have hFirst : Real.log
      ((firstInitial (states 0)).toReal / (firstInitial (states 0)).toReal) = 0 := by
    by_cases hZero : (firstInitial (states 0)).toReal = 0
    · simp [hZero]
    · rw [div_self hZero, Real.log_one]
  have hSecond : Real.log
      ((secondInitial (states 0)).toReal / (secondInitial (states 0)).toReal) = 0 := by
    by_cases hZero : (secondInitial (states 0)).toReal = 0
    · simp [hZero]
    · rw [div_self hZero, Real.log_one]
  unfold finiteStateTimeDependentMarkovJumpSliceLogAction
  rw [hFirst, hSecond]

/-- If every used candidate jump has log rate ratio bounded by `jumpLogBound`, then on an ordered
physical history the complete action is bounded by the jump count times that bound plus the
reference escape bound times the horizon.  The common initial law contributes exactly zero. -/
theorem finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBound
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) (jumpLogBound : ℝ)
    (hJumpLogBound : ∀ time source target,
      0 < (rates.rate time source target : ℝ) →
        Real.log ((rates.rate time source target : ℝ) /
          (referenceRates.rate time source target : ℝ)) ≤ jumpLogBound)
    (history : FiniteJumpHistory State)
    (hOrdered : history.OrderedBefore duration)
    (hPositive : FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history) :
    finiteStateTimeDependentMarkovJumpLogAction
        initial initial rates referenceRates duration history ≤
      (history.jumpCount : ℝ) * jumpLogBound +
        (referenceRates.escapeBound : ℝ) * duration := by
  rcases history with ⟨eventCount, states, times⟩
  change
    finiteStateTimeDependentMarkovJumpSliceLogAction
        initial initial rates referenceRates duration states times ≤
      (eventCount : ℝ) * jumpLogBound +
        (referenceRates.escapeBound : ℝ) * duration
  have hInitialNe : (initial (states 0)).toReal ≠ 0 := hPositive.1.ne'
  have hJumpSum :
      (∑ index : Fin eventCount,
        Real.log
          ((rates.rate (times index)
              (states index.castSucc) (states index.succ) : ℝ) /
            (referenceRates.rate (times index)
              (states index.castSucc) (states index.succ) : ℝ))) ≤
        (eventCount : ℝ) * jumpLogBound := by
    calc
      _ ≤ ∑ _index : Fin eventCount, jumpLogBound := by
        apply Finset.sum_le_sum
        intro index _hIndex
        exact hJumpLogBound (times index)
          (states index.castSucc) (states index.succ) (hPositive.2 index)
      _ = (eventCount : ℝ) * jumpLogBound := by simp
  have hCandidateEscapeNonnegative :
      0 ≤ finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states times :=
    finiteStateTimeDependentMarkovIntegratedEscape_nonneg_of_mem_orderedJumpTimes
      rates hDuration states times hOrdered
  have hReferenceEscapeBound :
      finiteStateTimeDependentMarkovIntegratedEscape
          referenceRates duration states times ≤
        (referenceRates.escapeBound : ℝ) * duration :=
    finiteStateTimeDependentMarkovIntegratedEscape_le_bound_mul_duration_of_ordered
      referenceRates hDuration states times hOrdered
  unfold finiteStateTimeDependentMarkovJumpSliceLogAction
  rw [div_self hInitialNe, Real.log_one, zero_add]
  linarith

/-- An absolute bound on every used jump log ratio gives an absolute complete-action bound by
physical jump count plus the two declared escape budgets. -/
theorem abs_finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBounds
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) (jumpLogAbsoluteBound : ℝ)
    (hJumpLogAbsoluteBound : ∀ time source target,
      0 < (rates.rate time source target : ℝ) →
        |Real.log ((rates.rate time source target : ℝ) /
          (referenceRates.rate time source target : ℝ))| ≤ jumpLogAbsoluteBound)
    (history : FiniteJumpHistory State)
    (hOrdered : history.OrderedBefore duration)
    (hPositive : FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history) :
    |finiteStateTimeDependentMarkovJumpLogAction
        initial initial rates referenceRates duration history| ≤
      (history.jumpCount : ℝ) * jumpLogAbsoluteBound +
        ((referenceRates.escapeBound : ℝ) + (rates.escapeBound : ℝ)) * duration := by
  rcases history with ⟨eventCount, states, times⟩
  change
    |finiteStateTimeDependentMarkovJumpSliceLogAction
        initial initial rates referenceRates duration states times| ≤
      (eventCount : ℝ) * jumpLogAbsoluteBound +
        ((referenceRates.escapeBound : ℝ) + (rates.escapeBound : ℝ)) * duration
  have hInitialNe : (initial (states 0)).toReal ≠ 0 := hPositive.1.ne'
  let jumpSum := ∑ index : Fin eventCount,
    Real.log
      ((rates.rate (times index)
          (states index.castSucc) (states index.succ) : ℝ) /
        (referenceRates.rate (times index)
          (states index.castSucc) (states index.succ) : ℝ))
  have hJumpSum : |jumpSum| ≤ (eventCount : ℝ) * jumpLogAbsoluteBound := by
    calc
      |jumpSum| ≤ ∑ index : Fin eventCount,
          |Real.log
            ((rates.rate (times index)
                (states index.castSucc) (states index.succ) : ℝ) /
              (referenceRates.rate (times index)
                (states index.castSucc) (states index.succ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index : Fin eventCount, jumpLogAbsoluteBound := by
        apply Finset.sum_le_sum
        intro index _hIndex
        exact hJumpLogAbsoluteBound (times index)
          (states index.castSucc) (states index.succ) (hPositive.2 index)
      _ = (eventCount : ℝ) * jumpLogAbsoluteBound := by simp
  have hCandidateEscapeNonnegative :
      0 ≤ finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states times :=
    finiteStateTimeDependentMarkovIntegratedEscape_nonneg_of_mem_orderedJumpTimes
      rates hDuration states times hOrdered
  have hReferenceEscapeNonnegative :
      0 ≤ finiteStateTimeDependentMarkovIntegratedEscape
        referenceRates duration states times :=
    finiteStateTimeDependentMarkovIntegratedEscape_nonneg_of_mem_orderedJumpTimes
      referenceRates hDuration states times hOrdered
  have hCandidateEscapeBound :
      finiteStateTimeDependentMarkovIntegratedEscape rates duration states times ≤
        (rates.escapeBound : ℝ) * duration :=
    finiteStateTimeDependentMarkovIntegratedEscape_le_bound_mul_duration_of_ordered
      rates hDuration states times hOrdered
  have hReferenceEscapeBound :
      finiteStateTimeDependentMarkovIntegratedEscape referenceRates duration states times ≤
        (referenceRates.escapeBound : ℝ) * duration :=
    finiteStateTimeDependentMarkovIntegratedEscape_le_bound_mul_duration_of_ordered
      referenceRates hDuration states times hOrdered
  have hEscapeDifference :
      |finiteStateTimeDependentMarkovIntegratedEscape referenceRates duration states times -
          finiteStateTimeDependentMarkovIntegratedEscape rates duration states times| ≤
        ((referenceRates.escapeBound : ℝ) + (rates.escapeBound : ℝ)) * duration := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  unfold finiteStateTimeDependentMarkovJumpSliceLogAction
  rw [div_self hInitialNe, Real.log_one, zero_add]
  exact (abs_add_le _ _).trans (add_le_add hJumpSum hEscapeDifference)

/-- Common initial and pointwise directed support give identical zero sets for every fixed-word
time-dependent density. -/
theorem finiteStateTimeDependentMarkovJumpSliceDensity_eq_zero_iff
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    finiteStateTimeDependentMarkovJumpSliceDensity
        initial rates duration states times = 0 ↔
      finiteStateTimeDependentMarkovJumpSliceDensity
        referenceInitial referenceRates duration states times = 0 := by
  have hInitialZero :
      (initial (states 0)).toReal = 0 ↔
        (referenceInitial (states 0)).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, initial.apply_ne_top,
      referenceInitial.apply_ne_top, or_false]
    exact hInitialSupport (states 0)
  have hRateZero (index : Fin eventCount) :
      (rates.rate (times index)
          (states index.castSucc) (states index.succ) : ℝ) = 0 ↔
        (referenceRates.rate (times index)
          (states index.castSucc) (states index.succ) : ℝ) = 0 := by
    norm_cast
    exact hRateSupport (times index)
      (states index.castSucc) (states index.succ)
  have hProductZero :
      finiteStateTimeDependentMarkovJumpRateProduct rates states times = 0 ↔
        finiteStateTimeDependentMarkovJumpRateProduct referenceRates states times = 0 := by
    unfold finiteStateTimeDependentMarkovJumpRateProduct
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    exact exists_congr fun index => hRateZero index
  unfold finiteStateTimeDependentMarkovJumpSliceDensity
  simp only [mul_eq_zero, Real.exp_ne_zero, or_false]
  exact or_congr hInitialZero hProductZero

/-- Common support gives identical zero sets for the complete bounded time-dependent densities. -/
theorem finiteStateTimeDependentMarkovJumpDensity_eq_zero_iff
    {initial referenceInitial : PMF State}
    {rates referenceRates : FiniteStateTimeDependentMarkovRate State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : ℝ) (history : FiniteJumpHistory State) :
    finiteStateTimeDependentMarkovJumpDensity initial rates duration history = 0 ↔
      finiteStateTimeDependentMarkovJumpDensity
        referenceInitial referenceRates duration history = 0 := by
  rcases history with ⟨eventCount, states, times⟩
  exact finiteStateTimeDependentMarkovJumpSliceDensity_eq_zero_iff
    hInitialSupport hRateSupport duration states times

/-- On common positive support, the complete density ratio is the exponential of the complete
time-dependent log action. -/
theorem finiteStateTimeDependentMarkovJumpDensity_div_eq_exp_logAction
    (initial referenceInitial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (history : FiniteJumpHistory State)
    (hPositive : FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history)
    (hReferencePositive :
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt
        referenceInitial referenceRates history) :
    finiteStateTimeDependentMarkovJumpDensity initial rates duration history /
        finiteStateTimeDependentMarkovJumpDensity
          referenceInitial referenceRates duration history =
      Real.exp (finiteStateTimeDependentMarkovJumpLogAction
        initial referenceInitial rates referenceRates duration history) := by
  rcases history with ⟨eventCount, states, times⟩
  exact finiteStateTimeDependentMarkovJumpSliceDensity_div_eq_exp_logAction
    initial referenceInitial rates referenceRates duration states times
      hPositive.1 hReferencePositive.1 hPositive.2 hReferencePositive.2

end

end FiniteMarkovProcesses.InformationTheory
