/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpLaw

/-!
# Finite-state Markov jump log actions

This module derives the complete pointwise log-density action between two finite-state Markov
jump densities on the common physical-history carrier. Initial, jump-rate, and dwell/escape
sectors remain separately visible.

Measure-level Radon--Nikodym and fluctuation theorems require exact normalization and are kept in
later modules; no symbolic density is promoted here.

## Main results

- `finiteStateMarkovJumpSliceLogAction`: the complete fixed-slice action.
- `log_finiteStateMarkovJumpSliceDensity`: the exact log of a positive physical density.
- `log_finiteStateMarkovJumpSliceDensity_div`: exact sector decomposition of the density ratio.
- `finiteStateMarkovJumpSliceDensity_div_eq_exp_logAction`: multiplicative action identity.
- `finiteStateMarkovJumpLogAction`: the action on the unbounded history carrier.
- `finiteStateMarkovInitialLogRatio`, `finiteStateMarkovTransitionLogRatio`, and
  `finiteStateMarkovEscapeRateDifference`: reusable weights of its three sectors.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

variable {State : Type u} [Fintype State]

/-- A generator/initial pair assigns a strictly positive density to one complete history when its
initial state and every used directed edge have positive weight. -/
def FiniteStateMarkovJumpDensityPositiveAt
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (history : FiniteJumpHistory State) : Prop :=
  0 < (initial history.initialState).toReal ∧
    ∀ i : Fin history.jumpCount,
      0 < (generator.rate (history.states i.castSucc) (history.states i.succ) : ℝ)

/-- Every complete physical density is nonnegative. -/
theorem finiteStateMarkovJumpDensity_nonneg
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State) :
    0 ≤ finiteStateMarkovJumpDensity initial generator T history := by
  rcases history with ⟨n, states, times⟩
  exact finiteStateMarkovJumpSliceDensity_nonneg initial generator T states times

/-- A nonzero complete density exposes positive initial weight and every positive used rate. -/
theorem finiteStateMarkovJumpDensityPositiveAt_of_ne_zero
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State)
    (hDensity : finiteStateMarkovJumpDensity initial generator T history ≠ 0) :
    FiniteStateMarkovJumpDensityPositiveAt initial generator history := by
  rcases history with ⟨n, states, times⟩
  change finiteStateMarkovJumpSliceDensity initial generator T states times ≠ 0 at hDensity
  have hInitial : (initial (states 0)).toReal ≠ 0 := by
    intro hZero
    apply hDensity
    unfold finiteStateMarkovJumpSliceDensity
    rw [hZero, zero_mul, zero_mul]
  have hRate (i : Fin n) :
      (generator.rate (states i.castSucc) (states i.succ) : ℝ) ≠ 0 := by
    intro hZero
    apply hDensity
    unfold finiteStateMarkovJumpSliceDensity
    have hProduct : finiteStateMarkovJumpRateProduct generator states = 0 := by
      unfold finiteStateMarkovJumpRateProduct
      exact Finset.prod_eq_zero (Finset.mem_univ i) hZero
    rw [hProduct, mul_zero, zero_mul]
  constructor
  · exact lt_of_le_of_ne ENNReal.toReal_nonneg hInitial.symm
  · intro i
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (hRate i).symm

/-- Complete candidate-to-reference log action on one fixed state-word/time slice. -/
noncomputable def finiteStateMarkovJumpSliceLogAction
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) : ℝ :=
  Real.log ((initial (states 0)).toReal / (referenceInitial (states 0)).toReal) +
    ∑ i : Fin n,
      Real.log
        ((generator.rate (states i.castSucc) (states i.succ) : ℝ) /
          (referenceGenerator.rate (states i.castSucc) (states i.succ) : ℝ)) +
    ∑ i : Fin (n + 1),
      ((referenceGenerator.escapeRate (states i) : ℝ) -
          (generator.escapeRate (states i) : ℝ)) *
        FiniteJumpHistory.dwellTimeVector T times i

/-- The log of a positive fixed-word density separates into initial, jump, and integrated-escape
terms. -/
theorem log_finiteStateMarkovJumpSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hRates : ∀ i : Fin n,
      0 < (generator.rate (states i.castSucc) (states i.succ) : ℝ)) :
    Real.log (finiteStateMarkovJumpSliceDensity initial generator T states times) =
      Real.log (initial (states 0)).toReal +
        ∑ i : Fin n,
          Real.log (generator.rate (states i.castSucc) (states i.succ) : ℝ) -
        finiteStateMarkovIntegratedEscape generator T states times := by
  have hRateProduct : 0 < finiteStateMarkovJumpRateProduct generator states := by
    exact Finset.prod_pos fun i _ => hRates i
  unfold finiteStateMarkovJumpSliceDensity
  rw [Real.log_mul (mul_ne_zero hInitial.ne' hRateProduct.ne') (Real.exp_ne_zero _),
    Real.log_mul hInitial.ne' hRateProduct.ne', Real.log_exp]
  unfold finiteStateMarkovJumpRateProduct
  rw [Real.log_prod]
  · ring
  · intro i _
    exact (hRates i).ne'

/-- A positive fixed-word density is strictly positive. -/
theorem finiteStateMarkovJumpSliceDensity_pos
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hRates : ∀ i : Fin n,
      0 < (generator.rate (states i.castSucc) (states i.succ) : ℝ)) :
    0 < finiteStateMarkovJumpSliceDensity initial generator T states times := by
  unfold finiteStateMarkovJumpSliceDensity
  exact mul_pos (mul_pos hInitial (Finset.prod_pos fun i _ => hRates i)) (Real.exp_pos _)

/-- Initial-state log likelihood ratio from a candidate law to a reference law. -/
noncomputable def finiteStateMarkovInitialLogRatio
    (initial referenceInitial : PMF State) (state : State) : ℝ :=
  Real.log ((initial state).toReal / (referenceInitial state).toReal)

/-- Directed transition log-rate ratio from a candidate generator to a reference generator. -/
noncomputable def finiteStateMarkovTransitionLogRatio
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (source target : State) : ℝ :=
  Real.log ((generator.rate source target : ℝ) /
    (referenceGenerator.rate source target : ℝ))

/-- Escape-rate compensator accumulated during the dwell at one state. -/
def finiteStateMarkovEscapeRateDifference
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (state : State) : ℝ :=
  (referenceGenerator.escapeRate state : ℝ) - (generator.escapeRate state : ℝ)

omit [Fintype State] in
/-- A generator transition log ratio vanishes on virtual diagonal events. -/
@[simp]
theorem finiteStateMarkovTransitionLogRatio_self
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (state : State) :
    finiteStateMarkovTransitionLogRatio generator referenceGenerator state state = 0 := by
  simp [finiteStateMarkovTransitionLogRatio, generator.rate_self,
    referenceGenerator.rate_self]

/-- The log density ratio is exactly the sum of the initial, jump-rate, and dwell compensator
sectors. -/
theorem log_finiteStateMarkovJumpSliceDensity_div
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hReferenceInitial : 0 < (referenceInitial (states 0)).toReal)
    (hRates : ∀ i : Fin n,
      0 < (generator.rate (states i.castSucc) (states i.succ) : ℝ))
    (hReferenceRates : ∀ i : Fin n,
      0 < (referenceGenerator.rate (states i.castSucc) (states i.succ) : ℝ)) :
    Real.log
        (finiteStateMarkovJumpSliceDensity initial generator T states times /
          finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times) =
      finiteStateMarkovJumpSliceLogAction initial referenceInitial generator
        referenceGenerator T states times := by
  rw [Real.log_div
    (finiteStateMarkovJumpSliceDensity_pos initial generator T states times
      hInitial hRates).ne'
    (finiteStateMarkovJumpSliceDensity_pos referenceInitial referenceGenerator T states times
      hReferenceInitial hReferenceRates).ne',
    log_finiteStateMarkovJumpSliceDensity initial generator T states times hInitial hRates,
    log_finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times
      hReferenceInitial hReferenceRates]
  unfold finiteStateMarkovJumpSliceLogAction finiteStateMarkovIntegratedEscape
  rw [Real.log_div hInitial.ne' hReferenceInitial.ne']
  simp_rw [Real.log_div (hRates _).ne' (hReferenceRates _).ne']
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- The fixed-word density ratio is the exponential of the complete sector action. -/
theorem finiteStateMarkovJumpSliceDensity_div_eq_exp_logAction
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (hInitial : 0 < (initial (states 0)).toReal)
    (hReferenceInitial : 0 < (referenceInitial (states 0)).toReal)
    (hRates : ∀ i : Fin n,
      0 < (generator.rate (states i.castSucc) (states i.succ) : ℝ))
    (hReferenceRates : ∀ i : Fin n,
      0 < (referenceGenerator.rate (states i.castSucc) (states i.succ) : ℝ)) :
    finiteStateMarkovJumpSliceDensity initial generator T states times /
        finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times =
      Real.exp (finiteStateMarkovJumpSliceLogAction initial referenceInitial generator
        referenceGenerator T states times) := by
  have hRatio : 0 <
      finiteStateMarkovJumpSliceDensity initial generator T states times /
        finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times :=
    div_pos
      (finiteStateMarkovJumpSliceDensity_pos initial generator T states times hInitial hRates)
      (finiteStateMarkovJumpSliceDensity_pos referenceInitial referenceGenerator T states times
        hReferenceInitial hReferenceRates)
  calc
    _ = Real.exp (Real.log
        (finiteStateMarkovJumpSliceDensity initial generator T states times /
          finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times)) :=
      (Real.exp_log hRatio).symm
    _ = _ := by
      rw [log_finiteStateMarkovJumpSliceDensity_div initial referenceInitial generator
        referenceGenerator T states times hInitial hReferenceInitial hRates hReferenceRates]

/-- Complete candidate-to-reference log action on the unbounded history carrier. -/
noncomputable def finiteStateMarkovJumpLogAction
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateMarkovJumpSliceLogAction initial referenceInitial generator
        referenceGenerator T states times

/-- The complete log action is measurable on the unbounded history carrier. -/
theorem measurable_finiteStateMarkovJumpLogAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovJumpLogAction initial referenceInitial generator
      referenceGenerator T) := by
  rw [measurable_sigma_iff]
  intro n
  apply measurable_from_prod_countable_right
  intro states
  unfold finiteStateMarkovJumpLogAction finiteStateMarkovJumpSliceLogAction
  fun_prop

/-- On a history supported by both densities, the global log-density ratio is the complete
sector action. -/
theorem log_finiteStateMarkovJumpDensity_div
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State)
    (hPositive : FiniteStateMarkovJumpDensityPositiveAt initial generator history)
    (hReferencePositive :
      FiniteStateMarkovJumpDensityPositiveAt referenceInitial referenceGenerator history) :
    Real.log
        (finiteStateMarkovJumpDensity initial generator T history /
          finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history) =
      finiteStateMarkovJumpLogAction initial referenceInitial generator
        referenceGenerator T history := by
  rcases history with ⟨n, states, times⟩
  exact log_finiteStateMarkovJumpSliceDensity_div initial referenceInitial generator
    referenceGenerator T states times hPositive.1 hReferencePositive.1
      hPositive.2 hReferencePositive.2

/-- On common positive support, the global density ratio is the exponential of the complete
sector action. -/
theorem finiteStateMarkovJumpDensity_div_eq_exp_logAction
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State)
    (hPositive : FiniteStateMarkovJumpDensityPositiveAt initial generator history)
    (hReferencePositive :
      FiniteStateMarkovJumpDensityPositiveAt referenceInitial referenceGenerator history) :
    finiteStateMarkovJumpDensity initial generator T history /
        finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history =
      Real.exp (finiteStateMarkovJumpLogAction initial referenceInitial generator
        referenceGenerator T history) := by
  rcases history with ⟨n, states, times⟩
  exact finiteStateMarkovJumpSliceDensity_div_eq_exp_logAction
    initial referenceInitial generator referenceGenerator T states times
      hPositive.1 hReferencePositive.1 hPositive.2 hReferencePositive.2

end FiniteMarkovProcesses.InformationTheory
