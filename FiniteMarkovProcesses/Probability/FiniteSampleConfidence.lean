/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Data.Rat.Floor
import Mathlib.Basic.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Executable particle counts from finite-sample envelopes

Rational ceilings turn polynomial and exponential probability envelopes into sufficient
positive sample counts. These are arithmetic consequences of an independently proved envelope;
the algorithms do not establish an envelope or estimate its constants from data.

## Main results

* `le_of_polynomialParticleBudget`: polynomial-envelope confidence at an executable count.
* `le_dyadic_of_exponentialParticleBudget`: exponential-envelope dyadic confidence.
* `two_mul_exp_neg_le_exp_neg_of_margin`: an explicit margin removes the prefactor two.

The exponential rate retains both its quadratic and linear branches. The sufficient dyadic
count uses `2 ≤ exp 1`, avoiding a numerical approximation to a logarithm.
-/

namespace FiniteMarkovProcesses.Probability

/-- A sufficient positive count for an envelope `constant / (count * radius²)`.
The confidence theorems require positive radius and failure tolerance. -/
def polynomialParticleBudget (constant radius failure : ℚ) : ℕ :=
  max 1 ⌈constant / (failure * radius ^ 2)⌉₊

/-- The polynomial algorithm always returns a positive count, even for invalid inputs. -/
theorem polynomialParticleBudget_pos (constant radius failure : ℚ) :
    0 < polynomialParticleBudget constant radius failure :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- Counts above the rational ceiling satisfy the real polynomial confidence criterion. -/
theorem polynomialParticleBudget_criterion
    {constant radius failure : ℚ} (hRadius : 0 < radius) (hFailure : 0 < failure)
    {count : ℕ} (hCount : polynomialParticleBudget constant radius failure ≤ count) :
    (constant : ℝ) ≤ (count : ℝ) * (radius : ℝ) ^ 2 * (failure : ℝ) := by
  have hCeil : constant / (failure * radius ^ 2) ≤ (count : ℚ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1 ⌈constant / (failure * radius ^ 2)⌉₊).trans hCount
  have hCriterion :=
    (div_le_iff₀ (mul_pos hFailure (sq_pos_of_pos hRadius))).mp hCeil
  have hReal : (constant : ℝ) ≤
      (count : ℝ) * ((failure : ℝ) * (radius : ℝ) ^ 2) := by
    exact_mod_cast hCriterion
  nlinarith

/-- An independently proved polynomial event-mass envelope gives the requested confidence.
Here `count` is the actual positive number of samples, rather than a successor index. -/
theorem le_of_polynomialParticleBudget
    {mass : ENNReal} {constant radius failure : ℚ}
    (hRadius : 0 < radius) (hFailure : 0 < failure) {count : ℕ}
    (hCount : polynomialParticleBudget constant radius failure ≤ count)
    (hEnvelope : mass ≤ ENNReal.ofReal
      ((constant : ℝ) / ((count : ℝ) * (radius : ℝ) ^ 2))) :
    mass ≤ ENNReal.ofReal (failure : ℝ) := by
  have hPositive : 0 < count :=
    lt_of_lt_of_le (polynomialParticleBudget_pos constant radius failure) hCount
  have hDenominator : 0 < (count : ℝ) * (radius : ℝ) ^ 2 := by
    exact mul_pos (by exact_mod_cast hPositive) (sq_pos_of_pos (by exact_mod_cast hRadius))
  refine hEnvelope.trans (ENNReal.ofReal_le_ofReal ((div_le_iff₀ hDenominator).mpr ?_))
  nlinarith [polynomialParticleBudget_criterion hRadius hFailure hCount]

/-- Rational quadratic/linear rate for a positive scale and deviation radius. -/
def exponentialRateRat (scale radius : ℚ) : ℚ :=
  min (radius ^ 2 / (4 * scale ^ 2)) (radius / (8 * scale))

/-- Both branches of the rational rate are positive for positive inputs. -/
theorem exponentialRateRat_pos {scale radius : ℚ}
    (hScale : 0 < scale) (hRadius : 0 < radius) :
    0 < exponentialRateRat scale radius := by
  unfold exponentialRateRat
  positivity

/-- A sufficient positive count for dyadic confidence under `2 * exp (-count * rate)`.
Only the rational rate is evaluated; no real-valued ceiling is used. -/
def exponentialParticleBudget (scale radius : ℚ) (confidenceBits : ℕ) : ℕ :=
  max 1 ⌈(confidenceBits + 1 : ℚ) / exponentialRateRat scale radius⌉₊

/-- The dyadic algorithm always returns a positive count. -/
theorem exponentialParticleBudget_pos (scale radius : ℚ) (confidenceBits : ℕ) :
    0 < exponentialParticleBudget scale radius confidenceBits :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- Counts above the dyadic budget satisfy the real rate-times-count criterion. -/
theorem exponentialParticleBudget_criterion
    {scale radius : ℚ} (hScale : 0 < scale) (hRadius : 0 < radius)
    (confidenceBits : ℕ) {count : ℕ}
    (hCount : exponentialParticleBudget scale radius confidenceBits ≤ count) :
    (confidenceBits + 1 : ℝ) ≤ (count : ℝ) * (exponentialRateRat scale radius : ℝ) := by
  have hCeil : (confidenceBits + 1 : ℚ) / exponentialRateRat scale radius ≤ (count : ℚ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1
      ⌈(confidenceBits + 1 : ℚ) / exponentialRateRat scale radius⌉₊).trans hCount
  have h := (div_le_iff₀ (exponentialRateRat_pos hScale hRadius)).mp hCeil
  exact_mod_cast h

/-- A real exponential envelope meets dyadic confidence once count times rate is large enough. -/
theorem two_mul_exp_neg_le_dyadic {rate : ℝ} (count confidenceBits : ℕ)
    (hCriterion : (confidenceBits + 1 : ℝ) ≤ (count : ℝ) * rate) :
    2 * Real.exp (-(count : ℝ) * rate) ≤ 1 / (2 : ℝ) ^ confidenceBits := by
  have hTwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hPower : (2 : ℝ) ^ (confidenceBits + 1) ≤ Real.exp (confidenceBits + 1 : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ (confidenceBits + 1) :=
        pow_le_pow_left₀ (by norm_num) hTwo _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_cast; simp
  have hDenom := hPower.trans (Real.exp_le_exp.mpr hCriterion)
  calc
    _ = 2 / Real.exp ((count : ℝ) * rate) := by
      rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
    _ ≤ 2 / (2 : ℝ) ^ (confidenceBits + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hDenom
    _ = _ := by rw [pow_succ]; field_simp

/-- An independently proved exponential event-mass envelope gives dyadic confidence at the
computed count. The supplied envelope must use the same scale, radius, and actual count. -/
theorem le_dyadic_of_exponentialParticleBudget
    {mass : ENNReal} {scale radius : ℚ} (hScale : 0 < scale) (hRadius : 0 < radius)
    (confidenceBits : ℕ) {count : ℕ}
    (hCount : exponentialParticleBudget scale radius confidenceBits ≤ count)
    (hEnvelope : mass ≤ ENNReal.ofReal
      (2 * Real.exp (-(count : ℝ) * (exponentialRateRat scale radius : ℝ)))) :
    mass ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ confidenceBits) :=
  hEnvelope.trans (ENNReal.ofReal_le_ofReal (two_mul_exp_neg_le_dyadic count confidenceBits
    (exponentialParticleBudget_criterion hScale hRadius confidenceBits hCount)))

/-- A sufficient arithmetic margin removes the factor two. In applications with positive
count, this requires the requested exponent to be strictly smaller than the envelope rate. -/
theorem two_mul_exp_neg_le_exp_neg_of_margin {count rate exponent : ℝ}
    (hMargin : 1 ≤ count * (rate - exponent)) :
    2 * Real.exp (-count * rate) ≤ Real.exp (-count * exponent) := by
  have hBase : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTwo : (2 : ℝ) ≤ Real.exp (count * (rate - exponent)) :=
    hBase.trans (Real.exp_le_exp.mpr hMargin)
  calc
    _ ≤ Real.exp (count * (rate - exponent)) * Real.exp (-count * rate) :=
      mul_le_mul_of_nonneg_right hTwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end FiniteMarkovProcesses.Probability
