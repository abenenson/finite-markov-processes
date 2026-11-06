/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mode of a finite multinomial law at its empirical parameter

This module proves the exact finite combinatorial inequality behind the method-of-types lower
bound.  If a nonzero integer count vector is normalized to a probability vector, then the
original count vector maximizes the resulting multinomial mass among all count vectors with the
same total.

The proof separates the multinomial mass into a common total-count factor and coordinate factors
`c ^ d / d!`.  Each coordinate factor is maximized at `d = c`; hence no multivariate exchange
argument or asymptotic factorial estimate is needed.

## Main declarations

- `factorialNormalizedNaturalPower`: the coordinate factor `c ^ d / d!`.
- `factorialNormalizedNaturalPower_le_self`: its maximum occurs at `d = c`.
- `multinomialEmpiricalProbabilityReal_eq_factorialNormalizedNaturalPower`: exact factorization.
- `multinomialEmpiricalProbabilityReal_le_self`: the empirical count vector is a mode.
-/

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators

universe u

noncomputable section

/-- The real coordinate factor `count ^ observation / observation!` occurring in a multinomial
mass after removal of the total-count normalization. -/
def factorialNormalizedNaturalPower (count observation : ℕ) : ℝ :=
  (count : ℝ) ^ observation / (observation.factorial : ℝ)

/-- The factorial-normalized natural power is nonnegative. -/
theorem factorialNormalizedNaturalPower_nonneg (count observation : ℕ) :
    0 ≤ factorialNormalizedNaturalPower count observation := by
  exact div_nonneg (pow_nonneg (Nat.cast_nonneg count) observation)
    (Nat.cast_nonneg observation.factorial)

/-- Below a positive count, increasing the observation by one does not decrease its
factorial-normalized power. -/
theorem factorialNormalizedNaturalPower_le_succ (count observation : ℕ)
    (hCount : 0 < count) (hObservation : observation + 1 ≤ count) :
    factorialNormalizedNaturalPower count observation ≤
      factorialNormalizedNaturalPower count (observation + 1) := by
  unfold factorialNormalizedNaturalPower
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < observation.factorial)
    (by positivity : (0 : ℝ) < (observation + 1) * observation.factorial)]
  have hObservationReal : (observation + 1 : ℝ) ≤ count := by
    exact_mod_cast hObservation
  calc
    (count : ℝ) ^ observation * ((observation + 1) * observation.factorial) =
        ((count : ℝ) ^ observation * observation.factorial) * (observation + 1) := by
          ring
    _ ≤ ((count : ℝ) ^ observation * observation.factorial) * count :=
      mul_le_mul_of_nonneg_left hObservationReal (by positivity)
    _ = (count : ℝ) ^ observation * count * observation.factorial := by ring

/-- At or above a positive count, increasing the observation by one does not increase its
factorial-normalized power. -/
theorem factorialNormalizedNaturalPower_succ_le (count observation : ℕ)
    (hCount : 0 < count) (hObservation : count ≤ observation + 1) :
    factorialNormalizedNaturalPower count (observation + 1) ≤
      factorialNormalizedNaturalPower count observation := by
  unfold factorialNormalizedNaturalPower
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [div_le_div_iff₀
    (by positivity : (0 : ℝ) < (observation + 1) * observation.factorial)
    (by positivity : (0 : ℝ) < observation.factorial)]
  have hObservationReal : (count : ℝ) ≤ observation + 1 := by
    exact_mod_cast hObservation
  calc
    (count : ℝ) ^ observation * count * observation.factorial =
        ((count : ℝ) ^ observation * observation.factorial) * count := by ring
    _ ≤ ((count : ℝ) ^ observation * observation.factorial) * (observation + 1) :=
      mul_le_mul_of_nonneg_left hObservationReal (by positivity)
    _ = (count : ℝ) ^ observation * ((observation + 1) * observation.factorial) := by ring

/-- For every natural count, its factorial-normalized power is maximized when the observation
equals the count.  When the count is zero, all positive observations have zero weight. -/
theorem factorialNormalizedNaturalPower_le_self (count observation : ℕ) :
    factorialNormalizedNaturalPower count observation ≤
      factorialNormalizedNaturalPower count count := by
  by_cases hCountZero : count = 0
  · subst count
    cases observation <;> simp [factorialNormalizedNaturalPower]
  have hCount : 0 < count := Nat.pos_of_ne_zero hCountZero
  rcases le_total observation count with hObservationCount | hCountObservation
  · exact Nat.decreasingInduction (n := count)
      (motive := fun candidate _ =>
        factorialNormalizedNaturalPower count candidate ≤
          factorialNormalizedNaturalPower count count)
      (fun candidate hCandidate inductionHypothesis =>
        (factorialNormalizedNaturalPower_le_succ count candidate hCount
          (Nat.succ_le_iff.mpr hCandidate)).trans inductionHypothesis)
      le_rfl hObservationCount
  · exact Nat.le_induction (m := count)
      (P := fun candidate _ =>
        factorialNormalizedNaturalPower count candidate ≤
          factorialNormalizedNaturalPower count count)
      le_rfl
      (fun candidate hCountCandidate inductionHypothesis =>
        (factorialNormalizedNaturalPower_succ_le count candidate hCount
          (hCountCandidate.trans (Nat.le_succ candidate))).trans inductionHypothesis)
      observation hCountObservation

variable {Alphabet : Type u} [Fintype Alphabet]

/-- Exact factorization of a multinomial empirical probability into its common total-count
factor and coordinatewise factorial-normalized natural powers. -/
theorem multinomialEmpiricalProbabilityReal_eq_factorialNormalizedNaturalPower
    (total : ℕ) (hTotal : 0 < total) (empiricalCounts candidateCounts : Alphabet → ℕ)
    (hCandidateTotal : ∑ symbol, candidateCounts symbol = total) :
    (Nat.multinomial Finset.univ candidateCounts : ℝ) *
        ∏ symbol,
          ((empiricalCounts symbol : ℝ) / (total : ℝ)) ^ candidateCounts symbol =
      ((total.factorial : ℝ) / (total : ℝ) ^ total) *
        ∏ symbol,
          factorialNormalizedNaturalPower (empiricalCounts symbol) (candidateCounts symbol) := by
  have hMultinomialNatural :=
    Nat.multinomial_spec (Finset.univ : Finset Alphabet) candidateCounts
  have hMultinomialReal :
      (∏ symbol, ((candidateCounts symbol).factorial : ℝ)) *
          (Nat.multinomial Finset.univ candidateCounts : ℝ) =
        (total.factorial : ℝ) := by
    exact_mod_cast hMultinomialNatural.trans
      (congrArg Nat.factorial hCandidateTotal)
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum Finset.univ candidateCounts (total : ℝ),
    hCandidateTotal]
  simp_rw [factorialNormalizedNaturalPower]
  rw [Finset.prod_div_distrib]
  have hTotalReal : (total : ℝ) ≠ 0 := by positivity
  have hFactorialProduct :
      (∏ symbol, ((candidateCounts symbol).factorial : ℝ)) ≠ 0 := by
    positivity
  field_simp
  calc
    ((Nat.multinomial Finset.univ candidateCounts : ℝ) *
          ∏ symbol, (empiricalCounts symbol : ℝ) ^ candidateCounts symbol) *
        ∏ symbol, ((candidateCounts symbol).factorial : ℝ) =
      (∏ symbol, (empiricalCounts symbol : ℝ) ^ candidateCounts symbol) *
        ((∏ symbol, ((candidateCounts symbol).factorial : ℝ)) *
          (Nat.multinomial Finset.univ candidateCounts : ℝ)) := by
            ring
    _ = (∏ symbol, (empiricalCounts symbol : ℝ) ^ candidateCounts symbol) *
        (total.factorial : ℝ) := by
      rw [hMultinomialReal]

/-- If integer empirical counts are normalized to a probability vector, their own multinomial
probability is at least that of every other count vector with the same total. -/
theorem multinomialEmpiricalProbabilityReal_le_self
    (total : ℕ) (hTotal : 0 < total) (empiricalCounts candidateCounts : Alphabet → ℕ)
    (hEmpiricalTotal : ∑ symbol, empiricalCounts symbol = total)
    (hCandidateTotal : ∑ symbol, candidateCounts symbol = total) :
    (Nat.multinomial Finset.univ candidateCounts : ℝ) *
        ∏ symbol,
          ((empiricalCounts symbol : ℝ) / (total : ℝ)) ^ candidateCounts symbol ≤
      (Nat.multinomial Finset.univ empiricalCounts : ℝ) *
        ∏ symbol,
          ((empiricalCounts symbol : ℝ) / (total : ℝ)) ^ empiricalCounts symbol := by
  rw [multinomialEmpiricalProbabilityReal_eq_factorialNormalizedNaturalPower
      total hTotal empiricalCounts candidateCounts hCandidateTotal,
    multinomialEmpiricalProbabilityReal_eq_factorialNormalizedNaturalPower
      total hTotal empiricalCounts empiricalCounts hEmpiricalTotal]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.prod_le_prod₀
    (fun symbol _ =>
      factorialNormalizedNaturalPower_nonneg
        (empiricalCounts symbol) (candidateCounts symbol))
    (fun symbol _ =>
      factorialNormalizedNaturalPower_le_self
        (empiricalCounts symbol) (candidateCounts symbol))

end

end FiniteMarkovProcesses.Probability
