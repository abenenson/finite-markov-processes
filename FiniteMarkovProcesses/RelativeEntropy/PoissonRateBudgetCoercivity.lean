/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.PoissonRateHellinger

/-!
# Square-root coercivity for Poisson rate budgets

On the unit entropy-budget interval, the existing Poisson residual modulus is bounded by an
explicit multiple of the square root of the budget. A positive radius supplies a positive
unit-bounded quadratic budget with a strict factor-two margin.

## Main results

* `sqrt_poissonRateBudgetRadicand_le_mul_sqrt` bounds the square-root term.
* `poissonRateBudgetModulus_le_mul_sqrt` bounds the complete residual modulus.
* `poissonRateRadiusBudget_pos` and `poissonRateRadiusBudget_le_one` give the budget domain.
* `mul_sqrt_poissonRateRadiusBudget_le` gives the prescribed radius margin.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

noncomputable section

/-- On a unit entropy budget, the Poisson radicand has a square-root bound linear in the
nonnegative reference budget. -/
theorem sqrt_poissonRateBudgetRadicand_le_mul_sqrt
    {epsilon budget : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1)
    (hBudget : 0 ≤ budget) :
    Real.sqrt (epsilon ^ 2 + 4 * budget * epsilon) ≤
      (1 + 2 * budget) * Real.sqrt epsilon := by
  apply (Real.sqrt_le_left (mul_nonneg (by positivity) (Real.sqrt_nonneg epsilon))).2
  rw [mul_pow, Real.sq_sqrt hEpsilon]
  calc
    epsilon ^ 2 + 4 * budget * epsilon ≤ (1 + 4 * budget) * epsilon := by nlinarith
    _ ≤ (1 + 2 * budget) ^ 2 * epsilon := by
      apply mul_le_mul_of_nonneg_right _ hEpsilon
      nlinarith [sq_nonneg budget]

/-- The original Poisson residual modulus is at most a fixed multiple of the square root of
any entropy budget between zero and one. -/
theorem poissonRateBudgetModulus_le_mul_sqrt
    {epsilon budget : ℝ} (hEpsilon : 0 ≤ epsilon) (hEpsilonOne : epsilon ≤ 1)
    (hBudget : 0 ≤ budget) :
    poissonRateBudgetModulus epsilon budget ≤
      2 * (1 + budget) * Real.sqrt epsilon := by
  have hEpsilonSqrt : epsilon ≤ Real.sqrt epsilon := by
    calc
      epsilon = Real.sqrt (epsilon ^ 2) := (Real.sqrt_sq hEpsilon).symm
      _ ≤ Real.sqrt epsilon := Real.sqrt_le_sqrt (by nlinarith)
  have hRadicand := sqrt_poissonRateBudgetRadicand_le_mul_sqrt
    hEpsilon hEpsilonOne hBudget
  unfold poissonRateBudgetModulus
  nlinarith

/-- Positive radii are converted into unit-bounded quadratic rate budgets. -/
def poissonRateRadiusBudget (constant radius : ℝ) : ℝ :=
  min 1 ((radius / (2 * constant)) ^ 2)

/-- The quadratic radius budget is nonnegative for every real constant and radius. -/
theorem poissonRateRadiusBudget_nonneg (constant radius : ℝ) :
    0 ≤ poissonRateRadiusBudget constant radius := by
  unfold poissonRateRadiusBudget
  exact le_min (by norm_num) (sq_nonneg _)

/-- A positive constant and radius give a strictly positive quadratic rate budget. -/
theorem poissonRateRadiusBudget_pos {constant radius : ℝ}
    (hConstant : 0 < constant) (hRadius : 0 < radius) :
    0 < poissonRateRadiusBudget constant radius := by
  unfold poissonRateRadiusBudget
  exact lt_min_iff.mpr ⟨by norm_num,
    sq_pos_of_pos (div_pos hRadius (mul_pos (by norm_num) hConstant))⟩

/-- The quadratic radius budget is always at most one. -/
theorem poissonRateRadiusBudget_le_one (constant radius : ℝ) :
    poissonRateRadiusBudget constant radius ≤ 1 := by
  unfold poissonRateRadiusBudget
  exact min_le_left _ _

/-- The radius budget makes the constant times its square root at most half the radius. -/
theorem mul_sqrt_poissonRateRadiusBudget_le {constant radius : ℝ}
    (hConstant : 0 < constant) (hRadius : 0 < radius) : constant *
      Real.sqrt (poissonRateRadiusBudget constant radius) ≤ radius / 2 := by
  have hRatio : 0 ≤ radius / (2 * constant) :=
    (div_pos hRadius (mul_pos (by norm_num) hConstant)).le
  have hBudget : poissonRateRadiusBudget constant radius ≤
      (radius / (2 * constant)) ^ 2 := by
    exact min_le_right _ _
  have hSqrt : Real.sqrt (poissonRateRadiusBudget constant radius) ≤
      radius / (2 * constant) := by
    calc
      _ ≤ Real.sqrt ((radius / (2 * constant)) ^ 2) :=
        Real.sqrt_le_sqrt hBudget
      _ = radius / (2 * constant) := Real.sqrt_sq hRatio
  calc
    _ ≤ constant * (radius / (2 * constant)) :=
      mul_le_mul_of_nonneg_left hSqrt hConstant.le
    _ = radius / 2 := by field_simp [hConstant.ne']

end

end FiniteMarkovProcesses.InformationTheory
