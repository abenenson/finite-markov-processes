/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerExtendedPoissonDuality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hellinger control by extended Poisson rate cost

The classical scalar Hellinger estimate controls intensity errors by Poisson relative entropy.
The extended version retains infinite cost for positive flow against zero reference intensity.
A finite normalized-vector consequence supplies a conservative initial-law estimate.

## Main results

* `ofReal_sq_sub_sqrt_le_rengerExtendedPoissonRateCost` is the extended Hellinger bound.
* `sq_sub_le_two_mul_add_mul_rengerExtendedPoissonRateCost_toReal` controls real intensity error.
* `sum_abs_sub_le_two_mul_sqrt_of_rengerExtendedPoissonRateCost_le` controls normalized vectors.
* `le_poissonRateBudgetModulus_of_sq_le` solves the scalar residual budget inequality.
-/

namespace FiniteMarkovProcesses.InformationTheory

open scoped ENNReal BigOperators Topology

noncomputable section

/-- The classical Hellinger lower bound for finite Poisson discrimination. -/
theorem sq_sub_sqrt_le_poissonRateDiscrimination
    {flow expected : ℝ} (hFlow : 0 ≤ flow) (hExpected : 0 < expected) :
    (Real.sqrt flow - Real.sqrt expected) ^ 2 ≤
      poissonRateDiscrimination flow expected := by
  by_cases hFlowZero : flow = 0
  · subst flow
    simp only [Real.sqrt_zero, zero_sub, neg_sq, Real.sq_sqrt hExpected.le,
      poissonRateDiscrimination, zero_div, Real.log_zero, zero_mul, sub_zero, zero_add]
    rfl
  have hFlowPositive : 0 < flow := lt_of_le_of_ne hFlow (Ne.symm hFlowZero)
  have hSqrtFlowPositive := Real.sqrt_pos.2 hFlowPositive
  have hSqrtExpectedPositive := Real.sqrt_pos.2 hExpected
  have hLog : Real.log (flow / expected) =
      2 * Real.log (Real.sqrt flow / Real.sqrt expected) := by
    rw [Real.log_div hFlowPositive.ne' hExpected.ne',
      Real.log_div hSqrtFlowPositive.ne' hSqrtExpectedPositive.ne',
      Real.log_sqrt hFlow, Real.log_sqrt hExpected.le]
    ring
  have hSqrtFlow := Real.sq_sqrt hFlow
  have hSqrtExpected := Real.sq_sqrt hExpected.le
  have hWeightedSquare := congrArg
    (fun value : ℝ => value * (2 * Real.log (Real.sqrt flow / Real.sqrt expected) - 1))
    hSqrtFlow
  have hIdentity : poissonRateDiscrimination flow expected -
      (Real.sqrt flow - Real.sqrt expected) ^ 2 =
      2 * Real.sqrt flow *
        poissonRateDiscrimination (Real.sqrt flow) (Real.sqrt expected) := by
    unfold poissonRateDiscrimination
    rw [hLog]
    nlinarith only [hWeightedSquare, hSqrtExpected]
  have hNonnegative := mul_nonneg (by positivity : 0 ≤ 2 * Real.sqrt flow)
    (poissonRateDiscrimination_nonneg hSqrtFlowPositive.le hSqrtExpectedPositive)
  linarith

/-- Extended Poisson cost dominates squared Hellinger distance in every zero-rate sector. -/
theorem ofReal_sq_sub_sqrt_le_rengerExtendedPoissonRateCost
    (flow expected : NNReal) :
    ENNReal.ofReal ((Real.sqrt (flow : ℝ) - Real.sqrt (expected : ℝ)) ^ 2) ≤
      rengerExtendedPoissonRateCost flow expected := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · simp [rengerExtendedPoissonRateCost, hFlow]
  rw [rengerExtendedPoissonRateCost_of_expected_pos flow (pos_iff_ne_zero.mpr hExpected)]
  exact ENNReal.ofReal_le_ofReal (sq_sub_sqrt_le_poissonRateDiscrimination
    (by positivity) (by exact_mod_cast (pos_iff_ne_zero.mpr hExpected)))

/-- Squared intensity difference factors through squared Hellinger distance. -/
private theorem sq_sub_eq_sq_sub_sqrt_mul_sq_add_sqrt
    {flow expected : ℝ} (hFlow : 0 ≤ flow) (hExpected : 0 ≤ expected) :
    (flow - expected) ^ 2 =
      (Real.sqrt flow - Real.sqrt expected) ^ 2 *
        (Real.sqrt flow + Real.sqrt expected) ^ 2 := by
  calc
    (flow - expected) ^ 2 = (Real.sqrt flow ^ 2 - Real.sqrt expected ^ 2) ^ 2 := by
      rw [Real.sq_sqrt hFlow, Real.sq_sqrt hExpected]
    _ = _ := by ring

/-- The squared sum of square roots is at most twice the sum of the intensities. -/
private theorem sq_add_sqrt_le_two_mul_add
    {flow expected : ℝ} (hFlow : 0 ≤ flow) (hExpected : 0 ≤ expected) :
    (Real.sqrt flow + Real.sqrt expected) ^ 2 ≤ 2 * (flow + expected) := by
  nlinarith [Real.sq_sqrt hFlow, Real.sq_sqrt hExpected,
    sq_nonneg (Real.sqrt flow - Real.sqrt expected)]

/-- Extended Poisson cost controls squared intensity error, including singular zero references. -/
theorem ofReal_sq_sub_le_two_mul_add_mul_rengerExtendedPoissonRateCost
    (flow expected : NNReal) :
    ENNReal.ofReal (((flow : ℝ) - (expected : ℝ)) ^ 2) ≤
      ENNReal.ofReal (2 * ((flow : ℝ) + (expected : ℝ))) *
        rengerExtendedPoissonRateCost flow expected := by
  have hFlow : 0 ≤ (flow : ℝ) := flow.coe_nonneg
  have hExpected : 0 ≤ (expected : ℝ) := expected.coe_nonneg
  calc
    _ = ENNReal.ofReal ((Real.sqrt (flow : ℝ) + Real.sqrt (expected : ℝ)) ^ 2) *
        ENNReal.ofReal ((Real.sqrt (flow : ℝ) - Real.sqrt (expected : ℝ)) ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _),
        sq_sub_eq_sq_sub_sqrt_mul_sq_add_sqrt hFlow hExpected, mul_comm]
    _ ≤ _ := mul_le_mul
      (ENNReal.ofReal_le_ofReal (sq_add_sqrt_le_two_mul_add hFlow hExpected))
      (ofReal_sq_sub_sqrt_le_rengerExtendedPoissonRateCost flow expected) (by positivity)
      (by positivity)

/-- Finite extended Poisson cost controls the ordinary squared intensity error. -/
theorem sq_sub_le_two_mul_add_mul_rengerExtendedPoissonRateCost_toReal
    (flow expected : NNReal) (hCost : rengerExtendedPoissonRateCost flow expected ≠ ⊤) :
    ((flow : ℝ) - (expected : ℝ)) ^ 2 ≤
      2 * ((flow : ℝ) + (expected : ℝ)) *
        (rengerExtendedPoissonRateCost flow expected).toReal := by
  have hBound := ofReal_sq_sub_le_two_mul_add_mul_rengerExtendedPoissonRateCost flow expected
  have hFinite : ENNReal.ofReal (2 * ((flow : ℝ) + (expected : ℝ))) *
      rengerExtendedPoissonRateCost flow expected ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCost
  have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hFinite).2 hBound
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((flow : ℝ) + (expected : ℝ)))]
    using hReal

/-- An entropy budget controls the L1 distance between two finite normalized intensity vectors.
This conservative estimate uses Hellinger control and does not assert a sharp Pinsker constant. -/
theorem sum_abs_sub_le_two_mul_sqrt_of_rengerExtendedPoissonRateCost_le
    {ι : Type*} [Fintype ι] (flow expected : ι → NNReal) {epsilon : ℝ}
    (hFlowMass : ∑ i, (flow i : ℝ) = 1)
    (hExpectedMass : ∑ i, (expected i : ℝ) = 1) (hEpsilon : 0 ≤ epsilon)
    (hCost : ∑ i, rengerExtendedPoissonRateCost (flow i) (expected i) ≤
      ENNReal.ofReal epsilon) :
    ∑ i, |(flow i : ℝ) - (expected i : ℝ)| ≤ 2 * Real.sqrt epsilon := by
  classical
  let hellinger (i : ι) : ℝ :=
    (Real.sqrt (flow i : ℝ) - Real.sqrt (expected i : ℝ)) ^ 2
  have hHellingerNonnegative (i : ι) : 0 ≤ hellinger i := sq_nonneg _
  have hHellingerExtended : ENNReal.ofReal (∑ i, hellinger i) ≤
      ENNReal.ofReal epsilon := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hHellingerNonnegative i)]
    exact (Finset.sum_le_sum (fun i _ =>
      ofReal_sq_sub_sqrt_le_rengerExtendedPoissonRateCost (flow i) (expected i))).trans hCost
  have hHellinger : ∑ i, hellinger i ≤ epsilon :=
    (ENNReal.ofReal_le_ofReal_iff hEpsilon).1 hHellingerExtended
  have hCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => |(flow i : ℝ) - (expected i : ℝ)|)
    (f := fun i => 2 * ((flow i : ℝ) + (expected i : ℝ)))
    (g := hellinger)
    (fun i _ => by positivity) (fun i _ => hHellingerNonnegative i)
    (fun i _ => by
      rw [sq_abs,
        sq_sub_eq_sq_sub_sqrt_mul_sq_add_sqrt (flow i).coe_nonneg (expected i).coe_nonneg]
      exact (mul_le_mul_of_nonneg_left
        (sq_add_sqrt_le_two_mul_add (flow i).coe_nonneg (expected i).coe_nonneg)
        (hHellingerNonnegative i)).trans_eq (mul_comm _ _))
  have hMass : ∑ i, 2 * ((flow i : ℝ) + (expected i : ℝ)) = 4 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hFlowMass, hExpectedMass]
    norm_num
  rw [hMass] at hCauchy
  have hRoot := Real.sq_sqrt hEpsilon
  have hRootNonnegative := Real.sqrt_nonneg epsilon
  have hDistanceNonnegative : 0 ≤ ∑ i, |(flow i : ℝ) - (expected i : ℝ)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

/-- Explicit residual modulus from an entropy budget and an integrated reference budget. -/
def poissonRateBudgetModulus (epsilon budget : ℝ) : ℝ :=
  epsilon + Real.sqrt (epsilon ^ 2 + 4 * budget * epsilon)

/-- The residual modulus is nonnegative for a nonnegative entropy budget. -/
theorem poissonRateBudgetModulus_nonneg {epsilon budget : ℝ} (hEpsilon : 0 ≤ epsilon) :
    0 ≤ poissonRateBudgetModulus epsilon budget := by
  exact add_nonneg hEpsilon (Real.sqrt_nonneg _)

/-- Zero entropy budget gives zero residual modulus for every reference budget. -/
@[simp]
theorem poissonRateBudgetModulus_zero (budget : ℝ) :
    poissonRateBudgetModulus 0 budget = 0 := by
  simp [poissonRateBudgetModulus]

/-- The residual modulus is monotone in both nonnegative budgets. -/
theorem poissonRateBudgetModulus_mono {epsilon epsilon' budget budget' : ℝ}
    (hEpsilon : 0 ≤ epsilon) (hBudget : 0 ≤ budget)
    (hEpsilonLe : epsilon ≤ epsilon') (hBudgetLe : budget ≤ budget') :
    poissonRateBudgetModulus epsilon budget ≤ poissonRateBudgetModulus epsilon' budget' := by
  unfold poissonRateBudgetModulus
  apply add_le_add hEpsilonLe
  apply Real.sqrt_le_sqrt
  have hProduct : budget * epsilon ≤ budget' * epsilon' :=
    mul_le_mul hBudgetLe hEpsilonLe hEpsilon (hBudget.trans hBudgetLe)
  nlinarith

/-- The residual modulus depends continuously on both real budget coordinates. -/
theorem continuous_poissonRateBudgetModulus :
    Continuous fun budgets : ℝ × ℝ => poissonRateBudgetModulus budgets.1 budgets.2 := by
  unfold poissonRateBudgetModulus
  fun_prop

/-- The residual modulus tends to zero as the entropy budget tends to zero. -/
theorem tendsto_poissonRateBudgetModulus_zero (budget : ℝ) :
    Filter.Tendsto (fun epsilon : ℝ => poissonRateBudgetModulus epsilon budget)
      (nhds 0) (nhds 0) := by
  have hContinuous : Continuous fun epsilon : ℝ => poissonRateBudgetModulus epsilon budget :=
    continuous_poissonRateBudgetModulus.comp (continuous_id.prodMk continuous_const)
  simpa only [poissonRateBudgetModulus_zero] using hContinuous.continuousAt.tendsto (x := 0)

/-- Solving the residual quadratic gives the explicit entropy-budget modulus. -/
theorem le_poissonRateBudgetModulus_of_sq_le {error epsilon budget : ℝ}
    (hEpsilon : 0 ≤ epsilon) (hBudget : 0 ≤ budget)
    (hSquare : error ^ 2 ≤ 2 * epsilon * (error + 2 * budget)) :
    error ≤ poissonRateBudgetModulus epsilon budget := by
  have hRadicand : 0 ≤ epsilon ^ 2 + 4 * budget * epsilon := by positivity
  have hRoot := Real.sq_sqrt hRadicand
  have hRootNonnegative := Real.sqrt_nonneg (epsilon ^ 2 + 4 * budget * epsilon)
  unfold poissonRateBudgetModulus
  nlinarith

end

end FiniteMarkovProcesses.InformationTheory
