/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateProbabilityDensityRelativeEntropy
import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalTypeLaw

/-!
# Exponential bounds for positive finite IID empirical types

This module proves the exact likelihood-ratio identity and the two finite exponential estimates
used in a finite-alphabet method-of-types proof.  For an interior reference density `q` and a
positive sample of size `N`, the probability of an exact type `p` is bounded above by
`exp (-N D(p || q))` and below by the same exponential divided by the polynomial type-count
bound.

No asymptotic limit, open-set bound, or closed-set bound is asserted here.

## Main declarations

- `finiteIIDPositiveEmpiricalType_referenceProduct_eq_entropyTilt_ownProduct`.
- `finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_eq_entropyTilt_own`.
- `finiteIIDPositiveEmpiricalTypeProbability_upperBound`.
- `finiteIIDPositiveEmpiricalTypeProbability_lowerBound`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State]

/-- Exact coordinate-product likelihood-ratio identity for an empirical type.  Zero empirical
coordinates are handled by their zero counts; the reference is required to be strictly positive. -/
theorem finiteIIDPositiveEmpiricalType_referenceProduct_eq_entropyTilt_ownProduct
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    Real.exp (-(successorIndex + 1 : ℝ) *
        finiteStateProbabilityDensityRelativeEntropyReal reference
          empiricalType.probabilityDensity) *
        ∏ state, (empiricalType.probabilityDensity.weight state : ℝ) ^
          (empiricalType.count state : ℕ) =
      ∏ state, (reference.weight state : ℝ) ^
        (empiricalType.count state : ℕ) := by
  rw [finiteStateProbabilityDensityRelativeEntropyReal_eq_sum_mul_log]
  have hNormalized (state : State) :
      (empiricalType.probabilityDensity.weight state : ℝ) =
        ((empiricalType.count state : ℕ) : ℝ) /
          (successorIndex + 1 : ℝ) := by
    rw [FiniteIIDPositiveEmpiricalType.probabilityDensity_weight]
    simp only [NNReal.coe_div, NNReal.coe_natCast]
    norm_cast
  have hScale :
      (successorIndex + 1 : ℝ) *
          ∑ state, (empiricalType.probabilityDensity.weight state : ℝ) *
            Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
              (reference.weight state : ℝ)) =
        ∑ state, ((empiricalType.count state : ℕ) : ℝ) *
            Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
              (reference.weight state : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _hState
    rw [hNormalized state]
    field_simp
  rw [neg_mul, hScale]
  rw [show -(∑ state, ((empiricalType.count state : ℕ) : ℝ) *
      Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
        (reference.weight state : ℝ))) =
      ∑ state, -(((empiricalType.count state : ℕ) : ℝ) *
        Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
          (reference.weight state : ℝ))) by
        rw [Finset.sum_neg_distrib]]
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro state _hState
  by_cases hCount : (empiricalType.count state : ℕ) = 0
  · simp [hCount]
  have hCountPos : 0 < (empiricalType.count state : ℕ) :=
    Nat.pos_of_ne_zero hCount
  have hDensityPos :
      0 < (empiricalType.probabilityDensity.weight state : ℝ) := by
    rw [hNormalized state]
    positivity
  have hReferencePos : 0 < (reference.weight state : ℝ) := by
    exact_mod_cast hReference state
  rw [show -(((empiricalType.count state : ℕ) : ℝ) *
      Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
        (reference.weight state : ℝ))) =
      ((empiricalType.count state : ℕ) : ℝ) *
        (-Real.log ((empiricalType.probabilityDensity.weight state : ℝ) /
          (reference.weight state : ℝ))) by ring]
  rw [Real.exp_nat_mul, Real.exp_neg,
    Real.exp_log (div_pos hDensityPos hReferencePos), inv_div, ← mul_pow]
  field_simp

variable [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The exact type probability under an interior reference is its probability under the type's
own normalized law multiplied by the relative-entropy exponential tilt. -/
theorem finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_eq_entropyTilt_own
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    (finiteIIDPositiveEmpiricalTypeLaw successorIndex
      reference.probabilityMassFunction {empiricalType}).toReal =
      Real.exp (-(successorIndex + 1 : ℝ) *
        finiteStateProbabilityDensityRelativeEntropyReal reference
          empiricalType.probabilityDensity) *
      (finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {empiricalType}).toReal := by
  rw [finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_probabilityDensity,
    show empiricalType.probabilityMassFunction =
      empiricalType.probabilityDensity.probabilityMassFunction from rfl,
    finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_probabilityDensity]
  nlinarith [
    finiteIIDPositiveEmpiricalType_referenceProduct_eq_entropyTilt_ownProduct
      reference hReference successorIndex empiricalType]

/-- Exact-type upper bound by the relative-entropy exponential. -/
theorem finiteIIDPositiveEmpiricalTypeProbability_upperBound
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    finiteIIDPositiveEmpiricalTypeLaw successorIndex
        reference.probabilityMassFunction {empiricalType} ≤
      ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) *
        finiteStateProbabilityDensityRelativeEntropyReal reference
          empiricalType.probabilityDensity)) := by
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_eq_entropyTilt_own
      reference hReference successorIndex empiricalType,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact mul_le_of_le_one_right (Real.exp_pos _).le measureReal_le_one

/-- Exact-type lower bound by the relative-entropy exponential divided by the polynomial number
of finite empirical types. -/
theorem finiteIIDPositiveEmpiricalTypeProbability_lowerBound
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) *
          finiteStateProbabilityDensityRelativeEntropyReal reference
            empiricalType.probabilityDensity) /
          (((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) ≤
      finiteIIDPositiveEmpiricalTypeLaw successorIndex
        reference.probabilityMassFunction {empiricalType} := by
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le (by positivity)),
    finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_eq_entropyTilt_own
      reference hReference successorIndex empiricalType]
  have hOwnReal :
      ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal)⁻¹).toReal ≤
        (finiteIIDPositiveEmpiricalTypeLaw successorIndex
          empiricalType.probabilityMassFunction {empiricalType}).toReal :=
    (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _)).mpr
      (finiteIIDPositiveEmpiricalType_ownProbability_ge_polynomial_inv
        successorIndex empiricalType)
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at hOwnReal
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hOwnReal (Real.exp_pos _).le

end

end FiniteMarkovProcesses.Probability
