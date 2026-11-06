/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.DensityFluxLargeDeviationRepresentation
import Mathlib.Data.EReal.Inv
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Exponential concentration from a large-deviation upper bound

A closed event separated from zero rate inherits an extended-log upper bound. Strict exponent
slack then gives an eventual bound on actual event mass, preserving zero mass as logarithmic
bottom. Altering any finite prefix of normalized laws shows why the conclusion is eventual.

## Main results

- `HasLargeDeviationUpperBound.limsup_le_neg_of_isClosed_of_le_rate`: a closed-event rate gap.
- `eventually_probability_le_exp_of_limsup_log_div_le`: eventual exponential mass control.
- `finitePrefixEventLaw_scaledLog_limsup_eq_bot`: an exact normalized finite-prefix control.
- `finitePrefixEventLaw_not_forall_le_exp`: the same laws refute an all-index bound.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped ENNReal

universe u

/-- A pointwise rate lower bound on a closed event yields the corresponding log-limsup bound. -/
theorem HasLargeDeviationUpperBound.limsup_le_neg_of_isClosed_of_le_rate
    {Path : Type u} [TopologicalSpace Path]
    {scaledLogProbability : ℕ → Set Path → EReal} {rate : Path → ENNReal}
    (hUpper : HasLargeDeviationUpperBound scaledLogProbability rate)
    {event : Set Path} (hClosed : IsClosed event) {level : ENNReal}
    (hGap : ∀ path ∈ event, level ≤ rate path) :
    limsup (fun index ↦ scaledLogProbability index event) atTop ≤ -(level : EReal) := by
  refine (hUpper event hClosed).trans ?_
  rw [EReal.neg_le_neg_iff]
  exact le_iInf fun path ↦ le_iInf fun hPath ↦ by exact_mod_cast hGap path hPath

/-- A strict loss in the exponent converts an extended-log limsup into an eventual actual-mass
bound. A positive exponent gives decay; zero mass requires no separate positivity assumption. -/
theorem eventually_probability_le_exp_of_limsup_log_div_le
    (probability : ℕ → ENNReal) (speed : ℕ → ℝ)
    (hProbability : ∀ index, probability index ≤ 1)
    (hSpeed : ∀ index, 0 < speed index) {rate exponent : ℝ}
    (hRate : limsup (fun index ↦ (probability index).log / (speed index : EReal)) atTop ≤
      -(rate : EReal)) (hExponent : exponent < rate) :
    ∀ᶠ index in atTop,
      probability index ≤ ENNReal.ofReal (Real.exp (-speed index * exponent)) := by
  have hBounded : atTop.IsBoundedUnder (· ≤ ·)
      (fun index ↦ (probability index).log / (speed index : EReal)) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ index : ℕ in atTop, (probability index).log / (speed index : EReal) ≤ 0
    exact Eventually.of_forall fun index ↦ EReal.div_nonpos_of_nonpos_of_nonneg
      (ENNReal.log_le_zero_iff.mpr (hProbability index))
      (EReal.coe_nonneg.mpr (hSpeed index).le)
  have hStrict : limsup (fun index ↦ (probability index).log / (speed index : EReal))
      atTop < -(exponent : EReal) := by
    refine hRate.trans_lt ?_
    rw [EReal.neg_lt_neg_iff]
    exact_mod_cast hExponent
  filter_upwards [eventually_lt_of_limsup_lt hStrict hBounded] with index hIndex
  apply le_of_lt
  apply ENNReal.log_lt_log_iff.mp
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hLog := (EReal.div_lt_iff (EReal.coe_pos.mpr (hSpeed index))
    (EReal.coe_ne_top _)).mp hIndex
  have hProduct : -(exponent : EReal) * (speed index : EReal) =
      ((-speed index * exponent : ℝ) : EReal) := by
    rw [← EReal.coe_neg, ← EReal.coe_mul]
    congr 1
    ring
  rwa [hProduct] at hLog

/-- Normalized Boolean laws whose fixed true event has mass one on an arbitrary finite prefix
and mass zero afterwards. -/
noncomputable def finitePrefixEventLaw (cutoff index : ℕ) : Measure Bool :=
  Measure.dirac (decide (index ≤ cutoff))

/-- Every member of the finite-prefix family is an actual probability law. -/
theorem finitePrefixEventLaw_isProbabilityMeasure (cutoff index : ℕ) :
    IsProbabilityMeasure (finitePrefixEventLaw cutoff index) := by
  unfold finitePrefixEventLaw
  infer_instance

/-- The fixed true event exposes exactly the retained finite prefix. -/
@[simp]
theorem finitePrefixEventLaw_apply_true (cutoff index : ℕ) :
    finitePrefixEventLaw cutoff index {true} = if index ≤ cutoff then 1 else 0 := by
  by_cases hIndex : index ≤ cutoff <;> simp [finitePrefixEventLaw, hIndex]

/-- A finite prefix leaves the scaled-log limsup at bottom even for diverging positive speed. -/
theorem finitePrefixEventLaw_scaledLog_limsup_eq_bot (cutoff : ℕ) :
    limsup (fun index ↦ (finitePrefixEventLaw cutoff index {true}).log /
      (((index : ℝ) + 1) : EReal)) atTop = ⊥ := by
  have hTail : ∀ᶠ index in atTop,
      (finitePrefixEventLaw cutoff index {true}).log /
        (((index : ℝ) + 1) : EReal) = ⊥ := by
    filter_upwards [eventually_gt_atTop cutoff] with index hIndex
    rw [finitePrefixEventLaw_apply_true, ite_eq_right (not_le.mpr hIndex), ENNReal.log_zero]
    exact EReal.bot_div_of_pos_ne_top (by positivity) (EReal.coe_ne_top _)
  exact (limsup_congr hTail).trans (limsup_const ⊥)

/-- No positive exponential bound holds at every index of these normalized laws, despite their
arbitrarily strong asymptotic log-limsup bound. -/
theorem finitePrefixEventLaw_not_forall_le_exp (cutoff : ℕ) {exponent : ℝ}
    (hExponent : 0 < exponent) :
    ¬ ∀ index, finitePrefixEventLaw cutoff index {true} ≤
      ENNReal.ofReal (Real.exp (-((index : ℝ) + 1) * exponent)) := by
  intro hBound
  have hLog := ENNReal.log_monotone (hBound 0)
  simp only [finitePrefixEventLaw_apply_true, Nat.zero_le, ite_true, ENNReal.log_one,
    Nat.cast_zero, zero_add, neg_one_mul,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at hLog
  norm_cast at hLog
  linarith

end FiniteMarkovProcesses.InformationTheory
