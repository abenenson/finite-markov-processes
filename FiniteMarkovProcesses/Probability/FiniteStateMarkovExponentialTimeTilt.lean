/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovUniformization

/-!
# Exponential time tilts of finite-state Markov jump generators

This module turns a uniformly upper-bounded measurable transition exponent into the bounded
time-dependent rate family `q(x,y) * exp (zeta(t,x,y))`. The construction is source-neutral and
keeps the exponent, its measurability, and the bound explicit.

It does not assert a Girsanov identity or identify a reduced physical history law. Those require
the time-dependent virtual-law normalization and self-event deletion developed separately.

## Main results

- `FiniteStateTransitionExponent`: measurable uniformly upper-bounded transition exponents.
- `FiniteStateMarkovGenerator.exponentialTimeTilt`: the induced bounded time-dependent rates.
- `FiniteStateMarkovGenerator.exponentialTimeTilt_rate_toReal`: exact real-valued tilted rate.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- A measurable transition exponent with one explicit uniform upper bound. Only an upper bound is
needed to dominate the exponentially tilted escape rates. -/
structure FiniteStateTransitionExponent (State : Type u) where
  /-- Time- and transition-dependent real exponent. -/
  exponent : ℝ → State → State → ℝ
  /-- Every transition exponent is measurable in physical time. -/
  measurable_exponent : ∀ source target, Measurable fun time ↦ exponent time source target
  /-- Supplied uniform upper bound. -/
  upperBound : ℝ
  /-- The supplied bound controls every time and directed pair. -/
  exponent_le_upperBound : ∀ time source target, exponent time source target ≤ upperBound

namespace FiniteStateTransitionExponent

/-- Positive nonnegative-real exponential multiplier at one time and transition. -/
noncomputable def exponentialMultiplier (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source target : State) : ℝ≥0 :=
  ⟨Real.exp (tilt.exponent time source target), (Real.exp_pos _).le⟩

/-- Nonnegative-real exponential of the supplied uniform upper bound. -/
noncomputable def exponentialUpperBound
    (tilt : FiniteStateTransitionExponent State) : ℝ≥0 :=
  ⟨Real.exp tilt.upperBound, (Real.exp_pos _).le⟩

omit [Fintype State] [DecidableEq State] in
/-- The multiplier has the literal real exponential value. -/
@[simp]
theorem coe_exponentialMultiplier (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source target : State) :
    (tilt.exponentialMultiplier time source target : ℝ) =
      Real.exp (tilt.exponent time source target) :=
  rfl

omit [Fintype State] [DecidableEq State] in
/-- The uniform multiplier bound has the literal real exponential value. -/
@[simp]
theorem coe_exponentialUpperBound (tilt : FiniteStateTransitionExponent State) :
    (tilt.exponentialUpperBound : ℝ) = Real.exp tilt.upperBound :=
  rfl

omit [Fintype State] [DecidableEq State] in
/-- Every exponential multiplier is dominated by the supplied exponential upper bound. -/
theorem exponentialMultiplier_le_exponentialUpperBound
    (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source target : State) :
    tilt.exponentialMultiplier time source target ≤ tilt.exponentialUpperBound := by
  exact_mod_cast Real.exp_le_exp.mpr (tilt.exponent_le_upperBound time source target)

omit [Fintype State] [DecidableEq State] in
/-- Every exponential multiplier is measurable in physical time. -/
theorem measurable_exponentialMultiplier
    (tilt : FiniteStateTransitionExponent State) (source target : State) :
    Measurable fun time ↦ tilt.exponentialMultiplier time source target := by
  apply measurable_coe_nnreal_real_iff.mp
  simpa only [coe_exponentialMultiplier] using
    (tilt.measurable_exponent source target).exp

end FiniteStateTransitionExponent

namespace FiniteStateMarkovGenerator

/-- Time-dependent rate obtained by exponentially tilting every physical directed rate. -/
noncomputable def exponentialTimeTilt
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State) :
    FiniteStateTimeDependentMarkovRate State where
  rate := fun time source target ↦
    generator.rate source target * tilt.exponentialMultiplier time source target
  rate_self := fun time state ↦ by simp [generator.rate_self state]
  measurable_rate := fun source target ↦
    measurable_const.mul (tilt.measurable_exponentialMultiplier source target)
  escapeBound := finiteStateTotalEscapeBound generator * tilt.exponentialUpperBound
  escapeRate_le_bound := fun time source ↦ by
    calc
      (∑ target ∈ Finset.univ.erase source,
        generator.rate source target * tilt.exponentialMultiplier time source target) ≤
          ∑ target ∈ Finset.univ.erase source,
            generator.rate source target * tilt.exponentialUpperBound := by
        apply Finset.sum_le_sum
        intro target _hTarget
        exact mul_le_mul le_rfl
          (tilt.exponentialMultiplier_le_exponentialUpperBound time source target)
          zero_le zero_le
      _ = generator.escapeRate source * tilt.exponentialUpperBound := by
        rw [← Finset.sum_mul]
        rw [show (∑ target ∈ Finset.univ.erase source, generator.rate source target) =
            generator.escapeRate source by
          rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self source)]
          rfl]
      _ ≤ finiteStateTotalEscapeBound generator * tilt.exponentialUpperBound :=
        mul_le_mul (escapeRate_le_finiteStateTotalEscapeBound generator source)
          le_rfl zero_le zero_le

/-- The exponentially tilted nonnegative rate has the exact expected real value. -/
theorem exponentialTimeTilt_rate_toReal
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source target : State) :
    (generator.exponentialTimeTilt tilt).rate time source target =
      generator.rate source target * tilt.exponentialMultiplier time source target :=
  rfl

/-- Real-valued form of the exponentially tilted directed rate. -/
theorem coe_exponentialTimeTilt_rate
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source target : State) :
    ((generator.exponentialTimeTilt tilt).rate time source target : ℝ) =
      (generator.rate source target : ℝ) *
        Real.exp (tilt.exponent time source target) := by
  rfl

/-- The tilted escape rate is the finite sum of the exponentially tilted physical rates. -/
theorem exponentialTimeTilt_escapeRate
    (generator : FiniteStateMarkovGenerator State)
    (tilt : FiniteStateTransitionExponent State)
    (time : ℝ) (source : State) :
    (generator.exponentialTimeTilt tilt).escapeRate time source =
      ∑ target ∈ Finset.univ.erase source,
        generator.rate source target * tilt.exponentialMultiplier time source target := by
  rfl

end FiniteStateMarkovGenerator

end FiniteMarkovProcesses.Probability
