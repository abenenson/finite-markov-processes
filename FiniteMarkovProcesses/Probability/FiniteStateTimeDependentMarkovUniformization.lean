/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniformization of bounded time-dependent finite-state jump rates

This module constructs a single strictly dominating clock for a bounded measurable family of
finite-state off-diagonal jump rates. At every physical time, the clock turns the rate row into a
probability mass function by placing the unused rate on a virtual self-event.

The final section proves the finite-word normalization used by time-dependent uniformized
history laws. These words retain virtual self-events.

## Main results

- `FiniteStateTimeDependentMarkovRate.uniformizedTransitionPMF`: the time-dependent stochastic
  virtual-event row.
- `sum_finiteStateTimeDependentMarkovContinuationWeight`: every finite time-dependent future-word
  weight has total mass one.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- A bounded measurable family of finite-state off-diagonal jump rates. The explicit escape
bound is source data: no compactness or continuity premise is hidden in the structure. -/
structure FiniteStateTimeDependentMarkovRate (State : Type u)
    [Fintype State] [DecidableEq State] where
  /-- Directed jump rate at one physical time. -/
  rate : ℝ → State → State → ℝ≥0
  /-- Virtual self-jumps have zero physical rate. -/
  rate_self : ∀ time state, rate time state state = 0
  /-- Every directed rate is measurable in physical time. -/
  measurable_rate : ∀ source target, Measurable fun time ↦ rate time source target
  /-- Supplied uniform bound for every escape row. -/
  escapeBound : ℝ≥0
  /-- The supplied bound dominates every time-dependent escape row. -/
  escapeRate_le_bound : ∀ time source,
    (∑ target ∈ Finset.univ.erase source, rate time source target) ≤ escapeBound

namespace FiniteStateTimeDependentMarkovRate

/-- Total physical escape rate from one state at one time. -/
noncomputable def escapeRate (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source : State) : ℝ≥0 :=
  ∑ target ∈ Finset.univ.erase source, rates.rate time source target

/-- The declared escape bound controls the named escape rate. -/
theorem escapeRate_le_escapeBound (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source : State) :
    rates.escapeRate time source ≤ rates.escapeBound :=
  rates.escapeRate_le_bound time source

/-- Every time-dependent escape row is measurable. -/
theorem measurable_escapeRate (rates : FiniteStateTimeDependentMarkovRate State)
    (source : State) :
    Measurable fun time ↦ rates.escapeRate time source := by
  unfold escapeRate
  apply Finset.measurable_sum
  intro target _hTarget
  exact rates.measurable_rate source target

/-- Every bounded measurable escape row is interval integrable on arbitrary finite endpoints. -/
theorem intervalIntegrable_escapeRate
    (rates : FiniteStateTimeDependentMarkovRate State)
    (source : State) (lower upper : ℝ) :
    IntervalIntegrable
      (fun time ↦ (rates.escapeRate time source : ℝ)) volume lower upper := by
  constructor <;> apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
  · exact rates.measurable_escapeRate source |>.coe_nnreal_real.aestronglyMeasurable
  · exact Eventually.of_forall fun time ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact_mod_cast rates.escapeRate_le_escapeBound time source
  · exact rates.measurable_escapeRate source |>.coe_nnreal_real.aestronglyMeasurable
  · exact Eventually.of_forall fun time ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact_mod_cast rates.escapeRate_le_escapeBound time source

/-- The cumulative integrated escape of a bounded measurable row is globally Lipschitz with the
declared escape bound. -/
theorem lipschitzWith_integral_escapeRate
    (rates : FiniteStateTimeDependentMarkovRate State) (source : State) :
    LipschitzWith rates.escapeBound
      (fun endpoint ↦
        ∫ time in (0 : ℝ)..endpoint, (rates.escapeRate time source : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [Real.dist_eq]
  have hFirst := rates.intervalIntegrable_escapeRate source 0 first
  have hSecond := rates.intervalIntegrable_escapeRate source 0 second
  have hDifference := intervalIntegral.integral_interval_sub_left hFirst hSecond
  calc
    |(∫ time in (0 : ℝ)..first, (rates.escapeRate time source : ℝ)) -
        ∫ time in (0 : ℝ)..second, (rates.escapeRate time source : ℝ)| =
      ‖∫ time in second..first, (rates.escapeRate time source : ℝ)‖ := by
        rw [hDifference, Real.norm_eq_abs]
    _ ≤ (rates.escapeBound : ℝ) * |first - second| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro time _hTime
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact_mod_cast rates.escapeRate_le_escapeBound time source
    _ = (rates.escapeBound : ℝ) * dist first second := by rw [Real.dist_eq]

/-- Strictly positive common clock dominating every time-dependent escape row. -/
noncomputable def uniformizationRate
    (rates : FiniteStateTimeDependentMarkovRate State) : ℝ≥0 :=
  rates.escapeBound + 1

/-- The time-dependent uniformization clock is strictly positive. -/
theorem uniformizationRate_pos (rates : FiniteStateTimeDependentMarkovRate State) :
    0 < rates.uniformizationRate := by
  unfold uniformizationRate
  exact lt_add_of_le_of_pos (zero_le : (0 : ℝ≥0) ≤ rates.escapeBound) zero_lt_one

/-- Every escape row is dominated by the strictly positive uniformization clock. -/
theorem escapeRate_le_uniformizationRate
    (rates : FiniteStateTimeDependentMarkovRate State) (time : ℝ) (source : State) :
    rates.escapeRate time source ≤ rates.uniformizationRate :=
  (rates.escapeRate_le_escapeBound time source).trans
    (le_add_of_nonneg_right zero_le_one)

/-- One virtual-event transition weight at a fixed physical time. Genuine jumps carry their
physical rate divided by the common clock; the diagonal carries the unused clock rate. -/
noncomputable def uniformizedTransitionWeight
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source target : State) : ℝ≥0 :=
  if source = target then
    1 - rates.escapeRate time source / rates.uniformizationRate
  else rates.rate time source target / rates.uniformizationRate

/-- An off-diagonal transition has its exact rate-over-clock weight. -/
theorem uniformizedTransitionWeight_of_ne
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) {source target : State} (hNe : source ≠ target) :
    rates.uniformizedTransitionWeight time source target =
      rates.rate time source target / rates.uniformizationRate := by
  simp [uniformizedTransitionWeight, hNe]

/-- A virtual self-event has the exact unused escape fraction. -/
theorem uniformizedTransitionWeight_self
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (state : State) :
    rates.uniformizedTransitionWeight time state state =
      1 - rates.escapeRate time state / rates.uniformizationRate := by
  simp [uniformizedTransitionWeight]

/-- Every virtual transition weight is measurable in physical time. -/
theorem measurable_uniformizedTransitionWeight
    (rates : FiniteStateTimeDependentMarkovRate State)
    (source target : State) :
    Measurable fun time ↦ rates.uniformizedTransitionWeight time source target := by
  by_cases hEq : source = target
  · subst target
    simp only [uniformizedTransitionWeight_self]
    exact measurable_const.sub ((rates.measurable_escapeRate source).div_const _)
  · simp only [uniformizedTransitionWeight, hEq]
    exact (rates.measurable_rate source target).div_const _

/-- Every time-dependent virtual transition row sums to one. -/
theorem sum_uniformizedTransitionWeight
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source : State) :
    ∑ target, rates.uniformizedTransitionWeight time source target = 1 := by
  rw [show (∑ target, rates.uniformizedTransitionWeight time source target) =
      rates.uniformizedTransitionWeight time source source +
        ∑ target ∈ Finset.univ.erase source,
          rates.uniformizedTransitionWeight time source target by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ source), add_comm]]
  rw [rates.uniformizedTransitionWeight_self]
  have hOffDiagonal (target : State) (hTarget : target ∈ Finset.univ.erase source) :
      rates.uniformizedTransitionWeight time source target =
        rates.rate time source target / rates.uniformizationRate := by
    apply rates.uniformizedTransitionWeight_of_ne
    exact fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm
  rw [Finset.sum_congr rfl hOffDiagonal, ← Finset.sum_div]
  change 1 - rates.escapeRate time source / rates.uniformizationRate +
      rates.escapeRate time source / rates.uniformizationRate = 1
  exact tsub_add_cancel_of_le <| by
    exact (div_le_one rates.uniformizationRate_pos).mpr
      (rates.escapeRate_le_uniformizationRate time source)

/-- Probability mass function of one time-dependent virtual-event transition. -/
noncomputable def uniformizedTransitionPMF
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source : State) : PMF State :=
  PMF.ofFintype
    (fun target ↦ (rates.uniformizedTransitionWeight time source target : ℝ≥0∞))
    (by
      rw [← ENNReal.ofNNReal_finsetSum]
      congr 1
      exact rates.sum_uniformizedTransitionWeight time source)

/-- Evaluating the time-dependent transition PMF recovers its virtual transition weight. -/
@[simp]
theorem uniformizedTransitionPMF_apply
    (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (source target : State) :
    rates.uniformizedTransitionPMF time source target =
      rates.uniformizedTransitionWeight time source target := by
  simp [uniformizedTransitionPMF]

/-- Every real-valued time-dependent transition probability is measurable in physical time. -/
theorem measurable_uniformizedTransitionPMF_toReal
    (rates : FiniteStateTimeDependentMarkovRate State)
    (source target : State) :
    Measurable fun time ↦ (rates.uniformizedTransitionPMF time source target).toReal := by
  simpa only [uniformizedTransitionPMF_apply, ENNReal.coe_toReal, Function.comp_def] using
    NNReal.continuous_coe.measurable.comp
      (rates.measurable_uniformizedTransitionWeight source target)

end FiniteStateTimeDependentMarkovRate

/-- Weight of one future-state word under an arbitrary finite family of Markov rows. -/
noncomputable def finiteStateTimeDependentMarkovContinuationWeight
    {eventCount : ℕ} (transition : Fin eventCount → State → PMF State)
    (source : State) (future : Fin eventCount → State) : ℝ :=
  let states : Fin (eventCount + 1) → State := Fin.cons source future
  ∏ index : Fin eventCount,
    (transition index (states index.castSucc) (states index.succ)).toReal

omit [Fintype State] [DecidableEq State] in
/-- A nonempty time-dependent future-word weight factors through its first transition. -/
theorem finiteStateTimeDependentMarkovContinuationWeight_cons
    {eventCount : ℕ} (first : State → PMF State)
    (remaining : Fin eventCount → State → PMF State)
    (source target : State) (future : Fin eventCount → State) :
    finiteStateTimeDependentMarkovContinuationWeight
        (Fin.cons first remaining) source (Fin.cons target future) =
      (first source target).toReal *
        finiteStateTimeDependentMarkovContinuationWeight remaining target future := by
  unfold finiteStateTimeDependentMarkovContinuationWeight
  rw [Fin.prod_univ_succ]
  congr 1

omit [DecidableEq State] in
private theorem sum_pmf_toReal (law : PMF State) :
    ∑ state, (law state).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun state _ ↦ law.apply_ne_top state)]
  rw [show ∑ state, law state = 1 by
    simpa only [tsum_fintype] using law.tsum_coe]
  simp

omit [DecidableEq State] in
/-- Every finite time-dependent future-word weight has total mass one. -/
theorem sum_finiteStateTimeDependentMarkovContinuationWeight
    {eventCount : ℕ} (transition : Fin eventCount → State → PMF State)
    (source : State) :
    ∑ future : Fin eventCount → State,
      finiteStateTimeDependentMarkovContinuationWeight transition source future = 1 := by
  induction eventCount generalizing source with
  | zero =>
      rw [Fintype.sum_unique]
      unfold finiteStateTimeDependentMarkovContinuationWeight
      simp
  | succ eventCount inductionHypothesis =>
      let first : State → PMF State := transition 0
      let remaining : Fin eventCount → State → PMF State := Fin.tail transition
      have hTransition : Fin.cons first remaining = transition := by
        exact Fin.cons_self_tail transition
      rw [← hTransition]
      rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) => State)).sum_comp]
      rw [Fintype.sum_prod_type]
      change (∑ target : State, ∑ future : Fin eventCount → State,
        finiteStateTimeDependentMarkovContinuationWeight
          (Fin.cons first remaining) source (Fin.cons target future)) = 1
      simp_rw [finiteStateTimeDependentMarkovContinuationWeight_cons]
      rw [show (∑ target : State, ∑ future : Fin eventCount → State,
          (first source target).toReal *
            finiteStateTimeDependentMarkovContinuationWeight remaining target future) =
        ∑ target : State, (first source target).toReal *
          ∑ future : Fin eventCount → State,
            finiteStateTimeDependentMarkovContinuationWeight remaining target future by
        apply Finset.sum_congr rfl
        intro target _
        rw [Finset.mul_sum]]
      simp_rw [inductionHypothesis, mul_one]
      exact sum_pmf_toReal (first source)

end FiniteMarkovProcesses.Probability
