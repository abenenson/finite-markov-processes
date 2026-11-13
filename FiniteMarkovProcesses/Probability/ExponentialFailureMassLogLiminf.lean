/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Order.LiminfLimsup

/-!
# Logarithmic liminf from an exponential estimate with vanishing failure mass

An event probability bounded below by an exponential particle-speed factor times one minus a
vanishing failure mass has logarithmic liminf at least the negative exponential rate.  The proof
keeps probabilities and their logarithms extended-valued, so zero probability remains visible.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter
open scoped ENNReal Topology

noncomputable section

/-- If a nonnegative extended probability sequence dominates
`exp (-(n+1) * threshold) * (1 - failure n)` eventually and `failure` tends to zero, then its
extended logarithm divided by the exact positive particle count has liminf at least
`-threshold`. -/
theorem neg_le_liminf_ennrealLog_div_positiveParticleCount_of_exponential_one_sub_failure_le
    (probability failure : ℕ → ENNReal) (threshold : ℝ)
    (hFailure : Tendsto failure atTop (nhds 0))
    (hLower : ∀ᶠ successorIndex : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-((successorIndex + 1 : ℝ) * threshold))) *
        (1 - failure successorIndex) ≤ probability successorIndex) :
    ((-threshold : ℝ) : EReal) ≤
      liminf
        (fun successorIndex ↦
          ENNReal.log (probability successorIndex) /
            (((successorIndex + 1 : ℕ) : ℝ) : EReal))
        atTop := by
  let remainder : ℕ → ENNReal := fun successorIndex ↦ 1 - failure successorIndex
  have hRemainder : Tendsto remainder atTop (nhds 1) := by
    have hContinuous := ENNReal.continuous_sub_left ENNReal.one_ne_top
    simpa only [remainder, tsub_zero, Function.comp_def] using
      (hContinuous.tendsto 0).comp hFailure
  have hRemainderPositive : ∀ᶠ successorIndex in atTop,
      0 < remainder successorIndex :=
    hRemainder.eventually (eventually_gt_nhds zero_lt_one)
  have hRemainderReal : Tendsto
      (fun successorIndex ↦ (remainder successorIndex).toReal)
      atTop (nhds 1) := by
    simpa only [ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hRemainder
  have hLogRemainderReal : Tendsto
      (fun successorIndex ↦ Real.log (remainder successorIndex).toReal)
      atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hRemainderReal
  have hParticleCount : Tendsto
      (fun successorIndex : ℕ ↦ ((successorIndex + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hCorrection : Tendsto
      (fun successorIndex ↦
        Real.log (remainder successorIndex).toReal /
          ((successorIndex + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    hLogRemainderReal.div_atTop hParticleCount
  have hRealLowerLimit : Tendsto
      (fun successorIndex ↦
        -threshold +
          Real.log (remainder successorIndex).toReal /
            ((successorIndex + 1 : ℕ) : ℝ))
      atTop (nhds (-threshold)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hCorrection
  have hCoeLowerLimit : Tendsto
      (fun successorIndex ↦
        ((-threshold +
          Real.log (remainder successorIndex).toReal /
            ((successorIndex + 1 : ℕ) : ℝ) : ℝ) : EReal))
      atTop (nhds (((-threshold : ℝ) : EReal))) :=
    EReal.tendsto_coe.mpr hRealLowerLimit
  let lowerLog : ℕ → EReal := fun successorIndex ↦
    ENNReal.log
        (ENNReal.ofReal
            (Real.exp (-((successorIndex + 1 : ℝ) * threshold))) *
          remainder successorIndex) /
      (((successorIndex + 1 : ℕ) : ℝ) : EReal)
  have hLowerLogEq : ∀ᶠ successorIndex in atTop,
      lowerLog successorIndex =
        ((-threshold +
          Real.log (remainder successorIndex).toReal /
            ((successorIndex + 1 : ℕ) : ℝ) : ℝ) : EReal) := by
    filter_upwards [hRemainderPositive] with successorIndex hPositive
    have hRemainderFinite : remainder successorIndex ≠ ⊤ := by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self)
    unfold lowerLog
    rw [ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
      ENNReal.log_pos_real hPositive.ne' hRemainderFinite]
    rw [← EReal.coe_add, ← EReal.coe_div]
    norm_cast
    have hParticlePositive : (0 : ℝ) < successorIndex + 1 := by positivity
    field_simp
  have hLowerLogLimit : Tendsto lowerLog atTop
      (nhds (((-threshold : ℝ) : EReal))) :=
    hCoeLowerLimit.congr' (hLowerLogEq.mono fun _successorIndex hEquality ↦
      hEquality.symm)
  have hLogLower : ∀ᶠ successorIndex in atTop,
      lowerLog successorIndex ≤
        ENNReal.log (probability successorIndex) /
          (((successorIndex + 1 : ℕ) : ℝ) : EReal) := by
    filter_upwards [hLower] with successorIndex hSuccessorIndex
    unfold lowerLog remainder
    exact EReal.monotone_div_right_of_nonneg
      (by positivity : (0 : EReal) ≤
        (((successorIndex + 1 : ℕ) : ℝ) : EReal))
      (ENNReal.log_monotone hSuccessorIndex)
  calc
    ((-threshold : ℝ) : EReal) = liminf lowerLog atTop :=
      hLowerLogLimit.liminf_eq.symm
    _ ≤ liminf
        (fun successorIndex ↦
          ENNReal.log (probability successorIndex) /
            (((successorIndex + 1 : ℕ) : ℝ) : EReal))
        atTop := Filter.liminf_le_liminf hLogLower

end

end FiniteMarkovProcesses.Probability
