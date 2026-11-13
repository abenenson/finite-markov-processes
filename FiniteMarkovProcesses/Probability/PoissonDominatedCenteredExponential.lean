/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.PoissonCountExponentialTail
public import Mathlib.Analysis.Complex.Exponential

/-!
# Centered exponential moments under Poisson count domination

The positive exponential remainder is monotone on nonnegative observations. Pulling an
observation back to a law carrying a dominating Poisson count therefore controls its centered
moment without replacing its actual mean by the count intensity.

## Main results

* `mgf_centered_le_poissonRemainder`: both signed tilts retain the true observation mean.
* `poissonExponentialRemainder_le_quadratic`: an explicit local quadratic estimate.
* `mgf_centered_le_exp_sq_of_mem_Icc`: the bounded density-coordinate control.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- The raw exponential remainder of a Poisson count, including its exact first moment. -/
def poissonExponentialRemainder (intensity tilt : ℝ) : ℝ :=
  Real.exp (intensity * (Real.exp tilt - 1)) - 1 - intensity * tilt

/-- A signed exponential remainder is bounded by the positive absolute-argument remainder. -/
theorem exp_sub_one_sub_le_abs_remainder (value : ℝ) :
    Real.exp value - 1 - value ≤ Real.exp |value| - 1 - |value| := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (value : ℂ) 2
  norm_num [Finset.sum_range_succ, ← Complex.ofReal_exp, ← Complex.ofReal_sub] at h
  have hReal : |Real.exp value - (1 + value)| ≤ Real.exp |value| - (1 + |value|) := by
    exact_mod_cast h
  convert (le_abs_self (Real.exp value - (1 + value))).trans hReal using 1 <;> ring

/-- The positive exponential remainder increases with its nonnegative argument. -/
theorem exp_sub_one_sub_mono {left right : ℝ} (hLeft : 0 ≤ left) (hOrder : left ≤ right) :
    Real.exp left - 1 - left ≤ Real.exp right - 1 - right := by
  have hOne : 1 ≤ Real.exp left := Real.one_le_exp_iff.mpr hLeft
  have hStep := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (right - left))
    (Real.exp_nonneg left)
  rw [← Real.exp_add] at hStep
  have hGap := mul_le_mul_of_nonneg_right hOne (sub_nonneg.mpr hOrder)
  have hAdd : left + (right - left) = right := by ring
  rw [hAdd] at hStep
  nlinarith

private theorem exp_le_quadratic {value : ℝ} (hZero : 0 ≤ value) (hHalf : value ≤ 1 / 2) :
    Real.exp value ≤ 1 + value + (2 / 3 : ℝ) * value ^ 2 := by
  have h := Real.exp_bound' hZero (hHalf.trans (by norm_num)) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [sq_nonneg value, mul_nonneg (sq_nonneg value) (sub_nonneg.mpr hHalf)]

/-- The Poisson raw remainder has an explicit quadratic bound on a capped tilt interval.
The intensity may be zero; no division by intensity is used. -/
theorem poissonExponentialRemainder_le_quadratic
    {intensity tilt : ℝ} (hIntensity : 0 ≤ intensity) (hTilt : 0 ≤ tilt)
    (hCap : tilt ≤ 1 / (4 * (intensity + 1))) :
    poissonExponentialRemainder intensity tilt ≤ (intensity + 1) ^ 2 * tilt ^ 2 := by
  have hDenom : 0 < 4 * (intensity + 1) := by positivity
  have hProduct : tilt * (4 * (intensity + 1)) ≤ 1 :=
    (le_div_iff₀ hDenom).mp hCap
  have hQuarter : tilt ≤ 1 / 4 := by nlinarith [mul_nonneg hIntensity hTilt]
  have hSmall := exp_le_quadratic hTilt (hQuarter.trans (by norm_num))
  have hTiltSquare : tilt ^ 2 ≤ tilt / 4 := by
    nlinarith [mul_nonneg hTilt (sub_nonneg.mpr hQuarter)]
  have hExp : Real.exp tilt - 1 ≤ (7 / 6 : ℝ) * tilt := by nlinarith
  let inner := intensity * (Real.exp tilt - 1)
  have hInnerZero : 0 ≤ inner :=
    mul_nonneg hIntensity (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hTilt))
  have hInnerBound : inner ≤ (7 / 6 : ℝ) * intensity * tilt := by
    dsimp [inner]
    nlinarith [mul_le_mul_of_nonneg_left hExp hIntensity]
  have hInnerHalf : inner ≤ 1 / 2 := by nlinarith
  have hOuter := exp_le_quadratic hInnerZero hInnerHalf
  have hInnerSquare : inner ^ 2 ≤ ((7 / 6 : ℝ) * intensity * tilt) ^ 2 :=
    sq_le_sq₀ hInnerZero (by positivity) |>.mpr hInnerBound
  have hInnerFirst : inner - intensity * tilt ≤ (2 / 3 : ℝ) * intensity * tilt ^ 2 := by
    dsimp [inner]
    nlinarith [mul_le_mul_of_nonneg_left hSmall hIntensity]
  change Real.exp inner - 1 - intensity * tilt ≤ _
  nlinarith [sq_nonneg intensity, sq_nonneg tilt,
    mul_nonneg hIntensity (sq_nonneg tilt), sq_nonneg (intensity * tilt)]

universe u
variable {Sample : Type u} [MeasurableSpace Sample]

/-- Centering cancels the actual first moment in any integrable raw-remainder estimate. -/
theorem mgf_centered_le_exp_of_remainder
    (law : Measure Sample) [IsProbabilityMeasure law] (observable : Sample → ℝ)
    (hObservable : Integrable observable law) (tilt bound : ℝ)
    (hExp : Integrable (fun sample ↦ Real.exp (tilt * observable sample)) law)
    (hRemainder : (∫ sample,
      Real.exp (tilt * observable sample) - 1 - tilt * observable sample ∂law) ≤ bound) :
    mgf (fun sample ↦ observable sample - ∫ point, observable point ∂law) law tilt ≤
      Real.exp bound := by
  have hMoment : mgf observable law tilt ≤
      Real.exp (tilt * (∫ sample, observable sample ∂law) + bound) := by
    have hRaw : Integrable (fun sample ↦ Real.exp (tilt * observable sample) - 1) law :=
      hExp.sub (integrable_const 1)
    rw [integral_sub hRaw (hObservable.const_mul tilt),
      integral_sub hExp (integrable_const 1), integral_const_mul] at hRemainder
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hRemainder
    have h := Real.add_one_le_exp (tilt * (∫ sample, observable sample ∂law) + bound)
    change (∫ sample, Real.exp (tilt * observable sample) ∂law) ≤ _
    linarith
  have hRewrite :
      (fun sample ↦ observable sample - ∫ point, observable point ∂law) =
      (fun sample ↦ -(∫ point, observable point ∂law) + observable sample) := by
    funext sample
    ring
  rw [hRewrite, mgf_const_add]
  calc
    _ ≤ Real.exp (tilt * -(∫ point, observable point ∂law)) *
        Real.exp (tilt * (∫ point, observable point ∂law) + bound) := by
      exact mul_le_mul_of_nonneg_left hMoment (Real.exp_nonneg _)
    _ = Real.exp bound := by rw [← Real.exp_add]; congr 1; ring

/-- A nonnegative observation dominated by an exactly Poisson count has a centered exponential
moment bounded at both signed tilts. Its center remains its own expectation. -/
theorem mgf_centered_le_poissonRemainder
    (law : Measure Sample) [IsProbabilityMeasure law] (observable : Sample → ℝ)
    (count : Sample → ℕ) (intensity : NNReal)
    (hObservable : Measurable observable) (hCount : Measurable count)
    (hBound : ∀ sample, 0 ≤ observable sample ∧ observable sample ≤ (count sample : ℝ))
    (hLaw : Measure.map count law = poissonMeasure intensity) (tilt : ℝ) :
    Integrable (fun sample ↦ Real.exp (tilt *
        (observable sample - ∫ point, observable point ∂law))) law ∧
      mgf (fun sample ↦ observable sample - ∫ point, observable point ∂law) law tilt ≤
        Real.exp (poissonExponentialRemainder intensity |tilt|) := by
  have hCountInt : Integrable (fun sample ↦ (count sample : ℝ)) law := by
    have h := integrable_poissonCount intensity
    rw [← hLaw] at h
    exact (integrable_map_measure h.1 hCount.aemeasurable).mp h
  have hCountExp : Integrable (fun sample ↦ Real.exp ((count sample : ℝ) * |tilt|)) law := by
    have h := integrable_exp_mul_poissonCount intensity |tilt|
    rw [← hLaw] at h
    exact (integrable_map_measure h.1 hCount.aemeasurable).mp h
  have hObsInt : Integrable observable law := by
    refine hCountInt.mono' hObservable.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro sample
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hBound sample).1] using (hBound sample).2
  have hObsExp : Integrable (fun sample ↦ Real.exp (tilt * observable sample)) law := by
    refine hCountExp.mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
    intro sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      tilt * observable sample ≤ |tilt| * observable sample :=
        mul_le_mul_of_nonneg_right (le_abs_self tilt) (hBound sample).1
      _ ≤ (count sample : ℝ) * |tilt| := by
        nlinarith [mul_le_mul_of_nonneg_left (hBound sample).2 (abs_nonneg tilt)]
  constructor
  · have h := hObsExp.mul_const (Real.exp (-(tilt * ∫ point, observable point ∂law)))
    convert h using 1
    funext sample
    rw [← Real.exp_add]
    congr 1
    ring
  apply mgf_centered_le_exp_of_remainder law observable hObsInt tilt _ hObsExp
  have hCountRemainder : Integrable (fun sample ↦
      Real.exp ((count sample : ℝ) * |tilt|) - 1 - |tilt| * (count sample : ℝ)) law :=
    (hCountExp.sub (integrable_const 1)).sub (hCountInt.const_mul |tilt|)
  have hCompare : (∫ sample,
      Real.exp (tilt * observable sample) - 1 - tilt * observable sample ∂law) ≤
      ∫ sample, Real.exp (|tilt| * (count sample : ℝ)) - 1 -
        |tilt| * (count sample : ℝ) ∂law := by
    apply integral_mono ((hObsExp.sub (integrable_const 1)).sub (hObsInt.const_mul tilt))
      (by simpa only [mul_comm] using hCountRemainder)
    intro sample
    refine (exp_sub_one_sub_le_abs_remainder (tilt * observable sample)).trans ?_
    rw [abs_mul, abs_of_nonneg (hBound sample).1]
    exact exp_sub_one_sub_mono (mul_nonneg (abs_nonneg tilt) (hBound sample).1)
      (mul_le_mul_of_nonneg_left (hBound sample).2 (abs_nonneg tilt))
  refine hCompare.trans_eq ?_
  have hMap : (∫ sample, Real.exp (|tilt| * (count sample : ℝ)) - 1 -
      |tilt| * (count sample : ℝ) ∂law) =
      ∫ value : ℕ, Real.exp (|tilt| * (value : ℝ)) - 1 - |tilt| * (value : ℝ)
        ∂poissonMeasure intensity := by
    rw [← hLaw, integral_map hCount.aemeasurable (by fun_prop)]
  have hPoissonExp : Integrable (fun value : ℕ ↦ Real.exp (|tilt| * (value : ℝ)))
      (poissonMeasure intensity) := by
    simpa only [mul_comm] using integrable_exp_mul_poissonCount intensity |tilt|
  have hPoissonRaw : Integrable (fun value : ℕ ↦ Real.exp (|tilt| * (value : ℝ)) - 1)
      (poissonMeasure intensity) := hPoissonExp.sub (integrable_const 1)
  rw [hMap, integral_sub hPoissonRaw ((integrable_poissonCount intensity).const_mul |tilt|),
    integral_sub hPoissonExp (integrable_const 1),
    integral_const_mul, integral_poissonCount]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [show (fun value : ℕ ↦ Real.exp (|tilt| * (value : ℝ))) =
      (fun value : ℕ ↦ Real.exp ((value : ℝ) * |tilt|)) by funext value; rw [mul_comm],
    integral_exp_mul_poissonCount]
  unfold poissonExponentialRemainder
  ring

/-- Bounded density coordinates retain their own initial randomness under the local tilt bound. -/
theorem mgf_centered_le_exp_sq_of_mem_Icc
    (law : Measure Sample) [IsProbabilityMeasure law] (observable : Sample → ℝ)
    (hObservable : Measurable observable) (hBound : ∀ sample, observable sample ∈ Icc 0 1)
    {tilt : ℝ} (hTilt : |tilt| ≤ 1) :
    Integrable (fun sample ↦ Real.exp (tilt *
        (observable sample - ∫ point, observable point ∂law))) law ∧
      mgf (fun sample ↦ observable sample - ∫ point, observable point ∂law) law tilt ≤
        Real.exp (tilt ^ 2) := by
  have hObsInt : Integrable observable law := by
    apply Integrable.of_bound hObservable.aestronglyMeasurable 1
    filter_upwards [] with sample
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hBound sample).1] using (hBound sample).2
  have hProduct (sample : Sample) : |tilt * observable sample| ≤ |tilt| := by
    rw [abs_mul, abs_of_nonneg (hBound sample).1]
    exact mul_le_of_le_one_right (abs_nonneg tilt) (hBound sample).2
  have hObsExp : Integrable (fun sample ↦ Real.exp (tilt * observable sample)) law := by
    apply Integrable.of_bound (by fun_prop) (Real.exp |tilt|)
    filter_upwards [] with sample
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hProduct sample))
  constructor
  · have h := hObsExp.mul_const (Real.exp (-(tilt * ∫ point, observable point ∂law)))
    convert h using 1
    funext sample
    rw [← Real.exp_add]
    congr 1
    ring
  apply mgf_centered_le_exp_of_remainder law observable hObsInt tilt _ hObsExp
  calc
    _ ≤ ∫ _sample : Sample, tilt ^ 2 ∂law := by
      apply integral_mono ((hObsExp.sub (integrable_const 1)).sub (hObsInt.const_mul tilt))
        (integrable_const _)
      intro sample
      have h := Real.abs_exp_sub_one_sub_id_le ((hProduct sample).trans hTilt)
      have hSquare := sq_le_sq₀ (abs_nonneg _) (abs_nonneg tilt) |>.mpr (hProduct sample)
      rw [sq_abs, sq_abs] at hSquare
      exact (le_abs_self _).trans (h.trans hSquare)
    _ = _ := by simp

end

end FiniteMarkovProcesses.Probability
