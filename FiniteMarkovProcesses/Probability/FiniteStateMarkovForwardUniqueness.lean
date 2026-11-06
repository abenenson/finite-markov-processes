/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Stability

/-!
# Uniqueness of finite-state constant-generator forward evolution

Absolutely continuous solutions of the same finite-state forward equation contract in coordinate
`L1`. Equal initial data therefore determine the whole evolution on a positive physical interval.
The proof uses sign dissipation, not a supplied uniqueness field, and requires neither stationary
initial data nor strictly positive transition rates. The coordinate functions may be real-valued;
normalization and nonnegativity of their values are unnecessary for uniqueness.

## Main results

- `finiteStateMarkov_l1_le_of_forwardEquation`: contraction on a closed interval.
- `finiteStateMarkov_eqOn_of_forwardEquation`: uniqueness on a half-open physical interval.

## References

Finite-state forward-equation uniqueness is classical; see J. R. Norris, *Markov Chains*,
Section 2.8, https://www.statslab.cam.ac.uk/~jrn10/Markov/.
Here the coordinate `L1` sign-dissipation estimate gives uniqueness for absolutely continuous,
real-valued solutions with an almost-everywhere equation, without probability normalization.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators NNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State]

/-- The finite-state drift is linear under subtraction of coordinate vectors. -/
theorem finiteStateRateErrorDivergence_sub
    (rate : State → State → NNReal) (first second : State → ℝ) (state : State) :
    finiteStateRateErrorDivergence rate (fun point ↦ first point - second point) state =
      finiteStateRateErrorDivergence rate first state -
        finiteStateRateErrorDivergence rate second state := by
  simp only [finiteStateRateErrorDivergence, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Two absolutely continuous solutions of the same constant-generator forward equation contract
in finite-coordinate `L1`. No sign or normalization premise is imposed on their coordinates. -/
theorem finiteStateMarkov_l1_le_of_forwardEquation
    (generator : FiniteStateMarkovGenerator State)
    {first second : ℝ → State → ℝ} {lower upper : ℝ}
    (hBounds : lower ≤ upper)
    (hFirstContinuous : ∀ state,
      AbsolutelyContinuousOnInterval (fun time ↦ first time state) lower upper)
    (hSecondContinuous : ∀ state,
      AbsolutelyContinuousOnInterval (fun time ↦ second time state) lower upper)
    (hFirstDerivative : ∀ state, ∀ᵐ time ∂volume.restrict (Ioo lower upper),
      HasDerivAt (fun point ↦ first point state)
        (finiteStateRateErrorDivergence generator.rate (first time) state) time)
    (hSecondDerivative : ∀ state, ∀ᵐ time ∂volume.restrict (Ioo lower upper),
      HasDerivAt (fun point ↦ second point state)
        (finiteStateRateErrorDivergence generator.rate (second time) state) time) :
    (∑ state, |first upper state - second upper state|) ≤
      ∑ state, |first lower state - second lower state| := by
  let error := fun time state ↦ first time state - second time state
  have hDerivative : ∀ state, ∀ᵐ time ∂volume.restrict (Ioo lower upper),
      HasDerivAt (fun point ↦ error point state)
        (finiteStateRateErrorDivergence generator.rate (error time) state) time := by
    intro state
    filter_upwards [hFirstDerivative state, hSecondDerivative state]
      with time hFirst hSecond
    simpa only [error, finiteStateRateErrorDivergence_sub, Pi.sub_def] using!
      hFirst.sub hSecond
  have hEstimate := finite_sum_abs_sub_le_intervalIntegral_of_ae_hasDerivAt hBounds
    (fun state ↦ (hFirstContinuous state).sub (hSecondContinuous state))
    hDerivative (fun _time ↦ (0 : ℝ)) (intervalIntegrable_const)
    (Eventually.of_forall fun time ↦
      sum_sign_mul_finiteStateRateErrorDivergence_nonpos generator.rate (error time))
  simpa only [error, Pi.sub_def, intervalIntegral.integral_zero, sub_nonpos] using hEstimate

/-- Constant-generator forward evolution is unique from its initial vector. Absolute continuity
is required on each strict subhorizon and is independent of positivity or stationarity.
No duration assumption is needed: the conclusion is vacuous when the interval is empty. -/
theorem finiteStateMarkov_eqOn_of_forwardEquation
    (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ}
    {first second : ℝ → State → ℝ}
    (hFirstContinuous : ∀ horizon ∈ Ico 0 duration, ∀ state,
      AbsolutelyContinuousOnInterval (fun time ↦ first time state) 0 horizon)
    (hSecondContinuous : ∀ horizon ∈ Ico 0 duration, ∀ state,
      AbsolutelyContinuousOnInterval (fun time ↦ second time state) 0 horizon)
    (hFirstDerivative : ∀ state, ∀ᵐ time ∂volume.restrict (Ioo 0 duration),
      HasDerivAt (fun point ↦ first point state)
        (finiteStateRateErrorDivergence generator.rate (first time) state) time)
    (hSecondDerivative : ∀ state, ∀ᵐ time ∂volume.restrict (Ioo 0 duration),
      HasDerivAt (fun point ↦ second point state)
        (finiteStateRateErrorDivergence generator.rate (second time) state) time)
    (hInitial : first 0 = second 0) :
    EqOn first second (Ico 0 duration) := by
  intro horizon hHorizon
  have hRestrict : volume.restrict (Ioo 0 horizon) ≤ volume.restrict (Ioo 0 duration) :=
    Measure.restrict_mono (Ioo_subset_Ioo_right hHorizon.2.le) le_rfl
  have hBound := finiteStateMarkov_l1_le_of_forwardEquation generator hHorizon.1
    (hFirstContinuous horizon hHorizon) (hSecondContinuous horizon hHorizon)
    (fun state ↦ ae_mono hRestrict (hFirstDerivative state))
    (fun state ↦ ae_mono hRestrict (hSecondDerivative state))
  have hSumZero : ∑ state, |first horizon state - second horizon state| = 0 := by
    apply le_antisymm
    · simpa only [hInitial, sub_self, abs_zero, Finset.sum_const_zero] using hBound
    · exact Finset.sum_nonneg fun _state _hState ↦ abs_nonneg _
  funext state
  exact sub_eq_zero.mp (abs_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun point _hPoint ↦ abs_nonneg
      (first horizon point - second horizon point))).mp hSumZero state (Finset.mem_univ state)))

end

end FiniteMarkovProcesses.Probability
