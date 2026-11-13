/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousAbsoluteValue
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Dissipation

/-!
# Finite-state endpoint L1 stability

This module integrates a finite family of almost-everywhere coordinate derivatives through the
absolute-value Kato bridge.  A pointwise sign-paired derivative bound therefore controls the exact
change in endpoint `L1` norm with no Gronwall constant.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State]

/-- A pointwise sign-paired derivative bound integrates to an exact finite-state endpoint `L1`
bound. -/
theorem finite_sum_abs_sub_le_intervalIntegral_of_ae_hasDerivAt
    {error derivative : ℝ → State → ℝ} {lower upper : ℝ}
    (hBounds : lower ≤ upper)
    (hContinuous : ∀ state,
      AbsolutelyContinuousOnInterval (fun time ↦ error time state) lower upper)
    (hDerivative : ∀ state,
      ∀ᵐ time ∂volume.restrict (Ioo lower upper),
        HasDerivAt (fun horizon ↦ error horizon state)
          (derivative time state) time)
    (bound : ℝ → ℝ) (hBoundIntegrable : IntervalIntegrable bound volume lower upper)
    (hDerivativeBound :
      ∀ᵐ time ∂volume.restrict (Ioo lower upper),
        (∑ state, Real.sign (error time state) * derivative time state) ≤ bound time) :
    (∑ state, |error upper state|) - ∑ state, |error lower state| ≤
      ∫ time in lower..upper, bound time := by
  have hAbsContinuous (state : State) :
      AbsolutelyContinuousOnInterval (fun time ↦ |error time state|) lower upper :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.abs (hContinuous state)
  have hAbsDerivative (state : State) :
      ∀ᵐ time ∂volume.restrict (Ioo lower upper),
        HasDerivAt (fun horizon ↦ |error horizon state|)
          (Real.sign (error time state) * derivative time state) time :=
    ae_hasDerivAt_abs_of_ae_hasDerivAt
      (volume.restrict (Ioo lower upper)) (hDerivative state)
  have hDerivativeEquality (state : State) :
      ∀ᵐ time ∂volume.restrict (Ioo lower upper),
        deriv (fun horizon ↦ |error horizon state|) time =
          Real.sign (error time state) * derivative time state :=
    (hAbsDerivative state).mono fun _time hAt ↦ hAt.deriv
  have hSignedIntegrable (state : State) :
      IntervalIntegrable
        (fun time ↦ Real.sign (error time state) * derivative time state)
        volume lower upper := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hBounds]
    have hAbsDerivativeIntegrable :
        IntegrableOn (deriv (fun horizon ↦ |error horizon state|))
          (Ioo lower upper) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hBounds]
      exact (hAbsContinuous state).intervalIntegrable_deriv
    exact hAbsDerivativeIntegrable.congr_fun_ae (hDerivativeEquality state)
  have hCoordinateIdentity (state : State) :
      |error upper state| - |error lower state| =
        ∫ time in lower..upper,
          Real.sign (error time state) * derivative time state := by
    calc
      |error upper state| - |error lower state| =
          ∫ time in lower..upper,
            deriv (fun horizon ↦ |error horizon state|) time :=
        (FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
          (hAbsContinuous state)).symm
      _ = ∫ time in lower..upper,
          Real.sign (error time state) * derivative time state := by
        rw [intervalIntegral.integral_of_le hBounds,
          integral_Ioc_eq_integral_Ioo,
          intervalIntegral.integral_of_le hBounds,
          integral_Ioc_eq_integral_Ioo]
        exact integral_congr_ae (hDerivativeEquality state)
  have hSignedSumIntegrable : IntervalIntegrable
      (fun time ↦ ∑ state, Real.sign (error time state) * derivative time state)
      volume lower upper := by
      refine (IntervalIntegrable.sum Finset.univ fun state _hState ↦
        hSignedIntegrable state).congr ?_
      intro time _hTime
      simp
  calc
    (∑ state, |error upper state|) - ∑ state, |error lower state| =
        ∑ state, (|error upper state| - |error lower state|) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ state, ∫ time in lower..upper,
        Real.sign (error time state) * derivative time state := by
      apply Finset.sum_congr rfl
      intro state _hState
      exact hCoordinateIdentity state
    _ = ∫ time in lower..upper,
        ∑ state, Real.sign (error time state) * derivative time state := by
      rw [intervalIntegral.integral_finsetSum]
      exact fun state _hState ↦ hSignedIntegrable state
    _ ≤ ∫ time in lower..upper, bound time := by
      rw [intervalIntegral.integral_of_le hBounds,
        integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le hBounds,
        integral_Ioc_eq_integral_Ioo]
      exact integral_mono_ae
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hBounds).mp hSignedSumIntegrable)
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hBounds).mp hBoundIntegrable)
        hDerivativeBound

end

end FiniteMarkovProcesses.Probability
