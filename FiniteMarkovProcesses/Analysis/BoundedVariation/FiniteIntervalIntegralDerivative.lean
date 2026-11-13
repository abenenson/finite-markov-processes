/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite-interval integral derivatives

An integrable real density on the physical-time measure generates a continuous integral
primitive, a finite signed Stieltjes derivative, and a bounded-variation path.  This is the
absolutely-continuous counterpart of the finite event-step witnesses.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

/-- The physical-time volume inherits atomlessness from Lebesgue measure. -/
noncomputable instance instNoAtomsFiniteOpenIntervalVolume (duration : ℝ) :
    NullSingletonClass (finiteOpenIntervalVolume duration) := by
  unfold finiteOpenIntervalVolume
  infer_instance

/-- Continuous primitive of an integrable density on the finite physical-time measure. -/
noncomputable def finiteIntervalIntegralPrimitive
    (initialValue duration : ℝ) (derivative : ℝ → ℝ) (time : ℝ) : ℝ :=
  initialValue +
    ∫ markedTime : ℝ in 0..time, derivative markedTime
      ∂finiteOpenIntervalVolume duration

/-- An integrable physical-time density has a globally continuous finite-interval primitive. -/
theorem continuous_finiteIntervalIntegralPrimitive
    (initialValue duration : ℝ) {derivative : ℝ → ℝ}
    (hDerivative : Integrable derivative (finiteOpenIntervalVolume duration)) :
    Continuous (finiteIntervalIntegralPrimitive initialValue duration derivative) := by
  unfold finiteIntervalIntegralPrimitive
  exact continuous_const.add (hDerivative.continuous_primitive 0)

/-- The primitive increment on a physical subinterval is the corresponding density integral. -/
theorem finiteIntervalIntegralPrimitive_sub_eq_integral
    (initialValue duration : ℝ) {derivative : ℝ → ℝ}
    (hDerivative : Integrable derivative (finiteOpenIntervalVolume duration))
    {start finish : ℝ} (hOrder : start ≤ finish) :
    finiteIntervalIntegralPrimitive initialValue duration derivative finish -
        finiteIntervalIntegralPrimitive initialValue duration derivative start =
      ∫ markedTime : ℝ in Ioc start finish, derivative markedTime
        ∂finiteOpenIntervalVolume duration := by
  rw [← intervalIntegral.integral_of_le hOrder]
  have hFirst := hDerivative.intervalIntegrable (a := 0) (b := start)
  have hSecond := hDerivative.intervalIntegrable (a := start) (b := finish)
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hFirst hSecond
  unfold finiteIntervalIntegralPrimitive
  linarith

/-- Every integrable scalar density generates a bounded-variation primitive on physical time. -/
theorem boundedVariationOn_finiteIntervalIntegralPrimitive
    (initialValue duration : ℝ) {derivative : ℝ → ℝ}
    (hDerivative : Integrable derivative (finiteOpenIntervalVolume duration)) :
    BoundedVariationOn
      (finiteIntervalIntegralPrimitive initialValue duration derivative)
      (Ioo 0 duration) := by
  let positivePart : ℝ → ℝ := fun time =>
    (|derivative time| + derivative time) / 2
  let negativePart : ℝ → ℝ := fun time =>
    (|derivative time| - derivative time) / 2
  have hNorm : Integrable (fun time => |derivative time|)
      (finiteOpenIntervalVolume duration) := by
    simpa only [Real.norm_eq_abs] using hDerivative.norm
  have hPositiveIntegrable :
      Integrable positivePart (finiteOpenIntervalVolume duration) := by
    exact (hNorm.add hDerivative).div_const 2
  have hNegativeIntegrable :
      Integrable negativePart (finiteOpenIntervalVolume duration) := by
    exact (hNorm.sub hDerivative).div_const 2
  have hPositiveNonnegative (time : ℝ) : 0 ≤ positivePart time := by
    dsimp only [positivePart]
    exact div_nonneg (neg_le_iff_add_nonneg.mp (neg_le_abs (derivative time))) (by positivity)
  have hNegativeNonnegative (time : ℝ) : 0 ≤ negativePart time := by
    dsimp only [negativePart]
    exact div_nonneg (sub_nonneg.mpr (le_abs_self (derivative time))) (by positivity)
  let positivePrimitive : ℝ → ℝ := fun time =>
    initialValue +
      ∫ markedTime : ℝ in 0..time, positivePart markedTime
        ∂finiteOpenIntervalVolume duration
  let negativePrimitive : ℝ → ℝ := fun time =>
    ∫ markedTime : ℝ in 0..time, negativePart markedTime
      ∂finiteOpenIntervalVolume duration
  have hPositiveMonotone : Monotone positivePrimitive := by
    intro first second hOrder
    have hFirst := hPositiveIntegrable.intervalIntegrable (a := 0) (b := first)
    have hSecond := hPositiveIntegrable.intervalIntegrable (a := first) (b := second)
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hFirst hSecond
    have hNonnegative := intervalIntegral.integral_nonneg_of_ae
      (μ := finiteOpenIntervalVolume duration) hOrder
      (Filter.Eventually.of_forall hPositiveNonnegative)
    dsimp only [positivePrimitive]
    linarith
  have hNegativeMonotone : Monotone negativePrimitive := by
    intro first second hOrder
    have hFirst := hNegativeIntegrable.intervalIntegrable (a := 0) (b := first)
    have hSecond := hNegativeIntegrable.intervalIntegrable (a := first) (b := second)
    have hAdd := intervalIntegral.integral_add_adjacent_intervals hFirst hSecond
    have hNonnegative := intervalIntegral.integral_nonneg_of_ae
      (μ := finiteOpenIntervalVolume duration) hOrder
      (Filter.Eventually.of_forall hNegativeNonnegative)
    dsimp only [negativePrimitive]
    linarith
  have hPrimitive :
      finiteIntervalIntegralPrimitive initialValue duration derivative =
        positivePrimitive - negativePrimitive := by
    funext time
    have hPositiveInterval := hPositiveIntegrable.intervalIntegrable (a := 0) (b := time)
    have hNegativeInterval := hNegativeIntegrable.intervalIntegrable (a := 0) (b := time)
    have hIntegrand : derivative = positivePart - negativePart := by
      funext markedTime
      change derivative markedTime =
        (|derivative markedTime| + derivative markedTime) / 2 -
          (|derivative markedTime| - derivative markedTime) / 2
      ring
    rw [finiteIntervalIntegralPrimitive, hIntegrand]
    simp only [Pi.sub_apply]
    rw [intervalIntegral.integral_sub hPositiveInterval hNegativeInterval]
    dsimp only [positivePrimitive, negativePrimitive, Pi.sub_apply]
    ring
  rw [hPrimitive]
  exact FiniteIntervalBVAlgebra.boundedVariationOn_sub
    (FiniteIntervalBVAlgebra.boundedVariationOn_Ioo_of_monotone
      hPositiveMonotone 0 duration)
    (FiniteIntervalBVAlgebra.boundedVariationOn_Ioo_of_monotone
      hNegativeMonotone 0 duration)

namespace ScalarFiniteIntervalCadlagDerivativeWitness

/-- An integrable physical-time density supplies its exact continuous Stieltjes derivative
witness. -/
noncomputable def ofIntegral
    (initialValue duration : ℝ) (derivative : ℝ → ℝ)
    (hDerivative : Integrable derivative (finiteOpenIntervalVolume duration)) :
    ScalarFiniteIntervalCadlagDerivativeWitness
      (finiteIntervalIntegralPrimitive initialValue duration derivative) duration where
  modification := finiteIntervalIntegralPrimitive initialValue duration derivative
  derivative := VagueSignedMeasure.ofSignedMeasure <|
    (finiteOpenIntervalVolume duration).withDensityᵥ derivative
  derivative_restrict_openInterval := by
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    apply VectorMeasure.ext
    intro event hEvent
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioo hEvent,
      withDensityᵥ_apply hDerivative (hEvent.inter measurableSet_Ioo),
      withDensityᵥ_apply hDerivative hEvent]
    change
      (∫ time, derivative time
          ∂(finiteOpenIntervalVolume duration).restrict (event ∩ Ioo 0 duration)) =
        ∫ time, derivative time
          ∂(finiteOpenIntervalVolume duration).restrict event
    congr 1
    unfold finiteOpenIntervalVolume
    rw [Measure.restrict_restrict (hEvent.inter measurableSet_Ioo),
      Measure.restrict_restrict hEvent]
    simp only [inter_assoc, inter_self]
  eventuallyEq := Filter.Eventually.of_forall fun _ => rfl
  rightContinuous := fun time =>
    (continuous_finiteIntervalIntegralPrimitive
      initialValue duration hDerivative).continuousAt.continuousWithinAt
  hasLeftLimit := fun time =>
    ⟨finiteIntervalIntegralPrimitive initialValue duration derivative time,
      (continuous_finiteIntervalIntegralPrimitive
        initialValue duration hDerivative).continuousAt.continuousWithinAt.tendsto⟩
  derivative_Ioc := by
    intro start finish _hStart hOrder _hFinish
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      withDensityᵥ_apply hDerivative measurableSet_Ioc,
      finiteIntervalIntegralPrimitive_sub_eq_integral
        initialValue duration hDerivative hOrder]

end ScalarFiniteIntervalCadlagDerivativeWitness

end

end FiniteMarkovProcesses
