/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteIIDIntegratedL1Concentration
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Exponential control of integrated IID coordinate deviations

Jensen's inequality averages over physical time and finitely many observed coordinates.
Independence is used only across the sampled histories. Both signed centered exponential
moments control the absolute deviation, retaining the factor two.

## Main results

* `exp_integrated_abs_sum_le`: normalized time and finite-coordinate Jensen inequality.
* `measure_finiteIIDIntegratedL1Deviation_ge_le_exponential`: finite-sample Chernoff bound.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

universe u v w

variable {Sample : Type u} {Time : Type v} {Coordinate : Type w}
  [MeasurableSpace Sample] [MeasurableSpace Time] [Fintype Coordinate] [Nonempty Coordinate]

omit [MeasurableSpace Sample] in
/-- Jensen bounds the exponential of an integrated coordinatewise absolute sum by the
average of the coordinate exponentials. The normalization is the actual time mass times
the coordinate cardinality. -/
theorem exp_integrated_abs_sum_le
    (timeLaw : Measure Time) [IsFiniteMeasure timeLaw]
    (hMass : 0 < timeLaw.real univ) (function : Coordinate → Time → ℝ) (weight : ℝ)
    (hFunction : ∀ coordinate, Integrable (function coordinate) timeLaw)
    (hExp : ∀ coordinate,
      Integrable (fun time ↦ Real.exp (weight * |function coordinate time|)) timeLaw) :
    Real.exp (weight / (timeLaw.real univ * (Fintype.card Coordinate : ℝ)) *
        ∫ time, ∑ coordinate, |function coordinate time| ∂timeLaw) ≤
      (∫ time, ∑ coordinate, Real.exp (weight * |function coordinate time|) ∂timeLaw) /
        (timeLaw.real univ * (Fintype.card Coordinate : ℝ)) := by
  classical
  let dimension : ℝ := Fintype.card Coordinate
  have hDimension : 0 < dimension := by
    dsimp [dimension]
    exact_mod_cast (Fintype.card_pos (α := Coordinate))
  let : NeZero timeLaw := ⟨fun hZero ↦ by simp [hZero] at hMass⟩
  have hFinite (time : Time) :
      Real.exp (weight / dimension * ∑ coordinate, |function coordinate time|) ≤
        (∑ coordinate, Real.exp (weight * |function coordinate time|)) / dimension := by
    have hJensen := convexOn_exp.map_sum_le (t := Finset.univ)
      (w := fun _ : Coordinate ↦ dimension⁻¹)
      (p := fun coordinate ↦ weight * |function coordinate time|)
      (fun _ _ ↦ inv_nonneg.mpr hDimension.le)
      (by simp [dimension, Fintype.card_ne_zero]) (fun _ _ ↦ mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum] at hJensen
    convert hJensen using 1 <;> congr 1 <;> ring
  have hSum : Integrable (fun time ↦ ∑ coordinate, |function coordinate time|) timeLaw :=
    integrable_finsetSum _ (fun coordinate _ ↦ (hFunction coordinate).abs)
  have hExpSum : Integrable
      (fun time ↦ ∑ coordinate, Real.exp (weight * |function coordinate time|)) timeLaw :=
    integrable_finsetSum _ (fun coordinate _ ↦ hExp coordinate)
  have hScaled : Integrable
      (fun time ↦ weight / dimension * ∑ coordinate, |function coordinate time|) timeLaw :=
    hSum.const_mul _
  have hExpScaled : Integrable
      (fun time ↦ Real.exp (weight / dimension * ∑ coordinate, |function coordinate time|))
      timeLaw := by
    refine (hExpSum.div_const dimension).mono'
      (Real.continuous_exp.comp_aestronglyMeasurable hScaled.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun time ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hFinite time
  have hJensen := convexOn_exp.map_average_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ ↦ mem_univ _) hScaled hExpScaled
  simp only [average_eq, smul_eq_mul, integral_const_mul] at hJensen
  have hIntegral := integral_mono hExpScaled (hExpSum.div_const dimension) hFinite
  rw [integral_div] at hIntegral
  have hFinal := hJensen.trans
    (mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr hMass.le))
  convert hFinal using 1 <;> congr 1 <;> dsimp [dimension] <;> ring

omit [MeasurableSpace Time] [Fintype Coordinate] [Nonempty Coordinate] in
/-- Independent coordinates of the sample product tensorize one signed centered moment.
The coordinate observations are centered at the original one-history expectation. -/
theorem integral_exp_sum_centered_iid_le
    (law : Measure Sample) [IsProbabilityMeasure law] (successorIndex : ℕ)
    (observable : Sample → ℝ) (hMeasurable : Measurable observable) (tilt bound : ℝ)
    (hExp : Integrable (fun sample ↦ Real.exp
      (tilt * (observable sample - ∫ point, observable point ∂law))) law)
    (hBound : mgf (fun sample ↦ observable sample - ∫ point, observable point ∂law) law tilt ≤
      Real.exp bound) :
    Integrable (fun samples : Fin (successorIndex + 1) → Sample ↦ Real.exp
      (tilt * ∑ replica, (observable (samples replica) - ∫ point, observable point ∂law)))
      (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law) ∧
    (∫ samples : Fin (successorIndex + 1) → Sample, Real.exp
      (tilt * ∑ replica, (observable (samples replica) - ∫ point, observable point ∂law))
      ∂Measure.pi (fun _ : Fin (successorIndex + 1) ↦ law)) ≤
        Real.exp ((successorIndex + 1 : ℝ) * bound) := by
  classical
  let centered := fun sample ↦ observable sample - ∫ point, observable point ∂law
  let replicas := fun replica : Fin (successorIndex + 1) ↦
    fun samples : Fin (successorIndex + 1) → Sample ↦ centered (samples replica)
  let productLaw := Measure.pi fun _ : Fin (successorIndex + 1) ↦ law
  have hCentered : Measurable centered := hMeasurable.sub measurable_const
  have hIndependent : iIndepFun replicas productLaw := iIndepFun_pi (fun _ ↦ hCentered.aemeasurable)
  have hReplica (replica : Fin (successorIndex + 1)) : Measurable (replicas replica) :=
    hCentered.comp (measurable_pi_apply replica)
  have hMap (replica : Fin (successorIndex + 1)) :
      Measure.map (Function.eval replica) productLaw = law :=
    (measurePreserving_eval _ replica).map_eq
  have hInt (replica : Fin (successorIndex + 1)) :
      Integrable (fun samples ↦ Real.exp (tilt * replicas replica samples)) productLaw := by
    have h : Integrable (fun sample ↦ Real.exp (tilt * centered sample))
        (Measure.map (Function.eval replica) productLaw) := by
      rw [hMap replica]
      exact hExp
    exact (integrable_map_measure h.1 (measurable_pi_apply replica).aemeasurable).mp h
  constructor
  · simpa only [Finset.sum_apply] using
      hIndependent.integrable_exp_mul_sum hReplica (s := Finset.univ) (fun replica _ ↦ hInt replica)
  have hMoment (replica : Fin (successorIndex + 1)) :
      mgf (replicas replica) productLaw tilt = mgf centered law tilt := by
    unfold mgf
    rw [← hMap replica, integral_map (measurable_pi_apply replica).aemeasurable
      (by exact (hCentered.const_mul tilt).exp.aestronglyMeasurable)]
  have hProduct := hIndependent.mgf_sum hReplica Finset.univ (t := tilt)
  simp only [hMoment, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hProduct
  calc
    _ = (mgf centered law tilt) ^ (successorIndex + 1) := by
      simpa only [mgf, Finset.sum_apply] using hProduct
    _ ≤ (Real.exp bound) ^ (successorIndex + 1) :=
      pow_le_pow_left₀ mgf_nonneg hBound _
    _ = Real.exp ((successorIndex + 1 : ℝ) * bound) := by
      rw [show (successorIndex + 1 : ℝ) = ((successorIndex + 1 : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul]

/-- Both signed exponential moments control the absolute argument with prefactor two. -/
theorem exp_abs_le_exp_add_exp_neg (value : ℝ) :
    Real.exp |value| ≤ Real.exp value + Real.exp (-value) := by
  rcases le_total 0 value with hValue | hValue
  · rw [abs_of_nonneg hValue]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hValue]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- Joint exponential integrability follows from measurable sections and a uniform bound on
their actual exponential moments. No independence across time is assumed. -/
theorem integrable_exp_of_uniform_integral_bound
    (law : Measure Sample) [IsProbabilityMeasure law]
    (timeLaw : Measure Time) [IsFiniteMeasure timeLaw]
    (function : Sample × Time → ℝ)
    (hMeasurable : AEStronglyMeasurable function (law.prod timeLaw))
    (hPoint : ∀ time, Integrable (fun sample ↦ Real.exp (function (sample, time))) law)
    (bound : ℝ) (hBound : ∀ time, (∫ sample, Real.exp (function (sample, time)) ∂law) ≤ bound) :
    Integrable (fun data ↦ Real.exp (function data)) (law.prod timeLaw) := by
  have hExpMeasurable := Real.continuous_exp.comp_aestronglyMeasurable hMeasurable
  apply (integrable_prod_iff' hExpMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hPoint, ?_⟩
  apply Integrable.of_bound
    (hExpMeasurable.norm.prod_swap.integral_prod_right') bound
  filter_upwards [] with time
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [abs_of_nonneg (integral_nonneg fun _ ↦ Real.exp_nonneg _)]
  exact hBound time

/-- Uniform fixed-time coordinate exponential moments bound the exponential of the complete
integrated absolute-coordinate statistic. Joint integrability is retained explicitly. -/
theorem integral_exp_integrated_abs_sum_le
    (law : Measure Sample) [IsProbabilityMeasure law]
    (timeLaw : Measure Time) [IsFiniteMeasure timeLaw]
    (hMass : 0 < timeLaw.real univ)
    (function : Coordinate → Sample → Time → ℝ) (weight bound : ℝ)
    (hFunction : ∀ coordinate,
      Integrable (fun data : Sample × Time ↦ function coordinate data.1 data.2)
        (law.prod timeLaw))
    (hExp : ∀ coordinate,
      Integrable (fun data : Sample × Time ↦ Real.exp (weight *
        |function coordinate data.1 data.2|)) (law.prod timeLaw))
    (hBound : ∀ coordinate time,
      (∫ sample, Real.exp (weight * |function coordinate sample time|) ∂law) ≤ bound) :
    Integrable (fun sample ↦ Real.exp
      (weight / (timeLaw.real univ * (Fintype.card Coordinate : ℝ)) *
        ∫ time, ∑ coordinate, |function coordinate sample time| ∂timeLaw)) law ∧
    (∫ sample, Real.exp (weight / (timeLaw.real univ * (Fintype.card Coordinate : ℝ)) *
      ∫ time, ∑ coordinate, |function coordinate sample time| ∂timeLaw) ∂law) ≤ bound := by
  classical
  let mass : ℝ := timeLaw.real univ * (Fintype.card Coordinate : ℝ)
  have hMassPos : 0 < mass :=
    mul_pos hMass (by exact_mod_cast (Fintype.card_pos (α := Coordinate)))
  have hSum : Integrable
      (fun data : Sample × Time ↦ ∑ coordinate, |function coordinate data.1 data.2|)
      (law.prod timeLaw) :=
    integrable_finsetSum _ (fun coordinate _ ↦ (hFunction coordinate).abs)
  have hExpSum : Integrable (fun data : Sample × Time ↦
      ∑ coordinate, Real.exp (weight * |function coordinate data.1 data.2|))
      (law.prod timeLaw) :=
    integrable_finsetSum _ (fun coordinate _ ↦ hExp coordinate)
  have hDom : ∀ᵐ sample ∂law,
      Real.exp (weight / mass *
        ∫ time, ∑ coordinate, |function coordinate sample time| ∂timeLaw) ≤
      (∫ time, ∑ coordinate, Real.exp (weight * |function coordinate sample time|) ∂timeLaw) /
        mass := by
    have hSections := (ae_all_iff.mpr fun coordinate ↦ (hFunction coordinate).prod_right_ae)
    have hExpSections := (ae_all_iff.mpr fun coordinate ↦ (hExp coordinate).prod_right_ae)
    filter_upwards [hSections, hExpSections] with sample hSample hExpSample
    exact exp_integrated_abs_sum_le timeLaw hMass
      (fun coordinate time ↦ function coordinate sample time) weight hSample hExpSample
  have hIntegralExp : Integrable (fun sample ↦
      (∫ time, ∑ coordinate, Real.exp (weight * |function coordinate sample time|) ∂timeLaw) /
        mass) law := hExpSum.integral_prod_left.div_const mass
  have hExpIntegral : Integrable (fun sample ↦ Real.exp (weight / mass *
      ∫ time, ∑ coordinate, |function coordinate sample time| ∂timeLaw)) law := by
    refine hIntegralExp.mono'
      (Real.continuous_exp.comp_aestronglyMeasurable
        ((hSum.integral_prod_left.const_mul (weight / mass)).aestronglyMeasurable)) ?_
    filter_upwards [hDom] with sample hSample
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hSample
  refine ⟨hExpIntegral, (integral_mono_ae hExpIntegral hIntegralExp hDom).trans ?_⟩
  rw [integral_div, ← integral_prod _ hExpSum,
    integral_finsetSum Finset.univ (fun coordinate _ ↦ hExp coordinate)]
  apply (div_le_iff₀ hMassPos).mpr
  calc
    _ ≤ ∑ _coordinate : Coordinate, timeLaw.real univ * bound := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [integral_prod _ (hExp coordinate), integral_integral_swap (hExp coordinate)]
      calc
        _ ≤ ∫ _time : Time, bound ∂timeLaw :=
          integral_mono (hExp coordinate).integral_prod_right
            (integrable_const _) (hBound coordinate)
        _ = _ := by rw [integral_const, smul_eq_mul]
    _ = bound * mass := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [mass]
      ring

omit [MeasurableSpace Time] [Fintype Coordinate] [Nonempty Coordinate] in
/-- Two signed centered one-history bounds give the fixed-time absolute empirical bound. -/
theorem integral_exp_abs_finiteIIDCoordinateDeviation_le
    (law : Measure Sample) [IsProbabilityMeasure law] (successorIndex : ℕ)
    (observable : Coordinate → Time → Sample → ℝ) (coordinate : Coordinate) (time : Time)
    (hMeasurable : Measurable (observable coordinate time))
    (tilt budget : ℝ) (hTilt : 0 ≤ tilt)
    (hMoment : ∀ sign : ℝ, |sign| = tilt →
      Integrable (fun sample ↦ Real.exp (sign * (observable coordinate time sample -
        ∫ point, observable coordinate time point ∂law))) law ∧
      mgf (fun sample ↦ observable coordinate time sample -
        ∫ point, observable coordinate time point ∂law) law sign ≤ Real.exp budget) :
    Integrable (fun samples ↦ Real.exp ((successorIndex + 1 : ℝ) * tilt *
      |finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time|))
      (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law) ∧
    (∫ samples, Real.exp ((successorIndex + 1 : ℝ) * tilt *
      |finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time|)
      ∂Measure.pi (fun _ : Fin (successorIndex + 1) ↦ law)) ≤
        2 * Real.exp ((successorIndex + 1 : ℝ) * budget) := by
  classical
  let centeredSum := fun samples : Fin (successorIndex + 1) → Sample ↦
    ∑ replica, (observable coordinate time (samples replica) -
      ∫ point, observable coordinate time point ∂law)
  have hPositive := integral_exp_sum_centered_iid_le law successorIndex
    (observable coordinate time) hMeasurable tilt budget
    (hMoment tilt (abs_of_nonneg hTilt)).1 (hMoment tilt (abs_of_nonneg hTilt)).2
  have hNegative := integral_exp_sum_centered_iid_le law successorIndex
    (observable coordinate time) hMeasurable (-tilt) budget
    (hMoment (-tilt) (by rw [abs_neg, abs_of_nonneg hTilt])).1
    (hMoment (-tilt) (by rw [abs_neg, abs_of_nonneg hTilt])).2
  have hCount : (successorIndex + 1 : ℝ) ≠ 0 := by positivity
  have hSum (samples : Fin (successorIndex + 1) → Sample) :
      (successorIndex + 1 : ℝ) *
          finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time =
        centeredSum samples := by
    simp only [finiteIIDCoordinateDeviation, centeredSum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hValue (samples : Fin (successorIndex + 1) → Sample) :
      (successorIndex + 1 : ℝ) * tilt *
          |finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time| =
        |tilt * centeredSum samples| := by
    rw [← hSum]
    simp only [abs_mul, abs_of_nonneg hTilt,
      abs_of_pos (show (0 : ℝ) < successorIndex + 1 by positivity)]
    ring
  have hDom (samples : Fin (successorIndex + 1) → Sample) :
      Real.exp ((successorIndex + 1 : ℝ) * tilt *
        |finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time|) ≤
      Real.exp (tilt * centeredSum samples) + Real.exp (-tilt * centeredSum samples) := by
    rw [hValue]
    simpa only [neg_mul] using exp_abs_le_exp_add_exp_neg (tilt * centeredSum samples)
  have hCoordinate : Measurable
      (fun samples ↦ finiteIIDCoordinateDeviation
        law successorIndex observable coordinate samples time) := by
    unfold finiteIIDCoordinateDeviation
    fun_prop
  have hAdd : Integrable (fun samples ↦ Real.exp (tilt * centeredSum samples) +
      Real.exp (-tilt * centeredSum samples))
      (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law) := hPositive.1.add hNegative.1
  have hIntegral : Integrable (fun samples ↦ Real.exp ((successorIndex + 1 : ℝ) * tilt *
      |finiteIIDCoordinateDeviation law successorIndex observable coordinate samples time|))
      (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law) :=
    hAdd.mono' (by fun_prop)
      (Filter.Eventually.of_forall fun samples ↦ by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hDom samples)
  refine ⟨hIntegral, ?_⟩
  have hCompare := integral_mono hIntegral hAdd hDom
  rw [integral_add hPositive.1 hNegative.1] at hCompare
  linarith [hPositive.2, hNegative.2]

/-- A direct all-particle-count exponential bound for the original integrated IID statistic.
The hypotheses are joint second moments and two actual centered exponential moments; every
exponential integrability requirement for time averaging follows from these hypotheses. -/
theorem measure_finiteIIDIntegratedL1Deviation_ge_le_exponential
    (law : Measure Sample) [IsProbabilityMeasure law]
    (timeLaw : Measure Time) [IsFiniteMeasure timeLaw]
    (hMass : 0 < timeLaw.real univ) (successorIndex : ℕ)
    (observable : Coordinate → Time → Sample → ℝ)
    (hMeasurable : ∀ coordinate time, Measurable (observable coordinate time))
    (hJoint : ∀ coordinate, MemLp
      (fun data : Sample × Time ↦ observable coordinate data.2 data.1) 2 (law.prod timeLaw))
    (hMean : ∀ coordinate, MemLp
      (fun time ↦ ∫ sample, observable coordinate time sample ∂law) 2 timeLaw)
    (tilt budget : ℝ) (hTilt : 0 ≤ tilt)
    (hMoment : ∀ coordinate time sign, |sign| = tilt →
      Integrable (fun sample ↦ Real.exp (sign * (observable coordinate time sample -
        ∫ point, observable coordinate time point ∂law))) law ∧
      mgf (fun sample ↦ observable coordinate time sample -
        ∫ point, observable coordinate time point ∂law) law sign ≤ Real.exp budget)
    (radius : ℝ) :
    (Measure.pi fun _ : Fin (successorIndex + 1) ↦ law)
      {samples | radius ≤
        finiteIIDIntegratedL1Deviation law timeLaw successorIndex observable samples} ≤
      ENNReal.ofReal (2 * Real.exp ((successorIndex + 1 : ℝ) * budget -
        (successorIndex + 1 : ℝ) * tilt * radius /
          (timeLaw.real univ * (Fintype.card Coordinate : ℝ)))) := by
  let productLaw := Measure.pi fun _ : Fin (successorIndex + 1) ↦ law
  let coordinateDeviation := finiteIIDCoordinateDeviation law successorIndex observable
  let weight := (successorIndex + 1 : ℝ) * tilt
  let exponent := weight / (timeLaw.real univ * (Fintype.card Coordinate : ℝ))
  let bound := 2 * Real.exp ((successorIndex + 1 : ℝ) * budget)
  have hCoordinate (coordinate : Coordinate) :=
    memLp_finiteIIDCoordinateDeviation law timeLaw successorIndex observable hJoint hMean coordinate
  have hFixed (coordinate : Coordinate) (time : Time) :=
    integral_exp_abs_finiteIIDCoordinateDeviation_le law successorIndex observable coordinate time
      (hMeasurable coordinate time) tilt budget hTilt (hMoment coordinate time)
  have hExpJoint (coordinate : Coordinate) : Integrable (fun data ↦ Real.exp
      (weight * |coordinateDeviation coordinate data.1 data.2|)) (productLaw.prod timeLaw) := by
    apply integrable_exp_of_uniform_integral_bound productLaw timeLaw
      (fun data ↦ weight * |coordinateDeviation coordinate data.1 data.2|)
      (by simpa only [Real.norm_eq_abs] using
        (hCoordinate coordinate).aestronglyMeasurable.norm.const_mul weight)
      (fun time ↦ (hFixed coordinate time).1) bound (fun time ↦ (hFixed coordinate time).2)
  have hIntegrated := integral_exp_integrated_abs_sum_le productLaw timeLaw hMass
    coordinateDeviation weight bound
    (fun coordinate ↦ (hCoordinate coordinate).integrable one_le_two) hExpJoint
    (fun coordinate time ↦ (hFixed coordinate time).2)
  have hChernoff := measure_ge_le_exp_mul_mgf
    (μ := productLaw) (X := finiteIIDIntegratedL1Deviation law timeLaw successorIndex observable)
    (t := exponent) radius (by dsimp [exponent, weight]; positivity) hIntegrated.1
  rw [← ENNReal.ofReal_toReal (measure_ne_top productLaw _)]
  apply ENNReal.ofReal_le_ofReal
  change productLaw.real _ ≤ _
  calc
    _ ≤ Real.exp (-exponent * radius) * bound :=
      hChernoff.trans (mul_le_mul_of_nonneg_left hIntegrated.2 (Real.exp_nonneg _))
    _ = _ := by
      dsimp [bound, exponent, weight]
      rw [mul_left_comm _ 2, ← Real.exp_add]
      congr 2
      ring

end

end FiniteMarkovProcesses.Probability
