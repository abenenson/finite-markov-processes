/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite-particle concentration of integrated IID coordinate deviations

Finite-coordinate and time Cauchy-Schwarz estimates turn the variance of independent empirical
means into an explicit second-moment bound for their integrated coordinatewise absolute error.
The observations, their true means, and joint second-moment premises are retained explicitly.

## Main results

* `integral_sq_finiteIIDCoordinateDeviation_le`: fixed-time variance control.
* `measure_finiteIIDIntegratedL1Deviation_ge_le`: an all-particle-count polynomial tail bound.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

universe u v w

variable {Sample : Type u} {Time : Type v} {Coordinate : Type w}
  [MeasurableSpace Sample] [MeasurableSpace Time] [Fintype Coordinate]

/-- One centered empirical coordinate, with literal positive particle count `successorIndex+1`.
The center is the expectation under the original one-particle probability law. -/
def finiteIIDCoordinateDeviation (μ : Measure Sample) (successorIndex : ℕ)
    (observable : Coordinate → Time → Sample → ℝ) (coordinate : Coordinate)
    (samples : Fin (successorIndex + 1) → Sample) (time : Time) : ℝ :=
  (∑ replica, observable coordinate time (samples replica)) / (successorIndex + 1 : ℝ) -
    ∫ sample, observable coordinate time sample ∂μ

/-- Integrated coordinatewise absolute deviation of the empirical mean from its true source mean.
No conditional initial configuration or replacement observation is introduced. -/
def finiteIIDIntegratedL1Deviation (μ : Measure Sample) (ν : Measure Time)
    (successorIndex : ℕ) (observable : Coordinate → Time → Sample → ℝ)
    (samples : Fin (successorIndex + 1) → Sample) : ℝ :=
  ∫ time, ∑ coordinate,
    |finiteIIDCoordinateDeviation μ successorIndex observable coordinate samples time| ∂ν

omit [Fintype Coordinate] in
/-- One-history joint second moments and square-integrable true means give joint second moments
of every centered empirical coordinate under the actual IID product law. -/
theorem memLp_finiteIIDCoordinateDeviation
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (ν : Measure Time) [IsFiniteMeasure ν]
    (successorIndex : ℕ) (observable : Coordinate → Time → Sample → ℝ)
    (hJoint : ∀ coordinate, MemLp
      (fun data : Sample × Time ↦ observable coordinate data.2 data.1) 2 (μ.prod ν))
    (hMean : ∀ coordinate, MemLp
      (fun time ↦ ∫ sample, observable coordinate time sample ∂μ) 2 ν)
    (coordinate : Coordinate) :
    MemLp (fun data : (Fin (successorIndex + 1) → Sample) × Time ↦
      finiteIIDCoordinateDeviation μ successorIndex observable coordinate data.1 data.2)
      2 ((Measure.pi fun _ : Fin (successorIndex + 1) ↦ μ).prod ν) := by
  have hReplica (replica : Fin (successorIndex + 1)) :
      MemLp (fun data : (Fin (successorIndex + 1) → Sample) × Time ↦
        observable coordinate data.2 (data.1 replica)) 2
        ((Measure.pi fun _ : Fin (successorIndex + 1) ↦ μ).prod ν) := by
    exact (hJoint coordinate).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin (successorIndex + 1) ↦ μ) replica).prod
        (MeasurePreserving.id ν))
  refine MemLp.ae_eq ?_ (((memLp_finsetSum Finset.univ fun replica _ ↦ hReplica replica).mul_const
    (successorIndex + 1 : ℝ)⁻¹).sub ((hMean coordinate).comp_snd _))
  filter_upwards [] with data
  simp only [finiteIIDCoordinateDeviation, Pi.sub_apply, div_eq_mul_inv]

omit [MeasurableSpace Time] [Fintype Coordinate] in
/-- At any fixed time the centered IID empirical coordinate has second moment bounded by its
one-history variance budget divided by the positive particle count. -/
theorem integral_sq_finiteIIDCoordinateDeviation_le
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (successorIndex : ℕ) (observable : Coordinate → Time → Sample → ℝ)
    (coordinate : Coordinate) (time : Time)
    (hPoint : MemLp (observable coordinate time) 2 μ)
    (varianceBound : ℝ)
    (hVariance : variance (observable coordinate time) μ ≤ varianceBound) :
    (∫ samples,
      (finiteIIDCoordinateDeviation μ successorIndex observable coordinate samples time) ^ 2
        ∂Measure.pi (fun _ : Fin (successorIndex + 1) ↦ μ)) ≤
      varianceBound / (successorIndex + 1 : ℝ) := by
  let law := Measure.pi fun _ : Fin (successorIndex + 1) ↦ μ
  let average : (Fin (successorIndex + 1) → Sample) → ℝ := fun samples ↦
    (∑ replica, observable coordinate time (samples replica)) / (successorIndex + 1 : ℝ)
  have hReplica (replica : Fin (successorIndex + 1)) :
      MemLp (fun samples : Fin (successorIndex + 1) → Sample ↦
        observable coordinate time (samples replica)) 2 law :=
    hPoint.comp_measurePreserving (measurePreserving_eval _ replica)
  have hAverage : MemLp average 2 law := by
    simpa only [average, div_eq_mul_inv] using
      (memLp_finsetSum Finset.univ fun replica _ ↦ hReplica replica).mul_const
        (successorIndex + 1 : ℝ)⁻¹
  have hMean : ∫ samples, average samples ∂law =
      ∫ sample, observable coordinate time sample ∂μ := by
    unfold average
    rw [integral_div, integral_finsetSum Finset.univ
      (fun replica _ ↦ (hReplica replica).integrable one_le_two)]
    have hIntegral (replica : Fin (successorIndex + 1)) :
        (∫ samples : Fin (successorIndex + 1) → Sample,
          observable coordinate time (samples replica) ∂law) =
          ∫ sample, observable coordinate time sample ∂μ := by
      have hPreserving := measurePreserving_eval
        (fun _ : Fin (successorIndex + 1) ↦ μ) replica
      have hMeasurable : AEStronglyMeasurable (observable coordinate time)
          (Measure.map (Function.eval replica) law) := by
        rw [hPreserving.map_eq]
        exact hPoint.aestronglyMeasurable
      calc
        _ = ∫ sample, observable coordinate time sample
            ∂Measure.map (Function.eval replica) law :=
          (integral_map hPreserving.aemeasurable hMeasurable).symm
        _ = _ := by rw [hPreserving.map_eq]
    simp_rw [hIntegral]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hCount : (successorIndex + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hCount]
  have hVarianceAverage : variance average law =
      variance (observable coordinate time) μ / (successorIndex + 1 : ℝ) := by
    have hAverageEq : average = fun samples ↦ (1 / (successorIndex + 1 : ℝ)) *
        (∑ replica, observable coordinate time (samples replica)) := by
      funext samples
      simp only [average, div_eq_mul_inv, one_mul, mul_comm]
    rw [hAverageEq, variance_const_mul]
    have hSumVariance : variance
        (fun samples : Fin (successorIndex + 1) → Sample ↦
          ∑ replica, observable coordinate time (samples replica)) law =
        (successorIndex + 1 : ℝ) * variance (observable coordinate time) μ := by
      have hSumEq : (∑ replica : Fin (successorIndex + 1),
          fun samples : Fin (successorIndex + 1) → Sample ↦
            observable coordinate time (samples replica)) =
          fun samples ↦ ∑ replica, observable coordinate time (samples replica) := by
        funext samples
        simp only [Finset.sum_apply]
      have hSum := variance_sum_pi (μ := fun _ : Fin (successorIndex + 1) ↦ μ)
        (X := fun _ ↦ observable coordinate time) (fun _ ↦ hPoint)
      rw [hSumEq] at hSum
      simpa only [law, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hSum
    rw [hSumVariance]
    have hCount : (successorIndex + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hCount]
  calc
    _ = variance average law := by
      rw [variance_eq_integral hAverage.aemeasurable, hMean]
      rfl
    _ ≤ varianceBound / (successorIndex + 1 : ℝ) := by
      rw [hVarianceAverage]
      exact div_le_div_of_nonneg_right hVariance (by positivity)

private theorem sq_integral_le_mass_mul_integral_sq
    (ν : Measure Time) [IsFiniteMeasure ν] {function : Time → ℝ}
    (hFunction : MemLp function 2 ν) :
    (∫ time, function time ∂ν) ^ 2 ≤
      ν.real univ * ∫ time, (function time) ^ 2 ∂ν := by
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    (μ := ν) (f := function) (g := fun _ : Time ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hFunction)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Time ↦ (1 : ℝ)) 2 ν))
  have hRoot : |∫ time, function time ∂ν| ≤
      Real.sqrt (∫ time, (function time) ^ 2 ∂ν) * Real.sqrt (ν.real univ) := by
    calc
      _ ≤ ∫ time, ‖function time‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ _ := by
        simpa only [norm_one, mul_one, Real.norm_eq_abs, Real.rpow_two, sq_abs,
          one_pow, integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using hHolder
  calc
    _ = |∫ time, function time ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ time, (function time) ^ 2 ∂ν) *
        Real.sqrt (ν.real univ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hRoot
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
        Real.sq_sqrt measureReal_nonneg]
      ring

private theorem integrated_abs_sum_secondMoment
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (ν : Measure Time) [IsFiniteMeasure ν]
    (field : Coordinate → Sample → Time → ℝ)
    (hField : ∀ coordinate, MemLp
      (fun data : Sample × Time ↦ field coordinate data.1 data.2) 2 (μ.prod ν))
    (bound : Coordinate → ℝ)
    (hBound : ∀ coordinate time,
      (∫ sample, (field coordinate sample time) ^ 2 ∂μ) ≤ bound coordinate) :
    Integrable (fun sample ↦ (∫ time, ∑ coordinate,
      |field coordinate sample time| ∂ν) ^ 2) μ ∧
    (∫ sample, (∫ time, ∑ coordinate, |field coordinate sample time| ∂ν) ^ 2 ∂μ) ≤
      (ν.real univ) ^ 2 * (Fintype.card Coordinate : ℝ) * ∑ coordinate, bound coordinate := by
  classical
  let squared : Sample × Time → ℝ := fun data ↦
    ∑ coordinate, (field coordinate data.1 data.2) ^ 2
  let integrated : Sample → ℝ := fun sample ↦ ∫ time, ∑ coordinate,
    |field coordinate sample time| ∂ν
  let energy : Sample → ℝ := fun sample ↦ ∫ time, squared (sample, time) ∂ν
  have hSquared : Integrable squared (μ.prod ν) :=
    integrable_finsetSum Finset.univ fun coordinate _ ↦ (hField coordinate).integrable_sq
  have hAbs : Integrable (fun data : Sample × Time ↦
      ∑ coordinate, |field coordinate data.1 data.2|) (μ.prod ν) := by
    apply integrable_finsetSum Finset.univ
    intro coordinate _hCoordinate
    simpa only [Real.norm_eq_abs] using ((hField coordinate).integrable one_le_two).norm
  have hIntegrated : Integrable integrated μ := hAbs.integral_prod_left
  have hEnergy : Integrable energy μ := hSquared.integral_prod_left
  have hSections : ∀ᵐ sample ∂μ, ∀ coordinate,
      MemLp (field coordinate sample) 2 ν := by
    have hFirst := ae_all_iff.mpr fun coordinate ↦
      ((hField coordinate).integrable one_le_two).prod_right_ae
    have hSecond := ae_all_iff.mpr fun coordinate ↦
      (hField coordinate).integrable_sq.prod_right_ae
    filter_upwards [hFirst, hSecond] with sample hFirst hSecond coordinate
    exact (memLp_two_iff_integrable_sq (hFirst coordinate).aestronglyMeasurable).mpr
      (hSecond coordinate)
  have hPointwise : ∀ᵐ sample ∂μ, integrated sample ^ 2 ≤
      (ν.real univ * (Fintype.card Coordinate : ℝ)) * energy sample := by
    filter_upwards [hSections] with sample hSection
    have hSum : MemLp (fun time ↦ ∑ coordinate, |field coordinate sample time|) 2 ν := by
      apply memLp_finsetSum Finset.univ
      intro coordinate _hCoordinate
      simpa only [Real.norm_eq_abs] using (hSection coordinate).norm
    have hTime := sq_integral_le_mass_mul_integral_sq ν hSum
    have hEnergySection : Integrable (fun time ↦
        ∑ coordinate, (field coordinate sample time) ^ 2) ν :=
      integrable_finsetSum Finset.univ fun coordinate _ ↦
        (hSection coordinate).integrable_sq
    have hCoordinate : (∫ time, (∑ coordinate, |field coordinate sample time|) ^ 2 ∂ν) ≤
        (Fintype.card Coordinate : ℝ) * energy sample := by
      calc
        _ ≤ ∫ time, (Fintype.card Coordinate : ℝ) *
            (∑ coordinate, (field coordinate sample time) ^ 2) ∂ν := by
          apply integral_mono hSum.integrable_sq (hEnergySection.const_mul _)
          intro time
          simpa only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_comm] using
            (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
              (fun coordinate ↦ |field coordinate sample time|) (fun _ ↦ (1 : ℝ)))
        _ = _ := integral_const_mul _ _
    exact hTime.trans <| by
      simpa only [integrated, energy, mul_assoc] using
        mul_le_mul_of_nonneg_left hCoordinate (measureReal_nonneg : 0 ≤ ν.real univ)
  have hIntegratedSquared : Integrable (fun sample ↦ integrated sample ^ 2) μ := by
    apply (hEnergy.const_mul (ν.real univ * (Fintype.card Coordinate : ℝ))).mono'
      (hIntegrated.aestronglyMeasurable.pow 2)
    filter_upwards [hPointwise] with sample hSample
    change ‖integrated sample ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (integrated sample))]
    exact hSample
  have hEnergyMean : (∫ sample, energy sample ∂μ) ≤
      ν.real univ * ∑ coordinate, bound coordinate := by
    calc
      _ = ∫ time, ∫ sample, squared (sample, time) ∂μ ∂ν :=
        integral_integral_swap hSquared
      _ ≤ ∫ _time, ∑ coordinate, bound coordinate ∂ν := by
        apply integral_mono_ae hSquared.integral_prod_right (integrable_const _)
        have hFiber := ae_all_iff.mpr fun coordinate ↦
          (hField coordinate).integrable_sq.prod_left_ae
        filter_upwards [hFiber] with time hFiber
        dsimp only [squared]
        rw [integral_finsetSum Finset.univ (fun coordinate _ ↦ hFiber coordinate)]
        exact Finset.sum_le_sum fun coordinate _ ↦ hBound coordinate time
      _ = _ := by simp only [integral_const, smul_eq_mul]
  refine ⟨hIntegratedSquared, ?_⟩
  calc
    _ ≤ ∫ sample, (ν.real univ * (Fintype.card Coordinate : ℝ)) * energy sample ∂μ :=
      integral_mono_ae hIntegratedSquared (hEnergy.const_mul _) hPointwise
    _ = (ν.real univ * (Fintype.card Coordinate : ℝ)) * ∫ sample, energy sample ∂μ :=
      integral_const_mul _ _
    _ ≤ (ν.real univ * (Fintype.card Coordinate : ℝ)) *
        (ν.real univ * ∑ coordinate, bound coordinate) :=
      mul_le_mul_of_nonneg_left hEnergyMean (by positivity)
    _ = _ := by ring

/-- The integrated absolute-coordinate deviation of actual IID empirical means has an explicit
all-particle-count tail bound from the supplied one-history variance budgets. -/
theorem measure_finiteIIDIntegratedL1Deviation_ge_le
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (ν : Measure Time) [IsFiniteMeasure ν]
    (successorIndex : ℕ) (observable : Coordinate → Time → Sample → ℝ)
    (hJoint : ∀ coordinate, MemLp
      (fun data : Sample × Time ↦ observable coordinate data.2 data.1) 2 (μ.prod ν))
    (hMean : ∀ coordinate, MemLp
      (fun time ↦ ∫ sample, observable coordinate time sample ∂μ) 2 ν)
    (hPoint : ∀ coordinate time, MemLp (observable coordinate time) 2 μ)
    (varianceBound : Coordinate → ℝ)
    (hVariance : ∀ coordinate time,
      variance (observable coordinate time) μ ≤ varianceBound coordinate)
    {radius : ℝ} (hRadius : 0 < radius) :
    (Measure.pi fun _ : Fin (successorIndex + 1) ↦ μ)
      {samples | radius ≤ finiteIIDIntegratedL1Deviation μ ν successorIndex observable samples} ≤
      ENNReal.ofReal ((ν.real univ) ^ 2 * (Fintype.card Coordinate : ℝ) *
        (∑ coordinate, varianceBound coordinate) /
          ((successorIndex + 1 : ℝ) * radius ^ 2)) := by
  let law := Measure.pi fun _ : Fin (successorIndex + 1) ↦ μ
  let deviation := finiteIIDIntegratedL1Deviation μ ν successorIndex observable
  have hSecond := integrated_abs_sum_secondMoment law ν
    (finiteIIDCoordinateDeviation μ successorIndex observable)
    (fun coordinate ↦ memLp_finiteIIDCoordinateDeviation
      μ ν successorIndex observable hJoint hMean coordinate)
    (fun coordinate ↦ varianceBound coordinate / (successorIndex + 1 : ℝ))
    (fun coordinate time ↦ integral_sq_finiteIIDCoordinateDeviation_le
      μ successorIndex observable coordinate time (hPoint coordinate time)
      (varianceBound coordinate) (hVariance coordinate time))
  have hSquared : Integrable (fun samples ↦ deviation samples ^ 2) law := hSecond.1
  have hExpectation : (∫ samples, deviation samples ^ 2 ∂law) ≤
      (ν.real univ) ^ 2 * (Fintype.card Coordinate : ℝ) *
        (∑ coordinate, varianceBound coordinate) / (successorIndex + 1 : ℝ) := by
    simpa only [deviation, finiteIIDIntegratedL1Deviation, ← Finset.sum_div,
      mul_div_assoc] using hSecond.2
  have hEvent : {samples | radius ≤ deviation samples} ⊆
      {samples | radius ^ 2 ≤ deviation samples ^ 2} := by
    intro samples hSample
    exact (sq_le_sq₀ hRadius.le (hRadius.le.trans hSample)).mpr hSample
  have hMarkov : radius ^ 2 * law.real {samples | radius ≤ deviation samples} ≤
      ∫ samples, deviation samples ^ 2 ∂law := by
    calc
      _ ≤ radius ^ 2 * law.real {samples | radius ^ 2 ≤ deviation samples ^ 2} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hEvent) (sq_nonneg radius)
      _ ≤ _ := mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun samples ↦ sq_nonneg (deviation samples))
        hSquared (radius ^ 2)
  rw [← ENNReal.ofReal_toReal (measure_ne_top law _)]
  apply ENNReal.ofReal_le_ofReal
  change law.real {samples | radius ≤ deviation samples} ≤ _
  rw [← div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hRadius)).mpr
  calc
    _ ≤ ∫ samples, deviation samples ^ 2 ∂law := by
      simpa only [mul_comm] using hMarkov
    _ ≤ _ := hExpectation

end

end FiniteMarkovProcesses.Probability
