/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVLinearCombination
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureWithDensityPairing

/-!
# Hybrid convergence from vanishing difference variation

Two hybrid-BV paths with the same initial trace are close in strong `L1` and against every
interior derivative test whenever the complete derivative variation of their literal difference
is small.  This supplies a reusable convergence criterion on the exact hybrid topology.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction CompactlySupported ENNReal Topology

universe u

noncomputable section

namespace FiniteIntervalHybridBVPath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Hybrid convergence follows from a shared initial trace and vanishing complete derivative
variation of the genuine difference path. -/
theorem tendsto_of_initialTrace_eq_of_tendsto_differenceDerivativeTotalVariation
    {Index : Type*} {filter : Filter Index}
    {paths : Index → FiniteIntervalHybridBVPath Coordinate duration}
    {limit : FiniteIntervalHybridBVPath Coordinate duration}
    (hDuration : 0 < duration)
    (hInitial : ∀ index, (paths index).initialTrace = limit.initialTrace)
    (hVariation : Tendsto
      (fun index ↦ finiteIntervalHybridBVDerivativeTotalVariation
        (linearCombination 1 (-1) (paths index) limit))
      filter (𝓝 0)) :
    Tendsto paths filter (𝓝 limit) := by
  rw [FiniteIntervalHybridBVPath.tendsto_iff]
  constructor
  · rw [tendsto_iff_edist_tendsto_0]
    have hUpper : Tendsto
        (fun index ↦ ENNReal.ofReal duration *
          finiteIntervalHybridBVDerivativeTotalVariation
            (linearCombination 1 (-1) (paths index) limit))
        filter (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hVariation (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
    · exact Filter.Eventually.of_forall fun _index ↦ zero_le
    · exact Filter.Eventually.of_forall fun index ↦ by
        let difference := linearCombination 1 (-1) (paths index) limit
        have hDifferenceInitial : difference.initialTrace = 0 := by
          rw [show difference = linearCombination 1 (-1) (paths index) limit by rfl,
            linearCombination_initialTrace 1 (-1) (paths index) limit hDuration,
            hInitial index]
          simp
        rw [edist_eq_enorm_sub]
        have hDifferenceL1 :
            difference.toDerivativePath.toL1Path =
              (paths index).toDerivativePath.toL1Path -
                limit.toDerivativePath.toL1Path := by
          rw [show difference = linearCombination 1 (-1) (paths index) limit by rfl,
            linearCombination_toL1Path]
          simp [sub_eq_add_neg]
        rw [← hDifferenceL1]
        exact
          (enorm_toL1Path_le_duration_mul_initialTrace_add_derivativeTotalVariation
            difference).trans_eq <| by simp [hDifferenceInitial, difference]
  · intro coordinate test
    rw [← tendsto_sub_nhds_zero_iff]
    let boundedTest : ℝ →ᵇ ℝ :=
      ofCompactSupport test.1 test.1.continuous test.1.hasCompactSupport
    have hUpper : Tendsto
        (fun index ↦ ‖boundedTest‖ *
          (finiteIntervalHybridBVDerivativeTotalVariation
            (linearCombination 1 (-1) (paths index) limit)).toReal)
        filter (𝓝 0) := by
      have hToReal : Tendsto
          (fun index ↦ (finiteIntervalHybridBVDerivativeTotalVariation
            (linearCombination 1 (-1) (paths index) limit)).toReal)
          filter (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hVariation
      simpa only [mul_zero] using
        (show Tendsto (fun _index : Index ↦ ‖boundedTest‖) filter (𝓝 ‖boundedTest‖) from
          tendsto_const_nhds).mul hToReal
    have hFiniteEventually : ∀ᶠ index in filter,
        finiteIntervalHybridBVDerivativeTotalVariation
          (linearCombination 1 (-1) (paths index) limit) < 1 :=
      hVariation.eventually (Iio_mem_nhds zero_lt_one)
    rw [Metric.tendsto_nhds]
    intro tolerance hTolerance
    filter_upwards [hUpper.eventually (Iio_mem_nhds hTolerance), hFiniteEventually] with
      index hIndex hFinite
    let difference := linearCombination 1 (-1) (paths index) limit
    have hFormula :
        (difference.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 =
          ((paths index).toDerivativePath.derivative coordinate).continuousTestIntegral test.1 -
            (limit.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 := by
      rw [show difference = linearCombination 1 (-1) (paths index) limit by rfl,
        linearCombination_derivative]
      calc
        _ = VagueSignedMeasure.continuousTestIntegral
              (VagueSignedMeasure.ofSignedMeasure
                ((1 : ℝ) •
                  ((paths index).toDerivativePath.derivative coordinate).toSignedMeasure))
              test.1 +
            VagueSignedMeasure.continuousTestIntegral
              (VagueSignedMeasure.ofSignedMeasure
                ((-1 : ℝ) •
                  (limit.toDerivativePath.derivative coordinate).toSignedMeasure))
              test.1 := by
          simpa only [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure] using
            VagueSignedMeasure.continuousTestIntegral_add
              (VagueSignedMeasure.ofSignedMeasure
                ((1 : ℝ) •
                  ((paths index).toDerivativePath.derivative coordinate).toSignedMeasure))
              (VagueSignedMeasure.ofSignedMeasure
                ((-1 : ℝ) •
                  (limit.toDerivativePath.derivative coordinate).toSignedMeasure)) test.1
        _ = _ := by
          rw [VagueSignedMeasure.continuousTestIntegral_smul,
            VagueSignedMeasure.continuousTestIntegral_smul]
          ring
    have hDifferenceFinite :
        finiteIntervalHybridBVDerivativeTotalVariation difference ≠ ⊤ := by
      exact ne_top_of_lt (hFinite.trans ENNReal.one_lt_top)
    rw [Real.dist_eq, sub_zero, ← hFormula]
    apply lt_of_le_of_lt ?_ hIndex
    calc
      |(difference.toDerivativePath.derivative coordinate).continuousTestIntegral test.1| ≤
          ‖boundedTest‖ *
            (difference.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation.real
              Set.univ :=
        VagueSignedMeasure.abs_continuousTestIntegral_le_mul_totalVariation
          (difference.toDerivativePath.derivative coordinate) test.1
          (fun point ↦ by
            change |boundedTest point| ≤ ‖boundedTest‖
            simpa only [Real.norm_eq_abs] using boundedTest.norm_coe_le_norm point)
      _ ≤ ‖boundedTest‖ *
          (finiteIntervalHybridBVDerivativeTotalVariation difference).toReal := by
        gcongr
        apply ENNReal.toReal_mono hDifferenceFinite
        change
          (difference.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
              Set.univ ≤
            ∑ other,
              (difference.toDerivativePath.derivative other).toSignedMeasure.totalVariation
                Set.univ
        exact Finset.single_le_sum
          (f := fun other =>
            (difference.toDerivativePath.derivative other).toSignedMeasure.totalVariation
              Set.univ)
          (fun other _hOther ↦ (bot_le : (0 : ENNReal) ≤ _))
          (Finset.mem_univ coordinate)

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses
