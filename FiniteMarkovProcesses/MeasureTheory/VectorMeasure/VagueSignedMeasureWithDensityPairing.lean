/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureTopology

/-!
# Pairing vague signed measures supplied by integrable densities

This module identifies the Jordan-decomposition test integral of a signed measure built with
`Measure.withDensityᵥ` with the ordinary integral of the test times the real density.  It is the
bridge between vague signed-measure topology and Radon--Nikodym density formulas.
-/

namespace FiniteMarkovProcesses

open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported ENNReal

universe u

variable {Carrier : Type u} [MeasurableSpace Carrier] [TopologicalSpace Carrier]
  [OpensMeasurableSpace Carrier]

/-- Multiplication by a compactly supported continuous real test preserves integrability. -/
theorem integrable_compactlySupportedContinuousMap_mul_of_integrable_right
    (test : C_c(Carrier, ℝ)) {density : Carrier → ℝ} {measure : Measure Carrier}
    (hDensityIntegrable : Integrable density measure) :
    Integrable (fun point => test point * density point) measure := by
  let boundedTest : Carrier →ᵇ ℝ :=
    ofCompactSupport test test.continuous test.hasCompactSupport
  apply hDensityIntegrable.bdd_mul test.continuous.aestronglyMeasurable
  filter_upwards [] with point
  change ‖boundedTest point‖ ≤ ‖boundedTest‖
  exact boundedTest.norm_coe_le_norm point

/-- A compactly supported continuous test paired against an integrable real density agrees with
the ordinary integral of their product. -/
theorem VagueSignedMeasure.continuousTestIntegral_withDensity
    (measure : Measure Carrier) (density : Carrier → ℝ)
    (hDensityMeasurable : Measurable density)
    (hDensityIntegrable : Integrable density measure)
    (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure
      (measure.withDensityᵥ density)).continuousTestIntegral test =
      ∫ point, test point * density point ∂measure := by
  have hPositiveIntegrable :
      Integrable
        (fun point => (ENNReal.ofReal (density point)).toReal * test point) measure := by
    simpa only [ENNReal.toReal_ofReal', mul_comm] using
      integrable_compactlySupportedContinuousMap_mul_of_integrable_right
        test hDensityIntegrable.pos_part
  have hNegativeIntegrable :
      Integrable
        (fun point => (ENNReal.ofReal (-density point)).toReal * test point) measure := by
    simpa only [ENNReal.toReal_ofReal', mul_comm] using
      integrable_compactlySupportedContinuousMap_mul_of_integrable_right
        test hDensityIntegrable.neg_part
  have hJordan :=
    SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
      (s := measure.withDensityᵥ density) (t := 0)
      hDensityMeasurable hDensityIntegrable
      VectorMeasure.MutuallySingular.zero_left (by simp)
  unfold VagueSignedMeasure.continuousTestIntegral
  rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure, hJordan]
  simp only [SignedMeasure.toJordanDecomposition_zero]
  simp only [JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart, zero_add]
  rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun point => ENNReal.ofReal (density point))
      (ENNReal.continuous_ofReal.measurable.comp hDensityMeasurable)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) test,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun point => ENNReal.ofReal (-density point))
      (ENNReal.continuous_ofReal.measurable.comp hDensityMeasurable.neg)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) test]
  rw [← integral_sub
    (by simpa only [smul_eq_mul] using hPositiveIntegrable)
    (by simpa only [smul_eq_mul] using hNegativeIntegrable)]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [smul_eq_mul, ENNReal.toReal_ofReal']
  rcases le_total (density point) 0 with hNonpositive | hNonnegative
  · rw [max_eq_right hNonpositive, max_eq_left (neg_nonneg.mpr hNonpositive)]
    ring
  · rw [max_eq_left hNonnegative, max_eq_right (neg_nonpos.mpr hNonnegative)]
    ring

end FiniteMarkovProcesses
