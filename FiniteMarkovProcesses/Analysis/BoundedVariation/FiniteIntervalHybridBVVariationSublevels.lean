/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCoerciveEnvelope
import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff
import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureVariationLowerSemicontinuity

/-!
# Lower semicontinuity of finite-interval hybrid BV derivative variation

This module transfers vague lower semicontinuity of signed total variation to the relative
open-interval derivative topology used by `FiniteIntervalHybridBVPath`.  A derivative may lose
mass through either physical boundary, so the coordinate map is not continuous into the full
real-line vague topology.  Instead, support inside the open physical interval and one cutoff of
the limiting measure show that the relative test family still detects its complete variation.

The resulting coordinatewise theorem composes over the finite derivative family.  Consequently
the broad admissibility-free derivative-variation budget is closed under genuine hybrid
convergence; no absolute continuity, continuity equation, or boundary trace enters the proof.
-/

namespace FiniteMarkovProcesses

open MeasureTheory Set
open scoped CompactlySupported ENNReal Topology BigOperators

noncomputable section

namespace VagueSignedMeasure

/-- Compact tests that vanish outside a positive open physical interval detect the complete
total variation of every signed measure supported in that interval. -/
theorem totalVariation_real_univ_le_of_relativeIntervalTestIntegral_le
    (measure : VagueSignedMeasure ℝ) {duration bound : ℝ}
    (hDuration : 0 < duration)
    (hSupport : measure.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      measure.toSignedMeasure)
    (hBound : ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
      (∀ point, |test.1 point| ≤ 1) →
        measure.continuousTestIntegral test.1 ≤ bound) :
    measure.toSignedMeasure.totalVariation.real Set.univ ≤ bound := by
  apply totalVariation_real_univ_le_of_continuousTestIntegral_le measure bound
  intro test hTest
  by_contra hIntegral
  have hIntegralStrict : bound < measure.continuousTestIntegral test :=
    lt_of_not_ge hIntegral
  let epsilon := (measure.continuousTestIntegral test - bound) / 2
  have hEpsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨margin, hMargin, hBoundaryVariation⟩ :=
    SignedMeasure.exists_positive_margin_totalVariation_real_boundaryLayer_lt
      measure.toSignedMeasure hDuration hEpsilon hSupport
  let cutoff := finiteOpenIntervalCoreCutoff duration margin hMargin
  let relativeTest : FiniteOpenIntervalVanishingContinuousTest duration :=
    finiteOpenIntervalCoreCutoffMulTest hMargin test
  have hCutoffRange (point : ℝ) : cutoff point ∈ Set.Icc (0 : ℝ) 1 :=
    finiteOpenIntervalCoreCutoff_mem_Icc hMargin point
  have hRelativeTestBound (point : ℝ) : |relativeTest.1 point| ≤ 1 := by
    change |test point * cutoff point| ≤ 1
    rw [abs_mul, abs_of_nonneg (hCutoffRange point).1]
    calc
      |test point| * cutoff point ≤ 1 * 1 :=
        mul_le_mul (hTest point) (hCutoffRange point).2
          (hCutoffRange point).1 (by positivity)
      _ = 1 := one_mul 1
  have hDifferenceBound (point : ℝ) :
      |test point - (test * cutoff) point| ≤ 1 := by
    have hOneSub : |1 - cutoff point| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hCutoffRange point).2)]
      linarith [(hCutoffRange point).1]
    change |test point - test point * cutoff point| ≤ 1
    rw [show test point - test point * cutoff point =
      test point * (1 - cutoff point) by ring, abs_mul]
    calc
      |test point| * |1 - cutoff point| ≤ 1 * 1 :=
        mul_le_mul (hTest point) hOneSub (abs_nonneg _) (by positivity)
      _ = 1 := one_mul 1
  have hOutside : Set.EqOn test (test * cutoff)
      (finiteOpenIntervalBoundaryLayer duration margin)ᶜ := by
    intro point hPoint
    have hCoreOpen : point ∈ Set.Ioo margin (duration - margin) := by
      simpa only [finiteOpenIntervalBoundaryLayer, compl_compl] using hPoint
    have hCutoffOne : cutoff point = 1 :=
      finiteOpenIntervalCoreCutoff_eq_one_of_mem_core hMargin
        ⟨hCoreOpen.1.le, hCoreOpen.2.le⟩
    simp [hCutoffOne]
  have hIntegralError :
      |measure.continuousTestIntegral test -
          measure.continuousTestIntegral (test * cutoff)| ≤
        measure.toSignedMeasure.totalVariation.real
          (finiteOpenIntervalBoundaryLayer duration margin) := by
    simpa only [one_mul] using
      abs_continuousTestIntegral_sub_le_mul_totalVariationOn
        measure test (test * cutoff)
          (measurableSet_finiteOpenIntervalBoundaryLayer duration margin)
          hDifferenceBound hOutside
  have hIntegralErrorStrict :
      |measure.continuousTestIntegral test -
          measure.continuousTestIntegral (test * cutoff)| < epsilon :=
    hIntegralError.trans_lt hBoundaryVariation
  have hCutoffIntegralStrict :
      bound < measure.continuousTestIntegral (test * cutoff) := by
    have hDifferenceUpper := (abs_lt.mp hIntegralErrorStrict).2
    dsimp only [epsilon] at hDifferenceUpper
    linarith
  have hRelativeBound := hBound relativeTest hRelativeTestBound
  change measure.continuousTestIntegral (test * cutoff) ≤ bound at hRelativeBound
  exact (not_lt_of_ge hRelativeBound) hCutoffIntegralStrict

/-- For a signed measure supported in a positive physical interval, its finite total-variation
sublevels are characterized by the relative open-interval continuous-test family. -/
theorem totalVariation_apply_univ_le_iff_relativeIntervalTestIntegral_le
    (measure : VagueSignedMeasure ℝ) {duration : ℝ}
    (hDuration : 0 < duration)
    (hSupport : measure.toSignedMeasure.restrict (Set.Ioo 0 duration) =
      measure.toSignedMeasure)
    (bound : ENNReal) (hBound : bound ≠ ∞) :
    measure.toSignedMeasure.totalVariation Set.univ ≤ bound ↔
      ∀ test : FiniteOpenIntervalVanishingContinuousTest duration,
        (∀ point, |test.1 point| ≤ 1) →
          measure.continuousTestIntegral test.1 ≤ bound.toReal := by
  constructor
  · intro hVariation test hTest
    have hIntegral :
        measure.continuousTestIntegral test.1 ≤
          measure.toSignedMeasure.totalVariation.real Set.univ := by
      calc
        measure.continuousTestIntegral test.1 ≤
            |measure.continuousTestIntegral test.1| := le_abs_self _
        _ ≤ 1 * measure.toSignedMeasure.totalVariation.real Set.univ :=
          abs_continuousTestIntegral_le_mul_totalVariation measure test.1 hTest
        _ = measure.toSignedMeasure.totalVariation.real Set.univ := one_mul _
    exact hIntegral.trans (ENNReal.toReal_mono hBound hVariation)
  · intro hTests
    have hVariationReal :=
      totalVariation_real_univ_le_of_relativeIntervalTestIntegral_le
        measure hDuration hSupport hTests
    have hVariationFinite :
        measure.toSignedMeasure.totalVariation Set.univ ≠ ∞ := by
      rw [SignedMeasure.totalVariation, Measure.add_apply]
      exact (ENNReal.add_lt_top.mpr
        ⟨measure_lt_top _ _, measure_lt_top _ _⟩).ne
    exact (ENNReal.toReal_le_toReal hVariationFinite hBound).mp hVariationReal

end VagueSignedMeasure

universe u

namespace FiniteIntervalHybridBVPath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- One derivative coordinate's total variation is lower semicontinuous in the genuine hybrid
topology.  Boundary escape may strictly decrease the limit variation. -/
theorem lowerSemicontinuous_derivativeCoordinateTotalVariation
    (hDuration : 0 < duration) (coordinate : Coordinate) :
    LowerSemicontinuous fun path : FiniteIntervalHybridBVPath Coordinate duration =>
      (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro bound
  change IsClosed {path : FiniteIntervalHybridBVPath Coordinate duration |
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ ≤
      bound}
  by_cases hBound : bound = ∞
  · subst bound
    simpa only [le_top, Set.ofPred_true] using
      (isClosed_univ : IsClosed
        (Set.univ : Set (FiniteIntervalHybridBVPath Coordinate duration)))
  ·
    have hSublevel :
        {path : FiniteIntervalHybridBVPath Coordinate duration |
            (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
              Set.univ ≤ bound} =
          ⋂ test : FiniteOpenIntervalVanishingContinuousTest duration,
            ⋂ (_hTest : ∀ point, |test.1 point| ≤ 1),
              {path : FiniteIntervalHybridBVPath Coordinate duration |
                (path.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 ≤
                  bound.toReal} := by
      ext path
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact
        VagueSignedMeasure.totalVariation_apply_univ_le_iff_relativeIntervalTestIntegral_le
          (path.toDerivativePath.derivative coordinate) hDuration
          ((Classical.choose_spec path.hasCadlagDerivativeRealization).1 coordinate)
          bound hBound
    rw [hSublevel]
    exact isClosed_iInter fun test =>
      isClosed_iInter fun _hTest =>
        isClosed_Iic.preimage
          ((FiniteIntervalL1DerivativePath.continuous_derivativeTestIntegral coordinate test).comp
            isEmbedding_toDerivativePath.continuous)

end FiniteIntervalHybridBVPath

/-- The finite coordinate sum of derivative total variations is lower semicontinuous in the
hybrid topology. -/
theorem lowerSemicontinuous_finiteIntervalHybridBVDerivativeTotalVariation
    {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}
    (hDuration : 0 < duration) :
    LowerSemicontinuous fun path : FiniteIntervalHybridBVPath Coordinate duration =>
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  change LowerSemicontinuous fun path : FiniteIntervalHybridBVPath Coordinate duration =>
    ∑ coordinate,
      (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ
  exact lowerSemicontinuous_sum fun coordinate _hCoordinate =>
    FiniteIntervalHybridBVPath.lowerSemicontinuous_derivativeCoordinateTotalVariation
      hDuration coordinate

end

end FiniteMarkovProcesses
