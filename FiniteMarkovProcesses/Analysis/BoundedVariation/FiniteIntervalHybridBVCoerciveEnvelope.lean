/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation
import Mathlib.MeasureTheory.Integral.Average

/-!
# Coercive envelopes for finite-interval hybrid BV paths

This module isolates the admissibility-free quantitative envelope used in the HPR compactness
route.  It bounds the strong `L1` quotient and the total variation of every carried derivative
measure.  Absolute continuity, a continuity equation, and boundary conditions deliberately do
not enter the envelope: those properties need not be closed in the hybrid topology.

No compactness theorem is asserted here.  Proving that the closure of this envelope is compact
requires the finite-dimensional BV/Helly compactness and derivative-test convergence arguments.

## Main declarations

- `finiteIntervalHybridBVDerivativeTotalVariation`: total derivative variation over all finite
  coordinates.
- `enorm_toL1Path_le_duration_mul_initialTrace_add_derivativeTotalVariation`: duration times the
  initial norm plus derivative variation controls the strong-`L1` norm.
- `finiteIntervalHybridBVUniformL1VariationEnvelope`: the broad admissibility-free `L1` and
  derivative-variation envelope.
-/

namespace FiniteMarkovProcesses

open MeasureTheory
open scoped BigOperators ENNReal

universe u

noncomputable section

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Sum of the total-variation masses of every derivative coordinate carried by a hybrid path. -/
noncomputable def finiteIntervalHybridBVDerivativeTotalVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration) : ENNReal :=
  ∑ coordinate,
    (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ

/-- On the absolutely continuous representation domain, complete derivative variation is the
finite sum of the physical-time `L1` masses of the Radon--Nikodym densities. -/
theorem finiteIntervalHybridBVDerivativeTotalVariation_eq_sum_lintegral_ofReal_abs
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative) :
    finiteIntervalHybridBVDerivativeTotalVariation path =
      ∑ coordinate,
        ∫⁻ time, ENNReal.ofReal |path.derivativeDensity coordinate time|
          ∂finiteOpenIntervalVolume duration := by
  unfold finiteIntervalHybridBVDerivativeTotalVariation
  apply Finset.sum_congr rfl
  intro coordinate _hCoordinate
  rw [← path.withDensity_derivativeDensity_eq_derivative
      hAbsolutelyContinuous coordinate,
    SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs]
  · exact path.measurable_derivativeDensity coordinate
  · exact SignedMeasure.integrable_rnDeriv
      (path.toDerivativePath.derivative coordinate).toSignedMeasure
      (finiteOpenIntervalVolume duration)

/-- The displacement of a hybrid path across one ordered physical interval is controlled by the
coordinatewise total variation of its derivative on that same interval. -/
theorem edist_cadlagRepresentative_le_derivativeTotalVariation_Ioc
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    {start finish : ℝ} (hStart : 0 ≤ start) (hOrder : start ≤ finish)
    (hFinish : finish < duration) :
    edist (path.cadlagRepresentative.representative finish)
        (path.cadlagRepresentative.representative start) ≤
      ∑ coordinate,
        (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation
          (Set.Ioc start finish) := by
  classical
  rw [PiLp.edist_eq_of_L1]
  apply Finset.sum_le_sum
  intro coordinate _hCoordinate
  rw [edist_dist, Real.dist_eq,
    ← path.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
      hStart hOrder hFinish]
  exact SignedMeasure.ofReal_abs_apply_le_totalVariation _ measurableSet_Ioc

/-- The complete derivative-variation mass controls every displacement between ordered physical
times. -/
theorem edist_cadlagRepresentative_le_derivativeTotalVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    {start finish : ℝ} (hStart : 0 ≤ start) (hOrder : start ≤ finish)
    (hFinish : finish < duration) :
    edist (path.cadlagRepresentative.representative finish)
        (path.cadlagRepresentative.representative start) ≤
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  refine (edist_cadlagRepresentative_le_derivativeTotalVariation_Ioc path
    hStart hOrder hFinish).trans ?_
  apply Finset.sum_le_sum
  intro coordinate _hCoordinate
  exact measure_mono (Set.subset_univ (Set.Ioc start finish))

/-- Every positive-duration hybrid path has a physical anchor whose norm is at most its `L1`
average.  The anchor is chosen outside the null complement of the open physical interval. -/
theorem exists_physicalTime_enorm_cadlagRepresentative_le_l1Average
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) :
    ∃ time ∈ Set.Ioo 0 duration,
      ‖path.cadlagRepresentative.representative time‖ₑ ≤
        ‖path.toDerivativePath.toL1Path‖ₑ / ENNReal.ofReal duration := by
  let representative := path.cadlagRepresentative.representative
  let hRepresentative :
      MemLp representative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose path.cadlagRepresentative.represents
  have hRepresents :
      hRepresentative.toLp representative = path.toDerivativePath.toL1Path :=
    Classical.choose_spec path.cadlagRepresentative.represents
  have hMeasureNonzero : finiteOpenIntervalVolume duration ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    rw [finiteOpenIntervalVolume_apply_univ]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hDuration)
  have hRepresentativeEnormMeasurable :
      AEMeasurable (fun time => ‖representative time‖ₑ)
        (finiteOpenIntervalVolume duration) :=
    hRepresentative.aestronglyMeasurable.enorm
  obtain ⟨time, hTime, hTimeAverage⟩ :=
    exists_notMem_null_le_laverage hMeasureNonzero
      hRepresentativeEnormMeasurable
      (finiteOpenIntervalVolume_apply_compl_Ioo duration)
  refine ⟨time, Set.notMem_compl_iff.mp hTime, ?_⟩
  calc
    ‖path.cadlagRepresentative.representative time‖ₑ =
        ‖representative time‖ₑ := rfl
    _ ≤ ⨍⁻ point, ‖representative point‖ₑ
        ∂finiteOpenIntervalVolume duration := hTimeAverage
    _ = ‖path.toDerivativePath.toL1Path‖ₑ /
        ENNReal.ofReal duration := by
      rw [laverage_eq, finiteOpenIntervalVolume_apply_univ,
        ← hRepresents, Lp.enorm_toLp,
        eLpNorm_one_eq_lintegral_enorm hRepresentative.aestronglyMeasurable]

/-- The `L1` average plus complete derivative variation controls the canonical càdlàg
representative at every left-closed physical time.  Including time zero is useful for left-endpoint
step approximations; no terminal value is asserted because the physical carrier is open at the
right endpoint. -/
theorem enorm_cadlagRepresentative_le_l1Average_add_derivativeTotalVariation_of_mem_Ico
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) {time : ℝ} (hTime : time ∈ Set.Ico 0 duration) :
    ‖path.cadlagRepresentative.representative time‖ₑ ≤
      ‖path.toDerivativePath.toL1Path‖ₑ / ENNReal.ofReal duration +
        finiteIntervalHybridBVDerivativeTotalVariation path := by
  obtain ⟨anchor, hAnchor, hAnchorNorm⟩ :=
    exists_physicalTime_enorm_cadlagRepresentative_le_l1Average path hDuration
  have hDisplacement :
      edist (path.cadlagRepresentative.representative time)
          (path.cadlagRepresentative.representative anchor) ≤
        finiteIntervalHybridBVDerivativeTotalVariation path := by
    rcases le_total anchor time with hAnchorTime | hTimeAnchor
    · exact edist_cadlagRepresentative_le_derivativeTotalVariation path
        hAnchor.1.le hAnchorTime hTime.2
    · rw [edist_comm]
      exact edist_cadlagRepresentative_le_derivativeTotalVariation path
        hTime.1 hTimeAnchor hAnchor.2
  calc
    ‖path.cadlagRepresentative.representative time‖ₑ =
        edist (path.cadlagRepresentative.representative time) 0 :=
      (edist_zero_right _).symm
    _ ≤ edist (path.cadlagRepresentative.representative time)
          (path.cadlagRepresentative.representative anchor) +
        edist (path.cadlagRepresentative.representative anchor) 0 :=
      edist_triangle _ _ _
    _ ≤ finiteIntervalHybridBVDerivativeTotalVariation path +
        ‖path.cadlagRepresentative.representative anchor‖ₑ := by
      rw [edist_zero_right]
      exact add_le_add hDisplacement le_rfl
    _ ≤ finiteIntervalHybridBVDerivativeTotalVariation path +
        ‖path.toDerivativePath.toL1Path‖ₑ / ENNReal.ofReal duration :=
      add_le_add le_rfl hAnchorNorm
    _ = ‖path.toDerivativePath.toL1Path‖ₑ / ENNReal.ofReal duration +
        finiteIntervalHybridBVDerivativeTotalVariation path := add_comm _ _

/-- The `L1` average plus complete derivative variation controls every physical-time value of the
canonical càdlàg representative. -/
theorem enorm_cadlagRepresentative_le_l1Average_add_derivativeTotalVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) {time : ℝ} (hTime : time ∈ Set.Ioo 0 duration) :
    ‖path.cadlagRepresentative.representative time‖ₑ ≤
      ‖path.toDerivativePath.toL1Path‖ₑ / ENNReal.ofReal duration +
        finiteIntervalHybridBVDerivativeTotalVariation path :=
  enorm_cadlagRepresentative_le_l1Average_add_derivativeTotalVariation_of_mem_Ico
    path hDuration ⟨hTime.1.le, hTime.2⟩

/-- On a bounded interval, duration times the initial-trace norm plus complete derivative
variation controls the strong-`L1` norm. This estimate uses no admissibility or absolute
continuity premise. -/
theorem enorm_toL1Path_le_duration_mul_initialTrace_add_derivativeTotalVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration) :
    ‖path.toDerivativePath.toL1Path‖ₑ ≤
      ENNReal.ofReal duration *
        (‖path.initialTrace‖ₑ +
          finiteIntervalHybridBVDerivativeTotalVariation path) := by
  let representative := path.cadlagRepresentative.representative
  let hRepresentative :
      MemLp representative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose path.cadlagRepresentative.represents
  have hRepresents :
      hRepresentative.toLp representative =
        path.toDerivativePath.toL1Path :=
    Classical.choose_spec path.cadlagRepresentative.represents
  rw [← hRepresents, Lp.enorm_toLp,
    eLpNorm_one_eq_lintegral_enorm hRepresentative.aestronglyMeasurable]
  calc
    (∫⁻ time, ‖representative time‖ₑ
        ∂finiteOpenIntervalVolume duration) ≤
        ∫⁻ _time, (‖path.initialTrace‖ₑ +
          finiteIntervalHybridBVDerivativeTotalVariation path)
          ∂finiteOpenIntervalVolume duration := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
      calc
        ‖representative time‖ₑ =
            edist (path.cadlagRepresentative.representative time) 0 := by
          rw [edist_zero_right]
        _ ≤ edist (path.cadlagRepresentative.representative time)
              (path.cadlagRepresentative.representative 0) +
            edist (path.cadlagRepresentative.representative 0) 0 :=
          edist_triangle _ _ _
        _ ≤ finiteIntervalHybridBVDerivativeTotalVariation path +
            ‖path.initialTrace‖ₑ := by
          apply add_le_add
          · exact edist_cadlagRepresentative_le_derivativeTotalVariation
              path le_rfl hTime.1.le hTime.2
          · rw [edist_zero_right]
            exact le_rfl
        _ = ‖path.initialTrace‖ₑ +
            finiteIntervalHybridBVDerivativeTotalVariation path := add_comm _ _
    _ = ENNReal.ofReal duration *
        (‖path.initialTrace‖ₑ +
          finiteIntervalHybridBVDerivativeTotalVariation path) := by
      rw [lintegral_const]
      simp only [finiteOpenIntervalVolume_apply_univ]
      exact mul_comm _ _

/-- The pointwise variation of the canonical càdlàg representative is controlled by the sum of
the total-variation masses of its coordinate derivatives.  This is the quantitative bridge from
the derivative-measure envelope to the finite-dimensional BV compactness argument. -/
theorem eVariationOn_cadlagRepresentative_le_derivativeTotalVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration) :
    eVariationOn path.cadlagRepresentative.representative (Set.Ioo 0 duration) ≤
      finiteIntervalHybridBVDerivativeTotalVariation path := by
  classical
  apply iSup_le
  rintro ⟨count, sampledPath, hSampledPathMonotone, hSampledPathPhysical⟩
  calc
    (∑ index ∈ Finset.range count,
        edist (path.cadlagRepresentative.representative (sampledPath (index + 1)))
          (path.cadlagRepresentative.representative (sampledPath index))) =
        ∑ index ∈ Finset.range count, ∑ coordinate,
          edist
            (path.cadlagRepresentative.representative (sampledPath (index + 1)) coordinate)
            (path.cadlagRepresentative.representative (sampledPath index) coordinate) := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      exact PiLp.edist_eq_of_L1 _ _
    _ = ∑ coordinate, ∑ index ∈ Finset.range count,
        edist
          (path.cadlagRepresentative.representative (sampledPath (index + 1)) coordinate)
          (path.cadlagRepresentative.representative (sampledPath index) coordinate) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ coordinate,
        (path.toDerivativePath.derivative coordinate).toSignedMeasure.totalVariation Set.univ := by
      apply Finset.sum_le_sum
      intro coordinate _hCoordinate
      let derivative :=
        (path.toDerivativePath.derivative coordinate).toSignedMeasure
      let incrementInterval : ℕ → Set ℝ :=
        fun index => Set.Ioc (sampledPath index) (sampledPath (index + 1))
      have hIncrement (index : ℕ) :
          derivative (incrementInterval index) =
            path.cadlagRepresentative.representative (sampledPath (index + 1)) coordinate -
              path.cadlagRepresentative.representative (sampledPath index) coordinate := by
        exact path.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
          (hSampledPathPhysical index).1.le
          (hSampledPathMonotone (Nat.le_succ index))
          (hSampledPathPhysical (index + 1)).2
      calc
        (∑ index ∈ Finset.range count,
            edist
              (path.cadlagRepresentative.representative (sampledPath (index + 1)) coordinate)
              (path.cadlagRepresentative.representative (sampledPath index) coordinate)) =
            ∑ index ∈ Finset.range count,
              ENNReal.ofReal |derivative (incrementInterval index)| := by
          apply Finset.sum_congr rfl
          intro index _hIndex
          rw [edist_dist, Real.dist_eq, hIncrement]
        _ ≤ ∑ index ∈ Finset.range count,
              derivative.totalVariation (incrementInterval index) := by
          apply Finset.sum_le_sum
          intro index _hIndex
          exact SignedMeasure.ofReal_abs_apply_le_totalVariation derivative measurableSet_Ioc
        _ ≤ derivative.totalVariation Set.univ := by
          apply sum_measure_le_measure_univ
          · intro index _hIndex
            exact measurableSet_Ioc.nullMeasurableSet
          · intro first _hFirst second _hSecond hDistinct
            apply Disjoint.aedisjoint
            apply Set.disjoint_left.2
            intro time hTimeFirst hTimeSecond
            rcases lt_or_gt_of_ne hDistinct with hFirstSecond | hSecondFirst
            · have hTimeLeSecond : time ≤ sampledPath second :=
                hTimeFirst.2.trans
                  (hSampledPathMonotone (Nat.succ_le_of_lt hFirstSecond))
              exact (not_lt_of_ge hTimeLeSecond) hTimeSecond.1
            · have hTimeLeFirst : time ≤ sampledPath first :=
                hTimeSecond.2.trans
                  (hSampledPathMonotone (Nat.succ_le_of_lt hSecondFirst))
              exact (not_lt_of_ge hTimeLeFirst) hTimeFirst.1

/-- Broad quantitative envelope used before HPR compact closure.  It contains no absolute-
continuity, continuity-equation, or boundary constraint. -/
noncomputable def finiteIntervalHybridBVUniformL1VariationEnvelope
    (l1Bound variationBound : ENNReal) :
    Set (FiniteIntervalHybridBVPath Coordinate duration) :=
  {path |
    ‖path.toDerivativePath.toL1Path‖ₑ ≤ l1Bound ∧
      finiteIntervalHybridBVDerivativeTotalVariation path ≤ variationBound}

/-- Membership in the broad envelope exposes exactly its two quantitative inequalities. -/
theorem mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff
    {path : FiniteIntervalHybridBVPath Coordinate duration}
    {l1Bound variationBound : ENNReal} :
    path ∈ finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound ↔
      ‖path.toDerivativePath.toL1Path‖ₑ ≤ l1Bound ∧
      finiteIntervalHybridBVDerivativeTotalVariation path ≤ variationBound :=
  Iff.rfl

/-- Every member of the quantitative envelope has canonical representative variation bounded by
the declared derivative-variation budget. -/
theorem eVariationOn_cadlagRepresentative_le_of_mem_uniformL1VariationEnvelope
    {path : FiniteIntervalHybridBVPath Coordinate duration}
    {l1Bound variationBound : ENNReal}
    (hPath : path ∈
      finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound) :
    eVariationOn path.cadlagRepresentative.representative (Set.Ioo 0 duration) ≤
      variationBound :=
  (eVariationOn_cadlagRepresentative_le_derivativeTotalVariation path).trans hPath.2

end

end FiniteMarkovProcesses
