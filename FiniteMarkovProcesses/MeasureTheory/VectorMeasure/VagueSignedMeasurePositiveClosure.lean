/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureTopology
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Positive-cone closure for vaguely convergent signed measures

This module proves that nonnegative finite signed measures remain nonnegative under genuine vague
convergence.  The proof is representation-free: nonnegativity of every compactly supported
continuous test implies that the negative Jordan part is dominated by the positive Jordan part.
Inner regularity upgrades the compact-set comparison to a measure comparison.

The result concerns the full vague topology on the ambient carrier.  Applications using a
boundary-blind relative test family must separately prove that no variation escapes through the
omitted boundary before invoking it.

## Main declarations

* `VagueSignedMeasure.zero_le_toSignedMeasure_of_continuousTestIntegral_nonnegative` recognizes a
  nonnegative signed measure from its action on nonnegative compact tests.
* `VagueSignedMeasure.zero_le_toSignedMeasure_of_tendsto_of_zero_le` proves sequential or netwise
  closure of the positive cone in the genuine vague topology.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

universe u v

noncomputable section

namespace VagueSignedMeasure

variable {Carrier : Type u} [MetricSpace Carrier]
  [LocallyCompactSpace Carrier] [SecondCountableTopology Carrier]
  [MeasurableSpace Carrier] [BorelSpace Carrier]

private theorem measure_apply_compact_le_of_nonnegative_compactTestIntegral_le
    {first second : Measure Carrier} [IsFiniteMeasure first] [IsFiniteMeasure second]
    (hIntegral : ∀ test : C_c(Carrier, ℝ), (∀ point, 0 ≤ test point) →
      ∫ point, test point ∂first ≤ ∫ point, test point ∂second)
    {compactSet : Set Carrier} (hCompact : IsCompact compactSet) :
    first compactSet ≤ second compactSet := by
  refine ENNReal.le_of_forall_pos_le_add fun epsilon hEpsilon hSecondFinite => ?_
  have hSecondCompactFinite : second compactSet ≠ ⊤ := hSecondFinite.ne
  have hFirstCompactFinite : first compactSet ≠ ⊤ :=
    (measure_lt_top first compactSet).ne
  obtain ⟨openSet, hCompactSubset, hOpen, hOpenBound⟩ :
      ∃ openSet ⊇ compactSet, IsOpen openSet ∧
        second openSet ≤ second compactSet + epsilon :=
    exists_isOpen_le_add compactSet second
      (ne_of_gt (ENNReal.coe_lt_coe.mpr hEpsilon))
  have hOpenFinite : second openSet < ⊤ :=
    hOpenBound.trans_lt (by finiteness)
  obtain ⟨test, hTestOne, hTestSupport, hTestRange⟩ :
      ∃ test : C_c(Carrier, ℝ), Set.EqOn test 1 compactSet ∧
        tsupport test ⊆ openSet ∧ ∀ point, test point ∈ Set.Icc 0 1 := by
    obtain ⟨test, hOne, hSupportCompact, hSupportSubset, hRange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        hCompact hOpen hCompactSubset
    exact ⟨⟨test, hasCompactSupport_def.mpr hSupportCompact⟩,
      hOne, hSupportSubset, hRange⟩
  have hTestLeOpenIndicator (point : Carrier) :
      test point ≤ openSet.indicator 1 point := by
    by_cases hPoint : point ∈ tsupport test
    · simp [(hTestSupport hPoint), (hTestRange point).2]
    · simp [image_eq_zero_of_notMem_tsupport hPoint, Set.indicator_nonneg]
  have hCompactIndicatorLeTest (point : Carrier) :
      compactSet.indicator 1 point ≤ test point := by
    by_cases hPoint : point ∈ compactSet
    · simp [hPoint, hTestOne hPoint]
    · simp [hPoint, (hTestRange point).1]
  suffices first.real compactSet ≤ (second compactSet).toReal + ↑epsilon by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  calc
    first.real compactSet =
        ∫ point, compactSet.indicator 1 point ∂first :=
      (integral_indicator_one hCompact.measurableSet).symm
    _ ≤ ∫ point, test point ∂first := by
      refine integral_mono ?_ test.integrable hCompactIndicatorLeTest
      exact (continuousOn_const.integrableOn_compact hCompact).integrable_indicator
        hCompact.measurableSet
    _ ≤ ∫ point, test point ∂second :=
      hIntegral test fun point => (hTestRange point).1
    _ ≤ ∫ point, openSet.indicator 1 point ∂second := by
      refine integral_mono test.integrable ?_ hTestLeOpenIndicator
      exact IntegrableOn.integrable_indicator integrableOn_const hOpen.measurableSet
    _ ≤ (second compactSet).toReal + ↑epsilon := by
      rwa [integral_indicator_one hOpen.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

private theorem measure_le_of_nonnegative_compactTestIntegral_le
    {first second : Measure Carrier} [IsFiniteMeasure first] [IsFiniteMeasure second]
    (hIntegral : ∀ test : C_c(Carrier, ℝ), (∀ point, 0 ≤ test point) →
      ∫ point, test point ∂first ≤ ∫ point, test point ∂second) :
    first ≤ second := by
  apply Measure.le_iff.mpr
  intro event hEvent
  rw [hEvent.measure_eq_iSup_isCompact first,
    hEvent.measure_eq_iSup_isCompact second]
  refine iSup_mono fun compactSet =>
    iSup_mono fun _hCompactSubset =>
      iSup_mono fun hCompact => ?_
  exact measure_apply_compact_le_of_nonnegative_compactTestIntegral_le
    hIntegral hCompact

/-- A finite signed Borel measure is nonnegative when it integrates every nonnegative compactly
supported continuous real test to a nonnegative number. -/
theorem zero_le_toSignedMeasure_of_continuousTestIntegral_nonnegative
    (measure : VagueSignedMeasure Carrier)
    (hNonnegative : ∀ test : C_c(Carrier, ℝ), (∀ point, 0 ≤ test point) →
      0 ≤ measure.continuousTestIntegral test) :
    0 ≤ measure.toSignedMeasure := by
  let jordan := measure.toSignedMeasure.toJordanDecomposition
  have hNegativeLePositive : jordan.negPart ≤ jordan.posPart := by
    apply measure_le_of_nonnegative_compactTestIntegral_le
    intro test hTest
    have hSignedIntegral := hNonnegative test hTest
    unfold continuousTestIntegral at hSignedIntegral
    change 0 ≤ (∫ point, test point ∂jordan.posPart) -
      ∫ point, test point ∂jordan.negPart at hSignedIntegral
    linarith
  rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition measure.toSignedMeasure]
  unfold JordanDecomposition.toSignedMeasure
  rw [sub_nonneg, Measure.toSignedMeasure_le_toSignedMeasure_iff]
  exact hNegativeLePositive

omit [LocallyCompactSpace Carrier] [SecondCountableTopology Carrier] [BorelSpace Carrier] in
/-- Continuous compact test integration of a nonnegative signed measure equals integration
against its total variation. -/
theorem continuousTestIntegral_eq_integral_totalVariation_of_zero_le
    (measure : VagueSignedMeasure Carrier)
    (hMeasure : 0 ≤ measure.toSignedMeasure)
    (test : C_c(Carrier, ℝ)) :
    measure.continuousTestIntegral test =
      ∫ point, test point ∂measure.toSignedMeasure.totalVariation := by
  have hRestricted : 0 ≤[Set.univ] measure.toSignedMeasure :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hMeasure
  let positiveMeasure := measure.toSignedMeasure.toMeasureOfZeroLE
    Set.univ MeasurableSet.univ hRestricted
  have hRepresentation : positiveMeasure.toSignedMeasure = measure.toSignedMeasure :=
    SignedMeasure.toMeasureOfZeroLE_toSignedMeasure measure.toSignedMeasure hRestricted
  change VagueSignedMeasure.continuousTestIntegral
      (VagueSignedMeasure.ofSignedMeasure measure.toSignedMeasure) test = _
  rw [← hRepresentation, continuousTestIntegral_toSignedMeasure,
    SignedMeasure.totalVariation_toSignedMeasure]

omit [LocallyCompactSpace Carrier] [SecondCountableTopology Carrier] [BorelSpace Carrier] in
private theorem continuousTestIntegral_nonnegative_of_zero_le
    (measure : VagueSignedMeasure Carrier)
    (hMeasure : 0 ≤ measure.toSignedMeasure)
    (test : C_c(Carrier, ℝ)) (hTest : ∀ point, 0 ≤ test point) :
    0 ≤ measure.continuousTestIntegral test := by
  have hRestricted : 0 ≤[Set.univ] measure.toSignedMeasure :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hMeasure
  let positiveMeasure := measure.toSignedMeasure.toMeasureOfZeroLE
    Set.univ MeasurableSet.univ hRestricted
  have hRepresentation : positiveMeasure.toSignedMeasure = measure.toSignedMeasure :=
    SignedMeasure.toMeasureOfZeroLE_toSignedMeasure measure.toSignedMeasure hRestricted
  change 0 ≤ VagueSignedMeasure.continuousTestIntegral
    (VagueSignedMeasure.ofSignedMeasure measure.toSignedMeasure) test
  rw [← hRepresentation]
  rw [continuousTestIntegral_toSignedMeasure]
  exact integral_nonneg hTest

/-- The cone of nonnegative finite signed Borel measures is closed under genuine vague
convergence against every compactly supported continuous real test. -/
theorem zero_le_toSignedMeasure_of_tendsto_of_zero_le
    {Index : Type v} {indexFilter : Filter Index} [indexFilter.NeBot]
    {measures : Index → VagueSignedMeasure Carrier}
    {limit : VagueSignedMeasure Carrier}
    (hTendsto : Tendsto measures indexFilter (nhds limit))
    (hNonnegative : ∀ index, 0 ≤ (measures index).toSignedMeasure) :
    0 ≤ limit.toSignedMeasure := by
  apply zero_le_toSignedMeasure_of_continuousTestIntegral_nonnegative
  intro test hTest
  have hIntegralTendsto :=
    (tendsto_iff_forall_continuousTestIntegral_tendsto.mp hTendsto) test
  apply ge_of_tendsto hIntegralTendsto
  exact Filter.Eventually.of_forall fun index =>
    continuousTestIntegral_nonnegative_of_zero_le
      (measures index) (hNonnegative index) test hTest

end VagueSignedMeasure

end

end FiniteMarkovProcesses
