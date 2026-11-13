/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff

/-!
# Absolute-continuity closure for vaguely convergent signed measures

This module proves a uniform-integrability form of absolute-continuity closure.  A genuinely
vaguely convergent family of nonnegative finite signed Borel measures cannot acquire singular
mass in the limit when one event modulus controls the total variation of every approximating
measure in terms of a fixed reference measure.

The proof is local and quantitative.  Inner regularity reduces a hypothetical singular event to
a positive compact set, outer regularity surrounds that compact set by a reference-small open
set, and a compactly supported Urysohn test transports the uniform variation bound through vague
convergence.

## Main declaration

* `VagueSignedMeasure.absolutelyContinuous_toSignedMeasure_of_tendsto_of_uniformVariation` closes
  absolute continuity under genuine vague convergence and a uniform event modulus.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

universe u v

noncomputable section

namespace VagueSignedMeasure

variable {Carrier : Type u} [MetricSpace Carrier]
  [LocallyCompactSpace Carrier] [SecondCountableTopology Carrier]
  [MeasurableSpace Carrier] [BorelSpace Carrier]

/-- Genuine vague convergence, nonnegativity, and one uniform reference-measure event modulus
force the limiting signed measure to remain absolutely continuous with respect to the reference
measure. -/
theorem absolutelyContinuous_toSignedMeasure_of_tendsto_of_uniformVariation
    {Index : Type v} {indexFilter : Filter Index} [indexFilter.NeBot]
    {measures : Index → VagueSignedMeasure Carrier}
    {limit : VagueSignedMeasure Carrier}
    (reference : Measure Carrier)
    [IsFiniteMeasure reference]
    (hTendsto : Tendsto measures indexFilter (nhds limit))
    (hNonnegative : ∀ index, 0 ≤ (measures index).toSignedMeasure)
    (hUniformVariation : ∀ epsilon : ENNReal, 0 < epsilon →
      ∃ delta : ENNReal, 0 < delta ∧
        ∀ index event, MeasurableSet event → reference event ≤ delta →
          (measures index).toSignedMeasure.totalVariation event ≤ epsilon) :
    limit.toSignedMeasure ≪ᵥ reference.toENNRealVectorMeasure := by
  have hLimitNonnegative : 0 ≤ limit.toSignedMeasure :=
    zero_le_toSignedMeasure_of_tendsto_of_zero_le hTendsto hNonnegative
  have hLimitNonnegativeOn : 0 ≤[Set.univ] limit.toSignedMeasure :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hLimitNonnegative
  let limitMeasure := limit.toSignedMeasure.toMeasureOfZeroLE
    Set.univ MeasurableSet.univ hLimitNonnegativeOn
  have hLimitRepresentation : limitMeasure.toSignedMeasure = limit.toSignedMeasure :=
    SignedMeasure.toMeasureOfZeroLE_toSignedMeasure
      limit.toSignedMeasure hLimitNonnegativeOn
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro event hEvent hReferenceVectorZero
  have hReferenceZero : reference event = 0 := by
    simpa only [Measure.toENNRealVectorMeasure_apply_measurable hEvent] using
      hReferenceVectorZero
  suffices hLimitMeasureZero : limitMeasure event = 0 by
    rw [← hLimitRepresentation,
      Measure.toSignedMeasure_apply_measurable hEvent, measureReal_def,
      hLimitMeasureZero]
    simp
  by_contra hLimitMeasureNonzero
  have hLimitMeasurePositive : 0 < limitMeasure event :=
    pos_iff_ne_zero.mpr hLimitMeasureNonzero
  obtain ⟨compactSet, hCompactSubset, hCompact, hCompactPositive⟩ :=
    hEvent.exists_lt_isCompact_of_ne_top
      (measure_ne_top limitMeasure event) hLimitMeasurePositive
  have hCompactReferenceZero : reference compactSet = 0 :=
    measure_mono_null hCompactSubset hReferenceZero
  have hCompactLimitFinite : limitMeasure compactSet ≠ ∞ :=
    measure_ne_top limitMeasure compactSet
  have hCompactLimitRealPositive : 0 < limitMeasure.real compactSet := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hCompactPositive.ne' hCompactLimitFinite
  let epsilonReal := limitMeasure.real compactSet / 2
  have hEpsilonRealPositive : 0 < epsilonReal := by
    dsimp only [epsilonReal]
    positivity
  let epsilon : ENNReal := ENNReal.ofReal epsilonReal
  have hEpsilonPositive : 0 < epsilon :=
    ENNReal.ofReal_pos.mpr hEpsilonRealPositive
  obtain ⟨delta, hDeltaPositive, hVariation⟩ :=
    hUniformVariation epsilon hEpsilonPositive
  obtain ⟨openSet, hCompactOpen, hOpen, hOpenReference⟩ :=
    exists_isOpen_le_add compactSet reference hDeltaPositive.ne'
  have hOpenReferenceLe : reference openSet ≤ delta := by
    simpa only [hCompactReferenceZero, zero_add] using hOpenReference
  obtain ⟨test, hTestOne, hTestSupport, hTestRange⟩ :
      ∃ test : C_c(Carrier, ℝ), Set.EqOn test 1 compactSet ∧
        tsupport test ⊆ openSet ∧ ∀ point, test point ∈ Set.Icc 0 1 := by
    obtain ⟨test, hOne, hSupportCompact, hSupportSubset, hRange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        hCompact hOpen hCompactOpen
    exact ⟨⟨test, hasCompactSupport_def.mpr hSupportCompact⟩,
      hOne, hSupportSubset, hRange⟩
  have hTestErrorBound (point : Carrier) : |test point - (0 : C_c(Carrier, ℝ)) point| ≤ 1 := by
    change |test point - 0| ≤ 1
    rw [sub_zero]
    rw [abs_of_nonneg (hTestRange point).1]
    exact (hTestRange point).2
  have hTestOutside : Set.EqOn test (0 : C_c(Carrier, ℝ)) openSetᶜ := by
    intro point hPoint
    have hPointSupport : point ∉ tsupport test := fun hMembership =>
      hPoint (hTestSupport hMembership)
    simp [image_eq_zero_of_notMem_tsupport hPointSupport]
  have hApproximateIntegralBound (index : Index) :
      |(measures index).continuousTestIntegral test| ≤ epsilonReal := by
    have hLocalized :=
      abs_continuousTestIntegral_sub_le_mul_totalVariationOn
        (measures index) test 0 hOpen.measurableSet
          hTestErrorBound hTestOutside
    have hVariationBound :=
      hVariation index openSet hOpen.measurableSet hOpenReferenceLe
    have hVariationRealBound :
        (measures index).toSignedMeasure.totalVariation.real openSet ≤ epsilonReal := by
      rw [measureReal_def]
      have := ENNReal.toReal_mono (by simp [epsilon]) hVariationBound
      simpa only [epsilon, ENNReal.toReal_ofReal hEpsilonRealPositive.le] using this
    have hLocalizedBound := hLocalized.trans
      (show 1 * (measures index).toSignedMeasure.totalVariation.real openSet ≤ epsilonReal by
        simpa only [one_mul] using hVariationRealBound)
    have hZero :
        (measures index).continuousTestIntegral (0 : C_c(Carrier, ℝ)) = 0 := by
      unfold continuousTestIntegral
      simp
    rw [hZero, sub_zero] at hLocalizedBound
    exact hLocalizedBound
  have hLimitIntegralUpper :
      limit.continuousTestIntegral test ≤ epsilonReal := by
    apply le_of_tendsto
      ((tendsto_iff_forall_continuousTestIntegral_tendsto.mp hTendsto) test)
    exact Filter.Eventually.of_forall fun index =>
      (le_abs_self _).trans (hApproximateIntegralBound index)
  have hCompactIndicatorLeTest (point : Carrier) :
      compactSet.indicator 1 point ≤ test point := by
    by_cases hPoint : point ∈ compactSet
    · simp [hPoint, hTestOne hPoint]
    · simp [hPoint, (hTestRange point).1]
  have hCompactRealLeIntegral :
      limitMeasure.real compactSet ≤ limit.continuousTestIntegral test := by
    calc
      limitMeasure.real compactSet =
          ∫ point, compactSet.indicator 1 point ∂limitMeasure :=
        (integral_indicator_one hCompact.measurableSet).symm
      _ ≤ ∫ point, test point ∂limitMeasure := by
        refine integral_mono ?_ test.integrable hCompactIndicatorLeTest
        exact (continuousOn_const.integrableOn_compact hCompact).integrable_indicator
          hCompact.measurableSet
      _ = limit.continuousTestIntegral test := by
        change (∫ point, test point ∂limitMeasure) =
          VagueSignedMeasure.continuousTestIntegral
            (VagueSignedMeasure.ofSignedMeasure limit.toSignedMeasure) test
        rw [← hLimitRepresentation, continuousTestIntegral_toSignedMeasure]
  have hHalfContradiction :
      limitMeasure.real compactSet ≤ limitMeasure.real compactSet / 2 := by
    exact hCompactRealLeIntegral.trans hLimitIntegralUpper
  linarith

end VagueSignedMeasure

end

end FiniteMarkovProcesses
