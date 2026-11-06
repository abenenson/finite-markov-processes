/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureAbsoluteContinuityClosure

/-!
# Lower semicontinuity of signed total variation under vague convergence

This module identifies the total variation of a finite signed Borel measure with the supremum of
its integrals against compactly supported continuous tests bounded by one.  Consequently bounded
total-variation sublevels are closed in the genuine vague topology.

The proof keeps mass escape visible.  Compact inner approximations of the mutually singular
Jordan parts are separated by one compactly supported Urysohn test; no setwise convergence or
compactness of the carrier is assumed.
-/

namespace FiniteMarkovProcesses

open MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

noncomputable section

universe u

namespace VagueSignedMeasure

variable {Carrier : Type u} [MetricSpace Carrier]
  [LocallyCompactSpace Carrier] [SecondCountableTopology Carrier]
  [MeasurableSpace Carrier] [BorelSpace Carrier]

/-- A bounded compactly supported test that is one on a compact set controls the total mass lost
outside that set. -/
private theorem measureReal_univ_sub_two_mul_compl_le_integral
    (measure : Measure Carrier) [IsFiniteMeasure measure]
    (test : C_c(Carrier, ℝ)) (compactSet : Set Carrier)
    (hCompact : IsCompact compactSet)
    (hTestRange : ∀ point, test point ∈ Set.Icc (-1 : ℝ) 1)
    (hTestOne : Set.EqOn test 1 compactSet) :
    measure.real Set.univ - 2 * measure.real compactSetᶜ ≤
      ∫ point, test point ∂measure := by
  let indicator : Carrier → ℝ :=
    compactSetᶜ.indicator (fun _ => (1 : ℝ))
  let lower : Carrier → ℝ := fun point => 1 - 2 * indicator point
  have hIndicatorIntegrable : Integrable indicator measure :=
    (integrableOn_const (C := (1 : ℝ))).integrable_indicator
      hCompact.isClosed.measurableSet.compl
  have hLowerIntegrable : Integrable lower measure :=
    (integrable_const 1).sub (hIndicatorIntegrable.const_mul 2)
  have hLowerLe (point : Carrier) : lower point ≤ test point := by
    by_cases hPoint : point ∈ compactSet
    · simp [lower, indicator, hPoint, hTestOne hPoint]
    · have hPointComplement : point ∈ compactSetᶜ := by simpa
      simp only [lower, indicator, Set.indicator_of_mem hPointComplement, mul_one]
      linarith [(hTestRange point).1]
  calc
    measure.real Set.univ - 2 * measure.real compactSetᶜ =
        ∫ point, lower point ∂measure := by
      change measure.real Set.univ - 2 * measure.real compactSetᶜ =
        ∫ point, (1 : ℝ) - 2 * indicator point ∂measure
      rw [integral_sub (integrable_const 1) (hIndicatorIntegrable.const_mul 2),
        integral_const_mul]
      have hIndicatorIntegral :
          (∫ point, indicator point ∂measure) = measure.real compactSetᶜ := by
        change (∫ point, compactSetᶜ.indicator (1 : Carrier → ℝ) point ∂measure) =
          measure.real compactSetᶜ
        rw [integral_indicator_one hCompact.isClosed.measurableSet.compl]
      rw [hIndicatorIntegral]
      simp [measureReal_def]
    _ ≤ ∫ point, test point ∂measure :=
      integral_mono hLowerIntegrable test.integrable hLowerLe

/-- The negative analogue of
`measureReal_univ_sub_two_mul_compl_le_integral`. -/
private theorem integral_le_neg_measureReal_univ_add_two_mul_compl
    (measure : Measure Carrier) [IsFiniteMeasure measure]
    (test : C_c(Carrier, ℝ)) (compactSet : Set Carrier)
    (hCompact : IsCompact compactSet)
    (hTestRange : ∀ point, test point ∈ Set.Icc (-1 : ℝ) 1)
    (hTestNegOne : Set.EqOn test (-1) compactSet) :
    (∫ point, test point ∂measure) ≤
      -measure.real Set.univ + 2 * measure.real compactSetᶜ := by
  have hNegRange (point : Carrier) :
      (-test) point ∈ Set.Icc (-1 : ℝ) 1 := by
    change -1 ≤ -test point ∧ -test point ≤ 1
    rcases hTestRange point with ⟨hLower, hUpper⟩
    constructor <;> linarith
  have hNegOne : Set.EqOn (-test) 1 compactSet := by
    intro point hPoint
    simp [hTestNegOne hPoint]
  have hLower :=
    measureReal_univ_sub_two_mul_compl_le_integral
      measure (-test) compactSet hCompact hNegRange hNegOne
  have hIntegralNeg :
      (∫ point, (-test) point ∂measure) =
        -(∫ point, test point ∂measure) := by
    change (∫ point, -test point ∂measure) =
      -(∫ point, test point ∂measure)
    rw [integral_neg]
  rw [hIntegralNeg] at hLower
  linarith

omit [MetricSpace Carrier] [LocallyCompactSpace Carrier]
  [SecondCountableTopology Carrier] [BorelSpace Carrier] in
/-- A compact approximation inside the complement of a null set leaves little total mass outside
the compact set. -/
private theorem measureReal_compl_compact_lt
    (measure : Measure Carrier) [IsFiniteMeasure measure]
    {separation compactSet : Set Carrier}
    (hNull : measure separation = 0)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (hDifference :
      measure (separationᶜ \ compactSet) < ENNReal.ofReal epsilon) :
    measure.real compactSetᶜ < epsilon := by
  have hComplementSubset :
      compactSetᶜ ⊆ separation ∪ (separationᶜ \ compactSet) := by
    intro point hPoint
    by_cases hPointSeparation : point ∈ separation
    · exact Or.inl hPointSeparation
    · exact Or.inr ⟨hPointSeparation, hPoint⟩
  have hComplement : measure compactSetᶜ < ENNReal.ofReal epsilon := by
    calc
      measure compactSetᶜ ≤
          measure (separation ∪ (separationᶜ \ compactSet)) :=
        measure_mono hComplementSubset
      _ ≤ measure separation + measure (separationᶜ \ compactSet) :=
        measure_union_le _ _
      _ = measure (separationᶜ \ compactSet) := by rw [hNull, zero_add]
      _ < ENNReal.ofReal epsilon := hDifference
  rw [measureReal_def, ← ENNReal.toReal_ofReal hEpsilon.le]
  exact (ENNReal.toReal_lt_toReal (measure_ne_top measure compactSetᶜ)
    ENNReal.ofReal_ne_top).2 hComplement

/-- If every compactly supported continuous test bounded by one has signed integral at most
`bound`, then the total-variation mass is at most `bound`.  This is the noncompact signed Riesz
dual characterization needed for vague lower semicontinuity. -/
theorem totalVariation_real_univ_le_of_continuousTestIntegral_le
    (measure : VagueSignedMeasure Carrier) (bound : ℝ)
    (hBound : ∀ test : C_c(Carrier, ℝ),
      (∀ point, |test point| ≤ 1) →
        measure.continuousTestIntegral test ≤ bound) :
    measure.toSignedMeasure.totalVariation.real Set.univ ≤ bound := by
  by_contra hVariation
  have hVariationStrict :
      bound < measure.toSignedMeasure.totalVariation.real Set.univ :=
    lt_of_not_ge hVariation
  let positive := measure.toSignedMeasure.toJordanDecomposition.posPart
  let negative := measure.toSignedMeasure.toJordanDecomposition.negPart
  obtain ⟨separation, hSeparation, hPositiveNull, hNegativeComplementNull⟩ :=
    measure.toSignedMeasure.toJordanDecomposition.mutuallySingular
  let epsilon :=
    (measure.toSignedMeasure.totalVariation.real Set.univ - bound) / 8
  have hEpsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  obtain ⟨positiveCompact, hPositiveCompactSubset, hPositiveCompact,
      hPositiveDifference⟩ :=
    hSeparation.compl.exists_isCompact_sdiff_lt
      (measure_ne_top positive separationᶜ)
      (ENNReal.ofReal_pos.mpr hEpsilon).ne'
  obtain ⟨negativeCompact, hNegativeCompactSubset, hNegativeCompact,
      hNegativeDifference⟩ :=
    hSeparation.exists_isCompact_sdiff_lt
      (measure_ne_top negative separation)
      (ENNReal.ofReal_pos.mpr hEpsilon).ne'
  have hPositiveComplement :
      positive.real positiveCompactᶜ < epsilon :=
    measureReal_compl_compact_lt positive hPositiveNull
      epsilon hEpsilon hPositiveDifference
  have hNegativeComplement : negative.real negativeCompactᶜ < epsilon := by
    have hNegativeDifferenceComplement :
        negative ((separationᶜ)ᶜ \ negativeCompact) <
          ENNReal.ofReal epsilon := by
      simpa only [compl_compl] using hNegativeDifference
    exact measureReal_compl_compact_lt negative
      hNegativeComplementNull epsilon hEpsilon hNegativeDifferenceComplement
  have hCompactDisjoint : Disjoint positiveCompact negativeCompact := by
    apply Set.disjoint_left.2
    intro point hPositivePoint hNegativePoint
    exact (hPositiveCompactSubset hPositivePoint)
      (hNegativeCompactSubset hNegativePoint)
  obtain ⟨separatingMap, hSeparatingOne, hSeparatingZero,
      hSeparatingCompactSupport, hSeparatingRange⟩ :=
    exists_continuous_one_zero_of_isCompact
      hPositiveCompact hNegativeCompact.isClosed hCompactDisjoint
  let separatingTest : C_c(Carrier, ℝ) :=
    ⟨separatingMap, hSeparatingCompactSupport⟩
  let supportSet : Set Carrier := tsupport separatingMap ∪ negativeCompact
  have hSupportCompact : IsCompact supportSet :=
    (hasCompactSupport_def.mp hSeparatingCompactSupport).union hNegativeCompact
  obtain ⟨supportMap, hSupportOne, hSupportCompactSupport, _hSupportSubset,
      hSupportRange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      hSupportCompact isOpen_univ (subset_univ supportSet)
  let supportTest : C_c(Carrier, ℝ) :=
    ⟨supportMap, hSupportCompactSupport⟩
  let test : C_c(Carrier, ℝ) :=
    separatingTest + separatingTest - supportTest
  have hSupportOneOfSeparatingNonzero {point : Carrier}
      (hPoint : separatingMap point ≠ 0) :
      supportMap point = 1 := by
    apply hSupportOne
    exact Or.inl (subset_closure hPoint)
  have hTestRange (point : Carrier) : test point ∈ Set.Icc (-1 : ℝ) 1 := by
    by_cases hPoint : separatingMap point = 0
    · rcases hSupportRange point with ⟨hSupportLower, hSupportUpper⟩
      change -1 ≤ separatingMap point + separatingMap point - supportMap point ∧
        separatingMap point + separatingMap point - supportMap point ≤ 1
      rw [hPoint, zero_add, zero_sub]
      constructor <;> linarith
    · have hSupportOnePoint := hSupportOneOfSeparatingNonzero hPoint
      rcases hSeparatingRange point with ⟨hSeparatingLower, hSeparatingUpper⟩
      change -1 ≤ separatingMap point + separatingMap point - supportMap point ∧
        separatingMap point + separatingMap point - supportMap point ≤ 1
      rw [hSupportOnePoint]
      constructor <;> linarith
  have hTestOne : Set.EqOn test 1 positiveCompact := by
    intro point hPoint
    have hSeparating := hSeparatingOne hPoint
    have hSupport := hSupportOneOfSeparatingNonzero
      (show separatingMap point ≠ 0 by rw [hSeparating]; norm_num)
    change separatingMap point + separatingMap point - supportMap point = 1
    rw [hSeparating, hSupport]
    norm_num
  have hTestNegOne : Set.EqOn test (-1) negativeCompact := by
    intro point hPoint
    have hSeparating := hSeparatingZero hPoint
    have hSupport := hSupportOne (Or.inr hPoint)
    change separatingMap point + separatingMap point - supportMap point = -1
    rw [hSeparating, hSupport]
    norm_num
  have hPositiveIntegral :=
    measureReal_univ_sub_two_mul_compl_le_integral
      positive test positiveCompact hPositiveCompact hTestRange hTestOne
  have hNegativeIntegral :=
    integral_le_neg_measureReal_univ_add_two_mul_compl
      negative test negativeCompact hNegativeCompact hTestRange hTestNegOne
  have hIntegralLower :
      positive.real Set.univ + negative.real Set.univ -
          2 * positive.real positiveCompactᶜ -
          2 * negative.real negativeCompactᶜ ≤
        measure.continuousTestIntegral test := by
    change _ ≤
      (∫ point, test point ∂positive) -
        ∫ point, test point ∂negative
    linarith
  have hVariationReal :
      measure.toSignedMeasure.totalVariation.real Set.univ =
        positive.real Set.univ + negative.real Set.univ := by
    rw [SignedMeasure.totalVariation, measureReal_add_apply]
  have hTestIntegralStrict :
      bound < measure.continuousTestIntegral test := by
    rw [hVariationReal] at hVariationStrict
    dsimp only [epsilon] at hEpsilon hPositiveComplement hNegativeComplement
    linarith
  exact (not_lt_of_ge (hBound test fun point => abs_le.mpr (hTestRange point)))
    hTestIntegralStrict

/-- A finite total-variation sublevel is exactly the family of upper bounds against every
compactly supported continuous test bounded by one. -/
theorem totalVariation_apply_univ_le_iff_continuousTestIntegral_le
    (measure : VagueSignedMeasure Carrier) (bound : ENNReal)
    (hBound : bound ≠ ∞) :
    measure.toSignedMeasure.totalVariation Set.univ ≤ bound ↔
      ∀ test : C_c(Carrier, ℝ),
        (∀ point, |test point| ≤ 1) →
          measure.continuousTestIntegral test ≤ bound.toReal := by
  constructor
  · intro hVariation test hTest
    have hIntegral :
        measure.continuousTestIntegral test ≤
          measure.toSignedMeasure.totalVariation.real Set.univ := by
      calc
        measure.continuousTestIntegral test ≤
            |measure.continuousTestIntegral test| := le_abs_self _
        _ ≤ 1 * measure.toSignedMeasure.totalVariation.real Set.univ :=
          abs_continuousTestIntegral_le_mul_totalVariation measure test hTest
        _ = measure.toSignedMeasure.totalVariation.real Set.univ := one_mul _
    have hVariationReal :
        measure.toSignedMeasure.totalVariation.real Set.univ ≤ bound.toReal := by
      exact ENNReal.toReal_mono hBound hVariation
    exact hIntegral.trans hVariationReal
  · intro hTests
    have hVariationReal :=
      totalVariation_real_univ_le_of_continuousTestIntegral_le
        measure bound.toReal hTests
    have hVariationFinite :
        measure.toSignedMeasure.totalVariation Set.univ ≠ ∞ := by
      rw [SignedMeasure.totalVariation, Measure.add_apply]
      exact (ENNReal.add_lt_top.mpr
        ⟨measure_lt_top _ _, measure_lt_top _ _⟩).ne
    exact (ENNReal.toReal_le_toReal
      hVariationFinite
      hBound).mp hVariationReal

/-- Every finite total-variation sublevel is closed in the vague topology. -/
theorem isClosed_totalVariation_apply_univ_sublevel
    (bound : ENNReal) (hBound : bound ≠ ∞) :
    IsClosed {measure : VagueSignedMeasure Carrier |
      measure.toSignedMeasure.totalVariation Set.univ ≤ bound} := by
  have hSublevel :
      {measure : VagueSignedMeasure Carrier |
          measure.toSignedMeasure.totalVariation Set.univ ≤ bound} =
        ⋂ test : C_c(Carrier, ℝ),
          ⋂ (_hTest : ∀ point, |test point| ≤ 1),
            {measure : VagueSignedMeasure Carrier |
              measure.continuousTestIntegral test ≤ bound.toReal} := by
    ext measure
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact totalVariation_apply_univ_le_iff_continuousTestIntegral_le
      measure bound hBound
  rw [hSublevel]
  exact isClosed_iInter fun test =>
    isClosed_iInter fun _hTest =>
      isClosed_Iic.preimage (continuous_continuousTestIntegral test)

/-- Total-variation mass is lower semicontinuous for genuine vague convergence of finite signed
Borel measures.  Boundary mass may escape under this topology, so continuity is not asserted. -/
theorem lowerSemicontinuous_totalVariation_apply_univ :
    LowerSemicontinuous fun measure : VagueSignedMeasure Carrier =>
      measure.toSignedMeasure.totalVariation Set.univ := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro bound
  change IsClosed {measure : VagueSignedMeasure Carrier |
    measure.toSignedMeasure.totalVariation Set.univ ≤ bound}
  by_cases hBound : bound = ∞
  · subst bound
    simpa only [le_top, Set.ofPred_true] using
      (isClosed_univ : IsClosed (Set.univ : Set (VagueSignedMeasure Carrier)))
  · exact isClosed_totalVariation_apply_univ_sublevel bound hBound

end VagueSignedMeasure

end

end FiniteMarkovProcesses
