/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Topology.Maps.Basic

/-!
# Vague topology for finite signed measures

This module equips a type synonym of finite signed measures with the topology induced by
integration against every compactly supported continuous real test function.  Keeping the
topology on a synonym prevents it from competing with any future topology on Mathlib's underlying
`SignedMeasure` type.

The signed integral is defined through the canonical Jordan decomposition.  Both Jordan parts
are finite measures, so every compactly supported continuous test is genuinely integrable; the
definition does not rely on the Bochner integral's nonintegrable default.

## Main declarations

- `VagueSignedMeasure`: a finite signed measure carrying the vague topology;
- `VagueSignedMeasure.continuousTestIntegral`: the Jordan-decomposition signed integral;
- `VagueSignedMeasure.tendsto_iff_forall_continuousTestIntegral_tendsto`: convergence is exactly
  pointwise convergence of all compactly supported continuous test integrals;
- `VagueSignedMeasure.instMeasurableSpace`: the measurable structure is definitionally the Borel
  sigma algebra of the vague topology.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open MeasureTheory
open scoped CompactlySupported Topology

universe u

variable (Carrier : Type u) [MeasurableSpace Carrier]

/-- A finite signed measure equipped with the topology of vague convergence against compactly
supported continuous real tests. -/
def VagueSignedMeasure := SignedMeasure Carrier

namespace VagueSignedMeasure

variable {Carrier : Type u} [MeasurableSpace Carrier] [TopologicalSpace Carrier]
  [OpensMeasurableSpace Carrier]

/-- Forget the vague topology and recover the underlying finite signed measure. -/
def toSignedMeasure (measure : VagueSignedMeasure Carrier) : SignedMeasure Carrier :=
  measure

/-- Equip a finite signed measure with the vague topology. -/
def ofSignedMeasure (measure : SignedMeasure Carrier) : VagueSignedMeasure Carrier :=
  measure

omit [TopologicalSpace Carrier] [OpensMeasurableSpace Carrier] in
/-- Forgetting the vague topology after equipping a signed measure is the identity. -/
@[simp]
theorem toSignedMeasure_ofSignedMeasure (measure : SignedMeasure Carrier) :
    (ofSignedMeasure measure : VagueSignedMeasure Carrier).toSignedMeasure = measure :=
  rfl

/-- A compactly supported continuous test is integrable against the positive Jordan part. -/
theorem integrable_continuousTest_posPart
    (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ)) :
    Integrable test measure.toSignedMeasure.toJordanDecomposition.posPart :=
  test.integrable

/-- A compactly supported continuous test is integrable against the negative Jordan part. -/
theorem integrable_continuousTest_negPart
    (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ)) :
    Integrable test measure.toSignedMeasure.toJordanDecomposition.negPart :=
  test.integrable

/-- Integral of a compactly supported continuous test against a signed measure, defined as the
positive-Jordan-part integral minus the negative-Jordan-part integral. -/
noncomputable def continuousTestIntegral
    (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ)) : ℝ :=
  ∫ point, test point ∂measure.toSignedMeasure.toJordanDecomposition.posPart -
    ∫ point, test point ∂measure.toSignedMeasure.toJordanDecomposition.negPart

omit [OpensMeasurableSpace Carrier] in
/-- A uniform pointwise bound on a compactly supported test controls its signed integral by the
total-variation mass of the measure.  The bound is stated explicitly because `C_c` has no global
supremum-norm instance on a noncompact carrier. -/
theorem abs_continuousTestIntegral_le_mul_totalVariation
    (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ))
    {bound : ℝ} (hBound : ∀ point, |test point| ≤ bound) :
    |measure.continuousTestIntegral test| ≤
      bound * measure.toSignedMeasure.totalVariation.real Set.univ := by
  let positive := measure.toSignedMeasure.toJordanDecomposition.posPart
  let negative := measure.toSignedMeasure.toJordanDecomposition.negPart
  have hPositive :
      |∫ point, test point ∂positive| ≤ bound * positive.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := positive) (f := fun point => test point) (C := bound)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hBound point)
  have hNegative :
      |∫ point, test point ∂negative| ≤ bound * negative.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := negative) (f := fun point => test point) (C := bound)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hBound point)
  calc
    |measure.continuousTestIntegral test| =
        |(∫ point, test point ∂positive) -
          ∫ point, test point ∂negative| := by
      rfl
    _ ≤ |∫ point, test point ∂positive| +
        |∫ point, test point ∂negative| := abs_sub _ _
    _ ≤ bound * positive.real Set.univ +
        bound * negative.real Set.univ := add_le_add hPositive hNegative
    _ = bound * measure.toSignedMeasure.totalVariation.real Set.univ := by
      rw [SignedMeasure.totalVariation, measureReal_add_apply]
      ring

/-- Replacing a continuous test by any Jordan-integrable measurable approximation incurs at most
its uniform pointwise error times the total-variation mass.  This estimate is the signed-measure
bridge used to replace a vague test by a finite step test before evaluating interval increments. -/
theorem abs_continuousTestIntegral_sub_jordanIntegral_le_mul_totalVariation
    (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ))
    (approximation : Carrier → ℝ)
    (hApproximationPositive :
      Integrable approximation measure.toSignedMeasure.toJordanDecomposition.posPart)
    (hApproximationNegative :
      Integrable approximation measure.toSignedMeasure.toJordanDecomposition.negPart)
    {error : ℝ} (hError : ∀ point, |test point - approximation point| ≤ error) :
    |measure.continuousTestIntegral test -
        ((∫ point, approximation point
            ∂measure.toSignedMeasure.toJordanDecomposition.posPart) -
          ∫ point, approximation point
            ∂measure.toSignedMeasure.toJordanDecomposition.negPart)| ≤
      error * measure.toSignedMeasure.totalVariation.real Set.univ := by
  let positive := measure.toSignedMeasure.toJordanDecomposition.posPart
  let negative := measure.toSignedMeasure.toJordanDecomposition.negPart
  have hPositive :
      |∫ point, test point - approximation point ∂positive| ≤
        error * positive.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := positive) (f := fun point => test point - approximation point) (C := error)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hError point)
  have hNegative :
      |∫ point, test point - approximation point ∂negative| ≤
        error * negative.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const
        (μ := negative) (f := fun point => test point - approximation point) (C := error)
        (Filter.Eventually.of_forall fun point => by
          simpa only [Real.norm_eq_abs] using hError point)
  have hDifference :
      measure.continuousTestIntegral test -
          ((∫ point, approximation point ∂positive) -
            ∫ point, approximation point ∂negative) =
        (∫ point, test point - approximation point ∂positive) -
          ∫ point, test point - approximation point ∂negative := by
    unfold continuousTestIntegral
    rw [integral_sub (measure.integrable_continuousTest_posPart test)
        hApproximationPositive,
      integral_sub (measure.integrable_continuousTest_negPart test)
        hApproximationNegative]
    ring
  rw [show measure.toSignedMeasure.toJordanDecomposition.posPart = positive by rfl,
    show measure.toSignedMeasure.toJordanDecomposition.negPart = negative by rfl,
    hDifference]
  calc
    |(∫ point, test point - approximation point ∂positive) -
        ∫ point, test point - approximation point ∂negative| ≤
        |∫ point, test point - approximation point ∂positive| +
          |∫ point, test point - approximation point ∂negative| := abs_sub _ _
    _ ≤ error * positive.real Set.univ + error * negative.real Set.univ :=
      add_le_add hPositive hNegative
    _ = error * measure.toSignedMeasure.totalVariation.real Set.univ := by
      rw [SignedMeasure.totalVariation, measureReal_add_apply]
      ring

/-- Finite measurable step approximation written as a weighted sum of set indicators.  The sets
need not be disjoint; disjoint partitions are imposed only by callers that need pointwise error
control. -/
noncomputable def finiteWeightedIndicator {Index : Type*}
    (indices : Finset Index) (cell : Index → Set Carrier)
    (coefficient : Index → ℝ) : Carrier → ℝ :=
  fun point => ∑ index ∈ indices,
    (cell index).indicator (fun _ => coefficient index) point

omit [TopologicalSpace Carrier] [OpensMeasurableSpace Carrier] in
/-- A finite weighted indicator is integrable against every finite measure when all participating
sets are measurable. -/
theorem integrable_finiteWeightedIndicator {Index : Type*}
    (indices : Finset Index) (cell : Index → Set Carrier)
    (coefficient : Index → ℝ) (measure : Measure Carrier) [IsFiniteMeasure measure]
    (hCell : ∀ index ∈ indices, MeasurableSet (cell index)) :
    Integrable (finiteWeightedIndicator indices cell coefficient) measure := by
  unfold finiteWeightedIndicator
  apply integrable_finsetSum indices
  intro index hIndex
  exact IntegrableOn.integrable_indicator integrableOn_const (hCell index hIndex)

omit [TopologicalSpace Carrier] [OpensMeasurableSpace Carrier] in
/-- The Jordan signed integral of a finite measurable step approximation is the corresponding
finite weighted sum of signed set masses. -/
theorem jordanIntegral_finiteWeightedIndicator_eq_finsetSum_apply
    {Index : Type*} (measure : VagueSignedMeasure Carrier)
    (indices : Finset Index) (cell : Index → Set Carrier)
    (coefficient : Index → ℝ)
    (hCell : ∀ index ∈ indices, MeasurableSet (cell index)) :
    (∫ point, finiteWeightedIndicator indices cell coefficient point
        ∂measure.toSignedMeasure.toJordanDecomposition.posPart) -
      (∫ point, finiteWeightedIndicator indices cell coefficient point
        ∂measure.toSignedMeasure.toJordanDecomposition.negPart) =
      ∑ index ∈ indices,
        coefficient index * measure.toSignedMeasure (cell index) := by
  let positive := measure.toSignedMeasure.toJordanDecomposition.posPart
  let negative := measure.toSignedMeasure.toJordanDecomposition.negPart
  have hPositiveIntegrable (index : Index) (hIndex : index ∈ indices) :
      Integrable ((cell index).indicator (fun _ => coefficient index)) positive :=
    IntegrableOn.integrable_indicator integrableOn_const (hCell index hIndex)
  have hNegativeIntegrable (index : Index) (hIndex : index ∈ indices) :
      Integrable ((cell index).indicator (fun _ => coefficient index)) negative :=
    IntegrableOn.integrable_indicator integrableOn_const (hCell index hIndex)
  rw [show measure.toSignedMeasure.toJordanDecomposition.posPart = positive by rfl,
    show measure.toSignedMeasure.toJordanDecomposition.negPart = negative by rfl]
  unfold finiteWeightedIndicator
  rw [integral_finsetSum indices hPositiveIntegrable,
    integral_finsetSum indices hNegativeIntegrable, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index hIndex
  rw [integral_indicator_const (coefficient index) (hCell index hIndex),
    integral_indicator_const (coefficient index) (hCell index hIndex)]
  change positive.real (cell index) * coefficient index -
      negative.real (cell index) * coefficient index =
    coefficient index * measure.toSignedMeasure (cell index)
  rw [show measure.toSignedMeasure = positive.toSignedMeasure - negative.toSignedMeasure by
      change measure.toSignedMeasure =
        measure.toSignedMeasure.toJordanDecomposition.toSignedMeasure
      exact (SignedMeasure.toSignedMeasure_toJordanDecomposition measure.toSignedMeasure).symm,
    Measure.toSignedMeasure_sub_apply (hCell index hIndex)]
  ring

/-- A continuous signed test integral is uniformly approximated by the finite weighted sum of
signed masses of measurable cells whenever the associated step function uniformly approximates
the test. -/
theorem abs_continuousTestIntegral_sub_finsetSum_apply_le_mul_totalVariation
    {Index : Type*} (measure : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ))
    (indices : Finset Index) (cell : Index → Set Carrier)
    (coefficient : Index → ℝ)
    (hCell : ∀ index ∈ indices, MeasurableSet (cell index))
    {error : ℝ}
    (hError : ∀ point,
      |test point - finiteWeightedIndicator indices cell coefficient point| ≤ error) :
    |measure.continuousTestIntegral test -
        ∑ index ∈ indices,
          coefficient index * measure.toSignedMeasure (cell index)| ≤
      error * measure.toSignedMeasure.totalVariation.real Set.univ := by
  have hPositiveIntegrable := integrable_finiteWeightedIndicator
    indices cell coefficient measure.toSignedMeasure.toJordanDecomposition.posPart hCell
  have hNegativeIntegrable := integrable_finiteWeightedIndicator
    indices cell coefficient measure.toSignedMeasure.toJordanDecomposition.negPart hCell
  rw [← jordanIntegral_finiteWeightedIndicator_eq_finsetSum_apply
    measure indices cell coefficient hCell]
  exact abs_continuousTestIntegral_sub_jordanIntegral_le_mul_totalVariation
    measure test (finiteWeightedIndicator indices cell coefficient)
      hPositiveIntegrable hNegativeIntegrable hError

/-- The complete family of compactly supported continuous test integrals. -/
noncomputable def continuousTestIntegralFamily :
    VagueSignedMeasure Carrier → (C_c(Carrier, ℝ) → ℝ) :=
  fun measure test => measure.continuousTestIntegral test

/-- The vague topology is the initial topology of all compactly supported continuous test
integrals. -/
noncomputable instance instTopologicalSpace :
    TopologicalSpace (VagueSignedMeasure Carrier) :=
  TopologicalSpace.induced
    (continuousTestIntegralFamily (Carrier := Carrier)) inferInstance

/-- The measurable carrier used with vague signed measures is exactly the Borel sigma algebra of
the vague topology. -/
noncomputable instance instMeasurableSpaceVagueSignedMeasure :
    MeasurableSpace (VagueSignedMeasure Carrier) :=
  borel (VagueSignedMeasure Carrier)

/-- The declared measurable structure is the Borel sigma algebra of the vague topology. -/
instance instBorelSpace : BorelSpace (VagueSignedMeasure Carrier) :=
  ⟨rfl⟩

omit [OpensMeasurableSpace Carrier] in
/-- Borel compatibility is definitional, not a caller-supplied compatibility premise. -/
theorem measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace (VagueSignedMeasure Carrier)) =
      borel (VagueSignedMeasure Carrier) :=
  rfl

omit [OpensMeasurableSpace Carrier] in
/-- The map into the complete family of test integrals induces the vague topology. -/
theorem isInducing_continuousTestIntegralFamily :
    Topology.IsInducing (continuousTestIntegralFamily (Carrier := Carrier)) :=
  ⟨rfl⟩

omit [OpensMeasurableSpace Carrier] in
/-- Every compactly supported continuous test integral is continuous for the vague topology. -/
theorem continuous_continuousTestIntegral (test : C_c(Carrier, ℝ)) :
    Continuous fun measure : VagueSignedMeasure Carrier =>
      measure.continuousTestIntegral test := by
  have hContinuous := (continuous_apply test).comp
    (isInducing_continuousTestIntegralFamily (Carrier := Carrier)).continuous
  dsimp only [continuousTestIntegralFamily, Function.comp_def] at hContinuous
  exact hContinuous

omit [OpensMeasurableSpace Carrier] in
/-- Continuity into the vague signed-measure carrier is exactly continuity of every compactly
supported continuous test integral.  This topological criterion is stronger than a coordinatewise
measurability assertion for the uncountable test family. -/
theorem continuous_iff_continuousTestIntegral
    {Source : Type*} [TopologicalSpace Source]
    {measure : Source → VagueSignedMeasure Carrier} :
    Continuous measure ↔
      ∀ test : C_c(Carrier, ℝ),
        Continuous fun source => (measure source).continuousTestIntegral test := by
  rw [isInducing_continuousTestIntegralFamily.continuous_iff,
    continuous_pi_iff]
  rfl

/-- A signed-measure equality between two finite positive-minus-negative presentations preserves
the corresponding difference of test integrals. -/
theorem integral_sub_eq_integral_sub_of_toSignedMeasure_sub_eq
    (firstPositive firstNegative secondPositive secondNegative : Measure Carrier)
    [IsFiniteMeasure firstPositive] [IsFiniteMeasure firstNegative]
    [IsFiniteMeasure secondPositive] [IsFiniteMeasure secondNegative]
    (test : C_c(Carrier, ℝ))
    (hSigned : firstPositive.toSignedMeasure - firstNegative.toSignedMeasure =
      secondPositive.toSignedMeasure - secondNegative.toSignedMeasure) :
    (∫ point, test point ∂firstPositive) -
        ∫ point, test point ∂firstNegative =
      (∫ point, test point ∂secondPositive) -
        ∫ point, test point ∂secondNegative := by
  have hSignedSum :
      (firstPositive + secondNegative).toSignedMeasure =
        (secondPositive + firstNegative).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hSigned
  have hMeasureSum : firstPositive + secondNegative =
      secondPositive + firstNegative :=
    Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp hSignedSum
  apply sub_eq_sub_iff_add_eq_add.mpr
  rw [← integral_add_measure test.integrable test.integrable,
    ← integral_add_measure test.integrable test.integrable, hMeasureSum]

/-- The vague test integral is additive in the underlying finite signed measure. -/
theorem continuousTestIntegral_add
    (first second : VagueSignedMeasure Carrier) (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure
        (first.toSignedMeasure + second.toSignedMeasure)).continuousTestIntegral test =
      first.continuousTestIntegral test + second.continuousTestIntegral test := by
  let firstJordan := first.toSignedMeasure.toJordanDecomposition
  let secondJordan := second.toSignedMeasure.toJordanDecomposition
  let sumJordan :=
    (first.toSignedMeasure + second.toSignedMeasure).toJordanDecomposition
  have hPresentation :
      sumJordan.posPart.toSignedMeasure - sumJordan.negPart.toSignedMeasure =
        (firstJordan.posPart + secondJordan.posPart).toSignedMeasure -
          (firstJordan.negPart + secondJordan.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    change sumJordan.toSignedMeasure = _
    calc
      sumJordan.toSignedMeasure = first.toSignedMeasure + second.toSignedMeasure := by
        simp only [sumJordan,
          SignedMeasure.toSignedMeasure_toJordanDecomposition]
      _ = firstJordan.toSignedMeasure + secondJordan.toSignedMeasure := by
        simp only [firstJordan, secondJordan,
          SignedMeasure.toSignedMeasure_toJordanDecomposition]
      _ = _ := by
        unfold JordanDecomposition.toSignedMeasure
        abel
  have hIntegral := integral_sub_eq_integral_sub_of_toSignedMeasure_sub_eq
    sumJordan.posPart sumJordan.negPart
    (firstJordan.posPart + secondJordan.posPart)
    (firstJordan.negPart + secondJordan.negPart) test hPresentation
  rw [integral_add_measure test.integrable test.integrable,
    integral_add_measure test.integrable test.integrable] at hIntegral
  unfold continuousTestIntegral
  rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
  change (∫ point, test point ∂sumJordan.posPart) -
      ∫ point, test point ∂sumJordan.negPart =
    ((∫ point, test point ∂firstJordan.posPart) -
      ∫ point, test point ∂firstJordan.negPart) +
    ((∫ point, test point ∂secondJordan.posPart) -
      ∫ point, test point ∂secondJordan.negPart)
  linarith

omit [OpensMeasurableSpace Carrier] in
/-- The vague test integral is homogeneous for real scalar multiplication of the underlying
finite signed measure. -/
theorem continuousTestIntegral_smul
    (coefficient : ℝ) (measure : VagueSignedMeasure Carrier)
    (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure
        (coefficient • measure.toSignedMeasure)).continuousTestIntegral test =
      coefficient * measure.continuousTestIntegral test := by
  unfold continuousTestIntegral
  rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
    SignedMeasure.toJordanDecomposition_smul_real]
  by_cases hCoefficient : 0 ≤ coefficient
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hCoefficient,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hCoefficient,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, Real.coe_toNNReal _ hCoefficient, smul_eq_mul]
    ring
  · have hCoefficientNegative : coefficient < 0 := lt_of_not_ge hCoefficient
    rw [JordanDecomposition.real_smul_posPart_neg _ _ hCoefficientNegative,
      JordanDecomposition.real_smul_negPart_neg _ _ hCoefficientNegative,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    simp only [NNReal.smul_def,
      Real.coe_toNNReal _ (neg_nonneg.mpr hCoefficientNegative.le), smul_eq_mul]
    ring

omit [OpensMeasurableSpace Carrier] in
/-- A nonnegative finite measure, viewed as a signed measure, integrates tests by its ordinary
Bochner integral. -/
theorem continuousTestIntegral_toSignedMeasure
    (measure : Measure Carrier) [IsFiniteMeasure measure]
    (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure measure.toSignedMeasure).continuousTestIntegral test =
      ∫ point, test point ∂measure := by
  let jordan : JordanDecomposition Carrier :=
    { posPart := measure
      negPart := 0
      posPart_finite := inferInstance
      negPart_finite := inferInstance
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hJordan : measure.toSignedMeasure.toJordanDecomposition = jordan := by
    have hSigned : jordan.toSignedMeasure = measure.toSignedMeasure := by
      simp only [jordan, JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_zero, sub_zero]
    rw [← hSigned, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  unfold continuousTestIntegral
  rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure, hJordan]
  simp only [jordan, integral_zero_measure, sub_zero]

omit [OpensMeasurableSpace Carrier] in
/-- Test integration of a real multiple of a finite positive measure. -/
theorem continuousTestIntegral_smul_toSignedMeasure
    (coefficient : ℝ) (measure : Measure Carrier) [IsFiniteMeasure measure]
    (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure
        (coefficient • measure.toSignedMeasure)).continuousTestIntegral test =
      coefficient * ∫ point, test point ∂measure := by
  calc
    _ = coefficient *
        (VagueSignedMeasure.ofSignedMeasure measure.toSignedMeasure).continuousTestIntegral test :=
      continuousTestIntegral_smul coefficient
        (VagueSignedMeasure.ofSignedMeasure measure.toSignedMeasure) test
    _ = coefficient * ∫ point, test point ∂measure := by
      rw [continuousTestIntegral_toSignedMeasure]

omit [OpensMeasurableSpace Carrier] in
/-- The zero vague signed measure.  This named constructor avoids importing algebraic operations
through the topology-carrying type synonym. -/
def zero : VagueSignedMeasure Carrier :=
  VagueSignedMeasure.ofSignedMeasure 0

omit [OpensMeasurableSpace Carrier] in
/-- Addition of the underlying finite signed measures, returned to the vague carrier. -/
def add (first second : VagueSignedMeasure Carrier) : VagueSignedMeasure Carrier :=
  VagueSignedMeasure.ofSignedMeasure
    (first.toSignedMeasure + second.toSignedMeasure)

omit [OpensMeasurableSpace Carrier] in
/-- Real scalar multiplication of the underlying signed measure. -/
noncomputable def realScalarMultiple
    (coefficient : ℝ) (measure : VagueSignedMeasure Carrier) : VagueSignedMeasure Carrier :=
  VagueSignedMeasure.ofSignedMeasure (coefficient • measure.toSignedMeasure)

omit [OpensMeasurableSpace Carrier] in
/-- Test integration against the zero vague signed measure vanishes. -/
@[simp]
theorem continuousTestIntegral_zero (test : C_c(Carrier, ℝ)) :
    (zero : VagueSignedMeasure Carrier).continuousTestIntegral test = 0 := by
  rw [show (zero : VagueSignedMeasure Carrier) = VagueSignedMeasure.ofSignedMeasure
      (0 : Measure Carrier).toSignedMeasure by
    unfold zero
    congr
    simp]
  rw [continuousTestIntegral_toSignedMeasure]
  simp

/-- Test integration converts named vague addition into scalar addition. -/
@[simp]
theorem continuousTestIntegral_add' (first second : VagueSignedMeasure Carrier)
    (test : C_c(Carrier, ℝ)) :
    (add first second).continuousTestIntegral test =
      first.continuousTestIntegral test + second.continuousTestIntegral test :=
  continuousTestIntegral_add first second test

omit [OpensMeasurableSpace Carrier] in
/-- Test integration converts named real scaling into scalar multiplication. -/
@[simp]
theorem continuousTestIntegral_realScalarMultiple
    (coefficient : ℝ) (measure : VagueSignedMeasure Carrier)
    (test : C_c(Carrier, ℝ)) :
    (realScalarMultiple coefficient measure).continuousTestIntegral test =
      coefficient * measure.continuousTestIntegral test :=
  continuousTestIntegral_smul coefficient measure test

/-- Test integration commutes with a finite sum of underlying signed measures. -/
theorem continuousTestIntegral_finsetSum
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (measure : Index → VagueSignedMeasure Carrier)
    (test : C_c(Carrier, ℝ)) :
    (VagueSignedMeasure.ofSignedMeasure
      (∑ index ∈ indices, (measure index).toSignedMeasure)).continuousTestIntegral test =
        ∑ index ∈ indices, (measure index).continuousTestIntegral test := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, zero] using continuousTestIntegral_zero test
  | @insert index indices hFresh hInduction =>
      rw [Finset.sum_insert hFresh, Finset.sum_insert hFresh]
      calc
        _ = (measure index).continuousTestIntegral test +
            (VagueSignedMeasure.ofSignedMeasure
              (∑ other ∈ indices,
                (measure other).toSignedMeasure)).continuousTestIntegral test := by
          simpa only [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure] using
            continuousTestIntegral_add (measure index)
              (VagueSignedMeasure.ofSignedMeasure
                (∑ other ∈ indices, (measure other).toSignedMeasure)) test
        _ = _ := congrArg ((measure index).continuousTestIntegral test + ·) hInduction

omit [OpensMeasurableSpace Carrier] in
/-- The zero vague signed measure is a continuous constant. -/
theorem continuous_zero {Source : Type*} [TopologicalSpace Source] :
    Continuous fun _ : Source => (zero : VagueSignedMeasure Carrier) :=
  continuous_const

/-- Named addition is jointly continuous for the vague topology. -/
theorem continuous_add :
    Continuous fun pair : VagueSignedMeasure Carrier × VagueSignedMeasure Carrier =>
      add pair.1 pair.2 := by
  rw [continuous_iff_continuousTestIntegral]
  intro test
  simp only [continuousTestIntegral_add']
  exact ((continuous_continuousTestIntegral test).comp continuous_fst).add
    ((continuous_continuousTestIntegral test).comp continuous_snd)

omit [OpensMeasurableSpace Carrier] in
/-- Named real scalar multiplication is jointly continuous for the vague topology. -/
theorem continuous_realScalarMultiple :
    Continuous fun pair : ℝ × VagueSignedMeasure Carrier =>
      realScalarMultiple pair.1 pair.2 := by
  rw [continuous_iff_continuousTestIntegral]
  intro test
  simp only [continuousTestIntegral_realScalarMultiple]
  exact continuous_fst.mul
    ((continuous_continuousTestIntegral test).comp continuous_snd)

omit [OpensMeasurableSpace Carrier] in
open Filter in
/-- The defining convergence theorem for the vague topology: a net converges exactly when every
compactly supported continuous test integral converges. -/
theorem tendsto_iff_forall_continuousTestIntegral_tendsto
    {Index : Type*} {filter : Filter Index}
    {measures : Index → VagueSignedMeasure Carrier}
    {limit : VagueSignedMeasure Carrier} :
    Tendsto measures filter (𝓝 limit) ↔
      ∀ test : C_c(Carrier, ℝ),
        Tendsto
          (fun index => (measures index).continuousTestIntegral test)
          filter (𝓝 (limit.continuousTestIntegral test)) := by
  simp [isInducing_continuousTestIntegralFamily.tendsto_nhds_iff,
    tendsto_pi_nhds,
    continuousTestIntegralFamily]

end VagueSignedMeasure

end FiniteMarkovProcesses
