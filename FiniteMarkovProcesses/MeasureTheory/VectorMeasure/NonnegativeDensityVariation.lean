/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Total variation of integrable signed densities

This module records the elementary bridge from an integrable real density, viewed as a signed
vector-measure density, to its positive total-variation measure.  It makes the total-variation
mass available as the usual nonnegative Lebesgue integral of the absolute density.  The
nonnegative specialization is retained as a convenient physical-flow interface.

## Main declarations

- `SignedMeasure.totalVariation_toSignedMeasure`: a finite positive measure has itself as total
  variation when viewed as a signed measure.
- `SignedMeasure.totalVariation_smul_apply_univ`: real scaling multiplies total-variation mass by
  the absolute scalar.
- `SignedMeasure.ofReal_abs_apply_le_totalVariation`: the absolute mass of any measurable set is
  bounded by its total-variation mass.
- `SignedMeasure.totalVariation_withDensityᵥ_eq_withDensity_ofReal_abs`: an integrable measurable
  signed density has the expected absolute-density total-variation measure.
- `SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs`: its total mass is
  the nonnegative Lebesgue integral of the absolute density.
- `SignedMeasure.totalVariation_withDensityᵥ_eq_withDensity_of_ae_nonnegative`: a nonnegative
  integrable signed density has the expected positive total-variation measure.
- `SignedMeasure.zero_le_withDensityᵥ_of_ae_nonnegative`: a nonnegative integrable real density
  induces a nonnegative signed measure.
- `SignedMeasure.rnDeriv_nonnegative_of_zero_le`: the Radon--Nikodym derivative of a nonnegative
  signed measure is almost everywhere nonnegative.
- `SignedMeasure.rnDeriv_fintypeSum`: Radon--Nikodym derivatives commute almost everywhere with
  finite indexed sums of signed measures.
- `SignedMeasure.totalVariation_fintypeSum_apply_univ_le`: the total variation of a finite sum is
  bounded by the sum of the component total variations.
- `SignedMeasure.totalVariation_withDensityᵥ_apply_univ`: its total mass is the nonnegative
  Lebesgue integral of the density.
-/

@[expose] public section

namespace MeasureTheory

open scoped ENNReal

universe u

noncomputable section

variable {Carrier : Type u} [MeasurableSpace Carrier]

namespace SignedMeasure

/-- The absolute mass assigned by a signed measure to a measurable set is bounded by the
total-variation mass of that set. -/
theorem ofReal_abs_apply_le_totalVariation
    (measure : SignedMeasure Carrier) {set : Set Carrier} (hSet : MeasurableSet set) :
    ENNReal.ofReal |measure set| ≤ measure.totalVariation set := by
  have hApply :
      measure set =
        (measure.toJordanDecomposition.posPart set).toReal -
          (measure.toJordanDecomposition.negPart set).toReal := by
    conv_lhs => rw [← toSignedMeasure_toJordanDecomposition measure]
    rw [JordanDecomposition.toSignedMeasure, _root_.sub_apply,
      Measure.toSignedMeasure_apply_measurable hSet,
      Measure.toSignedMeasure_apply_measurable hSet, measureReal_def, measureReal_def]
  rw [hApply, totalVariation, Measure.add_apply]
  have hPositive :
      0 ≤ (measure.toJordanDecomposition.posPart set).toReal :=
    ENNReal.toReal_nonneg
  have hNegative :
      0 ≤ (measure.toJordanDecomposition.negPart set).toReal :=
    ENNReal.toReal_nonneg
  have hAbsoluteValue :
      |(measure.toJordanDecomposition.posPart set).toReal -
          (measure.toJordanDecomposition.negPart set).toReal| ≤
        (measure.toJordanDecomposition.posPart set).toReal +
          (measure.toJordanDecomposition.negPart set).toReal := by
    simpa [abs_of_nonneg hPositive, abs_of_nonneg hNegative] using
      abs_sub (measure.toJordanDecomposition.posPart set).toReal
        (measure.toJordanDecomposition.negPart set).toReal
  calc
    ENNReal.ofReal
        |(measure.toJordanDecomposition.posPart set).toReal -
          (measure.toJordanDecomposition.negPart set).toReal| ≤
      ENNReal.ofReal
        ((measure.toJordanDecomposition.posPart set).toReal +
          (measure.toJordanDecomposition.negPart set).toReal) :=
      ENNReal.ofReal_le_ofReal hAbsoluteValue
    _ = measure.toJordanDecomposition.posPart set +
        measure.toJordanDecomposition.negPart set := by
      rw [ENNReal.ofReal_add hPositive hNegative,
        ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A finite positive measure, viewed as a signed measure, has the original measure as its total
variation. -/
theorem totalVariation_toSignedMeasure
    (measure : Measure Carrier) [IsFiniteMeasure measure] :
    measure.toSignedMeasure.totalVariation = measure := by
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
  rw [SignedMeasure.totalVariation, hJordan]
  simp only [jordan, add_zero]

/-- Real scalar multiplication scales total-variation mass by the absolute scalar. -/
theorem totalVariation_smul_apply_univ
    (coefficient : ℝ) (signedMeasure : SignedMeasure Carrier) :
    (coefficient • signedMeasure).totalVariation Set.univ =
      ENNReal.ofReal |coefficient| * signedMeasure.totalVariation Set.univ := by
  rw [SignedMeasure.totalVariation,
    SignedMeasure.toJordanDecomposition_smul_real]
  by_cases hCoefficient : 0 ≤ coefficient
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hCoefficient,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hCoefficient]
    simp [SignedMeasure.totalVariation, abs_of_nonneg hCoefficient,
      Real.toNNReal_of_nonneg hCoefficient,
      ENNReal.ofReal_eq_coe_nnreal hCoefficient, mul_add]
  · have hCoefficientNegative : coefficient < 0 := lt_of_not_ge hCoefficient
    rw [JordanDecomposition.real_smul_posPart_neg _ _ hCoefficientNegative,
      JordanDecomposition.real_smul_negPart_neg _ _ hCoefficientNegative]
    simp [SignedMeasure.totalVariation, abs_of_neg hCoefficientNegative,
      Real.toNNReal_of_nonneg (neg_nonneg.mpr hCoefficientNegative.le),
      ENNReal.ofReal_eq_coe_nnreal
        (neg_nonneg.mpr hCoefficientNegative.le), mul_add]
    exact add_comm _ _

/-- The total variation of an integrable measurable real density is the positive measure with
Radon--Nikodym density given by its absolute value. -/
theorem totalVariation_withDensityᵥ_eq_withDensity_ofReal_abs
    {measure : Measure Carrier} {density : Carrier → ℝ}
    (hDensityMeasurable : Measurable density)
    (hDensityIntegrable : Integrable density measure) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) =
      measure.withDensity fun point => ENNReal.ofReal |density point| := by
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.2
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (-density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.neg.2
  let jordan : JordanDecomposition Carrier :=
    { posPart := measure.withDensity fun point => ENNReal.ofReal (density point)
      negPart := measure.withDensity fun point => ENNReal.ofReal (-density point)
      posPart_finite := inferInstance
      negPart_finite := inferInstance
      mutuallySingular := withDensity_ofReal_mutuallySingular hDensityMeasurable }
  have hJordan :
      SignedMeasure.toJordanDecomposition
          (measure.withDensityᵥ density : SignedMeasure Carrier) = jordan := by
    apply toJordanDecomposition_eq
    exact (withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part
      hDensityIntegrable).trans rfl
  rw [SignedMeasure.totalVariation, hJordan]
  ext measurableSet hMeasurableSet
  rw [Measure.coe_add, Pi.add_apply]
  simp only [jordan]
  rw [withDensity_apply _ hMeasurableSet, withDensity_apply _ hMeasurableSet,
    withDensity_apply _ hMeasurableSet]
  rw [← lintegral_add_left'
    hDensityMeasurable.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro point
  by_cases hPoint : 0 ≤ density point
  · simp [abs_of_nonneg hPoint, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hPoint)]
  · have hPointNonpositive : density point ≤ 0 := le_of_not_ge hPoint
    simp [abs_of_nonpos hPointNonpositive, ENNReal.ofReal_eq_zero.mpr hPointNonpositive]

/-- The total-variation mass of an integrable measurable signed density is the nonnegative
Lebesgue integral of its absolute value. -/
theorem totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs
    {measure : Measure Carrier} {density : Carrier → ℝ}
    (hDensityMeasurable : Measurable density)
    (hDensityIntegrable : Integrable density measure) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) Set.univ =
      ∫⁻ point, ENNReal.ofReal |density point| ∂measure := by
  rw [totalVariation_withDensityᵥ_eq_withDensity_ofReal_abs
    hDensityMeasurable hDensityIntegrable]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp

/-- On every measurable event, the total variation of an integrable signed density is the
restricted nonnegative integral of its absolute value. -/
theorem totalVariation_withDensityᵥ_apply_eq_setLIntegral_ofReal_abs
    {measure : Measure Carrier} {density : Carrier → ℝ} {event : Set Carrier}
    (hDensityMeasurable : Measurable density)
    (hDensityIntegrable : Integrable density measure)
    (hEvent : MeasurableSet event) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) event =
      ∫⁻ point in event, ENNReal.ofReal |density point| ∂measure := by
  rw [totalVariation_withDensityᵥ_eq_withDensity_ofReal_abs
    hDensityMeasurable hDensityIntegrable]
  exact withDensity_apply _ hEvent

private theorem withDensityᵥ_eq_toSignedMeasure_withDensity_of_ae_nonnegative
    {measure : Measure Carrier} {density : Carrier → ℝ}
    [IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (density point))]
    [IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (-density point))]
    (hDensityIntegrable : Integrable density measure)
    (hDensityNonnegative : ∀ᵐ point ∂measure, 0 ≤ density point) :
    (measure.withDensityᵥ density : SignedMeasure Carrier) =
      (measure.withDensity fun point => ENNReal.ofReal (density point)).toSignedMeasure := by
  have hNegativeDensityZero :
      measure.withDensity (fun point => ENNReal.ofReal (-density point)) = 0 := by
    calc
      measure.withDensity (fun point => ENNReal.ofReal (-density point)) =
          measure.withDensity (fun _point => 0) := by
        apply withDensity_congr_ae
        filter_upwards [hDensityNonnegative] with point hPoint
        exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hPoint)
      _ = 0 := by simp
  have hNegativeSignedDensityZero :
      (measure.withDensity fun point => ENNReal.ofReal (-density point)).toSignedMeasure = 0 := by
    calc
      (measure.withDensity fun point => ENNReal.ofReal (-density point)).toSignedMeasure =
          (0 : Measure Carrier).toSignedMeasure :=
        Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr hNegativeDensityZero
      _ = 0 := Measure.toSignedMeasure_zero
  calc
    (measure.withDensityᵥ density : SignedMeasure Carrier) =
        (measure.withDensity fun point => ENNReal.ofReal (density point)).toSignedMeasure -
          (measure.withDensity fun point =>
            ENNReal.ofReal (-density point)).toSignedMeasure :=
      withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hDensityIntegrable
    _ = (measure.withDensity fun point =>
        ENNReal.ofReal (density point)).toSignedMeasure := by
      rw [hNegativeSignedDensityZero, sub_zero]

/-- A nonnegative integrable real density induces a nonnegative signed measure. -/
theorem zero_le_withDensityᵥ_of_ae_nonnegative
    {measure : Measure Carrier} {density : Carrier → ℝ}
    (hDensityIntegrable : Integrable density measure)
    (hDensityNonnegative : ∀ᵐ point ∂measure, 0 ≤ density point) :
    0 ≤ (measure.withDensityᵥ density : SignedMeasure Carrier) := by
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.2
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (-density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.neg.2
  rw [withDensityᵥ_eq_toSignedMeasure_withDensity_of_ae_nonnegative
    hDensityIntegrable hDensityNonnegative]
  exact Measure.zero_le_toSignedMeasure _

/-- The Radon--Nikodym derivative of a nonnegative finite signed measure is almost everywhere
nonnegative with respect to every reference measure. -/
theorem rnDeriv_nonnegative_of_zero_le
    (signedMeasure : SignedMeasure Carrier) (reference : Measure Carrier)
    (hNonnegative : 0 ≤ signedMeasure) :
    ∀ᵐ point ∂reference, 0 ≤ signedMeasure.rnDeriv reference point := by
  have hNonnegativeOn : 0 ≤[Set.univ] signedMeasure :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hNonnegative
  let positiveMeasure := signedMeasure.toMeasureOfZeroLE
    Set.univ MeasurableSet.univ hNonnegativeOn
  let positiveJordan : JordanDecomposition Carrier :=
    { posPart := positiveMeasure
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hRepresentation : signedMeasure = positiveJordan.toSignedMeasure := by
    calc
      signedMeasure = positiveMeasure.toSignedMeasure :=
        (SignedMeasure.toMeasureOfZeroLE_toSignedMeasure
          signedMeasure hNonnegativeOn).symm
      _ = positiveJordan.toSignedMeasure := by
        simp [positiveJordan, JordanDecomposition.toSignedMeasure]
  have hJordan : signedMeasure.toJordanDecomposition = positiveJordan :=
    SignedMeasure.toJordanDecomposition_eq hRepresentation
  rw [SignedMeasure.rnDeriv_def, hJordan]
  change ∀ᵐ point ∂reference,
    0 ≤ (positiveMeasure.rnDeriv reference point).toReal -
      ((0 : Measure Carrier).rnDeriv reference point).toReal
  filter_upwards [Measure.rnDeriv_zero reference] with point hZero
  change (0 : Measure Carrier).rnDeriv reference point = (0 : ENNReal) at hZero
  rw [hZero, ENNReal.toReal_zero, sub_zero]
  exact ENNReal.toReal_nonneg

/-- The Radon--Nikodym derivative of a finite sum of signed measures is almost everywhere the sum
of their Radon--Nikodym derivatives. -/
theorem rnDeriv_fintypeSum
    {Index : Type*} [Fintype Index]
    (signedMeasures : Index → SignedMeasure Carrier)
    (reference : Measure Carrier) [SigmaFinite reference] :
    (∑ index, signedMeasures index).rnDeriv reference =ᵐ[reference]
      fun point => ∑ index, (signedMeasures index).rnDeriv reference point := by
  classical
  have hFiniteSum (indices : Finset Index) :
      (∑ index ∈ indices, signedMeasures index).rnDeriv reference =ᵐ[reference]
        fun point => ∑ index ∈ indices,
          (signedMeasures index).rnDeriv reference point := by
    induction indices using Finset.induction_on with
    | empty =>
        filter_upwards [Measure.rnDeriv_zero reference] with point hZero
        change (0 : Measure Carrier).rnDeriv reference point = (0 : ENNReal) at hZero
        simp only [Finset.sum_empty]
        rw [SignedMeasure.rnDeriv_def, SignedMeasure.toJordanDecomposition_zero]
        change ((0 : Measure Carrier).rnDeriv reference point).toReal -
          ((0 : Measure Carrier).rnDeriv reference point).toReal = 0
        rw [hZero]
        simp
    | @insert index indices hIndex ih =>
        filter_upwards [SignedMeasure.rnDeriv_add (signedMeasures index)
            (∑ candidate ∈ indices, signedMeasures candidate) reference,
          ih] with point hAdd hInduction
        simp only [Finset.sum_insert hIndex]
        simpa only [Pi.add_apply, hInduction] using hAdd
  simpa using hFiniteSum Finset.univ

/-- The total-variation mass of a finite sum of signed measures is bounded by the sum of the
component total-variation masses. -/
theorem totalVariation_fintypeSum_apply_univ_le
    {Index : Type*} [Fintype Index]
    (signedMeasures : Index → SignedMeasure Carrier) :
    (∑ index, signedMeasures index).totalVariation Set.univ ≤
      ∑ index, (signedMeasures index).totalVariation Set.univ := by
  classical
  let (index : Index) : IsFiniteMeasure (signedMeasures index).totalVariation :=
    IsFiniteMeasure.mk (by
      rw [SignedMeasure.totalVariation, Measure.add_apply]
      exact ENNReal.add_lt_top.mpr
        ⟨measure_lt_top _ _, measure_lt_top _ _⟩)
  let reference : Measure Carrier :=
    ∑ index, (signedMeasures index).totalVariation
  let : IsFiniteMeasure reference := inferInstance
  have hComponentAbsolutelyContinuous (index : Index) :
      signedMeasures index ≪ᵥ reference.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    apply Measure.absolutelyContinuous_of_le
    dsimp only [reference]
    exact Finset.single_le_sum
      (fun candidate (_hCandidate : candidate ∈ Finset.univ) =>
        Measure.zero_le ((signedMeasures candidate).totalVariation))
      (Finset.mem_univ index)
  have hSumAbsolutelyContinuous :
      (∑ index, signedMeasures index) ≪ᵥ reference.toENNRealVectorMeasure := by
    exact Finset.sum_induction signedMeasures
      (fun measure => measure ≪ᵥ reference.toENNRealVectorMeasure)
      (fun _left _right hLeft hRight =>
        VectorMeasure.AbsolutelyContinuous.add hLeft hRight)
      (VectorMeasure.AbsolutelyContinuous.zero _)
      (fun index _hIndex => hComponentAbsolutelyContinuous index)
  have hSumRepresentation :
      reference.withDensityᵥ
          ((∑ index, signedMeasures index).rnDeriv reference) =
        ∑ index, signedMeasures index :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hSumAbsolutelyContinuous
  have hComponentRepresentation (index : Index) :
      reference.withDensityᵥ ((signedMeasures index).rnDeriv reference) =
        signedMeasures index :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
      (hComponentAbsolutelyContinuous index)
  calc
    (∑ index, signedMeasures index).totalVariation Set.univ =
        (SignedMeasure.totalVariation
          (reference.withDensityᵥ
            ((∑ index, signedMeasures index).rnDeriv reference))) Set.univ := by
      rw [hSumRepresentation]
    _ = ∫⁻ point, ENNReal.ofReal
          |(∑ index, signedMeasures index).rnDeriv reference point| ∂reference :=
      SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs
        (SignedMeasure.measurable_rnDeriv _ _)
        (SignedMeasure.integrable_rnDeriv _ _)
    _ ≤ ∫⁻ point, ∑ index,
          ENNReal.ofReal
            |(signedMeasures index).rnDeriv reference point| ∂reference := by
      apply lintegral_mono_ae
      filter_upwards [SignedMeasure.rnDeriv_fintypeSum signedMeasures reference] with point hPoint
      rw [hPoint]
      calc
        ENNReal.ofReal
            |∑ index, (signedMeasures index).rnDeriv reference point| ≤
            ENNReal.ofReal
              (∑ index,
                |(signedMeasures index).rnDeriv reference point|) := by
          apply ENNReal.ofReal_le_ofReal
          simpa only [Real.norm_eq_abs] using
            norm_sum_le Finset.univ
              (fun index =>
                (signedMeasures index).rnDeriv reference point)
        _ = ∑ index,
              ENNReal.ofReal
                |(signedMeasures index).rnDeriv reference point| := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro index _hIndex
          exact abs_nonneg _
    _ = ∑ index, ∫⁻ point,
          ENNReal.ofReal
            |(signedMeasures index).rnDeriv reference point| ∂reference := by
      rw [lintegral_finsetSum']
      intro index _hIndex
      simpa only [Real.norm_eq_abs] using
        ((SignedMeasure.measurable_rnDeriv
          (signedMeasures index) reference).norm.ennreal_ofReal).aemeasurable
    _ = ∑ index, (signedMeasures index).totalVariation Set.univ := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      have hVariation :=
        SignedMeasure.totalVariation_withDensityᵥ_apply_univ_eq_lintegral_ofReal_abs
          (SignedMeasure.measurable_rnDeriv (signedMeasures index) reference)
          (SignedMeasure.integrable_rnDeriv (signedMeasures index) reference)
      rw [hComponentRepresentation index] at hVariation
      exact hVariation.symm

/-- A nonnegative integrable real density induces the corresponding positive measure when viewed
through signed total variation. -/
theorem totalVariation_withDensityᵥ_eq_withDensity_of_ae_nonnegative
    {measure : Measure Carrier} {density : Carrier → ℝ}
    (hDensityIntegrable : Integrable density measure)
    (hDensityNonnegative : ∀ᵐ point ∂measure, 0 ≤ density point) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) =
      measure.withDensity fun point => ENNReal.ofReal (density point) := by
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.2
  let : IsFiniteMeasure
      (measure.withDensity fun point => ENNReal.ofReal (-density point)) :=
    isFiniteMeasure_withDensity_ofReal hDensityIntegrable.neg.2
  rw [withDensityᵥ_eq_toSignedMeasure_withDensity_of_ae_nonnegative
    hDensityIntegrable hDensityNonnegative, totalVariation_toSignedMeasure]

/-- The total-variation mass of a nonnegative integrable signed density is its nonnegative
Lebesgue integral. -/
theorem totalVariation_withDensityᵥ_apply_univ
    {measure : Measure Carrier} {density : Carrier → ℝ}
    (hDensityIntegrable : Integrable density measure)
    (hDensityNonnegative : ∀ᵐ point ∂measure, 0 ≤ density point) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) Set.univ =
      ∫⁻ point, ENNReal.ofReal (density point) ∂measure := by
  rw [totalVariation_withDensityᵥ_eq_withDensity_of_ae_nonnegative
    hDensityIntegrable hDensityNonnegative]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp

/-- On every measurable event, a nonnegative integrable signed density has total variation equal
to its restricted nonnegative integral. -/
theorem totalVariation_withDensityᵥ_apply_eq_setLIntegral
    {measure : Measure Carrier} {density : Carrier → ℝ} {event : Set Carrier}
    (hDensityIntegrable : Integrable density measure)
    (hDensityNonnegative : ∀ᵐ point ∂measure, 0 ≤ density point)
    (hEvent : MeasurableSet event) :
    SignedMeasure.totalVariation (measure.withDensityᵥ density) event =
      ∫⁻ point in event, ENNReal.ofReal (density point) ∂measure := by
  rw [totalVariation_withDensityᵥ_eq_withDensity_of_ae_nonnegative
    hDensityIntegrable hDensityNonnegative]
  exact withDensity_apply _ hEvent

end SignedMeasure

end

end MeasureTheory
