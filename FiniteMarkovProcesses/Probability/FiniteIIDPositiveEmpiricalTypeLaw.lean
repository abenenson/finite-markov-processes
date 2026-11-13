/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalType
public import FiniteMarkovProcesses.Probability.FiniteMultinomialEmpiricalMode

/-!
# Law of a positive finite IID empirical count type

This module pushes a positive finite IID sample law to its exact integer count type.  Every type
atom is computed by its multinomial fibre cardinal times the common probability of any word in
that fibre.  Mapping the count type to its normalized simplex point recovers the existing
empirical probability-density law exactly.

No exponential estimate or large-deviation limit is asserted here.

## Main declarations

- `finiteIIDPositiveEmpiricalTypeLaw`: exact count-type pushforward law.
- `finiteIIDPositiveEmpiricalTypeLaw_apply_singleton`: exact multinomial atom formula.
- `finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_probabilityDensity`: real atom formula.
- `finiteIIDPositiveEmpiricalType_ownProbability_isGreatest`: the owned type is a mode.
- `finiteIIDPositiveEmpiricalType_ownProbability_ge_polynomial_inv`: exact polynomial lower bound.
- `map_probabilityDensity_finiteIIDPositiveEmpiricalTypeLaw`: recovery of the simplex law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Empirical count types use their discrete measurable structure. -/
instance instMeasurableSpaceFiniteIIDPositiveEmpiricalType {successorIndex : ℕ} :
    MeasurableSpace (FiniteIIDPositiveEmpiricalType State successorIndex) :=
  ⊤

/-- Every empirical count-type singleton is measurable. -/
instance instMeasurableSingletonClassFiniteIIDPositiveEmpiricalType
    {successorIndex : ℕ} :
    MeasurableSingletonClass (FiniteIIDPositiveEmpiricalType State successorIndex) := by
  infer_instance

/-- The exact pushforward law of the empirical integer count type. -/
def finiteIIDPositiveEmpiricalTypeLaw
    (successorIndex : ℕ) (law : PMF State) :
    Measure (FiniteIIDPositiveEmpiricalType State successorIndex) :=
  Measure.map (finiteIIDPositiveSampleEmpiricalType successorIndex)
    (finiteIIDPositiveSampleLaw successorIndex law)

/-- The empirical count-type law is exactly normalized. -/
instance instIsProbabilityMeasureFiniteIIDPositiveEmpiricalTypeLaw
    (successorIndex : ℕ) (law : PMF State) :
    IsProbabilityMeasure (finiteIIDPositiveEmpiricalTypeLaw successorIndex law) := by
  unfold finiteIIDPositiveEmpiricalTypeLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (μ := finiteIIDPositiveSampleLaw successorIndex law)
    (f := finiteIIDPositiveSampleEmpiricalType successorIndex)
    (measurable_of_finite _).aemeasurable).2 inferInstance

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every IID sample word's coordinate product equals the product of state masses raised to the
corresponding empirical counts. -/
theorem finiteIIDPositiveSampleProbability_eq_prod_state_pow_count
    (successorIndex : ℕ) (law : PMF State)
    (sample : Fin (successorIndex + 1) → State) :
    (∏ replica, law (sample replica)) =
      ∏ state, law state ^
        finiteIIDPositiveSampleStateCount successorIndex sample state := by
  rw [← Finset.prod_fiberwise' Finset.univ sample law]
  apply Finset.prod_congr rfl
  intro state _hState
  simp [finiteIIDPositiveSampleStateCount]

/-- Exact atom formula for one empirical count type: multinomial fibre cardinal times the common
IID probability of every word in that fibre. -/
theorem finiteIIDPositiveEmpiricalTypeLaw_apply_singleton
    (successorIndex : ℕ) (law : PMF State)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    finiteIIDPositiveEmpiricalTypeLaw successorIndex law {empiricalType} =
      (Nat.multinomial Finset.univ
        (fun state => (empiricalType.count state : ℕ)) : ENNReal) *
        ∏ state, law state ^ (empiricalType.count state : ℕ) := by
  classical
  rw [finiteIIDPositiveEmpiricalTypeLaw, Measure.map_apply
    (measurable_of_finite _) (MeasurableSet.singleton _)]
  let fibre := Finset.univ.filter fun sample =>
    finiteIIDPositiveSampleEmpiricalType successorIndex sample = empiricalType
  have hFibreSet :
      finiteIIDPositiveSampleEmpiricalType successorIndex ⁻¹' {empiricalType} =
        (fibre : Set (Fin (successorIndex + 1) → State)) := by
    ext sample
    simp [fibre]
  rw [hFibreSet, ← sum_measure_singleton]
  have hAtom (sample : Fin (successorIndex + 1) → State)
      (hSample : sample ∈ fibre) :
      finiteIIDPositiveSampleLaw successorIndex law {sample} =
        ∏ state, law state ^ (empiricalType.count state : ℕ) := by
    rw [finiteIIDPositiveSampleLaw_apply_singleton,
      finiteIIDPositiveSampleProbability_eq_prod_state_pow_count]
    apply Finset.prod_congr rfl
    intro state _hState
    have hType :
        finiteIIDPositiveSampleEmpiricalType successorIndex sample = empiricalType :=
      (Finset.mem_filter.mp hSample).2
    have hCount := congrArg
      (fun candidate : FiniteIIDPositiveEmpiricalType State successorIndex =>
        (candidate.count state : ℕ)) hType
    exact congrArg (fun count : ℕ => law state ^ count) hCount
  have hSum :
      (∑ sample ∈ fibre, finiteIIDPositiveSampleLaw successorIndex law {sample}) =
        ∑ _sample ∈ fibre,
          ∏ state, law state ^ (empiricalType.count state : ℕ) := by
    apply Finset.sum_congr rfl
    intro sample hSample
    exact hAtom sample hSample
  rw [hSum, Finset.sum_const]
  simp only [nsmul_eq_mul]
  have hCard :
      fibre.card = Nat.multinomial Finset.univ
        (fun state => (empiricalType.count state : ℕ)) := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun sample => by simp [fibre]))).trans
      (finiteIIDPositiveSampleEmpiricalType_fiber_card empiricalType)
  rw [hCard]

/-- The real value of an empirical-type atom under a finite probability density is its literal
multinomial probability. -/
theorem finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_probabilityDensity
    (successorIndex : ℕ) (density : FiniteStateProbabilityDensity State)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    (finiteIIDPositiveEmpiricalTypeLaw successorIndex
      density.probabilityMassFunction {empiricalType}).toReal =
      (Nat.multinomial Finset.univ
        (fun state => (empiricalType.count state : ℕ)) : ℝ) *
        ∏ state, (density.weight state : ℝ) ^
          (empiricalType.count state : ℕ) := by
  rw [finiteIIDPositiveEmpiricalTypeLaw_apply_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod]
  apply congrArg ((Nat.multinomial Finset.univ
    (fun state => (empiricalType.count state : ℕ)) : ℝ) * ·)
  apply Finset.prod_congr rfl
  intro state _hState
  rw [ENNReal.toReal_pow,
    FiniteStateProbabilityDensity.probabilityMassFunction_apply,
    ENNReal.coe_toReal]

/-- The real value of an empirical-type atom under the law normalized from another empirical
type is its literal multinomial probability. -/
theorem finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_own
    (successorIndex : ℕ)
    (empiricalType candidateType :
      FiniteIIDPositiveEmpiricalType State successorIndex) :
    (finiteIIDPositiveEmpiricalTypeLaw successorIndex
      empiricalType.probabilityMassFunction {candidateType}).toReal =
      (Nat.multinomial Finset.univ
        (fun state => (candidateType.count state : ℕ)) : ℝ) *
        ∏ state,
          (((empiricalType.count state : ℕ) : ℝ) /
            (successorIndex + 1 : ℝ)) ^ (candidateType.count state : ℕ) := by
  rw [show empiricalType.probabilityMassFunction =
      empiricalType.probabilityDensity.probabilityMassFunction from rfl,
    finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_probabilityDensity]
  congr 1

/-- An empirical type maximizes the exact multinomial type probability when the IID law is its
own normalized count vector. -/
theorem finiteIIDPositiveEmpiricalType_ownProbability_isGreatest
    (successorIndex : ℕ)
    (empiricalType candidateType :
      FiniteIIDPositiveEmpiricalType State successorIndex) :
    finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {candidateType} ≤
      finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {empiricalType} := by
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_own,
    finiteIIDPositiveEmpiricalTypeLaw_toReal_apply_singleton_own]
  simpa [Nat.cast_add, Nat.cast_one] using
    multinomialEmpiricalProbabilityReal_le_self
    (successorIndex + 1) (by omega)
    (fun state => (empiricalType.count state : ℕ))
    (fun state => (candidateType.count state : ℕ))
    empiricalType.sum_count candidateType.sum_count

/-- The empirical type's own multinomial probability is at least the reciprocal of the exact
number of possible empirical types.  This uses only normalization and the exact mode theorem. -/
theorem finiteIIDPositiveEmpiricalType_ownProbability_ge_card_inv
    (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal)⁻¹ ≤
      finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {empiricalType} := by
  let : Nonempty (FiniteIIDPositiveEmpiricalType State successorIndex) :=
    ⟨empiricalType⟩
  let empiricalTypeMeasure :=
    finiteIIDPositiveEmpiricalTypeLaw successorIndex
      empiricalType.probabilityMassFunction
  have hNormalizedMode :
      (1 : ENNReal) ≤
        (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
          empiricalTypeMeasure {empiricalType} := by
    calc
      (1 : ENNReal) = empiricalTypeMeasure Set.univ := by
        simp [empiricalTypeMeasure]
      _ = ∑ candidate : FiniteIIDPositiveEmpiricalType State successorIndex,
          empiricalTypeMeasure {candidate} := by
        rw [sum_measure_singleton]
        simp
      _ ≤ ∑ _candidate : FiniteIIDPositiveEmpiricalType State successorIndex,
          empiricalTypeMeasure {empiricalType} :=
        Finset.sum_le_sum fun candidate _hCandidate =>
          finiteIIDPositiveEmpiricalType_ownProbability_isGreatest
            successorIndex empiricalType candidate
      _ = (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
          empiricalTypeMeasure {empiricalType} := by
        simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  rw [inv_eq_one_div]
  exact (ENNReal.div_le_iff
    (by exact_mod_cast (Nat.card_pos :
      0 < Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex)).ne')
    (ENNReal.natCast_ne_top _)).mpr (by simpa [mul_comm] using hNormalizedMode)

/-- The empirical type's own multinomial probability has the explicit method-of-types lower
bound `(sampleSize + 1) ^ (-|State|)`.  No Stirling estimate enters. -/
theorem finiteIIDPositiveEmpiricalType_ownProbability_ge_polynomial_inv
    (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal)⁻¹ ≤
      finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {empiricalType} := by
  calc
    (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal)⁻¹ ≤
        (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by
        exact_mod_cast card_finiteIIDPositiveEmpiricalType_le
          (State := State) successorIndex)
    _ ≤ finiteIIDPositiveEmpiricalTypeLaw successorIndex
        empiricalType.probabilityMassFunction {empiricalType} :=
      finiteIIDPositiveEmpiricalType_ownProbability_ge_card_inv
        successorIndex empiricalType

/-- Mapping exact count types to their normalized simplex points recovers the empirical
probability-density law without loss. -/
theorem map_probabilityDensity_finiteIIDPositiveEmpiricalTypeLaw
    (successorIndex : ℕ) (law : PMF State) :
    Measure.map FiniteIIDPositiveEmpiricalType.probabilityDensity
        (finiteIIDPositiveEmpiricalTypeLaw successorIndex law) =
      finiteIIDEmpiricalProbabilityDensityLaw successorIndex law := by
  unfold finiteIIDPositiveEmpiricalTypeLaw
    finiteIIDEmpiricalProbabilityDensityLaw
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  congr 1

end

end FiniteMarkovProcesses.Probability
