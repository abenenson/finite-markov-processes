/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalTypeExponentialBound

/-!
# Finite-event exponential bounds for empirical probability densities

This module aggregates the exact empirical-type atom estimates over an arbitrary measurable
event in the finite probability simplex.  It gives the finite-sample upper estimate needed by
the closed-set half of the finite-alphabet method of types, while preserving the exact count-type
law beneath the simplex observation.

No asymptotic limit or large-deviation principle is asserted here.

## Main declarations

- `finiteIIDEmpiricalProbabilityDensityLaw_apply_eq_sum_types`: exact event decomposition.
- `finiteIIDEmpiricalProbabilityDensityLaw_upperBound_of_rate_le`: uniform exponential event
  bound from a real lower bound on relative entropy.
- `finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem`: one-type exponential lower
  bound for any event containing its normalized density.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Count types whose normalized densities lie in a selected simplex event. -/
noncomputable def finiteIIDEmpiricalProbabilityDensityEventTypes
    (successorIndex : ℕ) (event : Set (FiniteStateProbabilityDensity State)) :
    Finset (FiniteIIDPositiveEmpiricalType State successorIndex) := by
  classical
  exact Finset.univ.filter fun empiricalType => empiricalType.probabilityDensity ∈ event

/-- Membership in the finite collection of count types over an event is literal membership of
the normalized empirical density in that event. -/
@[simp]
theorem mem_finiteIIDEmpiricalProbabilityDensityEventTypes
    (successorIndex : ℕ) (event : Set (FiniteStateProbabilityDensity State))
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    empiricalType ∈ finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event ↔
      empiricalType.probabilityDensity ∈ event := by
  classical
  simp [finiteIIDEmpiricalProbabilityDensityEventTypes]

variable [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A measurable simplex event has probability equal to the sum of the exact count-type atoms
whose normalized densities lie in the event. -/
theorem finiteIIDEmpiricalProbabilityDensityLaw_apply_eq_sum_types
    (successorIndex : ℕ) (law : PMF State)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event) :
    finiteIIDEmpiricalProbabilityDensityLaw successorIndex law event =
      ∑ empiricalType ∈
          finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event,
        finiteIIDPositiveEmpiricalTypeLaw successorIndex law {empiricalType} := by
  classical
  rw [← map_probabilityDensity_finiteIIDPositiveEmpiricalTypeLaw,
    Measure.map_apply (measurable_of_finite _) hEvent]
  have hPreimage :
      FiniteIIDPositiveEmpiricalType.probabilityDensity ⁻¹' event =
        (finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event :
          Set (FiniteIIDPositiveEmpiricalType State successorIndex)) := by
    ext empiricalType
    simp
  rw [hPreimage, ← sum_measure_singleton]

/-- If relative entropy is bounded below by `rateLowerBound` throughout an event, its empirical
probability is bounded by the polynomial number of types times the corresponding exponential.
The estimate is finite-sample and remains valid for empty events and boundary empirical types. -/
theorem finiteIIDEmpiricalProbabilityDensityLaw_upperBound_of_rate_le
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event)
    (rateLowerBound : ℝ)
    (hRate : ∀ density ∈ event,
      rateLowerBound ≤ finiteStateProbabilityDensityRelativeEntropyReal reference density) :
    finiteIIDEmpiricalProbabilityDensityLaw successorIndex
        reference.probabilityMassFunction event ≤
      (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal) *
        ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * rateLowerBound)) := by
  classical
  rw [finiteIIDEmpiricalProbabilityDensityLaw_apply_eq_sum_types
    successorIndex reference.probabilityMassFunction hEvent]
  calc
    (∑ empiricalType ∈
        finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event,
          finiteIIDPositiveEmpiricalTypeLaw successorIndex
            reference.probabilityMassFunction {empiricalType}) ≤
        ∑ _empiricalType ∈
          finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event,
          ENNReal.ofReal
            (Real.exp (-(successorIndex + 1 : ℝ) * rateLowerBound)) := by
      apply Finset.sum_le_sum
      intro empiricalType hEmpiricalType
      refine (finiteIIDPositiveEmpiricalTypeProbability_upperBound
        reference hReference successorIndex empiricalType).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left
        (hRate empiricalType.probabilityDensity
          ((mem_finiteIIDEmpiricalProbabilityDensityEventTypes
            successorIndex event empiricalType).mp hEmpiricalType))
        (neg_nonpos.mpr (by positivity))
    _ = (finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event).card *
          ENNReal.ofReal
            (Real.exp (-(successorIndex + 1 : ℝ) * rateLowerBound)) := by
      simp [nsmul_eq_mul]
    _ ≤ (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal) *
          ENNReal.ofReal
            (Real.exp (-(successorIndex + 1 : ℝ) * rateLowerBound)) := by
      gcongr
      exact_mod_cast (Finset.card_le_univ
        (finiteIIDEmpiricalProbabilityDensityEventTypes successorIndex event)).trans
          (by simpa [Nat.card_eq_fintype_card] using
            card_finiteIIDPositiveEmpiricalType_le (State := State) successorIndex)

/-- The exact atom of any empirical type whose normalized density lies in an event is bounded
above by the probability of the entire event. -/
theorem finiteIIDPositiveEmpiricalTypeLaw_apply_singleton_le_density_event
    (successorIndex : ℕ) (law : PMF State)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event)
    (hEmpiricalType : empiricalType.probabilityDensity ∈ event) :
    finiteIIDPositiveEmpiricalTypeLaw successorIndex law {empiricalType} ≤
      finiteIIDEmpiricalProbabilityDensityLaw successorIndex law event := by
  classical
  rw [finiteIIDEmpiricalProbabilityDensityLaw_apply_eq_sum_types
    successorIndex law hEvent]
  exact Finset.single_le_sum
    (fun candidate _hCandidate =>
      (zero_le : 0 ≤ finiteIIDPositiveEmpiricalTypeLaw successorIndex law {candidate}))
    ((mem_finiteIIDEmpiricalProbabilityDensityEventTypes
      successorIndex event empiricalType).mpr hEmpiricalType)

/-- A measurable event containing one empirical type has at least that type's relative-entropy
exponential probability, including the exact polynomial method-of-types denominator. -/
theorem finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event)
    (hEmpiricalType : empiricalType.probabilityDensity ∈ event) :
    ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) *
          finiteStateProbabilityDensityRelativeEntropyReal reference
            empiricalType.probabilityDensity) /
          (((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) ≤
      finiteIIDEmpiricalProbabilityDensityLaw successorIndex
        reference.probabilityMassFunction event := by
  exact (finiteIIDPositiveEmpiricalTypeProbability_lowerBound
    reference hReference successorIndex empiricalType).trans
      (finiteIIDPositiveEmpiricalTypeLaw_apply_singleton_le_density_event
        successorIndex reference.probabilityMassFunction empiricalType hEvent hEmpiricalType)

end

end FiniteMarkovProcesses.Probability
