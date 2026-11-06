/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpReversalLaw

/-!
# Partial-conjugate laws of finite-state Markov jump processes

This module defines a positive stationary distribution, the stationary adjoint of a finite-state
generator, and the partial-conjugate auxiliary associated with a directed transition mask. It
then constructs the auxiliary forward law and its literal complete-history reversal.

The reversed comparison is deliberately retained as a pushforward law. A partial-conjugate
auxiliary need not preserve the source stationary distribution, so no time-homogeneous reversed
generator is asserted without an additional theorem.

## Main Results

- `FiniteStateMarkovStationaryDistribution`: positive normalized stationary weights.
- `FiniteStateMarkovGenerator.stationaryAdjointGenerator`: the stationary adjoint generator.
- `FiniteStateMarkovGenerator.partialConjugateGenerator`: retain masked rates and adjoint all
  complementary rates.
- `FiniteStateMarkovGenerator.haveSameDirectedSupport_partialConjugateGenerator`: exact common
  directed support under reversal-closed source support.
- `finiteStateMarkovPartialConjugateForwardProbabilityMeasure`: normalized auxiliary law.
- `finiteStateMarkovPartialConjugateComparisonProbabilityMeasure`: normalized literal reversal
  of the auxiliary law on the same complete-history carrier.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State]

/-- Strictly positive normalized stationary weights for a finite-state Markov generator. -/
structure FiniteStateMarkovStationaryDistribution
    (generator : FiniteStateMarkovGenerator State) where
  /-- Stationary state weight. -/
  weight : State → ℝ≥0
  /-- Every stationary state weight is strictly positive. -/
  weight_pos : ∀ state, 0 < weight state
  /-- The stationary weights have total mass one. -/
  sum_weight : ∑ state, weight state = 1
  /-- Incoming stationary flow equals escape flow at every state. -/
  balance : ∀ state,
    weight state * generator.escapeRate state =
      ∑ source, weight source * generator.rate source state

namespace FiniteStateMarkovStationaryDistribution

/-- The probability mass function represented by positive stationary weights. -/
noncomputable def pmf {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) : PMF State :=
  PMF.ofFintype (fun state => (stationary.weight state : ℝ≥0∞)) (by
    simpa using congrArg (fun weight : ℝ≥0 => (weight : ℝ≥0∞))
      stationary.sum_weight)

/-- Evaluation of the stationary PMF recovers the corresponding stationary weight. -/
@[simp]
theorem pmf_apply {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) (state : State) :
    stationary.pmf state = stationary.weight state := by
  simp [pmf]

/-- The stationary PMF has full point support. -/
theorem pmf_ne_zero {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) (state : State) :
    stationary.pmf state ≠ 0 := by
  rw [pmf_apply]
  exact_mod_cast (stationary.weight_pos state).ne'

/-- Every stationary PMF weight has strictly positive real value. -/
theorem pmf_toReal_pos {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) (state : State) :
    0 < (stationary.pmf state).toReal := by
  rw [pmf_apply, ENNReal.coe_toReal]
  exact_mod_cast stationary.weight_pos state

end FiniteStateMarkovStationaryDistribution

namespace FiniteStateMarkovGenerator

/-- A directed support is closed under edge reversal. -/
def HasReversalClosedDirectedSupport
    (generator : FiniteStateMarkovGenerator State) : Prop :=
  ∀ source target,
    generator.rate source target = 0 ↔ generator.rate target source = 0

/-- A directed transition mask is closed under edge reversal. -/
def IsReversalClosedMask (observed : State → State → Prop) : Prop :=
  ∀ source target, observed source target ↔ observed target source

/-- Stationary adjoint of a finite-state generator. -/
noncomputable def stationaryAdjointGenerator
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    FiniteStateMarkovGenerator State where
  rate source target :=
    stationary.weight target * generator.rate target source /
      stationary.weight source
  rate_self state := by
    simp [generator.rate_self]

/-- A stationary-adjoint rate vanishes exactly when the reversed source rate vanishes. -/
theorem stationaryAdjointGenerator_rate_eq_zero_iff
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (source target : State) :
    (generator.stationaryAdjointGenerator stationary).rate source target = 0 ↔
      generator.rate target source = 0 := by
  rw [stationaryAdjointGenerator]
  simp only
  rw [div_eq_zero_iff]
  simp [stationary.weight_pos source |>.ne',
    stationary.weight_pos target |>.ne']

/-- The stationary adjoint has the same escape rate as the source generator. -/
theorem stationaryAdjointGenerator_escapeRate
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator) (state : State) :
    (generator.stationaryAdjointGenerator stationary).escapeRate state =
      generator.escapeRate state := by
  unfold escapeRate stationaryAdjointGenerator
  rw [← Finset.sum_div, ← stationary.balance state]
  exact mul_div_cancel_left₀ _ (stationary.weight_pos state).ne'

/-- The same stationary weights are stationary for the stationary adjoint. -/
noncomputable def stationaryAdjointDistribution
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    FiniteStateMarkovStationaryDistribution
      (generator.stationaryAdjointGenerator stationary) where
  weight := stationary.weight
  weight_pos := stationary.weight_pos
  sum_weight := stationary.sum_weight
  balance state := by
    rw [stationaryAdjointGenerator_escapeRate]
    unfold stationaryAdjointGenerator
    have hTerm (source : State) :
        stationary.weight source *
            (stationary.weight state * generator.rate state source /
              stationary.weight source) =
          stationary.weight state * generator.rate state source := by
      field_simp [(stationary.weight_pos source).ne']
    simp_rw [hTerm]
    rw [← Finset.mul_sum]
    rfl

/-- Partial-conjugate auxiliary generator for a directed observed-transition mask. Observed
rates are retained; every complementary rate is replaced by its stationary adjoint. -/
noncomputable def partialConjugateGenerator
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] :
    FiniteStateMarkovGenerator State where
  rate source target :=
    if observed source target then generator.rate source target
    else (generator.stationaryAdjointGenerator stationary).rate source target
  rate_self state := by
    split_ifs <;> simp [stationaryAdjointGenerator, generator.rate_self]

/-- The partial-conjugate auxiliary retains every observed rate literally. -/
@[simp]
theorem partialConjugateGenerator_rate_of_observed
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    {source target : State} (hObserved : observed source target) :
    (generator.partialConjugateGenerator stationary observed).rate source target =
      generator.rate source target := by
  simp [partialConjugateGenerator, hObserved]

/-- On an unobserved edge, the partial-conjugate rate is the stationary adjoint rate. -/
@[simp]
theorem partialConjugateGenerator_rate_of_not_observed
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    {source target : State} (hObserved : ¬ observed source target) :
    (generator.partialConjugateGenerator stationary observed).rate source target =
      stationary.weight target * generator.rate target source /
        stationary.weight source := by
  simp [partialConjugateGenerator, stationaryAdjointGenerator, hObserved]

/-- Under a reversal-closed mask, the rate assigned to a reversed edge has the corresponding
observed or stationary-adjoint form. -/
theorem partialConjugateGenerator_rate_reverse
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (hMask : IsReversalClosedMask observed) (source target : State) :
    (generator.partialConjugateGenerator stationary observed).rate target source =
      if observed source target then generator.rate target source
      else stationary.weight source * generator.rate source target /
        stationary.weight target := by
  by_cases hObserved : observed source target
  · have hReverse : observed target source := (hMask source target).mp hObserved
    simp [partialConjugateGenerator, hObserved, hReverse]
  · have hReverse : ¬ observed target source := by
      exact fun h => hObserved ((hMask source target).mpr h)
    simp [partialConjugateGenerator, stationaryAdjointGenerator, hObserved, hReverse]

/-- Reversal-closed source support gives literal common directed support between the source and
its partial-conjugate auxiliary. -/
theorem haveSameDirectedSupport_partialConjugateGenerator
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (hSupport : generator.HasReversalClosedDirectedSupport) :
    generator.HaveSameDirectedSupport
      (generator.partialConjugateGenerator stationary observed) := by
  intro source target
  by_cases hObserved : observed source target
  · simp [partialConjugateGenerator, hObserved]
  · rw [partialConjugateGenerator_rate_of_not_observed
      generator stationary observed hObserved]
    rw [div_eq_zero_iff]
    simp [stationary.weight_pos source |>.ne',
      stationary.weight_pos target |>.ne', hSupport source target]

/-- A reversed partial-conjugate edge vanishes exactly when the corresponding forward source
edge vanishes. -/
theorem partialConjugateGenerator_reverse_rate_eq_zero_iff
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (hSupport : generator.HasReversalClosedDirectedSupport)
    (source target : State) :
    (generator.partialConjugateGenerator stationary observed).rate target source = 0 ↔
      generator.rate source target = 0 :=
  (generator.haveSameDirectedSupport_partialConjugateGenerator
      stationary observed hSupport target source).symm.trans
    (hSupport source target).symm

/-- A reversed partial-conjugate edge is positive exactly when the corresponding forward source
edge is positive. -/
theorem partialConjugateGenerator_reverse_rate_pos_iff
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (hSupport : generator.HasReversalClosedDirectedSupport)
    (source target : State) :
    0 < (generator.partialConjugateGenerator stationary observed).rate target source ↔
      0 < generator.rate source target := by
  simp only [pos_iff_ne_zero]
  exact not_congr <|
    generator.partialConjugateGenerator_reverse_rate_eq_zero_iff
      stationary observed hSupport source target

end FiniteStateMarkovGenerator

/-- Forward density measure of the partial-conjugate auxiliary. -/
noncomputable def finiteStateMarkovPartialConjugateForwardDensityMeasure
    [MeasurableSpace State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  finiteStateMarkovJumpDensityMeasure stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T

/-- Normalized forward probability law of the partial-conjugate auxiliary. -/
noncomputable def finiteStateMarkovPartialConjugateForwardProbabilityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (T : ℝ) (hT : 0 ≤ T) : ProbabilityMeasure (FiniteJumpHistory State) :=
  finiteStateMarkovJumpProbabilityMeasure stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative stationary.pmf
      (generator.partialConjugateGenerator stationary observed) T hT)

/-- The forward probability promotion has the exact auxiliary density measure underneath. -/
@[simp]
theorem finiteStateMarkovPartialConjugateForwardProbabilityMeasure_toMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (T : ℝ) (hT : 0 ≤ T) :
    (finiteStateMarkovPartialConjugateForwardProbabilityMeasure
      generator stationary observed T hT).toMeasure =
      finiteStateMarkovPartialConjugateForwardDensityMeasure
        generator stationary observed T :=
  rfl

/-- Comparison density measure obtained by complete-history reversal of the auxiliary law. -/
noncomputable def finiteStateMarkovPartialConjugateComparisonDensityMeasure
    [MeasurableSpace State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  finiteStateMarkovJumpReversalDensityMeasure stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T

/-- A partial-conjugate comparison density measure is sigma-finite. -/
noncomputable instance instSigmaFiniteFiniteStateMarkovPartialConjugateComparisonDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] (T : ℝ) :
    SigmaFinite (finiteStateMarkovPartialConjugateComparisonDensityMeasure
      generator stationary observed T) := by
  unfold finiteStateMarkovPartialConjugateComparisonDensityMeasure
  infer_instance

/-- Normalized comparison probability law: the literal reversal pushforward of the normalized
partial-conjugate forward law. -/
noncomputable def finiteStateMarkovPartialConjugateComparisonProbabilityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (T : ℝ) (hT : 0 ≤ T) : ProbabilityMeasure (FiniteJumpHistory State) :=
  finiteStateMarkovJumpReversalProbabilityMeasure stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T hT

/-- The comparison probability promotion has the exact reversal density measure underneath. -/
@[simp]
theorem finiteStateMarkovPartialConjugateComparisonProbabilityMeasure_toMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (T : ℝ) (hT : 0 ≤ T) :
    (finiteStateMarkovPartialConjugateComparisonProbabilityMeasure
      generator stationary observed T hT).toMeasure =
      finiteStateMarkovPartialConjugateComparisonDensityMeasure
        generator stationary observed T :=
  rfl

/-- The comparison density is exactly the reversed auxiliary density against the unchanged
counting--Lebesgue history base. -/
theorem finiteStateMarkovPartialConjugateComparisonDensityMeasure_eq_withDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] (T : ℝ) :
    finiteStateMarkovPartialConjugateComparisonDensityMeasure
        generator stationary observed T =
      (finiteJumpHistoryBaseMeasure State T).withDensity
        (finiteStateMarkovJumpDensityENNReal stationary.pmf
          (generator.partialConjugateGenerator stationary observed) T ∘
            FiniteJumpHistory.reverse T) :=
  finiteStateMarkovJumpReversalDensityMeasure_eq_withDensity
    stationary.pmf (generator.partialConjugateGenerator stationary observed) T

/-- The comparison law has total mass one at every nonnegative horizon. -/
theorem finiteStateMarkovPartialConjugateComparisonDensityMeasure_univ
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed]
    (T : ℝ) (hT : 0 ≤ T) :
    finiteStateMarkovPartialConjugateComparisonDensityMeasure
      generator stationary observed T Set.univ = 1 :=
  finiteStateMarkovJumpReversalDensityMeasure_univ stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T hT

/-- The comparison law remains concentrated on the identical fixed-horizon physical carrier. -/
theorem ae_physicalAt_finiteStateMarkovPartialConjugateComparisonDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (observed : State → State → Prop) [DecidableRel observed] (T : ℝ) :
    ∀ᵐ history ∂finiteStateMarkovPartialConjugateComparisonDensityMeasure
        generator stationary observed T,
      history.PhysicalAt T :=
  ae_physicalAt_finiteStateMarkovJumpReversalDensityMeasure stationary.pmf
    (generator.partialConjugateGenerator stationary observed) T

end FiniteMarkovProcesses.Probability
