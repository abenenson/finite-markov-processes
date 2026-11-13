/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import FiniteMarkovProcesses.RelativeEntropy.DensityFluxLargeDeviationRepresentation
public import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensityExponentialBound
public import FiniteMarkovProcesses.Probability.FiniteStateProbabilityDensityEmpiricalApproximation

/-!
# Finite IID empirical-density large deviations

This module proves the literal closed-set upper and open-set lower large-deviation bounds for
positive finite IID samples on a finite alphabet.  The speed is the exact sample size
`successorIndex + 1`; the good rate is relative entropy against an interior reference density.
The proof is the finite method of types, including its vanishing polynomial overhead and a
deterministic rounded type approaching every point of the closed simplex.

## Main declarations

- `finiteEmpiricalTypeLogarithmicOverhead`: the finite type-count correction per sample.
- `finiteIIDEmpiricalProbabilityDensityLaw_closedUpperBound`.
- `finiteIIDEmpiricalProbabilityDensityLaw_openLowerBound`.
- `finiteStateProbabilityDensityRelativeEntropy_isGoodRateFunction`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

/-- Exact polynomial type-count logarithmic correction per positive sample. -/
def finiteEmpiricalTypeLogarithmicOverhead
    (stateCount successorIndex : ℕ) : ℝ :=
  (stateCount : ℝ) * Real.log (successorIndex + 2 : ℝ) /
    (successorIndex + 1 : ℝ)

/-- The polynomial number of finite empirical types contributes zero on the exponential scale. -/
theorem finiteEmpiricalTypeLogarithmicOverhead_tendsto_zero (stateCount : ℕ) :
    Tendsto (finiteEmpiricalTypeLogarithmicOverhead stateCount) atTop (nhds 0) := by
  have hArgument :
      Tendsto (fun successorIndex : ℕ => (successorIndex + 2 : ℝ)) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2) :
        Tendsto (fun successorIndex : ℕ => ((successorIndex + 2 : ℕ) : ℝ)) atTop atTop)
  have hBase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hArgument
  have hScaled := hBase.const_mul (stateCount : ℝ)
  convert hScaled using 1
  · funext successorIndex
    unfold finiteEmpiricalTypeLogarithmicOverhead
    dsimp
    ring_nf
  · simp

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Exact sample-size speed for the successor-indexed positive IID laws. -/
def finiteIIDPositiveSampleSpeed (successorIndex : ℕ) : ℝ :=
  ((successorIndex + 1 : ℕ) : ℝ)

/-- The speed is strictly positive at every successor index. -/
theorem finiteIIDPositiveSampleSpeed_pos (successorIndex : ℕ) :
    0 < finiteIIDPositiveSampleSpeed successorIndex := by
  unfold finiteIIDPositiveSampleSpeed
  positivity

/-- The positive-sample speed diverges. -/
theorem finiteIIDPositiveSampleSpeed_tendsto_atTop :
    Tendsto finiteIIDPositiveSampleSpeed atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- Finite-sample upper bound after applying extended logarithm and dividing by the exact sample
size.  The only residual is the explicit polynomial type-count overhead. -/
theorem scaledEventLogProbability_finiteIIDEmpiricalProbabilityDensityLaw_upperBound
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event)
    (rateLowerBound : ℝ)
    (hRate : ∀ density ∈ event,
      rateLowerBound ≤ finiteStateProbabilityDensityRelativeEntropyReal reference density) :
    scaledEventLogProbability
        (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
          reference.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex event ≤
      (finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex -
        rateLowerBound : ℝ) := by
  have hProbability :=
    finiteIIDEmpiricalProbabilityDensityLaw_upperBound_of_rate_le
      reference hReference successorIndex hEvent rateLowerBound hRate
  unfold scaledEventLogProbability finiteIIDPositiveSampleSpeed
  change
    (finiteIIDEmpiricalProbabilityDensityLaw successorIndex
      reference.probabilityMassFunction event).log /
        ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) ≤ _
  refine (EReal.monotone_div_right_of_nonneg
    (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
    (ENNReal.log_monotone hProbability)).trans_eq ?_
  have hPolynomialPos :
      0 < ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) := by
    positivity
  rw [ENNReal.log_mul_add]
  rw [show ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal)) =
      ENNReal.ofReal ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) by
        exact (ENNReal.ofReal_natCast _).symm]
  change
    (ENNReal.log (ENNReal.ofReal
        ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ))) +
      ENNReal.log (ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) * rateLowerBound)))) /
      ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) = _
  rw [ENNReal.log_ofReal_of_pos hPolynomialPos,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  rw [show ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) =
      (successorIndex + 2 : ℝ) ^ Fintype.card State by norm_num,
    Real.log_pow]
  rw [← EReal.coe_add, ← EReal.coe_div]
  norm_cast
  unfold finiteEmpiricalTypeLogarithmicOverhead
  push_cast
  field_simp
  ring

/-- Finite-sample lower bound after applying extended logarithm and dividing by the exact sample
size.  It is valid whenever one selected count type lies in the event. -/
theorem scaledEventLogProbability_finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    {event : Set (FiniteStateProbabilityDensity State)} (hEvent : MeasurableSet event)
    (hEmpiricalType : empiricalType.probabilityDensity ∈ event) :
    (-(finiteStateProbabilityDensityRelativeEntropyReal reference
        empiricalType.probabilityDensity) -
      finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex : ℝ) ≤
      scaledEventLogProbability
        (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
          reference.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex event := by
  have hProbability :=
    finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem
      reference hReference successorIndex empiricalType hEvent hEmpiricalType
  unfold scaledEventLogProbability finiteIIDPositiveSampleSpeed
  change _ ≤
    (finiteIIDEmpiricalProbabilityDensityLaw successorIndex
      reference.probabilityMassFunction event).log /
        ((((successorIndex + 1 : ℕ) : ℝ) : EReal))
  refine le_trans ?_ (EReal.monotone_div_right_of_nonneg
    (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
    (ENNReal.log_monotone hProbability))
  have hPolynomialPos :
      0 < ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) := by
    positivity
  rw [ENNReal.log_ofReal_of_pos
    (div_pos (Real.exp_pos _) hPolynomialPos), Real.log_div (Real.exp_pos _).ne',
    Real.log_exp]
  rw [show ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) =
      (successorIndex + 2 : ℝ) ^ Fintype.card State by norm_num,
    Real.log_pow]
  dsimp only
  rw [← EReal.coe_div]
  norm_cast
  unfold finiteEmpiricalTypeLogarithmicOverhead
  push_cast
  · field_simp
    exact le_rfl
  · exact ne_of_gt hPolynomialPos

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The extended relative-entropy rate embeds into `EReal` as its literal real formula. -/
theorem finiteStateProbabilityDensityRelativeEntropy_coe_ereal
    (reference density : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    ((finiteStateProbabilityDensityRelativeEntropy reference density : ENNReal) : EReal) =
      (finiteStateProbabilityDensityRelativeEntropyReal reference density : EReal) := by
  simp [finiteStateProbabilityDensityRelativeEntropy,
    finiteStateProbabilityDensityRelativeEntropyReal_nonneg reference density hReference]

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Relative entropy against an interior finite reference is a good rate function on the compact
closed probability simplex. -/
theorem finiteStateProbabilityDensityRelativeEntropy_isGoodRateFunction
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    IsGoodRateFunction (finiteStateProbabilityDensityRelativeEntropy reference) := by
  intro bound
  apply IsCompact.of_isClosed_subset isCompact_univ
    (isClosed_le
      (continuous_finiteStateProbabilityDensityRelativeEntropy reference hReference)
      continuous_const)
  exact Set.subset_univ _

/-- The empirical density of positive finite IID samples satisfies the literal large-deviation
upper bound on every closed finite-simplex event. -/
theorem finiteIIDEmpiricalProbabilityDensityLaw_closedUpperBound
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun successorIndex => finiteIIDEmpiricalProbabilityDensityLaw successorIndex
          reference.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (finiteStateProbabilityDensityRelativeEntropy reference) := by
  intro closedSet hClosedSet
  rcases closedSet.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst closedSet
    simp [scaledEventLogProbability]
    rw [show (fun sampleSize => (⊥ : EReal) /
        (finiteIIDPositiveSampleSpeed sampleSize : EReal)) =
        (fun _ => (⊥ : EReal)) by
      funext sampleSize
      exact EReal.bot_div_of_pos_ne_top
        (EReal.coe_pos.mpr (finiteIIDPositiveSampleSpeed_pos sampleSize))
        (EReal.coe_ne_top _)]
    simp
  obtain ⟨minimizingDensity, hMinimizingDensity, hMinimum⟩ :=
    hClosedSet.isCompact.exists_isMinOn hNonempty
      (continuous_finiteStateProbabilityDensityRelativeEntropyReal
        reference hReference).continuousOn
  have hUpper (successorIndex : ℕ) :
      scaledEventLogProbability
          (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
            reference.probabilityMassFunction)
          (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedSet ≤
        (finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex -
          finiteStateProbabilityDensityRelativeEntropyReal reference minimizingDensity : ℝ) :=
    scaledEventLogProbability_finiteIIDEmpiricalProbabilityDensityLaw_upperBound
      reference hReference successorIndex hClosedSet.measurableSet
      (finiteStateProbabilityDensityRelativeEntropyReal reference minimizingDensity)
      hMinimum
  have hUpperLimit :
      Tendsto
        (fun successorIndex =>
          (finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex -
            finiteStateProbabilityDensityRelativeEntropyReal reference minimizingDensity : ℝ) :
            ℕ → EReal)
        atTop
        (nhds
          ((-finiteStateProbabilityDensityRelativeEntropyReal
            reference minimizingDensity : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using
      (finiteEmpiricalTypeLogarithmicOverhead_tendsto_zero
        (Fintype.card State)).sub
          (tendsto_const_nhds : Tendsto
            (fun _ : ℕ => finiteStateProbabilityDensityRelativeEntropyReal
              reference minimizingDensity) atTop _)
  have hInfimum :
      (⨅ density ∈ closedSet,
        ((finiteStateProbabilityDensityRelativeEntropy reference density : ENNReal) : EReal)) =
          (finiteStateProbabilityDensityRelativeEntropyReal
            reference minimizingDensity : EReal) := by
    apply le_antisymm
    · calc
        (⨅ density ∈ closedSet,
            ((finiteStateProbabilityDensityRelativeEntropy reference density : ENNReal) :
              EReal)) ≤
            ((finiteStateProbabilityDensityRelativeEntropy
              reference minimizingDensity : ENNReal) : EReal) :=
          le_trans (iInf_le _ minimizingDensity)
            (iInf_le_of_le hMinimizingDensity le_rfl)
        _ = _ := finiteStateProbabilityDensityRelativeEntropy_coe_ereal
          reference minimizingDensity hReference
    · apply le_iInf
      intro density
      apply le_iInf
      intro hDensity
      rw [finiteStateProbabilityDensityRelativeEntropy_coe_ereal
        reference density hReference]
      exact_mod_cast hMinimum hDensity
  calc
    Filter.limsup
        (fun successorIndex =>
          scaledEventLogProbability
            (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
              reference.probabilityMassFunction)
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedSet)
        atTop ≤
      Filter.limsup
        (fun successorIndex =>
          (finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex -
            finiteStateProbabilityDensityRelativeEntropyReal reference minimizingDensity : ℝ) :
            ℕ → EReal)
        atTop := Filter.limsup_le_limsup (Eventually.of_forall hUpper)
    _ = ((-finiteStateProbabilityDensityRelativeEntropyReal
        reference minimizingDensity : ℝ) : EReal) := hUpperLimit.limsup_eq
    _ = -(⨅ density ∈ closedSet,
        ((finiteStateProbabilityDensityRelativeEntropy reference density : ENNReal) : EReal)) := by
      rw [hInfimum, ← EReal.coe_neg]

/-- The empirical density of positive finite IID samples satisfies the literal large-deviation
lower bound on every open finite-simplex event. -/
theorem finiteIIDEmpiricalProbabilityDensityLaw_openLowerBound
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    HasLargeDeviationLowerBound
      (scaledEventLogProbability
        (fun successorIndex => finiteIIDEmpiricalProbabilityDensityLaw successorIndex
          reference.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (finiteStateProbabilityDensityRelativeEntropy reference) := by
  intro openSet hOpenSet
  rw [show -(⨅ path ∈ openSet,
      ((finiteStateProbabilityDensityRelativeEntropy reference path : ENNReal) : EReal)) =
        ⨆ path, ⨆ (_ : path ∈ openSet),
          -((finiteStateProbabilityDensityRelativeEntropy reference path : ENNReal) : EReal) by
    exact EReal.negOrderIso.map_iInf₂ _]
  apply iSup_le
  intro density
  apply iSup_le
  intro hDensity
  let roundedDensity : ℕ → FiniteStateProbabilityDensity State :=
    finiteStateRoundedEmpiricalProbabilityDensity density
  have hRoundedDensity : Tendsto roundedDensity atTop (nhds density) :=
    finiteStateProbabilityDensityRoundedPositiveEmpiricalType_probabilityDensity_tendsto density
  have hEventuallyMem : ∀ᶠ successorIndex in atTop, roundedDensity successorIndex ∈ openSet :=
    hRoundedDensity.eventually (hOpenSet.mem_nhds hDensity)
  have hLower : ∀ᶠ successorIndex in atTop,
      (-(finiteStateProbabilityDensityRelativeEntropyReal reference
          (roundedDensity successorIndex)) -
        finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex : ℝ) ≤
        scaledEventLogProbability
          (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
            reference.probabilityMassFunction)
          (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex openSet := by
    filter_upwards [hEventuallyMem] with successorIndex hSuccessorIndex
    exact
      scaledEventLogProbability_finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem
        reference hReference successorIndex
        (finiteStateProbabilityDensityRoundedPositiveEmpiricalType density successorIndex)
        hOpenSet.measurableSet (by
          simpa [roundedDensity, finiteStateRoundedEmpiricalProbabilityDensity] using
            hSuccessorIndex)
  have hRateLimit :
      Tendsto
        (fun successorIndex =>
          finiteStateProbabilityDensityRelativeEntropyReal reference
            (roundedDensity successorIndex))
        atTop
        (nhds (finiteStateProbabilityDensityRelativeEntropyReal reference density)) :=
    (continuous_finiteStateProbabilityDensityRelativeEntropyReal
      reference hReference).tendsto density |>.comp hRoundedDensity
  have hLowerLimit :
      Tendsto
        (fun successorIndex =>
          (-(finiteStateProbabilityDensityRelativeEntropyReal reference
              (roundedDensity successorIndex)) -
            finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex : ℝ) :
            ℕ → EReal)
        atTop
        (nhds
          ((-finiteStateProbabilityDensityRelativeEntropyReal reference density : ℝ) :
            EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using hRateLimit.neg.sub
      (finiteEmpiricalTypeLogarithmicOverhead_tendsto_zero (Fintype.card State))
  calc
    -((finiteStateProbabilityDensityRelativeEntropy reference density : ENNReal) : EReal) =
        ((-finiteStateProbabilityDensityRelativeEntropyReal reference density : ℝ) :
          EReal) := by
      rw [finiteStateProbabilityDensityRelativeEntropy_coe_ereal
        reference density hReference, ← EReal.coe_neg]
    _ = Filter.liminf
        (fun successorIndex =>
          (-(finiteStateProbabilityDensityRelativeEntropyReal reference
              (roundedDensity successorIndex)) -
            finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) successorIndex : ℝ) :
            ℕ → EReal)
        atTop := hLowerLimit.liminf_eq.symm
    _ ≤ Filter.liminf
        (fun successorIndex =>
          scaledEventLogProbability
            (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
              reference.probabilityMassFunction)
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex openSet)
        atTop := Filter.liminf_le_liminf hLower

end

end FiniteMarkovProcesses.Probability
