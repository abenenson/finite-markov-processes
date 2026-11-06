/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVCompleteRate
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovInvariantIIDInitialLDP
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateSublevelCompactness

/-!
# Compact complete-rate sublevels for the Renger hybrid-BV action

This module combines compact dynamic-rate sublevels with an independently good initial-simplex
rate.  The separately recovered initial trace becomes continuous after restriction to one finite
dynamic-rate sublevel, so the initial plus dynamic complete action is lower semicontinuous there.
Its finite sublevels are consequently closed subsets of compact dynamic sublevels.
-/

namespace FiniteMarkovProcesses.InformationTheory

open _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Every member of a genuinely finite dynamic-rate sublevel is admissible. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevelPath_admissible
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level) :
    RengerDirectionalFlowHybridBVAdmissible path.1 hDuration :=
  (rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet
    generator hDuration hLevel path.2).1

/-- Initial simplex point recovered continuously on one finite dynamic-rate sublevel. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateInitialProbabilityDensity
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) (hLevel : level < ∞)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level) :
    FiniteStateProbabilityDensity State where
  weight := rengerDirectionalFlowHybridBVInitialDensity path.1
  sum_weight := by
    have hPath := rengerDirectionalFlowHybridBVFiniteRateSublevelPath_admissible
      generator hDuration hLevel path
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_one,
      rengerDirectionalFlowHybridBVInitialDensity]
    simp_rw [Real.coe_toNNReal _ (hPath.initialDensityNonnegative _)]
    exact hPath.initialDensityNormalized

/-- Initial-simplex recovery is continuous on every genuinely finite dynamic-rate sublevel. -/
theorem continuous_rengerDirectionalFlowHybridBVFiniteRateInitialProbabilityDensity
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    Continuous
      (rengerDirectionalFlowHybridBVFiniteRateInitialProbabilityDensity
        generator hDuration level hLevel) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro state
  change Continuous fun path :
      RengerDirectionalFlowHybridBVFiniteRateSublevelPath generator hDuration level =>
    Real.toNNReal (path.1.initialTrace (Sum.inl state))
  exact continuous_real_toNNReal.comp <|
    (PiLp.proj (𝕜 := ℝ) (p := 1)
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
      (Sum.inl state)).continuous.comp
        (continuous_rengerDirectionalFlowHybridBVInitialTrace_on_finiteRateSublevel
          generator hDuration hLevel)

/-- On a finite dynamic-rate sublevel, the lifted initial cost is exactly the supplied rate of
the continuously recovered initial simplex point. -/
theorem rengerDirectionalFlowHybridBVLiftedInitialCost_eq_on_finiteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level) :
    rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path.1 =
      initialRate
        (rengerDirectionalFlowHybridBVFiniteRateInitialProbabilityDensity
          generator hDuration level hLevel path) := by
  rw [rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
    initialRate hDuration
      (rengerDirectionalFlowHybridBVFiniteRateSublevelPath_admissible
        generator hDuration hLevel path)]
  rfl

/-- The dynamic sector never exceeds the complete initial-plus-dynamic path rate. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_le_completeRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤
      rengerDirectionalFlowHybridBVCompleteRate
        generator hDuration initialRate path := by
  by_cases hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration
  · rw [rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
      generator hDuration initialRate hPath]
    calc
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path =
          0 + rengerDirectionalFlowHybridBVDynamicRate generator hDuration path :=
        (zero_add _).symm
      _ ≤ rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path :=
        add_le_add_left (zero_le) _
  · rw [rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
      generator hDuration hPath,
      rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
        generator hDuration initialRate hPath]

/-- A good initial-simplex rate makes the complete action lower semicontinuous after restriction
to any genuinely finite dynamic-rate sublevel. -/
theorem lowerSemicontinuous_rengerDirectionalFlowHybridBVCompleteRate_on_finiteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (hInitialRate : IsGoodRateFunction initialRate) :
    LowerSemicontinuous fun path :
        RengerDirectionalFlowHybridBVFiniteRateSublevelPath
          generator hDuration level =>
      rengerDirectionalFlowHybridBVCompleteRate
        generator hDuration initialRate path.1 := by
  have hInitial := LowerSemicontinuous.comp hInitialRate.lowerSemicontinuous
    (continuous_rengerDirectionalFlowHybridBVFiniteRateInitialProbabilityDensity
      generator hDuration hLevel)
  have hDynamic : LowerSemicontinuous fun path :
      RengerDirectionalFlowHybridBVFiniteRateSublevelPath
        generator hDuration level =>
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 :=
    LowerSemicontinuous.comp
      (lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration) continuous_subtype_val
  convert hInitial.add hDynamic using 1
  funext path
  rw [rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
    generator hDuration initialRate
      (rengerDirectionalFlowHybridBVFiniteRateSublevelPath_admissible
        generator hDuration hLevel path),
    rengerDirectionalFlowHybridBVLiftedInitialCost_eq_on_finiteRateSublevel
      generator hDuration hLevel initialRate path]
  rfl

/-- An independently good initial rate gives compact complete hybrid-path sublevels. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_isGoodRateFunction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (hInitialRate : IsGoodRateFunction initialRate) :
    IsGoodRateFunction
      (rengerDirectionalFlowHybridBVCompleteRate
        generator hDuration initialRate) := by
  intro bound
  let dynamicSublevel :=
    RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration (bound : ENNReal)
  let : CompactSpace dynamicSublevel :=
    isCompact_iff_compactSpace.mp
      (isCompact_rengerDirectionalFlowHybridBVFiniteRateSublevel
        generator hDuration ENNReal.coe_lt_top)
  let completeSublevel : Set dynamicSublevel :=
    {path |
      rengerDirectionalFlowHybridBVCompleteRate
        generator hDuration initialRate path.1 ≤ (bound : ENNReal)}
  have hCompleteSublevelClosed : IsClosed completeSublevel := by
    exact
      (lowerSemicontinuous_rengerDirectionalFlowHybridBVCompleteRate_on_finiteRateSublevel
        generator hDuration ENNReal.coe_lt_top initialRate hInitialRate).isClosed_preimage
        (bound : ENNReal)
  have hCompleteSublevelCompact : IsCompact completeSublevel :=
    hCompleteSublevelClosed.isCompact
  have hImageCompact := hCompleteSublevelCompact.image continuous_subtype_val
  have hSublevelIdentity :
      {path : RengerDirectionalFlowHybridBVPath State duration |
        rengerDirectionalFlowHybridBVCompleteRate
          generator hDuration initialRate path ≤ (bound : ENNReal)} =
        Subtype.val '' completeSublevel := by
    ext path
    constructor
    · intro hCompleteRate
      have hDynamicRate :
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path ≤
            (bound : ENNReal) :=
        (rengerDirectionalFlowHybridBVDynamicRate_le_completeRate
          generator hDuration initialRate path).trans hCompleteRate
      exact ⟨⟨path, hDynamicRate⟩, hCompleteRate, rfl⟩
    · rintro ⟨sublevelPath, hCompleteRate, rfl⟩
      exact hCompleteRate
  rw [hSublevelIdentity]
  exact hImageCompact

/-- The deterministic limiting-density indicator is a good rate function. -/
theorem rengerTheoremFourOneInitialRate_isGoodRateFunction
    (initialData : RengerTheoremFourOneInitialData State) :
    IsGoodRateFunction (rengerTheoremFourOneInitialRate initialData) := by
  intro bound
  have hSublevel :
      {density : FiniteStateProbabilityDensity State |
        rengerTheoremFourOneInitialRate initialData density ≤ (bound : ENNReal)} =
        {initialData.limitingDensity} := by
    ext density
    constructor
    · intro hRate
      change rengerTheoremFourOneInitialRate initialData density ≤ (bound : ENNReal) at hRate
      by_contra hDensity
      have hDensityNe : density ≠ initialData.limitingDensity := by
        simpa only [Set.mem_singleton_iff] using hDensity
      rw [rengerTheoremFourOneInitialRate_of_ne initialData hDensityNe] at hRate
      exact (not_le_of_gt ENNReal.coe_lt_top) hRate
    · intro hDensity
      rw [Set.mem_singleton_iff.mp hDensity]
      simp
  rw [hSublevel]
  exact isCompact_singleton

/-- Renger Theorem 4.1's complete hybrid-BV rate is good. -/
theorem rengerTheoremFourOneHybridBVCompleteRate_isGoodRateFunction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    IsGoodRateFunction
      (rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData) := by
  simpa only [rengerTheoremFourOneHybridBVCompleteRate] using
    rengerDirectionalFlowHybridBVCompleteRate_isGoodRateFunction
      generator hDuration (rengerTheoremFourOneInitialRate initialData)
        (rengerTheoremFourOneInitialRate_isGoodRateFunction initialData)

/-- Renger Theorem 4.2's complete hybrid-BV rate is good under its supplied initial LDP
contract. -/
theorem rengerTheoremFourTwoHybridBVCompleteRate_isGoodRateFunction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State) :
    IsGoodRateFunction
      (rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData) := by
  simpa only [rengerTheoremFourTwoHybridBVCompleteRate] using
    rengerDirectionalFlowHybridBVCompleteRate_isGoodRateFunction
      generator hDuration initialData.initialRate initialData.initialRate_good

/-- Renger Corollary 4.16's invariant-IID complete hybrid-BV rate is good. -/
theorem rengerCorollaryFourSixteenHybridBVCompleteRate_isGoodRateFunction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    IsGoodRateFunction
      (rengerCorollaryFourSixteenHybridBVCompleteRate
        generator hDuration initialData) := by
  simpa only [rengerCorollaryFourSixteenHybridBVCompleteRate] using
    rengerDirectionalFlowHybridBVCompleteRate_isGoodRateFunction
      generator hDuration (rengerInvariantInitialCost initialData.stationary)
        (rengerInvariantInitialCost_isGoodRateFunction initialData.stationary)

end

end FiniteMarkovProcesses.InformationTheory
