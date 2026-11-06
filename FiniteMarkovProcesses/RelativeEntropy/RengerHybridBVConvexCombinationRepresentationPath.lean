/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVLinearCombination
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMean

/-!
# Convex combinations in the Renger representation domain

The exact finite-rate hybrid-BV representation domain is convex.  This module packages the
source-neutral path combination, its hybrid-topology convergence, pointwise coordinate formulas,
and preservation of every admissibility and boundary field.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Convex combination of two paths on the genuine hybrid derivative graph. -/
noncomputable def rengerDirectionalFlowHybridBVConvexCombinationPath
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) : RengerDirectionalFlowHybridBVPath State duration :=
  FiniteIntervalHybridBVPath.linearCombination
    (1 - mixingWeight) mixingWeight first.1 second.1

/-- Convex combinations converge to the first path as their mixing weight tends to zero. -/
theorem tendsto_rengerDirectionalFlowHybridBVConvexCombinationPath
    {Index : Type*} {filter : Filter Index}
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {mixingWeight : Index → ℝ}
    (hMixingWeight : Tendsto mixingWeight filter (𝓝 0)) :
    Tendsto
      (fun index => rengerDirectionalFlowHybridBVConvexCombinationPath
        first second (mixingWeight index))
      filter (𝓝 first.1) := by
  have hFirstCoefficient :
      Tendsto (fun index => (1 : ℝ) - mixingWeight index) filter (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hMixingWeight
  simpa only [rengerDirectionalFlowHybridBVConvexCombinationPath,
    sub_zero, FiniteIntervalHybridBVPath.linearCombination_one_zero] using
    FiniteIntervalHybridBVPath.tendsto_linearCombination first.1 second.1
      hFirstCoefficient hMixingWeight

/-- Density coordinates combine pointwise on the physical half-open interval. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_densityValue
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityValue
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) time state =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVDensityValue first.1 time state +
        mixingWeight *
          rengerDirectionalFlowHybridBVDensityValue second.1 time state := by
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVConvexCombinationPath
  rw [FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq
    _ _ _ _ hTime]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Cumulative ordered-flow coordinates combine pointwise on physical half-open time. -/
theorem rengerDirectionalFlowHybridBVConvexCombinationPath_cumulativeFlowValue
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) {time : ℝ} (hTime : time ∈ Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVCumulativeFlowValue
        (rengerDirectionalFlowHybridBVConvexCombinationPath
          first second mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVCumulativeFlowValue first.1 time transition +
        mixingWeight *
          rengerDirectionalFlowHybridBVCumulativeFlowValue second.1 time transition := by
  unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rengerDirectionalFlowHybridBVConvexCombinationPath
  rw [FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq
    _ _ _ _ hTime]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Density derivatives combine pointwise almost everywhere. -/
theorem ae_rengerDirectionalFlowHybridBVConvexCombinationPath_densityDerivative_eq
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ state,
      rengerDirectionalFlowHybridBVDensityDerivative
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time state =
        (1 - mixingWeight) *
            rengerDirectionalFlowHybridBVDensityDerivative first.1 time state +
          mixingWeight *
            rengerDirectionalFlowHybridBVDensityDerivative second.1 time state := by
  rw [ae_all_iff]
  intro state
  have hCoordinate :=
    FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
      (1 - mixingWeight) mixingWeight first.1 second.1
      first.2.absolutelyContinuousDerivative second.2.absolutelyContinuousDerivative
      (Sum.inl state)
  filter_upwards [hCoordinate] with time hTime
  simpa only [rengerDirectionalFlowHybridBVDensityDerivative,
    rengerDirectionalFlowHybridBVConvexCombinationPath,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hTime

/-- Ordered-flow derivatives combine pointwise almost everywhere. -/
theorem ae_rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivative_eq
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ transition,
      rengerDirectionalFlowHybridBVFlowDerivative
          (rengerDirectionalFlowHybridBVConvexCombinationPath
            first second mixingWeight) time transition =
        (1 - mixingWeight) *
            rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition +
          mixingWeight *
            rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition := by
  rw [ae_all_iff]
  intro transition
  have hCoordinate :=
    FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
      (1 - mixingWeight) mixingWeight first.1 second.1
      first.2.absolutelyContinuousDerivative second.2.absolutelyContinuousDerivative
      (Sum.inr transition)
  filter_upwards [hCoordinate] with time hTime
  simpa only [rengerDirectionalFlowHybridBVFlowDerivative,
    rengerDirectionalFlowHybridBVConvexCombinationPath,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hTime

/-- Every nonnegative unit-bounded combination remains in the exact representation domain. -/
noncomputable def rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath
    {hDuration : 0 < duration}
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) (hMixingWeightNonnegative : 0 ≤ mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration := by
  let combined := rengerDirectionalFlowHybridBVConvexCombinationPath
    first second mixingWeight
  have hFirstCoefficient : 0 ≤ 1 - mixingWeight := sub_nonneg.mpr hMixingWeightLeOne
  refine ⟨combined, ?_⟩
  refine
    { absolutelyContinuousDerivative :=
        FiniteIntervalHybridBVPath.linearCombination_hasAbsolutelyContinuousDerivative
          (1 - mixingWeight) mixingWeight first.1 second.1
          first.2.absolutelyContinuousDerivative second.2.absolutelyContinuousDerivative
      densityNonnegativeAE := ?_
      densityNormalizedAE := ?_
      cumulativeFlowNonnegativeAE := ?_
      flowDerivativeNonnegativeAE := ?_
      continuityEquationAE := ?_
      initialDensityNormalized := ?_
      initialDensityNonnegative := ?_
      cumulativeFlowInitiallyZero := ?_
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · filter_upwards [first.2.densityNonnegativeAE, second.2.densityNonnegativeAE,
      ae_restrict_mem measurableSet_Ioo] with time hFirst hSecond hTime
    intro state
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath_densityValue
        first second mixingWeight ⟨hTime.1.le, hTime.2⟩ state]
    exact add_nonneg (mul_nonneg hFirstCoefficient (hFirst state))
      (mul_nonneg hMixingWeightNonnegative (hSecond state))
  · filter_upwards [first.2.densityNormalizedAE, second.2.densityNormalizedAE,
      ae_restrict_mem measurableSet_Ioo] with time hFirst hSecond hTime
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
      first second mixingWeight by rfl]
    simp_rw [rengerDirectionalFlowHybridBVConvexCombinationPath_densityValue
      first second mixingWeight ⟨hTime.1.le, hTime.2⟩,
      Finset.sum_add_distrib, ← Finset.mul_sum, hFirst, hSecond]
    ring
  · filter_upwards [first.2.cumulativeFlowNonnegativeAE,
      second.2.cumulativeFlowNonnegativeAE, ae_restrict_mem measurableSet_Ioo]
      with time hFirst hSecond hTime
    intro transition
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath_cumulativeFlowValue
        first second mixingWeight ⟨hTime.1.le, hTime.2⟩ transition]
    exact add_nonneg (mul_nonneg hFirstCoefficient (hFirst transition))
      (mul_nonneg hMixingWeightNonnegative (hSecond transition))
  · filter_upwards [first.2.flowDerivativeNonnegativeAE,
      second.2.flowDerivativeNonnegativeAE,
      ae_rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivative_eq
        first second mixingWeight] with time hFirst hSecond hCombined
    intro transition
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl, hCombined transition]
    exact add_nonneg (mul_nonneg hFirstCoefficient (hFirst transition))
      (mul_nonneg hMixingWeightNonnegative (hSecond transition))
  · filter_upwards [first.2.continuityEquationAE, second.2.continuityEquationAE,
      ae_rengerDirectionalFlowHybridBVConvexCombinationPath_densityDerivative_eq
        first second mixingWeight,
      ae_rengerDirectionalFlowHybridBVConvexCombinationPath_flowDerivative_eq
        first second mixingWeight] with time hFirst hSecond hDensity hFlow
    intro state
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      hDensity state, hFirst state, hSecond state]
    simp_rw [hFlow, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum,
      first.2.initialDensityNormalized, second.2.initialDensityNormalized]
    ring
  · intro state
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hFirstCoefficient (first.2.initialDensityNonnegative state))
      (mul_nonneg hMixingWeightNonnegative (second.2.initialDensityNonnegative state))
  · intro transition
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp [first.2.cumulativeFlowInitiallyZero transition,
      second.2.cumulativeFlowInitiallyZero transition]
  · rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum,
      first.2.terminalDensityNormalized, second.2.terminalDensityNormalized]
    ring
  · intro state
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hFirstCoefficient (first.2.terminalDensityNonnegative state))
      (mul_nonneg hMixingWeightNonnegative (second.2.terminalDensityNonnegative state))
  · intro transition
    rw [show combined = rengerDirectionalFlowHybridBVConvexCombinationPath
        first second mixingWeight by rfl,
      rengerDirectionalFlowHybridBVConvexCombinationPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg
      (mul_nonneg hFirstCoefficient
        (first.2.terminalCumulativeFlowNonnegative transition))
      (mul_nonneg hMixingWeightNonnegative
        (second.2.terminalCumulativeFlowNonnegative transition))

end

end FiniteMarkovProcesses.InformationTheory
