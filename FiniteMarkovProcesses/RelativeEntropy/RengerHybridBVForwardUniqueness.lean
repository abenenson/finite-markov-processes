/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerDirectionalFlowZeroRate
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTargetForwardEquation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovForwardUniqueness

/-!
# Fixed-initial uniqueness on the hybrid-BV directional-flow carrier

Admissibility reconstructs density and cumulative flow from their absolutely continuous
derivatives. The generator flow equation therefore determines the entire hybrid path from its
initial density, via the source-neutral finite-state forward uniqueness theorem.

## Main results

- `ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow`.
- `rengerDirectionalFlowHybridBVPath_eq_of_generatorFlow_initialDensity`.

The equality is literal hybrid-carrier equality, not equality of only density or net current.

## References

The forward-equation argument is classical finite-state Markov uniqueness (Norris,
*Markov Chains*, Section 2.8); see `FiniteStateMarkovForwardUniqueness`.
The additional step here is reconstruction of the cumulative flows and derivative measures
from the admissible hybrid path. Equality of the density alone would not suffice.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] {duration : ℝ}

/-- Every admissible density coordinate is absolutely continuous on each strict subhorizon.
This regularity follows from the existing reconstruction, rather than being supplied anew. -/
theorem absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {horizon : ℝ} (hHorizon : horizon ∈ Ico 0 duration) (state : State) :
    AbsolutelyContinuousOnInterval
      (fun time ↦ rengerDirectionalFlowHybridBVDensityValue path.1 time state) 0 horizon := by
  let divergence := fun time ↦ rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state
  have hIntegrable : IntervalIntegrable divergence volume 0 horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hHorizon.1]
    exact (integrable_rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 state).mono_measure
      (Measure.restrict_mono (Ioo_subset_Ioo_right hHorizon.2.le) le_rfl)
  have hPrimitive : AbsolutelyContinuousOnInterval
      (fun time ↦ path.1.initialTrace (Sum.inl state) + ∫ point in 0..time, divergence point)
      0 horizon :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.const_add _
      (intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral hIntegrable
        (by simpa only [uIcc_of_le hHorizon.1, mem_Icc] using
          And.intro (le_refl (0 : ℝ)) hHorizon.1))
  apply FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.congr_on ?_ hPrimitive
  intro time hTime
  rw [uIcc_of_le hHorizon.1] at hTime
  change path.1.initialTrace (Sum.inl state) + (∫ point in 0..time, divergence point) =
    rengerDirectionalFlowHybridBVDensityValue path.1 time state
  rw [intervalIntegral.integral_of_le hTime.1, integral_Ioc_eq_integral_Ioo]
  exact (rengerDirectionalFlowHybridBVDensityValue_eq_initial_add_integral_flowDivergence
    hDuration path ⟨hTime.1, hTime.2.trans_lt hHorizon.2⟩ state).symm

/-- Including the zero diagonal, the raw ordered flow agrees a.e. with density times rate. -/
theorem ae_rengerDirectionalFlowHybridBVRawFlowDerivativeValue_eq_generatorFlow
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (hFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator path) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ source target,
      rengerDirectionalFlowHybridBVRawFlowDerivativeValue path time source target =
        rengerDirectionalFlowHybridBVDensityValue path time source *
          (generator.rate source target : ℝ) := by
  have hRaw := (rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw
    generator hDuration hPath).mp hFlow
  filter_upwards [hRaw] with time hAt
  intro source target
  by_cases hDistinct : source ≠ target
  · simpa only [rengerDirectionalFlowHybridBVRawFlowDerivativeValue, dite_eq_left hDistinct] using
      hAt ⟨(source, target), hDistinct⟩
  · have hEqual : source = target := not_ne_iff.mp hDistinct
    subst target
    simp [rengerDirectionalFlowHybridBVRawFlowDerivativeValue, generator.rate_self]

/-- Admissibility and generator flow derive the a.e. classical finite-state forward equation. -/
theorem ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator path.1) (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      HasDerivAt (fun point ↦ rengerDirectionalFlowHybridBVDensityValue path.1 point state)
        (finiteStateRateErrorDivergence generator.rate
          (rengerDirectionalFlowHybridBVDensityValue path.1 time) state) time := by
  filter_upwards [ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue hDuration path state,
    ae_rengerDirectionalFlowHybridBVRawFlowDerivativeValue_eq_generatorFlow
      generator hDuration path.2 hFlow] with time hDerivative hAt
  have hDrift : rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state =
      finiteStateRateErrorDivergence generator.rate
        (rengerDirectionalFlowHybridBVDensityValue path.1 time) state := by
    rw [rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence]
    simp only [finiteStateFlowDivergence, hAt, finiteStateRateErrorDivergence, Finset.mul_sum]
  simpa only [hDrift] using hDerivative

/-- The density coordinates of two admissible generator-flow paths agree throughout physical
time when their recovered initial density vectors agree. -/
theorem rengerDirectionalFlowHybridBVDensityValue_eqOn_of_generatorFlow_initialDensity
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hFirstFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator first.1)
    (hSecondFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator second.1)
    (hInitial : ∀ state, first.1.initialTrace (Sum.inl state) =
      second.1.initialTrace (Sum.inl state)) :
    EqOn (rengerDirectionalFlowHybridBVDensityValue first.1)
      (rengerDirectionalFlowHybridBVDensityValue second.1) (Ico 0 duration) := by
  apply finiteStateMarkov_eqOn_of_forwardEquation generator
    (fun _horizon hHorizon ↦
      absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue
        hDuration first hHorizon)
    (fun _horizon hHorizon ↦
      absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue
        hDuration second hHorizon)
    (ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow
      generator hDuration first hFirstFlow)
    (ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow
      generator hDuration second hSecondFlow)
  funext state
  exact hInitial state

/-- Fixed initial density determines the whole admissible generator-flow hybrid path. Both
cumulative directional flow and carried derivative measures are retained in the equality. -/
theorem rengerDirectionalFlowHybridBVPath_eq_of_generatorFlow_initialDensity
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (first second : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hFirstFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator first.1)
    (hSecondFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator second.1)
    (hInitial : ∀ state, first.1.initialTrace (Sum.inl state) =
      second.1.initialTrace (Sum.inl state)) :
    first.1 = second.1 := by
  have hDensity := rengerDirectionalFlowHybridBVDensityValue_eqOn_of_generatorFlow_initialDensity
    generator hDuration first second hFirstFlow hSecondFlow hInitial
  have hDerivative : ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ transition,
      rengerDirectionalFlowHybridBVFlowDerivative first.1 time transition =
        rengerDirectionalFlowHybridBVFlowDerivative second.1 time transition := by
    filter_upwards
      [(rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw
          generator hDuration first.2).mp hFirstFlow,
        (rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw
          generator hDuration second.2).mp hSecondFlow,
        ae_restrict_mem measurableSet_Ioo] with time hFirst hSecond hTime
    intro transition
    rw [hFirst transition, hSecond transition, hDensity ⟨hTime.1.le, hTime.2⟩]
  have hRepresentative : ∀ time ∈ Ico 0 duration,
      first.1.cadlagRepresentative.representative time =
        second.1.cadlagRepresentative.representative time := by
    intro time hTime
    ext coordinate
    cases coordinate with
    | inl state => exact congrFun (hDensity hTime) state
    | inr transition =>
        rw [first.1.cadlagRepresentative_eq_initial_add_integral_derivativeDensity
            first.2.absolutelyContinuousDerivative (Sum.inr transition) hTime.1 hTime.2,
          second.1.cadlagRepresentative_eq_initial_add_integral_derivativeDensity
            second.2.absolutelyContinuousDerivative (Sum.inr transition) hTime.1 hTime.2]
        change first.1.initialTrace (Sum.inr transition) + _ =
          second.1.initialTrace (Sum.inr transition) + _
        rw [first.2.cumulativeFlowInitiallyZero, second.2.cumulativeFlowInitiallyZero]
        congr 1
        apply integral_congr_ae
        exact ae_restrict_of_ae (hDerivative.mono fun _point hAt ↦ hAt transition)
  apply FiniteIntervalHybridBVPath.injective_toL1Path
  obtain ⟨hFirstMem, hFirstLp⟩ := first.1.cadlagRepresentative.represents
  obtain ⟨hSecondMem, hSecondLp⟩ := second.1.cadlagRepresentative.represents
  change first.1.toDerivativePath.toL1Path = second.1.toDerivativePath.toL1Path
  rw [← hFirstLp, ← hSecondLp]
  apply hFirstMem.toLp_congr hSecondMem
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  exact hRepresentative time ⟨hTime.1.le, hTime.2⟩

end

end FiniteMarkovProcesses.InformationTheory
