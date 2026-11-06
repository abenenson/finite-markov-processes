/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVConstantTranslation
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDualEvaluation

/-!
# Constant cumulative-flow translations on the Renger hybrid carrier

The current dual functional sees density and the derivative of cumulative directional flow, but
not the absolute cumulative-flow origin.  This module freezes that fact as an exact adverse
control: translate only the cumulative-flow coordinates by a constant nonzero offset.  Every dual
test is invariant, while the physical zero-start condition rejects the translated path and the
totalized dynamic rate assigns it infinite cost.

This is a representation diagnostic.  It neither weakens the physical domain nor identifies a
large-deviation theorem.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The finite coordinate vector that is zero on density coordinates and carries the supplied
constant offset on cumulative directional-flow coordinates. -/
noncomputable def rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm
      (fun coordinate => Sum.elim (fun _state => 0) offset coordinate)

/-- A Markov-jump hybrid path with only its absolute cumulative-flow origin translated. -/
noncomputable def rengerDirectionalFlowHybridBVTranslateCumulativeFlow
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ) :
    RengerDirectionalFlowHybridBVPath State duration :=
  path.constantTranslate
    (rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset)

/-- The cumulative-flow translation vector vanishes on density coordinates. -/
@[simp]
theorem rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector_density
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (state : State) :
    rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset
      (Sum.inl state) = 0 := by
  simp [rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector]

/-- The cumulative-flow translation vector evaluates to the supplied offset on flow
coordinates. -/
@[simp]
theorem rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector_flow
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset
      (Sum.inr transition) = offset transition := by
  simp [rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector]

/-- Every carried signed derivative is unchanged by cumulative-flow translation. -/
@[simp]
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_derivative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset).toDerivativePath.derivative
        coordinate = path.toDerivativePath.derivative coordinate := by
  exact FiniteIntervalHybridBVPath.constantTranslate_derivative path _ coordinate

/-- Density values are unchanged throughout physical half-open time. -/
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_densityValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityValue
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) time state =
      rengerDirectionalFlowHybridBVDensityValue path time state := by
  unfold rengerDirectionalFlowHybridBVDensityValue
  simp only [rengerDirectionalFlowHybridBVTranslateCumulativeFlow]
  rw [FiniteIntervalHybridBVPath.constantTranslate_cadlagRepresentative_eq
    path (rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset) hTime]
  simp

/-- Cumulative-flow values are shifted by exactly the requested constant throughout physical
half-open time. -/
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_cumulativeFlowValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    {time : ℝ} (hTime : time ∈ Ico 0 duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVCumulativeFlowValue
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) time transition =
      rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition +
        offset transition := by
  unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
  simp only [rengerDirectionalFlowHybridBVTranslateCumulativeFlow]
  rw [FiniteIntervalHybridBVPath.constantTranslate_cadlagRepresentative_eq
    path (rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset) hTime]
  simp

/-- The separately recovered initial cumulative-flow trace is shifted by the requested offset. -/
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_initialTrace_flow
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (hDuration : 0 < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset).initialTrace
        (Sum.inr transition) =
      path.initialTrace (Sum.inr transition) + offset transition := by
  simp only [rengerDirectionalFlowHybridBVTranslateCumulativeFlow]
  rw [FiniteIntervalHybridBVPath.constantTranslate_initialTrace path
    (rengerDirectionalFlowHybridBVCumulativeFlowTranslationVector offset) hDuration]
  simp

/-- The Radon--Nikodym density of every carried derivative is unchanged. -/
@[simp]
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_derivativeDensity
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset).derivativeDensity
        coordinate = path.derivativeDensity coordinate := by
  unfold FiniteIntervalHybridBVPath.derivativeDensity
  rw [rengerDirectionalFlowHybridBVTranslateCumulativeFlow_derivative]

/-- Every density-coordinate weighted `L1` integral is unchanged by a cumulative-flow
translation. -/
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_weightedDensityIntegral
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (test : C_c(ℝ, ℝ)) (state : State) :
    finiteIntervalL1PathWeightedCoordinateIntegral test (Sum.inl state)
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow
          path offset).toDerivativePath.toL1Path =
      finiteIntervalL1PathWeightedCoordinateIntegral test (Sum.inl state)
        path.toDerivativePath.toL1Path := by
  rw [rengerDirectionalFlowHybridBVWeightedDensityIntegral_eq,
    rengerDirectionalFlowHybridBVWeightedDensityIntegral_eq]
  apply integral_congr_ae
  have hPhysical :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, time ∈ Ioo 0 duration := by
    rw [finiteOpenIntervalVolume]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hPhysical] with time hTime
  rw [rengerDirectionalFlowHybridBVTranslateCumulativeFlow_densityValue
    path offset ⟨hTime.1.le, hTime.2⟩ state]

/-- Every real dual evaluation is invariant under a constant cumulative-flow translation. -/
theorem rengerDirectionalFlowHybridBVDualEvaluation_translateCumulativeFlow
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ) :
    rengerDirectionalFlowHybridBVDualEvaluation generator test
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) =
      rengerDirectionalFlowHybridBVDualEvaluation generator test path := by
  unfold rengerDirectionalFlowHybridBVDualEvaluation
  apply Finset.sum_congr rfl
  intro transition _hTransition
  rw [rengerDirectionalFlowHybridBVTranslateCumulativeFlow_derivative,
    rengerDirectionalFlowHybridBVTranslateCumulativeFlow_weightedDensityIntegral]

/-- Every extended dual evaluation is invariant under a constant cumulative-flow translation. -/
theorem rengerDirectionalFlowHybridBVExtendedDualEvaluation_translateCumulativeFlow
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ) :
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) =
      rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test path := by
  unfold rengerDirectionalFlowHybridBVExtendedDualEvaluation
  rw [rengerDirectionalFlowHybridBVDualEvaluation_translateCumulativeFlow]

/-- The entire dual supremum is invariant under a constant cumulative-flow translation. -/
theorem rengerDirectionalFlowHybridBVDualRate_translateCumulativeFlow
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ) :
    rengerDirectionalFlowHybridBVDualRate generator
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) =
      rengerDirectionalFlowHybridBVDualRate generator path := by
  unfold rengerDirectionalFlowHybridBVDualRate
  congr 1
  funext test
  exact rengerDirectionalFlowHybridBVExtendedDualEvaluation_translateCumulativeFlow
    generator test path offset

/-- Any nonzero cumulative-flow translation of a physically admissible path violates the exact
zero-start boundary condition. -/
theorem not_rengerDirectionalFlowHybridBVAdmissible_translateCumulativeFlow_of_ne_zero
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hOffset : offset transition ≠ 0) :
    ¬RengerDirectionalFlowHybridBVAdmissible
      (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) hDuration := by
  intro hTranslated
  have hOriginalZero := hPath.cumulativeFlowInitiallyZero transition
  have hTranslatedZero := hTranslated.cumulativeFlowInitiallyZero transition
  rw [rengerDirectionalFlowHybridBVTranslateCumulativeFlow_initialTrace_flow
    path offset hDuration transition, hOriginalZero, zero_add] at hTranslatedZero
  exact hOffset hTranslatedZero

/-- The totalized dynamic rate assigns infinite cost to every nonzero cumulative-flow translation
of an admissible path. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_translateCumulativeFlow_eq_top_of_ne_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hOffset : offset transition ≠ 0) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) = ∞ := by
  apply rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
  exact not_rengerDirectionalFlowHybridBVAdmissible_translateCumulativeFlow_of_ne_zero
    hDuration hPath offset transition hOffset

/-- On any admissible finite-rate witness, a nonzero cumulative-flow translation proves that the
total-carrier dual supremum cannot equal the totalized physical dynamic rate. -/
theorem rengerDirectionalFlowHybridBVDualRate_ne_dynamicRate_after_cumulativeFlowTranslation
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (hRateFinite : rengerDirectionalFlowHybridBVDynamicRate generator hDuration path < ∞)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hOffset : offset transition ≠ 0) :
    rengerDirectionalFlowHybridBVDualRate generator
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) ≠
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVTranslateCumulativeFlow path offset) := by
  rw [rengerDirectionalFlowHybridBVDualRate_translateCumulativeFlow,
    rengerDirectionalFlowHybridBVDynamicRate_translateCumulativeFlow_eq_top_of_ne_zero
      generator hDuration hPath offset transition hOffset]
  exact (rengerDirectionalFlowHybridBVDualRate_le_dynamicRate generator hDuration hPath).trans_lt
    hRateFinite |>.ne

end

end FiniteMarkovProcesses.InformationTheory
