/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateTimeDependentMarkovJumpRadonNikodym
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetSourceMean

/-!
# Girsanov identity for canonical positive Renger target regularizations

The canonical positive target rate has exactly the directed support of the frozen homogeneous
reference generator.  Starting both laws from the target's recovered initial PMF therefore
specializes the generic bounded time-dependent Radon--Nikodym theorem to the regularized physical
source used in the Renger lower route.

This module supplies the physical likelihood change of measure.  It does not yet prove an open-
neighborhood lower estimate or take the regularization limit.

## Main results

- `rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport`:
  exact pointwise support equality.
- `rengerDirectionalFlowHybridBVPositiveTargetJumpMeasure_withDensity_expLogAction`:
  physical Girsanov identity against the homogeneous reference source.
- `rnDeriv_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpDensityMeasure`:
  exact regularized-source RN density.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The canonical positive target regularization and constant reference generator have identical
directed support at every physical time. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ) :
    FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index)
      generator.toTimeDependentMarkovRate := by
  intro time source target
  change
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).rate time source target = 0 ↔
      generator.rate source target = 0
  constructor
  · intro hRegularized
    by_contra hGenerator
    have hGeneratorPositive : 0 < generator.rate source target :=
      lt_of_le_of_ne zero_le (Ne.symm hGenerator)
    exact (ne_of_gt
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_pos
        generator path index time hGeneratorPositive)) hRegularized
  · exact rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_eq_zero
      generator path index time

/-- Complete regularized-source-to-reference physical log action. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) : FiniteJumpHistory State → ℝ :=
  finiteStateTimeDependentMarkovJumpLogAction
    (rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    generator.toTimeDependentMarkovRate duration

/-- The homogeneous physical reference law tilted by the complete canonical positive target
action is exactly the regularized physical target law. -/
theorem rengerDirectionalFlowHybridBVPositiveTargetJumpMeasure_withDensity_expLogAction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    (finiteStateMarkovJumpDensityMeasure
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration).withDensity
      (fun history => ENNReal.ofReal
        (Real.exp
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index history))) =
      finiteStateTimeDependentMarkovJumpDensityMeasure
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        duration := by
  have hSupport :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
      generator path.1 index
  have hGirsanov :=
    finiteStateTimeDependentMarkovJumpDensityMeasure_withDensity_expLogAction
      (initial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (referenceInitial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      (referenceRates := generator.toTimeDependentMarkovRate)
      (fun _state => Iff.rfl) hSupport duration
  have hReference :
      finiteStateTimeDependentMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          generator.toTimeDependentMarkovRate duration =
        finiteStateMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration := by
    simpa only [NNReal.coe_mk] using!
      finiteStateTimeDependentMarkovJumpDensityMeasure_constant
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator
        ⟨duration, hDuration.le⟩
  rw [hReference] at hGirsanov
  exact hGirsanov

/-- The exact RN derivative of the canonical positive target law against the homogeneous
reference law is the exponential of its complete physical action. -/
theorem rnDeriv_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpDensityMeasure
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    (finiteStateTimeDependentMarkovJumpDensityMeasure
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        duration).rnDeriv
      (finiteStateMarkovJumpDensityMeasure
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration) =ᵐ[
          finiteStateMarkovJumpDensityMeasure
            (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration]
      fun history => ENNReal.ofReal
        (Real.exp
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index history)) := by
  have hSupport :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
      generator path.1 index
  have hDerivative :=
    rnDeriv_finiteStateTimeDependentMarkovJumpDensityMeasure_eq_exp_logAction
      (initial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (referenceInitial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      (referenceRates := generator.toTimeDependentMarkovRate)
      (fun _state => Iff.rfl) hSupport duration
  have hReference :
      finiteStateTimeDependentMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          generator.toTimeDependentMarkovRate duration =
        finiteStateMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration := by
    simpa only [NNReal.coe_mk] using!
      finiteStateTimeDependentMarkovJumpDensityMeasure_constant
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator
        ⟨duration, hDuration.le⟩
  rw [hReference] at hDerivative
  exact hDerivative

/-- The physical log likelihood of the canonical positive target law relative to the homogeneous
reference is exactly its complete jump action. -/
theorem llr_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpDensityMeasure
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    MeasureTheory.llr
        (finiteStateTimeDependentMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          duration)
        (finiteStateMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration) =ᵐ[
            finiteStateTimeDependentMarkovJumpDensityMeasure
              (rengerDirectionalFlowHybridBVTargetInitialPMF path)
              (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
                generator path.1 index)
              duration]
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index := by
  have hSupport :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
      generator path.1 index
  have hLikelihood := llr_finiteStateTimeDependentMarkovJumpDensityMeasure
    (initial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (referenceInitial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    (referenceRates := generator.toTimeDependentMarkovRate)
    (fun _state => Iff.rfl) hSupport duration
  have hReference :
      finiteStateTimeDependentMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path)
          generator.toTimeDependentMarkovRate duration =
        finiteStateMarkovJumpDensityMeasure
          (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator duration := by
    simpa only [NNReal.coe_mk] using!
      finiteStateTimeDependentMarkovJumpDensityMeasure_constant
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator
        ⟨duration, hDuration.le⟩
  rw [hReference] at hLikelihood
  exact hLikelihood

/-- The regularized physical source obeys the exact integral fluctuation identity against its
homogeneous reference source. -/
theorem lintegral_exp_neg_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    ∫⁻ history,
        ENNReal.ofReal (Real.exp
          (-rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index history))
      ∂finiteStateTimeDependentMarkovJumpDensityMeasure
        (rengerDirectionalFlowHybridBVTargetInitialPMF path)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        duration = 1 := by
  exact lintegral_exp_neg_finiteStateTimeDependentMarkovJumpLogAction
    (initial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (referenceInitial := rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    (referenceRates := generator.toTimeDependentMarkovRate)
    (fun _state => Iff.rfl)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
      generator path.1 index)
    hDuration.le

end

end FiniteMarkovProcesses.InformationTheory
