/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateTimeDependentMarkovJumpActionExpectation
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTargetActionBound
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Expected action of a positive Renger target regularization

The source-neutral jump-plus-escape expectation theorem is specialized to the canonical positive
Renger target rate.  The initial law remains explicit: this is required for heterogeneous
deterministic particle configurations and prevents a target-initial mixture from being silently
substituted for a coordinate-specific law.

This module identifies the exact finite-regularization expectation.  It does not yet assert its
regularization limit or an open-neighborhood large-deviation lower bound.
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

/-- Exact expectation of the canonical positive target action for one supplied
initial law.  Jump and occupation-weighted escape sectors remain visible in the underlying
generic definition. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initial : PMF State) : ℝ :=
  finiteStateTimeDependentMarkovExpectedJumpLogAction
    initial
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    generator.toTimeDependentMarkovRate
    ⟨duration, hDuration.le⟩

/-- Under any supplied common initial law, the physical expectation of the canonical target
action is exactly its jump-plus-escape mean. -/
theorem integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_eq_expected
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initial : PMF State) :
    (∫ history : FiniteJumpHistory State,
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩) =
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
        generator path index initial := by
  let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    generator path.1 index
  let jumpBound :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
      generator index
  have hJumpBoundNonnegative : 0 ≤ jumpBound := by
    unfold jumpBound
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
    positivity
  have hExpected :=
    integral_finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq_expected
      initial rates generator.toTimeDependentMarkovRate
      ⟨duration, hDuration.le⟩ hJumpBoundNonnegative
      (fun time source target _hOffDiagonal ↦ by
        change
          |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
            generator path.1 index source target time| ≤ jumpBound
        exact
          abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight_le
            generator path.1 index source target time)
  have hActionIndependent :
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index =
        finiteStateTimeDependentMarkovJumpLogAction
          initial initial rates generator.toTimeDependentMarkovRate duration := by
    unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
    exact finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq
      (rengerDirectionalFlowHybridBVTargetInitialPMF path) initial
      rates generator.toTimeDependentMarkovRate duration
  rw [hActionIndependent]
  simpa only [
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction,
    rates] using! hExpected

/-- The exact finite-regularization expectation is finite relative entropy between the physical
canonical target law and the unchanged homogeneous reference law.  This holds for every supplied
common initial law; no asymptotic action limit is used. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction_eq_klDiv
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initial : PMF State) :
    let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index
    let candidate := finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates ⟨duration, hDuration.le⟩
    let reference := finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
    _root_.InformationTheory.klDiv candidate reference ≠ ⊤ ∧
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetExpectedJumpLogAction
          generator path index initial =
        (_root_.InformationTheory.klDiv candidate reference).toReal := by
  dsimp only
  let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    generator path.1 index
  let candidate := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates ⟨duration, hDuration.le⟩
  let reference := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
  let : IsProbabilityMeasure candidate :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates ⟨duration, hDuration.le⟩⟩
  let : IsProbabilityMeasure reference :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩⟩
  have hSupport : FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport
      rates generator.toTimeDependentMarkovRate :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_haveSameDirectedSupport
      generator path.1 index
  have hAbsoluteContinuity : candidate ≪ reference := by
    dsimp only [candidate, reference]
    rw
      [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
        initial rates ⟨duration, hDuration.le⟩,
      finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩]
    exact finiteStateTimeDependentMarkovJumpDensityMeasure_absolutelyContinuous
      (fun _state ↦ Iff.rfl) hSupport duration
  have hLikelihood : llr candidate reference =ᵐ[candidate]
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index := by
    have hCandidateDensity : candidate =
        finiteStateTimeDependentMarkovJumpDensityMeasure
          initial rates duration := by
      dsimp only [candidate]
      simpa only [NNReal.coe_mk] using!
        finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
          initial rates ⟨duration, hDuration.le⟩
    have hReferenceDensity : reference =
        finiteStateTimeDependentMarkovJumpDensityMeasure
          initial generator.toTimeDependentMarkovRate duration := by
      dsimp only [reference]
      simpa only [NNReal.coe_mk] using!
        finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
          initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
    have hGenericLikelihood :=
      llr_finiteStateTimeDependentMarkovJumpDensityMeasure
        (initial := initial) (referenceInitial := initial)
        (rates := rates) (referenceRates := generator.toTimeDependentMarkovRate)
        (fun _state ↦ Iff.rfl) hSupport duration
    have hActionIndependent :
        finiteStateTimeDependentMarkovJumpLogAction
            initial initial rates generator.toTimeDependentMarkovRate duration =
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index := by
      unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
      exact (finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq
        (rengerDirectionalFlowHybridBVTargetInitialPMF path) initial
        rates generator.toTimeDependentMarkovRate duration).symm
    rw [hCandidateDensity, hReferenceDensity]
    simpa only [NNReal.coe_mk, hActionIndependent] using hGenericLikelihood
  have hActionIntegrable : Integrable
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index) candidate := by
    exact (memLp_two_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
      generator hDuration path index initial).integrable one_le_two
  have hLikelihoodIntegrable : Integrable (llr candidate reference) candidate :=
    hActionIntegrable.congr hLikelihood.symm
  constructor
  · exact _root_.InformationTheory.klDiv_ne_top_iff.mpr
      ⟨hAbsoluteContinuity, hLikelihoodIntegrable⟩
  · rw [← integral_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_eq_expected
      generator hDuration path index initial]
    calc
      (∫ history,
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
            generator path index history ∂candidate) =
          ∫ history, llr candidate reference history ∂candidate :=
        integral_congr_ae hLikelihood.symm
      _ = (_root_.InformationTheory.klDiv candidate reference).toReal :=
        (_root_.InformationTheory.toReal_klDiv_of_measure_eq
          hAbsoluteContinuity (by simp)).symm

end

end FiniteMarkovProcesses.InformationTheory
