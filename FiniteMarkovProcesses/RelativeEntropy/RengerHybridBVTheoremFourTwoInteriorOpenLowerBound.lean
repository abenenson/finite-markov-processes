/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteEmpiricalTypeInitialAtomLargeDeviation
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourOneOpenLowerBound

/-!
# Renger Theorem 4.2 interior-initial open lower bound

This module composes the exact empirical initial atom selected from Theorem 4.2's supplied initial
LDP with the deterministic conditional hybrid-path lower estimate.  The finite disintegration of
the canonical random-initial source contains the selected atom times its conditional path law;
extended logarithms and particle speed retain that product exactly.

The result covers finite-rate candidates whose recovered initial density is coordinate-positive.
Lower-boundary candidates still require the theorem's separately supplied left-continuity premise
and an interior path approximation; that premise is not silently used here.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- Exact empirical count types converging to a positive target initial density satisfy the
conditional dynamic-action lower estimate on every hybrid-open neighborhood. -/
theorem
neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetEmpiricalTypeReference_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    (empiricalType :
      (successorIndex : ℕ) → FiniteIIDPositiveEmpiricalType State successorIndex)
    (hEmpiricalType : FiniteStateProbabilityDensity.TendstoCoordinatewise
      (fun successorIndex ↦ (empiricalType successorIndex).probabilityDensity)
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path))
    {openSet : Set (RengerDirectionalFlowHybridBVPath State duration)}
    (hOpen : IsOpen openSet) (hTarget : path.1 ∈ openSet) :
    -(rengerDirectionalFlowHybridBVDynamicRate
        generator hDuration path.1 : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦
              finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
                (empiricalType index) generator duration hDuration.le)
            (fun _index family ↦
              finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  obtain ⟨ambientOpenSet, hAmbientOpen, hAmbientPreimage⟩ :=
    FiniteIntervalHybridBVPath.isInducing_toDerivativePath.isOpen_iff.mp hOpen
  have hTargetAmbient : path.1.toDerivativePath ∈ ambientOpenSet := by
    have : path.1 ∈
        (fun candidate : RengerDirectionalFlowHybridBVPath State duration ↦
          candidate.toDerivativePath) ⁻¹' ambientOpenSet := by
      rw [hAmbientPreimage]
      exact hTarget
    exact this
  have hWeight : ∀ state, Tendsto
      (fun successorIndex ↦
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (empiricalType successorIndex).representative).weight state : ℝ))
      atTop
      (nhds
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight
          state : ℝ)) := by
    intro state
    have hReal : Tendsto
        (fun successorIndex ↦
          (((empiricalType successorIndex).probabilityDensity.weight state : NNReal) : ℝ))
        atTop
        (nhds
          ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state : ℝ)) :=
      (NNReal.continuous_coe.tendsto
        ((rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).weight state)).comp
          (hEmpiricalType state)
    convert hReal using 1
    funext successorIndex
    have hDensity : finiteIIDEmpiricalProbabilityDensity successorIndex
          (empiricalType successorIndex).representative =
        (empiricalType successorIndex).probabilityDensity := by
      rw [← finiteIIDPositiveSampleEmpiricalType_probabilityDensity,
        finiteIIDPositiveSampleEmpiricalType_representative]
    exact congrArg (fun density : FiniteStateProbabilityDensity State ↦
      (density.weight state : ℝ)) hDensity
  have hLower :=
    neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetDeterministicInitialReference_openSet
      generator hDuration path hDynamicRate hInitial
        (fun successorIndex ↦ (empiricalType successorIndex).representative)
        hWeight hAmbientOpen hTargetAmbient
  rw [← hAmbientPreimage]
  simpa only [finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw] using! hLower

/-- On every coordinate-positive finite-rate candidate, Theorem 4.2's exact mixed source attains
the sum of its supplied initial rate and the conditional dynamic action. -/
theorem
neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwoInteriorInitial_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitialRate : initialData.initialRate
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) ≠ ⊤)
    (hInitial : ∀ state,
      0 < rengerDirectionalFlowHybridBVInitialDensity path.1 state)
    {openSet : Set (RengerDirectionalFlowHybridBVPath State duration)}
    (hOpen : IsOpen openSet) (hTarget : path.1 ∈ openSet) :
    -(initialData.initialRate
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) : EReal) -
        (rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration path.1 : EReal) ≤
      liminf
        (fun successorIndex ↦
          scaledEventLogProbability
            (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
              initialData index generator duration hDuration.le)
            (fun _index family ↦
              finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
            finiteStateMarkovJumpParticleSpeed successorIndex openSet)
        atTop := by
  obtain ⟨empiricalType, hEmpiricalType, hInitialAtom⟩ :=
    exists_finiteIIDPositiveEmpiricalTypeSequence_tendsto_and_initialAtomLogLiminf
      initialData (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path)
        hInitialRate
  let initialAtomScaledLog : ℕ → EReal := fun successorIndex ↦
    ENNReal.log
        (initialData.initialEmpiricalTypeLaw successorIndex
          {empiricalType successorIndex}) /
      (finiteStateMarkovJumpParticleSpeed successorIndex : EReal)
  let conditionalScaledLog : ℕ → EReal := fun successorIndex ↦
    scaledEventLogProbability
      (fun index ↦
        finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
          (empiricalType index) generator duration hDuration.le)
      (fun _index family ↦
        finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
      finiteStateMarkovJumpParticleSpeed successorIndex openSet
  let mixedScaledLog : ℕ → EReal := fun successorIndex ↦
    scaledEventLogProbability
      (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
        initialData index generator duration hDuration.le)
      (fun _index family ↦
        finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
      finiteStateMarkovJumpParticleSpeed successorIndex openSet
  have hConditional :
      -(rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration path.1 : EReal) ≤
        liminf conditionalScaledLog atTop := by
    exact
      neg_dynamicRate_le_liminf_scaledEventLogProbability_rengerDirectionalFlowHybridBVTargetEmpiricalTypeReference_openSet
        generator hDuration path hDynamicRate hInitial empiricalType hEmpiricalType hOpen hTarget
  have hInitialAtom' :
      -(initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) : EReal) ≤
        liminf initialAtomScaledLog atTop := by
    simpa only [initialAtomScaledLog, finiteStateMarkovJumpParticleSpeed,
      finiteIIDPositiveSampleSpeed] using hInitialAtom
  have hProductToMixed : ∀ successorIndex,
      initialAtomScaledLog successorIndex + conditionalScaledLog successorIndex ≤
        mixedScaledLog successorIndex := by
    intro successorIndex
    let microscopicEvent :=
      finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration ⁻¹' openSet
    have hMicroscopicEvent : MeasurableSet microscopicEvent :=
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
        hOpen.measurableSet
    have hProbability :
        finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
              (empiricalType successorIndex) generator duration hDuration.le microscopicEvent *
            initialData.initialEmpiricalTypeLaw successorIndex
              {empiricalType successorIndex} ≤
          rengerTheoremFourTwoPositiveReplicaFamilyLaw
            initialData successorIndex generator duration hDuration.le microscopicEvent := by
      rw [rengerTheoremFourTwoPositiveReplicaFamilyLaw,
        finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_apply_eq_sum
          successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
            generator duration hDuration.le hMicroscopicEvent]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun candidate ↦
          finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
              candidate generator duration hDuration.le microscopicEvent *
            initialData.initialEmpiricalTypeLaw successorIndex {candidate})
        (fun _candidate _hCandidate ↦ zero_le)
        (Finset.mem_univ (empiricalType successorIndex))
    have hLogProduct :
        initialAtomScaledLog successorIndex + conditionalScaledLog successorIndex =
          ENNReal.log
              (initialData.initialEmpiricalTypeLaw successorIndex
                  {empiricalType successorIndex} *
                finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
                  (empiricalType successorIndex) generator duration hDuration.le microscopicEvent) /
            (finiteStateMarkovJumpParticleSpeed successorIndex : EReal) := by
      unfold initialAtomScaledLog conditionalScaledLog scaledEventLogProbability microscopicEvent
      rw [ENNReal.log_mul_add, EReal.add_div_of_nonneg_right (by
        exact EReal.coe_nonneg.mpr
          (finiteStateMarkovJumpParticleSpeed_pos successorIndex).le)]
    rw [hLogProduct]
    unfold mixedScaledLog scaledEventLogProbability microscopicEvent
    apply EReal.monotone_div_right_of_nonneg
      (EReal.coe_nonneg.mpr (finiteStateMarkovJumpParticleSpeed_pos successorIndex).le)
    apply ENNReal.log_monotone
    simpa only [mul_comm] using hProbability
  calc
    -(initialData.initialRate
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) : EReal) -
        (rengerDirectionalFlowHybridBVDynamicRate
          generator hDuration path.1 : EReal) =
        -(initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) : EReal) +
          -(rengerDirectionalFlowHybridBVDynamicRate
            generator hDuration path.1 : EReal) := sub_eq_add_neg _ _
    _ ≤ liminf initialAtomScaledLog atTop + liminf conditionalScaledLog atTop :=
      add_le_add hInitialAtom' hConditional
    _ ≤ liminf (initialAtomScaledLog + conditionalScaledLog) atTop :=
      EReal.le_liminf_add
    _ ≤ liminf mixedScaledLog atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hProductToMixed)

end

end FiniteMarkovProcesses.InformationTheory
