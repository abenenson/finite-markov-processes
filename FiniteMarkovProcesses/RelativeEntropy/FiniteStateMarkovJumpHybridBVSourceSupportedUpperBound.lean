/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteJumpHistoryRengerHybridBVSourceSupport
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVConditionalUpperBound
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVSourceSupportClassification
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpInitialBoundaryHybridBVControl

/-!
# Source-supported upper bounds for finite-state hybrid-BV jump observations

This module combines the ambient continuous-test exponential estimate with the exact
source-support classification.  Positive singular interior flow is handled by the ambient dual;
positive recovered initial flow is handled by the independent initial-layer jump estimate.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability
open PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- The compact count-controlled empirical container restricted to topology-closed
source-kinematic support. -/
noncomputable def finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
    (duration countCutoff : ℝ) (hDuration : 0 < duration) :
    Set (RengerDirectionalFlowHybridBVPath State duration) :=
  finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff ∩
    {path | RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration}

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The source-supported count container is compact in the published hybrid topology.  The
proof transports sequential closure only through the metric projected-closure subtype and does
not assert that the ambient hybrid carrier is first countable. -/
theorem isCompact_finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
    (duration countCutoff : ℝ) (hDuration : 0 < duration) :
    IsCompact
      (finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
        (State := State) duration countCutoff hDuration) := by
  let l1Bound := empiricalDensityDirectionalFlowL1Bound duration countCutoff
  let variationBound := empiricalDensityDirectionalFlowVariationBound countCutoff
  have hL1Bound : l1Bound < ∞ := by
    exact empiricalDensityDirectionalFlowL1Bound_lt_top duration countCutoff
  have hVariationBound : variationBound < ∞ := by
    exact empiricalDensityDirectionalFlowVariationBound_lt_top countCutoff
  let projectedPath := FiniteIntervalHybridBVUniformEnvelopeProjectedPath
    (EmpiricalDensityDirectionalFlowCoordinate State) duration l1Bound variationBound
  let lift := finiteIntervalHybridBVUniformEnvelopeL1Inverse
    (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
      hDuration l1Bound variationBound hVariationBound
  let supportedProjected : Set projectedPath :=
    {projected |
      RengerDirectionalFlowHybridBVSourceKinematicSupport
        (lift projected).1 hDuration}
  let : CompactSpace projectedPath :=
    isCompact_iff_compactSpace.mp
      (isCompact_closure_toL1Path_image_uniformL1VariationEnvelope
        hDuration hL1Bound hVariationBound)
  have hSupportedProjectedClosed : IsClosed supportedProjected := by
    apply IsSeqClosed.isClosed
    intro projectedPaths projectedLimit hPaths hTendsto
    have hLiftTendsto : Tendsto (fun sequenceIndex => lift (projectedPaths sequenceIndex))
        atTop (nhds (lift projectedLimit)) :=
      (continuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
        (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
        hDuration l1Bound variationBound hVariationBound).continuousAt.tendsto.comp hTendsto
    have hPathTendsto : Tendsto
        (fun sequenceIndex => (lift (projectedPaths sequenceIndex)).1)
        atTop (nhds (lift projectedLimit).1) :=
      tendsto_subtype_rng.mp hLiftTendsto
    exact rengerDirectionalFlowHybridBVSourceKinematicSupport_of_tendsto
      hDuration (fun sequenceIndex => (lift (projectedPaths sequenceIndex)).1)
        (lift projectedLimit).1 (fun sequenceIndex => hPaths sequenceIndex) hPathTendsto
  have hSupportedProjectedCompact : IsCompact supportedProjected :=
    hSupportedProjectedClosed.isCompact
  have hImageCompact := hSupportedProjectedCompact.image
    (continuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
      (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
      hDuration l1Bound variationBound hVariationBound)
  have hImage : lift '' supportedProjected =
      {path : FiniteIntervalHybridBVUniformL1VariationCompactPath
          (EmpiricalDensityDirectionalFlowCoordinate State) duration l1Bound variationBound |
        RengerDirectionalFlowHybridBVSourceKinematicSupport path.1 hDuration} := by
    ext path
    constructor
    · rintro ⟨projected, hProjected, rfl⟩
      exact hProjected
    · intro hPath
      rcases finiteIntervalHybridBVUniformEnvelopeL1Inverse_surjective
          (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
          hDuration l1Bound variationBound hVariationBound path with
        ⟨projected, hProjected⟩
      refine ⟨projected, ?_, hProjected⟩
      change RengerDirectionalFlowHybridBVSourceKinematicSupport
        (lift projected).1 hDuration
      change lift projected = path at hProjected
      rw [hProjected]
      exact hPath
  rw [hImage] at hImageCompact
  have hSubtypeImage := hImageCompact.image continuous_subtype_val
  have hSubtypeImageSet :
      ((fun path : FiniteIntervalHybridBVUniformL1VariationCompactPath
          (EmpiricalDensityDirectionalFlowCoordinate State) duration l1Bound variationBound =>
        path.1) ''
        {path | RengerDirectionalFlowHybridBVSourceKinematicSupport path.1 hDuration}) =
      finiteIntervalHybridBVUniformL1VariationCompactContainer
          l1Bound variationBound ∩
        {path | RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration} := by
    ext path
    constructor
    · rintro ⟨supportedPath, hSupportedPath, rfl⟩
      exact ⟨supportedPath.2, hSupportedPath⟩
    · rintro ⟨hContainer, hSupported⟩
      exact ⟨⟨path, hContainer⟩, hSupported, rfl⟩
  rw [hSubtypeImageSet] at hSubtypeImage
  simpa only [finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer,
    finiteStateMarkovJumpEmpiricalHybridBVCompactContainer, l1Bound, variationBound,
    ] using hSubtypeImage

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Every ordered empirical observation in the count container belongs to its source-supported
compact refinement. -/
theorem empiricalDensityDirectionalFlowTotalHybridBVObservation_mem_sourceSupportedContainer
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration countCutoff : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (hCount : (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) ≤
      (successorIndex + 1 : ℝ) * countCutoff) :
    empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories ∈
      finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
        duration countCutoff hDuration := by
  constructor
  · exact empiricalDensityDirectionalFlowTotalHybridBVObservation_mem_compactContainer
      successorIndex histories duration countCutoff hDuration hOrdered hCount
  · rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
      successorIndex duration histories hOrdered]
    exact empiricalDensityDirectionalFlowExplicitHybridBVPath_sourceKinematicSupport
      successorIndex histories duration hDuration hOrdered

/-- A compact source-supported target above one dynamic-rate level has a finite mixed cover by
ambient dual neighborhoods and initial-boundary superexponential neighborhoods. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVSourceSupportedCompact_le
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (hSupport : ∀ path ∈ compactTarget,
      RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    ∃ prefactor : ℕ, ∀ (successorIndex : ℕ)
      (initialConfiguration : Fin (successorIndex + 1) → State),
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration.le compactTarget ≤
        (prefactor : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  classical
  have hNeighborhood (path : compactTarget) :
      ∃ neighborhood : Set (RengerDirectionalFlowHybridBVPath State duration),
        IsOpen neighborhood ∧ path.1 ∈ neighborhood ∧
          ∀ (successorIndex : ℕ)
            (initialConfiguration : Fin (successorIndex + 1) → State),
            finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
                successorIndex initialConfiguration generator duration hDuration.le
                neighborhood ≤
              ENNReal.ofReal
                (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
    rcases (hSupport path.1 path.2).finiteRateOrSingularFlow_or_initialFlowPos with
      hDualSupport | ⟨transition, hInitialFlow⟩
    · have hDualRate : ENNReal.ofReal level <
          rengerDirectionalFlowHybridBVDualRate generator path.1 := by
        rw [rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_of_finiteRateOrSingularFlow
          hDuration generator hDualSupport]
        exact hDynamicRate path.1 path.2
      unfold rengerDirectionalFlowHybridBVDualRate at hDualRate
      obtain ⟨test, hTest⟩ := lt_iSup_iff.mp hDualRate
      have hEvaluation : level <
          rengerDirectionalFlowHybridBVDualEvaluation generator test path.1 :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLevel).mp hTest
      let neighborhood : Set (RengerDirectionalFlowHybridBVPath State duration) :=
        {candidate | level <
          rengerDirectionalFlowHybridBVDualEvaluation generator test candidate}
      refine ⟨neighborhood,
        isOpen_lt continuous_const
          (continuous_rengerDirectionalFlowHybridBVDualEvaluation generator test),
        hEvaluation, ?_⟩
      intro successorIndex initialConfiguration
      exact (measure_mono fun candidate hCandidate => by
        change level ≤ rengerDirectionalFlowHybridBVDualEvaluation generator test candidate
        exact hCandidate.le).trans
        (finiteStateMarkovJumpDeterministicInitialHybridBVDualEvaluation_ge_le_exponential
          successorIndex initialConfiguration generator duration test hDuration.le level)
    · exact
        exists_open_initialBoundaryFlowNeighborhood_probability_le_of_initialTrace_flow_pos
          generator hDuration path.1 transition hInitialFlow level hLevel
  choose neighborhood hNeighborhoodOpen hPathNeighborhood hNeighborhoodProbability using
    hNeighborhood
  have hCover : compactTarget ⊆ ⋃ path, neighborhood path := by
    intro path hPath
    exact mem_iUnion.mpr ⟨⟨path, hPath⟩, hPathNeighborhood ⟨path, hPath⟩⟩
  rcases hCompactTarget.elim_finite_subcover neighborhood hNeighborhoodOpen hCover with
    ⟨points, hPoints⟩
  refine ⟨points.card, ?_⟩
  intro successorIndex initialConfiguration
  let law := finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    successorIndex initialConfiguration generator duration hDuration.le
  let exponentialLevel :=
    ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level))
  calc
    law compactTarget ≤ law (⋃ path ∈ points, neighborhood path) :=
      measure_mono hPoints
    _ ≤ ∑ path ∈ points, law (neighborhood path) :=
      measure_biUnion_finset_le points _
    _ ≤ ∑ _path ∈ points, exponentialLevel := by
      apply Finset.sum_le_sum
      intro path _
      exact hNeighborhoodProbability path successorIndex initialConfiguration
    _ = (points.card : ℝ≥0∞) * exponentialLevel := by simp

/-- The deterministic observation law restricted to the broad compact count container is carried
by its compact source-supported refinement. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVInterContainer_le_sourceSupported
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration countCutoff : ℝ)
    (hDuration : 0 < duration)
    (target : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hTarget : MeasurableSet target) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration.le
        (target ∩ finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
          (State := State) duration countCutoff) ≤
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration.le
        (target ∩
          finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
            duration countCutoff hDuration) := by
  have hCompact := isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
    (State := State) duration countCutoff hDuration
  have hSourceCompact :=
    isCompact_finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff hDuration
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw]
  rw [Measure.map_apply
      (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration)
      (hTarget.inter hCompact.isClosed.measurableSet),
    Measure.map_apply
      (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration)
      (hTarget.inter hSourceCompact.isClosed.measurableSet)]
  apply measure_mono_ae
  filter_upwards [
    ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration.le] with histories hOrdered
  intro hMembership
  refine ⟨hMembership.1, hMembership.2, ?_⟩
  rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    successorIndex duration histories hOrdered]
  exact empiricalDensityDirectionalFlowExplicitHybridBVPath_sourceKinematicSupport
    successorIndex histories duration hDuration hOrdered

/-- Configuration-uniform finite-sample closed-set upper bound for the published dynamic rate.
The compact source support is covered by ambient-dual or initial-boundary neighborhoods, while
the broad-container complement is controlled by the independent jump-count Chernoff estimate. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVClosed_le_dynamicRate
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    ∃ prefactor : ℕ, ∀ (successorIndex : ℕ)
      (initialConfiguration : Fin (successorIndex + 1) → State),
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration.le closedTarget ≤
        ((prefactor + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  let durationNNReal : NNReal := ⟨duration, hDuration.le⟩
  let sourceExponentCoefficient : ℝ :=
    ((generator.uniformizationRate * durationNNReal : NNReal) : ℝ) *
      (Real.exp 1 - 1)
  let countCutoff : ℝ := sourceExponentCoefficient + level
  let compactContainer :=
    finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff
  let sourceSupportedContainer :=
    finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff hDuration
  have hCompactContainer : IsCompact compactContainer :=
    isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      duration countCutoff hDuration
  have hSourceSupportedContainer : IsCompact sourceSupportedContainer :=
    isCompact_finiteStateMarkovJumpSourceSupportedEmpiricalHybridBVCompactContainer
      duration countCutoff hDuration
  have hCompactTarget : IsCompact (closedTarget ∩ sourceSupportedContainer) :=
    by simpa only [inter_comm] using
      hSourceSupportedContainer.inter_right hClosedTarget
  have hCompactSupport : ∀ path ∈ closedTarget ∩ sourceSupportedContainer,
      RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration := by
    intro path hPath
    exact hPath.2.2
  have hCompactDynamicRate : ∀ path ∈ closedTarget ∩ sourceSupportedContainer,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
    intro path hPath
    exact hDynamicRate path hPath.1
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVSourceSupportedCompact_le
      generator duration hDuration (closedTarget ∩ sourceSupportedContainer)
        hCompactTarget hCompactSupport level hLevel hCompactDynamicRate with
    ⟨prefactor, hCompactBound⟩
  refine ⟨prefactor, ?_⟩
  intro successorIndex initialConfiguration
  let law := finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    successorIndex initialConfiguration generator duration hDuration.le
  let exponentialLevel : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level))
  have hTail : law compactContainerᶜ ≤ exponentialLevel := by
    have hChernoff :=
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_compl_compactContainer_le
        successorIndex initialConfiguration generator durationNNReal
          (by exact_mod_cast hDuration) (by norm_num : (0 : ℝ) < 1) countCutoff
    change law compactContainerᶜ ≤ exponentialLevel
    refine hChernoff.trans_eq ?_
    apply congrArg ENNReal.ofReal
    dsimp only [countCutoff, sourceExponentCoefficient, durationNNReal,
      exponentialLevel]
    push_cast
    ring_nf
  have hContainerToSource : law (closedTarget ∩ compactContainer) ≤
      law (closedTarget ∩ sourceSupportedContainer) := by
    exact
      finiteStateMarkovJumpDeterministicInitialHybridBVInterContainer_le_sourceSupported
        successorIndex initialConfiguration generator duration countCutoff hDuration
          closedTarget hClosedTarget.measurableSet
  have hCompact : law (closedTarget ∩ sourceSupportedContainer) ≤
      (prefactor : ℝ≥0∞) * exponentialLevel := by
    exact hCompactBound successorIndex initialConfiguration
  have hTargetSubset : closedTarget ⊆
      (closedTarget ∩ compactContainer) ∪ compactContainerᶜ := by
    intro path hPath
    by_cases hContainer : path ∈ compactContainer
    · exact Or.inl ⟨hPath, hContainer⟩
    · exact Or.inr hContainer
  change law closedTarget ≤ ((prefactor + 1 : ℕ) : ℝ≥0∞) * exponentialLevel
  calc
    law closedTarget ≤
        law ((closedTarget ∩ compactContainer) ∪ compactContainerᶜ) :=
      measure_mono hTargetSubset
    _ ≤ law (closedTarget ∩ compactContainer) + law compactContainerᶜ :=
      measure_union_le _ _
    _ ≤ law (closedTarget ∩ sourceSupportedContainer) + law compactContainerᶜ :=
      add_le_add hContainerToSource le_rfl
    _ ≤ (prefactor : ℝ≥0∞) * exponentialLevel + exponentialLevel :=
      add_le_add hCompact hTail
    _ = ((prefactor + 1 : ℕ) : ℝ≥0∞) * exponentialLevel := by
      push_cast
      ring

/-- Full deterministic-initial closed-set upper bound for the published dynamic rate in literal
particle-speed limsup form. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDynamicRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget)
        atTop ≤ (-level : ℝ) := by
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVClosed_le_dynamicRate
      generator duration hDuration closedTarget hClosedTarget level hLevel hDynamicRate with
    ⟨prefactor, hProbability⟩
  have hUpper : ∀ successorIndex,
      finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget ≤
        (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) := by
    intro successorIndex
    unfold finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
    refine (EReal.monotone_div_right_of_nonneg
      (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
      (ENNReal.log_monotone
        (hProbability successorIndex (initialConfiguration successorIndex)))).trans_eq ?_
    have hPrefactorPositive : 0 < (prefactor + 1 : ℝ) := by positivity
    rw [show (((prefactor + 1 : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal (prefactor + 1 : ℝ) by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (ENNReal.ofReal_natCast (prefactor + 1)).symm]
    rw [ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos hPrefactorPositive,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    have hReal :
        (Real.log (prefactor + 1 : ℝ) +
            -(successorIndex + 1 : ℝ) * level) /
          (successorIndex + 1 : ℝ) =
        Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level := by
      field_simp
      ring
    simpa only [EReal.coe_add, EReal.coe_div, Nat.cast_add, Nat.cast_one,
      EReal.coe_natCast] using
      congrArg (fun value : ℝ => (value : EReal)) hReal
  have hUpperLimit : Tendsto (fun successorIndex =>
      (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) :
        ℕ → EReal) atTop (nhds ((-level : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using
      (fixedFinitePrefactorLog_div_particleCount_tendsto_zero prefactor).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => level) atTop (nhds level))
  exact (limsup_le_limsup (Eventually.of_forall hUpper)).trans_eq hUpperLimit.limsup_eq

end

end FiniteMarkovProcesses.InformationTheory
