/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoLargeDeviationRepresentation
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourOneOpenLowerBound
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialPermutation

/-!
# Renger Theorem 4.1 hybrid-BV large-deviation representation

This module realizes the deterministic-initial regime on its actual microscopic law.  The exact
empirical count type of each supplied configuration first yields a initial LDP at
the coordinate-positive limiting density.  That derived initial contract transports the closed
upper bound from the common count-type machinery; the independently proved deterministic lower
bound and the original labelled configurations remain visible in the final representation.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- The exact empirical count type of Theorem 4.1's supplied deterministic configuration. -/
def rengerTheoremFourOneInitialEmpiricalType
    (initialData : RengerTheoremFourOneInitialData State) (successorIndex : ℕ) :
    FiniteIIDPositiveEmpiricalType State successorIndex :=
  finiteIIDPositiveSampleEmpiricalType successorIndex
    (initialData.initialState successorIndex)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The count type of the supplied configuration has exactly its declared empirical density. -/
theorem rengerTheoremFourOneInitialEmpiricalType_probabilityDensity
    (initialData : RengerTheoremFourOneInitialData State) (successorIndex : ℕ) :
    (rengerTheoremFourOneInitialEmpiricalType initialData successorIndex).probabilityDensity =
      initialData.empiricalInitialDensity successorIndex := by
  apply FiniteStateProbabilityDensity.ext
  intro state
  rw [rengerTheoremFourOneInitialEmpiricalType,
    finiteIIDPositiveSampleEmpiricalType_probabilityDensity,
    finiteIIDEmpiricalProbabilityDensity_weight,
    finiteIIDPositiveSampleStateCount]
  exact (initialData.empiricalInitialDensity_eq successorIndex state).symm

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The deterministic limiting-density rate has infimum zero on every set containing its unique
finite-rate point. -/
theorem iInf_rengerTheoremFourOneInitialRate_eq_zero_of_mem
    (initialData : RengerTheoremFourOneInitialData State)
    (target : Set (FiniteStateProbabilityDensity State))
    (hLimit : initialData.limitingDensity ∈ target) :
    (⨅ density, ⨅ (_hDensity : density ∈ target),
        (rengerTheoremFourOneInitialRate initialData density : EReal)) = 0 := by
  apply le_antisymm
  · exact iInf_le_of_le initialData.limitingDensity
      (iInf_le_of_le hLimit (by simp))
  · apply le_iInf
    intro density
    apply le_iInf
    intro _hDensity
    exact EReal.coe_ennreal_nonneg _

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Away from its unique finite-rate point, the deterministic limiting-density rate has infimum
infinity. -/
theorem iInf_rengerTheoremFourOneInitialRate_eq_top_of_not_mem
    (initialData : RengerTheoremFourOneInitialData State)
    (target : Set (FiniteStateProbabilityDensity State))
    (hLimit : initialData.limitingDensity ∉ target) :
    (⨅ density, ⨅ (_hDensity : density ∈ target),
        (rengerTheoremFourOneInitialRate initialData density : EReal)) = ⊤ := by
  apply top_unique
  apply le_iInf
  intro density
  apply le_iInf
  intro hDensity
  have hDensityNe : density ≠ initialData.limitingDensity := by
    intro hDensityEq
    exact hLimit (hDensityEq ▸ hDensity)
  rw [rengerTheoremFourOneInitialRate_of_ne initialData hDensityNe]
  rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Dirac laws at the convergent empirical densities satisfy the deterministic initial closed-set
large-deviation upper bound. -/
theorem rengerTheoremFourOneInitialLaw_hasLargeDeviationUpperBound
    (initialData : RengerTheoremFourOneInitialData State) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun successorIndex =>
          Measure.dirac (initialData.empiricalInitialDensity successorIndex))
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (rengerTheoremFourOneInitialRate initialData) := by
  intro closedTarget hClosedTarget
  have hDensityTendsto : Tendsto initialData.empiricalInitialDensity atTop
      (nhds initialData.limitingDensity) :=
    FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise.mpr
      initialData.empiricalInitialDensity_tendsto
  by_cases hLimit : initialData.limitingDensity ∈ closedTarget
  · rw [iInf_rengerTheoremFourOneInitialRate_eq_zero_of_mem initialData closedTarget hLimit]
    simp only [neg_zero]
    have hScaledNonpositive : ∀ successorIndex,
        scaledEventLogProbability
            (fun index => Measure.dirac (initialData.empiricalInitialDensity index))
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedTarget ≤
          (0 : EReal) := by
      intro successorIndex
      unfold scaledEventLogProbability
      simp only [preimage_id]
      have hProbability :
          Measure.dirac (initialData.empiricalInitialDensity successorIndex) closedTarget ≤ 1 :=
        by simpa using
          (measure_mono (subset_univ closedTarget) :
            Measure.dirac (initialData.empiricalInitialDensity successorIndex) closedTarget ≤
              Measure.dirac (initialData.empiricalInitialDensity successorIndex) univ)
      calc
        ENNReal.log
              (Measure.dirac (initialData.empiricalInitialDensity successorIndex) closedTarget) /
            (finiteIIDPositiveSampleSpeed successorIndex : EReal) ≤
            ENNReal.log 1 / (finiteIIDPositiveSampleSpeed successorIndex : EReal) :=
          EReal.monotone_div_right_of_nonneg
            (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
            (ENNReal.log_monotone hProbability)
        _ = 0 := by simp
    exact (limsup_le_limsup (Eventually.of_forall hScaledNonpositive)).trans_eq
      (limsup_const (0 : EReal))
  · rw [iInf_rengerTheoremFourOneInitialRate_eq_top_of_not_mem
      initialData closedTarget hLimit]
    have hEventuallyOutside : ∀ᶠ successorIndex in atTop,
        initialData.empiricalInitialDensity successorIndex ∉ closedTarget :=
      hDensityTendsto.eventually
        (hClosedTarget.isOpen_compl.mem_nhds hLimit)
    have hEventuallyBottom : ∀ᶠ successorIndex in atTop,
        scaledEventLogProbability
            (fun index => Measure.dirac (initialData.empiricalInitialDensity index))
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedTarget = ⊥ := by
      filter_upwards [hEventuallyOutside] with successorIndex hOutside
      unfold scaledEventLogProbability
      simp only [preimage_id, Measure.dirac_apply' _ hClosedTarget.measurableSet]
      rw [Set.indicator_of_notMem hOutside, ENNReal.log_zero]
      exact EReal.bot_div_of_pos_ne_top
        (EReal.coe_pos.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex)) (by simp)
    rw [limsup_congr hEventuallyBottom, limsup_const]
    simp

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Dirac laws at the convergent empirical densities satisfy the deterministic initial open-set
large-deviation lower bound. -/
theorem rengerTheoremFourOneInitialLaw_hasLargeDeviationLowerBound
    (initialData : RengerTheoremFourOneInitialData State) :
    HasLargeDeviationLowerBound
      (scaledEventLogProbability
        (fun successorIndex =>
          Measure.dirac (initialData.empiricalInitialDensity successorIndex))
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (rengerTheoremFourOneInitialRate initialData) := by
  intro openTarget hOpenTarget
  have hDensityTendsto : Tendsto initialData.empiricalInitialDensity atTop
      (nhds initialData.limitingDensity) :=
    FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise.mpr
      initialData.empiricalInitialDensity_tendsto
  by_cases hLimit : initialData.limitingDensity ∈ openTarget
  · rw [iInf_rengerTheoremFourOneInitialRate_eq_zero_of_mem initialData openTarget hLimit]
    have hEventuallyInside : ∀ᶠ successorIndex in atTop,
        initialData.empiricalInitialDensity successorIndex ∈ openTarget :=
      hDensityTendsto.eventually (hOpenTarget.mem_nhds hLimit)
    have hEventuallyZero : ∀ᶠ successorIndex in atTop,
        scaledEventLogProbability
            (fun index => Measure.dirac (initialData.empiricalInitialDensity index))
            (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex openTarget = 0 := by
      filter_upwards [hEventuallyInside] with successorIndex hInside
      unfold scaledEventLogProbability
      simp [Measure.dirac_apply' _ hOpenTarget.measurableSet, hInside]
    rw [liminf_congr hEventuallyZero, liminf_const]
    simp
  · rw [iInf_rengerTheoremFourOneInitialRate_eq_top_of_not_mem
      initialData openTarget hLimit]
    exact bot_le

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The deterministic limiting-density rate satisfies the boundary continuity contract because
its unique finite-rate point is strictly interior. -/
theorem rengerTheoremFourOneInitialRate_leftContinuousAtLowerBoundary
    (initialData : RengerTheoremFourOneInitialData State) :
    FiniteStateProbabilityDensity.InitialRateIsLeftContinuousAtLowerBoundary
      (rengerTheoremFourOneInitialRate initialData) := by
  intro boundaryDensity hBoundaryDensity sequence _hSequenceInterior hSequence
  have hBoundaryNe : boundaryDensity ≠ initialData.limitingDensity := by
    intro hBoundaryEq
    obtain ⟨state, hState⟩ := hBoundaryDensity
    have hPositive := initialData.limitingDensity_interior state
    rw [← hBoundaryEq, hState] at hPositive
    exact (lt_irrefl 0) hPositive
  have hSequenceTendsto : Tendsto sequence atTop (nhds boundaryDensity) :=
    FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise.mpr hSequence
  have hEventuallyNe : ∀ᶠ successorIndex in atTop,
      sequence successorIndex ≠ initialData.limitingDensity := by
    have hBoundaryOutside : boundaryDensity ∈
        ({initialData.limitingDensity} : Set (FiniteStateProbabilityDensity State))ᶜ := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hBoundaryNe
    exact hSequenceTendsto.eventually
      (isClosed_singleton.isOpen_compl.mem_nhds hBoundaryOutside)
  have hEventuallyTop : ∀ᶠ successorIndex in atTop,
      rengerTheoremFourOneInitialRate initialData (sequence successorIndex) = ⊤ :=
    hEventuallyNe.mono fun _ hNe =>
      rengerTheoremFourOneInitialRate_of_ne initialData hNe
  have hBoundaryTop :
      rengerTheoremFourOneInitialRate initialData boundaryDensity = ⊤ :=
    rengerTheoremFourOneInitialRate_of_ne initialData hBoundaryNe
  rw [hBoundaryTop]
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (⊤ : ENNReal)) atTop (nhds ⊤)).congr'
  filter_upwards [hEventuallyTop] with successorIndex hSuccessorIndex
  exact hSuccessorIndex.symm

/-- Theorem 4.1's deterministic empirical types inhabit the stronger count-type initial contract
without changing their rate, limit, or microscopic source semantics. -/
noncomputable def rengerTheoremFourOneAsTheoremFourTwoInitialData
    (initialData : RengerTheoremFourOneInitialData State) :
    RengerTheoremFourTwoInitialData State where
  initialLaw successorIndex :=
    Measure.dirac (initialData.empiricalInitialDensity successorIndex)
  initialLaw_probability _ := inferInstance
  initialEmpiricalTypeLaw successorIndex :=
    Measure.dirac (rengerTheoremFourOneInitialEmpiricalType initialData successorIndex)
  initialEmpiricalTypeLaw_probability _ := inferInstance
  initialLaw_eq_map_probabilityDensity successorIndex := by
    rw [Measure.map_dirac' (measurable_of_finite _),
      rengerTheoremFourOneInitialEmpiricalType_probabilityDensity]
  initialRate := rengerTheoremFourOneInitialRate initialData
  topology_generates_measurableSpace := rfl
  initialRate_good := rengerTheoremFourOneInitialRate_isGoodRateFunction initialData
  initialUpperBound := rengerTheoremFourOneInitialLaw_hasLargeDeviationUpperBound initialData
  initialLowerBound := rengerTheoremFourOneInitialLaw_hasLargeDeviationLowerBound initialData
  initialRate_leftContinuousAtLowerBoundary :=
    rengerTheoremFourOneInitialRate_leftContinuousAtLowerBoundary initialData

/-- The count-type mixture derived from Theorem 4.1 is exactly the hybrid observation law of the
original labelled deterministic configurations.  Permutation invariance is used explicitly; the
microscopic labelled laws themselves are not identified. -/
theorem rengerTheoremFourOneCountTypeHybridBVObservationLaw_eq_deterministicLaw
    (initialData : RengerTheoremFourOneInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    rengerTheoremFourTwoHybridBVObservationLaw
        (rengerTheoremFourOneAsTheoremFourTwoInitialData initialData)
        successorIndex generator duration hDuration =
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex (initialData.initialState successorIndex)
          generator duration hDuration := by
  have hCountTypeLaw :
      rengerTheoremFourTwoHybridBVObservationLaw
          (rengerTheoremFourOneAsTheoremFourTwoInitialData initialData)
          successorIndex generator duration hDuration =
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
          (rengerTheoremFourOneInitialEmpiricalType initialData successorIndex)
            generator duration hDuration := by
    ext event hEvent
    rw [rengerTheoremFourTwoHybridBVObservationLaw_apply _ _ _ _ _ hEvent]
    change (∫⁻ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
            empiricalType generator duration hDuration event
          ∂Measure.dirac
            (rengerTheoremFourOneInitialEmpiricalType initialData successorIndex)) = _
    rw [lintegral_dirac' _ (measurable_of_finite _)]
  rw [hCountTypeLaw]
  unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
  apply finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_empiricalType_eq
  simp only [rengerTheoremFourOneInitialEmpiricalType,
    finiteIIDPositiveSampleEmpiricalType_representative]

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The complete rate produced by the derived count-type contract is definitionally Theorem
4.1's deterministic limiting-density complete rate. -/
theorem rengerTheoremFourOneAsTheoremFourTwoHybridBVCompleteRate_eq
    (initialData : RengerTheoremFourOneInitialData State)
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration) :
    rengerTheoremFourTwoHybridBVCompleteRate generator hDuration
        (rengerTheoremFourOneAsTheoremFourTwoInitialData initialData) =
      rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData := by
  rfl

/-- Theorem 4.1's actual deterministic-initial microscopic source satisfies the literal
closed-set upper bound at its complete rate. -/
theorem rengerTheoremFourOneDeterministicInitialHybridBV_hasLargeDeviationUpperBound
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun index =>
          finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
            index (initialData.initialState index) generator duration hDuration.le)
        (fun _index family =>
          finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
        finiteStateMarkovJumpParticleSpeed)
      (rengerTheoremFourOneHybridBVCompleteRate generator hDuration initialData) := by
  intro closedPathTarget hClosedPathTarget
  have hGenericUpper :=
    rengerTheoremFourTwoHybridBVObservationLaw_closedUpperBound
      (rengerTheoremFourOneAsTheoremFourTwoInitialData initialData)
        generator duration hDuration closedPathTarget hClosedPathTarget
  let deterministicScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index =>
        finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
          index (initialData.initialState index) generator duration hDuration.le)
      (fun _index family =>
        finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
      finiteStateMarkovJumpParticleSpeed successorIndex closedPathTarget
  let countTypeScaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => rengerTheoremFourTwoHybridBVObservationLaw
        (rengerTheoremFourOneAsTheoremFourTwoInitialData initialData)
          index generator duration hDuration.le)
      (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget
  have hScaledLogEquality : deterministicScaledLog = countTypeScaledLog := by
    funext successorIndex
    unfold deterministicScaledLog countTypeScaledLog scaledEventLogProbability
    simp only [preimage_id]
    congr 1
    congr 1
    rw [← Measure.map_apply
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
      hClosedPathTarget.measurableSet]
    change
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex (initialData.initialState successorIndex)
            generator duration hDuration.le closedPathTarget = _
    rw [← rengerTheoremFourOneCountTypeHybridBVObservationLaw_eq_deterministicLaw
      initialData generator duration hDuration.le successorIndex]
  change limsup deterministicScaledLog atTop ≤ _
  rw [hScaledLogEquality,
    ← rengerTheoremFourOneAsTheoremFourTwoHybridBVCompleteRate_eq
      initialData generator hDuration]
  exact hGenericUpper

/-- Full provenance-bearing Renger Theorem 4.1 representation on the actual deterministic
microscopic source and hybrid-BV carrier. -/
noncomputable def rengerTheoremFourOneHybridBVLargeDeviationRepresentation
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    DensityFluxLargeDeviationRepresentation
      (FiniteStateMarkovJumpPositiveReplicaFamily State)
      (RengerDirectionalFlowHybridBVPath State duration)
      ℝ (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal)
      Renger2018DirectionalFlowProvenance where
  microscopicLaw := fun index =>
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
      index (initialData.initialState index) generator duration hDuration.le
  microscopicLaw_probability := fun index =>
    finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw_isProbabilityMeasure
      index (initialData.initialState index) generator duration hDuration.le
  observation := fun _index family =>
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family
  observation_measurable := fun _index =>
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration
  speed := finiteStateMarkovJumpParticleSpeed
  speed_pos := finiteStateMarkovJumpParticleSpeed_pos
  speed_tendsto_atTop := finiteStateMarkovJumpParticleSpeed_tendsto_atTop
  rateData := rengerDirectionalFlowHybridBVCompleteRateData generator hDuration
    (rengerTheoremFourOneInitialRate initialData)
  topology_generates_measurableSpace :=
    FiniteIntervalHybridBVPath.measurableSpace_eq_borel
  rate_good := by
    simpa only [rengerTheoremFourOneHybridBVCompleteRate] using!
      rengerTheoremFourOneHybridBVCompleteRate_isGoodRateFunction
        generator hDuration initialData
  provenance := ⟨.theoremFourOne⟩
  upperBound := rengerTheoremFourOneDeterministicInitialHybridBV_hasLargeDeviationUpperBound
    generator hDuration initialData
  lowerBound := rengerTheoremFourOneDeterministicInitialHybridBV_hasLargeDeviationLowerBound
    generator hDuration initialData

end

end FiniteMarkovProcesses.InformationTheory
