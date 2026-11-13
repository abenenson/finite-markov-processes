/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteEmpiricalTypeInitialAtomSelection
public import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensityLargeDeviation

/-!
# Diagonal empirical atoms from an initial large-deviation lower bound

This module converts a simplex-valued initial-law lower bound into one exact sequence of empirical
count types.  A slow diagonal advances through shrinking coordinate neighborhoods only after the
fixed-neighborhood lower estimate is valid.  In every active neighborhood the selected type has
maximum singleton mass, so the simplex-event mass is lost only through the explicit polynomial
ambient type count.

The construction is the source/lattice seam needed by random-initial path lower bounds.  It does
not yet combine the selected atom with a conditional path law or use lower-boundary continuity.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] in
/-- If one simplex-event mass is bounded by the number of empirical types times one selected
atom, its scaled logarithm is bounded by that atom's scaled logarithm plus the explicit
polynomial type-count overhead.  Zero masses remain extended-real bottom values. -/
theorem scaledEventLogProbability_le_typeOverhead_add_atomScaledLog_of_eventMass_le
    (successorIndex : ℕ)
    (initialLaw : Measure (FiniteStateProbabilityDensity State))
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (event : Set (FiniteStateProbabilityDensity State))
    (hEventMass : initialLaw event ≤
      (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
        initialEmpiricalTypeLaw {empiricalType}) :
    scaledEventLogProbability (fun _index ↦ initialLaw) (fun _index ↦ id)
        finiteIIDPositiveSampleSpeed successorIndex event ≤
      (finiteEmpiricalTypeLogarithmicOverhead
          (Fintype.card State) successorIndex : EReal) +
        ENNReal.log (initialEmpiricalTypeLaw {empiricalType}) /
          (finiteIIDPositiveSampleSpeed successorIndex : EReal) := by
  have hCard :
      (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) ≤
        (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal) := by
    exact_mod_cast card_finiteIIDPositiveEmpiricalType_le
      (State := State) successorIndex
  have hProbability : initialLaw event ≤
      (((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal) *
        initialEmpiricalTypeLaw {empiricalType} :=
    hEventMass.trans (by gcongr)
  unfold scaledEventLogProbability finiteIIDPositiveSampleSpeed
  change ENNReal.log (initialLaw event) /
      ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) ≤ _
  refine (EReal.monotone_div_right_of_nonneg
    (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
    (ENNReal.log_monotone hProbability)).trans_eq ?_
  have hPolynomialPositive :
      0 < ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) := by
    positivity
  rw [ENNReal.log_mul_add]
  rw [show ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ENNReal)) =
      ENNReal.ofReal ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) by
        exact (ENNReal.ofReal_natCast _).symm]
  rw [ENNReal.log_ofReal_of_pos hPolynomialPositive]
  change (((Real.log
      ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) : ℝ) : EReal) +
        ENNReal.log (initialEmpiricalTypeLaw {empiricalType})) /
      ((((successorIndex + 1 : ℕ) : ℝ) : EReal)) = _
  rw [EReal.add_div_of_nonneg_right (by positivity)]
  congr 1
  rw [show ((((successorIndex + 2) ^ Fintype.card State : ℕ) : ℝ)) =
      (successorIndex + 2 : ℝ) ^ Fintype.card State by norm_num,
    Real.log_pow, ← EReal.coe_div]
  norm_cast
  unfold finiteEmpiricalTypeLogarithmicOverhead
  push_cast
  field_simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] in
/-- A finite initial rate at one target density supplies a slowly shrinking sequence of exact
empirical count types.  Their densities converge to the target; eventually each selected atom
dominates its complete shrinking-neighborhood mass up to the ambient finite type count, and that
event mass already satisfies the requested stagewise exponential lower threshold. -/
theorem exists_finiteIIDPositiveEmpiricalTypeSequence_tendsto_and_eventMass_le_card_mul_atom
    (initialData : RengerTheoremFourTwoInitialData State)
    (target : FiniteStateProbabilityDensity State)
    (hInitialRate : initialData.initialRate target ≠ ⊤) :
    ∃ stage : ℕ → ℕ,
      Tendsto stage atTop atTop ∧
      ∃ empiricalType :
          (successorIndex : ℕ) → FiniteIIDPositiveEmpiricalType State successorIndex,
        FiniteStateProbabilityDensity.TendstoCoordinatewise
          (fun successorIndex ↦ (empiricalType successorIndex).probabilityDensity) target ∧
        ∀ᶠ successorIndex in atTop,
          let event := finiteStateProbabilityDensityCoordinateNeighborhood
            target (stage successorIndex)
          ((-(initialData.initialRate target).toReal -
              1 / ((stage successorIndex : ℝ) + 1) : ℝ) : EReal) <
              scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
                finiteIIDPositiveSampleSpeed successorIndex event ∧
            0 < initialData.initialLaw successorIndex event ∧
            initialData.initialLaw successorIndex event ≤
              (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
                initialData.initialEmpiricalTypeLaw successorIndex
                  {empiricalType successorIndex} := by
  have hInitialLower (stage : ℕ) :
      -(initialData.initialRate target : EReal) ≤
        liminf
          (fun successorIndex ↦
            scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
              finiteIIDPositiveSampleSpeed successorIndex
                (finiteStateProbabilityDensityCoordinateNeighborhood target stage))
          atTop := by
    have hOpen := isOpen_finiteStateProbabilityDensityCoordinateNeighborhood target stage
    have hTarget := mem_finiteStateProbabilityDensityCoordinateNeighborhood target stage
    calc
      -(initialData.initialRate target : EReal) ≤
          -(⨅ density, ⨅ (_hDensity : density ∈
              finiteStateProbabilityDensityCoordinateNeighborhood target stage),
              (initialData.initialRate density : EReal)) := by
        rw [EReal.neg_le_neg_iff]
        exact iInf_le_of_le target (iInf_le_of_le hTarget le_rfl)
      _ ≤ liminf
          (fun successorIndex ↦
            scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
              finiteIIDPositiveSampleSpeed successorIndex
                (finiteStateProbabilityDensityCoordinateNeighborhood target stage))
          atTop := initialData.initialLowerBound _ hOpen
  have hStageThreshold (stage : ℕ) :
      ((-(initialData.initialRate target).toReal -
          1 / ((stage : ℝ) + 1) : ℝ) : EReal) <
        -(initialData.initialRate target : EReal) := by
    rw [← EReal.coe_ennreal_toReal hInitialRate, ← EReal.coe_neg,
      EReal.coe_lt_coe_iff]
    have hMargin : 0 < 1 / ((stage : ℝ) + 1) := by positivity
    linarith
  have hEventuallyStage (stage : ℕ) :
      ∀ᶠ successorIndex in atTop,
        ((-(initialData.initialRate target).toReal -
            1 / ((stage : ℝ) + 1) : ℝ) : EReal) <
          scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
            finiteIIDPositiveSampleSpeed successorIndex
              (finiteStateProbabilityDensityCoordinateNeighborhood target stage) :=
    eventually_lt_of_lt_liminf
      ((hStageThreshold stage).trans_le (hInitialLower stage))
  let cutoff : ℕ → ℕ := fun stage ↦
    Classical.choose (eventually_atTop.1 (hEventuallyStage stage))
  have hCutoff (stage successorIndex : ℕ) (hSuccessorIndex : cutoff stage ≤ successorIndex) :
      ((-(initialData.initialRate target).toReal -
          1 / ((stage : ℝ) + 1) : ℝ) : EReal) <
        scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
          finiteIIDPositiveSampleSpeed successorIndex
            (finiteStateProbabilityDensityCoordinateNeighborhood target stage) :=
    Classical.choose_spec (eventually_atTop.1 (hEventuallyStage stage))
      successorIndex hSuccessorIndex
  let stage := finiteEmpiricalTypeDiagonalStage cutoff
  have hStage : Tendsto stage atTop atTop :=
    finiteEmpiricalTypeDiagonalStage_tendsto_atTop cutoff
  let empiricalType :
      (successorIndex : ℕ) → FiniteIIDPositiveEmpiricalType State successorIndex :=
    fun successorIndex ↦
      finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet successorIndex
        (initialData.initialEmpiricalTypeLaw successorIndex)
        (finiteStateProbabilityDensityCoordinateNeighborhood
          target (stage successorIndex))
  have hEventually : ∀ᶠ successorIndex in atTop,
      let event := finiteStateProbabilityDensityCoordinateNeighborhood
        target (stage successorIndex)
      ((-(initialData.initialRate target).toReal -
          1 / ((stage successorIndex : ℝ) + 1) : ℝ) : EReal) <
            scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
              finiteIIDPositiveSampleSpeed successorIndex event ∧
        0 < initialData.initialLaw successorIndex event ∧
        initialData.initialLaw successorIndex event ≤
          (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
            initialData.initialEmpiricalTypeLaw successorIndex
              {empiricalType successorIndex} := by
    filter_upwards
        [eventually_cutoff_finiteEmpiricalTypeDiagonalStage_le cutoff] with
        successorIndex hSuccessorIndex
    let event := finiteStateProbabilityDensityCoordinateNeighborhood
      target (stage successorIndex)
    have hThreshold := hCutoff (stage successorIndex) successorIndex hSuccessorIndex
    have hEventMassPositive : 0 < initialData.initialLaw successorIndex event := by
      by_contra hEventMass
      have hEventMassZero : initialData.initialLaw successorIndex event = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp hEventMass)
      have hScaledBottom :
          scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
              finiteIIDPositiveSampleSpeed successorIndex event = ⊥ := by
        unfold scaledEventLogProbability
        change ENNReal.log (initialData.initialLaw successorIndex event) /
            (finiteIIDPositiveSampleSpeed successorIndex : EReal) = ⊥
        rw [hEventMassZero, ENNReal.log_zero]
        exact EReal.bot_div_of_pos_ne_top
          (EReal.coe_pos.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex)) (by simp)
      rw [hScaledBottom] at hThreshold
      exact (not_lt_of_ge bot_le) hThreshold
    have hLatticeNonempty :
        ∃ candidate : FiniteIIDPositiveEmpiricalType State successorIndex,
          candidate.probabilityDensity ∈ event := by
      by_contra hCandidate
      have hPreimageEmpty :
          FiniteIIDPositiveEmpiricalType.probabilityDensity ⁻¹' event =
            (∅ : Set (FiniteIIDPositiveEmpiricalType State successorIndex)) := by
        ext candidate
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        exact fun hCandidateEvent ↦ hCandidate ⟨candidate, hCandidateEvent⟩
      have hInitialEventMassZero : initialData.initialLaw successorIndex event = 0 := by
        rw [initialData.initialLaw_eq_map_probabilityDensity,
          Measure.map_apply (measurable_of_finite _)
            (isOpen_finiteStateProbabilityDensityCoordinateNeighborhood
              target (stage successorIndex)).measurableSet,
          hPreimageEmpty, measure_empty]
      exact hEventMassPositive.ne' hInitialEventMassZero
    have hEventMassBound :
        initialData.initialLaw successorIndex event ≤
          (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
            initialData.initialEmpiricalTypeLaw successorIndex
              {empiricalType successorIndex} := by
      rw [initialData.initialLaw_eq_map_probabilityDensity]
      exact map_probabilityDensity_apply_le_card_mul_maximumMassInDensitySet_singleton
        successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
          (isOpen_finiteStateProbabilityDensityCoordinateNeighborhood
            target (stage successorIndex)).measurableSet hLatticeNonempty
    exact ⟨hThreshold, hEventMassPositive, hEventMassBound⟩
  have hEmpiricalTypeDensity :
      FiniteStateProbabilityDensity.TendstoCoordinatewise
        (fun successorIndex ↦ (empiricalType successorIndex).probabilityDensity) target := by
    apply tendstoCoordinatewise_of_mem_finiteStateProbabilityDensityCoordinateNeighborhood
      target stage _ hStage
    filter_upwards [hEventually] with successorIndex hSuccessorIndex
    let event := finiteStateProbabilityDensityCoordinateNeighborhood
      target (stage successorIndex)
    have hLatticeNonempty :
        ∃ candidate : FiniteIIDPositiveEmpiricalType State successorIndex,
          candidate.probabilityDensity ∈ event := by
      by_contra hCandidate
      have hPreimageEmpty :
          FiniteIIDPositiveEmpiricalType.probabilityDensity ⁻¹' event =
            (∅ : Set (FiniteIIDPositiveEmpiricalType State successorIndex)) := by
        ext candidate
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        exact fun hCandidateEvent ↦ hCandidate ⟨candidate, hCandidateEvent⟩
      have hInitialEventMassZero : initialData.initialLaw successorIndex event = 0 := by
        rw [initialData.initialLaw_eq_map_probabilityDensity,
          Measure.map_apply (measurable_of_finite _)
            (isOpen_finiteStateProbabilityDensityCoordinateNeighborhood
              target (stage successorIndex)).measurableSet,
          hPreimageEmpty, measure_empty]
      exact hSuccessorIndex.2.1.ne' hInitialEventMassZero
    exact
      finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet_probabilityDensity_mem
        successorIndex (initialData.initialEmpiricalTypeLaw successorIndex)
          event hLatticeNonempty
  exact ⟨stage, hStage, empiricalType, hEmpiricalTypeDensity, hEventually⟩

omit [MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
  [DiscreteTopology State] [BorelSpace State] in
/-- A finite-rate target of the supplied initial LDP admits one exact empirical count-type
sequence converging to that target whose singleton masses already attain the target initial rate
on the particle-number exponential scale.  The polynomial number of count types vanishes through
the explicit logarithmic overhead, not through an unrecorded subexponential assumption. -/
theorem exists_finiteIIDPositiveEmpiricalTypeSequence_tendsto_and_initialAtomLogLiminf
    (initialData : RengerTheoremFourTwoInitialData State)
    (target : FiniteStateProbabilityDensity State)
    (hInitialRate : initialData.initialRate target ≠ ⊤) :
    ∃ empiricalType :
        (successorIndex : ℕ) → FiniteIIDPositiveEmpiricalType State successorIndex,
      FiniteStateProbabilityDensity.TendstoCoordinatewise
          (fun successorIndex ↦ (empiricalType successorIndex).probabilityDensity) target ∧
        -(initialData.initialRate target : EReal) ≤
          liminf
            (fun successorIndex ↦
              ENNReal.log
                  (initialData.initialEmpiricalTypeLaw successorIndex
                    {empiricalType successorIndex}) /
                (finiteIIDPositiveSampleSpeed successorIndex : EReal))
            atTop := by
  obtain ⟨stage, hStage, empiricalType, hEmpiricalTypeDensity, hEventually⟩ :=
    exists_finiteIIDPositiveEmpiricalTypeSequence_tendsto_and_eventMass_le_card_mul_atom
      initialData target hInitialRate
  let atomScaledLog : ℕ → EReal := fun successorIndex ↦
    ENNReal.log
        (initialData.initialEmpiricalTypeLaw successorIndex
          {empiricalType successorIndex}) /
      (finiteIIDPositiveSampleSpeed successorIndex : EReal)
  let lowerLog : ℕ → EReal := fun successorIndex ↦
    ((-(initialData.initialRate target).toReal -
      1 / ((stage successorIndex : ℝ) + 1) -
      finiteEmpiricalTypeLogarithmicOverhead
        (Fintype.card State) successorIndex : ℝ) : EReal)
  have hLower : ∀ᶠ successorIndex in atTop,
      lowerLog successorIndex ≤ atomScaledLog successorIndex := by
    filter_upwards [hEventually] with successorIndex hSuccessorIndex
    let event := finiteStateProbabilityDensityCoordinateNeighborhood
      target (stage successorIndex)
    have hEventUpper :
        scaledEventLogProbability initialData.initialLaw (fun _ ↦ id)
            finiteIIDPositiveSampleSpeed successorIndex event ≤
          (finiteEmpiricalTypeLogarithmicOverhead
              (Fintype.card State) successorIndex : EReal) +
            atomScaledLog successorIndex := by
      simpa only [atomScaledLog] using!
        scaledEventLogProbability_le_typeOverhead_add_atomScaledLog_of_eventMass_le
          successorIndex (initialData.initialLaw successorIndex)
            (initialData.initialEmpiricalTypeLaw successorIndex)
            (empiricalType successorIndex) event hSuccessorIndex.2.2
    have hThresholdUpper :
        ((-(initialData.initialRate target).toReal -
          1 / ((stage successorIndex : ℝ) + 1) : ℝ) : EReal) ≤
            atomScaledLog successorIndex +
              (finiteEmpiricalTypeLogarithmicOverhead
                (Fintype.card State) successorIndex : EReal) := by
      calc
        ((-(initialData.initialRate target).toReal -
            1 / ((stage successorIndex : ℝ) + 1) : ℝ) : EReal) ≤
            (finiteEmpiricalTypeLogarithmicOverhead
                (Fintype.card State) successorIndex : EReal) +
              atomScaledLog successorIndex :=
          hSuccessorIndex.1.le.trans hEventUpper
        _ = atomScaledLog successorIndex +
            (finiteEmpiricalTypeLogarithmicOverhead
              (Fintype.card State) successorIndex : EReal) := add_comm _ _
    have hSubtract :
        ((-(initialData.initialRate target).toReal -
          1 / ((stage successorIndex : ℝ) + 1) : ℝ) : EReal) -
            (finiteEmpiricalTypeLogarithmicOverhead
              (Fintype.card State) successorIndex : EReal) ≤
          atomScaledLog successorIndex := by
      apply (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).2
      exact hThresholdUpper
    simpa only [lowerLog, EReal.coe_sub] using hSubtract
  have hMargin : Tendsto
      (fun successorIndex ↦ 1 / ((stage successorIndex : ℝ) + 1))
      atTop (nhds 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hStage
  have hOverhead : Tendsto
      (finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State))
      atTop (nhds 0) :=
    finiteEmpiricalTypeLogarithmicOverhead_tendsto_zero (Fintype.card State)
  have hLowerLimit : Tendsto lowerLog atTop
      (nhds ((-(initialData.initialRate target).toReal : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hMargin).sub hOverhead
  refine ⟨empiricalType, hEmpiricalTypeDensity, ?_⟩
  calc
    -(initialData.initialRate target : EReal) = liminf lowerLog atTop := by
      rw [← EReal.coe_ennreal_toReal hInitialRate, ← EReal.coe_neg]
      exact hLowerLimit.liminf_eq.symm
    _ ≤ liminf atomScaledLog atTop := Filter.liminf_le_liminf hLower

end

end FiniteMarkovProcesses.InformationTheory
