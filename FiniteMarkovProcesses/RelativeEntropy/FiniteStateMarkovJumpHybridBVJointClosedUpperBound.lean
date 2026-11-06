/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVJointUpperBound
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVCompleteRate
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpRengerEmpiricalInitialSource

/-!
# Closed upper bounds for random-density hybrid paths

This module upgrades the compact joint upper bound to closed targets.  The first ingredient is
particle-speed exponential tightness inherited through the path coordinate from the exact mixed
compact-containment estimate.
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

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- On the closed conservation graph, the separately carried density rate plus the dynamic rate
is exactly the complete path rate.  Nonadmissible paths agree at infinity; admissible paths use
continuous conservation recovery to identify the graph density with the literal initial trace. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_densityRate_add_dynamicRate_of_mem_graph
    (generator : FiniteStateMarkovGenerator State) {duration : ℝ}
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (pair : FiniteStateProbabilityDensity State ×
      RengerDirectionalFlowHybridBVPath State duration)
    (hPair : pair ∈
      RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate pair.2 =
      initialRate pair.1 +
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2 := by
  by_cases hAdmissible : RengerDirectionalFlowHybridBVAdmissible pair.2 hDuration
  · rw [rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
      generator hDuration initialRate hAdmissible]
    congr 1
    rw [rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
      initialRate hDuration hAdmissible]
    congr 1
    apply FiniteStateProbabilityDensity.injective_realWeight
    have hRecovered :=
      rengerDirectionalFlowHybridBVConservationInitialDensity_eq_initialTrace hDuration
        (rengerDirectionalFlowHybridBVIntegratedContinuity_of_admissible hAdmissible)
    have hRealWeight : pair.1.realWeight =
        fun state => pair.2.initialTrace (Sum.inl state) := hPair.trans hRecovered
    funext state
    change (Real.toNNReal (pair.2.initialTrace (Sum.inl state)) : ℝ) =
      (pair.1.weight state : ℝ)
    have hCoordinate := congrFun hRealWeight state
    change (pair.1.weight state : ℝ) =
      pair.2.initialTrace (Sum.inl state) at hCoordinate
    rw [hCoordinate]
    exact Real.coe_toNNReal _ (hAdmissible.initialDensityNonnegative state)
  · rw [rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
      generator hDuration initialRate hAdmissible,
      rengerDirectionalFlowHybridBVDynamicRate_eq_top_of_not_admissible
        generator hDuration hAdmissible, add_top]

/-- The mixed density/path joint laws are exponentially tight through their path coordinate.
For every real level, one compact hybrid-path container has complement limsup at most the negative
of that level, uniformly over the supplied random empirical initial laws. -/
theorem
    exists_compact_hybridBV_pathTarget_joint_pathTail_limsup_le_neg_level
    (initialEmpiricalTypeLaw : ∀ successorIndex,
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (initialEmpiricalTypeLawProbability : ∀ successorIndex,
      IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) (level : ℝ) :
    ∃ compactPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration),
      IsCompact compactPathTarget ∧
        limsup (fun successorIndex =>
          finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
            initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
              (univ ×ˢ compactPathTargetᶜ)) atTop ≤ ((-level : ℝ) : EReal) := by
  let durationNNReal : NNReal := ⟨duration, hDuration.le⟩
  let sourceExponentCoefficient : ℝ :=
    ((generator.uniformizationRate * durationNNReal : NNReal) : ℝ) *
      (Real.exp 1 - 1)
  let countCutoff : ℝ := sourceExponentCoefficient + level
  let compactPathTarget := finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
    (State := State) duration countCutoff
  have hCompactPathTarget : IsCompact compactPathTarget :=
    isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      duration countCutoff hDuration
  refine ⟨compactPathTarget, hCompactPathTarget, ?_⟩
  have hProbability : ∀ successorIndex,
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
          (initialEmpiricalTypeLaw successorIndex) generator duration hDuration.le
          (univ ×ˢ compactPathTargetᶜ) ≤
        ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
    intro successorIndex
    let : IsProbabilityMeasure (initialEmpiricalTypeLaw successorIndex) :=
      initialEmpiricalTypeLawProbability successorIndex
    have hTail :=
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_pathTail_le
        successorIndex (initialEmpiricalTypeLaw successorIndex) generator durationNNReal
          (by exact_mod_cast hDuration) (by norm_num : (0 : ℝ) < 1) countCutoff
    change finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
        (initialEmpiricalTypeLaw successorIndex) generator duration hDuration.le
        (univ ×ˢ compactPathTargetᶜ) ≤ _ at hTail ⊢
    refine hTail.trans_eq ?_
    apply congrArg ENNReal.ofReal
    dsimp only [countCutoff, sourceExponentCoefficient, durationNNReal]
    push_cast
    ring_nf
  have hScaled : ∀ successorIndex,
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (univ ×ˢ compactPathTargetᶜ) ≤ ((-level : ℝ) : EReal) := by
    intro successorIndex
    unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      scaledEventLogProbability
    simp only [preimage_id]
    refine (EReal.monotone_div_right_of_nonneg
      (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
      (ENNReal.log_monotone (hProbability successorIndex))).trans_eq ?_
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    change (((-(successorIndex + 1 : ℝ) * level : ℝ) : EReal) /
        ((((successorIndex + 1 : ℕ) : ℝ) : EReal))) = ((-level : ℝ) : EReal)
    rw [← EReal.coe_div]
    congr 1
    apply (div_eq_iff (by positivity)).2
    push_cast
    ring
  exact (limsup_le_limsup (Eventually.of_forall hScaled)).trans_eq
    (limsup_const ((-level : ℝ) : EReal))

/-- Closed joint upper bound for one strict complete initial-plus-dynamic level.  Exponential
tightness reduces the closed target to a compact part; the compact joint theorem handles that
part, and the fixed two-set union contributes no particle-speed cost. -/
theorem rengerTheoremFourTwoDensityHybridBVJointClosedLimsup_le_neg_level
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hCompleteCost : ∀ pair ∈ closedTarget,
      ENNReal.ofReal level <
        initialData.initialRate pair.1 +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2) :
    limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          closedTarget) atTop ≤ ((-level : ℝ) : EReal) := by
  rcases exists_compact_hybridBV_pathTarget_joint_pathTail_limsup_le_neg_level
      initialData.initialEmpiricalTypeLaw initialData.initialEmpiricalTypeLaw_probability
        generator duration hDuration level with
    ⟨compactPathTarget, hCompactPathTarget, hPathTailLimsup⟩
  let compactJointTarget := closedTarget ∩ (univ ×ˢ compactPathTarget)
  have hCompactJointTarget : IsCompact compactJointTarget := by
    have hProductCompact : IsCompact
        (univ ×ˢ compactPathTarget : Set
          (FiniteStateProbabilityDensity State ×
            RengerDirectionalFlowHybridBVPath State duration)) :=
      isCompact_univ.prod hCompactPathTarget
    simpa only [compactJointTarget, inter_comm] using
      hProductCompact.inter_right hClosedTarget
  have hCompactCost : ∀ pair ∈ compactJointTarget,
      ENNReal.ofReal level <
        initialData.initialRate pair.1 +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2 := by
    intro pair hPair
    exact hCompleteCost pair hPair.1
  have hCompactLimsup : limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          compactJointTarget) atTop ≤ ((-level : ℝ) : EReal) :=
    rengerTheoremFourTwoDensityHybridBVJointCompactLimsup_le_neg_level
      initialData generator duration hDuration compactJointTarget hCompactJointTarget
        level hLevel hCompactCost
  let partitionTarget : Bool → Set
      (FiniteStateProbabilityDensity State ×
        RengerDirectionalFlowHybridBVPath State duration) := fun isTail =>
    if isTail then univ ×ˢ compactPathTargetᶜ else compactJointTarget
  have hPartitionLimsup : ∀ part ∈ (Finset.univ : Finset Bool),
      limsup (fun successorIndex =>
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (partitionTarget part)) atTop ≤ ((-level : ℝ) : EReal) := by
    intro part _hPart
    cases part <;> simp only [partitionTarget, Bool.false_eq_true, ite_false, ite_true]
    · exact hCompactLimsup
    · exact hPathTailLimsup
  have hPartitionNonempty : (Finset.univ : Finset Bool).Nonempty := by simp
  have hPartitionUnionLimsup : limsup (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          (⋃ part : Bool, partitionTarget part)) atTop ≤ ((-level : ℝ) : EReal) := by
    simpa only [Finset.mem_univ, iUnion_true] using
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJoint_biUnion_limsup_le
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le
          (Finset.univ : Finset Bool) hPartitionNonempty partitionTarget (-level)
            hPartitionLimsup
  have hClosedTargetSubset : closedTarget ⊆ ⋃ part : Bool, partitionTarget part := by
    intro pair hPair
    by_cases hPath : pair.2 ∈ compactPathTarget
    · exact mem_iUnion.mpr ⟨false, by simp [partitionTarget, compactJointTarget, hPair, hPath]⟩
    · exact mem_iUnion.mpr ⟨true, by simp [partitionTarget, hPath]⟩
  have hScaledMonotone : ∀ successorIndex,
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            closedTarget ≤
        finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
          initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
            (⋃ part : Bool, partitionTarget part) := by
    intro successorIndex
    unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      scaledEventLogProbability
    simp only [preimage_id]
    exact EReal.monotone_div_right_of_nonneg
      (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
      (ENNReal.log_monotone (measure_mono hClosedTargetSubset))
  exact (limsup_le_limsup (Eventually.of_forall hScaledMonotone)).trans
    hPartitionUnionLimsup

/-- Restricting the mixed density/path joint law to the conservation graph and one measurable
path event recovers exactly the mixed path law of that event. -/
theorem
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_graph_inter_prod_eq_pathLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (pathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hPathTarget : MeasurableSet pathTarget) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
        initialEmpiricalTypeLaw generator duration hDuration.le
        (RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration ∩
          (univ ×ˢ pathTarget)) =
      finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw successorIndex
        initialEmpiricalTypeLaw generator duration hDuration.le pathTarget := by
  let jointLaw := finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
    initialEmpiricalTypeLaw generator duration hDuration.le
  let : IsProbabilityMeasure jointLaw :=
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_isProbabilityMeasure
      successorIndex initialEmpiricalTypeLaw generator duration hDuration.le
  have hGraphMeasurable :=
    measurableSet_rengerDirectionalFlowHybridBVConservationInitialDensityGraph
      (State := State) hDuration
  have hGraphAlmostEverywhere : ∀ᵐ pair ∂jointLaw,
      pair ∈ RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration :=
    (mem_ae_iff_prob_eq_one hGraphMeasurable).2
      (finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_conservationGraph_eq_one
        successorIndex initialEmpiricalTypeLaw generator duration hDuration)
  calc
    jointLaw
        (RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration ∩
          (univ ×ˢ pathTarget)) = jointLaw (univ ×ˢ pathTarget) :=
      Measure.measure_inter_eq_of_ae hGraphAlmostEverywhere
    _ = jointLaw (Prod.snd ⁻¹' pathTarget) := by
      congr 1
      ext densityPath
      simp
    _ = jointLaw.snd pathTarget := (Measure.snd_apply hPathTarget).symm
    _ = finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw successorIndex
          initialEmpiricalTypeLaw generator duration hDuration.le pathTarget := by
      rw [snd_finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw]

/-- Theorem 4.2 closed-path upper bound on the exact mixed hybrid observation law at one strict
nonnegative complete-rate level. -/
theorem rengerTheoremFourTwoHybridBVObservationLaw_closedLimsup_le_neg_level
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedPathTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedPathTarget : IsClosed closedPathTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hCompleteRate : ∀ path ∈ closedPathTarget,
      ENNReal.ofReal level <
        rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData path) :
    limsup (fun successorIndex =>
      scaledEventLogProbability
        (fun index => rengerTheoremFourTwoHybridBVObservationLaw
          initialData index generator duration hDuration.le)
        (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget) atTop ≤
      ((-level : ℝ) : EReal) := by
  let jointTarget :=
    RengerDirectionalFlowHybridBVConservationInitialDensityGraph hDuration ∩
      (univ ×ˢ closedPathTarget)
  have hJointTargetClosed : IsClosed jointTarget :=
    (isClosed_rengerDirectionalFlowHybridBVConservationInitialDensityGraph
      (State := State) hDuration).inter
        (isClosed_univ.prod hClosedPathTarget)
  have hJointCost : ∀ pair ∈ jointTarget,
      ENNReal.ofReal level <
        initialData.initialRate pair.1 +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration pair.2 := by
    intro pair hPair
    rw [← rengerDirectionalFlowHybridBVCompleteRate_eq_densityRate_add_dynamicRate_of_mem_graph
      generator hDuration initialData.initialRate pair hPair.1]
    exact hCompleteRate pair.2 hPair.2.2
  have hJointUpper :=
    rengerTheoremFourTwoDensityHybridBVJointClosedLimsup_le_neg_level
      initialData generator duration hDuration jointTarget hJointTargetClosed level hLevel
        hJointCost
  have hScaledEquality : (fun successorIndex =>
      finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
        initialData.initialEmpiricalTypeLaw generator duration hDuration.le successorIndex
          jointTarget) =
      (fun successorIndex =>
        scaledEventLogProbability
          (fun index => rengerTheoremFourTwoHybridBVObservationLaw
            initialData index generator duration hDuration.le)
          (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget) := by
    funext successorIndex
    let : IsProbabilityMeasure (initialData.initialEmpiricalTypeLaw successorIndex) :=
      initialData.initialEmpiricalTypeLaw_probability successorIndex
    unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointScaledEventLogProbability
      scaledEventLogProbability rengerTheoremFourTwoHybridBVObservationLaw
    simp only [preimage_id]
    rw [finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_graph_inter_prod_eq_pathLaw
      successorIndex (initialData.initialEmpiricalTypeLaw successorIndex) generator duration
        hDuration closedPathTarget hClosedPathTarget.measurableSet]
  rw [← hScaledEquality]
  exact hJointUpper

/-- Theorem 4.2's exact mixed hybrid observation laws satisfy the literal closed-set upper bound
for the complete initial-plus-dynamic rate. -/
theorem rengerTheoremFourTwoHybridBVObservationLaw_closedUpperBound
    (initialData : RengerTheoremFourTwoInitialData State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun index => rengerTheoremFourTwoHybridBVObservationLaw
          initialData index generator duration hDuration.le)
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData) := by
  intro closedPathTarget hClosedPathTarget
  let scaledLog : ℕ → EReal := fun successorIndex =>
    scaledEventLogProbability
      (fun index => rengerTheoremFourTwoHybridBVObservationLaw
        initialData index generator duration hDuration.le)
      (fun _ => id) finiteIIDPositiveSampleSpeed successorIndex closedPathTarget
  let rateInfimum : EReal :=
    ⨅ path ∈ closedPathTarget,
      (rengerTheoremFourTwoHybridBVCompleteRate generator hDuration initialData path : EReal)
  have hScaledNonpositive : ∀ successorIndex, scaledLog successorIndex ≤ (0 : EReal) := by
    intro successorIndex
    let law := rengerTheoremFourTwoHybridBVObservationLaw
      initialData successorIndex generator duration hDuration.le
    let : IsProbabilityMeasure law :=
      rengerTheoremFourTwoHybridBVObservationLaw_isProbabilityMeasure
        initialData successorIndex generator duration hDuration.le
    have hProbability : law closedPathTarget ≤ 1 := by
      simpa using (measure_mono (subset_univ closedPathTarget) : law closedPathTarget ≤ law univ)
    dsimp only [scaledLog]
    unfold scaledEventLogProbability
    simp only [preimage_id]
    calc
      ENNReal.log (law closedPathTarget) /
          (finiteIIDPositiveSampleSpeed successorIndex : EReal) ≤
          ENNReal.log 1 / (finiteIIDPositiveSampleSpeed successorIndex : EReal) :=
        EReal.monotone_div_right_of_nonneg
          (EReal.coe_nonneg.mpr (finiteIIDPositiveSampleSpeed_pos successorIndex).le)
          (ENNReal.log_monotone hProbability)
      _ = 0 := by simp
  have hLimsupNonpositive : limsup scaledLog atTop ≤ (0 : EReal) :=
    (limsup_le_limsup (Eventually.of_forall hScaledNonpositive)).trans_eq
      (limsup_const (0 : EReal))
  change limsup scaledLog atTop ≤ -rateInfimum
  rw [EReal.le_neg]
  apply le_of_forall_lt
  intro lowerBound hLowerBound
  cases lowerBound with
  | bot => exact EReal.bot_lt_coe 0 |>.trans_le (EReal.neg_nonneg.mpr hLimsupNonpositive)
  | top => exact (not_top_lt hLowerBound).elim
  | coe realLowerBound =>
      by_cases hRealLowerBound : 0 ≤ realLowerBound
      · obtain ⟨level, hLowerLevel, hLevelInfimum⟩ :=
          EReal.lt_iff_exists_real_btwn.mp hLowerBound
        have hRealLowerLevel : realLowerBound < level :=
          EReal.coe_lt_coe_iff.mp hLowerLevel
        have hLevel : 0 ≤ level := hRealLowerBound.trans hRealLowerLevel.le
        have hLevelRate : ∀ path ∈ closedPathTarget,
            ENNReal.ofReal level <
              rengerTheoremFourTwoHybridBVCompleteRate
                generator hDuration initialData path := by
          intro path hPath
          apply EReal.coe_ennreal_lt_coe_ennreal_iff.mp
          rw [EReal.coe_ennreal_ofReal, max_eq_left hLevel]
          exact hLevelInfimum.trans_le
            (iInf_le_of_le path (iInf_le_of_le hPath le_rfl))
        have hLevelUpper : limsup scaledLog atTop ≤ ((-level : ℝ) : EReal) :=
          rengerTheoremFourTwoHybridBVObservationLaw_closedLimsup_le_neg_level
            initialData generator duration hDuration closedPathTarget hClosedPathTarget
              level hLevel hLevelRate
        have hLevelLeNegativeLimsup : (level : EReal) ≤ -limsup scaledLog atTop :=
          EReal.le_neg.mp hLevelUpper
        exact hLowerLevel.trans_le hLevelLeNegativeLimsup
      · have hRealLowerBoundNegative : realLowerBound < 0 := lt_of_not_ge hRealLowerBound
        exact (EReal.coe_lt_coe_iff.mpr hRealLowerBoundNegative).trans_le
          (EReal.neg_nonneg.mpr hLimsupNonpositive)

end

end FiniteMarkovProcesses.InformationTheory
