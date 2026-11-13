/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVConvexCombinationRate
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVUniformStaticRepresentationPath
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourTwoInteriorOpenLowerBound

/-!
# Renger Theorem 4.2 lower-boundary open lower bound

An arbitrary finite-rate boundary candidate is mixed with the admissible uniform static anchor at
weight `1 / (n + 1)`.  These paths converge in the exact hybrid topology, their recovered initial
simplex points approach from the strict interior, the supplied Theorem 4.2 initial-rate boundary
continuity controls the initial sector, and dynamic-action convexity controls the path sector.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

/-- Canonical strictly positive weight used to approach a lower simplex boundary. -/
noncomputable def rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight
    (index : ℕ) : NNReal :=
  1 / ((index : NNReal) + 1)

/-- Every canonical boundary-interior mixing weight is strictly positive. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_pos (index : ℕ) :
    0 < rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index := by
  unfold rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight
  positivity

/-- Every canonical boundary-interior mixing weight is at most one. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_le_one (index : ℕ) :
    rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index ≤ 1 := by
  unfold rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight
  exact (div_le_one (by positivity)).2 (by simp)

/-- Canonical boundary-interior weights vanish at large index. -/
theorem tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop :
    Tendsto rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight atTop (nhds 0) := by
  simpa only [rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal))

/-- Hybrid path obtained by mixing a target with its uniform static interior anchor. -/
noncomputable def rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
  rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath path
    (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path)
    (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index)
    (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index).coe_nonneg
    (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_le_one index)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Boundary-interior approximation paths converge in the exact hybrid topology. -/
theorem tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_atTop
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    Tendsto
      (fun index =>
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index).1)
      atTop (nhds path.1) := by
  have hWeightReal : Tendsto
      (fun index =>
        (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : ℝ))
      atTop (nhds 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop
  simpa only [rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath] using!
    tendsto_rengerDirectionalFlowHybridBVConvexCombinationPath path
      (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path) hWeightReal

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Every approximating initial simplex coordinate is strictly positive. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity_pos
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (state : State) :
    0 < rengerDirectionalFlowHybridBVInitialDensity
      (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index).1 state := by
  rw [rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath,
    rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath_initialDensity]
  exact add_pos_of_nonneg_of_pos (zero_le)
    (mul_pos
      (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_pos index)
      (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath_initialDensity_pos
        path state))

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Recovered initial simplex points converge coordinatewise to the target initial point. -/
theorem
tendstoCoordinatewise_rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    FiniteStateProbabilityDensity.TendstoCoordinatewise
      (fun index => rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index))
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) := by
  intro state
  simp_rw [rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath,
    rengerDirectionalFlowHybridBVConvexCombinationRepresentationPath_initialProbabilityDensity_weight]
  have hFirstCoefficient : Tendsto
      (fun index =>
        1 - rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index)
      atTop (nhds 1) := by
    simpa only [tsub_zero] using
      (show Tendsto (fun _ : ℕ => (1 : NNReal)) atTop (nhds 1) from
        tendsto_const_nhds).sub
        tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop
  simpa only [one_mul, zero_mul, add_zero] using
    (hFirstCoefficient.mul tendsto_const_nhds).add
      (tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop.mul
        tendsto_const_nhds)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Every recovered approximation density lies in the strict simplex interior. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity_isInterior
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
      (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index)).IsInterior :=
  rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity_pos path index

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The supplied Theorem 4.2 boundary premise gives convergence of approximation initial rates. -/
theorem tendsto_rengerTheoremFourTwoInitialRate_boundaryInteriorApproximationPath
    (initialData : RengerTheoremFourTwoInitialData State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hBoundary :
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).IsOnLowerBoundary) :
    Tendsto
      (fun index => initialData.initialRate
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
          (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index)))
      atTop
      (nhds (initialData.initialRate
        (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path))) :=
  initialData.initialRate_leftContinuousAtLowerBoundary
    (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) hBoundary
    (fun index => rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
      (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index))
    (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity_isInterior
      path)
    (tendstoCoordinatewise_rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity
      path)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Dynamic costs of boundary-interior approximations obey the exact convex upper envelope. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_dynamicRate_le
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index).1 ≤
      ((1 - rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : NNReal) :
          ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 +
        (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration
            (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1 := by
  exact rengerDirectionalFlowHybridBVConvexCombinationPath_dynamicRate_le generator path
    (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path)
    (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index)
    (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_le_one index)

/-- Initial cost plus the convex dynamic upper envelope along the boundary approximation. -/
noncomputable def rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
    (generator : FiniteStateMarkovGenerator State)
    (initialData : RengerTheoremFourTwoInitialData State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) : ENNReal :=
  initialData.initialRate
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index)) +
    (((1 - rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : NNReal) :
          ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 +
        (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : ENNReal) *
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration
            (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath path).1)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The approximation upper envelope converges to the original complete finite-sector cost. -/
theorem tendsto_rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate_atTop
    (generator : FiniteStateMarkovGenerator State)
    (initialData : RengerTheoremFourTwoInitialData State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hBoundary :
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).IsOnLowerBoundary) :
    Tendsto
      (rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
        generator initialData path)
      atTop
      (nhds
        (initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1)) := by
  have hWeightENNReal : Tendsto
      (fun index =>
        (rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : ENNReal))
      atTop (nhds 0) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp
      tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop
  have hFirstWeightNNReal : Tendsto
      (fun index =>
        1 - rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index)
      atTop (nhds 1) := by
    simpa only [tsub_zero] using
      (show Tendsto (fun _ : ℕ => (1 : NNReal)) atTop (nhds 1) from
        tendsto_const_nhds).sub
        tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight_atTop
  have hFirstWeightENNReal : Tendsto
      (fun index =>
        ((1 - rengerDirectionalFlowHybridBVBoundaryInteriorMixingWeight index : NNReal) :
          ENNReal))
      atTop (nhds 1) := by
    simpa only [ENNReal.coe_one] using!
      ENNReal.continuous_coe.continuousAt.tendsto.comp hFirstWeightNNReal
  unfold rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
  simpa only [one_mul, zero_mul, add_zero] using
    (tendsto_rengerTheoremFourTwoInitialRate_boundaryInteriorApproximationPath
      initialData path hBoundary).add
      ((ENNReal.Tendsto.mul_const hFirstWeightENNReal (Or.inr hDynamicRate)).add
        (ENNReal.Tendsto.mul_const hWeightENNReal (Or.inr
          (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath_dynamicRate_ne_top
            generator path))))

omit [MeasurableSpace State] [MeasurableSingletonClass State]
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- Every approximating dynamic cost is finite when the target dynamic cost is finite. -/
theorem rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_dynamicRate_ne_top
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (index : ℕ) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index).1 ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt
    (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_dynamicRate_le
      generator path index)
  apply ENNReal.add_lt_top.2
  constructor
  · exact ENNReal.mul_lt_top ENNReal.coe_lt_top hDynamicRate.lt_top
  · exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (rengerDirectionalFlowHybridBVUniformStaticRepresentationPath_dynamicRate_ne_top
        generator path).lt_top

/-- At a lower-boundary candidate, Theorem 4.2 attains the complete initial-plus-dynamic cost on
every hybrid-open neighborhood. -/
theorem
neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwoBoundaryInitial_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitialRate : initialData.initialRate
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) ≠ ⊤)
    (hBoundary :
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).IsOnLowerBoundary)
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
  let lowerBound : EReal :=
    liminf
      (fun successorIndex ↦
        scaledEventLogProbability
          (fun index ↦ rengerTheoremFourTwoPositiveReplicaFamilyLaw
            initialData index generator duration hDuration.le)
          (fun _index family ↦
            finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration family)
          finiteStateMarkovJumpParticleSpeed successorIndex openSet)
      atTop
  have hInitialTendsto :=
    tendsto_rengerTheoremFourTwoInitialRate_boundaryInteriorApproximationPath
      initialData path hBoundary
  have hInitialEventuallyFinite : ∀ᶠ index in atTop,
      initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
            (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index)) ≠ ⊤ := by
    have hLimitLt :
        initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) <
          initialData.initialRate
              (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) + 1 :=
      ENNReal.lt_add_right hInitialRate one_ne_zero
    have hLimitPlusOneLtTop :
        initialData.initialRate
              (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) + 1 < ⊤ :=
      ENNReal.add_lt_top.2 ⟨hInitialRate.lt_top, ENNReal.one_lt_top⟩
    filter_upwards [(tendsto_order.1 hInitialTendsto).2 _ hLimitLt]
      with index hIndex
    exact ne_of_lt (hIndex.trans hLimitPlusOneLtTop)
  have hApproximationInOpen : ∀ᶠ index in atTop,
      (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index).1 ∈
        openSet :=
    (tendsto_rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_atTop path).eventually
      (hOpen.mem_nhds hTarget)
  have hNegativeUpperBound : ∀ᶠ index in atTop,
      -(rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
          generator initialData path index : EReal) ≤ lowerBound := by
    filter_upwards [hInitialEventuallyFinite, hApproximationInOpen]
      with index hApproximationInitialFinite hApproximationTarget
    let approximation :=
      rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath path index
    have hApproximationDynamicFinite :=
      rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_dynamicRate_ne_top
        generator path hDynamicRate index
    have hLower :=
      neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwoInteriorInitial_openSet
        generator hDuration initialData approximation hApproximationDynamicFinite
        hApproximationInitialFinite
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_initialDensity_pos
          path index)
        hOpen hApproximationTarget
    have hActualRateLeUpper :
        initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity approximation) +
          rengerDirectionalFlowHybridBVDynamicRate
            generator hDuration approximation.1 ≤
        rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
          generator initialData path index := by
      unfold rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
      exact add_le_add le_rfl
        (rengerDirectionalFlowHybridBVBoundaryInteriorApproximationPath_dynamicRate_le
          generator path index)
    calc
      -(rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
          generator initialData path index : EReal) ≤
          -((initialData.initialRate
              (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity approximation) +
            rengerDirectionalFlowHybridBVDynamicRate
              generator hDuration approximation.1 : ENNReal) : EReal) := by
        rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
        exact hActualRateLeUpper
      _ = -(initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity approximation) :
              EReal) -
          (rengerDirectionalFlowHybridBVDynamicRate
            generator hDuration approximation.1 : EReal) := by
        rw [EReal.coe_ennreal_add,
          EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
            (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg]
      _ ≤ lowerBound := by
        exact hLower
  have hUpperRateTendsto :=
    tendsto_rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate_atTop
      generator initialData path hDynamicRate hBoundary
  have hNegativeUpperRateTendsto : Tendsto
      (fun index ↦
        -(rengerTheoremFourTwoBoundaryInteriorApproximationUpperRate
          generator initialData path index : EReal))
      atTop
      (nhds
        (-((initialData.initialRate
              (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) +
            rengerDirectionalFlowHybridBVDynamicRate
              generator hDuration path.1 : ENNReal) : EReal))) :=
    (continuous_neg.tendsto _).comp
      (continuous_coe_ennreal_ereal.tendsto _ |>.comp hUpperRateTendsto)
  change _ ≤ lowerBound
  rw [show -(initialData.initialRate
          (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) : EReal) -
        (rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 : EReal) =
      -((initialData.initialRate
            (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) +
          rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 : ENNReal) :
        EReal) by
    rw [EReal.coe_ennreal_add,
      EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
        (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg]]
  exact le_of_tendsto hNegativeUpperRateTendsto hNegativeUpperBound

/-- Every finite-rate Theorem 4.2 representation candidate attains its complete
initial-plus-dynamic cost on every hybrid-open neighborhood.  The proof separates the genuine
lower boundary, where left-continuity is required, from the coordinate-positive simplex
interior. -/
theorem
neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwo_openSet
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (hInitialRate : initialData.initialRate
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path) ≠ ⊤)
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
  by_cases hBoundary :
      (rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path).IsOnLowerBoundary
  · exact
      neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwoBoundaryInitial_openSet
        generator hDuration initialData path hDynamicRate hInitialRate hBoundary hOpen hTarget
  · apply
      neg_initialRate_add_dynamicRate_le_liminf_scaledEventLogProbability_rengerTheoremFourTwoInteriorInitial_openSet
        generator hDuration initialData path hDynamicRate hInitialRate _ hOpen hTarget
    intro state
    apply pos_iff_ne_zero.mpr
    intro hZero
    exact hBoundary ⟨state, hZero⟩

end

end FiniteMarkovProcesses.InformationTheory
