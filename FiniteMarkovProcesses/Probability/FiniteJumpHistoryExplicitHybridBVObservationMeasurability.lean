/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryExplicitHybridBVObservation

/-!
# Measurability of the explicit finite-history hybrid-BV observation

This module equips the explicit empirical density--directional-flow construction with its
source-facing regularity theorem.  The proof is topological: fixed-count history slices vary
continuously in their event times, state words are discrete, and the unbounded count carrier is
the corresponding topological sum.  On the ordered physical subtype every restricted Dirac is a
full interior Dirac, so the complete graph-valued observation is continuous and hence Borel
measurable.

No coordinatewise characterization of the Borel sigma algebra of the uncountable vague-test
product is used.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

namespace FiniteJumpHistory

/-- One finite history restricted to the strictly ordered physical-time carrier. -/
def OrderedCarrier (State : Type u) (duration : ℝ) :=
  {history : FiniteJumpHistory State // history.OrderedBefore duration}

instance instTopologicalSpaceOrderedCarrier
    [TopologicalSpace (FiniteJumpHistory State)] :
    TopologicalSpace (OrderedCarrier State duration) :=
  inferInstanceAs (TopologicalSpace
    {history : FiniteJumpHistory State // history.OrderedBefore duration})

instance instMeasurableSpaceOrderedCarrier
    [MeasurableSpace (FiniteJumpHistory State)] :
    MeasurableSpace (OrderedCarrier State duration) :=
  inferInstanceAs (MeasurableSpace
    {history : FiniteJumpHistory State // history.OrderedBefore duration})

/-- The supplied countable base descends to the original ordered finite-history subtype. -/
instance instSecondCountableTopologyOrderedCarrier
    [TopologicalSpace (FiniteJumpHistory State)]
    [SecondCountableTopology (FiniteJumpHistory State)] :
    SecondCountableTopology (OrderedCarrier State duration) :=
  TopologicalSpace.secondCountableTopology_induced
    (OrderedCarrier State duration) (FiniteJumpHistory State) Subtype.val

/-- The supplied Borel structure descends to the original ordered finite-history subtype. -/
instance instBorelSpaceOrderedCarrier
    [TopologicalSpace (FiniteJumpHistory State)]
    [MeasurableSpace (FiniteJumpHistory State)]
    [BorelSpace (FiniteJumpHistory State)] :
    BorelSpace (OrderedCarrier State duration) :=
  inferInstanceAs (BorelSpace
    {history : FiniteJumpHistory State // history.OrderedBefore duration})

/-- Open sets of the original ordered carrier are measurable under its supplied Borel
structure. -/
instance instOpensMeasurableSpaceOrderedCarrier
    [TopologicalSpace (FiniteJumpHistory State)]
    [MeasurableSpace (FiniteJumpHistory State)]
    [BorelSpace (FiniteJumpHistory State)] :
    OpensMeasurableSpace (OrderedCarrier State duration) :=
  BorelSpace.opensMeasurable

end FiniteJumpHistory

/-- A positive finite replica family whose every history lies in the ordered physical carrier. -/
abbrev OrderedPositiveFiniteJumpHistoryReplicas
    (State : Type u) (successorIndex : ℕ) (duration : ℝ) :=
  Fin (successorIndex + 1) → FiniteJumpHistory.OrderedCarrier State duration

/-- The original finite ordered replica family has measurable open sets under the supplied
carrier witnesses. -/
instance instOpensMeasurableSpaceOrderedPositiveFiniteJumpHistoryReplicas
    [TopologicalSpace (FiniteJumpHistory State)]
    [MeasurableSpace (FiniteJumpHistory State)]
    [SecondCountableTopology (FiniteJumpHistory State)]
    [BorelSpace (FiniteJumpHistory State)] :
    OpensMeasurableSpace
      (OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration) := by
  unfold OrderedPositiveFiniteJumpHistoryReplicas
  infer_instance

namespace PositiveFiniteJumpHistoryReplicas

/-- Forget the ordered-carrier proofs while retaining the complete finite histories. -/
def orderedReplicaHistories
    (successorIndex : ℕ) (duration : ℝ)
    (histories : OrderedPositiveFiniteJumpHistoryReplicas
      State successorIndex duration) :
    PositiveFiniteJumpHistoryReplicas State successorIndex :=
  fun replica => (histories replica).val

/-- The explicit hybrid-BV observation as a function on the ordered source carrier. -/
def orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    (successorIndex : ℕ) (duration : ℝ)
    (histories : OrderedPositiveFiniteJumpHistoryReplicas
      State successorIndex duration) :
    FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  empiricalDensityDirectionalFlowExplicitHybridBVPath
    successorIndex (orderedReplicaHistories successorIndex duration histories) duration
    fun replica => by
      change ((histories replica).val).OrderedBefore duration
      exact (histories replica).property

section Topological

variable [TopologicalSpace State] [DiscreteTopology State]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] [DiscreteTopology State] in
/-- Initial-state extraction is continuous for the natural countable topological-sum history
carrier. -/
theorem continuous_finiteJumpHistory_initialState :
    Continuous (FiniteJumpHistory.initialState : FiniteJumpHistory State → State) := by
  rw [continuous_sigma_iff]
  intro eventCount
  exact (continuous_apply (0 : Fin (eventCount + 1))).comp continuous_fst

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- One normalized microscopic event increment varies continuously on a fixed-count history
slice.  Its state-word dependence is locally constant and it is independent of event times. -/
theorem continuous_empiricalDensityDirectionalFlowEventIncrementL1Value_fixedCount
    (successorIndex eventCount : ℕ) (index : Fin eventCount) :
    Continuous fun data :
        (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
      empiricalDensityDirectionalFlowEventIncrementL1Value successorIndex
        ⟨eventCount, data⟩ index := by
  let stateIncrement := fun states : Fin (eventCount + 1) → State =>
    empiricalDensityDirectionalFlowEventIncrementL1Value successorIndex
      ⟨eventCount, states, fun _ => 0⟩ index
  have hStateIncrement : Continuous stateIncrement := continuous_of_discreteTopology
  convert hStateIncrement.comp continuous_fst using 1
  funext data
  rfl

/-- The strong-`L1` contribution of all events in one complete finite history. -/
def singleHistoryDensityDirectionalFlowEventL1Path
    (successorIndex : ℕ) (duration : ℝ)
    (history : FiniteJumpHistory State) :
    FiniteIntervalL1Path
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  ∑ index : Fin history.jumpCount,
    finiteCoordinateVectorRightEventStepL1Path duration
      (history.jumpTimes index)
      (empiricalDensityDirectionalFlowEventIncrementL1Value
        successorIndex history index)

/-- Fixed-count slice of one history's strong-`L1` event contribution. -/
def fixedCountHistoryDensityDirectionalFlowEventL1Path
    (successorIndex eventCount : ℕ) (duration : ℝ)
    (data : (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) :
    FiniteIntervalL1Path
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  ∑ index : Fin eventCount,
    finiteCoordinateVectorRightEventStepL1Path duration (data.2 index)
      (empiricalDensityDirectionalFlowEventIncrementL1Value
        successorIndex ⟨eventCount, data⟩ index)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every fixed-count strong-`L1` event slice is continuous. -/
theorem continuous_fixedCountHistoryDensityDirectionalFlowEventL1Path
    (successorIndex eventCount : ℕ) (duration : ℝ) :
    Continuous (fixedCountHistoryDensityDirectionalFlowEventL1Path
      (State := State) successorIndex eventCount duration) := by
  unfold fixedCountHistoryDensityDirectionalFlowEventL1Path
    finiteCoordinateVectorRightEventStepL1Path
  apply continuous_finsetSum Finset.univ
  intro index _hIndex
  apply continuous_finsetSum Finset.univ
  intro coordinate _hCoordinate
  have hEventTime : Continuous fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) => data.2 index :=
    (continuous_apply index).comp continuous_snd
  have hIncrement : Continuous fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
        (empiricalDensityDirectionalFlowEventIncrementL1Value
          successorIndex ⟨eventCount, data⟩ index) coordinate :=
    (PiLp.proj (𝕜 := ℝ) (p := 1)
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
      coordinate).continuous.comp
        (continuous_empiricalDensityDirectionalFlowEventIncrementL1Value_fixedCount
          successorIndex eventCount index)
  exact (continuous_finiteCoordinateRightEventStepL1Path duration coordinate).comp
    (hEventTime.prodMk hIncrement)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A single history's complete vector-event strong-`L1` contribution is continuous across the
unbounded topological-sum count carrier. -/
theorem continuous_singleHistoryDensityDirectionalFlowEventL1Path
    (successorIndex : ℕ) (duration : ℝ) :
    Continuous fun history : FiniteJumpHistory State =>
      singleHistoryDensityDirectionalFlowEventL1Path
        successorIndex duration history := by
  rw [continuous_sigma_iff]
  intro eventCount
  change Continuous (fixedCountHistoryDensityDirectionalFlowEventL1Path
    (State := State) successorIndex eventCount duration)
  exact continuous_fixedCountHistoryDensityDirectionalFlowEventL1Path
    (State := State) successorIndex eventCount duration

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The complete event contribution of a positive replica family is continuous in strong
`L1`. -/
theorem continuous_empiricalDensityDirectionalFlowEventL1Path
    (successorIndex : ℕ) (duration : ℝ) :
    Continuous fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      ∑ replica, singleHistoryDensityDirectionalFlowEventL1Path
        successorIndex duration (histories replica) := by
  apply continuous_finsetSum Finset.univ
  intro replica _hReplica
  exact (continuous_singleHistoryDensityDirectionalFlowEventL1Path
    successorIndex duration).comp (continuous_apply replica)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The tagged initial empirical density, with zero initial directional flow, depends
continuously on the complete replica family. -/
theorem continuous_empiricalDensityDirectionalFlowInitialL1Value
    (successorIndex : ℕ) :
    Continuous fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalDensityDirectionalFlowInitialL1Value successorIndex histories := by
  apply (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro coordinate
  cases coordinate with
  | inl state =>
      unfold empiricalInitialDensity
      apply Continuous.div_const
      apply continuous_finsetSum Finset.univ
      intro replica _hReplica
      exact (continuous_of_discreteTopology : Continuous fun occupied : State =>
        FiniteJumpHistory.stateMembershipIndicator occupied state).comp
          (continuous_finiteJumpHistory_initialState.comp (continuous_apply replica))
  | inr edge => exact continuous_const

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The explicit strong-`L1` component of the empirical observation is continuous on the full
finite-history replica carrier. -/
theorem continuous_empiricalDensityDirectionalFlowExplicitL1Path
    (successorIndex : ℕ) (duration : ℝ) :
    Continuous fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalDensityDirectionalFlowExplicitL1Path
        successorIndex histories duration := by
  have hInitial := (continuous_finiteIntervalConstantL1Path
    (Value := FiniteCoordinateL1Value
      (EmpiricalDensityDirectionalFlowCoordinate State)) duration).comp
      (continuous_empiricalDensityDirectionalFlowInitialL1Value successorIndex)
  have hEvents := continuous_empiricalDensityDirectionalFlowEventL1Path
    (State := State) successorIndex duration
  have hEventFormula :
      (fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
        finiteCoordinateVectorEventStepL1PathSum duration
          (fun event : EmpiricalDensityDirectionalFlowEventIndex
              successorIndex histories =>
            (histories event.1).jumpTimes event.2)
          (fun event => empiricalDensityDirectionalFlowEventIncrementL1Value
            successorIndex (histories event.1) event.2)) =
      fun histories => ∑ replica,
        singleHistoryDensityDirectionalFlowEventL1Path
          successorIndex duration (histories replica) := by
    funext histories
    unfold finiteCoordinateVectorEventStepL1PathSum
      singleHistoryDensityDirectionalFlowEventL1Path
    rw [Fintype.sum_sigma]
  rw [show (fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalDensityDirectionalFlowExplicitL1Path successorIndex histories duration) =
      fun histories =>
        finiteIntervalConstantL1Path duration
          (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories) +
        ∑ replica, singleHistoryDensityDirectionalFlowEventL1Path
          successorIndex duration (histories replica) by
    funext histories
    unfold empiricalDensityDirectionalFlowExplicitL1Path
    exact congrArg
      (finiteIntervalConstantL1Path duration
        (empiricalDensityDirectionalFlowInitialL1Value successorIndex histories) + ·)
      (congrFun hEventFormula histories)]
  exact hInitial.add hEvents

/-- Full (unrestricted) finite weighted-Dirac derivative contributed by one history in one tagged
coordinate. -/
def singleHistoryDensityDirectionalFlowFullDerivative
    (successorIndex : ℕ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (history : FiniteJumpHistory State) : VagueSignedMeasure ℝ :=
  finiteWeightedDiracVagueSignedMeasure
    (fun index : Fin history.jumpCount => history.jumpTimes index)
    (fun index => empiricalDensityDirectionalFlowEventIncrement
      successorIndex history index coordinate)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A single history's full finite atomic derivative is continuous across the unbounded count
carrier. -/
theorem continuous_singleHistoryDensityDirectionalFlowFullDerivative
    (successorIndex : ℕ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    Continuous fun history : FiniteJumpHistory State =>
      singleHistoryDensityDirectionalFlowFullDerivative
        successorIndex coordinate history := by
  rw [continuous_sigma_iff]
  intro eventCount
  unfold singleHistoryDensityDirectionalFlowFullDerivative
    FiniteJumpHistory.jumpCount FiniteJumpHistory.jumpTimes
  change Continuous fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) =>
    finiteWeightedDiracVagueSignedMeasure
      (fun index : Fin eventCount => data.2 index)
      (fun index => empiricalDensityDirectionalFlowEventIncrement
        successorIndex ⟨eventCount, data⟩ index coordinate)
  apply continuous_finiteWeightedDiracVagueSignedMeasure
  · intro index
    exact (continuous_apply index).comp continuous_snd
  · intro index
    exact (PiLp.proj (𝕜 := ℝ) (p := 1)
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ)
      coordinate).continuous.comp
        (continuous_empiricalDensityDirectionalFlowEventIncrementL1Value_fixedCount
          successorIndex eventCount index)

/-- Full finite weighted-Dirac derivative of a positive replica family, before physical-time
restriction. -/
def empiricalDensityDirectionalFlowFullDerivative
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    VagueSignedMeasure ℝ :=
  VagueSignedMeasure.ofSignedMeasure <|
    ∑ replica, (singleHistoryDensityDirectionalFlowFullDerivative
      successorIndex coordinate (histories replica)).toSignedMeasure

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The full finite atomic derivative of a replica family is continuous in the complete source
histories. -/
theorem continuous_empiricalDensityDirectionalFlowFullDerivative
    (successorIndex : ℕ)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    Continuous fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
      empiricalDensityDirectionalFlowFullDerivative
        successorIndex histories coordinate := by
  rw [VagueSignedMeasure.continuous_iff_continuousTestIntegral]
  intro test
  have hTerm (replica : Fin (successorIndex + 1)) : Continuous
      (fun histories : PositiveFiniteJumpHistoryReplicas State successorIndex =>
        (singleHistoryDensityDirectionalFlowFullDerivative
          successorIndex coordinate (histories replica)).continuousTestIntegral test) :=
    (VagueSignedMeasure.continuous_continuousTestIntegral test).comp
      ((continuous_singleHistoryDensityDirectionalFlowFullDerivative
        successorIndex coordinate).comp (continuous_apply replica))
  have hSum := continuous_finsetSum Finset.univ fun replica _hReplica => hTerm replica
  simpa only [empiricalDensityDirectionalFlowFullDerivative,
    VagueSignedMeasure.continuousTestIntegral_finsetSum,
    Finset.sum_filter, Finset.filter_true_of_mem] using hSum

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] in
/-- The replica full derivative is exactly the single finite weighted-Dirac sum indexed by all
replica events. -/
theorem empiricalDensityDirectionalFlowFullDerivative_eq_finiteWeighted
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    empiricalDensityDirectionalFlowFullDerivative
        successorIndex histories coordinate =
      finiteWeightedDiracVagueSignedMeasure
        (fun event : EmpiricalDensityDirectionalFlowEventIndex
            successorIndex histories =>
          (histories event.1).jumpTimes event.2)
        (fun event => empiricalDensityDirectionalFlowEventIncrement
          successorIndex (histories event.1) event.2 coordinate) := by
  unfold empiricalDensityDirectionalFlowFullDerivative
    singleHistoryDensityDirectionalFlowFullDerivative
    finiteWeightedDiracVagueSignedMeasure
  simp only [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
    Fintype.sum_sigma]

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] in
/-- On the ordered physical carrier, every explicitly restricted derivative equals the continuous
full finite atomic derivative. -/
theorem orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_derivative
    (successorIndex : ℕ) (duration : ℝ)
    (histories : OrderedPositiveFiniteJumpHistoryReplicas
      State successorIndex duration)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    (orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
      successorIndex duration histories).toDerivativePath.derivative coordinate =
        empiricalDensityDirectionalFlowFullDerivative successorIndex
          (orderedReplicaHistories successorIndex duration histories) coordinate := by
  rw [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation,
    empiricalDensityDirectionalFlowExplicitHybridBVPath_derivative_eq_finiteRestricted]
  rw [finiteRestrictedWeightedDiracVagueSignedMeasure_eq_finiteWeighted_of_mem]
  · exact (empiricalDensityDirectionalFlowFullDerivative_eq_finiteWeighted
      successorIndex
      (orderedReplicaHistories successorIndex duration histories) coordinate).symm
  · intro event
    change ((histories event.1).val).jumpTimes event.2 ∈ Ioo 0 duration
    exact (histories event.1).property.1 event.2

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
  [DecidableEq State] [DiscreteTopology State] in
/-- Forgetting the ordered proofs is continuous into the complete replica-history carrier. -/
theorem continuous_orderedReplicaHistories
    (successorIndex : ℕ) (duration : ℝ) :
    Continuous (orderedReplicaHistories
      (State := State) successorIndex duration) := by
  apply continuous_pi
  intro replica
  exact continuous_subtype_val.comp (continuous_apply replica)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The exact ordered-source-to-hybrid-BV observation is continuous for the published strong-`L1`
plus vague-derivative topology. -/
theorem continuous_orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    (successorIndex : ℕ) (duration : ℝ) :
    Continuous
      (orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
        (State := State) successorIndex duration) := by
  rw [FiniteIntervalHybridBVPath.isInducing_toDerivativePath.continuous_iff,
    FiniteIntervalL1DerivativePath.isInducing_hybridTopologyEmbedding.continuous_iff]
  have hPath : Continuous fun histories :
      OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration =>
    empiricalDensityDirectionalFlowExplicitL1Path successorIndex
      (orderedReplicaHistories successorIndex duration histories) duration :=
    (continuous_empiricalDensityDirectionalFlowExplicitL1Path
      (State := State) successorIndex duration).comp
        (continuous_orderedReplicaHistories successorIndex duration)
  have hDerivativeTest : Continuous fun histories :
      OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration =>
      fun coordinate => fun test : FiniteOpenIntervalVanishingContinuousTest duration =>
        (empiricalDensityDirectionalFlowFullDerivative successorIndex
          (orderedReplicaHistories successorIndex duration histories) coordinate)
            |>.continuousTestIntegral test.1 := by
    apply continuous_pi
    intro coordinate
    apply continuous_pi
    intro test
    exact (VagueSignedMeasure.continuous_continuousTestIntegral test.1).comp
      ((continuous_empiricalDensityDirectionalFlowFullDerivative
        (State := State) successorIndex coordinate).comp
          (continuous_orderedReplicaHistories successorIndex duration))
  let target :
      OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration →
        FiniteIntervalL1Path
            (EmpiricalDensityDirectionalFlowCoordinate State) duration ×
          (EmpiricalDensityDirectionalFlowCoordinate State →
            FiniteOpenIntervalVanishingContinuousTest duration → ℝ) :=
    fun histories =>
      (empiricalDensityDirectionalFlowExplicitL1Path successorIndex
          (orderedReplicaHistories
            (State := State) successorIndex duration histories) duration,
        fun coordinate test =>
          (empiricalDensityDirectionalFlowFullDerivative successorIndex
            (orderedReplicaHistories
              (State := State) successorIndex duration histories) coordinate)
              |>.continuousTestIntegral test.1)
  have hTarget : Continuous target := hPath.prodMk hDerivativeTest
  have hFormula :
      (FiniteIntervalL1DerivativePath.hybridTopologyEmbedding ∘
        FiniteIntervalHybridBVPath.toDerivativePath ∘
          orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
            (State := State) successorIndex duration) = target := by
    funext (histories :
      OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration)
    dsimp only [Function.comp_apply,
      FiniteIntervalL1DerivativePath.hybridTopologyEmbedding,
      FiniteIntervalL1DerivativePath.interiorDerivativeTestIntegralFamily,
      target]
    apply Prod.ext
    · change
        (orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
            (State := State) successorIndex duration histories).toDerivativePath.toL1Path = _
      exact empiricalDensityDirectionalFlowExplicitHybridBVPath_toL1Path
        (State := State) successorIndex
        (orderedReplicaHistories
          (State := State) successorIndex duration histories) duration
        (fun replica => (histories replica).property)
    · funext coordinate test
      change
        ((orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
          (State := State) successorIndex duration histories).toDerivativePath.derivative
            coordinate).continuousTestIntegral test.1 =
          (empiricalDensityDirectionalFlowFullDerivative successorIndex
            (orderedReplicaHistories
              (State := State) successorIndex duration histories) coordinate).continuousTestIntegral
                test.1
      rw [orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation_derivative
        (State := State)]
  rw [hFormula]
  exact hTarget

variable [BorelSpace State]

/-- The exact ordered-source-to-hybrid-BV observation is Borel measurable. -/
theorem measurable_orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    (successorIndex : ℕ) (duration : ℝ) :
    Measurable
      (orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
        (State := State) successorIndex duration) := by
  let : OpensMeasurableSpace
      (OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration) :=
    inferInstance
  exact (continuous_orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    (State := State) successorIndex duration).measurable

/-- Canonical no-jump fallback in the ordered physical carrier.  It is used only off the
almost-sure ordered support to totalize the macroscopic observation. -/
noncomputable def fallbackOrderedFiniteJumpHistory
    [Nonempty State] (duration : ℝ) : FiniteJumpHistory.OrderedCarrier State duration :=
  ⟨⟨0, (fun _ => Classical.choice (inferInstance : Nonempty State)), Fin.elim0⟩, by
    change ((∀ index : Fin 0, 0 < Fin.elim0 index ∧ Fin.elim0 index < duration) ∧
      StrictMono (Fin.elim0 : Fin 0 → ℝ))
    constructor
    · intro index
      exact Fin.elim0 index
    · intro index
      exact Fin.elim0 index⟩

/-- Send an arbitrary finite history to itself when it is physically ordered and to the fixed
no-jump history otherwise. -/
noncomputable def orderedFiniteJumpHistoryOrFallback
    [Nonempty State] (duration : ℝ) (history : FiniteJumpHistory State) :
    FiniteJumpHistory.OrderedCarrier State duration := by
  classical
  exact if hOrdered : history.OrderedBefore duration then ⟨history, hOrdered⟩
    else fallbackOrderedFiniteJumpHistory duration

omit [Fintype State] [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The history-level ordered-or-fallback totalization is measurable. -/
theorem measurable_orderedFiniteJumpHistoryOrFallback
    [Nonempty State] (duration : ℝ) :
    Measurable (orderedFiniteJumpHistoryOrFallback (State := State) duration) := by
  classical
  let orderedSet : Set (FiniteJumpHistory State) :=
    {history | history.OrderedBefore duration}
  have hOrderedBranch : Measurable fun history : orderedSet =>
      (⟨history.1, history.2⟩ : FiniteJumpHistory.OrderedCarrier State duration) :=
    measurable_subtype_coe.subtype_mk
  have hFallbackBranch : Measurable fun _history : {history : FiniteJumpHistory State //
      history ∉ orderedSet} =>
      fallbackOrderedFiniteJumpHistory (State := State) duration := measurable_const
  change Measurable (fun history : FiniteJumpHistory State =>
    if hOrdered : history ∈ orderedSet then
      (⟨history, hOrdered⟩ : FiniteJumpHistory.OrderedCarrier State duration)
    else fallbackOrderedFiniteJumpHistory (State := State) duration)
  exact Measurable.dite (β := FiniteJumpHistory.OrderedCarrier State duration)
    hOrderedBranch hFallbackBranch
    (FiniteJumpHistory.measurableSet_orderedBefore (State := State) duration)

/-- Coordinatewise ordered-or-fallback totalization of a positive replica family. -/
noncomputable def orderedPositiveFiniteJumpHistoryReplicasOrFallback
    [Nonempty State] (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    OrderedPositiveFiniteJumpHistoryReplicas State successorIndex duration :=
  fun replica => orderedFiniteJumpHistoryOrFallback duration (histories replica)

omit [Fintype State] [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The coordinatewise ordered-or-fallback replica totalization is measurable. -/
theorem measurable_orderedPositiveFiniteJumpHistoryReplicasOrFallback
    [Nonempty State] (successorIndex : ℕ) (duration : ℝ) :
    Measurable (orderedPositiveFiniteJumpHistoryReplicasOrFallback
      (State := State) successorIndex duration) := by
  rw [measurable_pi_iff]
  intro replica
  exact (measurable_orderedFiniteJumpHistoryOrFallback
    (State := State) duration).comp (measurable_pi_apply replica)

/-- Total full-slice empirical density--directional-flow observation.  It agrees with the exact
ordered construction on physical support and uses one fixed measurable fallback elsewhere. -/
noncomputable def empiricalDensityDirectionalFlowTotalHybridBVObservation
    [Nonempty State] (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex) :
    FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration :=
  orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation successorIndex duration
    (orderedPositiveFiniteJumpHistoryReplicasOrFallback successorIndex duration histories)

/-- The total full-slice hybrid-BV observation is Borel measurable. -/
theorem measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
    [Nonempty State] (successorIndex : ℕ) (duration : ℝ) :
    Measurable (empiricalDensityDirectionalFlowTotalHybridBVObservation
      (State := State) successorIndex duration) :=
  (measurable_orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation
    (State := State) successorIndex duration).comp
      (measurable_orderedPositiveFiniteJumpHistoryReplicasOrFallback
        successorIndex duration)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- On a physically ordered replica family, totalization is exactly the ordered observation;
the fallback is absent and no data are changed. -/
theorem empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
    [Nonempty State] (successorIndex : ℕ) (duration : ℝ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories =
      orderedEmpiricalDensityDirectionalFlowExplicitHybridBVObservation successorIndex duration
        (fun replica => ⟨histories replica, hOrdered replica⟩) := by
  unfold empiricalDensityDirectionalFlowTotalHybridBVObservation
    orderedPositiveFiniteJumpHistoryReplicasOrFallback
  congr 1
  funext replica
  apply Subtype.ext
  simp [orderedFiniteJumpHistoryOrFallback, hOrdered replica]

end Topological

end PositiveFiniteJumpHistoryReplicas

end

end FiniteMarkovProcesses.Probability
