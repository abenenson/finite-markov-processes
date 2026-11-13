/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovOrderedSupport
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovInitialStateMarginal
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovStateObservationMoment
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovTransitionTestMoment

/-!
# Mean continuity for bounded time-dependent Markov jump laws

This module defines the exact expected initial density, time-dependent density, and cumulative
ordered flow of the normalized reduced time-dependent source.  Integrating the microscopic
continuity identity on its proved almost-sure ordered support yields the exact mean continuity
equation.  The result is kinematic; it does not yet identify cumulative-flow
means with integrated rate intensities or solve the forward equation.

## Main results

- `finiteStateTimeDependentMarkovMeanInitialDensity`.
- `finiteStateTimeDependentMarkovMeanDensityAt`.
- `finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt`.
- `finiteStateTimeDependentMarkovVirtualMeanCumulativeDirectionalFlowAt`.
- `finiteStateTimeDependentMarkovMeanInitialDensity_eq`.
- `finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_virtual`.
- `finiteStateTimeDependentMarkovMeanDensityAt_eq_initial_add_incoming_sub_outgoing`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Expected initial-state membership under the normalized reduced time-dependent source. -/
noncomputable def finiteStateTimeDependentMarkovMeanInitialDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (observed : State) : ℝ :=
  ∫ history : FiniteJumpHistory State,
    FiniteJumpHistory.stateMembershipIndicator history.initialState observed
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration

/-- Expected occupied-state membership at one physical time. -/
noncomputable def finiteStateTimeDependentMarkovMeanDensityAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (observed : State) : ℝ :=
  ∫ history : FiniteJumpHistory State,
    finiteJumpHistoryStateMembershipAtTime time observed history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration

/-- The expected density is measurable as a function of physical observation
time. -/
theorem measurable_finiteStateTimeDependentMarkovMeanDensityAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (observed : State) :
    Measurable fun time : ℝ ↦
      finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time observed := by
  unfold finiteStateTimeDependentMarkovMeanDensityAt
  let law :=
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  change Measurable fun time : ℝ ↦
    ∫ history : FiniteJumpHistory State,
      finiteJumpHistoryStateMembershipAtTime time observed history ∂law
  exact
    (measurable_finiteJumpHistoryStateMembershipAtTime_uncurry
      observed).stronglyMeasurable.integral_prod_left'.measurable

/-- Every expected density coordinate lies in the closed unit interval. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (observed : State) :
    finiteStateTimeDependentMarkovMeanDensityAt
      initial rates duration time observed ∈ Set.Icc (0 : ℝ) 1 := by
  let law :=
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  have hIntegrable : Integrable
      (finiteJumpHistoryStateMembershipAtTime time observed :
        FiniteJumpHistory State → ℝ) law :=
    (memLp_two_finiteJumpHistoryStateMembershipAtTime
      initial rates duration time observed).integrable one_le_two
  constructor
  · unfold finiteStateTimeDependentMarkovMeanDensityAt
    exact integral_nonneg fun history ↦
      (finiteJumpHistoryStateMembershipAtTime_mem_Icc
        time observed history).1
  · unfold finiteStateTimeDependentMarkovMeanDensityAt
    calc
      (∫ history : FiniteJumpHistory State,
          finiteJumpHistoryStateMembershipAtTime time observed history ∂law) ≤
          ∫ _history : FiniteJumpHistory State, (1 : ℝ) ∂law := by
        apply integral_mono hIntegrable (integrable_const 1)
        intro history
        exact (finiteJumpHistoryStateMembershipAtTime_mem_Icc
          time observed history).2
      _ = 1 := by simp

/-- Expected cumulative number of one ordered transition at or before one physical time. -/
noncomputable def finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (source target : State) : ℝ :=
  ∫ history : FiniteJumpHistory State,
    (history.directedTransitionCountAtTime time source target : ℝ)
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration

/-- The expected cumulative one-way flow is measurable in physical observation
time. -/
theorem measurable_finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (source target : State) :
    Measurable fun time : ℝ ↦
      finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration time source target := by
  unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
  let law :=
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  change Measurable fun time : ℝ ↦
    ∫ history : FiniteJumpHistory State,
      (history.directedTransitionCountAtTime time source target : ℝ) ∂law
  exact
    (((measurable_of_countable fun count : ℕ ↦ (count : ℝ)).comp
      (FiniteJumpHistory.measurable_directedTransitionCountAtTime_uncurry
        source target)).stronglyMeasurable.integral_prod_left').measurable

/-- Expected cumulative directed virtual-event count under the normalized common-clock law. -/
noncomputable def finiteStateTimeDependentMarkovVirtualMeanCumulativeDirectionalFlowAt
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (source target : State) : ℝ :=
  ∫ history : FiniteJumpHistory State,
    (history.directedTransitionCountAtTime time source target : ℝ)
      ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration

/-- Every off-diagonal expected physical flow can be computed on the simpler normalized virtual
common-clock law. -/
theorem finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_virtual
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) {source target : State} (hNe : source ≠ target) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration time source target =
      finiteStateTimeDependentMarkovVirtualMeanCumulativeDirectionalFlowAt
        initial rates duration time source target := by
  unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    finiteStateTimeDependentMarkovVirtualMeanCumulativeDirectionalFlowAt
    finiteStateTimeDependentMarkovReducedHistoryMeasure
  rw [integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
    (measurable_real_directedTransitionCountAtTime
      time source target).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with history
  exact_mod_cast directedTransitionCountAtTime_deleteSelfEvents
    time hNe history

/-- The expected initial density is exactly the supplied PMF coordinate. -/
theorem finiteStateTimeDependentMarkovMeanInitialDensity_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (observed : State) :
    finiteStateTimeDependentMarkovMeanInitialDensity
        initial rates duration observed =
      (initial observed).toReal := by
  unfold finiteStateTimeDependentMarkovMeanInitialDensity
  have hFunction :
      (fun history : FiniteJumpHistory State ↦
        FiniteJumpHistory.stateMembershipIndicator history.initialState observed) =
      (FiniteJumpHistory.initialState ⁻¹' {observed}).indicator
        (1 : FiniteJumpHistory State → ℝ) := by
    funext history
    unfold FiniteJumpHistory.stateMembershipIndicator Set.indicator
    by_cases hState : history.initialState = observed
    · simp only [hState, Set.mem_preimage, Set.mem_singleton_iff, ite_true,
        Pi.one_apply]
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, hState, ite_false,
        Pi.one_apply]
  rw [hFunction]
  rw [integral_indicator_one
    (FiniteJumpHistory.measurable_initialState
      (measurableSet_singleton observed))]
  unfold Measure.real
  rw [← Measure.map_apply FiniteJumpHistory.measurable_initialState
    (measurableSet_singleton observed)]
  rw [map_initialState_finiteStateTimeDependentMarkovReducedHistoryMeasure]
  rw [PMF.toMeasure_apply_singleton initial observed
    (measurableSet_singleton observed)]

/-- Initial-state membership has a finite second moment. -/
theorem memLp_two_finiteJumpHistoryInitialStateMembership
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (observed : State) :
    MemLp (fun history : FiniteJumpHistory State ↦
      FiniteJumpHistory.stateMembershipIndicator history.initialState observed) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  exact MemLp.of_bound
    ((FiniteJumpHistory.measurable_stateMembershipIndicator observed).comp
      FiniteJumpHistory.measurable_initialState).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun history ↦ by
      unfold FiniteJumpHistory.stateMembershipIndicator
      split <;> simp)

/-- Every fixed-time cumulative ordered transition count has a finite second moment. -/
theorem memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (source target : State) :
    MemLp (fun history : FiniteJumpHistory State ↦
      (history.directedTransitionCountAtTime time source target : ℝ)) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  have hTest := memLp_two_finiteJumpHistoryTransitionTestSum
    initial rates duration (finiteStateTransitionAtOrBeforeTest time source target)
    (fun eventSource eventTarget ↦
      measurable_finiteStateTransitionAtOrBeforeTest
        time source target eventSource eventTarget)
    (show (0 : ℝ) ≤ 1 by norm_num)
    (fun eventTime eventSource eventTarget ↦
      abs_finiteStateTransitionAtOrBeforeTest_le_one
        time source target eventSource eventTarget eventTime)
  have hFunction :
      finiteJumpHistoryTransitionTestSum
          (finiteStateTransitionAtOrBeforeTest time source target) =
        fun history : FiniteJumpHistory State ↦
          (history.directedTransitionCountAtTime time source target : ℝ) := by
    funext history
    exact finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq
      time source target history
  rw [hFunction] at hTest
  exact hTest

/-- Every cumulative ordered-flow mean is nonnegative and bounded by the expected
complete physical jump count. -/
theorem finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_mem_Icc_jumpCountMean
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (source target : State) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration time source target ∈
      Set.Icc 0
        (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ)
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  let law :=
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  have hFlowIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.directedTransitionCountAtTime time source target : ℝ)) law :=
    (memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
      initial rates duration time source target).integrable one_le_two
  have hCountIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ)) law :=
    (memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates duration).integrable one_le_two
  constructor
  · unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    exact integral_nonneg fun history ↦ Nat.cast_nonneg _
  · unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    apply integral_mono hFlowIntegrable hCountIntegrable
    intro history
    change
      ((history.directedTransitionCountAtTime time source target : ℕ) : ℝ) ≤
        ((history.jumpCount : ℕ) : ℝ)
    exact_mod_cast
      FiniteJumpHistory.directedTransitionCountAtTime_le_jumpCount
        history time source target

/-- The expected density and cumulative ordered flows obey exact finite-state continuity. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_eq_initial_add_incoming_sub_outgoing
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (observed : State) :
    finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time observed =
      finiteStateTimeDependentMarkovMeanInitialDensity
          initial rates duration observed +
        ∑ source : State,
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            initial rates duration time source observed -
        ∑ target : State,
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            initial rates duration time observed target := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hInitialIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦
        FiniteJumpHistory.stateMembershipIndicator history.initialState observed) law :=
    (memLp_two_finiteJumpHistoryInitialStateMembership
      initial rates duration observed).integrable one_le_two
  have hIncomingIntegrable : ∀ source : State, Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.directedTransitionCountAtTime time source observed : ℝ)) law :=
    fun source ↦
      (memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
        initial rates duration time source observed).integrable one_le_two
  have hOutgoingIntegrable : ∀ target : State, Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.directedTransitionCountAtTime time observed target : ℝ)) law :=
    fun target ↦
      (memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
        initial rates duration time observed target).integrable one_le_two
  have hIncomingSumIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦
        ∑ source : State,
          (history.directedTransitionCountAtTime time source observed : ℝ)) law :=
    integrable_finsetSum Finset.univ fun source _ ↦ hIncomingIntegrable source
  have hOutgoingSumIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦
        ∑ target : State,
          (history.directedTransitionCountAtTime time observed target : ℝ)) law :=
    integrable_finsetSum Finset.univ fun target _ ↦ hOutgoingIntegrable target
  have hInitialIncomingIntegrable : Integrable
      (fun history : FiniteJumpHistory State ↦
        FiniteJumpHistory.stateMembershipIndicator history.initialState observed +
          ∑ source : State,
            (history.directedTransitionCountAtTime time source observed : ℝ)) law :=
    hInitialIntegrable.add hIncomingSumIntegrable
  have hPathwise : ∀ᵐ history ∂law,
      finiteJumpHistoryStateMembershipAtTime time observed history =
        FiniteJumpHistory.stateMembershipIndicator history.initialState observed +
          ∑ source : State,
            (history.directedTransitionCountAtTime time source observed : ℝ) -
          ∑ target : State,
            (history.directedTransitionCountAtTime time observed target : ℝ) := by
    filter_upwards [
      ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration] with history hOrdered
    apply
      FiniteJumpHistory.stateMembershipIndicator_stateAtTime_eq_initial_add_incoming_sub_outgoing
      history duration time observed hOrdered
  have hIntegral := integral_congr_ae hPathwise
  change finiteStateTimeDependentMarkovMeanDensityAt
      initial rates duration time observed = _ at hIntegral
  rw [integral_sub hInitialIncomingIntegrable hOutgoingSumIntegrable,
    integral_add hInitialIntegrable hIncomingSumIntegrable,
    integral_finsetSum Finset.univ (fun source _ ↦ hIncomingIntegrable source),
    integral_finsetSum Finset.univ (fun target _ ↦ hOutgoingIntegrable target)] at hIntegral
  exact hIntegral

end

end FiniteMarkovProcesses.Probability
