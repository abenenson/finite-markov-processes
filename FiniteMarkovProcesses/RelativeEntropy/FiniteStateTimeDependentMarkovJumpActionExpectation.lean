/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateTimeDependentMarkovJumpAction
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateJumpDirectionalFlowLDPBoundary
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDirectionalFlowExpectation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovOccupationExpectation

/-!
# Expected action of bounded time-dependent Markov jump laws

The complete common-initial log action separates into bounded time-labelled jump log ratios and
the difference of two integrated escape sectors.  The normalized reduced source evaluates these
sectors exactly through its ordered-flow compensator and physical occupation mean.

The expectation identities retain the common initial law and directed-support hypotheses.
Large-deviation lower bounds are established separately.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Time-labelled candidate-to-reference jump log ratio on one directed state pair. -/
noncomputable def finiteStateTimeDependentMarkovJumpLogRatioWeight
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (source target : State) (time : ℝ) : ℝ :=
  Real.log
    ((rates.rate time source target : ℝ) /
      (referenceRates.rate time source target : ℝ))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every bounded measurable pair of rate rows gives a measurable jump log-ratio weight. -/
theorem measurable_finiteStateTimeDependentMarkovJumpLogRatioWeight
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (source target : State) :
    Measurable
      (finiteStateTimeDependentMarkovJumpLogRatioWeight
        rates referenceRates source target) := by
  unfold finiteStateTimeDependentMarkovJumpLogRatioWeight
  exact (((rates.measurable_rate source target).coe_nnreal_real.div
    (referenceRates.measurable_rate source target).coe_nnreal_real).log)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Summing edge-selected weights over the finite ordered off-diagonal family recovers the
complete time-labelled transition-word sum whenever every recorded transition changes state. -/
theorem sum_finiteJumpHistoryDirectedTransitionWeightSum_eq_transitionWordSum
    (weight : State → State → ℝ → ℝ) (history : FiniteJumpHistory State)
    (hNoSelf : ∀ index : Fin history.jumpCount,
      history.states index.castSucc ≠ history.states index.succ) :
    (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      finiteJumpHistoryDirectedTransitionWeightSum
        (weight transition.1.1 transition.1.2)
        transition.1.1 transition.1.2 history) =
      ∑ index : Fin history.jumpCount,
        weight (history.states index.castSucc) (history.states index.succ)
          (history.jumpTimes index) := by
  unfold finiteJumpHistoryDirectedTransitionWeightSum
    finiteJumpHistoryTransitionTestSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _hIndex
  let selected : FiniteStateOrderedOffDiagonalTransition State :=
    ⟨(history.states index.castSucc, history.states index.succ), hNoSelf index⟩
  rw [Finset.sum_eq_single selected]
  · simp [finiteStateDirectedTransitionWeightTest, selected]
  · intro transition _hTransition hTransitionNe
    simp only [finiteStateDirectedTransitionWeightTest]
    split_ifs with hMatch
    · exfalso
      apply hTransitionNe
      apply Subtype.ext
      exact Prod.ext hMatch.1.symm hMatch.2.symm
    · rfl
  · simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a state-changing history, the common-initial complete action is exactly the finite sum of
ordered-edge jump log ratios plus reference escape minus candidate escape. -/
theorem finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq_jump_add_escape
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (history : FiniteJumpHistory State)
    (hNoSelf : ∀ index : Fin history.jumpCount,
      history.states index.castSucc ≠ history.states index.succ) :
    finiteStateTimeDependentMarkovJumpLogAction
        initial initial rates referenceRates duration history =
      (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        finiteJumpHistoryDirectedTransitionWeightSum
          (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
            transition.1.1 transition.1.2)
          transition.1.1 transition.1.2 history) +
        (finiteStateTimeDependentMarkovIntegratedEscape
            referenceRates duration history.states history.jumpTimes -
          finiteStateTimeDependentMarkovIntegratedEscape
            rates duration history.states history.jumpTimes) := by
  rcases history with ⟨eventCount, states, times⟩
  change finiteStateTimeDependentMarkovJumpSliceLogAction
      initial initial rates referenceRates duration states times = _
  unfold finiteStateTimeDependentMarkovJumpSliceLogAction
  have hInitial :
      Real.log ((initial (states 0)).toReal / (initial (states 0)).toReal) = 0 := by
    by_cases hZero : (initial (states 0)).toReal = 0
    · simp [hZero]
    · rw [div_self hZero, Real.log_one]
  rw [hInitial, zero_add]
  congr 1
  symm
  exact sum_finiteJumpHistoryDirectedTransitionWeightSum_eq_transitionWordSum
    (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates)
    ⟨eventCount, states, times⟩ hNoSelf

/-- Exact mean of the complete common-initial jump action, with its finite jump and
two occupation-weighted escape sectors still separately visible. -/
noncomputable def finiteStateTimeDependentMarkovExpectedJumpLogAction
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) : ℝ :=
  (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    finiteStateTimeDependentMarkovDirectedTransitionWeightMean
      initial rates duration
      (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
        transition.1.1 transition.1.2)
      transition.1.1 transition.1.2) +
    (∫ time,
      ∑ state,
        finiteStateTimeDependentMarkovMeanDensityAt initial rates duration time state *
          (referenceRates.escapeRate time state : ℝ)
      ∂finiteOpenIntervalVolume (duration : ℝ)) -
    (∫ time,
      ∑ state,
        finiteStateTimeDependentMarkovMeanDensityAt initial rates duration time state *
          (rates.escapeRate time state : ℝ)
      ∂finiteOpenIntervalVolume (duration : ℝ))

/-- Under a uniform absolute bound on every off-diagonal jump log ratio, the expected complete
common-initial action is exactly its jump-plus-escape mean. -/
theorem integral_finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq_expected
    (initial : PMF State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) {jumpLogAbsoluteBound : ℝ}
    (hJumpLogAbsoluteBoundNonnegative : 0 ≤ jumpLogAbsoluteBound)
    (hJumpLogAbsoluteBound : ∀ time source target,
      source ≠ target →
      |finiteStateTimeDependentMarkovJumpLogRatioWeight
        rates referenceRates source target time| ≤ jumpLogAbsoluteBound) :
    (∫ history : FiniteJumpHistory State,
        finiteStateTimeDependentMarkovJumpLogAction
          initial initial rates referenceRates duration history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
      finiteStateTimeDependentMarkovExpectedJumpLogAction
        initial rates referenceRates duration := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates duration
  let jumpSector : FiniteJumpHistory State → ℝ := fun history ↦
    ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
      finiteJumpHistoryDirectedTransitionWeightSum
        (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
          transition.1.1 transition.1.2)
        transition.1.1 transition.1.2 history
  let referenceEscape : FiniteJumpHistory State → ℝ := fun history ↦
    finiteStateTimeDependentMarkovIntegratedEscape referenceRates duration
      history.states history.jumpTimes
  let candidateEscape : FiniteJumpHistory State → ℝ := fun history ↦
    finiteStateTimeDependentMarkovIntegratedEscape rates duration
      history.states history.jumpTimes
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates duration⟩
  have hPositive : ∀ᵐ history ∂law,
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history := by
    have hDensityPositive :=
      ae_finiteStateTimeDependentMarkovJumpDensityPositiveAt initial rates duration
    change ∀ᵐ history ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration,
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history
    rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
      initial rates duration]
    simpa only [NNReal.coe_mk] using hDensityPositive
  have hNoSelf : ∀ᵐ history ∂law, ∀ index : Fin history.jumpCount,
      history.states index.castSucc ≠ history.states index.succ := by
    filter_upwards [hPositive] with history hHistoryPositive
    intro index hState
    have hRatePositive := hHistoryPositive.2 index
    rw [hState, rates.rate_self] at hRatePositive
    norm_num at hRatePositive
  have hEdgeIntegrable
      (transition : FiniteStateOrderedOffDiagonalTransition State) : Integrable
      (finiteJumpHistoryDirectedTransitionWeightSum
        (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
          transition.1.1 transition.1.2)
        transition.1.1 transition.1.2)
      law := by
    exact (memLp_two_finiteJumpHistoryTransitionTestSum
      initial rates duration
      (finiteStateDirectedTransitionWeightTest
        (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
          transition.1.1 transition.1.2)
        transition.1.1 transition.1.2)
      (fun eventSource eventTarget ↦
        measurable_finiteStateDirectedTransitionWeightTest
          (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
            transition.1.1 transition.1.2)
          (measurable_finiteStateTimeDependentMarkovJumpLogRatioWeight
            rates referenceRates transition.1.1 transition.1.2)
          transition.1.1 transition.1.2 eventSource eventTarget)
      hJumpLogAbsoluteBoundNonnegative
      (fun time eventSource eventTarget ↦ by
        unfold finiteStateDirectedTransitionWeightTest
        split
        · exact hJumpLogAbsoluteBound time transition.1.1 transition.1.2 transition.2
        · simpa only [abs_zero] using hJumpLogAbsoluteBoundNonnegative)).integrable
          one_le_two
  have hJumpSectorIntegrable : Integrable jumpSector law :=
    integrable_finsetSum Finset.univ fun transition _hTransition ↦
      hEdgeIntegrable transition
  have hReferenceEscapeIntegrable : Integrable referenceEscape law :=
    integrable_finiteStateTimeDependentMarkovIntegratedEscape
      initial rates referenceRates duration
  have hCandidateEscapeIntegrable : Integrable candidateEscape law :=
    integrable_finiteStateTimeDependentMarkovIntegratedEscape
      initial rates rates duration
  calc
    (∫ history : FiniteJumpHistory State,
        finiteStateTimeDependentMarkovJumpLogAction
          initial initial rates referenceRates duration history ∂law) =
      ∫ history, jumpSector history +
        (referenceEscape history - candidateEscape history) ∂law := by
          apply integral_congr_ae
          filter_upwards [hNoSelf] with history hHistoryNoSelf
          exact finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq_jump_add_escape
            initial rates referenceRates duration history hHistoryNoSelf
    _ = (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ∫ history,
            finiteJumpHistoryDirectedTransitionWeightSum
              (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
                transition.1.1 transition.1.2)
              transition.1.1 transition.1.2 history ∂law) +
        (∫ history, referenceEscape history ∂law) -
        (∫ history, candidateEscape history ∂law) := by
          have hEscapeIntegral :
              (∫ history, (referenceEscape - candidateEscape) history ∂law) =
                (∫ history, referenceEscape history ∂law) -
                  (∫ history, candidateEscape history ∂law) := by
            exact integral_sub hReferenceEscapeIntegrable hCandidateEscapeIntegrable
          change (∫ history, jumpSector history +
            (referenceEscape - candidateEscape) history ∂law) = _
          rw [integral_add hJumpSectorIntegrable
            (hReferenceEscapeIntegrable.sub hCandidateEscapeIntegrable),
            hEscapeIntegral,
            integral_finsetSum Finset.univ fun transition _hTransition ↦
              hEdgeIntegrable transition]
          ring
    _ = finiteStateTimeDependentMarkovExpectedJumpLogAction
        initial rates referenceRates duration := by
          rw [integral_finiteStateTimeDependentMarkovIntegratedEscape_eq_occupationMean
            initial rates referenceRates duration,
            integral_finiteStateTimeDependentMarkovIntegratedEscape_eq_occupationMean
              initial rates rates duration]
          unfold finiteStateTimeDependentMarkovExpectedJumpLogAction
          congr 2
          apply Finset.sum_congr rfl
          intro transition _hTransition
          exact integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
            initial rates duration transition.2
            (finiteStateTimeDependentMarkovJumpLogRatioWeight rates referenceRates
              transition.1.1 transition.1.2)
            (measurable_finiteStateTimeDependentMarkovJumpLogRatioWeight
              rates referenceRates transition.1.1 transition.1.2)
            hJumpLogAbsoluteBoundNonnegative
            (fun time ↦ hJumpLogAbsoluteBound time
              transition.1.1 transition.1.2 transition.2)

end

end FiniteMarkovProcesses.InformationTheory
