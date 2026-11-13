/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowObservation
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCountMoment

/-!
# Transition-test moments for bounded time-dependent Markov jump histories

This module defines the sum of a measurable time-dependent transition test over the genuine jumps
of one finite history.  A uniform pointwise test bound controls the observable by jump count and,
under the normalized bounded time-dependent physical source, yields a finite second moment and an
explicit source-uniform variance bound.

## Main declarations

- `finiteJumpHistoryTransitionTestSum`.
- `finiteStateTransitionAtOrBeforeTest`.
- `abs_finiteJumpHistoryTransitionTestSum_le`.
- `memLp_two_finiteJumpHistoryTransitionTestSum`.
- `variance_finiteJumpHistoryTransitionTestSum_le`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Sum of one time-dependent transition test over every genuine jump in a finite history. -/
noncomputable def finiteJumpHistoryTransitionTestSum
    (test : ℝ → State → State → ℝ) (history : FiniteJumpHistory State) : ℝ :=
  ∑ index : Fin history.jumpCount,
    test (history.jumpTimes index)
      (history.states index.castSucc) (history.states index.succ)

/-- Unit test selecting one ordered transition at or before a specified physical time. -/
def finiteStateTransitionAtOrBeforeTest
    (time : ℝ) (source target : State) (eventTime : ℝ)
    (eventSource eventTarget : State) : ℝ :=
  if eventTime ≤ time ∧ eventSource = source ∧ eventTarget = target then 1 else 0

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The fixed-time transition selector is measurable in event time for every state pair. -/
theorem measurable_finiteStateTransitionAtOrBeforeTest
    (time : ℝ) (source target eventSource eventTarget : State) :
    Measurable fun eventTime ↦
      finiteStateTransitionAtOrBeforeTest
        time source target eventTime eventSource eventTarget := by
  by_cases hStates : eventSource = source ∧ eventTarget = target
  · simp only [finiteStateTransitionAtOrBeforeTest, hStates, and_true]
    have hTime : MeasurableSet {eventTime : ℝ | eventTime ≤ time} :=
      measurableSet_Iic
    exact Measurable.ite hTime measurable_const measurable_const
  · simp only [finiteStateTransitionAtOrBeforeTest, hStates, and_false]
    exact measurable_const

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The fixed-time transition selector is pointwise bounded by one in absolute value. -/
theorem abs_finiteStateTransitionAtOrBeforeTest_le_one
    (time : ℝ) (source target eventSource eventTarget : State) (eventTime : ℝ) :
    |finiteStateTransitionAtOrBeforeTest
      time source target eventTime eventSource eventTarget| ≤ 1 := by
  unfold finiteStateTransitionAtOrBeforeTest
  split <;> simp

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Summing the selector over genuine jumps is exactly the existing cumulative directed count. -/
theorem finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq
    (time : ℝ) (source target : State) (history : FiniteJumpHistory State) :
    finiteJumpHistoryTransitionTestSum
        (finiteStateTransitionAtOrBeforeTest time source target) history =
      history.directedTransitionCountAtTime time source target := by
  unfold finiteJumpHistoryTransitionTestSum finiteStateTransitionAtOrBeforeTest
    FiniteJumpHistory.directedTransitionCountAtTime
    FiniteJumpHistory.directedTransitionCountAtTimeVector
  norm_cast

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Self-event deletion preserves every time-dependent transition test that vanishes on the
diagonal. -/
theorem finiteJumpHistoryTransitionTestSum_deleteSelfEvents
    (test : ℝ → State → State → ℝ)
    (hSelf : ∀ time state, test time state state = 0)
    (history : FiniteJumpHistory State) :
    finiteJumpHistoryTransitionTestSum test history.deleteSelfEvents =
      finiteJumpHistoryTransitionTestSum test history := by
  unfold finiteJumpHistoryTransitionTestSum
  exact FiniteJumpHistory.sum_timeTransitionReward_deleteSelfEvents history test hSelf

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- For distinct states, self-event deletion preserves the cumulative directed count at every
fixed time. -/
theorem directedTransitionCountAtTime_deleteSelfEvents
    (time : ℝ) {source target : State} (hNe : source ≠ target)
    (history : FiniteJumpHistory State) :
    history.deleteSelfEvents.directedTransitionCountAtTime time source target =
      history.directedTransitionCountAtTime time source target := by
  have hSelf : ∀ eventTime state,
      finiteStateTransitionAtOrBeforeTest
        time source target eventTime state state = 0 := by
    intro eventTime state
    unfold finiteStateTransitionAtOrBeforeTest
    split
    · rename_i hSelected
      exact (hNe (hSelected.2.1.symm.trans hSelected.2.2)).elim
    · rfl
  have hPreserved := finiteJumpHistoryTransitionTestSum_deleteSelfEvents
    (finiteStateTransitionAtOrBeforeTest time source target) hSelf history
  rw [finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq,
    finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq] at hPreserved
  exact_mod_cast hPreserved

omit [DecidableEq State] in
/-- Coordinatewise measurable transition tests give a measurable complete-history sum. -/
theorem measurable_finiteJumpHistoryTransitionTestSum
    (test : ℝ → State → State → ℝ)
    (hTest : ∀ source target, Measurable fun time ↦ test time source target) :
    Measurable (finiteJumpHistoryTransitionTestSum test :
      FiniteJumpHistory State → ℝ) := by
  rw [measurable_sigma_iff]
  intro eventCount
  change Measurable fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) ↦
    ∑ index : Fin eventCount,
      test (data.2 index) (data.1 index.castSucc) (data.1 index.succ)
  apply Finset.measurable_sum
  intro index _hIndex
  let statePair :
      ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) → State × State :=
    fun data ↦ (data.1 index.castSucc, data.1 index.succ)
  have hStatePair : Measurable statePair :=
    ((measurable_pi_apply index.castSucc).comp measurable_fst).prodMk
      ((measurable_pi_apply index.succ).comp measurable_fst)
  have hTime : Measurable fun data :
      (Fin (eventCount + 1) → State) × (Fin eventCount → ℝ) ↦ data.2 index :=
    (measurable_pi_apply index).comp measurable_snd
  have hPiecewise : Measurable fun pair : (State × State) × ℝ ↦
      test pair.2 pair.1.1 pair.1.2 := by
    apply measurable_from_prod_countable_right
    intro pair
    simpa only using hTest pair.1 pair.2
  exact hPiecewise.comp (hStatePair.prodMk hTime)

/-- Every fixed-time directed transition count is measurable as a real-valued history
observable. -/
theorem measurable_real_directedTransitionCountAtTime
    (time : ℝ) (source target : State) :
    Measurable fun history : FiniteJumpHistory State ↦
      (history.directedTransitionCountAtTime time source target : ℝ) := by
  have hMeasured := measurable_finiteJumpHistoryTransitionTestSum
    (finiteStateTransitionAtOrBeforeTest time source target)
    (fun eventSource eventTarget ↦
      measurable_finiteStateTransitionAtOrBeforeTest
        time source target eventSource eventTarget)
  have hFunction :
      finiteJumpHistoryTransitionTestSum
          (finiteStateTransitionAtOrBeforeTest time source target) =
        fun history : FiniteJumpHistory State ↦
          (history.directedTransitionCountAtTime time source target : ℝ) := by
    funext history
    exact finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq
      time source target history
  rw [hFunction] at hMeasured
  exact hMeasured

omit [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State] in
/-- A uniformly bounded transition test is controlled pathwise by its bound times jump count. -/
theorem abs_finiteJumpHistoryTransitionTestSum_le
    (test : ℝ → State → State → ℝ) {testBound : ℝ}
    (hTestBound : ∀ time source target, |test time source target| ≤ testBound)
    (history : FiniteJumpHistory State) :
    |finiteJumpHistoryTransitionTestSum test history| ≤
      testBound * history.jumpCount := by
  calc
    |finiteJumpHistoryTransitionTestSum test history| ≤
        ∑ index : Fin history.jumpCount,
          |test (history.jumpTimes index)
            (history.states index.castSucc) (history.states index.succ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index : Fin history.jumpCount, testBound := by
      exact Finset.sum_le_sum fun index _ ↦ hTestBound _ _ _
    _ = testBound * history.jumpCount := by simp [mul_comm]

/-- A uniformly bounded transition-test sum has a finite second moment under every normalized
bounded time-dependent physical history source. -/
theorem memLp_two_finiteJumpHistoryTransitionTestSum
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (test : ℝ → State → State → ℝ)
    (hTest : ∀ source target, Measurable fun time ↦ test time source target)
    {testBound : ℝ} (hTestBoundNonnegative : 0 ≤ testBound)
    (hTestBound : ∀ time source target, |test time source target| ≤ testBound) :
    MemLp (finiteJumpHistoryTransitionTestSum test : FiniteJumpHistory State → ℝ) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) := by
  have hCount := memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates duration
  have hDominating : MemLp
      (fun history : FiniteJumpHistory State ↦
        testBound * (history.jumpCount : ℝ)) 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) :=
    hCount.const_mul testBound
  apply hDominating.mono
  · exact (measurable_finiteJumpHistoryTransitionTestSum test hTest).aestronglyMeasurable
  · filter_upwards [] with history
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hTestBoundNonnegative (Nat.cast_nonneg _))]
    exact abs_finiteJumpHistoryTransitionTestSum_le test hTestBound history

/-- The variance of a bounded transition-test sum has an explicit bound inherited from the
common-clock Poisson second moment. -/
theorem variance_finiteJumpHistoryTransitionTestSum_le
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (test : ℝ → State → State → ℝ)
    (hTest : ∀ source target, Measurable fun time ↦ test time source target)
    {testBound : ℝ} (hTestBoundNonnegative : 0 ≤ testBound)
    (hTestBound : ∀ time source target, |test time source target| ≤ testBound) :
    variance (finiteJumpHistoryTransitionTestSum test : FiniteJumpHistory State → ℝ)
        (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      testBound ^ 2 *
        (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1))) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hObservable := memLp_two_finiteJumpHistoryTransitionTestSum
    initial rates duration test hTest hTestBoundNonnegative hTestBound
  have hDominating : Integrable
      (fun history : FiniteJumpHistory State ↦
        (testBound * (history.jumpCount : ℝ)) ^ 2) law :=
    ((memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates duration).const_mul testBound).integrable_sq
  calc
    variance (finiteJumpHistoryTransitionTestSum test : FiniteJumpHistory State → ℝ)
        law ≤
      ∫ history : FiniteJumpHistory State,
        (finiteJumpHistoryTransitionTestSum test history) ^ 2 ∂law :=
      variance_le_expectation_sq hObservable.aestronglyMeasurable
    _ ≤ ∫ history : FiniteJumpHistory State,
        (testBound * (history.jumpCount : ℝ)) ^ 2 ∂law := by
      apply integral_mono hObservable.integrable_sq hDominating
      intro history
      have hAbs := abs_finiteJumpHistoryTransitionTestSum_le test hTestBound history
      have hRightNonnegative :
          0 ≤ testBound * (history.jumpCount : ℝ) :=
        mul_nonneg hTestBoundNonnegative (Nat.cast_nonneg _)
      have hObservableUpper :
          finiteJumpHistoryTransitionTestSum test history ≤
            testBound * (history.jumpCount : ℝ) :=
        (le_abs_self _).trans hAbs
      have hObservableLower :
          -(testBound * (history.jumpCount : ℝ)) ≤
            finiteJumpHistoryTransitionTestSum test history :=
        (neg_le_of_abs_le hAbs)
      change
        (finiteJumpHistoryTransitionTestSum test history) ^ 2 ≤
          (testBound * (history.jumpCount : ℝ)) ^ 2
      nlinarith
    _ = testBound ^ 2 *
        (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2 ∂law) := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
    _ ≤ testBound ^ 2 *
        (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1))) := by
      apply mul_le_mul_of_nonneg_left
      · exact integral_sq_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le
          initial rates duration
      · exact sq_nonneg testBound

end

end FiniteMarkovProcesses.Probability
