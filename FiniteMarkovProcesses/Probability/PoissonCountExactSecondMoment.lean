/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.PoissonCountExpectation
import FiniteMarkovProcesses.Probability.PoissonCountSecondMomentBound
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanContinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Exact Poisson second moments and physical jump-count bounds

The existing Poisson mass recursion gives the exact second moment at every nonnegative
intensity, including zero. The original common-clock count map and self-event deletion then
bound the physical count and fixed-time directional-flow variance for every initial PMF.
Joint history/time second-moment integrability retains the complete unbounded history carrier.

## Main results

- `integral_sq_poissonCount_eq`: the exact second moment is intensity squared plus intensity.
- The original physical jump-count second moment obeys the exact Poisson upper bound.
- `variance_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_le_poissonSecondMoment`.
- `memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_uncurry`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The mass-weighted count-square series sums to intensity squared plus intensity, including
at intensity zero. -/
theorem hasSum_sq_count_mul_poissonCountMassReal (intensity : ℝ≥0) :
    HasSum (fun count : ℕ ↦ (count : ℝ) ^ 2 * poissonCountMassReal intensity count)
      ((intensity : ℝ) ^ 2 + intensity) := by
  have hShifted : HasSum
      (fun count : ℕ ↦ ((count + 1 : ℕ) : ℝ) ^ 2 *
        poissonCountMassReal intensity (count + 1))
      ((intensity : ℝ) ^ 2 + intensity) := by
    convert ((hasSum_count_mul_poissonPMFReal intensity).add
      (hasSum_poissonCountMassReal intensity)).mul_left (intensity : ℝ) using 1
    · funext count
      have hRecursion := succ_mul_poissonPMFReal intensity count
      push_cast at hRecursion ⊢
      nlinarith
    · ring
  apply (hasSum_nat_add_iff' 1).mp
  convert hShifted using 1
  simp

/-- The second moment of the original Poisson count law is intensity squared plus intensity.
No positive-intensity assumption or division by intensity is required. -/
theorem integral_sq_poissonCount_eq (intensity : ℝ≥0) :
    (∫ count : ℕ, (count : ℝ) ^ 2 ∂poissonMeasure intensity) =
      (intensity : ℝ) ^ 2 + intensity := by
  rw [ProbabilityTheory.integral_poissonMeasure' (integrable_sq_poissonCount intensity)]
  simpa only [poissonCountMassReal, smul_eq_mul, mul_comm] using
    (hasSum_sq_count_mul_poissonCountMassReal intensity).tsum_eq

/-- The zero-intensity Poisson count has exactly zero second moment. -/
@[simp]
theorem integral_sq_poissonCount_zero :
    (∫ count : ℕ, (count : ℝ) ^ 2 ∂poissonMeasure 0) = 0 := by
  simp [integral_sq_poissonCount_eq]

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The complete physical jump-count second moment is bounded by the exact second moment of
the original virtual common clock, uniformly over the initial PMF and bounded rate profile. -/
theorem
    integral_sq_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le_poissonSecondMoment
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      (((rates.uniformizationRate * duration : NNReal) : ℝ) ^ 2 +
        ((rates.uniformizationRate * duration : NNReal) : ℝ)) := by
  let virtualLaw :=
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration
  have hVirtual : Integrable
      (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ) ^ 2) virtualLaw :=
    (memLp_two_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration).integrable_sq
  have hDeleted : Integrable
      (fun history : FiniteJumpHistory State ↦
        (history.deleteSelfEvents.jumpCount : ℝ) ^ 2) virtualLaw := by
    have hReduced :=
      (memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration).integrable_sq
    rw [finiteStateTimeDependentMarkovReducedHistoryMeasure] at hReduced
    exact (integrable_map_measure hReduced.aestronglyMeasurable
      FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable).mp hReduced
  calc
    (∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) =
        ∫ history : FiniteJumpHistory State,
          (history.deleteSelfEvents.jumpCount : ℝ) ^ 2 ∂virtualLaw := by
      unfold finiteStateTimeDependentMarkovReducedHistoryMeasure virtualLaw
      exact integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
        ((((measurable_of_countable (fun count : ℕ ↦ (count : ℝ))).comp
          FiniteJumpHistory.measurable_jumpCount).pow_const 2).aestronglyMeasurable)
    _ ≤ ∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2 ∂virtualLaw := by
      apply integral_mono hDeleted hVirtual
      intro history
      have hCount : ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) ≤
          ((history.jumpCount : ℕ) : ℝ) := by
        exact_mod_cast FiniteJumpHistory.jumpCount_deleteSelfEvents_le history
      have hDeletedNonnegative : (0 : ℝ) ≤
          ((history.deleteSelfEvents.jumpCount : ℕ) : ℝ) := Nat.cast_nonneg _
      have hOriginalNonnegative : (0 : ℝ) ≤ ((history.jumpCount : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    _ = ∫ count : ℕ, (count : ℝ) ^ 2
        ∂poissonMeasure (rates.uniformizationRate * duration) := by
      rw [← map_jumpCount_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration]
      exact (integral_map FiniteJumpHistory.measurable_jumpCount.aemeasurable
        (measurable_of_countable
          (fun count : ℕ ↦ (count : ℝ) ^ 2)).aestronglyMeasurable).symm
    _ = _ := integral_sq_poissonCount_eq (rates.uniformizationRate * duration)

/-- Every fixed-time directional count has variance at most the original virtual clock's
exact second moment. The initial PMF remains arbitrary. -/
theorem
    variance_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_le_poissonSecondMoment
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (time : ℝ) (source target : State) :
    variance (fun history : FiniteJumpHistory State ↦
        (history.directedTransitionCountAtTime time source target : ℝ))
        (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) ≤
      (((rates.uniformizationRate * duration : NNReal) : ℝ) ^ 2 +
        ((rates.uniformizationRate * duration : NNReal) : ℝ)) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hFlow := memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
    initial rates duration time source target
  have hCount := memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates duration
  have hSecond :=
    integral_sq_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure_le_poissonSecondMoment
      initial rates duration
  calc
    variance (fun history : FiniteJumpHistory State ↦
        (history.directedTransitionCountAtTime time source target : ℝ)) law ≤
      ∫ history : FiniteJumpHistory State,
        (history.directedTransitionCountAtTime time source target : ℝ) ^ 2 ∂law :=
      variance_le_expectation_sq hFlow.aestronglyMeasurable
    _ ≤ ∫ history : FiniteJumpHistory State, (history.jumpCount : ℝ) ^ 2 ∂law := by
      apply integral_mono hFlow.integrable_sq hCount.integrable_sq
      intro history
      have hLe : (history.directedTransitionCountAtTime time source target : ℝ) ≤
          (history.jumpCount : ℝ) := by
        exact_mod_cast history.directedTransitionCountAtTime_le_jumpCount time source target
      have hNonnegative : (0 : ℝ) ≤
          (history.directedTransitionCountAtTime time source target : ℝ) := Nat.cast_nonneg _
      have hCountNonnegative : (0 : ℝ) ≤ (history.jumpCount : ℝ) := Nat.cast_nonneg _
      nlinarith
    _ ≤ _ := hSecond

/-- A density indicator has a finite joint history/time second moment for every finite time
measure, without fixing the initial PMF. -/
theorem memLp_two_finiteJumpHistoryStateMembershipAtTime_uncurry
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (observed : State) (timeMeasure : Measure ℝ)
    [IsFiniteMeasure timeMeasure] :
    MemLp (fun data : FiniteJumpHistory State × ℝ ↦
      finiteJumpHistoryStateMembershipAtTime data.2 observed data.1) 2
      ((finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration).prod
        timeMeasure) := by
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  apply MemLp.of_bound
    (measurable_finiteJumpHistoryStateMembershipAtTime_uncurry observed).aestronglyMeasurable 1
  filter_upwards [] with data
  rw [Real.norm_eq_abs, abs_of_nonneg
    (finiteJumpHistoryStateMembershipAtTime_mem_Icc data.2 observed data.1).1]
  exact (finiteJumpHistoryStateMembershipAtTime_mem_Icc data.2 observed data.1).2

/-- Every directional count has a finite joint history/time second moment under the original
physical law and any finite time measure, by domination by the complete physical count. -/
theorem memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime_uncurry
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (source target : State) (timeMeasure : Measure ℝ)
    [IsFiniteMeasure timeMeasure] :
    MemLp (fun data : FiniteJumpHistory State × ℝ ↦
      (data.1.directedTransitionCountAtTime data.2 source target : ℝ)) 2
      ((finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration).prod
        timeMeasure) := by
  have hCount :=
    (memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates duration).comp_fst timeMeasure
  apply hCount.mono
  · exact (FiniteJumpHistory.measurable_real_directedTransitionCountAtTime_uncurry
      source target).aestronglyMeasurable
  · filter_upwards [] with data
    change |(data.1.directedTransitionCountAtTime data.2 source target : ℝ)| ≤
      |(data.1.jumpCount : ℝ)|
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast data.1.directedTransitionCountAtTime_le_jumpCount data.2 source target

end FiniteMarkovProcesses.Probability
