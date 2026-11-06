/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.Integral.OfRealIntegral
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedWordExpectation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovUniformization
import FiniteMarkovProcesses.Probability.OrderedJumpTimesVolume
import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Normalized virtual history law for bounded time-dependent jump rates

This module constructs the finite-horizon common-clock history law associated with a bounded
measurable time-dependent finite-state jump-rate family. The carrier retains virtual self-events.
At each fixed event-time vector, summing the state-word weights gives one; integration over the
ordered simplex and summation over event count therefore give the exact Poisson normalization.

This law is the normalization object required by time-dependent exponential-martingale arguments.
It is not yet identified with a reduced physical jump history after deletion of virtual events.

## Main results

- `sum_finiteStateTimeDependentMarkovUniformizedSliceDensity`: exact fixed-time state-word
  normalization.
- `finiteStateTimeDependentMarkovUniformizedCountMeasure_univ`: exact Poisson count mass.
- `finiteStateTimeDependentMarkovUniformizedHistoryMeasure_univ`: exact complete normalization.
- `finiteStateTimeDependentMarkovUniformizedHistoryProbabilityMeasure`: bundled probability law.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Conditional weight of a future state word evaluated at its ordered event times. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedContinuationWeight
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ)
    (source : State) (future : Fin eventCount → State) : ℝ :=
  finiteStateTimeDependentMarkovContinuationWeight
    (fun index ↦ rates.uniformizedTransitionPMF (times index)) source future

/-- Probability weight of one complete virtual state word at a fixed event-time vector. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedStateWordWeight
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ)
    (states : Fin (eventCount + 1) → State) : ℝ :=
  (initial (states 0)).toReal *
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
      rates times (states 0) (Fin.tail states)

/-- Fixed-word common-clock density for a bounded time-dependent virtual jump history. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) : ℝ :=
  (rates.uniformizationRate : ℝ) ^ eventCount *
    Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
      finiteStateTimeDependentMarkovUniformizedStateWordWeight initial rates times states

/-- Every time-dependent common-clock slice density is nonnegative. -/
theorem finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    0 ≤ finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states times := by
  unfold finiteStateTimeDependentMarkovUniformizedSliceDensity
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
    finiteStateTimeDependentMarkovContinuationWeight
  positivity

/-- The fixed-word time-dependent virtual density is measurable in its event-time vector. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) :
    Measurable (finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states) := by
  unfold finiteStateTimeDependentMarkovUniformizedSliceDensity
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
    finiteStateTimeDependentMarkovContinuationWeight
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro index _hIndex
  have hTime : Measurable (fun times : Fin eventCount → ℝ ↦ times index) :=
    measurable_pi_apply index
  simpa only [Function.comp_apply, Function.comp_def, Fin.cons_self_tail] using
    (rates.measurable_uniformizedTransitionPMF_toReal
      (states index.castSucc) (states index.succ)).comp hTime

/-- At fixed event times, the conditional future-word weights have total mass one. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedContinuationWeight
    (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (source : State) :
    ∑ future : Fin eventCount → State,
      finiteStateTimeDependentMarkovUniformizedContinuationWeight
        rates times source future = 1 := by
  unfold finiteStateTimeDependentMarkovUniformizedContinuationWeight
  exact sum_finiteStateTimeDependentMarkovContinuationWeight
    (fun index ↦ rates.uniformizedTransitionPMF (times index)) source

/-- At fixed event times, the complete virtual state-word weights have total mass one. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) :
    ∑ states : Fin (eventCount + 1) → State,
      finiteStateTimeDependentMarkovUniformizedStateWordWeight
        initial rates times states = 1 := by
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) ↦ State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ source : State, ∑ future : Fin eventCount → State,
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
      initial rates times (Fin.cons source future)) = 1
  unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [show (∑ source : State, ∑ future : Fin eventCount → State,
      (initial source).toReal *
        finiteStateTimeDependentMarkovUniformizedContinuationWeight
          rates times source future) =
    ∑ source : State, (initial source).toReal *
      ∑ future : Fin eventCount → State,
        finiteStateTimeDependentMarkovUniformizedContinuationWeight
          rates times source future by
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]]
  simp_rw [sum_finiteStateTimeDependentMarkovUniformizedContinuationWeight, mul_one]
  exact PMF.sum_toReal initial

/-- Summing over every state word leaves the common Poisson-clock density. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (times : Fin eventCount → ℝ) :
    (∑ states : Fin (eventCount + 1) → State,
      finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states times) =
      (rates.uniformizationRate : ℝ) ^ eventCount *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration)) := by
  simp_rw [finiteStateTimeDependentMarkovUniformizedSliceDensity]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [show (∑ states : Fin (eventCount + 1) → State,
      Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
        finiteStateTimeDependentMarkovUniformizedStateWordWeight
          initial rates times states) =
      Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
        ∑ states : Fin (eventCount + 1) → State,
          finiteStateTimeDependentMarkovUniformizedStateWordWeight
            initial rates times states by
    rw [Finset.mul_sum]]
  rw [sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight, mul_one]

/-- Integrating the state-summed fixed-count density gives the corresponding Poisson mass. -/
theorem integral_sum_finiteStateTimeDependentMarkovUniformizedSliceDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (eventCount : ℕ) :
    (∫ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
      ∑ states : Fin (eventCount + 1) → State,
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times) =
      poissonCountMassReal (rates.uniformizationRate * duration) eventCount := by
  simp_rw [sum_finiteStateTimeDependentMarkovUniformizedSliceDensity]
  rw [integral_const]
  rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [smul_eq_mul]
  change (volume (orderedJumpTimes eventCount duration)).toReal * _ = _
  rw [volume_orderedJumpTimes eventCount duration duration.coe_nonneg]
  rw [ENNReal.toReal_ofReal]
  · unfold poissonCountMassReal
    rw [NNReal.coe_mul]
    ring
  · exact div_nonneg (pow_nonneg duration.coe_nonneg eventCount)
      (Nat.cast_nonneg eventCount.factorial)

/-- Measure of one fixed time-dependent virtual state-word slice. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ)
    (states : Fin (eventCount + 1) → State) : Measure (FiniteJumpHistory State) :=
  Measure.map (embedJumpTimes eventCount states)
    ((volume.restrict (orderedJumpTimes eventCount duration)).withDensity
      (fun times ↦ ENNReal.ofReal
        (finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times)))

/-- Measure of every time-dependent virtual history with one fixed event count. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedCountMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun states : Fin (eventCount + 1) → State ↦
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
      initial rates duration eventCount states

/-- The full time-dependent virtual history measure, summed over every finite event count. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) : Measure (FiniteJumpHistory State) :=
  Measure.sum fun eventCount : ℕ ↦
    finiteStateTimeDependentMarkovUniformizedCountMeasure
      initial rates duration eventCount

/-- Every fixed-count virtual-history measure has exactly its Poisson count mass. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (eventCount : ℕ) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount Set.univ =
      poissonCountPMF (rates.uniformizationRate * duration) eventCount := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  simp_rw [Measure.map_apply (measurable_embedJumpTimes eventCount _)
    MeasurableSet.univ, preimage_univ]
  simp_rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← lintegral_finsetSum]
  · have hOfReal (times : Fin eventCount → ℝ) :
        (∑ states : Fin (eventCount + 1) → State,
          ENNReal.ofReal (finiteStateTimeDependentMarkovUniformizedSliceDensity
            initial rates duration states times)) =
          ENNReal.ofReal (∑ states : Fin (eventCount + 1) → State,
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro states _
        exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
          initial rates duration states times
    simp_rw [hOfReal]
    let totalDensity : (Fin eventCount → ℝ) → ℝ := fun times ↦
      ∑ states : Fin (eventCount + 1) → State,
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
    have hFunction : totalDensity = fun _ ↦
        (rates.uniformizationRate : ℝ) ^ eventCount *
          Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ))) := by
      funext times
      exact sum_finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration eventCount times
    have hIntegrable : Integrable totalDensity
        (volume.restrict (orderedJumpTimes eventCount duration)) := by
      rw [hFunction]
      exact integrable_const _
    have hNonnegative : 0 ≤ᶠ[
        ae (volume.restrict (orderedJumpTimes eventCount duration))] totalDensity := by
      apply ae_of_all
      intro times
      exact Finset.sum_nonneg fun states _ ↦
        finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
          initial rates duration states times
    rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hNonnegative]
    rw [integral_sum_finiteStateTimeDependentMarkovUniformizedSliceDensity]
    rfl
  · intro states _
    exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states).ennreal_ofReal

/-- The complete time-dependent virtual history measure is exactly normalized. -/
theorem finiteStateTimeDependentMarkovUniformizedHistoryMeasure_univ
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration Set.univ = 1 := by
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_univ]
  exact (poissonCountPMF (rates.uniformizationRate * duration)).tsum_coe

/-- Bundled normalized time-dependent virtual history law. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedHistoryProbabilityMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) : ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration,
    ⟨finiteStateTimeDependentMarkovUniformizedHistoryMeasure_univ
      initial rates duration⟩⟩

/-- Probability bundling preserves the underlying time-dependent virtual history measure. -/
@[simp]
theorem finiteStateTimeDependentMarkovUniformizedHistoryProbabilityMeasure_toMeasure
    [MeasurableSpace State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    (finiteStateTimeDependentMarkovUniformizedHistoryProbabilityMeasure
      initial rates duration).toMeasure =
      finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration :=
  rfl

end FiniteMarkovProcesses.Probability
