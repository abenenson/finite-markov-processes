/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMarkedTransitionErasure
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointCoefficient
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCutSectorResummation
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointEvolution
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Marked-transition compensator for bounded time-dependent Markov laws

This module combines marked-coordinate Tonelli disintegration with future state erasure.  One
fixed before/after virtual-event sector factors into the earlier endpoint coefficient, the marked
transition probability, and the exact later ordered-simplex volume.  Subsequent Poisson
resummation removes the later horizon.

## Main result

- `lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The complete marked-edge density is measurable in the event-time vector. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedMarkedTransitionDensity
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (earlierCount laterCount : ℕ) (source target : State) :
    Measurable fun times : Fin (earlierCount + 1 + laterCount) → ℝ ↦
      ENNReal.ofReal
        (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
          if states ⟨earlierCount, by omega⟩ = source ∧
              states ⟨earlierCount + 1, by omega⟩ = target then
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times
          else 0) := by
  apply Measurable.ennreal_ofReal
  apply Finset.measurable_sum
  intro states _hStates
  by_cases hMarked : states ⟨earlierCount, by omega⟩ = source ∧
      states ⟨earlierCount + 1, by omega⟩ = target
  · simpa only [ite_eq_left hMarked] using
      measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states
  · simp only [hMarked, ite_false]
    exact measurable_const

/-- Integrating one marked before/after count sector yields the earlier endpoint coefficient,
marked transition probability, and later ordered-simplex volume under the complete common clock. -/
theorem lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (earlierCount laterCount : ℕ) (source target : State) :
    (∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
        orderedJumpTimes (earlierCount + 1 + laterCount) duration,
      ENNReal.ofReal
        (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
          if states ⟨earlierCount, by omega⟩ = source ∧
              states ⟨earlierCount + 1, by omega⟩ = target then
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times
          else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        ENNReal.ofReal
            ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
              Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source *
          ENNReal.ofReal
            (rates.uniformizedTransitionPMF markedTime source target).toReal *
          ENNReal.ofReal
            ((duration - markedTime) ^ laterCount / laterCount.factorial) := by
  rw [lintegral_orderedJumpTimes_marked earlierCount laterCount
    (measurable_finiteStateTimeDependentMarkovUniformizedMarkedTransitionDensity
      initial rates duration earlierCount laterCount source target) duration]
  have hStateSum (markedTime : ℝ) (earlierTimes : Fin earlierCount → ℝ)
      (laterTimes : Fin laterCount → ℝ) :
      (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
        if states ⟨earlierCount, by omega⟩ = source ∧
            states ⟨earlierCount + 1, by omega⟩ = target then
          finiteStateTimeDependentMarkovUniformizedSliceDensity initial rates duration states
            (orderedJumpTimesMarkedJoin earlierCount laterCount
              ((markedTime, earlierTimes), laterTimes))
        else 0) =
        ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
          finiteStateTimeDependentMarkovUniformizedEndpointWordWeight initial rates
            (finiteStateTimeDependentMarkovMarkedEarlierTimes earlierCount laterCount
              (orderedJumpTimesMarkedJoin earlierCount laterCount
                ((markedTime, earlierTimes), laterTimes))) source *
          (rates.uniformizedTransitionPMF
            (orderedJumpTimesMarkedJoin earlierCount laterCount
              ((markedTime, earlierTimes), laterTimes)
              (finiteStateTimeDependentMarkovMarkedTimeIndex
                earlierCount laterCount)) source target).toReal := by
    simpa only [finiteStateTimeDependentMarkovMarkedSourceIndex,
      finiteStateTimeDependentMarkovMarkedTargetIndex] using!
      (sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
        initial rates duration earlierCount laterCount
          (orderedJumpTimesMarkedJoin earlierCount laterCount
            ((markedTime, earlierTimes), laterTimes)) source target)
  simp_rw [hStateSum]
  simp_rw [finiteStateTimeDependentMarkovMarkedEarlierTimes_markedJoin,
    finiteStateTimeDependentMarkovMarkedTime_markedJoin]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro markedTime hMarkedTime
  let clockFactor : ℝ :=
    (rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
      Real.exp (-((rates.uniformizationRate : ℝ) * duration))
  let markedTransition : ℝ :=
    (rates.uniformizedTransitionPMF markedTime source target).toReal
  let laterVolume : ℝ :=
    (duration - markedTime) ^ laterCount / laterCount.factorial
  have hClockFactor : 0 ≤ clockFactor := by
    dsimp only [clockFactor]
    positivity
  have hMarkedTransition : 0 ≤ markedTransition := by
    exact ENNReal.toReal_nonneg
  have hLaterDuration : markedTime ≤ duration := hMarkedTime.2.le
  have hLaterVolume : 0 ≤ laterVolume := by
    dsimp only [laterVolume]
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hLaterDuration) laterCount)
      (Nat.cast_nonneg laterCount.factorial)
  have hEndpointWeight (earlierTimes : Fin earlierCount → ℝ) :
      0 ≤ finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates earlierTimes source :=
    finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
      initial rates earlierTimes source
  change (∫⁻ earlierTimes : Fin earlierCount → ℝ in
      orderedJumpTimes earlierCount markedTime,
      ∫⁻ _laterTimes : Fin laterCount → ℝ in
        orderedTimesInInterval laterCount markedTime duration,
        ENNReal.ofReal
          (clockFactor *
            finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes source * markedTransition)) =
    ENNReal.ofReal clockFactor *
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates markedTime earlierCount source *
      ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume
  have hOfReal (earlierTimes : Fin earlierCount → ℝ) :
      ENNReal.ofReal
          (clockFactor *
            finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes source * markedTransition) =
        ENNReal.ofReal clockFactor *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes source) *
          ENNReal.ofReal markedTransition := by
    rw [ENNReal.ofReal_mul
      (mul_nonneg hClockFactor (hEndpointWeight earlierTimes)),
      ENNReal.ofReal_mul hClockFactor]
  simp_rw [hOfReal]
  simp_rw [lintegral_const]
  simp_rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [volume_orderedTimesInInterval laterCount markedTime duration hLaterDuration]
  change (∫⁻ earlierTimes : Fin earlierCount → ℝ in
      orderedJumpTimes earlierCount markedTime,
      ENNReal.ofReal clockFactor *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates earlierTimes source) *
        ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume) = _
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
  have hAssociate (earlierTimes : Fin earlierCount → ℝ) :
      ENNReal.ofReal clockFactor *
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes source) *
          ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume =
        ENNReal.ofReal clockFactor *
          (ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes source) *
            ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume) := by
    ac_rfl
  simp_rw [hAssociate]
  rw [lintegral_const_mul' (ENNReal.ofReal clockFactor) _ ENNReal.ofReal_ne_top]
  rw [lintegral_mul_const' (ENNReal.ofReal laterVolume) _ ENNReal.ofReal_ne_top]
  rw [lintegral_mul_const' (ENNReal.ofReal markedTransition) _ ENNReal.ofReal_ne_top]
  dsimp only [clockFactor, markedTransition, laterVolume]
  ac_rfl

/-- A finite measurable weight of the marked event time passes through the marked-sector
disintegration and future-state erasure. -/
theorem lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (earlierCount laterCount : ℕ) (source target : State)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
        orderedJumpTimes (earlierCount + 1 + laterCount) duration,
      (weight (times (finiteStateTimeDependentMarkovMarkedTimeIndex
          earlierCount laterCount)) : ℝ≥0∞) *
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
            if states ⟨earlierCount, by omega⟩ = source ∧
                states ⟨earlierCount + 1, by omega⟩ = target then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
                Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source *
          ENNReal.ofReal
            (rates.uniformizedTransitionPMF markedTime source target).toReal *
          ENNReal.ofReal
            ((duration - markedTime) ^ laterCount / laterCount.factorial) := by
  rw [lintegral_orderedJumpTimes_marked earlierCount laterCount _ duration]
  · have hStateSum (markedTime : ℝ) (earlierTimes : Fin earlierCount → ℝ)
        (laterTimes : Fin laterCount → ℝ) :
        (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
          if states ⟨earlierCount, by omega⟩ = source ∧
              states ⟨earlierCount + 1, by omega⟩ = target then
            finiteStateTimeDependentMarkovUniformizedSliceDensity initial rates duration states
              (orderedJumpTimesMarkedJoin earlierCount laterCount
                ((markedTime, earlierTimes), laterTimes))
          else 0) =
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
              Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
            finiteStateTimeDependentMarkovUniformizedEndpointWordWeight initial rates
              (finiteStateTimeDependentMarkovMarkedEarlierTimes earlierCount laterCount
                (orderedJumpTimesMarkedJoin earlierCount laterCount
                  ((markedTime, earlierTimes), laterTimes))) source *
            (rates.uniformizedTransitionPMF
              (orderedJumpTimesMarkedJoin earlierCount laterCount
                ((markedTime, earlierTimes), laterTimes)
                (finiteStateTimeDependentMarkovMarkedTimeIndex
                  earlierCount laterCount)) source target).toReal := by
      simpa only [finiteStateTimeDependentMarkovMarkedSourceIndex,
        finiteStateTimeDependentMarkovMarkedTargetIndex] using!
        (sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
          initial rates duration earlierCount laterCount
            (orderedJumpTimesMarkedJoin earlierCount laterCount
              ((markedTime, earlierTimes), laterTimes)) source target)
    simp_rw [hStateSum]
    simp_rw [finiteStateTimeDependentMarkovMarkedEarlierTimes_markedJoin,
      finiteStateTimeDependentMarkovMarkedTime_markedJoin]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro markedTime hMarkedTime
    let clockFactor : ℝ :=
      (rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
        Real.exp (-((rates.uniformizationRate : ℝ) * duration))
    let markedTransition : ℝ :=
      (rates.uniformizedTransitionPMF markedTime source target).toReal
    let laterVolume : ℝ :=
      (duration - markedTime) ^ laterCount / laterCount.factorial
    have hClockFactor : 0 ≤ clockFactor := by
      dsimp only [clockFactor]
      positivity
    have hMarkedTransition : 0 ≤ markedTransition := ENNReal.toReal_nonneg
    have hLaterDuration : markedTime ≤ duration := hMarkedTime.2.le
    have hLaterVolume : 0 ≤ laterVolume := by
      dsimp only [laterVolume]
      exact div_nonneg (pow_nonneg (sub_nonneg.mpr hLaterDuration) laterCount)
        (Nat.cast_nonneg laterCount.factorial)
    have hEndpointWeight (earlierTimes : Fin earlierCount → ℝ) :
        0 ≤ finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates earlierTimes source :=
      finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
        initial rates earlierTimes source
    change (∫⁻ earlierTimes : Fin earlierCount → ℝ in
        orderedJumpTimes earlierCount markedTime,
        ∫⁻ _laterTimes : Fin laterCount → ℝ in
          orderedTimesInInterval laterCount markedTime duration,
          (weight markedTime : ℝ≥0∞) *
            ENNReal.ofReal
              (clockFactor *
                finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                  initial rates earlierTimes source * markedTransition)) =
      (weight markedTime : ℝ≥0∞) * ENNReal.ofReal clockFactor *
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates markedTime earlierCount source *
        ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume
    have hOfReal (earlierTimes : Fin earlierCount → ℝ) :
        ENNReal.ofReal
            (clockFactor *
              finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes source * markedTransition) =
          ENNReal.ofReal clockFactor *
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes source) *
            ENNReal.ofReal markedTransition := by
      rw [ENNReal.ofReal_mul
        (mul_nonneg hClockFactor (hEndpointWeight earlierTimes)),
        ENNReal.ofReal_mul hClockFactor]
    simp_rw [hOfReal]
    simp_rw [lintegral_const]
    simp_rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [volume_orderedTimesInInterval laterCount markedTime duration hLaterDuration]
    change (∫⁻ earlierTimes : Fin earlierCount → ℝ in
        orderedJumpTimes earlierCount markedTime,
        (weight markedTime : ℝ≥0∞) *
            (ENNReal.ofReal clockFactor *
                ENNReal.ofReal
                  (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                    initial rates earlierTimes source) *
              ENNReal.ofReal markedTransition) *
          ENNReal.ofReal laterVolume) = _
    unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    have hAssociate (earlierTimes : Fin earlierCount → ℝ) :
        (weight markedTime : ℝ≥0∞) *
              (ENNReal.ofReal clockFactor *
                  ENNReal.ofReal
                    (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                      initial rates earlierTimes source) *
                ENNReal.ofReal markedTransition) *
            ENNReal.ofReal laterVolume =
          (weight markedTime : ℝ≥0∞) *
            (ENNReal.ofReal clockFactor *
              (ENNReal.ofReal
                  (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                    initial rates earlierTimes source) *
                ENNReal.ofReal markedTransition * ENNReal.ofReal laterVolume)) := by
      ac_rfl
    simp_rw [hAssociate]
    rw [lintegral_const_mul' (weight markedTime : ℝ≥0∞) _ ENNReal.coe_ne_top]
    rw [lintegral_const_mul' (ENNReal.ofReal clockFactor) _ ENNReal.ofReal_ne_top]
    rw [lintegral_mul_const' (ENNReal.ofReal laterVolume) _ ENNReal.ofReal_ne_top]
    rw [lintegral_mul_const' (ENNReal.ofReal markedTransition) _ ENNReal.ofReal_ne_top]
    dsimp only [clockFactor, markedTransition, laterVolume]
    ac_rfl
  · exact
      ((hWeight.coe_nnreal_ennreal.comp
        (measurable_pi_apply
          (finiteStateTimeDependentMarkovMarkedTimeIndex earlierCount laterCount))).mul
        (measurable_finiteStateTimeDependentMarkovUniformizedMarkedTransitionDensity
          initial rates duration earlierCount laterCount source target))

/-- Summing every future virtual-event count removes the later observation horizon from one
fixed earlier-count marked-transition sector. -/
theorem tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (earlierCount : ℕ) (source target : State) :
    (∑' laterCount : ℕ,
      ∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
          orderedJumpTimes (earlierCount + 1 + laterCount) duration,
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
            if states ⟨earlierCount, by omega⟩ = source ∧
                states ⟨earlierCount + 1, by omega⟩ = target then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        ENNReal.ofReal
            ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
              Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source *
          ENNReal.ofReal
            (rates.uniformizedTransitionPMF markedTime source target).toReal := by
  simp_rw [lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition]
  rw [← lintegral_tsum]
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro markedTime hMarkedTime
    have hMarkedDuration : markedTime ≤ (duration : ℝ) := hMarkedTime.2.le
    let remainingDuration : ℝ≥0 :=
      ⟨(duration : ℝ) - markedTime, sub_nonneg.mpr hMarkedDuration⟩
    let endpointClock : ℝ≥0∞ :=
      ENNReal.ofReal
        ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
          Real.exp (-((rates.uniformizationRate : ℝ) * markedTime)))
    let endpointCoefficient :=
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates markedTime earlierCount source
    let markedTransition := ENNReal.ofReal
      (rates.uniformizedTransitionPMF markedTime source target).toReal
    have hSummand (laterCount : ℕ) :
        ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
                Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) *
            endpointCoefficient * markedTransition *
            ENNReal.ofReal
              (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial) =
          endpointCoefficient * markedTransition *
            (endpointClock * poissonCountPMF
              (rates.uniformizationRate * remainingDuration) laterCount) := by
      rw [← finiteStateTimeDependentMarkovCutClockFactor_eq_endpoint_mul_poisson
        rates duration markedTime hMarkedDuration (earlierCount + 1) laterCount]
      ac_rfl
    change (∑' laterCount : ℕ,
      ENNReal.ofReal
            ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
              Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) *
          endpointCoefficient * markedTransition *
          ENNReal.ofReal
            (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial)) =
      endpointClock * endpointCoefficient * markedTransition
    simp_rw [hSummand]
    calc
      (∑' laterCount : ℕ,
        endpointCoefficient * markedTransition *
          (endpointClock * poissonCountPMF
            (rates.uniformizationRate * remainingDuration) laterCount)) =
          endpointCoefficient * markedTransition * endpointClock *
            ∑' laterCount : ℕ,
              poissonCountPMF
                (rates.uniformizationRate * remainingDuration) laterCount := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        ac_rfl
      _ = endpointClock * endpointCoefficient * markedTransition := by
        rw [(poissonCountPMF
          (rates.uniformizationRate * remainingDuration)).tsum_coe]
        simp
        ac_rfl
      _ = _ := rfl
  · intro laterCount
    apply Measurable.aemeasurable
    have hClock : Measurable fun _markedTime : ℝ ↦
        ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
            Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) :=
      measurable_const
    have hCoefficient :=
      measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates earlierCount source
    have hTransition : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (rates.uniformizedTransitionPMF markedTime source target).toReal :=
      (rates.measurable_uniformizedTransitionPMF_toReal source target).ennreal_ofReal
    have hLaterVolume : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial) := by
      apply Measurable.ennreal_ofReal
      fun_prop
    exact (((hClock.mul hCoefficient).mul hTransition).mul hLaterVolume)

/-- Summing every future virtual-event count preserves a finite measurable marked-time weight
while removing the later observation horizon. -/
theorem
    tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (earlierCount : ℕ) (source target : State)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∑' laterCount : ℕ,
      ∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
          orderedJumpTimes (earlierCount + 1 + laterCount) duration,
        (weight (times (finiteStateTimeDependentMarkovMarkedTimeIndex
            earlierCount laterCount)) : ℝ≥0∞) *
          ENNReal.ofReal
            (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
              if states ⟨earlierCount, by omega⟩ = source ∧
                  states ⟨earlierCount + 1, by omega⟩ = target then
                finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times
              else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
                Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source *
          ENNReal.ofReal
            (rates.uniformizedTransitionPMF markedTime source target).toReal := by
  simp_rw [
    lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
      initial rates duration _ _ source target weight hWeight]
  rw [← lintegral_tsum]
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro markedTime hMarkedTime
    have hMarkedDuration : markedTime ≤ (duration : ℝ) := hMarkedTime.2.le
    let remainingDuration : ℝ≥0 :=
      ⟨(duration : ℝ) - markedTime, sub_nonneg.mpr hMarkedDuration⟩
    let endpointClock : ℝ≥0∞ :=
      ENNReal.ofReal
        ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
          Real.exp (-((rates.uniformizationRate : ℝ) * markedTime)))
    let endpointCoefficient :=
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates markedTime earlierCount source
    let markedTransition := ENNReal.ofReal
      (rates.uniformizedTransitionPMF markedTime source target).toReal
    have hSummand (laterCount : ℕ) :
        (weight markedTime : ℝ≥0∞) *
              ENNReal.ofReal
                ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
                  Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) *
            endpointCoefficient * markedTransition *
            ENNReal.ofReal
              (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial) =
          (weight markedTime : ℝ≥0∞) *
            (endpointCoefficient * markedTransition *
              (endpointClock * poissonCountPMF
                (rates.uniformizationRate * remainingDuration) laterCount)) := by
      rw [← finiteStateTimeDependentMarkovCutClockFactor_eq_endpoint_mul_poisson
        rates duration markedTime hMarkedDuration (earlierCount + 1) laterCount]
      ac_rfl
    change (∑' laterCount : ℕ,
      (weight markedTime : ℝ≥0∞) *
            ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
                Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) *
          endpointCoefficient * markedTransition *
          ENNReal.ofReal
            (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial)) =
      (weight markedTime : ℝ≥0∞) * endpointClock * endpointCoefficient * markedTransition
    simp_rw [hSummand]
    have hFactor (laterCount : ℕ) :
        (weight markedTime : ℝ≥0∞) *
            (endpointCoefficient * markedTransition *
              (endpointClock * poissonCountPMF
                (rates.uniformizationRate * remainingDuration) laterCount)) =
          ((weight markedTime : ℝ≥0∞) * endpointCoefficient * markedTransition *
              endpointClock) *
            poissonCountPMF
              (rates.uniformizationRate * remainingDuration) laterCount := by
      ac_rfl
    simp_rw [hFactor]
    rw [ENNReal.tsum_mul_left]
    rw [(poissonCountPMF
      (rates.uniformizationRate * remainingDuration)).tsum_coe]
    simp
    ac_rfl
  · intro laterCount
    apply Measurable.aemeasurable
    have hClock : Measurable fun _markedTime : ℝ ↦
        ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1 + laterCount) *
            Real.exp (-((rates.uniformizationRate : ℝ) * (duration : ℝ)))) :=
      measurable_const
    have hCoefficient :=
      measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates earlierCount source
    have hTransition : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (rates.uniformizedTransitionPMF markedTime source target).toReal :=
      (rates.measurable_uniformizedTransitionPMF_toReal source target).ennreal_ofReal
    have hLaterVolume : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (((duration : ℝ) - markedTime) ^ laterCount / laterCount.factorial) := by
      apply Measurable.ennreal_ofReal
      fun_prop
    exact ((((hWeight.coe_nnreal_ennreal.mul hClock).mul hCoefficient).mul
      hTransition).mul hLaterVolume)

/-- Summing the earlier-event sectors identifies the endpoint probability times the
marked common-clock transition intensity. -/
theorem tsum_finiteStateTimeDependentMarkovUniformizedMarkedEndpointSector
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (markedTime : ℝ) (source target : State) :
    (∑' earlierCount : ℕ,
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
            Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates markedTime earlierCount source *
        ENNReal.ofReal
          (rates.uniformizedTransitionPMF markedTime source target).toReal) =
      finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source *
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
            rates markedTime source target) := by
  let survival : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-((rates.uniformizationRate : ℝ) * markedTime)))
  let transition : ℝ≥0∞ := ENNReal.ofReal
    (rates.uniformizedTransitionPMF markedTime source target).toReal
  have hClock (earlierCount : ℕ) :
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
            Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) =
        survival * (rates.uniformizationRate : ℝ≥0∞) ^ (earlierCount + 1) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) (earlierCount + 1))]
    rw [ENNReal.ofReal_pow (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity)]
    simp only [ENNReal.ofReal_coe_nnreal]
    dsimp only [survival]
    ac_rfl
  have hIntensity :
      (rates.uniformizationRate : ℝ≥0∞) * transition =
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
            rates markedTime source target) := by
    unfold finiteStateTimeDependentMarkovUniformizedTransitionIntensity
    dsimp only [transition]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_mul (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity)]
    congr 1
  simp_rw [hClock]
  calc
    (∑' earlierCount : ℕ,
      survival * (rates.uniformizationRate : ℝ≥0∞) ^ (earlierCount + 1) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source * transition) =
        ∑' earlierCount : ℕ,
          survival *
            ((rates.uniformizationRate : ℝ≥0∞) ^ earlierCount *
              finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                initial rates markedTime earlierCount source) *
            ((rates.uniformizationRate : ℝ≥0∞) * transition) := by
      apply tsum_congr
      intro earlierCount
      rw [pow_succ]
      ac_rfl
    _ = survival *
        (∑' earlierCount : ℕ,
          (rates.uniformizationRate : ℝ≥0∞) ^ earlierCount *
            finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
              initial rates markedTime earlierCount source) *
        ((rates.uniformizationRate : ℝ≥0∞) * transition) := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ = finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source *
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
            rates markedTime source target) := by
      rw [hIntensity]
      rfl

/-- Resumming both sides of a marked virtual event gives the exact endpoint-probability--intensity
compensator integral. -/
theorem tsum_tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (source target : State) :
    (∑' earlierCount : ℕ,
      ∑' laterCount : ℕ,
        ∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
            orderedJumpTimes (earlierCount + 1 + laterCount) duration,
          ENNReal.ofReal
            (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
              if states ⟨earlierCount, by omega⟩ = source ∧
                  states ⟨earlierCount + 1, by omega⟩ = target then
                finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times
              else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) := by
  simp_rw [tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition]
  rw [← lintegral_tsum]
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro markedTime _hMarkedTime
    exact tsum_finiteStateTimeDependentMarkovUniformizedMarkedEndpointSector
      initial rates markedTime source target
  · intro earlierCount
    apply Measurable.aemeasurable
    have hClock : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
            Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) := by
      apply Measurable.ennreal_ofReal
      fun_prop
    have hCoefficient :=
      measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates earlierCount source
    have hTransition : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (rates.uniformizedTransitionPMF markedTime source target).toReal :=
      (rates.measurable_uniformizedTransitionPMF_toReal source target).ennreal_ofReal
    exact (hClock.mul hCoefficient).mul hTransition

/-- Resumming both sides of a finitely weighted marked virtual event gives the endpoint-
probability--intensity compensator integral with the same physical-time weight. -/
theorem
    tsum_tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (source target : State)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∑' earlierCount : ℕ,
      ∑' laterCount : ℕ,
        ∫⁻ times : Fin (earlierCount + 1 + laterCount) → ℝ in
            orderedJumpTimes (earlierCount + 1 + laterCount) duration,
          (weight (times (finiteStateTimeDependentMarkovMarkedTimeIndex
              earlierCount laterCount)) : ℝ≥0∞) *
            ENNReal.ofReal
              (∑ states : Fin (earlierCount + 1 + laterCount + 1) → State,
                if states ⟨earlierCount, by omega⟩ = source ∧
                    states ⟨earlierCount + 1, by omega⟩ = target then
                  finiteStateTimeDependentMarkovUniformizedSliceDensity
                    initial rates duration states times
                else 0)) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) := by
  simp_rw [
    tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
      initial rates duration _ source target weight hWeight]
  rw [← lintegral_tsum]
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro markedTime _hMarkedTime
    simp only
    change (∑' earlierCount : ℕ,
      (weight markedTime : ℝ≥0∞) *
          ENNReal.ofReal
            ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
              Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates markedTime earlierCount source *
          ENNReal.ofReal
            (rates.uniformizedTransitionPMF markedTime source target).toReal) = _
    have hAssociate (earlierCount : ℕ) :
        (weight markedTime : ℝ≥0∞) *
              ENNReal.ofReal
                ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
                  Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
            finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
              initial rates markedTime earlierCount source *
            ENNReal.ofReal
              (rates.uniformizedTransitionPMF markedTime source target).toReal =
          (weight markedTime : ℝ≥0∞) *
            (ENNReal.ofReal
                ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
                  Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) *
              finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                initial rates markedTime earlierCount source *
              ENNReal.ofReal
                (rates.uniformizedTransitionPMF markedTime source target).toReal) := by
      ac_rfl
    simp_rw [hAssociate]
    rw [ENNReal.tsum_mul_left]
    rw [tsum_finiteStateTimeDependentMarkovUniformizedMarkedEndpointSector]
    ac_rfl
  · intro earlierCount
    apply Measurable.aemeasurable
    have hClock : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ (earlierCount + 1) *
            Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) := by
      apply Measurable.ennreal_ofReal
      fun_prop
    have hCoefficient :=
      measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates earlierCount source
    have hTransition : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (rates.uniformizedTransitionPMF markedTime source target).toReal :=
      (rates.measurable_uniformizedTransitionPMF_toReal source target).ennreal_ofReal
    exact ((hWeight.coe_nnreal_ennreal.mul hClock).mul hCoefficient).mul hTransition

end

end FiniteMarkovProcesses.Probability
