/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.MeasureTheory.Measure.PiWithDensity
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateTimeDependentMarkovJumpRadonNikodym
import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDeterministicInitialReplication

/-!
# Heterogeneous time-dependent Markov replica Radon--Nikodym tilt

The exact one-history Girsanov identity tensors over a finite family whose labelled replicas may
start in different prospectively supplied states.  The physical duration and both rate families
remain unchanged; the product log action is the literal sum of the coordinate actions.

This finite-particle theorem is the change-of-measure layer needed before any macroscopic lower
bound.  It does not assert an LDP or take a particle or regularization limit.

## Main results

- `finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction`: summed physical action.
- `finiteStateTimeDependentMarkovDeterministicInitialReplicaMeasure_withDensity_expLogAction`:
  exact heterogeneous finite-product Girsanov identity.
- `exp_neg_threshold_mul_timeDependentCandidateReplica_event_le_referenceReplica_event`:
  finite-particle event lower estimate under an action cap.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Sum of the complete candidate-to-reference actions over a heterogeneous deterministic-
initial replica family. -/
noncomputable def finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ) :
    (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
  fun histories ↦ ∑ replica,
    finiteStateTimeDependentMarkovJumpLogAction
      (PMF.pure (initialConfiguration replica))
      (PMF.pure (initialConfiguration replica))
      rates referenceRates duration (histories replica)

/-- The summed heterogeneous replica action is measurable. -/
theorem measurable_finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ) :
    Measurable (finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
      initialConfiguration rates referenceRates duration) := by
  unfold finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
  apply Finset.measurable_sum Finset.univ
  intro replica _hReplica
  exact (measurable_finiteStateTimeDependentMarkovJumpLogAction
    (PMF.pure (initialConfiguration replica))
    (PMF.pure (initialConfiguration replica)) rates referenceRates duration).comp
      (measurable_pi_apply replica)

/-- Product of the coordinate exponential action densities. -/
noncomputable def finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ) :
    (Fin replicaCount → FiniteJumpHistory State) → ℝ≥0∞ :=
  fun histories ↦ ∏ replica, ENNReal.ofReal (Real.exp
    (finiteStateTimeDependentMarkovJumpLogAction
      (PMF.pure (initialConfiguration replica))
      (PMF.pure (initialConfiguration replica))
      rates referenceRates duration (histories replica)))

/-- The product exponential action density is measurable. -/
theorem measurable_finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ) :
    Measurable (finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
      initialConfiguration rates referenceRates duration) := by
  unfold finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
  apply Finset.measurable_prod Finset.univ
  intro replica _hReplica
  exact ((measurable_finiteStateTimeDependentMarkovJumpLogAction
    (PMF.pure (initialConfiguration replica))
    (PMF.pure (initialConfiguration replica)) rates referenceRates duration).comp
      (measurable_pi_apply replica)).exp.ennreal_ofReal

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The product density is exactly the exponential of the summed complete replica action. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal_eq
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ)
    (histories : Fin replicaCount → FiniteJumpHistory State) :
    finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
        initialConfiguration rates referenceRates duration histories =
      ENNReal.ofReal (Real.exp
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
          initialConfiguration rates referenceRates duration histories)) := by
  unfold finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
    finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  intro replica _hReplica
  exact (Real.exp_pos _).le

/-- Exact finite-product Girsanov identity for replicas with a common pair of bounded rates and
prospectively supplied, possibly heterogeneous, initial states. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplicaMeasure_withDensity_expLogAction
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : NNReal) :
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration referenceRates duration).toMeasure.withDensity
      (fun histories ↦ ENNReal.ofReal (Real.exp
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
          initialConfiguration rates referenceRates duration histories))) =
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure := by
  have hDensity :
      (fun histories ↦ ENNReal.ofReal (Real.exp
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
          initialConfiguration rates referenceRates (duration : ℝ) histories))) =
        finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
          initialConfiguration rates referenceRates (duration : ℝ) := by
    funext histories
    exact (finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal_eq
      initialConfiguration rates referenceRates (duration : ℝ) histories).symm
  rw [hDensity]
  rw [finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure,
    finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure_toMeasure]
  let candidate := fun replica : Fin replicaCount ↦
    finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure (initialConfiguration replica)) rates duration
  let reference := fun replica : Fin replicaCount ↦
    finiteStateTimeDependentMarkovReducedHistoryMeasure
      (PMF.pure (initialConfiguration replica)) referenceRates duration
  let density := fun replica : Fin replicaCount ↦ fun history : FiniteJumpHistory State ↦
    ENNReal.ofReal (Real.exp (finiteStateTimeDependentMarkovJumpLogAction
      (PMF.pure (initialConfiguration replica))
      (PMF.pure (initialConfiguration replica))
      rates referenceRates duration history))
  have hSingle (replica : Fin replicaCount) :
      candidate replica = (reference replica).withDensity (density replica) := by
    dsimp only [candidate, reference, density]
    rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure,
      finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure]
    exact (finiteStateTimeDependentMarkovJumpDensityMeasure_withDensity_expLogAction
      (fun _state ↦ Iff.rfl) hRateSupport duration).symm
  let : ∀ replica : Fin replicaCount, IsProbabilityMeasure (reference replica) :=
    fun replica ↦ ⟨by
      dsimp only [reference]
      exact finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
        (PMF.pure (initialConfiguration replica)) referenceRates duration⟩
  let : ∀ replica : Fin replicaCount, IsProbabilityMeasure (candidate replica) :=
    fun replica ↦ ⟨by
      dsimp only [candidate]
      exact finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
        (PMF.pure (initialConfiguration replica)) rates duration⟩
  let : ∀ replica : Fin replicaCount, SigmaFinite (reference replica) :=
    fun _replica ↦ inferInstance
  let : ∀ replica : Fin replicaCount,
      SigmaFinite ((reference replica).withDensity (density replica)) := fun replica ↦ by
    rw [← hSingle replica]
    dsimp only [candidate]
    infer_instance
  change (Measure.pi reference).withDensity
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaExpLogActionENNReal
        initialConfiguration rates referenceRates duration) =
    Measure.pi candidate
  rw [show candidate = fun replica ↦ (reference replica).withDensity (density replica) by
    funext replica
    exact hSingle replica]
  rw [Measure.pi_withDensity_fin reference density (by
    intro replica
    exact ((measurable_finiteStateTimeDependentMarkovJumpLogAction
      (PMF.pure (initialConfiguration replica))
      (PMF.pure (initialConfiguration replica)) rates referenceRates duration).exp.ennreal_ofReal))]
  rfl

/-- Finite-particle Girsanov lower estimate: if the summed complete action is at most one
threshold on a measurable event, the reference replica law assigns at least the exponentially
discounted candidate mass to that event. -/
theorem exp_neg_threshold_mul_timeDependentCandidateReplica_event_le_referenceReplica_event
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : NNReal) {event : Set (Fin replicaCount → FiniteJumpHistory State)}
    (hEvent : MeasurableSet event) (threshold : ℝ)
    (hAction : ∀ histories ∈ event,
      finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
        initialConfiguration rates referenceRates duration histories ≤ threshold) :
    ENNReal.ofReal (Real.exp (-threshold)) *
        (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates duration).toMeasure event ≤
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration referenceRates duration).toMeasure event := by
  let candidate :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let reference :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration referenceRates duration).toMeasure
  let density := fun histories ↦ ENNReal.ofReal (Real.exp
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
      initialConfiguration rates referenceRates (duration : ℝ) histories))
  have hTilt : reference.withDensity density = candidate :=
    finiteStateTimeDependentMarkovDeterministicInitialReplicaMeasure_withDensity_expLogAction
      initialConfiguration rates referenceRates hRateSupport duration
  have hUpper : candidate event ≤
      ENNReal.ofReal (Real.exp threshold) * reference event := by
    rw [← hTilt, withDensity_apply _ hEvent]
    calc
      (∫⁻ histories in event, density histories ∂reference) ≤
          ∫⁻ _histories in event, ENNReal.ofReal (Real.exp threshold) ∂reference := by
            apply setLIntegral_mono' hEvent
            intro histories hHistories
            dsimp only [density]
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr (hAction histories hHistories))
      _ = _ := setLIntegral_const event _
  change ENNReal.ofReal (Real.exp (-threshold)) * candidate event ≤ reference event
  calc
    ENNReal.ofReal (Real.exp (-threshold)) * candidate event ≤
        ENNReal.ofReal (Real.exp (-threshold)) *
          (ENNReal.ofReal (Real.exp threshold) * reference event) :=
      mul_le_mul_right hUpper _
    _ = reference event := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp

/-- Finite-particle change-of-measure lower estimate with an explicit candidate-mass remainder.
The action cap need only hold on the requested event outside a separately measurable bad-action
event; the two candidate failure probabilities remain visible and can be discharged by topology
and action concentration. -/
theorem exp_neg_threshold_mul_one_sub_timeDependentCandidateReplica_failureMass_le_reference_event
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates referenceRates : FiniteStateTimeDependentMarkovRate State)
    (hRateSupport :
      FiniteStateTimeDependentMarkovRatesHaveSameDirectedSupport rates referenceRates)
    (duration : NNReal) {event badActionEvent : Set
      (Fin replicaCount → FiniteJumpHistory State)}
    (hEvent : MeasurableSet event) (hBadActionEvent : MeasurableSet badActionEvent)
    (threshold : ℝ)
    (hAction : ∀ histories ∈ event, histories ∉ badActionEvent →
      finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
        initialConfiguration rates referenceRates duration histories ≤ threshold) :
    let candidate :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    let reference :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration referenceRates duration).toMeasure
    ENNReal.ofReal (Real.exp (-threshold)) *
        (1 - (candidate eventᶜ + candidate badActionEvent)) ≤
      reference event := by
  dsimp only
  let candidate :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let reference :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration referenceRates duration).toMeasure
  let goodEvent := event \ badActionEvent
  have hGoodEvent : MeasurableSet goodEvent := hEvent.diff hBadActionEvent
  have hCandidateProbability : candidate Set.univ = 1 := by
    dsimp only [candidate]
    exact
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).property.measure_univ
  have hCover : Set.univ ⊆ goodEvent ∪ eventᶜ ∪ badActionEvent := by
    intro histories _hHistories
    by_cases hInEvent : histories ∈ event
    · by_cases hInBad : histories ∈ badActionEvent
      · exact Set.mem_union_right _ hInBad
      · exact Set.mem_union_left _ <| Set.mem_union_left _ ⟨hInEvent, hInBad⟩
    · exact Set.mem_union_left _ <| Set.mem_union_right _ hInEvent
  have hCandidateCover : 1 ≤
      candidate goodEvent + candidate eventᶜ + candidate badActionEvent := by
    rw [← hCandidateProbability]
    calc
      candidate Set.univ ≤ candidate (goodEvent ∪ eventᶜ ∪ badActionEvent) :=
        measure_mono hCover
      _ ≤ candidate (goodEvent ∪ eventᶜ) + candidate badActionEvent :=
        measure_union_le _ _
      _ ≤ (candidate goodEvent + candidate eventᶜ) + candidate badActionEvent := by
        gcongr
        exact measure_union_le _ _
  have hCandidateGood :
      1 - (candidate eventᶜ + candidate badActionEvent) ≤ candidate goodEvent := by
    rw [tsub_le_iff_right]
    simpa only [add_assoc, add_left_comm, add_comm] using hCandidateCover
  have hTiltLower :
      ENNReal.ofReal (Real.exp (-threshold)) * candidate goodEvent ≤
        reference goodEvent := by
    exact
      exp_neg_threshold_mul_timeDependentCandidateReplica_event_le_referenceReplica_event
        initialConfiguration rates referenceRates hRateSupport duration hGoodEvent threshold
        (fun histories hHistories ↦
          hAction histories hHistories.1 hHistories.2)
  calc
    ENNReal.ofReal (Real.exp (-threshold)) *
          (1 - (candidate eventᶜ + candidate badActionEvent)) ≤
        ENNReal.ofReal (Real.exp (-threshold)) * candidate goodEvent := by
      gcongr
    _ ≤ reference goodEvent := hTiltLower
    _ ≤ reference event := measure_mono Set.sdiff_subset

end

end FiniteMarkovProcesses.InformationTheory
