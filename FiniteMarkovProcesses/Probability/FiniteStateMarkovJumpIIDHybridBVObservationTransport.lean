/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovInitialMixture
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpRandomEmpiricalTypeHybridBVObservation
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialPermutation

/-!
# IID initial-state transport to the empirical-type hybrid-BV source

This module proves that the empirical hybrid-BV observation of genuinely IID-initialized Markov
jump replicas is exactly the canonical random empirical-count-type mixture.  The proof first
expands the one-history law over pure initial states, distributes the finite particle product over
labelled initial configurations, and then groups those configurations by exact empirical type.
Permutation invariance identifies every labelled configuration in a fibre with its canonical
representative.

The result is equality only after the empirical hybrid-BV observation.  It does not identify the
labelled microscopic laws: the count-type source deliberately selects one representative in each
permutation orbit.

## Main declarations

- `finiteStateMarkovJumpDensityMeasure_eq_sum_initialState_smul_pure`.
-
  `finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure_eq_sum_initialConfiguration_smul_deterministic`.
-
  `finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_sum_initialConfiguration_smul_deterministic`.
- `finiteStateMarkovJumpIIDHybridBVObservationLaw_eq_randomEmpiricalTypeHybridBVObservationLaw`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open PositiveFiniteJumpHistoryReplicas
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A homogeneous finite-state jump history law is the exact finite mixture of its pure-initial
history laws.  This is inherited from the already-proved time-dependent source mixture through
constant-rate recovery. -/
theorem finiteStateMarkovJumpDensityMeasure_eq_sum_initialState_smul_pure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpDensityMeasure initial generator duration =
      ∑ state, initial state • finiteStateMarkovJumpDensityMeasure
        (PMF.pure state) generator duration := by
  let nonnegativeDuration : NNReal := ⟨duration, hDuration⟩
  change finiteStateMarkovJumpDensityMeasure initial generator (nonnegativeDuration : ℝ) =
    ∑ state, initial state • finiteStateMarkovJumpDensityMeasure
      (PMF.pure state) generator (nonnegativeDuration : ℝ)
  rw [← finiteStateTimeDependentMarkovReducedHistoryMeasure_constant
      initial generator nonnegativeDuration]
  rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_smul_pure]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_constant]

/-- The IID history product expands exactly over every labelled initial configuration, weighted
by its coordinatewise product probability. -/
theorem
finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure_eq_sum_initialConfiguration_smul_deterministic
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    (finiteStateMarkovJumpReplicaProbabilityMeasure
      replicaCount initial generator duration hNormalized).toMeasure =
      ∑ initialConfiguration : Fin replicaCount → State,
        (∏ replica, initial (initialConfiguration replica)) •
          (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
            initialConfiguration generator duration hDuration).toMeasure := by
  rw [finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure]
  apply Measure.pi_eq
  intro event _hEvent
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_toMeasure,
    Measure.pi_pi _ event]
  have hCoordinate (replica : Fin replicaCount) :
      finiteStateMarkovJumpDensityMeasure initial generator duration (event replica) =
        ∑ state, initial state *
          finiteStateMarkovJumpDensityMeasure
            (PMF.pure state) generator duration (event replica) := by
    rw [finiteStateMarkovJumpDensityMeasure_eq_sum_initialState_smul_pure
      initial generator duration hDuration]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, smul_eq_mul]
  simp_rw [hCoordinate]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro initialConfiguration _hConfiguration
  rw [← Finset.prod_mul_distrib]

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- The empirical hybrid-BV observation of IID-initialized replicas is the exact finite mixture
of deterministic-initial observation laws over all labelled initial configurations. -/
theorem
finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_sum_initialConfiguration_smul_deterministic
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
        successorIndex initial generator duration hNormalized =
      ∑ initialConfiguration : Fin (successorIndex + 1) → State,
        (∏ replica, initial (initialConfiguration replica)) •
          finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
            successorIndex initialConfiguration generator duration hDuration := by
  rw [finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_map_replicaLaw]
  rw [
    finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure_eq_sum_initialConfiguration_smul_deterministic
      (successorIndex + 1) initial generator duration hDuration hNormalized]
  ext event hEvent
  simp only [Measure.map_apply
      (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration) hEvent,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro initialConfiguration _hConfiguration
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw,
    Measure.map_apply
      (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration) hEvent]

/-- After the empirical hybrid-BV observation, genuine IID initialization equals the canonical
mixture over the IID empirical-count-type law.  No equality of labelled microscopic sources is
asserted. -/
theorem finiteStateMarkovJumpIIDHybridBVObservationLaw_eq_randomEmpiricalTypeHybridBVObservationLaw
    (successorIndex : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw
        successorIndex initial generator duration hNormalized =
      finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw successorIndex
        (finiteIIDPositiveEmpiricalTypeLaw successorIndex initial)
        generator duration hDuration := by
  classical
  rw [
    finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_eq_sum_initialConfiguration_smul_deterministic
      successorIndex initial generator duration hDuration hNormalized]
  ext event hEvent
  rw [finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply_eq_sum
    successorIndex (finiteIIDPositiveEmpiricalTypeLaw successorIndex initial)
      generator duration hDuration hEvent]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := finiteIIDPositiveSampleEmpiricalType successorIndex)
    (f := fun initialConfiguration ↦
      (∏ replica, initial (initialConfiguration replica)) *
        finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration event)]
  change (∑ empiricalType,
      ∑ initialConfiguration ∈ Finset.univ.filter fun candidate ↦
        finiteIIDPositiveSampleEmpiricalType successorIndex candidate = empiricalType,
        (∏ replica, initial (initialConfiguration replica)) *
          finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
            successorIndex initialConfiguration generator duration hDuration event) = _
  apply Finset.sum_congr rfl
  intro empiricalType _hEmpiricalType
  have hLawEq (initialConfiguration : Fin (successorIndex + 1) → State)
      (hConfiguration :
        finiteIIDPositiveSampleEmpiricalType successorIndex initialConfiguration =
          empiricalType) :
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration =
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
          empiricalType generator duration hDuration := by
    unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
    apply finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_of_empiricalType_eq
    exact hConfiguration.trans
      (finiteIIDPositiveSampleEmpiricalType_representative empiricalType).symm
  have hInner :
      (∑ initialConfiguration ∈ Finset.univ.filter fun candidate ↦
          finiteIIDPositiveSampleEmpiricalType successorIndex candidate = empiricalType,
        (∏ replica, initial (initialConfiguration replica)) *
          finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
            successorIndex initialConfiguration generator duration hDuration event) =
        (∑ initialConfiguration ∈ Finset.univ.filter fun candidate ↦
            finiteIIDPositiveSampleEmpiricalType successorIndex candidate = empiricalType,
          ∏ replica, initial (initialConfiguration replica)) *
            finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
              empiricalType generator duration hDuration event := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro initialConfiguration hConfiguration
    rw [hLawEq initialConfiguration (Finset.mem_filter.mp hConfiguration).2]
  have hWeight :
      (∑ initialConfiguration ∈ Finset.univ.filter fun candidate ↦
          finiteIIDPositiveSampleEmpiricalType successorIndex candidate = empiricalType,
        ∏ replica, initial (initialConfiguration replica)) =
        finiteIIDPositiveEmpiricalTypeLaw successorIndex initial {empiricalType} := by
    rw [finiteIIDPositiveEmpiricalTypeLaw, Measure.map_apply
      (measurable_of_finite _) (MeasurableSet.singleton _)]
    let fibre := Finset.univ.filter fun candidate ↦
      finiteIIDPositiveSampleEmpiricalType successorIndex candidate = empiricalType
    have hFibreSet :
        finiteIIDPositiveSampleEmpiricalType successorIndex ⁻¹' {empiricalType} =
          (fibre : Set (Fin (successorIndex + 1) → State)) := by
      ext initialConfiguration
      simp [fibre]
    rw [hFibreSet, ← sum_measure_singleton]
    change (∑ initialConfiguration ∈ fibre,
        ∏ replica, initial (initialConfiguration replica)) =
      ∑ initialConfiguration ∈ fibre,
        finiteIIDPositiveSampleLaw successorIndex initial {initialConfiguration}
    apply Finset.sum_congr rfl
    intro initialConfiguration _hConfiguration
    rw [finiteIIDPositiveSampleLaw_apply_singleton]
  rw [hInner, hWeight, mul_comm]

end

end FiniteMarkovProcesses.Probability
