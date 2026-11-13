/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalTypeLaw
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation

/-!
# Random empirical-type Markov-jump replica laws

This module mixes the canonical deterministic-initial Markov-jump replica law over an arbitrary
probability law on exact positive empirical count types.  Both the microscopic common-carrier law
and its hybrid bounded-variation observation are constructed as compositions with explicit Markov
kernels.  Their finite atomic decompositions retain the conditional law at every empirical type.

No large-deviation estimate or asymptotic disintegration theorem is asserted here.

## Main declarations

- `finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel`: conditional microscopic law.
- `finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw`: mixed microscopic law.
- `finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel`: conditional hybrid law.
- `finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw`: mixed hybrid law.
- `finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_eq_sum_smul`: exact finite
  atomic disintegration.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Conditional common-carrier history law associated with one exact empirical count type. -/
noncomputable def finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
    (successorIndex : ℕ) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    Kernel (FiniteIIDPositiveEmpiricalType State successorIndex)
      (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  Kernel.ofFunOfCountable fun empiricalType ↦
    finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
      empiricalType generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Evaluation of the microscopic conditional kernel is the canonical empirical-type law. -/
@[simp]
theorem finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel_apply
    (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
        successorIndex generator duration hDuration empiricalType =
      finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
        empiricalType generator duration hDuration :=
  rfl

/-- The empirical-type-indexed microscopic conditional law is a Markov kernel. -/
instance instIsMarkovKernelFiniteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
    (successorIndex : ℕ) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    IsMarkovKernel
      (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
        successorIndex generator duration hDuration) :=
  ⟨fun empiricalType ↦
    finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw_isProbabilityMeasure
      empiricalType generator duration hDuration⟩

/-- Common-carrier history law obtained by mixing the canonical conditional law over a random
exact empirical count type. -/
noncomputable def finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration ∘ₘ
    initialEmpiricalTypeLaw

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- A probability law on empirical count types produces a normalized mixed microscopic law. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_isProbabilityMeasure
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
  infer_instance

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Exact eventwise disintegration of the mixed microscopic law over its empirical type. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_apply
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteStateMarkovJumpPositiveReplicaFamily State)}
    (hEvent : MeasurableSet event) :
    finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration event =
      ∫⁻ empiricalType,
        finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
          empiricalType generator duration hDuration event ∂initialEmpiricalTypeLaw := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
  rw [Measure.bind_apply hEvent (Kernel.aemeasurable _)]
  rfl

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The eventwise microscopic disintegration is an ordinary finite sum over empirical types. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_apply_eq_sum
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteStateMarkovJumpPositiveReplicaFamily State)}
    (hEvent : MeasurableSet event) :
    finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration event =
      ∑ empiricalType,
        finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
            empiricalType generator duration hDuration event *
          initialEmpiricalTypeLaw {empiricalType} := by
  rw [finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_apply
    successorIndex initialEmpiricalTypeLaw generator duration hDuration hEvent]
  exact lintegral_fintype _

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Exact finite atomic decomposition of the mixed microscopic law. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw_eq_sum_smul
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration =
      Measure.sum fun empiricalType ↦
        initialEmpiricalTypeLaw {empiricalType} •
          finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw
            empiricalType generator duration hDuration := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
  rw [Measure.comp_eq_sum_of_countable]
  rfl

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Initial-density observation maps the microscopic conditional kernel to the deterministic
empirical-type density kernel. -/
theorem map_initialDensity_finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
    (successorIndex : ℕ) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    Kernel.map
        (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
          successorIndex generator duration hDuration)
        finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation =
      Kernel.deterministic
        (FiniteIIDPositiveEmpiricalType.probabilityDensity :
          FiniteIIDPositiveEmpiricalType State successorIndex →
            FiniteStateProbabilityDensity State)
        (measurable_of_finite _) := by
  ext1 empiricalType
  rw [Kernel.map_apply _
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation,
    Kernel.deterministic_apply]
  exact
    map_initialDensity_finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyLaw_eq_dirac
      empiricalType generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The mixed microscopic law has exactly the simplex law induced by its empirical count-type
mixing measure. -/
theorem map_initialDensity_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation
        (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration) =
      Measure.map
        (FiniteIIDPositiveEmpiricalType.probabilityDensity :
          FiniteIIDPositiveEmpiricalType State successorIndex →
            FiniteStateProbabilityDensity State)
        initialEmpiricalTypeLaw := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
  rw [Measure.map_comp initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)
    measurable_finiteStateMarkovJumpPositiveReplicaFamilyInitialDensityObservation]
  rw [map_initialDensity_finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel]
  exact Measure.deterministic_comp_eq_map (measurable_of_finite _)

/-- Conditional hybrid-BV observation law associated with one exact empirical count type. -/
noncomputable def finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
    (successorIndex : ℕ) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    Kernel (FiniteIIDPositiveEmpiricalType State successorIndex)
      (FiniteIntervalHybridBVPath
        (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  Kernel.map
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)
    (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)

/-- Evaluation of the hybrid conditional kernel is the canonical empirical-type observation
law. -/
@[simp]
theorem finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel_apply
    (successorIndex : ℕ)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
        successorIndex generator duration hDuration empiricalType =
      finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
        empiricalType generator duration hDuration := by
  rw [finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel,
    Kernel.map_apply _
      (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)]
  rfl

/-- The empirical-type-indexed hybrid conditional law is a Markov kernel. -/
instance instIsMarkovKernelFiniteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
    (successorIndex : ℕ) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    IsMarkovKernel
      (finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
        successorIndex generator duration hDuration) :=
  Kernel.IsMarkovKernel.map
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)

/-- Hybrid-BV observation law obtained by mixing the canonical conditional law over a random
exact empirical count type. -/
noncomputable def finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
      successorIndex generator duration hDuration ∘ₘ
    initialEmpiricalTypeLaw

/-- A probability law on empirical count types produces a normalized mixed hybrid law. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_isProbabilityMeasure
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
  infer_instance

/-- Mixing and total hybrid-BV observation commute exactly. -/
theorem map_hybridBVObservation_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure.map
        (finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)
        (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration) =
      finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
    finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
    finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
  exact Measure.map_comp initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)
    (measurable_finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservation duration)

/-- Exact eventwise disintegration of the mixed hybrid law over its empirical type. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hEvent : MeasurableSet event) :
    finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration event =
      ∫⁻ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
          empiricalType generator duration hDuration event ∂initialEmpiricalTypeLaw := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
  rw [Measure.bind_apply hEvent (Kernel.aemeasurable _)]
  simp only [finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel_apply]

/-- The eventwise hybrid disintegration is an ordinary finite sum over empirical types. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply_eq_sum
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    {event : Set (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration)}
    (hEvent : MeasurableSet event) :
    finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration event =
      ∑ empiricalType,
        finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
            empiricalType generator duration hDuration event *
          initialEmpiricalTypeLaw {empiricalType} := by
  rw [finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply
    successorIndex initialEmpiricalTypeLaw generator duration hDuration hEvent]
  exact lintegral_fintype _

/-- Exact finite atomic decomposition of the mixed hybrid-BV observation law. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_eq_sum_smul
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration =
      Measure.sum fun empiricalType ↦
        initialEmpiricalTypeLaw {empiricalType} •
          finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
            empiricalType generator duration hDuration := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
  rw [Measure.comp_eq_sum_of_countable]
  simp only [finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel_apply]

/-- Joint empirical-type/history law retaining the mixing type and its conditional microscopic
source on one carrier. -/
noncomputable def finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIIDPositiveEmpiricalType State successorIndex ×
      FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  initialEmpiricalTypeLaw ⊗ₘ
    finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The joint empirical-type/history law is normalized whenever the mixing type law is. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw_isProbabilityMeasure
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
  infer_instance

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The first marginal of the joint source is exactly the supplied empirical count-type law. -/
theorem fst_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [_unusedInitialEmpiricalTypeLawProbability : IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).fst =
        initialEmpiricalTypeLaw := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
  exact Measure.fst_compProd initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- The second marginal of the joint source is exactly the mixed common-carrier history law. -/
theorem snd_finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [_unusedInitialEmpiricalTypeLawProbability : IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).snd =
        finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyJointLaw
    finiteStateMarkovJumpRandomEmpiricalTypePositiveReplicaFamilyLaw
  exact Measure.snd_compProd initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypePositiveReplicaFamilyKernel
      successorIndex generator duration hDuration)

/-- Joint empirical-type/hybrid-path law retaining the exact finite mixing type beside its
conditional macroscopic observation. -/
noncomputable def finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteIIDPositiveEmpiricalType State successorIndex ×
      FiniteIntervalHybridBVPath
        (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  initialEmpiricalTypeLaw ⊗ₘ
    finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
      successorIndex generator duration hDuration

/-- The empirical-type/hybrid-path joint law is normalized whenever the mixing law is. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw_isProbabilityMeasure
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
  infer_instance

/-- The first marginal of the empirical-type/hybrid-path joint law is the supplied type law. -/
theorem fst_finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [_unusedInitialEmpiricalTypeLawProbability : IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).fst =
        initialEmpiricalTypeLaw := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
  exact Measure.fst_compProd initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
      successorIndex generator duration hDuration)

/-- The second marginal of the empirical-type/hybrid-path joint law is the mixed hybrid law. -/
theorem snd_finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [_unusedInitialEmpiricalTypeLawProbability : IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).snd =
        finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration := by
  unfold finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
    finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
  exact Measure.snd_compProd initialEmpiricalTypeLaw
    (finiteStateMarkovJumpEmpiricalTypeHybridBVObservationKernel
      successorIndex generator duration hDuration)

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- Measurable projection from the finite empirical type to its probability-density coordinate,
retaining the observed hybrid path. -/
theorem measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
    (successorIndex : ℕ) (duration : ℝ) :
    Measurable fun source : FiniteIIDPositiveEmpiricalType State successorIndex ×
        FiniteIntervalHybridBVPath
          (EmpiricalDensityDirectionalFlowCoordinate State) duration =>
      (source.1.probabilityDensity, source.2) := by
  have hDensity : Measurable
      (FiniteIIDPositiveEmpiricalType.probabilityDensity :
        FiniteIIDPositiveEmpiricalType State successorIndex →
          FiniteStateProbabilityDensity State) :=
    measurable_of_finite _
  exact (hDensity.comp measurable_fst).prodMk measurable_snd

/-- Joint probability-density/hybrid-path law obtained without choosing a representative of an
empirical count type. -/
noncomputable def finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    Measure (FiniteStateProbabilityDensity State ×
      FiniteIntervalHybridBVPath
        (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  Measure.map
    (fun source => (source.1.probabilityDensity, source.2))
    (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration)

/-- The density/hybrid-path joint law is normalized whenever the mixing type law is. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_isProbabilityMeasure
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) := by
  let := finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw_isProbabilityMeasure
    successorIndex initialEmpiricalTypeLaw generator duration hDuration
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
      successorIndex duration).aemeasurable).mpr inferInstance

/-- The first marginal of the density/hybrid-path joint law is exactly the density pushforward of
the supplied empirical-type law. -/
theorem fst_finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).fst =
        Measure.map
          (FiniteIIDPositiveEmpiricalType.probabilityDensity :
            FiniteIIDPositiveEmpiricalType State successorIndex →
              FiniteStateProbabilityDensity State)
          initialEmpiricalTypeLaw := by
  have hPair :=
    measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
      (State := State) successorIndex duration
  have hDensity : Measurable
      (FiniteIIDPositiveEmpiricalType.probabilityDensity :
        FiniteIIDPositiveEmpiricalType State successorIndex →
          FiniteStateProbabilityDensity State) :=
    measurable_of_finite _
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw Measure.fst
  rw [Measure.map_map measurable_fst hPair]
  change Measure.map
      (FiniteIIDPositiveEmpiricalType.probabilityDensity ∘ Prod.fst)
      (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) = _
  rw [← Measure.map_map hDensity measurable_fst]
  change Measure.map _
      (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration).fst = _
  rw [fst_finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw]

/-- The second marginal of the density/hybrid-path joint law is exactly the mixed hybrid
observation law. -/
theorem snd_finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) :
    (finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).snd =
        finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw
          successorIndex initialEmpiricalTypeLaw generator duration hDuration := by
  have hPair :=
    measurable_finiteIIDPositiveEmpiricalTypeProbabilityDensity_prod_snd
      (State := State) successorIndex duration
  unfold finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw Measure.snd
  rw [Measure.map_map measurable_snd hPair]
  change Measure.map Prod.snd
      (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
        successorIndex initialEmpiricalTypeLaw generator duration hDuration) = _
  change
    (finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw
      successorIndex initialEmpiricalTypeLaw generator duration hDuration).snd = _
  rw [snd_finiteStateMarkovJumpRandomEmpiricalTypeHybridBVJointLaw]

end

end FiniteMarkovProcesses.Probability
