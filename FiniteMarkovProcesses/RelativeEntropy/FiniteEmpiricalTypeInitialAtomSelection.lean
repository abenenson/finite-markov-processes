/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpRengerEmpiricalInitialSource

/-!
# Maximum-mass finite empirical initial types

This module supplies the finite combinatorial bridge between an initial law on the probability
simplex and the exact empirical count-type carrier that generates the microscopic replica source.
For one simplex event it selects a count type of maximum singleton mass among precisely the types
whose empirical density belongs to that event.  The event mass is bounded by the polynomial
ambient type count times the selected atom.

The selection is finite-sample and source-neutral.  It does not assert an asymptotic atom lower
bound, choose an off-lattice density, or identify a path large-deviation rate.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State] [Nonempty State]

/-- Strictly increasing cumulative majorant of an arbitrary natural-number cutoff schedule. -/
def finiteEmpiricalTypeDiagonalCumulativeCutoff (cutoff : ℕ → ℕ) : ℕ → ℕ
  | 0 => cutoff 0
  | stage + 1 =>
      max (finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff stage + 1) (cutoff (stage + 1))

/-- Every raw cutoff is bounded by its cumulative majorant at the same stage. -/
theorem cutoff_le_finiteEmpiricalTypeDiagonalCumulativeCutoff
    (cutoff : ℕ → ℕ) (stage : ℕ) :
    cutoff stage ≤ finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff stage := by
  cases stage with
  | zero => rfl
  | succ stage =>
      rw [finiteEmpiricalTypeDiagonalCumulativeCutoff]
      exact le_max_right _ _

/-- The cumulative cutoff schedule is strictly increasing. -/
theorem strictMono_finiteEmpiricalTypeDiagonalCumulativeCutoff
    (cutoff : ℕ → ℕ) :
    StrictMono (finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff) := by
  apply strictMono_nat_of_lt_succ
  intro stage
  rw [finiteEmpiricalTypeDiagonalCumulativeCutoff]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

/-- Largest admissible diagonal stage whose cumulative cutoff has already been reached. -/
def finiteEmpiricalTypeDiagonalStage (cutoff : ℕ → ℕ) (successorIndex : ℕ) : ℕ :=
  Nat.findGreatest
    (fun stage ↦ finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff stage ≤ successorIndex)
    successorIndex

/-- Every fixed stage is eventually dominated by the diagonal stage. -/
theorem finiteEmpiricalTypeDiagonalStage_tendsto_atTop (cutoff : ℕ → ℕ) :
    Filter.Tendsto (finiteEmpiricalTypeDiagonalStage cutoff) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro stage
  filter_upwards
      [Filter.eventually_ge_atTop
        (max stage (finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff stage))] with
      successorIndex hSuccessorIndex
  apply Nat.le_findGreatest
  · exact (le_max_left _ _).trans hSuccessorIndex
  · exact (le_max_right _ _).trans hSuccessorIndex

/-- Eventually, the raw cutoff requested by the selected diagonal stage has been reached. -/
theorem eventually_cutoff_finiteEmpiricalTypeDiagonalStage_le
    (cutoff : ℕ → ℕ) :
    ∀ᶠ successorIndex in Filter.atTop,
      cutoff (finiteEmpiricalTypeDiagonalStage cutoff successorIndex) ≤ successorIndex := by
  filter_upwards
      [Filter.eventually_ge_atTop
        (finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff 0)] with
      successorIndex hSuccessorIndex
  refine (cutoff_le_finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff _).trans ?_
  unfold finiteEmpiricalTypeDiagonalStage
  exact Nat.findGreatest_spec
    (P := fun stage ↦
      finiteEmpiricalTypeDiagonalCumulativeCutoff cutoff stage ≤ successorIndex)
    (m := 0) (n := successorIndex) (Nat.zero_le successorIndex) hSuccessorIndex

/-- Shrinking coordinate box about one finite probability density. -/
def finiteStateProbabilityDensityCoordinateNeighborhood
    (target : FiniteStateProbabilityDensity State) (stage : ℕ) :
    Set (FiniteStateProbabilityDensity State) :=
  {density | ∀ state,
    dist (density.weight state) (target.weight state) < 1 / ((stage : ℝ) + 1)}

omit [DecidableEq State] [Nonempty State] in
/-- Every coordinate box in the canonical shrinking family is open. -/
theorem isOpen_finiteStateProbabilityDensityCoordinateNeighborhood
    (target : FiniteStateProbabilityDensity State) (stage : ℕ) :
    IsOpen (finiteStateProbabilityDensityCoordinateNeighborhood target stage) := by
  rw [finiteStateProbabilityDensityCoordinateNeighborhood, ofPred_forall]
  apply isOpen_iInter_of_finite
  intro state
  exact isOpen_lt
    ((FiniteStateProbabilityDensity.continuous_weight_apply state).dist continuous_const)
    continuous_const

omit [DecidableEq State] [Nonempty State] in
/-- The center belongs to every coordinate box in its shrinking family. -/
theorem mem_finiteStateProbabilityDensityCoordinateNeighborhood
    (target : FiniteStateProbabilityDensity State) (stage : ℕ) :
    target ∈ finiteStateProbabilityDensityCoordinateNeighborhood target stage := by
  intro state
  simp only [dist_self]
  positivity

omit [DecidableEq State] [Nonempty State] in
/-- Membership in coordinate boxes whose stages diverge forces coordinatewise convergence to
their common center. -/
theorem tendstoCoordinatewise_of_mem_finiteStateProbabilityDensityCoordinateNeighborhood
    (target : FiniteStateProbabilityDensity State)
    (stage : ℕ → ℕ) (density : ℕ → FiniteStateProbabilityDensity State)
    (hStage : Filter.Tendsto stage Filter.atTop Filter.atTop)
    (hDensity : ∀ᶠ successorIndex in Filter.atTop,
      density successorIndex ∈
        finiteStateProbabilityDensityCoordinateNeighborhood
          target (stage successorIndex)) :
    FiniteStateProbabilityDensity.TendstoCoordinatewise density target := by
  intro state
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _successorIndex ↦ dist_nonneg
  · exact hDensity.mono fun _successorIndex hSuccessorIndex ↦
      (hSuccessorIndex state).le
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hStage

/-- Exact count types whose associated finite-simplex point belongs to one event. -/
noncomputable def finiteIIDPositiveEmpiricalTypesInDensitySet
    (successorIndex : ℕ) (event : Set (FiniteStateProbabilityDensity State)) :
    Finset (FiniteIIDPositiveEmpiricalType State successorIndex) := by
  classical
  exact Finset.univ.filter fun empiricalType ↦ empiricalType.probabilityDensity ∈ event

/-- Canonical fallback count type, used only when a selected density event contains no empirical
lattice point at the requested particle count. -/
def finiteIIDPositiveEmpiricalTypeFallback
    (successorIndex : ℕ) : FiniteIIDPositiveEmpiricalType State successorIndex :=
  finiteIIDPositiveSampleEmpiricalType successorIndex fun _replica ↦ Classical.choice inferInstance

/-- A maximum-singleton-mass count type among the exact empirical types in one density event.
When the finite event is empty the value is the explicit fallback type. -/
noncomputable def finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (event : Set (FiniteStateProbabilityDensity State)) :
    FiniteIIDPositiveEmpiricalType State successorIndex := by
  classical
  let candidates := finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event
  exact if hCandidates : candidates.Nonempty then
    Classical.choose
      (Finset.exists_max_image candidates
        (fun empiricalType ↦ initialEmpiricalTypeLaw {empiricalType}) hCandidates)
  else finiteIIDPositiveEmpiricalTypeFallback successorIndex

/-- Whenever the density event contains an empirical lattice point, its selected maximum-mass
type belongs to the event. -/
theorem finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet_probabilityDensity_mem
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (event : Set (FiniteStateProbabilityDensity State))
    (hNonempty : ∃ empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex,
      empiricalType.probabilityDensity ∈ event) :
    (finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
        successorIndex initialEmpiricalTypeLaw event).probabilityDensity ∈ event := by
  classical
  have hCandidates :
      (finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event).Nonempty := by
    obtain ⟨empiricalType, hEmpiricalType⟩ := hNonempty
    exact ⟨empiricalType, by
      simp [finiteIIDPositiveEmpiricalTypesInDensitySet, hEmpiricalType]⟩
  unfold finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
  rw [dite_eq_left hCandidates]
  have hSelected :=
    (Classical.choose_spec
      (Finset.exists_max_image
        (finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event)
        (fun empiricalType ↦ initialEmpiricalTypeLaw {empiricalType}) hCandidates)).1
  simpa [finiteIIDPositiveEmpiricalTypesInDensitySet] using hSelected

/-- The selected atom dominates every other empirical-type atom whose density lies in the same
event. -/
theorem finiteIIDPositiveEmpiricalType_singleton_le_maximumMassInDensitySet_singleton
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    (event : Set (FiniteStateProbabilityDensity State))
    (hNonempty : ∃ empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex,
      empiricalType.probabilityDensity ∈ event)
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (hEmpiricalType : empiricalType.probabilityDensity ∈ event) :
    initialEmpiricalTypeLaw {empiricalType} ≤
      initialEmpiricalTypeLaw
        {finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
          successorIndex initialEmpiricalTypeLaw event} := by
  classical
  have hCandidates :
      (finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event).Nonempty := by
    obtain ⟨candidate, hCandidate⟩ := hNonempty
    exact ⟨candidate, by
      simp [finiteIIDPositiveEmpiricalTypesInDensitySet, hCandidate]⟩
  unfold finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
  rw [dite_eq_left hCandidates]
  exact
    (Classical.choose_spec
      (Finset.exists_max_image
        (finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event)
        (fun candidate ↦ initialEmpiricalTypeLaw {candidate}) hCandidates)).2
      empiricalType (by
        simp [finiteIIDPositiveEmpiricalTypesInDensitySet, hEmpiricalType])

/-- The simplex-event mass is at most the polynomial ambient count of empirical types times the
selected in-event singleton mass.  The statement uses the exact pushforward law. -/
theorem map_probabilityDensity_apply_le_card_mul_maximumMassInDensitySet_singleton
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    {event : Set (FiniteStateProbabilityDensity State)}
    (hEvent : MeasurableSet event)
    (hNonempty : ∃ empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex,
      empiricalType.probabilityDensity ∈ event) :
    Measure.map FiniteIIDPositiveEmpiricalType.probabilityDensity
        initialEmpiricalTypeLaw event ≤
      (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
        initialEmpiricalTypeLaw
          {finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
            successorIndex initialEmpiricalTypeLaw event} := by
  classical
  let candidates := finiteIIDPositiveEmpiricalTypesInDensitySet successorIndex event
  let selected := finiteIIDPositiveEmpiricalTypeMaximumMassInDensitySet
    successorIndex initialEmpiricalTypeLaw event
  have hCandidateBound : ∀ empiricalType ∈ candidates,
      initialEmpiricalTypeLaw {empiricalType} ≤ initialEmpiricalTypeLaw {selected} := by
    intro empiricalType hEmpiricalType
    apply finiteIIDPositiveEmpiricalType_singleton_le_maximumMassInDensitySet_singleton
      successorIndex initialEmpiricalTypeLaw event hNonempty empiricalType
    simpa only [candidates, finiteIIDPositiveEmpiricalTypesInDensitySet,
      Finset.mem_filter, Finset.mem_univ, true_and] using hEmpiricalType
  calc
    Measure.map FiniteIIDPositiveEmpiricalType.probabilityDensity
        initialEmpiricalTypeLaw event =
        initialEmpiricalTypeLaw
          (FiniteIIDPositiveEmpiricalType.probabilityDensity ⁻¹' event) := by
      rw [Measure.map_apply (measurable_of_finite _) hEvent]
    _ = ∑ empiricalType ∈ candidates,
        initialEmpiricalTypeLaw {empiricalType} := by
      rw [sum_measure_singleton]
      congr 1
      ext empiricalType
      simp [candidates, finiteIIDPositiveEmpiricalTypesInDensitySet]
    _ ≤ candidates.card • initialEmpiricalTypeLaw {selected} :=
      Finset.sum_le_card_nsmul candidates
        (fun empiricalType ↦ initialEmpiricalTypeLaw {empiricalType})
        (initialEmpiricalTypeLaw {selected}) hCandidateBound
    _ = (candidates.card : ENNReal) * initialEmpiricalTypeLaw {selected} := by
      simp only [nsmul_eq_mul]
    _ ≤ (Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) : ENNReal) *
        initialEmpiricalTypeLaw {selected} := by
      gcongr
      simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ candidates

end

end FiniteMarkovProcesses.InformationTheory
