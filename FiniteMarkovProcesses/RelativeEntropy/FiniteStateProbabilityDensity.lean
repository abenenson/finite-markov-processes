/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Probability densities on a finite state space

This module supplies the generic finite probability simplex used by finite-alphabet information
theory and finite-state large deviations.  Its topology is the ordinary coordinatewise topology,
and its measurable space is exactly the corresponding Borel sigma algebra.

## Main declarations

- `FiniteStateProbabilityDensity`: a nonnegative finite coordinate family of total mass one.
- `FiniteStateProbabilityDensity.probabilityMassFunction`: the exact finite PMF adapter.
- `FiniteStateProbabilityDensity.IsInterior`: strict positivity in every coordinate.
- `FiniteStateProbabilityDensity.IsOnLowerBoundary`: at least one zero coordinate.
- `FiniteStateProbabilityDensity.TendstoCoordinatewise`: coordinatewise sequential convergence.
- `FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise`: topology adapter for nets.
- `FiniteStateProbabilityDensity.InitialRateIsLeftContinuousAtLowerBoundary`: the boundary
  continuity contract used by finite-state initial-rate large deviations.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open scoped BigOperators ENNReal NNReal

universe u

/-- A probability density on a finite state space, kept as a typed simplex point rather than an
unconstrained coordinate function. -/
structure FiniteStateProbabilityDensity (State : Type u) [Fintype State] where
  /-- Nonnegative weight at each state of the finite probability density. -/
  weight : State → NNReal
  /-- The finite coordinate weights sum to one. -/
  sum_weight : ∑ state, weight state = 1

/-- The finite simplex inherits its ordinary coordinatewise topology. -/
instance instTopologicalSpaceFiniteStateProbabilityDensity
    (State : Type u) [Fintype State] :
    TopologicalSpace (FiniteStateProbabilityDensity State) :=
  TopologicalSpace.induced FiniteStateProbabilityDensity.weight inferInstance

/-- The finite simplex uses exactly the Borel sigma algebra of its coordinatewise topology. -/
instance instMeasurableSpaceFiniteStateProbabilityDensity
    (State : Type u) [Fintype State] :
    MeasurableSpace (FiniteStateProbabilityDensity State) :=
  borel (FiniteStateProbabilityDensity State)

/-- The simplex measurable structure is its coordinatewise Borel structure. -/
instance instBorelSpaceFiniteStateProbabilityDensity
    (State : Type u) [Fintype State] :
    BorelSpace (FiniteStateProbabilityDensity State) :=
  ⟨rfl⟩

namespace FiniteStateProbabilityDensity

variable {State : Type u} [Fintype State]

/-- Finite probability densities are equal exactly when every coordinate agrees. -/
@[ext]
theorem ext {first second : FiniteStateProbabilityDensity State}
    (hWeight : ∀ state, first.weight state = second.weight state) :
    first = second := by
  cases first
  cases second
  simp only [mk.injEq]
  funext state
  exact hWeight state

attribute [inherit_doc FiniteMarkovProcesses.InformationTheory.FiniteStateProbabilityDensity.ext]
  FiniteMarkovProcesses.InformationTheory.FiniteStateProbabilityDensity.ext_iff

/-- The complete coordinate family is continuous on the finite simplex. -/
theorem continuous_weight :
    Continuous fun density : FiniteStateProbabilityDensity State => density.weight :=
  continuous_induced_dom

/-- The coordinatewise simplex topology is Hausdorff because the complete weight family is
injective. -/
instance instT2Space : T2Space (FiniteStateProbabilityDensity State) :=
  T2Space.of_injective_continuous
    (fun _first _second hWeight => ext fun state => congrFun hWeight state)
    continuous_weight

/-- Evaluation at one finite-state coordinate is continuous on the simplex. -/
theorem continuous_weight_apply (state : State) :
    Continuous fun density : FiniteStateProbabilityDensity State => density.weight state :=
  (_root_.continuous_apply state).comp continuous_weight

/-- Evaluation at one finite-state coordinate is Borel measurable. -/
theorem measurable_weight_apply (state : State) :
    Measurable fun density : FiniteStateProbabilityDensity State => density.weight state :=
  (continuous_weight_apply state).measurable

/-- Real coordinate family underlying a finite probability density.  This is the closed-simplex
embedding used when a whole-carrier observable need not itself return a typed simplex point. -/
def realWeight (density : FiniteStateProbabilityDensity State) : State → ℝ :=
  fun state => density.weight state

/-- The real coordinate-family embedding of the finite simplex is continuous. -/
theorem continuous_realWeight :
    Continuous fun density : FiniteStateProbabilityDensity State => density.realWeight := by
  apply continuous_pi
  intro state
  exact NNReal.continuous_coe.comp (continuous_weight_apply state)

/-- The real coordinate-family embedding retains every finite probability density exactly. -/
theorem injective_realWeight :
    Function.Injective (realWeight : FiniteStateProbabilityDensity State → State → ℝ) := by
  intro first second hWeight
  apply ext
  intro state
  apply NNReal.eq
  exact congrFun hWeight state

/-- Convergence in the induced finite-simplex topology is exactly coordinatewise convergence.
The statement is filter-generic so it can be reused for sequences and nets. -/
theorem tendsto_iff_tendstoCoordinatewise
    {Index : Type*} {net : Index → FiniteStateProbabilityDensity State}
    {filter : Filter Index} {density : FiniteStateProbabilityDensity State} :
    Filter.Tendsto net filter (nhds density) ↔
      ∀ state, Filter.Tendsto (fun index => (net index).weight state) filter
        (nhds (density.weight state)) := by
  rw [(Topology.IsInducing.induced
    (FiniteStateProbabilityDensity.weight :
      FiniteStateProbabilityDensity State → State → NNReal)).tendsto_nhds_iff,
    tendsto_pi_nhds]
  rfl

/-- Every coordinate of a finite probability density is at most one. -/
theorem weight_le_one (density : FiniteStateProbabilityDensity State) (state : State) :
    density.weight state ≤ 1 := by
  calc
    density.weight state ≤ ∑ candidate, density.weight candidate :=
      Finset.single_le_sum
        (fun candidate _hCandidate => (zero_le : 0 ≤ density.weight candidate))
        (Finset.mem_univ state)
    _ = 1 := density.sum_weight

/-- The closed finite probability simplex is compact in its coordinatewise topology. -/
instance instCompactSpace : CompactSpace (FiniteStateProbabilityDensity State) where
  isCompact_univ := by
    have hInducing : Topology.IsInducing
        (FiniteStateProbabilityDensity.weight :
          FiniteStateProbabilityDensity State → State → NNReal) :=
      Topology.IsInducing.induced _
    rw [hInducing.isCompact_iff, Set.image_univ]
    have hRangeClosed : IsClosed
        (Set.range (FiniteStateProbabilityDensity.weight :
          FiniteStateProbabilityDensity State → State → NNReal)) := by
      have hRange :
          Set.range (FiniteStateProbabilityDensity.weight :
            FiniteStateProbabilityDensity State → State → NNReal) =
            {weight | ∑ state, weight state = 1} := by
        ext weight
        constructor
        · rintro ⟨density, rfl⟩
          exact density.sum_weight
        · intro hWeight
          exact ⟨⟨weight, hWeight⟩, rfl⟩
      rw [hRange]
      exact isClosed_eq
        (continuous_finsetSum _ fun state _hState => continuous_apply state)
        continuous_const
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _state : State =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) 1)))
      hRangeClosed
    rintro _weight ⟨density, rfl⟩ state _hState
    exact ⟨(zero_le : 0 ≤ density.weight state), density.weight_le_one state⟩

/-- Exact probability mass function represented by a finite probability density. -/
noncomputable def probabilityMassFunction
    (density : FiniteStateProbabilityDensity State) : PMF State :=
  PMF.ofFintype (fun state => (density.weight state : ENNReal)) (by
    rw [← ENNReal.ofNNReal_finsetSum, density.sum_weight]
    simp)

/-- The PMF adapter preserves every finite-simplex coordinate exactly. -/
@[simp]
theorem probabilityMassFunction_apply
    (density : FiniteStateProbabilityDensity State) (state : State) :
    density.probabilityMassFunction state = (density.weight state : ENNReal) :=
  rfl

/-- Every coordinate is strictly positive, i.e. the density is in the simplex interior. -/
def IsInterior (density : FiniteStateProbabilityDensity State) : Prop :=
  ∀ state, 0 < density.weight state

/-- At least one coordinate vanishes, i.e. the density lies on the simplex's lower boundary. -/
def IsOnLowerBoundary (density : FiniteStateProbabilityDensity State) : Prop :=
  ∃ state, density.weight state = 0

/-- Coordinatewise convergence of finite-state probability densities. -/
def TendstoCoordinatewise (sequence : ℕ → FiniteStateProbabilityDensity State)
    (limit : FiniteStateProbabilityDensity State) : Prop :=
  ∀ state, Filter.Tendsto (fun sampleSize => (sequence sampleSize).weight state)
    Filter.atTop (nhds (limit.weight state))

/-- Sequential continuity of an initial rate when a boundary density is approached from the
strictly positive simplex interior. -/
def InitialRateIsLeftContinuousAtLowerBoundary
    (initialRate : FiniteStateProbabilityDensity State → ENNReal) : Prop :=
  ∀ boundaryDensity, boundaryDensity.IsOnLowerBoundary →
    ∀ sequence, (∀ sampleSize, (sequence sampleSize).IsInterior) →
      TendstoCoordinatewise sequence boundaryDensity →
        Filter.Tendsto (fun sampleSize => initialRate (sequence sampleSize))
          Filter.atTop (nhds (initialRate boundaryDensity))

end FiniteStateProbabilityDensity

end FiniteMarkovProcesses.InformationTheory
