/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteBidirectionalPoissonCurrentContraction

/-!
# Finite oriented Poisson graph dynamics

This file supplies the finite graph structure needed to interpret edgewise bidirectional Poisson
current contractions as density dynamics.  A graph fixes one orientation per reversible edge.  A
positive generator and positive vertex density generate both directional reference flows, their
source net currents, and the conservative density velocity `-div current`.

The summed current action vanishes exactly at every source edge current.  Combined with the
continuity equation, this selects the literal forward density velocity.  Reversing every edge
orientation, directional rate, and current preserves both the action and density velocity.

These are exact finite graph identities.  The file does not assert a particle system, graph-edge
independence, a path-space large-deviation principle, or a continuum field limit.

## Main results

- `FiniteOrientedGraph.sum_densityVelocity_eq_zero`: exact mass conservation.
- `FiniteOrientedPoissonGenerator.currentAction_eq_zero_iff`: zero action exactly at source
  currents.
- `FiniteOrientedPoissonGenerator.zeroAction_continuityEquation_iff`: exact zero-cost forward
  density dynamics.
- `FiniteOrientedPoissonGenerator.reverseOrientation_currentAction`: orientation covariance.
- `sharedVertexGraph_densityVelocity_center_ne_firstEdgeOnly`: adverse shared-density control.
-/

namespace FiniteMarkovProcesses.InformationTheory

open scoped BigOperators

universe u v

/-- One chosen orientation for every edge of a finite graph.  Finiteness is supplied by the
consumer's `Fintype` instances. -/
structure FiniteOrientedGraph (Vertex : Type u) (Edge : Type v) where
  /-- Supplied tail vertex of each edge in the chosen orientation. -/
  tail : Edge → Vertex
  /-- Supplied head vertex of each edge in the chosen orientation. -/
  head : Edge → Vertex

namespace FiniteOrientedGraph

variable {Vertex : Type u} {Edge : Type v}
  [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]

/-- Signed outgoing-minus-incoming divergence of a net edge current. -/
def divergence (graph : FiniteOrientedGraph Vertex Edge)
    (edgeCurrent : Edge → ℝ) (vertex : Vertex) : ℝ :=
  (∑ edge, if graph.tail edge = vertex then edgeCurrent edge else 0) -
    ∑ edge, if graph.head edge = vertex then edgeCurrent edge else 0

/-- Density velocity selected by a net edge current through the continuity equation. -/
def densityVelocity (graph : FiniteOrientedGraph Vertex Edge)
    (edgeCurrent : Edge → ℝ) (vertex : Vertex) : ℝ :=
  -graph.divergence edgeCurrent vertex

/-- A density derivative satisfies the graph continuity equation exactly when it is `-div` of the
named edge-current family. -/
def SatisfiesContinuityEquation (graph : FiniteOrientedGraph Vertex Edge)
    (densityDerivative : Vertex → ℝ) (edgeCurrent : Edge → ℝ) : Prop :=
  densityDerivative = graph.densityVelocity edgeCurrent

/-- Every finite oriented current gives a mass-conserving density velocity. -/
theorem sum_densityVelocity_eq_zero
    (graph : FiniteOrientedGraph Vertex Edge) (edgeCurrent : Edge → ℝ) :
    ∑ vertex, graph.densityVelocity edgeCurrent vertex = 0 := by
  have hTail :
      (∑ vertex, ∑ edge,
        if graph.tail edge = vertex then edgeCurrent edge else 0) =
        ∑ edge, edgeCurrent edge := by
    rw [Finset.sum_comm]
    simp
  have hHead :
      (∑ vertex, ∑ edge,
        if graph.head edge = vertex then edgeCurrent edge else 0) =
        ∑ edge, edgeCurrent edge := by
    rw [Finset.sum_comm]
    simp
  unfold densityVelocity divergence
  simp_rw [neg_sub]
  rw [Finset.sum_sub_distrib, hHead, hTail]
  ring

/-- Reverse the chosen orientation of every edge. -/
def reverseOrientation (graph : FiniteOrientedGraph Vertex Edge) :
    FiniteOrientedGraph Vertex Edge where
  tail := graph.head
  head := graph.tail

omit [Fintype Vertex] in
/-- Reversing edge orientation and current together preserves density velocity. -/
theorem reverseOrientation_densityVelocity
    (graph : FiniteOrientedGraph Vertex Edge) (edgeCurrent : Edge → ℝ) :
    graph.reverseOrientation.densityVelocity (fun edge ↦ -edgeCurrent edge) =
      graph.densityVelocity edgeCurrent := by
  funext vertex
  have hHead :
      (∑ edge, if graph.head edge = vertex then -edgeCurrent edge else 0) =
        -(∑ edge, if graph.head edge = vertex then edgeCurrent edge else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    split <;> simp_all
  have hTail :
      (∑ edge, if graph.tail edge = vertex then -edgeCurrent edge else 0) =
        -(∑ edge, if graph.tail edge = vertex then edgeCurrent edge else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    split <;> simp_all
  unfold reverseOrientation densityVelocity divergence
  rw [hHead, hTail]
  ring

end FiniteOrientedGraph

/-- A finite oriented graph with strictly positive generator rates in both directions on every
edge. -/
structure FiniteOrientedPoissonGenerator (Vertex : Type u) (Edge : Type v)
    extends FiniteOrientedGraph Vertex Edge where
  /-- Supplied generator rate from the tail to the head of each oriented edge. -/
  forwardRate : Edge → ℝ
  /-- Supplied generator rate from the head to the tail of each oriented edge. -/
  reverseRate : Edge → ℝ
  /-- Supplied strict positivity of every forward generator rate. -/
  forwardRate_pos : ∀ edge, 0 < forwardRate edge
  /-- Supplied strict positivity of every reverse generator rate. -/
  reverseRate_pos : ∀ edge, 0 < reverseRate edge

namespace FiniteOrientedPoissonGenerator

variable {Vertex : Type u} {Edge : Type v}
  [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]

/-- Strict positivity of a vertex density. -/
def PositiveDensity (density : Vertex → ℝ) : Prop :=
  ∀ vertex, 0 < density vertex

/-- Directional expected edge flows generated at one positive vertex density. -/
def referenceRates (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edge : Edge) : BidirectionalPoissonRates where
  clockwise := density (generator.tail edge) * generator.forwardRate edge
  counterclockwise := density (generator.head edge) * generator.reverseRate edge

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] in
/-- Positive density and generator rates give positive directional edge flows. -/
theorem referenceRates_positive
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    {density : Vertex → ℝ} (hDensity : PositiveDensity density) (edge : Edge) :
    (generator.referenceRates density edge).Positive :=
  ⟨mul_pos (hDensity _) (generator.forwardRate_pos edge),
    mul_pos (hDensity _) (generator.reverseRate_pos edge)⟩

/-- Source net edge current generated by the positive density and directional generator. -/
def sourceEdgeCurrent (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edge : Edge) : ℝ :=
  density (generator.tail edge) * generator.forwardRate edge -
    density (generator.head edge) * generator.reverseRate edge

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] in
/-- The generated directional reference pair has the literal source edge current. -/
@[simp]
theorem referenceRates_current
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edge : Edge) :
    (generator.referenceRates density edge).current =
      generator.sourceEdgeCurrent density edge := rfl

/-- Summed directional-flow action relative to the generated edge references. -/
noncomputable def directionalFlowAction
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (directionalFlows : Edge → BidirectionalPoissonRates) : ℝ :=
  finiteBidirectionalPoissonDirectionalFlowAction
    (generator.referenceRates density) directionalFlows

/-- Summed current-contracted action relative to the generated edge references. -/
noncomputable def currentAction
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edgeCurrent : Edge → ℝ) : ℝ :=
  finiteBidirectionalPoissonCurrentAction
    (generator.referenceRates density) edgeCurrent

/-- Density velocity generated by the source edge currents. -/
def sourceDensityVelocity
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) : Vertex → ℝ :=
  generator.toFiniteOrientedGraph.densityVelocity
    (generator.sourceEdgeCurrent density)

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- The graph current action is nonnegative on every current family. -/
theorem currentAction_nonneg
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    {density : Vertex → ℝ} (hDensity : PositiveDensity density)
    (edgeCurrent : Edge → ℝ) :
    0 ≤ generator.currentAction density edgeCurrent := by
  exact finiteBidirectionalPoissonCurrentAction_nonneg
    (generator.referenceRates_positive hDensity) edgeCurrent

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- The graph current action vanishes exactly at the generated source current on every edge. -/
theorem currentAction_eq_zero_iff
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    {density : Vertex → ℝ} (hDensity : PositiveDensity density)
    (edgeCurrent : Edge → ℝ) :
    generator.currentAction density edgeCurrent = 0 ↔
      edgeCurrent = generator.sourceEdgeCurrent density := by
  exact finiteBidirectionalPoissonCurrentAction_eq_zero_iff
    (generator.referenceRates_positive hDensity) edgeCurrent

omit [Fintype Vertex] in
/-- Zero graph action plus the continuity equation is equivalent to the literal generated source
current and forward density velocity. -/
theorem zeroAction_continuityEquation_iff
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    {density : Vertex → ℝ} (hDensity : PositiveDensity density)
    (edgeCurrent : Edge → ℝ) (densityDerivative : Vertex → ℝ) :
    generator.currentAction density edgeCurrent = 0 ∧
        generator.toFiniteOrientedGraph.SatisfiesContinuityEquation
          densityDerivative edgeCurrent ↔
      edgeCurrent = generator.sourceEdgeCurrent density ∧
        densityDerivative = generator.sourceDensityVelocity density := by
  constructor
  · rintro ⟨hAction, hContinuity⟩
    have hCurrent := (generator.currentAction_eq_zero_iff
      hDensity edgeCurrent).mp hAction
    refine ⟨hCurrent, ?_⟩
    unfold FiniteOrientedGraph.SatisfiesContinuityEquation at hContinuity
    unfold sourceDensityVelocity
    simpa [hCurrent] using hContinuity
  · rintro ⟨hCurrent, hDerivative⟩
    constructor
    · exact (generator.currentAction_eq_zero_iff
        hDensity edgeCurrent).2 hCurrent
    · unfold FiniteOrientedGraph.SatisfiesContinuityEquation
      unfold sourceDensityVelocity at hDerivative
      simpa [hCurrent] using hDerivative

/-- The generated source density velocity conserves total mass. -/
theorem sum_sourceDensityVelocity_eq_zero
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) :
    ∑ vertex, generator.sourceDensityVelocity density vertex = 0 :=
  generator.toFiniteOrientedGraph.sum_densityVelocity_eq_zero _

/-- Reverse every chosen edge orientation and exchange its directional generator rates. -/
def reverseOrientation
    (generator : FiniteOrientedPoissonGenerator Vertex Edge) :
    FiniteOrientedPoissonGenerator Vertex Edge where
  tail := generator.head
  head := generator.tail
  forwardRate := generator.reverseRate
  reverseRate := generator.forwardRate
  forwardRate_pos := generator.reverseRate_pos
  reverseRate_pos := generator.forwardRate_pos

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] in
/-- Reversing generator orientation exchanges the generated directional reference flows. -/
@[simp]
theorem reverseOrientation_referenceRates
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edge : Edge) :
    (generator.reverseOrientation.referenceRates density edge) =
      (generator.referenceRates density edge).swap := rfl

omit [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] in
/-- Reversing generator orientation negates every generated source current. -/
@[simp]
theorem reverseOrientation_sourceEdgeCurrent
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) (edge : Edge) :
    generator.reverseOrientation.sourceEdgeCurrent density edge =
      -generator.sourceEdgeCurrent density edge := by
  unfold reverseOrientation sourceEdgeCurrent
  ring

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- Reversing generator orientation and the named currents preserves the complete finite graph
current action. -/
theorem reverseOrientation_currentAction
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    {density : Vertex → ℝ} (hDensity : PositiveDensity density)
    (edgeCurrent : Edge → ℝ) :
    generator.reverseOrientation.currentAction density
        (fun edge ↦ -edgeCurrent edge) =
      generator.currentAction density edgeCurrent := by
  unfold currentAction
  have hReferenceRates :
      generator.reverseOrientation.referenceRates density =
        fun edge ↦ (generator.referenceRates density edge).swap := by
    funext edge
    exact generator.reverseOrientation_referenceRates density edge
  rw [hReferenceRates]
  exact finiteBidirectionalPoissonCurrentAction_reversal
    (generator.referenceRates_positive hDensity) edgeCurrent

omit [Fintype Vertex] in
/-- Reversing generator orientation preserves the source density velocity. -/
theorem reverseOrientation_sourceDensityVelocity
    (generator : FiniteOrientedPoissonGenerator Vertex Edge)
    (density : Vertex → ℝ) :
    generator.reverseOrientation.sourceDensityVelocity density =
      generator.sourceDensityVelocity density := by
  unfold sourceDensityVelocity
  have hVelocity := generator.toFiniteOrientedGraph.reverseOrientation_densityVelocity
    (generator.sourceEdgeCurrent density)
  have hCurrent :
      generator.reverseOrientation.sourceEdgeCurrent density =
        fun edge ↦ -generator.sourceEdgeCurrent density edge := by
    funext edge
    exact generator.reverseOrientation_sourceEdgeCurrent density edge
  rw [hCurrent]
  exact hVelocity

end FiniteOrientedPoissonGenerator

/-- Two edges sharing one tail vertex, used to prevent independent-edge density updates from
silently violating the continuity equation. -/
def sharedVertexGraph : FiniteOrientedGraph (Fin 3) (Fin 2) where
  tail := fun _ ↦ 0
  head := fun edge ↦ if edge = 0 then 1 else 2

/-- The shared tail responds to the sum of both outgoing edge currents. -/
theorem sharedVertexGraph_densityVelocity_center (edgeCurrent : Fin 2 → ℝ) :
    sharedVertexGraph.densityVelocity edgeCurrent 0 =
      -(edgeCurrent 0 + edgeCurrent 1) := by
  simp [FiniteOrientedGraph.densityVelocity, FiniteOrientedGraph.divergence,
    sharedVertexGraph, Fin.sum_univ_two]

/-- Adverse shared-density control: when the second current is nonzero, updating the common tail
from the first edge alone is not the graph continuity equation. -/
theorem sharedVertexGraph_densityVelocity_center_ne_firstEdgeOnly
    (edgeCurrent : Fin 2 → ℝ) (hSecond : edgeCurrent 1 ≠ 0) :
    sharedVertexGraph.densityVelocity edgeCurrent 0 ≠ -edgeCurrent 0 := by
  rw [sharedVertexGraph_densityVelocity_center]
  intro hEqual
  apply hSecond
  linarith

end FiniteMarkovProcesses.InformationTheory
