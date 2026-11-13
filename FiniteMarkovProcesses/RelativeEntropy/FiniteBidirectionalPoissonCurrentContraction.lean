/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.BidirectionalPoissonCurrentContraction

/-!
# Finite-sector bidirectional Poisson current contraction

This file assembles the exact one-edge current contraction over an arbitrary finite sector type.
The finite directional-flow action splits into the contracted current action plus a sum of
nonnegative residual discriminations.  Equality therefore identifies every projected directional
flow, and zero current action identifies every source current.

The sector index does not assert graph independence, a continuity equation, or a microscopic
particle source.  Those structures require a separately typed finite-graph realization.

## Main results

- `finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_add_residual`: exact finite
  Pythagorean sum.
- `finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_iff`: literal projected-flow
  identification.
- `finiteBidirectionalPoissonCurrentAction_eq_zero_iff`: zero cost exactly at all source currents.
- `finiteBidirectionalPoissonCurrentAction_commonScale`: exact finite-sector extensivity.
- `finiteBidirectionalPoissonCurrentAction_fluctuationSymmetry`: summed time-odd sector.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open scoped BigOperators

universe u

variable {Edge : Type u} [Fintype Edge]

/-- Sum of exact directional-flow discriminations over a finite sector type. -/
noncomputable def finiteBidirectionalPoissonDirectionalFlowAction
    (referenceRates lawRates : Edge → BidirectionalPoissonRates) : ℝ :=
  ∑ edge, bidirectionalPoissonDiscrimination (lawRates edge) (referenceRates edge)

/-- Edgewise current-fibre projections for a finite family of prescribed currents. -/
noncomputable def finiteBidirectionalPoissonCurrentFibreProjection
    (referenceRates : Edge → BidirectionalPoissonRates) (netCurrents : Edge → ℝ) :
    Edge → BidirectionalPoissonRates :=
  fun edge ↦ currentFibreProjection (referenceRates edge) (netCurrents edge)

/-- Sum of exact current-contracted actions over a finite sector type. -/
noncomputable def finiteBidirectionalPoissonCurrentAction
    (referenceRates : Edge → BidirectionalPoissonRates) (netCurrents : Edge → ℝ) : ℝ :=
  ∑ edge, bidirectionalPoissonCurrentAction (referenceRates edge) (netCurrents edge)

omit [Fintype Edge] in
/-- Every finite projected directional flow is positive when every reference sector is positive. -/
theorem finiteBidirectionalPoissonCurrentFibreProjection_positive
    {referenceRates : Edge → BidirectionalPoissonRates}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) (edge : Edge) :
    (finiteBidirectionalPoissonCurrentFibreProjection referenceRates netCurrents edge).Positive :=
  currentFibreProjection_positive (hReference edge) (netCurrents edge)

omit [Fintype Edge] in
/-- Every finite projected directional flow has its prescribed current. -/
@[simp]
theorem finiteBidirectionalPoissonCurrentFibreProjection_current
    (referenceRates : Edge → BidirectionalPoissonRates) (netCurrents : Edge → ℝ)
    (edge : Edge) :
    (finiteBidirectionalPoissonCurrentFibreProjection
      referenceRates netCurrents edge).current = netCurrents edge :=
  currentFibreProjection_current _ _

/-- Exact finite-sector Pythagorean decomposition into contracted current action and residual
directional-flow discrimination. -/
theorem finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_add_residual
    {referenceRates lawRates : Edge → BidirectionalPoissonRates}
    {netCurrents : Edge → ℝ}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (hLaw : ∀ edge, (lawRates edge).Positive)
    (hCurrent : ∀ edge, (lawRates edge).current = netCurrents edge) :
    finiteBidirectionalPoissonDirectionalFlowAction referenceRates lawRates =
      finiteBidirectionalPoissonCurrentAction referenceRates netCurrents +
        ∑ edge, bidirectionalPoissonDiscrimination (lawRates edge)
          (finiteBidirectionalPoissonCurrentFibreProjection
            referenceRates netCurrents edge) := by
  unfold finiteBidirectionalPoissonDirectionalFlowAction
    finiteBidirectionalPoissonCurrentAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  exact bidirectionalPoissonDiscrimination_eq_currentAction_add_residual
    (hLaw edge) (hReference edge) (hCurrent edge)

/-- The finite contracted current action is a lower bound on every positive directional-flow
family with the prescribed currents. -/
theorem finiteBidirectionalPoissonCurrentAction_le_directionalFlowAction
    {referenceRates lawRates : Edge → BidirectionalPoissonRates}
    {netCurrents : Edge → ℝ}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (hLaw : ∀ edge, (lawRates edge).Positive)
    (hCurrent : ∀ edge, (lawRates edge).current = netCurrents edge) :
    finiteBidirectionalPoissonCurrentAction referenceRates netCurrents ≤
      finiteBidirectionalPoissonDirectionalFlowAction referenceRates lawRates := by
  rw [finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_add_residual
    hReference hLaw hCurrent]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun edge _ ↦
    bidirectionalPoissonDiscrimination_nonneg (hLaw edge)
      (finiteBidirectionalPoissonCurrentFibreProjection_positive
        hReference netCurrents edge)

/-- Equality with the finite contracted action identifies every directional flow with its
current-fibre projection. -/
theorem finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_iff
    {referenceRates lawRates : Edge → BidirectionalPoissonRates}
    {netCurrents : Edge → ℝ}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (hLaw : ∀ edge, (lawRates edge).Positive)
    (hCurrent : ∀ edge, (lawRates edge).current = netCurrents edge) :
    finiteBidirectionalPoissonDirectionalFlowAction referenceRates lawRates =
        finiteBidirectionalPoissonCurrentAction referenceRates netCurrents ↔
      lawRates = finiteBidirectionalPoissonCurrentFibreProjection
        referenceRates netCurrents := by
  rw [finiteBidirectionalPoissonDirectionalFlowAction_eq_currentAction_add_residual
    hReference hLaw hCurrent]
  have hResidualNonneg :
      0 ≤ fun edge ↦ bidirectionalPoissonDiscrimination (lawRates edge)
        (finiteBidirectionalPoissonCurrentFibreProjection
          referenceRates netCurrents edge) :=
    fun edge ↦ bidirectionalPoissonDiscrimination_nonneg (hLaw edge)
      (finiteBidirectionalPoissonCurrentFibreProjection_positive
        hReference netCurrents edge)
  constructor
  · intro hEqual
    have hResidualSum :
        ∑ edge, bidirectionalPoissonDiscrimination (lawRates edge)
          (finiteBidirectionalPoissonCurrentFibreProjection
            referenceRates netCurrents edge) = 0 := by
      linarith
    have hZero :=
      (Fintype.sum_eq_zero_iff_of_nonneg hResidualNonneg).mp hResidualSum
    funext edge
    exact (bidirectionalPoissonDiscrimination_eq_zero_iff (hLaw edge)
      (finiteBidirectionalPoissonCurrentFibreProjection_positive
        hReference netCurrents edge)).mp (congrFun hZero edge)
  · intro hRates
    have hZero :
        (fun edge ↦ bidirectionalPoissonDiscrimination (lawRates edge)
          (finiteBidirectionalPoissonCurrentFibreProjection
            referenceRates netCurrents edge)) = 0 := by
      funext edge
      rw [hRates]
      exact (bidirectionalPoissonDiscrimination_eq_zero_iff
        (finiteBidirectionalPoissonCurrentFibreProjection_positive
          hReference netCurrents edge)
        (finiteBidirectionalPoissonCurrentFibreProjection_positive
          hReference netCurrents edge)).2 rfl
    have hResidualSum :=
      (Fintype.sum_eq_zero_iff_of_nonneg hResidualNonneg).2 hZero
    rw [hResidualSum, add_zero]

/-- The finite current action is nonnegative. -/
theorem finiteBidirectionalPoissonCurrentAction_nonneg
    {referenceRates : Edge → BidirectionalPoissonRates}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) :
    0 ≤ finiteBidirectionalPoissonCurrentAction referenceRates netCurrents := by
  unfold finiteBidirectionalPoissonCurrentAction
  exact Finset.sum_nonneg fun edge _ ↦
    bidirectionalPoissonCurrentAction_nonneg (hReference edge) (netCurrents edge)

/-- The finite current action vanishes exactly when every prescribed current equals its source
current. -/
theorem finiteBidirectionalPoissonCurrentAction_eq_zero_iff
    {referenceRates : Edge → BidirectionalPoissonRates}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) :
    finiteBidirectionalPoissonCurrentAction referenceRates netCurrents = 0 ↔
      netCurrents = fun edge ↦ (referenceRates edge).current := by
  unfold finiteBidirectionalPoissonCurrentAction
  have hActionNonneg :
      0 ≤ fun edge ↦ bidirectionalPoissonCurrentAction
        (referenceRates edge) (netCurrents edge) :=
    fun edge ↦ bidirectionalPoissonCurrentAction_nonneg
      (hReference edge) (netCurrents edge)
  rw [Fintype.sum_eq_zero_iff_of_nonneg hActionNonneg]
  constructor
  · intro hZero
    funext edge
    exact (bidirectionalPoissonCurrentAction_eq_zero_iff
      (hReference edge) (netCurrents edge)).mp (congrFun hZero edge)
  · intro hCurrent
    funext edge
    exact (bidirectionalPoissonCurrentAction_eq_zero_iff
      (hReference edge) (netCurrents edge)).2 (congrFun hCurrent edge)

/-- Exact finite-sector common-scale extensivity. -/
theorem finiteBidirectionalPoissonCurrentAction_commonScale
    {scale : ℝ} {referenceRates : Edge → BidirectionalPoissonRates}
    (hScale : 0 < scale) (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) :
    finiteBidirectionalPoissonCurrentAction
        (fun edge ↦ (referenceRates edge).commonScale scale)
        (fun edge ↦ scale * netCurrents edge) =
      scale * finiteBidirectionalPoissonCurrentAction referenceRates netCurrents := by
  unfold finiteBidirectionalPoissonCurrentAction
  simp_rw [bidirectionalPoissonCurrentAction_commonScale hScale (hReference _)]
  exact (Finset.mul_sum Finset.univ
    (fun edge ↦ bidirectionalPoissonCurrentAction (referenceRates edge) (netCurrents edge))
    scale).symm

/-- Simultaneous reversal of every reference sector and current preserves the finite action. -/
theorem finiteBidirectionalPoissonCurrentAction_reversal
    {referenceRates : Edge → BidirectionalPoissonRates}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) :
    finiteBidirectionalPoissonCurrentAction
        (fun edge ↦ (referenceRates edge).swap)
        (fun edge ↦ -netCurrents edge) =
      finiteBidirectionalPoissonCurrentAction referenceRates netCurrents := by
  unfold finiteBidirectionalPoissonCurrentAction
  apply Finset.sum_congr rfl
  intro edge _
  exact bidirectionalPoissonCurrentAction_reversal
    (hReference edge) (netCurrents edge)

/-- The finite current action has the exact summed current--affinity fluctuation symmetry. -/
theorem finiteBidirectionalPoissonCurrentAction_fluctuationSymmetry
    {referenceRates : Edge → BidirectionalPoissonRates}
    (hReference : ∀ edge, (referenceRates edge).Positive)
    (netCurrents : Edge → ℝ) :
    finiteBidirectionalPoissonCurrentAction referenceRates netCurrents -
        finiteBidirectionalPoissonCurrentAction referenceRates
          (fun edge ↦ -netCurrents edge) =
      ∑ edge, -netCurrents edge * (referenceRates edge).affinity := by
  unfold finiteBidirectionalPoissonCurrentAction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  exact bidirectionalPoissonCurrentAction_fluctuationSymmetry
    (hReference edge) (netCurrents edge)

end FiniteMarkovProcesses.InformationTheory
