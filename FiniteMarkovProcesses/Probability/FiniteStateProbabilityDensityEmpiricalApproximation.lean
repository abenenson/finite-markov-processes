/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.SpecificLimits.Basic
import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalType

/-!
# Approximation of a finite probability density by empirical types

This module constructs, at every positive sample size, an exact integer empirical type converging
to an arbitrary point of the finite probability simplex.  A canonical pivot coordinate receives
the remainder after all non-pivot coordinates are rounded down.  The construction therefore
preserves total mass exactly at every size, including for boundary densities.

## Main declarations

- `finiteStateProbabilityDensityRoundingPivot`: canonical remainder coordinate.
- `finiteStateProbabilityDensityRoundedPositiveEmpiricalType`: exact count type at each size.
- `finiteStateProbabilityDensityRoundedPositiveEmpiricalType_probabilityDensity_tendsto`:
  convergence in the ordinary finite-simplex topology.
-/

namespace FiniteMarkovProcesses.Probability

open Filter
open scoped BigOperators NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

omit [DecidableEq State] in
/-- The existence of a finite probability density forces its state type to be nonempty. -/
theorem nonempty_state_of_finiteStateProbabilityDensity
    (density : FiniteStateProbabilityDensity State) : Nonempty State := by
  classical
  by_contra hState
  have : IsEmpty State := not_nonempty_iff.mp hState
  simpa using density.sum_weight

/-- Canonical coordinate receiving the exact remainder in the rounded empirical type. -/
def finiteStateProbabilityDensityRoundingPivot
    (density : FiniteStateProbabilityDensity State) : State :=
  Classical.choice (nonempty_state_of_finiteStateProbabilityDensity density)

/-- Natural floor of one sample-size-scaled simplex coordinate. -/
def finiteStateProbabilityDensityFloorCount
    (density : FiniteStateProbabilityDensity State) (sampleSize : ℕ) (state : State) : ℕ :=
  ⌊(sampleSize : ℝ) * (density.weight state : ℝ)⌋₊

/-- The non-pivot floor counts never exceed the total sample size. -/
theorem sum_finiteStateProbabilityDensityFloorCount_erase_pivot_le
    (density : FiniteStateProbabilityDensity State) (sampleSize : ℕ) :
    ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
        finiteStateProbabilityDensityFloorCount density sampleSize state ≤ sampleSize := by
  have hReal :
      (∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
        finiteStateProbabilityDensityFloorCount density sampleSize state : ℕ) ≤
          (sampleSize : ℝ) := by
    calc
      ((∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          finiteStateProbabilityDensityFloorCount density sampleSize state : ℕ) : ℝ) =
          ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
            (finiteStateProbabilityDensityFloorCount density sampleSize state : ℝ) := by
              norm_cast
      _ ≤ ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          (sampleSize : ℝ) * (density.weight state : ℝ) := by
        apply Finset.sum_le_sum
        intro state _hState
        exact Nat.floor_le
          (mul_nonneg (Nat.cast_nonneg sampleSize) (by positivity))
      _ ≤ ∑ state, (sampleSize : ℝ) * (density.weight state : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro state _hState _hMissing
        positivity
      _ = (sampleSize : ℝ) := by
        rw [← Finset.mul_sum]
        have hSum : ∑ state, (density.weight state : ℝ) = 1 := by
          exact_mod_cast density.sum_weight
        rw [hSum, mul_one]
  exact_mod_cast hReal

/-- Rounded count at one coordinate.  Non-pivot coordinates are floored and the pivot receives
the unique remainder needed for exact total mass. -/
def finiteStateProbabilityDensityRoundedCount
    (density : FiniteStateProbabilityDensity State) (sampleSize : ℕ) (state : State) : ℕ :=
  if state = finiteStateProbabilityDensityRoundingPivot density then
    sampleSize -
      ∑ candidate ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
        finiteStateProbabilityDensityFloorCount density sampleSize candidate
  else finiteStateProbabilityDensityFloorCount density sampleSize state

/-- The rounded coordinate counts sum to the exact requested sample size. -/
theorem sum_finiteStateProbabilityDensityRoundedCount
    (density : FiniteStateProbabilityDensity State) (sampleSize : ℕ) :
    ∑ state, finiteStateProbabilityDensityRoundedCount density sampleSize state = sampleSize := by
  rw [← Finset.sum_erase_add Finset.univ
    (finiteStateProbabilityDensityRoundedCount density sampleSize)
    (Finset.mem_univ (finiteStateProbabilityDensityRoundingPivot density))]
  have hErase :
      ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          finiteStateProbabilityDensityRoundedCount density sampleSize state =
        ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          finiteStateProbabilityDensityFloorCount density sampleSize state := by
    apply Finset.sum_congr rfl
    intro state hState
    rw [finiteStateProbabilityDensityRoundedCount,
      ite_eq_right (Finset.ne_of_mem_erase hState)]
  rw [hErase, finiteStateProbabilityDensityRoundedCount, ite_eq_left rfl]
  have hBound := sum_finiteStateProbabilityDensityFloorCount_erase_pivot_le
    density sampleSize
  omega

/-- Every rounded coordinate count is bounded by the total sample size. -/
theorem finiteStateProbabilityDensityRoundedCount_le
    (density : FiniteStateProbabilityDensity State) (sampleSize : ℕ) (state : State) :
    finiteStateProbabilityDensityRoundedCount density sampleSize state ≤ sampleSize := by
  calc
    finiteStateProbabilityDensityRoundedCount density sampleSize state ≤
        ∑ candidate,
          finiteStateProbabilityDensityRoundedCount density sampleSize candidate :=
      Finset.single_le_sum (fun _candidate _hCandidate => Nat.zero_le _)
        (Finset.mem_univ state)
    _ = sampleSize :=
      sum_finiteStateProbabilityDensityRoundedCount density sampleSize

/-- Exact positive empirical type obtained by floor rounding all non-pivot coordinates and
assigning the remainder to the pivot. -/
def finiteStateProbabilityDensityRoundedPositiveEmpiricalType
    (density : FiniteStateProbabilityDensity State) (successorIndex : ℕ) :
    FiniteIIDPositiveEmpiricalType State successorIndex where
  count state :=
    ⟨finiteStateProbabilityDensityRoundedCount density (successorIndex + 1) state, by
      have hBound := finiteStateProbabilityDensityRoundedCount_le
        density (successorIndex + 1) state
      omega⟩
  sum_count :=
    sum_finiteStateProbabilityDensityRoundedCount density (successorIndex + 1)

/-- The finite probability density represented by the rounded empirical count type. -/
def finiteStateRoundedEmpiricalProbabilityDensity
    (density : FiniteStateProbabilityDensity State) (successorIndex : ℕ) :
    FiniteStateProbabilityDensity State :=
  FiniteIIDPositiveEmpiricalType.probabilityDensity
    (finiteStateProbabilityDensityRoundedPositiveEmpiricalType density successorIndex)

/-- Every non-pivot coordinate of the rounded empirical density converges to the target
coordinate by the elementary floor-over-sample-size limit. -/
theorem finiteStateProbabilityDensityRoundedPositiveEmpiricalType_nonpivot_tendsto
    (density : FiniteStateProbabilityDensity State) (state : State)
    (hState : state ≠ finiteStateProbabilityDensityRoundingPivot density) :
    Tendsto
      (fun successorIndex =>
        ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state : ℝ))
      atTop (nhds (density.weight state : ℝ)) := by
  have hSampleSize :
      Tendsto (fun successorIndex : ℕ => ((successorIndex + 1 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hFloor :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ)
      (a := (density.weight state : ℝ)) (by positivity)).comp
      hSampleSize
  convert hFloor using 1
  funext successorIndex
  rw [finiteStateRoundedEmpiricalProbabilityDensity,
    FiniteIIDPositiveEmpiricalType.probabilityDensity_weight]
  simp only [finiteStateProbabilityDensityRoundedPositiveEmpiricalType,
    finiteStateProbabilityDensityRoundedCount, hState, ite_false,
    finiteStateProbabilityDensityFloorCount, NNReal.coe_div, NNReal.coe_natCast]
  congr 2
  rw [mul_comm]
  norm_cast

/-- The rounded pivot coordinate is exactly one minus the sum of the non-pivot coordinates. -/
theorem finiteStateProbabilityDensityRoundedPositiveEmpiricalType_pivot_weight_eq
    (density : FiniteStateProbabilityDensity State) (successorIndex : ℕ) :
    ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight
        (finiteStateProbabilityDensityRoundingPivot density) : ℝ) =
      1 -
        ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state :
            ℝ) := by
  have hSum :
      ∑ state,
          ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state :
            ℝ) = 1 := by
    exact_mod_cast
      (finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).sum_weight
  rw [← Finset.sum_erase_add Finset.univ
    (fun state =>
      ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state : ℝ))
    (Finset.mem_univ (finiteStateProbabilityDensityRoundingPivot density))] at hSum
  linarith

/-- The target pivot coordinate is one minus the sum of its non-pivot coordinates. -/
theorem finiteStateProbabilityDensity_pivot_weight_eq
    (density : FiniteStateProbabilityDensity State) :
    (density.weight (finiteStateProbabilityDensityRoundingPivot density) : ℝ) =
      1 -
        ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
          (density.weight state : ℝ) := by
  have hSum : ∑ state, (density.weight state : ℝ) = 1 := by
    exact_mod_cast density.sum_weight
  rw [← Finset.sum_erase_add Finset.univ
    (fun state => (density.weight state : ℝ))
    (Finset.mem_univ (finiteStateProbabilityDensityRoundingPivot density))] at hSum
  linarith

/-- The rounded pivot coordinate converges because both the rounded and target densities have
exact total mass one and every non-pivot coordinate converges. -/
theorem finiteStateProbabilityDensityRoundedPositiveEmpiricalType_pivot_tendsto
    (density : FiniteStateProbabilityDensity State) :
    Tendsto
      (fun successorIndex =>
        ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight
          (finiteStateProbabilityDensityRoundingPivot density) : ℝ))
      atTop
      (nhds (density.weight (finiteStateProbabilityDensityRoundingPivot density) : ℝ)) := by
  have hSum :
      Tendsto
        (fun successorIndex =>
          ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
            ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state :
              ℝ))
        atTop
        (nhds
          (∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
            (density.weight state : ℝ))) :=
    tendsto_finsetSum _ fun state hState =>
      finiteStateProbabilityDensityRoundedPositiveEmpiricalType_nonpivot_tendsto
        density state (Finset.ne_of_mem_erase hState)
  have hDifference :
      Tendsto
        (fun successorIndex =>
          (1 : ℝ) -
            ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
              ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight
                state : ℝ))
        atTop
        (nhds
          ((1 : ℝ) -
            ∑ state ∈ Finset.univ.erase (finiteStateProbabilityDensityRoundingPivot density),
              (density.weight state : ℝ))) :=
    tendsto_const_nhds.sub hSum
  convert hDifference using 1
  · funext successorIndex
    exact
      (finiteStateProbabilityDensityRoundedPositiveEmpiricalType_pivot_weight_eq
        density successorIndex)
  · exact congrArg nhds (finiteStateProbabilityDensity_pivot_weight_eq density)

/-- Every coordinate of the rounded empirical density converges to its target coordinate. -/
theorem finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto
    (density : FiniteStateProbabilityDensity State) (state : State) :
    Tendsto
      (fun successorIndex =>
        ((finiteStateRoundedEmpiricalProbabilityDensity density successorIndex).weight state : ℝ))
      atTop (nhds (density.weight state : ℝ)) := by
  by_cases hState : state = finiteStateProbabilityDensityRoundingPivot density
  · subst state
    exact finiteStateProbabilityDensityRoundedPositiveEmpiricalType_pivot_tendsto density
  · exact finiteStateProbabilityDensityRoundedPositiveEmpiricalType_nonpivot_tendsto
      density state hState

/-- Rounded exact empirical types converge to the target in the ordinary finite-simplex
topology. -/
theorem finiteStateProbabilityDensityRoundedPositiveEmpiricalType_probabilityDensity_tendsto
    (density : FiniteStateProbabilityDensity State) :
    Tendsto
      (fun successorIndex =>
        finiteStateRoundedEmpiricalProbabilityDensity density successorIndex)
      atTop (nhds density) := by
  rw [FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise]
  intro state
  exact NNReal.tendsto_coe.mp
    (finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto density state)

/-- Canonical deterministic positive-sample configuration realizing the rounded empirical type.
The word order is immaterial; only its exact state counts enter the particle source. -/
def finiteStateProbabilityDensityRoundedInitialConfiguration
    (density : FiniteStateProbabilityDensity State) (successorIndex : ℕ) :
    Fin (successorIndex + 1) → State :=
  (finiteStateProbabilityDensityRoundedPositiveEmpiricalType
    density successorIndex).representative

/-- The empirical simplex point of the canonical rounded configuration is exactly the rounded
probability density, with no asymptotic approximation at finite particle count. -/
@[simp]
theorem finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration
    (density : FiniteStateProbabilityDensity State) (successorIndex : ℕ) :
    finiteIIDEmpiricalProbabilityDensity successorIndex
        (finiteStateProbabilityDensityRoundedInitialConfiguration density successorIndex) =
      finiteStateRoundedEmpiricalProbabilityDensity density successorIndex := by
  rw [← finiteIIDPositiveSampleEmpiricalType_probabilityDensity]
  simp [finiteStateProbabilityDensityRoundedInitialConfiguration,
    finiteStateRoundedEmpiricalProbabilityDensity]

/-- The exact empirical densities of the canonical deterministic rounded configurations converge
to the requested finite-state density. -/
theorem finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration_tendsto
    (density : FiniteStateProbabilityDensity State) :
    Tendsto
      (fun successorIndex =>
        finiteIIDEmpiricalProbabilityDensity successorIndex
          (finiteStateProbabilityDensityRoundedInitialConfiguration density successorIndex))
      atTop (nhds density) := by
  simpa only [finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration] using
    finiteStateProbabilityDensityRoundedPositiveEmpiricalType_probabilityDensity_tendsto density

end

end FiniteMarkovProcesses.Probability
