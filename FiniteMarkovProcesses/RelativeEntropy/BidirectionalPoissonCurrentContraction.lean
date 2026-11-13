/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.BidirectionalPoissonForceReactivity
public import FiniteMarkovProcesses.RelativeEntropy.BidirectionalPoissonPathAction

/-!
# Bidirectional Poisson current contraction

This file contracts the exact directional-flow discrimination of two positive Poisson clocks onto
a prescribed net current.  The minimizing directional pair is fixed by the current and the
reference reactivity.  An exact Pythagorean identity proves unique minimization on the whole
positive current fibre.

The results concern finite normalized probability laws.  Common scaling gives exact extensivity
of the complete-law KL.  These identities alone do not establish a large-deviation principle.

## Main results

- `currentFibreProjection`: positive directional flow at a prescribed net current and reference
  reactivity.
- `bidirectionalPoissonDiscrimination_pythagorean`: exact whole-fibre contraction identity.
- `bidirectionalPoissonDiscrimination_eq_currentAction_iff`: literal unique minimization.
- `bidirectionalPoissonCurrentAction_eq_zero_iff`: zero cost exactly at the source current.
- `bidirectionalPoissonCurrentAction_fluctuationSymmetry`: exact time-odd current--affinity law.
- `toReal_klDiv_bidirectionalPoissonHistoryMeasure_commonScale`: exact finite complete-law KL
  extensivity.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open _root_.InformationTheory
open scoped NNReal

open FiniteMarkovProcesses.Probability

namespace BidirectionalPoissonRates

/-- Exchange the two directional rates. -/
def swap (rates : BidirectionalPoissonRates) : BidirectionalPoissonRates where
  clockwise := rates.counterclockwise
  counterclockwise := rates.clockwise

/-- Direction exchange preserves strict positivity. -/
theorem swap_positive {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    rates.swap.Positive :=
  ⟨hRates.2, hRates.1⟩

/-- Exchanging directions twice recovers the original rate pair. -/
@[simp]
theorem swap_swap (rates : BidirectionalPoissonRates) : rates.swap.swap = rates := rfl

/-- Direction exchange negates current. -/
@[simp]
theorem swap_current (rates : BidirectionalPoissonRates) :
    rates.swap.current = -rates.current := by
  unfold swap current
  ring

/-- Direction exchange preserves traffic. -/
@[simp]
theorem swap_traffic (rates : BidirectionalPoissonRates) :
    rates.swap.traffic = rates.traffic := by
  unfold swap traffic
  ring

/-- Direction exchange preserves the product of directional rates. -/
@[simp]
theorem swap_product (rates : BidirectionalPoissonRates) :
    rates.swap.clockwise * rates.swap.counterclockwise =
      rates.clockwise * rates.counterclockwise := by
  unfold swap
  ring

/-- Direction exchange negates affinity. -/
@[simp]
theorem swap_affinity {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    rates.swap.affinity = -rates.affinity := by
  unfold swap affinity
  rw [Real.log_div hRates.2.ne' hRates.1.ne',
    Real.log_div hRates.1.ne' hRates.2.ne']
  ring

/-- Direction exchange preserves reactivity. -/
@[simp]
theorem swap_reactivity (rates : BidirectionalPoissonRates) :
    rates.swap.reactivity = rates.reactivity := by
  unfold swap reactivity
  congr 1
  ring

/-- Common positive scaling transports current linearly. -/
@[simp]
theorem commonScale_current (scale : ℝ) (rates : BidirectionalPoissonRates) :
    (rates.commonScale scale).current = scale * rates.current := by
  unfold commonScale current
  ring

/-- Common positive scaling transports traffic linearly. -/
@[simp]
theorem commonScale_traffic (scale : ℝ) (rates : BidirectionalPoissonRates) :
    (rates.commonScale scale).traffic = scale * rates.traffic := by
  unfold commonScale traffic
  ring

/-- Common scaling transports the directional-rate product quadratically. -/
@[simp]
theorem commonScale_product (scale : ℝ) (rates : BidirectionalPoissonRates) :
    (rates.commonScale scale).clockwise * (rates.commonScale scale).counterclockwise =
      scale ^ 2 * (rates.clockwise * rates.counterclockwise) := by
  unfold commonScale
  ring

/-- Positive directional pairs are identified by their current and directional product. -/
theorem eq_of_current_eq_of_product_eq
    {first second : BidirectionalPoissonRates}
    (hFirst : first.Positive) (hSecond : second.Positive)
    (hCurrent : first.current = second.current)
    (hProduct :
      first.clockwise * first.counterclockwise =
        second.clockwise * second.counterclockwise) :
    first = second := by
  have hDifference :
      first.clockwise - second.clockwise =
        first.counterclockwise - second.counterclockwise := by
    unfold current at hCurrent
    linarith
  have hFactor :
      (first.clockwise - second.clockwise) *
        (first.counterclockwise + second.clockwise) = 0 := by
    calc
      _ = (first.clockwise - second.clockwise) * first.counterclockwise +
          second.clockwise * (first.clockwise - second.clockwise) := by ring
      _ = (first.clockwise - second.clockwise) * first.counterclockwise +
          second.clockwise * (first.counterclockwise - second.counterclockwise) := by
            rw [hDifference]
      _ = first.clockwise * first.counterclockwise -
          second.clockwise * second.counterclockwise := by ring
      _ = 0 := sub_eq_zero.mpr hProduct
  have hDifferenceZero : first.clockwise - second.clockwise = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right
      (add_pos hFirst.2 hSecond.1).ne'
  apply BidirectionalPoissonRates.ext
  · linarith
  · linarith

end BidirectionalPoissonRates

/-- Poisson discrimination is exactly extensive when law and reference intensities receive the
same positive scale. -/
theorem poissonRateDiscrimination_commonScale
    {scale lawIntensity referenceIntensity : ℝ}
    (hScale : 0 < scale) (hLaw : 0 < lawIntensity) (hReference : 0 < referenceIntensity) :
    poissonRateDiscrimination (scale * lawIntensity) (scale * referenceIntensity) =
      scale * poissonRateDiscrimination lawIntensity referenceIntensity := by
  unfold poissonRateDiscrimination
  have hRatio :
      scale * lawIntensity / (scale * referenceIntensity) =
        lawIntensity / referenceIntensity := by
    field_simp [hScale.ne', hReference.ne']
  rw [hRatio]
  ring

/-- Bidirectional discrimination is exactly extensive under one common positive kinetic scale. -/
theorem bidirectionalPoissonDiscrimination_commonScale
    {scale : ℝ} {lawRates referenceRates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hLaw : lawRates.Positive) (hReference : referenceRates.Positive) :
    bidirectionalPoissonDiscrimination (lawRates.commonScale scale)
        (referenceRates.commonScale scale) =
      scale * bidirectionalPoissonDiscrimination lawRates referenceRates := by
  unfold bidirectionalPoissonDiscrimination BidirectionalPoissonRates.commonScale
  rw [poissonRateDiscrimination_commonScale hScale hLaw.1 hReference.1,
    poissonRateDiscrimination_commonScale hScale hLaw.2 hReference.2]
  ring

/-- Simultaneous direction exchange preserves the ordered discrimination. -/
@[simp]
theorem bidirectionalPoissonDiscrimination_swap
    (lawRates referenceRates : BidirectionalPoissonRates) :
    bidirectionalPoissonDiscrimination lawRates.swap referenceRates.swap =
      bidirectionalPoissonDiscrimination lawRates referenceRates := by
  unfold bidirectionalPoissonDiscrimination BidirectionalPoissonRates.swap
  ring

/-- Difference between one directional flow and its exchanged flow against a fixed reference.
This is the exact time-odd current--affinity sector. -/
theorem bidirectionalPoissonDiscrimination_sub_swapLaw
    {lawRates referenceRates : BidirectionalPoissonRates}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive) :
    bidirectionalPoissonDiscrimination lawRates referenceRates -
        bidirectionalPoissonDiscrimination lawRates.swap referenceRates =
      -lawRates.current * referenceRates.affinity := by
  unfold bidirectionalPoissonDiscrimination poissonRateDiscrimination
  unfold BidirectionalPoissonRates.swap BidirectionalPoissonRates.current
    BidirectionalPoissonRates.affinity
  rw [Real.log_div hLaw.1.ne' hReference.1.ne',
    Real.log_div hLaw.2.ne' hReference.2.ne',
    Real.log_div hLaw.2.ne' hReference.1.ne',
    Real.log_div hLaw.1.ne' hReference.2.ne',
    Real.log_div hReference.1.ne' hReference.2.ne']
  ring

/-- Positive directional flow with prescribed net current and the reference directional product.
The positive square root fixes the construction before any source-specific replay. -/
noncomputable def currentFibreProjection
    (referenceRates : BidirectionalPoissonRates) (netCurrent : ℝ) :
    BidirectionalPoissonRates where
  clockwise :=
    (netCurrent + Real.sqrt
      (netCurrent ^ 2 +
        4 * referenceRates.clockwise * referenceRates.counterclockwise)) / 2
  counterclockwise :=
    (-netCurrent + Real.sqrt
      (netCurrent ^ 2 +
        4 * referenceRates.clockwise * referenceRates.counterclockwise)) / 2

/-- The current-fibre projection is strictly positive for every real current and positive
reference pair. -/
theorem currentFibreProjection_positive
    {referenceRates : BidirectionalPoissonRates}
    (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    (currentFibreProjection referenceRates netCurrent).Positive := by
  let radicand :=
    netCurrent ^ 2 +
      4 * referenceRates.clockwise * referenceRates.counterclockwise
  have hProduct : 0 < referenceRates.clockwise * referenceRates.counterclockwise :=
    mul_pos hReference.1 hReference.2
  have hRadicand : 0 < radicand := by
    dsimp [radicand]
    nlinarith [sq_nonneg netCurrent]
  have hSquare : (Real.sqrt radicand) ^ 2 = radicand :=
    Real.sq_sqrt hRadicand.le
  have hSqrtNonneg : 0 ≤ Real.sqrt radicand := Real.sqrt_nonneg _
  have hNetLtSqrt : netCurrent < Real.sqrt radicand := by
    dsimp [radicand] at hSquare
    nlinarith
  have hNegNetLtSqrt : -netCurrent < Real.sqrt radicand := by
    dsimp [radicand] at hSquare
    nlinarith
  constructor <;>
    simp only [currentFibreProjection] <;>
    linarith

/-- Boundary control: if the reference product vanishes, the frozen projection need not be
strictly positive.  This exact witness prevents the positive-interior contraction theorem from
being silently promoted to zero-rate boundary data. -/
theorem currentFibreProjection_unitZeroBoundary_not_positive :
    ¬ (currentFibreProjection (⟨1, 0⟩ : BidirectionalPoissonRates) 1).Positive := by
  norm_num [currentFibreProjection, BidirectionalPoissonRates.Positive]

/-- The current-fibre projection has the prescribed net current. -/
@[simp]
theorem currentFibreProjection_current
    (referenceRates : BidirectionalPoissonRates) (netCurrent : ℝ) :
    (currentFibreProjection referenceRates netCurrent).current = netCurrent := by
  unfold currentFibreProjection BidirectionalPoissonRates.current
  ring

/-- The current-fibre projection preserves the directional product of the reference pair. -/
theorem currentFibreProjection_product
    {referenceRates : BidirectionalPoissonRates}
    (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    (currentFibreProjection referenceRates netCurrent).clockwise *
        (currentFibreProjection referenceRates netCurrent).counterclockwise =
      referenceRates.clockwise * referenceRates.counterclockwise := by
  have hProduct : 0 < referenceRates.clockwise * referenceRates.counterclockwise :=
    mul_pos hReference.1 hReference.2
  have hRadicand :
      0 ≤ netCurrent ^ 2 +
        4 * referenceRates.clockwise * referenceRates.counterclockwise := by
    nlinarith [sq_nonneg netCurrent]
  have hSquare := Real.sq_sqrt hRadicand
  unfold currentFibreProjection
  nlinarith

/-- The current-fibre projection preserves the reference reactivity exactly. -/
@[simp]
theorem currentFibreProjection_reactivity
    {referenceRates : BidirectionalPoissonRates}
    (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    (currentFibreProjection referenceRates netCurrent).reactivity =
      referenceRates.reactivity := by
  have hProjection := currentFibreProjection_positive hReference netCurrent
  unfold BidirectionalPoissonRates.reactivity
  congr 1
  calc
    _ = Real.log
          ((currentFibreProjection referenceRates netCurrent).clockwise *
            (currentFibreProjection referenceRates netCurrent).counterclockwise) / 2 := by
          rw [Real.log_mul hProjection.1.ne' hProjection.2.ne']
    _ = Real.log (referenceRates.clockwise * referenceRates.counterclockwise) / 2 := by
          rw [currentFibreProjection_product hReference netCurrent]
    _ = _ := by rw [Real.log_mul hReference.1.ne' hReference.2.ne']

/-- A positive rate pair with the prescribed current and reference product is literally the
current-fibre projection. -/
theorem eq_currentFibreProjection_of_current_eq_of_product_eq
    {candidateRates referenceRates : BidirectionalPoissonRates} {netCurrent : ℝ}
    (hCandidate : candidateRates.Positive) (hReference : referenceRates.Positive)
    (hCurrent : candidateRates.current = netCurrent)
    (hProduct : candidateRates.clockwise * candidateRates.counterclockwise =
      referenceRates.clockwise * referenceRates.counterclockwise) :
    candidateRates = currentFibreProjection referenceRates netCurrent := by
  apply BidirectionalPoissonRates.eq_of_current_eq_of_product_eq hCandidate
    (currentFibreProjection_positive hReference netCurrent)
  · rw [currentFibreProjection_current, hCurrent]
  · rw [currentFibreProjection_product hReference netCurrent]
    exact hProduct

/-- Projecting the source current recovers the reference pair literally. -/
theorem currentFibreProjection_sourceCurrent
    {referenceRates : BidirectionalPoissonRates} (hReference : referenceRates.Positive) :
    currentFibreProjection referenceRates referenceRates.current = referenceRates := by
  symm
  exact eq_currentFibreProjection_of_current_eq_of_product_eq hReference hReference rfl rfl

/-- Projection commutes with positive common kinetic scaling when the current receives the same
scale. -/
theorem currentFibreProjection_commonScale
    {scale : ℝ} {referenceRates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    currentFibreProjection (referenceRates.commonScale scale) (scale * netCurrent) =
      (currentFibreProjection referenceRates netCurrent).commonScale scale := by
  symm
  apply eq_currentFibreProjection_of_current_eq_of_product_eq
    (BidirectionalPoissonRates.commonScale_positive hScale
      (currentFibreProjection_positive hReference netCurrent))
    (BidirectionalPoissonRates.commonScale_positive hScale hReference)
  · simp
  · rw [BidirectionalPoissonRates.commonScale_product,
      BidirectionalPoissonRates.commonScale_product,
      currentFibreProjection_product hReference netCurrent]

/-- Negating the prescribed current exchanges the projected directional flows. -/
theorem currentFibreProjection_negCurrent
    {referenceRates : BidirectionalPoissonRates}
    (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    currentFibreProjection referenceRates (-netCurrent) =
      (currentFibreProjection referenceRates netCurrent).swap := by
  symm
  apply eq_currentFibreProjection_of_current_eq_of_product_eq
    (BidirectionalPoissonRates.swap_positive
      (currentFibreProjection_positive hReference netCurrent))
    hReference
  · simp
  · rw [BidirectionalPoissonRates.swap_product,
      currentFibreProjection_product hReference netCurrent]

/-- Projection is covariant under simultaneous direction exchange and current reversal. -/
theorem currentFibreProjection_swap
    {referenceRates : BidirectionalPoissonRates}
    (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    currentFibreProjection referenceRates.swap (-netCurrent) =
      (currentFibreProjection referenceRates netCurrent).swap := by
  symm
  apply eq_currentFibreProjection_of_current_eq_of_product_eq
    (BidirectionalPoissonRates.swap_positive
      (currentFibreProjection_positive hReference netCurrent))
    (BidirectionalPoissonRates.swap_positive hReference)
  · simp
  · rw [BidirectionalPoissonRates.swap_product,
      currentFibreProjection_product hReference netCurrent,
      BidirectionalPoissonRates.swap_product]

/-- Exact Bregman/Pythagorean identity on one positive current fibre.  Product preservation is the
normal covector condition for the fibre. -/
theorem bidirectionalPoissonDiscrimination_pythagorean
    {lawRates referenceRates projectionRates : BidirectionalPoissonRates}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive)
    (hProjection : projectionRates.Positive)
    (hCurrent : lawRates.current = projectionRates.current)
    (hProduct : projectionRates.clockwise * projectionRates.counterclockwise =
      referenceRates.clockwise * referenceRates.counterclockwise) :
    bidirectionalPoissonDiscrimination lawRates referenceRates =
      bidirectionalPoissonDiscrimination projectionRates referenceRates +
        bidirectionalPoissonDiscrimination lawRates projectionRates := by
  have hDifference :
      lawRates.clockwise - projectionRates.clockwise =
        lawRates.counterclockwise - projectionRates.counterclockwise := by
    unfold BidirectionalPoissonRates.current at hCurrent
    linarith
  have hLogSum :
      (Real.log projectionRates.clockwise - Real.log referenceRates.clockwise) +
          (Real.log projectionRates.counterclockwise -
            Real.log referenceRates.counterclockwise) = 0 := by
    calc
      _ = Real.log (projectionRates.clockwise * projectionRates.counterclockwise) -
          Real.log (referenceRates.clockwise * referenceRates.counterclockwise) := by
            rw [Real.log_mul hProjection.1.ne' hProjection.2.ne',
              Real.log_mul hReference.1.ne' hReference.2.ne']
            ring
      _ = 0 := by rw [hProduct]; ring
  unfold bidirectionalPoissonDiscrimination poissonRateDiscrimination
  rw [Real.log_div hLaw.1.ne' hReference.1.ne',
    Real.log_div hLaw.2.ne' hReference.2.ne',
    Real.log_div hProjection.1.ne' hReference.1.ne',
    Real.log_div hProjection.2.ne' hReference.2.ne',
    Real.log_div hLaw.1.ne' hProjection.1.ne',
    Real.log_div hLaw.2.ne' hProjection.2.ne']
  linear_combination
    (Real.log projectionRates.clockwise - Real.log referenceRates.clockwise) * hDifference +
    (lawRates.counterclockwise - projectionRates.counterclockwise) * hLogSum

/-- Current-contracted directional Poisson action against a positive reference pair. -/
noncomputable def bidirectionalPoissonCurrentAction
    (referenceRates : BidirectionalPoissonRates) (netCurrent : ℝ) : ℝ :=
  bidirectionalPoissonDiscrimination
    (currentFibreProjection referenceRates netCurrent) referenceRates

/-- Exact whole-current-fibre decomposition into contracted action and residual discrimination. -/
theorem bidirectionalPoissonDiscrimination_eq_currentAction_add_residual
    {lawRates referenceRates : BidirectionalPoissonRates} {netCurrent : ℝ}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive)
    (hCurrent : lawRates.current = netCurrent) :
    bidirectionalPoissonDiscrimination lawRates referenceRates =
      bidirectionalPoissonCurrentAction referenceRates netCurrent +
        bidirectionalPoissonDiscrimination lawRates
          (currentFibreProjection referenceRates netCurrent) := by
  unfold bidirectionalPoissonCurrentAction
  apply bidirectionalPoissonDiscrimination_pythagorean hLaw hReference
    (currentFibreProjection_positive hReference netCurrent)
  · rw [currentFibreProjection_current, hCurrent]
  · exact currentFibreProjection_product hReference netCurrent

/-- The contracted action is a lower bound on the entire positive current fibre. -/
theorem bidirectionalPoissonCurrentAction_le_discrimination
    {lawRates referenceRates : BidirectionalPoissonRates} {netCurrent : ℝ}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive)
    (hCurrent : lawRates.current = netCurrent) :
    bidirectionalPoissonCurrentAction referenceRates netCurrent ≤
      bidirectionalPoissonDiscrimination lawRates referenceRates := by
  rw [bidirectionalPoissonDiscrimination_eq_currentAction_add_residual
    hLaw hReference hCurrent]
  exact le_add_of_nonneg_right
    (bidirectionalPoissonDiscrimination_nonneg hLaw
      (currentFibreProjection_positive hReference netCurrent))

/-- Equality with the contracted action holds exactly at the current-fibre projection. -/
theorem bidirectionalPoissonDiscrimination_eq_currentAction_iff
    {lawRates referenceRates : BidirectionalPoissonRates} {netCurrent : ℝ}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive)
    (hCurrent : lawRates.current = netCurrent) :
    bidirectionalPoissonDiscrimination lawRates referenceRates =
        bidirectionalPoissonCurrentAction referenceRates netCurrent ↔
      lawRates = currentFibreProjection referenceRates netCurrent := by
  rw [bidirectionalPoissonDiscrimination_eq_currentAction_add_residual
    hLaw hReference hCurrent]
  have hProjection := currentFibreProjection_positive hReference netCurrent
  constructor
  · intro hEqual
    apply (bidirectionalPoissonDiscrimination_eq_zero_iff hLaw hProjection).mp
    linarith
  · intro hEqual
    rw [hEqual,
      (bidirectionalPoissonDiscrimination_eq_zero_iff hProjection hProjection).2 rfl]
    ring

/-- The current-contracted action is nonnegative. -/
theorem bidirectionalPoissonCurrentAction_nonneg
    {referenceRates : BidirectionalPoissonRates} (hReference : referenceRates.Positive)
    (netCurrent : ℝ) :
    0 ≤ bidirectionalPoissonCurrentAction referenceRates netCurrent := by
  unfold bidirectionalPoissonCurrentAction
  exact bidirectionalPoissonDiscrimination_nonneg
    (currentFibreProjection_positive hReference netCurrent) hReference

/-- The current-contracted action vanishes exactly at the reference source current. -/
theorem bidirectionalPoissonCurrentAction_eq_zero_iff
    {referenceRates : BidirectionalPoissonRates} (hReference : referenceRates.Positive)
    (netCurrent : ℝ) :
    bidirectionalPoissonCurrentAction referenceRates netCurrent = 0 ↔
      netCurrent = referenceRates.current := by
  have hProjection := currentFibreProjection_positive hReference netCurrent
  constructor
  · intro hZero
    have hRates := (bidirectionalPoissonDiscrimination_eq_zero_iff
      hProjection hReference).mp hZero
    have hCurrent := congrArg BidirectionalPoissonRates.current hRates
    simpa using hCurrent
  · intro hCurrent
    unfold bidirectionalPoissonCurrentAction
    rw [hCurrent, currentFibreProjection_sourceCurrent hReference]
    exact (bidirectionalPoissonDiscrimination_eq_zero_iff hReference hReference).2 rfl

/-- Exact common-scale extensivity of the contracted current action. -/
theorem bidirectionalPoissonCurrentAction_commonScale
    {scale : ℝ} {referenceRates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hReference : referenceRates.Positive) (netCurrent : ℝ) :
    bidirectionalPoissonCurrentAction (referenceRates.commonScale scale)
        (scale * netCurrent) =
      scale * bidirectionalPoissonCurrentAction referenceRates netCurrent := by
  unfold bidirectionalPoissonCurrentAction
  rw [currentFibreProjection_commonScale hScale hReference]
  exact bidirectionalPoissonDiscrimination_commonScale hScale
    (currentFibreProjection_positive hReference netCurrent) hReference

/-- Reversing both the reference directions and the prescribed current preserves the contracted
action. -/
theorem bidirectionalPoissonCurrentAction_reversal
    {referenceRates : BidirectionalPoissonRates} (hReference : referenceRates.Positive)
    (netCurrent : ℝ) :
    bidirectionalPoissonCurrentAction referenceRates.swap (-netCurrent) =
      bidirectionalPoissonCurrentAction referenceRates netCurrent := by
  unfold bidirectionalPoissonCurrentAction
  rw [currentFibreProjection_swap hReference]
  exact bidirectionalPoissonDiscrimination_swap _ _

/-- Fixed-reference current fluctuation symmetry: reversing only the observed current exposes the
source affinity as the exact time-odd slope. -/
theorem bidirectionalPoissonCurrentAction_fluctuationSymmetry
    {referenceRates : BidirectionalPoissonRates} (hReference : referenceRates.Positive)
    (netCurrent : ℝ) :
    bidirectionalPoissonCurrentAction referenceRates netCurrent -
        bidirectionalPoissonCurrentAction referenceRates (-netCurrent) =
      -netCurrent * referenceRates.affinity := by
  unfold bidirectionalPoissonCurrentAction
  rw [currentFibreProjection_negCurrent hReference]
  simpa using bidirectionalPoissonDiscrimination_sub_swapLaw
    (currentFibreProjection_positive hReference netCurrent) hReference

namespace BidirectionalPoissonNNRates

/-- Multiply both actual nonnegative intensities by one common scale. -/
def commonScale (scale : ℝ≥0) (rates : BidirectionalPoissonNNRates) :
    BidirectionalPoissonNNRates where
  clockwise := scale * rates.clockwise
  counterclockwise := scale * rates.counterclockwise

/-- A strictly positive nonnegative-real scale preserves strict positivity. -/
theorem commonScale_positive
    {scale : ℝ≥0} {rates : BidirectionalPoissonNNRates}
    (hScale : 0 < scale) (hRates : rates.Positive) :
    (rates.commonScale scale).Positive :=
  ⟨mul_pos hScale hRates.1, mul_pos hScale hRates.2⟩

/-- Conversion to real rates commutes with common scaling. -/
@[simp]
theorem commonScale_toRealRates (scale : ℝ≥0) (rates : BidirectionalPoissonNNRates) :
    (rates.commonScale scale).toRealRates =
      rates.toRealRates.commonScale scale := rfl

end BidirectionalPoissonNNRates

/-- Exact common-scale extensivity of KL between actual normalized complete-history measures.
This theorem is finite and contains no particle-number limit. -/
theorem toReal_klDiv_bidirectionalPoissonHistoryMeasure_commonScale
    {scale : ℝ≥0} {lawRates referenceRates : BidirectionalPoissonNNRates}
    (hScale : 0 < scale) (hLaw : lawRates.Positive) (hReference : referenceRates.Positive) :
    (klDiv
      (bidirectionalPoissonHistoryMeasure (lawRates.commonScale scale))
      (bidirectionalPoissonHistoryMeasure (referenceRates.commonScale scale))).toReal =
      (scale : ℝ) *
        (klDiv (bidirectionalPoissonHistoryMeasure lawRates)
          (bidirectionalPoissonHistoryMeasure referenceRates)).toReal := by
  rw [toReal_klDiv_bidirectionalPoissonHistoryMeasure
      (lawRates.commonScale_positive hScale hLaw)
      (referenceRates.commonScale_positive hScale hReference),
    toReal_klDiv_bidirectionalPoissonHistoryMeasure hLaw hReference,
    BidirectionalPoissonNNRates.commonScale_toRealRates,
    BidirectionalPoissonNNRates.commonScale_toRealRates]
  exact bidirectionalPoissonDiscrimination_commonScale
    (by exact_mod_cast hScale)
    (BidirectionalPoissonNNRates.toRealRates_positive hLaw)
    (BidirectionalPoissonNNRates.toRealRates_positive hReference)

end FiniteMarkovProcesses.InformationTheory
