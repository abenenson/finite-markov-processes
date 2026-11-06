/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.BidirectionalPoissonAction

/-!
# Force-reactivity coordinates for bidirectional Poisson rates

This file classifies strictly positive bidirectional Poisson rates by their directional affinity
and symmetric reactivity. The two coordinates reconstruct both rates exactly. Affinity alone
identifies only a positive common-scale orbit, including on the detailed-balance diagonal.

The results concern integrated intensities. A physical generator additionally requires an
independently fixed clock convention.

## Main results

- `forceReactivity_reconstruction`: affinity and reactivity reconstruct both rates.
- `eq_iff_affinity_eq_and_reactivity_eq`: the two coordinates identify a positive rate pair.
- `affinity_eq_iff_exists_positive_commonScale`: equal affinity is exactly common scaling.
- `equilibriumAffinity_nonidentification`: zero affinity does not identify reactivity or rates.
-/

namespace FiniteMarkovProcesses.InformationTheory

namespace BidirectionalPoissonRates

/-- Reconstruct a positive rate pair from its affinity and reactivity coordinates. -/
theorem forceReactivity_reconstruction
    (rates : BidirectionalPoissonRates) (hRates : rates.Positive) :
    rates =
      ⟨rates.reactivity * Real.exp (rates.affinity / 2),
        rates.reactivity * Real.exp (-rates.affinity / 2)⟩ := by
  ext
  · exact (reactivity_mul_exp_half_affinity_eq_clockwise hRates).symm
  · exact (reactivity_mul_exp_neg_half_affinity_eq_counterclockwise hRates).symm

/-- Equal affinity and reactivity identify two positive rate pairs literally. -/
theorem eq_of_affinity_eq_of_reactivity_eq
    {first second : BidirectionalPoissonRates}
    (hFirst : first.Positive) (hSecond : second.Positive)
    (hAffinity : first.affinity = second.affinity)
    (hReactivity : first.reactivity = second.reactivity) :
    first = second := by
  ext
  · calc
      first.clockwise = first.reactivity * Real.exp (first.affinity / 2) :=
        (reactivity_mul_exp_half_affinity_eq_clockwise hFirst).symm
      _ = second.reactivity * Real.exp (second.affinity / 2) := by
        rw [hAffinity, hReactivity]
      _ = second.clockwise :=
        reactivity_mul_exp_half_affinity_eq_clockwise hSecond
  · calc
      first.counterclockwise = first.reactivity * Real.exp (-first.affinity / 2) :=
        (reactivity_mul_exp_neg_half_affinity_eq_counterclockwise hFirst).symm
      _ = second.reactivity * Real.exp (-second.affinity / 2) := by
        rw [hAffinity, hReactivity]
      _ = second.counterclockwise :=
        reactivity_mul_exp_neg_half_affinity_eq_counterclockwise hSecond

/-- Positive bidirectional rates are equal exactly when both coordinates are equal. -/
theorem eq_iff_affinity_eq_and_reactivity_eq
    {first second : BidirectionalPoissonRates}
    (hFirst : first.Positive) (hSecond : second.Positive) :
    first = second ↔
      first.affinity = second.affinity ∧ first.reactivity = second.reactivity := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hAffinity, hReactivity⟩
    exact eq_of_affinity_eq_of_reactivity_eq hFirst hSecond hAffinity hReactivity

/-- Multiply both directional rates by one common kinetic scale. -/
def commonScale (scale : ℝ) (rates : BidirectionalPoissonRates) :
    BidirectionalPoissonRates where
  clockwise := scale * rates.clockwise
  counterclockwise := scale * rates.counterclockwise

/-- A positive common scale preserves positivity of both directional rates. -/
theorem commonScale_positive
    {scale : ℝ} {rates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hRates : rates.Positive) :
    (commonScale scale rates).Positive :=
  ⟨mul_pos hScale hRates.1, mul_pos hScale hRates.2⟩

/-- A positive common kinetic scaling preserves directional affinity. -/
theorem commonScale_affinity
    {scale : ℝ} {rates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hRates : rates.Positive) :
    (commonScale scale rates).affinity = rates.affinity := by
  unfold commonScale affinity
  congr 1
  field_simp [hScale.ne', hRates.2.ne']

/-- Reactivity scales linearly under a positive common kinetic scaling. -/
theorem commonScale_reactivity
    {scale : ℝ} {rates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hRates : rates.Positive) :
    (commonScale scale rates).reactivity = scale * rates.reactivity := by
  have hScaled := commonScale_positive hScale hRates
  have hAffinity := commonScale_affinity hScale hRates
  have hProduct :
      (commonScale scale rates).reactivity * Real.exp (rates.affinity / 2) =
        (scale * rates.reactivity) * Real.exp (rates.affinity / 2) := by
    calc
      (commonScale scale rates).reactivity * Real.exp (rates.affinity / 2) =
          (commonScale scale rates).reactivity *
            Real.exp ((commonScale scale rates).affinity / 2) := by rw [hAffinity]
      _ = (commonScale scale rates).clockwise :=
        reactivity_mul_exp_half_affinity_eq_clockwise hScaled
      _ = scale * rates.clockwise := rfl
      _ = scale * (rates.reactivity * Real.exp (rates.affinity / 2)) := by
        rw [reactivity_mul_exp_half_affinity_eq_clockwise hRates]
      _ = (scale * rates.reactivity) * Real.exp (rates.affinity / 2) := by ring
  nlinarith [Real.exp_pos (rates.affinity / 2)]

/-- A common scale other than one changes a positive rate pair. -/
theorem commonScale_ne_self
    {scale : ℝ} {rates : BidirectionalPoissonRates}
    (hScaleNe : scale ≠ 1) (hRates : rates.Positive) :
    commonScale scale rates ≠ rates := by
  intro hEqual
  have hClockwise := congrArg BidirectionalPoissonRates.clockwise hEqual
  dsimp [commonScale] at hClockwise
  apply hScaleNe
  apply mul_right_cancel₀ hRates.1.ne'
  simpa using hClockwise

/-- A nontrivial positive common scale changes the symmetric reactivity. -/
theorem commonScale_reactivity_ne
    {scale : ℝ} {rates : BidirectionalPoissonRates}
    (hScale : 0 < scale) (hScaleNe : scale ≠ 1) (hRates : rates.Positive) :
    (commonScale scale rates).reactivity ≠ rates.reactivity := by
  rw [commonScale_reactivity hScale hRates]
  intro hEqual
  apply hScaleNe
  apply mul_right_cancel₀ (reactivity_pos rates).ne'
  simpa using hEqual

/-- Equal affinity of positive pairs is exactly equality up to a positive common scale. -/
theorem affinity_eq_iff_exists_positive_commonScale
    {first second : BidirectionalPoissonRates}
    (hFirst : first.Positive) (hSecond : second.Positive) :
    first.affinity = second.affinity ↔
      ∃ scale, 0 < scale ∧ second = commonScale scale first := by
  constructor
  · intro hAffinity
    let scale := second.reactivity / first.reactivity
    have hScale : 0 < scale := div_pos (reactivity_pos second) (reactivity_pos first)
    refine ⟨scale, hScale, ?_⟩
    apply eq_of_affinity_eq_of_reactivity_eq hSecond (commonScale_positive hScale hFirst)
    · exact hAffinity.symm.trans (commonScale_affinity hScale hFirst).symm
    · rw [commonScale_reactivity hScale hFirst]
      dsimp [scale]
      field_simp [ne_of_gt (reactivity_pos first)]
  · rintro ⟨scale, hScale, rfl⟩
    exact (commonScale_affinity hScale hFirst).symm

/-- Frozen driven witness: equal affinity alone does not identify rates or reactivity. -/
theorem drivenAffinity_nonidentification :
    ∃ first second : BidirectionalPoissonRates,
      first.Positive ∧ second.Positive ∧
        first.affinity = second.affinity ∧
        first.reactivity ≠ second.reactivity ∧ first ≠ second := by
  let first : BidirectionalPoissonRates := ⟨2, 1⟩
  let second : BidirectionalPoissonRates := ⟨4, 2⟩
  have hFirst : first.Positive := by norm_num [first, Positive]
  have hSecond : second.Positive := by norm_num [second, Positive]
  have hAffinity : first.affinity = second.affinity := by
    norm_num [first, second, affinity]
  have hDistinct : first ≠ second := by
    intro hEqual
    have hClockwise := congrArg BidirectionalPoissonRates.clockwise hEqual
    norm_num [first, second] at hClockwise
  have hReactivity : first.reactivity ≠ second.reactivity := by
    intro hEqual
    exact hDistinct <|
      eq_of_affinity_eq_of_reactivity_eq hFirst hSecond hAffinity hEqual
  exact ⟨first, second, hFirst, hSecond, hAffinity, hReactivity, hDistinct⟩

/-- Frozen equilibrium witness: zero affinity leaves the positive kinetic scale unidentified. -/
theorem equilibriumAffinity_nonidentification :
    ∃ first second : BidirectionalPoissonRates,
      first.Positive ∧ second.Positive ∧
        first.affinity = 0 ∧ second.affinity = 0 ∧
        first.reactivity ≠ second.reactivity ∧ first ≠ second := by
  let first : BidirectionalPoissonRates := ⟨1, 1⟩
  let second : BidirectionalPoissonRates := ⟨2, 2⟩
  have hFirst : first.Positive := by norm_num [first, Positive]
  have hSecond : second.Positive := by norm_num [second, Positive]
  have hFirstAffinity : first.affinity = 0 := by norm_num [first, affinity]
  have hSecondAffinity : second.affinity = 0 := by norm_num [second, affinity]
  have hDistinct : first ≠ second := by
    intro hEqual
    have hClockwise := congrArg BidirectionalPoissonRates.clockwise hEqual
    norm_num [first, second] at hClockwise
  have hReactivity : first.reactivity ≠ second.reactivity := by
    intro hEqual
    apply hDistinct
    exact eq_of_affinity_eq_of_reactivity_eq hFirst hSecond
      (hFirstAffinity.trans hSecondAffinity.symm) hEqual
  exact ⟨first, second, hFirst, hSecond, hFirstAffinity, hSecondAffinity,
    hReactivity, hDistinct⟩

end BidirectionalPoissonRates

end FiniteMarkovProcesses.InformationTheory
