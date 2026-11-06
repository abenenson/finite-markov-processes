/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Volume of ordered finite event times

This module computes the Lebesgue volume of the open event-time simplex
`0 < t₁ < ... < tₙ < T`. Splitting off the last event time gives a measurable recursive
disintegration; integrating the induction hypothesis gives `T ^ n / n!` at every nonnegative
horizon.

## Main Results

- `strictMono_snoc_iff`: strict monotonicity after adjoining a final coordinate.
- `volume_orderedJumpTimes_succ`: last-time disintegration of the ordered simplex.
- `volume_orderedJumpTimes`: exact ordered-simplex volume.
- `volume_orderedTimesInInterval`: exact ordered-simplex volume inside an arbitrary interval.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Splitting off the last coordinate preserves strict monotonicity exactly when the preceding
word is strictly monotone and lies strictly below the last coordinate. -/
theorem strictMono_snoc_iff {n : ℕ} (values : Fin n → ℝ) (lastValue : ℝ) :
    StrictMono (Fin.snoc values lastValue) ↔
      StrictMono values ∧ ∀ index, values index < lastValue := by
  constructor
  · intro hMono
    constructor
    · simpa only [Function.comp_def, Fin.snoc_castSucc] using
        hMono.comp Fin.strictMono_castSucc
    · intro index
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hMono (Fin.castSucc_lt_last index)
  · rintro ⟨hMono, hLast⟩
    cases n with
    | zero =>
        rw [Fin.strictMono_iff_lt_succ]
        intro index
        exact Fin.elim0 index
    | succ n =>
        rw [Fin.strictMono_iff_lt_succ]
        intro index
        refine Fin.lastCases ?_ (fun priorIndex ↦ ?_) index
        · simpa using hLast (Fin.last n)
        · rw [Fin.snoc_castSucc]
          have hIndex : priorIndex.castSucc.succ = priorIndex.succ.castSucc := Fin.ext rfl
          rw [hIndex, Fin.snoc_castSucc]
          exact Fin.strictMono_iff_lt_succ.mp hMono priorIndex

/-- Pairs consisting of a final event time and an earlier ordered event-time word. -/
def orderedJumpTimesLastSection (n : ℕ) (T : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {coordinates |
    coordinates.1 ∈ Ioo 0 T ∧
      coordinates.2 ∈ orderedJumpTimes n coordinates.1}

/-- The last-time disintegration set is measurable. -/
theorem measurableSet_orderedJumpTimesLastSection (n : ℕ) (T : ℝ) :
    MeasurableSet (orderedJumpTimesLastSection n T) := by
  unfold orderedJumpTimesLastSection orderedJumpTimes
  apply Measurable.setOf
  apply Measurable.and
  · exact ((measurable_const.lt measurable_fst).and
      (measurable_fst.lt measurable_const))
  · apply Measurable.and
    · apply Measurable.forall
      intro index
      exact (measurable_const.lt ((measurable_pi_apply index).comp measurable_snd)).and
        (((measurable_pi_apply index).comp measurable_snd).lt measurable_fst)
    · apply Measurable.forall
      intro first
      apply Measurable.forall
      intro second
      exact measurable_const.imp <|
        ((measurable_pi_apply first).comp measurable_snd).lt
          ((measurable_pi_apply second).comp measurable_snd)

/-- Splitting off the last coordinate sends the ordered simplex to its last-time
disintegration. -/
theorem piFinSuccAbove_preimage_orderedJumpTimesLastSection (n : ℕ) (T : ℝ) :
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)) ⁻¹'
        orderedJumpTimesLastSection n T =
      orderedJumpTimes (n + 1) T := by
  ext times
  rw [Set.mem_preimage]
  change (times (Fin.last n), fun index ↦ times ((Fin.last n).succAbove index)) ∈
      orderedJumpTimesLastSection n T ↔ _
  simp only [Fin.succAbove_last]
  unfold orderedJumpTimesLastSection orderedJumpTimes
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  have hSnoc :
      Fin.snoc (fun index ↦ times index.castSucc) (times (Fin.last n)) = times := by
    funext index
    refine Fin.lastCases ?_ (fun priorIndex ↦ ?_) index <;> simp
  constructor
  · rintro ⟨hLast, hBounds, hMono⟩
    constructor
    · intro index
      refine Fin.lastCases ?_ (fun priorIndex ↦ ?_) index
      · exact hLast
      · exact ⟨(hBounds priorIndex).1, (hBounds priorIndex).2.trans hLast.2⟩
    · rw [← hSnoc]
      exact (strictMono_snoc_iff
        (fun index ↦ times index.castSucc) (times (Fin.last n))).2
          ⟨hMono, fun index ↦ (hBounds index).2⟩
  · rintro ⟨hBounds, hMono⟩
    have hSnocMono :
        StrictMono (Fin.snoc
          (fun index ↦ times index.castSucc) (times (Fin.last n))) := by
      rwa [hSnoc]
    have hParts := (strictMono_snoc_iff
      (fun index ↦ times index.castSucc) (times (Fin.last n))).1 hSnocMono
    exact ⟨hBounds (Fin.last n),
      fun index ↦
        ⟨(hBounds index.castSucc).1, hMono (Fin.castSucc_lt_last index)⟩,
      hParts.1⟩

/-- The volume of a nonempty ordered event-time simplex is the integral of the preceding
simplex volume over its final event time. -/
theorem volume_orderedJumpTimes_succ (n : ℕ) (T : ℝ) :
    volume (orderedJumpTimes (n + 1) T) =
      ∫⁻ lastTime : ℝ in Ioo 0 T,
        volume (orderedJumpTimes n lastTime) := by
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  have hPreserving := volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)
  calc
    volume (orderedJumpTimes (n + 1) T) =
        volume (split ⁻¹' orderedJumpTimesLastSection n T) := by
      rw [piFinSuccAbove_preimage_orderedJumpTimesLastSection]
    _ = volume (orderedJumpTimesLastSection n T) :=
      hPreserving.measure_preimage
        (measurableSet_orderedJumpTimesLastSection n T).nullMeasurableSet
    _ = ∫⁻ lastTime : ℝ,
        volume (Prod.mk lastTime ⁻¹' orderedJumpTimesLastSection n T) := by
      exact Measure.prod_apply (measurableSet_orderedJumpTimesLastSection n T)
    _ = ∫⁻ lastTime : ℝ in Ioo 0 T,
        volume (orderedJumpTimes n lastTime) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      congr 1
      funext lastTime
      have hFiber :
          Prod.mk lastTime ⁻¹' orderedJumpTimesLastSection n T =
            if lastTime ∈ Ioo (0 : ℝ) T then
              orderedJumpTimes n lastTime else ∅ := by
        ext earlierTimes
        simp [orderedJumpTimesLastSection]
      rw [hFiber]
      by_cases hLast : lastTime ∈ Ioo (0 : ℝ) T
      · simp [hLast]
      · simp [hLast]

/-- Integrating the `n`th power over the positive horizon, with the factorial normalization from
the preceding simplex, gives the next simplex coefficient. -/
theorem lintegral_Ioo_pow_div_factorial (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ time : ℝ in Ioo 0 T,
        ENNReal.ofReal (time ^ n / n.factorial) =
      ENNReal.ofReal (T ^ (n + 1) / (n + 1).factorial) := by
  have hIntegrable :
      Integrable (fun time : ℝ ↦ time ^ n / n.factorial)
        (volume.restrict (Ioo 0 T)) := by
    exact ((continuous_pow n).div_const (n.factorial : ℝ)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hNonnegative :
      0 ≤ᶠ[ae (volume.restrict (Ioo 0 T))]
        fun time : ℝ ↦ time ^ n / n.factorial := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
    exact div_nonneg (pow_nonneg hTime.1.le n) (Nat.cast_nonneg n.factorial)
  rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hNonnegative]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hT]
  rw [intervalIntegral.integral_div, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The open ordered event-time simplex has exact Lebesgue volume `T ^ n / n!` at every
nonnegative horizon, including the zero-dimensional slice. -/
theorem volume_orderedJumpTimes (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    volume (orderedJumpTimes n T) =
      ENNReal.ofReal (T ^ n / n.factorial) := by
  induction n generalizing T with
  | zero =>
      have hStrict : ∀ times : Fin 0 → ℝ, StrictMono times := by
        intro times first
        exact Fin.elim0 first
      rw [show orderedJumpTimes 0 T = Set.univ by
        ext times
        simp [orderedJumpTimes, hStrict times]]
      have hPreserving := volume_preserving_pi_empty (fun _ : Fin 0 ↦ ℝ)
      have hUniv := hPreserving.measure_preimage
        (s := (Set.univ : Set Unit)) MeasurableSet.univ.nullMeasurableSet
      calc
        (volume : Measure (Fin 0 → ℝ)) Set.univ =
            (volume : Measure Unit) Set.univ := by simpa using hUniv
        _ = 1 := by
          change Measure.dirac () Set.univ = 1
          simp
        _ = ENNReal.ofReal (T ^ 0 / (0 : ℕ).factorial) := by simp
  | succ n inductionHypothesis =>
      rw [volume_orderedJumpTimes_succ]
      rw [← lintegral_indicator measurableSet_Ioo]
      have hIntegrand :
          (Ioo (0 : ℝ) T).indicator
              (fun time ↦ volume (orderedJumpTimes n time)) =
            (Ioo (0 : ℝ) T).indicator
              (fun time ↦ ENNReal.ofReal (time ^ n / n.factorial)) := by
        funext time
        by_cases hTime : time ∈ Ioo (0 : ℝ) T
        · simp [hTime, inductionHypothesis time hTime.1.le]
        · simp [hTime]
      rw [hIntegrand, lintegral_indicator measurableSet_Ioo]
      exact lintegral_Ioo_pow_div_factorial n T hT

/-- Strictly ordered event times inside an arbitrary open interval. -/
def orderedTimesInInterval (n : ℕ) (lower upper : ℝ) : Set (Fin n → ℝ) :=
  {times | (∀ index, lower < times index ∧ times index < upper) ∧ StrictMono times}

/-- An arbitrary ordered-time interval is measurable. -/
theorem measurableSet_orderedTimesInInterval (n : ℕ) (lower upper : ℝ) :
    MeasurableSet (orderedTimesInInterval n lower upper) := by
  unfold orderedTimesInInterval
  apply Measurable.setOf
  apply Measurable.and
  · apply Measurable.forall
    intro index
    exact (measurable_const.lt (measurable_pi_apply index)).and
      ((measurable_pi_apply index).lt measurable_const)
  · apply Measurable.forall
    intro first
    apply Measurable.forall
    intro second
    exact measurable_const.imp
      ((measurable_pi_apply first).lt (measurable_pi_apply second))

/-- Translating the zero-based ordered simplex gives the ordered simplex in an arbitrary
interval. -/
theorem translate_preimage_orderedTimesInInterval (n : ℕ) (lower upper : ℝ) :
    (fun times : Fin n → ℝ ↦ times + fun _ ↦ lower) ⁻¹'
        orderedTimesInInterval n lower upper =
      orderedJumpTimes n (upper - lower) := by
  ext times
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨hBounds, hMono⟩
    constructor
    · intro index
      have hBound := hBounds index
      change lower < times index + lower ∧ times index + lower < upper at hBound
      constructor <;> linarith
    · intro first second hLess
      have hValue := hMono hLess
      change times first + lower < times second + lower at hValue
      linarith
  · rintro ⟨hBounds, hMono⟩
    constructor
    · intro index
      have hBound := hBounds index
      change lower < times index + lower ∧ times index + lower < upper
      constructor <;> linarith
    · intro first second hLess
      change times first + lower < times second + lower
      have hValue := hMono hLess
      linarith

/-- The ordered-time simplex inside `[lower, upper]` has volume
`(upper - lower) ^ n / n!`. -/
theorem volume_orderedTimesInInterval
    (n : ℕ) (lower upper : ℝ) (hBounds : lower ≤ upper) :
    volume (orderedTimesInInterval n lower upper) =
      ENNReal.ofReal ((upper - lower) ^ n / n.factorial) := by
  let translate : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun times ↦ times + fun _ ↦ lower
  have hMeasurable : Measurable translate := by
    fun_prop
  have hPreserving : MeasurePreserving translate volume volume := by
    refine ⟨hMeasurable, ?_⟩
    exact map_add_right_eq_self volume (fun _ : Fin n ↦ lower)
  calc
    volume (orderedTimesInInterval n lower upper) =
        volume (translate ⁻¹' orderedTimesInInterval n lower upper) :=
      (hPreserving.measure_preimage
        (measurableSet_orderedTimesInInterval n lower upper).nullMeasurableSet).symm
    _ = volume (orderedJumpTimes n (upper - lower)) := by
      rw [show translate ⁻¹' orderedTimesInInterval n lower upper =
        orderedJumpTimes n (upper - lower) from
          translate_preimage_orderedTimesInInterval n lower upper]
    _ = _ := volume_orderedJumpTimes n (upper - lower) (sub_nonneg.mpr hBounds)

end FiniteMarkovProcesses.Probability
