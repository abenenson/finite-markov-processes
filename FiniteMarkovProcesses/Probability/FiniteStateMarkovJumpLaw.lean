/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import FiniteMarkovProcesses.MeasureTheory.Measure.MapWithDensity
import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Finite-state Markov jump densities

This module defines finite-state rate generators and the canonical finite-horizon density of a
physical jump history against the counting--Lebesgue base measure. The density includes the
initial law, every physical jump rate, every dwell escape factor, and terminal survival.

The resulting object is deliberately named a density measure, not a probability law: its total
mass must be proved equal to one before it can be promoted to `ProbabilityMeasure`.

## Main results

- `FiniteStateMarkovGenerator`: a finite-state off-diagonal nonnegative rate generator.
- `finiteStateMarkovJumpSliceDensity`: the physical density on a fixed state word.
- `finiteStateMarkovJumpWordSliceMeasure`: the physical density measure on one fixed state word.
- `finiteStateMarkovJumpDensity`: the density on the unbounded history carrier.
- `finiteStateMarkovJumpDensityMeasure`: the candidate measure against the common base.
- `FiniteStateMarkovJumpDensityIsNormalized`: the explicit probability-promotion gate.
- `finiteStateMarkovJumpProbabilityMeasure`: promotion after that gate is discharged.
- `finiteStateMarkovJumpSliceDensity_eq_zero_of_self_jump`: repeated states have zero density.
- `finiteStateMarkovJumpDensityENNReal_ne_zero_imp_reduced`: nonzero density excludes virtual
  self-jumps.
- `ae_physicalAt_finiteStateMarkovJumpDensityMeasure`: the CTMC density law is concentrated on
  the exact ordered reduced carrier.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

/-- A finite-state continuous-time Markov generator represented by its nonnegative jump rates.
The diagonal is zero because escape rates are recorded separately. -/
@[ext]
structure FiniteStateMarkovGenerator (State : Type u) where
  rate : State → State → ℝ≥0
  rate_self : ∀ state, rate state state = 0

namespace FiniteStateMarkovGenerator

variable {State : Type u} [Fintype State]

/-- Total escape rate from one state. -/
def escapeRate (generator : FiniteStateMarkovGenerator State) (state : State) : ℝ≥0 :=
  ∑ nextState, generator.rate state nextState

/-- The escape rate is nonnegative after coercion to the reals. -/
theorem escapeRate_toReal_nonneg (generator : FiniteStateMarkovGenerator State) (state : State) :
    0 ≤ (generator.escapeRate state : ℝ) :=
  NNReal.coe_nonneg _

/-- If a row's escape rate vanishes, every jump rate in that row vanishes. -/
theorem rate_eq_zero_of_escapeRate_eq_zero
    (generator : FiniteStateMarkovGenerator State) (state target : State)
    (hEscape : generator.escapeRate state = 0) :
    generator.rate state target = 0 := by
  apply le_zero_iff.mp
  calc
    generator.rate state target ≤ ∑ nextState, generator.rate state nextState :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ target)
    _ = 0 := hEscape

/-- Two generators have the same directed support when every rate vanishes on exactly the same
ordered state pairs. -/
def HaveSameDirectedSupport
    (generator referenceGenerator : FiniteStateMarkovGenerator State) : Prop :=
  ∀ source target,
    generator.rate source target = 0 ↔ referenceGenerator.rate source target = 0

end FiniteStateMarkovGenerator

variable {State : Type u} [Fintype State]

/-- Two finite initial laws have identical point support. -/
def FiniteInitialDistributionsHaveSameSupport
    (initial referenceInitial : PMF State) : Prop :=
  ∀ state, initial state = 0 ↔ referenceInitial state = 0

/-- Product of all physical jump rates along one fixed state word. -/
def finiteStateMarkovJumpRateProduct (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) : ℝ :=
  ∏ i : Fin n, (generator.rate (states i.castSucc) (states i.succ) : ℝ)

/-- Integrated escape rate over all visited-state dwells, including the terminal dwell. -/
def finiteStateMarkovIntegratedEscape (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    (generator.escapeRate (states i) : ℝ) *
      FiniteJumpHistory.dwellTimeVector T times i

/-- Canonical physical CTMC density on a fixed jump-count/state-word slice. -/
noncomputable def finiteStateMarkovJumpSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) : ℝ :=
  (initial (states 0)).toReal * finiteStateMarkovJumpRateProduct generator states *
    Real.exp (-finiteStateMarkovIntegratedEscape generator T states times)

/-- The integrated escape rate is measurable as a function of the jump-time vector. -/
@[fun_prop]
theorem measurable_finiteStateMarkovIntegratedEscape
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) :
    Measurable (finiteStateMarkovIntegratedEscape generator T states) := by
  unfold finiteStateMarkovIntegratedEscape
  fun_prop

/-- The fixed-word physical jump density is measurable in its jump-time vector. -/
@[fun_prop]
theorem measurable_finiteStateMarkovJumpSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) :
    Measurable (finiteStateMarkovJumpSliceDensity initial generator T states) := by
  unfold finiteStateMarkovJumpSliceDensity
  fun_prop

/-- Canonical physical CTMC density on the unbounded finite-jump history carrier. -/
noncomputable def finiteStateMarkovJumpDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateMarkovJumpSliceDensity initial generator T states times

/-- The physical CTMC density is measurable on the sigma/disjoint-union history carrier. -/
theorem measurable_finiteStateMarkovJumpDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovJumpDensity initial generator T) := by
  rw [measurable_sigma_iff]
  intro n
  apply measurable_from_prod_countable_right
  intro states
  exact measurable_finiteStateMarkovJumpSliceDensity initial generator T states

/-- The nonnegative extended-real density used by `Measure.withDensity`. -/
noncomputable def finiteStateMarkovJumpDensityENNReal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ≥0∞ :=
  fun history => ENNReal.ofReal (finiteStateMarkovJumpDensity initial generator T history)

/-- The extended-real physical density is measurable. -/
theorem measurable_finiteStateMarkovJumpDensityENNReal
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovJumpDensityENNReal initial generator T) :=
  (measurable_finiteStateMarkovJumpDensity initial generator T).ennreal_ofReal

/-- The density on a fixed embedded state-word slice is literally the fixed-word density. -/
@[simp]
theorem finiteStateMarkovJumpDensityENNReal_embedJumpTimes
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    finiteStateMarkovJumpDensityENNReal initial generator T
        (embedJumpTimes n states times) =
      ENNReal.ofReal (finiteStateMarkovJumpSliceDensity initial generator T states times) :=
  rfl

/-- Candidate finite-state Markov jump measure. It is not promoted to a probability measure until
its total mass is proved to be one. -/
noncomputable def finiteStateMarkovJumpDensityMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  (finiteJumpHistoryBaseMeasure State T).withDensity
    (finiteStateMarkovJumpDensityENNReal initial generator T)

/-- Canonical physical CTMC density measure on one fixed jump-count and state-word slice. -/
noncomputable def finiteStateMarkovJumpWordSliceMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (eventCount : ℕ) (states : Fin (eventCount + 1) → State) :
    Measure (FiniteJumpHistory State) :=
  Measure.map (embedJumpTimes eventCount states)
    ((volume.restrict (orderedJumpTimes eventCount T)).withDensity
      (fun times ↦ ENNReal.ofReal
        (finiteStateMarkovJumpSliceDensity initial generator T states times)))

/-- Decompose the global physical density measure into its exact jump-count and state-word
slices. Each slice is a pushforward of ordered-time Lebesgue measure weighted by the corresponding
fixed-word density. -/
theorem finiteStateMarkovJumpDensityMeasure_eq_sum_slices
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator T =
      Measure.sum fun n : ℕ =>
        Measure.sum fun states : Fin (n + 1) → State =>
          Measure.map (embedJumpTimes n states)
            ((volume.restrict (orderedJumpTimes n T)).withDensity
              (fun times => ENNReal.ofReal
                (finiteStateMarkovJumpSliceDensity initial generator T states times))) := by
  unfold finiteStateMarkovJumpDensityMeasure finiteJumpHistoryBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext n
  unfold finiteJumpHistoryCountBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext states
  unfold finiteJumpHistorySliceBaseMeasure
  rw [← Measure.map_withDensity_comp _ (measurable_embedJumpTimes n states)
    (finiteStateMarkovJumpDensityENNReal initial generator T)
    (measurable_finiteStateMarkovJumpDensityENNReal initial generator T)]
  congr 1

/-- Decompose the global physical density measure into the named fixed-word slice measures. -/
theorem finiteStateMarkovJumpDensityMeasure_eq_sum_wordSliceMeasures
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpDensityMeasure initial generator T =
      Measure.sum fun eventCount : ℕ ↦
        Measure.sum fun states : Fin (eventCount + 1) → State ↦
          finiteStateMarkovJumpWordSliceMeasure
            initial generator T eventCount states := by
  rw [finiteStateMarkovJumpDensityMeasure_eq_sum_slices]
  rfl

/-- The candidate density measure is sigma-finite. This is weaker than probability
normalization. -/
noncomputable instance instSigmaFiniteFiniteStateMarkovJumpDensityMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    SigmaFinite (finiteStateMarkovJumpDensityMeasure initial generator T) := by
  unfold finiteStateMarkovJumpDensityMeasure finiteStateMarkovJumpDensityENNReal
  exact SigmaFinite.withDensity_ofReal
    (finiteStateMarkovJumpDensity initial generator T)

/-- Exact normalization condition for a finite-state physical jump density. -/
def FiniteStateMarkovJumpDensityIsNormalized
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) : Prop :=
  finiteStateMarkovJumpDensityMeasure initial generator T Set.univ = 1

/-- Promote a physical jump density to a probability measure only after exact normalization has
been proved. -/
noncomputable def finiteStateMarkovJumpProbabilityMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator T) :
    ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateMarkovJumpDensityMeasure initial generator T, ⟨hNormalized⟩⟩

/-- Probability promotion leaves the underlying density measure unchanged. -/
@[simp]
theorem finiteStateMarkovJumpProbabilityMeasure_toMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator T) :
    (finiteStateMarkovJumpProbabilityMeasure initial generator T hNormalized).toMeasure =
      finiteStateMarkovJumpDensityMeasure initial generator T :=
  rfl

/-- Every fixed-word physical density is nonnegative. -/
theorem finiteStateMarkovJumpSliceDensity_nonneg
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    0 ≤ finiteStateMarkovJumpSliceDensity initial generator T states times := by
  unfold finiteStateMarkovJumpSliceDensity
  apply mul_nonneg
  · apply mul_nonneg ENNReal.toReal_nonneg
    exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  · exact (Real.exp_pos _).le

/-- A repeated adjacent state is a virtual jump and therefore has zero physical density. -/
theorem finiteStateMarkovJumpSliceDensity_eq_zero_of_self_jump
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ)
    (i : Fin n) (hSelf : states i.castSucc = states i.succ) :
    finiteStateMarkovJumpSliceDensity initial generator T states times = 0 := by
  unfold finiteStateMarkovJumpSliceDensity finiteStateMarkovJumpRateProduct
  have hRate : (generator.rate (states i.castSucc) (states i.succ) : ℝ) = 0 := by
    rw [hSelf, generator.rate_self]
    rfl
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hRate]
  ring

/-- A history with nonzero finite-state CTMC density has no virtual self-jumps. -/
theorem finiteStateMarkovJumpDensityENNReal_ne_zero_imp_reduced
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State)
    (hDensity :
      finiteStateMarkovJumpDensityENNReal initial generator T history ≠ 0) :
    history.Reduced := by
  rcases history with ⟨jumpCount, states, times⟩
  intro index hSelf
  apply hDensity
  change ENNReal.ofReal
      (finiteStateMarkovJumpSliceDensity initial generator T states times) = 0
  rw [finiteStateMarkovJumpSliceDensity_eq_zero_of_self_jump
    initial generator T states times index hSelf, ENNReal.ofReal_zero]

/-- The canonical finite-state CTMC density measure is concentrated on histories with strictly
ordered event times and genuine state changes. -/
theorem ae_physicalAt_finiteStateMarkovJumpDensityMeasure
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ∀ᵐ history ∂ finiteStateMarkovJumpDensityMeasure initial generator T,
      history.PhysicalAt T := by
  unfold finiteStateMarkovJumpDensityMeasure
  rw [ae_withDensity_iff
    (measurable_finiteStateMarkovJumpDensityENNReal initial generator T)]
  filter_upwards [FiniteJumpHistory.ae_orderedBefore_finiteJumpHistoryBaseMeasure
    (State := State) T] with history hOrdered
  intro hDensity
  exact ⟨hOrdered,
    finiteStateMarkovJumpDensityENNReal_ne_zero_imp_reduced
      initial generator T history hDensity⟩

/-- Common initial and directed support give identical zero sets for every fixed-word path
density. -/
theorem finiteStateMarkovJumpSliceDensity_eq_zero_iff
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (times : Fin n → ℝ) :
    finiteStateMarkovJumpSliceDensity initial generator T states times = 0 ↔
      finiteStateMarkovJumpSliceDensity referenceInitial referenceGenerator T states times = 0 := by
  have hInitialZero :
      (initial (states 0)).toReal = 0 ↔ (referenceInitial (states 0)).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, initial.apply_ne_top,
      referenceInitial.apply_ne_top, or_false]
    exact hInitialSupport (states 0)
  have hRateZero (i : Fin n) :
      (generator.rate (states i.castSucc) (states i.succ) : ℝ) = 0 ↔
        (referenceGenerator.rate (states i.castSucc) (states i.succ) : ℝ) = 0 := by
    norm_cast
    exact hRateSupport _ _
  have hProductZero :
      finiteStateMarkovJumpRateProduct generator states = 0 ↔
        finiteStateMarkovJumpRateProduct referenceGenerator states = 0 := by
    unfold finiteStateMarkovJumpRateProduct
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    exact exists_congr fun i => hRateZero i
  unfold finiteStateMarkovJumpSliceDensity
  simp only [mul_eq_zero, Real.exp_ne_zero, or_false]
  exact or_congr hInitialZero hProductZero

/-- Common support gives identical zero sets for the densities on the unbounded history
carrier. -/
theorem finiteStateMarkovJumpDensity_eq_zero_iff
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) (history : FiniteJumpHistory State) :
    finiteStateMarkovJumpDensity initial generator T history = 0 ↔
      finiteStateMarkovJumpDensity referenceInitial referenceGenerator T history = 0 := by
  rcases history with ⟨n, states, times⟩
  exact finiteStateMarkovJumpSliceDensity_eq_zero_iff
    hInitialSupport hRateSupport T states times

end FiniteMarkovProcesses.Probability
