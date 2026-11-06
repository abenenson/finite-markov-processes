/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedReducedLaw
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedSelfEventResummation

/-!
# Finite-history density of a uniformized Markov trajectory

This module defines the common-clock density on the existing `FiniteJumpHistory` carrier before
virtual self-events are deleted. Every event contributes its clock rate times uniformized
transition probability, while the complete horizon contributes common-clock survival.

Off-diagonal event intensities are exactly the physical directed rates; diagonal intensities are
exactly the unused self-event rates. The candidate density measure is kept distinct from the
normalized stopped uniformized law until their slice-by-slice identification is proved.

## Main Results

- `FiniteStateMarkovGenerator.uniformizedTransitionIntensity`: real event intensity.
- `finiteStateMarkovUniformizedSliceDensity`: fixed-word common-clock history density.
- `finiteStateMarkovUniformizedDensityMeasure`: candidate density against the common base.
- `finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices`: exact count/state-word
  decomposition.
- `FiniteStateUniformizedStoppedLawHasHistoryDensity`: named stopped-law density obligation.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- Real intensity of one uniformized event, including its possible virtual self-event. -/
noncomputable def uniformizedTransitionIntensity
    (generator : FiniteStateMarkovGenerator State) (source target : State) : ℝ :=
  (generator.uniformizationRate : ℝ) *
    (generator.uniformizedTransitionPMF source target).toReal

/-- Every off-diagonal uniformized event intensity is exactly its physical directed rate. -/
theorem uniformizedTransitionIntensity_of_ne
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hNe : source ≠ target) :
    generator.uniformizedTransitionIntensity source target =
      generator.rate source target := by
  rw [uniformizedTransitionIntensity,
    generator.uniformizedTransitionPMF_toReal_of_ne hNe]
  field_simp [generator.uniformizationRate_pos.ne']

/-- Every diagonal uniformized event intensity is exactly the unused self-event rate. -/
theorem uniformizedTransitionIntensity_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.uniformizedTransitionIntensity state state =
      generator.uniformizedSelfEventRate state :=
  generator.uniformizationRate_mul_uniformizedTransitionPMF_toReal_self state

end FiniteStateMarkovGenerator

/-- Product of all common-clock event intensities along one virtual state word. -/
noncomputable def finiteStateMarkovUniformizedTransitionIntensityProduct
    (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) : ℝ :=
  ∏ index : Fin n,
    generator.uniformizedTransitionIntensity
      (states index.castSucc) (states index.succ)

/-- Common-clock density on one fixed virtual-event state word. It is constant over the ordered
event-time simplex because the clock rate is state independent. -/
noncomputable def finiteStateMarkovUniformizedSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (_times : Fin n → ℝ) : ℝ :=
  (initial (states 0)).toReal *
    finiteStateMarkovUniformizedTransitionIntensityProduct generator states *
      Real.exp (-((generator.uniformizationRate : ℝ) * T))

/-- Common-clock density on the unbounded virtual finite-history carrier. -/
noncomputable def finiteStateMarkovUniformizedDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ
  | ⟨_, states, times⟩ =>
      finiteStateMarkovUniformizedSliceDensity initial generator T states times

/-- The virtual common-clock density is measurable. -/
theorem measurable_finiteStateMarkovUniformizedDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovUniformizedDensity initial generator T) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  exact measurable_const

/-- Nonnegative extended-real form of the virtual common-clock density. -/
noncomputable def finiteStateMarkovUniformizedDensityENNReal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ≥0∞ :=
  fun history ↦ ENNReal.ofReal (finiteStateMarkovUniformizedDensity initial generator T history)

/-- The extended-real virtual common-clock density is measurable. -/
theorem measurable_finiteStateMarkovUniformizedDensityENNReal
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovUniformizedDensityENNReal initial generator T) :=
  (measurable_finiteStateMarkovUniformizedDensity initial generator T).ennreal_ofReal

/-- Candidate virtual-history density measure against the same counting--Lebesgue base used by
the canonical physical CTMC law. -/
noncomputable def finiteStateMarkovUniformizedDensityMeasure
    [MeasurableSpace State] (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  (finiteJumpHistoryBaseMeasure State T).withDensity
    (finiteStateMarkovUniformizedDensityENNReal initial generator T)

/-- Decompose the candidate uniformized density measure into its exact event-count and virtual
state-word slices. -/
theorem finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovUniformizedDensityMeasure initial generator T =
      Measure.sum fun n : ℕ ↦
        Measure.sum fun states : Fin (n + 1) → State ↦
          Measure.map (embedJumpTimes n states)
            ((volume.restrict (orderedJumpTimes n T)).withDensity
              (fun times ↦ ENNReal.ofReal
                (finiteStateMarkovUniformizedSliceDensity
                  initial generator T states times))) := by
  unfold finiteStateMarkovUniformizedDensityMeasure finiteJumpHistoryBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext n
  unfold finiteJumpHistoryCountBaseMeasure
  rw [withDensity_sum]
  congr 1
  funext states
  unfold finiteJumpHistorySliceBaseMeasure
  rw [← Measure.map_withDensity_comp _ (measurable_embedJumpTimes n states)
    (finiteStateMarkovUniformizedDensityENNReal initial generator T)
    (measurable_finiteStateMarkovUniformizedDensityENNReal initial generator T)]
  congr 1

/-- Named remaining density theorem: the normalized stopped uniformized tape has the explicit
common-clock density on every finite virtual-event slice. -/
def FiniteStateUniformizedStoppedLawHasHistoryDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) : Prop :=
  FiniteStateMarkovUniformizedStoppedLaw.finiteStateUniformizedStoppedHistoryMeasure
      initial generator T =
    finiteStateMarkovUniformizedDensityMeasure initial generator T

end FiniteMarkovProcesses.Probability
