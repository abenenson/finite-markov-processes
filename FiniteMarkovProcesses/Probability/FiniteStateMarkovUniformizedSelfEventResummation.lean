/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformization

/-!
# Resumming virtual self-events in finite-state uniformization

This module isolates the analytic kernel of the uniformization-to-physical-law theorem. At one
state, the unused part of the common clock is the virtual self-event rate. Summing every possible
number of ordered self-events over a dwell exponentiates that unused rate and converts common-clock
survival exactly into physical escape survival.

The theorem is pointwise in one dwell. The full history-law identification must additionally
factor inserted event-time simplices across all physical dwells and sum the corresponding fibres.

## Main Results

- `FiniteStateMarkovGenerator.uniformizedSelfEventRate`: unused common-clock rate at one state.
- `uniformizationRate_mul_uniformizedTransitionPMF_toReal_self`: exact clock-times-self-probability
  identity.
- `uniformizedSelfEventResummation`: exact conversion from virtual to physical dwell survival.
- `uniformizedSelfEventResummation_finite`: simultaneous conversion across a finite dwell vector.
- `uniformizedSelfEventResummation_finite_ennreal`: the same conversion in the nonnegative
  extended-real coefficients used by density measures.
- `finiteStateMarkovUniformizedSelfEventFibreWeight_resums_to_jumpSliceDensity`: the complete
  fixed-physical-history fibre coefficient is the canonical physical density.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- Unused common-clock rate represented by virtual self-events at one state. -/
noncomputable def uniformizedSelfEventRate
    (generator : FiniteStateMarkovGenerator State) (state : State) : ℝ≥0 :=
  generator.uniformizationRate - generator.escapeRate state

omit [DecidableEq State] in
/-- Real coercion of the virtual self-event rate. -/
theorem coe_uniformizedSelfEventRate
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    (generator.uniformizedSelfEventRate state : ℝ) =
      (generator.uniformizationRate : ℝ) - (generator.escapeRate state : ℝ) := by
  rw [uniformizedSelfEventRate, NNReal.coe_sub]
  exact generator.escapeRate_le_uniformizationRate state

/-- The common clock rate times the virtual self-transition probability is exactly the unused
self-event rate. -/
theorem uniformizationRate_mul_uniformizedTransitionPMF_toReal_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    (generator.uniformizationRate : ℝ) *
        (generator.uniformizedTransitionPMF state state).toReal =
      generator.uniformizedSelfEventRate state := by
  rw [generator.uniformizedTransitionPMF_toReal_self,
    generator.coe_uniformizedSelfEventRate]
  field_simp [generator.uniformizationRate_pos.ne']

end FiniteStateMarkovGenerator

/-- The ordered-volume weights of repeated virtual self-events sum to the exponential of their
integrated rate. -/
theorem hasSum_uniformizedSelfEventVolumeWeight (selfEventRate dwell : ℝ) :
    HasSum (fun eventCount : ℕ ↦
      (selfEventRate * dwell) ^ eventCount / eventCount.factorial)
      (Real.exp (selfEventRate * dwell)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp (selfEventRate * dwell)

/-- The sum of all ordered virtual self-event volume weights is the corresponding exponential. -/
theorem tsum_uniformizedSelfEventVolumeWeight (selfEventRate dwell : ℝ) :
    ∑' eventCount : ℕ,
        (selfEventRate * dwell) ^ eventCount / eventCount.factorial =
      Real.exp (selfEventRate * dwell) :=
  (hasSum_uniformizedSelfEventVolumeWeight selfEventRate dwell).tsum_eq

omit [DecidableEq State] in
/-- Resumming every possible number of virtual self-events during one dwell converts the common
uniform-clock survival factor exactly into physical escape survival. -/
theorem uniformizedSelfEventResummation
    (generator : FiniteStateMarkovGenerator State) (state : State) (dwell : ℝ) :
    Real.exp (-((generator.uniformizationRate : ℝ) * dwell)) *
        (∑' eventCount : ℕ,
          ((generator.uniformizedSelfEventRate state : ℝ) * dwell) ^ eventCount /
            eventCount.factorial) =
      Real.exp (-((generator.escapeRate state : ℝ) * dwell)) := by
  rw [tsum_uniformizedSelfEventVolumeWeight, ← Real.exp_add]
  rw [generator.coe_uniformizedSelfEventRate]
  congr 1
  ring

omit [DecidableEq State] in
/-- Simultaneously resumming independent virtual self-event insertions in every member of a finite
dwell vector converts common-clock survival into the complete physical integrated-escape
survival. -/
theorem uniformizedSelfEventResummation_finite
    (generator : FiniteStateMarkovGenerator State) {n : ℕ}
    (states : Fin n → State) (dwells : Fin n → ℝ) :
    Real.exp
        (-((generator.uniformizationRate : ℝ) * ∑ index, dwells index)) *
        ∏ index,
          ∑' eventCount : ℕ,
            ((generator.uniformizedSelfEventRate (states index) : ℝ) * dwells index) ^
                eventCount /
              eventCount.factorial =
      Real.exp
        (-(∑ index, (generator.escapeRate (states index) : ℝ) * dwells index)) := by
  simp_rw [tsum_uniformizedSelfEventVolumeWeight]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  rw [Finset.mul_sum]
  simp_rw [generator.coe_uniformizedSelfEventRate, sub_mul, Finset.sum_sub_distrib]
  ring

omit [DecidableEq State] in
/-- Extended-real form of simultaneous finite-dwell self-event resummation. Every series term is
nonnegative, so `ENNReal.ofReal` commutes exactly with each sum and with the finite product. -/
theorem uniformizedSelfEventResummation_finite_ennreal
    (generator : FiniteStateMarkovGenerator State) {n : ℕ}
    (states : Fin n → State) (dwells : Fin n → ℝ)
    (hDwells : ∀ index, 0 ≤ dwells index) :
    ENNReal.ofReal
          (Real.exp (-((generator.uniformizationRate : ℝ) * ∑ index, dwells index))) *
        ∏ index,
          ∑' selfEventCount : ℕ,
            ENNReal.ofReal
              (((generator.uniformizedSelfEventRate (states index) : ℝ) * dwells index) ^
                  selfEventCount /
                selfEventCount.factorial) =
      ENNReal.ofReal
        (Real.exp
          (-(∑ index, (generator.escapeRate (states index) : ℝ) * dwells index))) := by
  have hSeries (index : Fin n) :
      ∑' selfEventCount : ℕ,
          ENNReal.ofReal
            (((generator.uniformizedSelfEventRate (states index) : ℝ) * dwells index) ^
                selfEventCount /
              selfEventCount.factorial) =
        ENNReal.ofReal
          (∑' selfEventCount : ℕ,
            ((generator.uniformizedSelfEventRate (states index) : ℝ) * dwells index) ^
                selfEventCount /
              selfEventCount.factorial) := by
    rw [ENNReal.ofReal_tsum_of_nonneg]
    · intro selfEventCount
      exact div_nonneg
        (pow_nonneg
          (mul_nonneg (NNReal.coe_nonneg _) (hDwells index)) selfEventCount)
        (Nat.cast_nonneg _)
    · exact (hasSum_uniformizedSelfEventVolumeWeight
        (generator.uniformizedSelfEventRate (states index)) (dwells index)).summable
  simp_rw [hSeries]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply congrArg ENNReal.ofReal
    exact uniformizedSelfEventResummation_finite generator states dwells
  · intro index _
    rw [tsum_uniformizedSelfEventVolumeWeight]
    positivity

omit [DecidableEq State] in
/-- On an ordered physical jump-time vector, extended-real self-event resummation uses the
observation horizon as the total dwell and the exact physical integrated escape in the result. -/
theorem uniformizedSelfEventResummation_finite_ennreal_of_mem_orderedJumpTimes
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes eventCount T) :
    ENNReal.ofReal (Real.exp (-((generator.uniformizationRate : ℝ) * T))) *
        ∏ index,
          ∑' selfEventCount : ℕ,
            ENNReal.ofReal
              (((generator.uniformizedSelfEventRate (states index) : ℝ) *
                    FiniteJumpHistory.dwellTimeVector T times index) ^ selfEventCount /
                selfEventCount.factorial) =
      ENNReal.ofReal
        (Real.exp
          (-(∑ index, (generator.escapeRate (states index) : ℝ) *
            FiniteJumpHistory.dwellTimeVector T times index))) := by
  have hResummation := uniformizedSelfEventResummation_finite_ennreal
    generator states (FiniteJumpHistory.dwellTimeVector T times)
    (FiniteJumpHistory.dwellTimeVector_nonneg_of_mem_orderedJumpTimes hT hTimes)
  rw [FiniteJumpHistory.sum_dwellTimeVector] at hResummation
  exact hResummation

omit [DecidableEq State] in
/-- Multiplying the extended-real insertion-series resummation by the physical initial and jump
rate prefactor gives exactly the canonical physical fixed-word density. -/
theorem
    finiteStateMarkovUniformizedSelfEventFibreWeight_resums_to_jumpSliceDensity_ennreal
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ)
    (hT : 0 ≤ T) (hTimes : times ∈ orderedJumpTimes eventCount T) :
    ENNReal.ofReal
          ((initial (states 0)).toReal * finiteStateMarkovJumpRateProduct generator states) *
        (ENNReal.ofReal (Real.exp (-((generator.uniformizationRate : ℝ) * T))) *
          ∏ index,
            ∑' selfEventCount : ℕ,
              ENNReal.ofReal
                (((generator.uniformizedSelfEventRate (states index) : ℝ) *
                      FiniteJumpHistory.dwellTimeVector T times index) ^ selfEventCount /
                  selfEventCount.factorial)) =
      ENNReal.ofReal (finiteStateMarkovJumpSliceDensity initial generator T states times) := by
  rw [uniformizedSelfEventResummation_finite_ennreal_of_mem_orderedJumpTimes
    generator T states times hT hTimes]
  rw [← ENNReal.ofReal_mul]
  · apply congrArg ENNReal.ofReal
    unfold finiteStateMarkovJumpSliceDensity finiteStateMarkovIntegratedEscape
    rfl
  · unfold finiteStateMarkovJumpRateProduct
    exact mul_nonneg ENNReal.toReal_nonneg <|
      Finset.prod_nonneg fun _ _ ↦ NNReal.coe_nonneg _

omit [DecidableEq State] in
/-- After physical transition intensities are held fixed, resumming every possible virtual
self-event count in every dwell gives the canonical physical jump-slice density. -/
theorem finiteStateMarkovUniformizedSelfEventFibreWeight_resums_to_jumpSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) :
    (initial (states 0)).toReal *
        finiteStateMarkovJumpRateProduct generator states *
        (Real.exp (-((generator.uniformizationRate : ℝ) * T)) *
          ∏ index : Fin (eventCount + 1),
            ∑' selfEventCount : ℕ,
              ((generator.uniformizedSelfEventRate (states index) : ℝ) *
                FiniteJumpHistory.dwellTimeVector T times index) ^ selfEventCount /
                  selfEventCount.factorial) =
      finiteStateMarkovJumpSliceDensity initial generator T states times := by
  have hResummation := uniformizedSelfEventResummation_finite generator states
    (FiniteJumpHistory.dwellTimeVector T times)
  rw [FiniteJumpHistory.sum_dwellTimeVector] at hResummation
  rw [hResummation]
  unfold finiteStateMarkovJumpSliceDensity finiteStateMarkovIntegratedEscape
  rfl

end FiniteMarkovProcesses.Probability
