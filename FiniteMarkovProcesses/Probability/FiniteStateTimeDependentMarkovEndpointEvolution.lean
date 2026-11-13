/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointCoefficient

/-!
# Endpoint evolution for time-dependent uniformized chains

This module supplies the analytic regularity needed to resum the exact fixed-event endpoint
coefficients.  In particular, the coefficient is measurable in its horizon, finite at every
nonnegative horizon, and its real coordinates retain the exact ordered-simplex normalization.

The full common-clock series and its Volterra equation are built on this surface.  No forward
equation, compensator, or path large-deviation result is asserted here.

## Main results

- `measurable_lintegral_Ioo_zero`.
- `measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient`.
- `finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_ne_top`.
- `sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

/-- The nonnegative integral of a measurable function over `(0, T)` is measurable in `T`.
The statement includes negative horizons, where the open interval is empty. -/
theorem measurable_lintegral_Ioo_zero
    {integrand : ℝ → ℝ≥0∞} (hIntegrand : Measurable integrand) :
    Measurable fun horizon : ℝ ↦
      ∫⁻ time : ℝ in Ioo 0 horizon, integrand time := by
  let region : Set (ℝ × ℝ) :=
    {coordinates | 0 < coordinates.2 ∧ coordinates.2 < coordinates.1}
  have hRegion : MeasurableSet region := by
    unfold region
    exact measurableSet_lt measurable_const measurable_snd |>.inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hJoint : Measurable
      (region.indicator (fun coordinates ↦ integrand coordinates.2)) :=
    (hIntegrand.comp measurable_snd).indicator hRegion
  have hIntegrated :=
    Measurable.lintegral_prod_right' (ν := volume) hJoint
  convert hIntegrated using 1
  funext horizon
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro time
  by_cases hTime : time ∈ Ioo (0 : ℝ) horizon
  · rw [Set.indicator_of_mem hTime]
    rw [Set.indicator_of_mem]
    exact ⟨hTime.1, hTime.2⟩
  · rw [Set.indicator_of_notMem hTime]
    rw [Set.indicator_of_notMem]
    intro hRegionMem
    exact hTime ⟨hRegionMem.1, hRegionMem.2⟩

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Each extended-valued uniformized transition coordinate is measurable in physical time. -/
theorem FiniteStateTimeDependentMarkovRate.measurable_uniformizedTransitionPMF
    (rates : FiniteStateTimeDependentMarkovRate State) (source target : State) :
    Measurable fun time ↦ rates.uniformizedTransitionPMF time source target := by
  have hReal := (rates.measurable_uniformizedTransitionPMF_toReal source target).ennreal_ofReal
  have hFunction :
      (fun time ↦ ENNReal.ofReal
        (rates.uniformizedTransitionPMF time source target).toReal) =
      fun time ↦ rates.uniformizedTransitionPMF time source target := by
    funext time
    exact ENNReal.ofReal_toReal
      ((rates.uniformizedTransitionPMF time source).apply_ne_top target)
  rw [hFunction] at hReal
  exact hReal

/-- Every fixed-event endpoint coefficient is measurable in its horizon. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (eventCount : ℕ) (observed : State) :
    Measurable fun duration : ℝ ↦
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates duration eventCount observed := by
  induction eventCount generalizing observed with
  | zero =>
      have hFunction :
          (fun duration : ℝ ↦
            finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
              initial rates duration 0 observed) =
          fun _ ↦ initial observed := by
        funext duration
        exact finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_zero
          initial rates duration observed
      rw [hFunction]
      exact measurable_const
  | succ eventCount inductionHypothesis =>
      have hFunction :
          (fun duration : ℝ ↦
            finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
              initial rates duration (eventCount + 1) observed) =
          fun duration ↦
            ∫⁻ lastTime : ℝ in Ioo 0 duration,
              ∑ source : State,
                finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                    initial rates lastTime eventCount source *
                  rates.uniformizedTransitionPMF lastTime source observed := by
        funext duration
        exact finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_succ
          initial rates duration eventCount observed
      rw [hFunction]
      apply measurable_lintegral_Ioo_zero
      apply Finset.measurable_sum
      intro source _hSource
      exact (inductionHypothesis source).mul
        (rates.measurable_uniformizedTransitionPMF source observed)

/-- At a nonnegative horizon, every endpoint coefficient is finite. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_ne_top
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) (eventCount : ℕ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates duration eventCount observed ≠ ⊤ := by
  have hCoordinate :
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates duration eventCount observed ≤
        ∑ target : State,
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates duration eventCount target :=
    Finset.single_le_sum (fun target _hTarget ↦ zero_le) (Finset.mem_univ observed)
  rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    initial rates duration hDuration eventCount] at hCoordinate
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCoordinate

/-- Real coordinate of one finite clock-free endpoint sector. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (observed : State) : ℝ :=
  (finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    initial rates duration eventCount observed).toReal

/-- The real endpoint coefficients are nonnegative. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal_nonneg
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (observed : State) :
    0 ≤ finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal
      initial rates duration eventCount observed :=
  ENNReal.toReal_nonneg

/-- At a nonnegative horizon, the real endpoint coordinates sum to the exact ordered-simplex
volume. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) (eventCount : ℕ) :
    ∑ observed : State,
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal
          initial rates duration eventCount observed =
      duration ^ eventCount / eventCount.factorial := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficientReal
  rw [← ENNReal.toReal_sum (fun observed _hObserved ↦
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_ne_top
      initial rates duration hDuration eventCount observed)]
  rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    initial rates duration hDuration eventCount]
  rw [ENNReal.toReal_ofReal]
  exact div_nonneg (pow_nonneg hDuration eventCount)
    (Nat.cast_nonneg eventCount.factorial)

/-- Common-clock endpoint series before multiplication by the Poisson survival factor. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedEndpointSeries
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (observed : State) : ℝ≥0∞ :=
  ∑' eventCount : ℕ,
    (rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
      finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates duration eventCount observed

/-- Every coordinate of the unnormalized endpoint series is measurable in its horizon. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (observed : State) :
    Measurable fun duration : ℝ ↦
      finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates duration observed := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointSeries
  apply Measurable.tsum
  intro eventCount
  exact measurable_const.mul
    (measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
      initial rates eventCount observed)

/-- At a nonnegative horizon, the state-summed clock-free endpoint series is the common-clock
exponential. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedEndpointSeries
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    ∑ observed : State,
        finiteStateTimeDependentMarkovUniformizedEndpointSeries
          initial rates duration observed =
      ENNReal.ofReal
        (Real.exp ((rates.uniformizationRate : ℝ) * duration)) := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointSeries
  rw [← Summable.tsum_finsetSum
    (fun observed _hObserved ↦ ENNReal.summable)]
  let clockHorizon : ℝ := (rates.uniformizationRate : ℝ) * duration
  have hSeriesNonnegative (eventCount : ℕ) :
      0 ≤ clockHorizon ^ eventCount / eventCount.factorial :=
    div_nonneg (pow_nonneg (mul_nonneg (by positivity) hDuration) eventCount)
      (Nat.cast_nonneg eventCount.factorial)
  have hSeriesSummable : Summable fun eventCount : ℕ ↦
      clockHorizon ^ eventCount / eventCount.factorial :=
    Real.summable_pow_div_factorial clockHorizon
  have hExponentialSeries :
      ENNReal.ofReal (Real.exp clockHorizon) =
        ∑' eventCount : ℕ,
          ENNReal.ofReal
            (clockHorizon ^ eventCount / eventCount.factorial) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hSeriesNonnegative hSeriesSummable]
    congr 1
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change _ = ENNReal.ofReal (Real.exp clockHorizon)
  rw [hExponentialSeries]
  apply tsum_congr
  intro eventCount
  rw [← Finset.mul_sum]
  rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    initial rates duration hDuration eventCount]
  rw [ENNReal.coe_nnreal_eq]
  rw [← ENNReal.ofReal_pow (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity)]
  rw [← ENNReal.ofReal_mul (pow_nonneg
    (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity) eventCount)]
  congr 1
  unfold clockHorizon
  rw [mul_pow]
  ring

/-- Every coordinate of the clock-free endpoint series is finite at a nonnegative horizon. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointSeries_ne_top
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates duration observed ≠ ⊤ := by
  have hCoordinate :
      finiteStateTimeDependentMarkovUniformizedEndpointSeries
          initial rates duration observed ≤
        ∑ target : State,
          finiteStateTimeDependentMarkovUniformizedEndpointSeries
            initial rates duration target :=
    Finset.single_le_sum (fun target _hTarget ↦ zero_le) (Finset.mem_univ observed)
  rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointSeries
    initial rates duration hDuration] at hCoordinate
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCoordinate

/-- Endpoint probability coordinate obtained by restoring the common Poisson survival factor. -/
noncomputable def finiteStateTimeDependentMarkovEndpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (observed : State) : ℝ≥0∞ :=
  ENNReal.ofReal
      (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
    finiteStateTimeDependentMarkovUniformizedEndpointSeries
      initial rates duration observed

/-- Retaining the zero-event sector gives a pointwise lower bound on every endpoint coordinate:
the initial mass survives with at least the common Poisson no-event probability. -/
theorem poissonSurvival_mul_initial_le_finiteStateTimeDependentMarkovEndpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (observed : State) :
    ENNReal.ofReal
          (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        initial observed ≤
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed := by
  unfold finiteStateTimeDependentMarkovEndpointProbability
    finiteStateTimeDependentMarkovUniformizedEndpointSeries
  apply mul_le_mul_right
  calc
    initial observed =
        (rates.uniformizationRate : ℝ≥0∞) ^ 0 *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates duration 0 observed := by
      rw [finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_zero]
      simp
    _ ≤ ∑' eventCount : ℕ,
        (rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates duration eventCount observed :=
      ENNReal.le_tsum (f := fun eventCount : ℕ ↦
        (rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates duration eventCount observed) 0

/-- Real-valued no-event lower bound at a nonnegative physical horizon. -/
theorem exp_neg_uniformizationRate_mul_duration_mul_initial_toReal_le_endpointProbability_toReal
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) (observed : State) :
    Real.exp (-((rates.uniformizationRate : ℝ) * duration)) *
        (initial observed).toReal ≤
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed).toReal := by
  have hEndpointFinite :
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteStateTimeDependentMarkovUniformizedEndpointSeries_ne_top
        initial rates duration hDuration observed)
  have hLower :=
    poissonSurvival_mul_initial_le_finiteStateTimeDependentMarkovEndpointProbability
      initial rates duration observed
  have hLowerFinite :
      ENNReal.ofReal
          (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        initial observed ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (initial.apply_ne_top observed)
  rw [← ENNReal.toReal_le_toReal hLowerFinite hEndpointFinite] at hLower
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hLower

/-- At every nonnegative horizon, the endpoint probability coordinates sum exactly to one. -/
theorem sum_finiteStateTimeDependentMarkovEndpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) :
    ∑ observed : State,
        finiteStateTimeDependentMarkovEndpointProbability
          initial rates duration observed = 1 := by
  unfold finiteStateTimeDependentMarkovEndpointProbability
  rw [← Finset.mul_sum]
  rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointSeries
    initial rates duration hDuration]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [Real.exp_neg]
  rw [inv_mul_cancel₀ (Real.exp_ne_zero _)]
  simp

/-- Endpoint probability mass function at a nonnegative physical horizon. -/
noncomputable def finiteStateTimeDependentMarkovEndpointPMF
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) : PMF State :=
  PMF.ofFintype
    (fun observed ↦ finiteStateTimeDependentMarkovEndpointProbability
      initial rates duration observed)
    (by
      exact sum_finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration duration.coe_nonneg)

/-- Evaluating the endpoint PMF recovers the resummed common-clock coordinate. -/
@[simp]
theorem finiteStateTimeDependentMarkovEndpointPMF_apply
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    finiteStateTimeDependentMarkovEndpointPMF initial rates duration observed =
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed := by
  simp [finiteStateTimeDependentMarkovEndpointPMF]

/-- The exact Volterra equation for the clock-free endpoint series.  The common clock appears
once at the last virtual event; every earlier event has already been resummed into the endpoint
series at that last-event time. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointSeries_eq_initial_add_lintegral
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (target : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates duration target =
      initial target +
        ∫⁻ lastTime : ℝ in Ioo 0 duration,
          (rates.uniformizationRate : ℝ≥0∞) *
            ∑ source : State,
              finiteStateTimeDependentMarkovUniformizedEndpointSeries
                  initial rates lastTime source *
                rates.uniformizedTransitionPMF lastTime source target := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointSeries
  rw [tsum_eq_zero_add' ENNReal.summable]
  rw [pow_zero, one_mul,
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_zero]
  congr 1
  calc
    (∑' eventCount : ℕ,
        (rates.uniformizationRate : ℝ≥0∞) ^ (eventCount + 1) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates duration (eventCount + 1) target) =
        ∑' eventCount : ℕ,
          ∫⁻ lastTime : ℝ in Ioo 0 duration,
            (rates.uniformizationRate : ℝ≥0∞) ^ (eventCount + 1) *
              ∑ source : State,
                finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                    initial rates lastTime eventCount source *
                  rates.uniformizedTransitionPMF lastTime source target := by
      apply tsum_congr
      intro eventCount
      rw [finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_succ]
      rw [lintegral_const_mul'
        ((rates.uniformizationRate : ℝ≥0∞) ^ (eventCount + 1)) _]
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    _ = ∫⁻ lastTime : ℝ in Ioo 0 duration,
        ∑' eventCount : ℕ,
          (rates.uniformizationRate : ℝ≥0∞) ^ (eventCount + 1) *
            ∑ source : State,
              finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                  initial rates lastTime eventCount source *
                rates.uniformizedTransitionPMF lastTime source target := by
      rw [lintegral_tsum]
      intro eventCount
      apply Measurable.aemeasurable
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro source _hSource
      exact
        (measurable_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates eventCount source).mul
            (rates.measurable_uniformizedTransitionPMF source target)
    _ = ∫⁻ lastTime : ℝ in Ioo 0 duration,
        (rates.uniformizationRate : ℝ≥0∞) *
          ∑ source : State,
            (∑' eventCount : ℕ,
              (rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
                finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                  initial rates lastTime eventCount source) *
              rates.uniformizedTransitionPMF lastTime source target := by
      apply lintegral_congr
      intro lastTime
      calc
        (∑' eventCount : ℕ,
            (rates.uniformizationRate : ℝ≥0∞) ^ (eventCount + 1) *
              ∑ source : State,
                finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                    initial rates lastTime eventCount source *
                  rates.uniformizedTransitionPMF lastTime source target) =
            (rates.uniformizationRate : ℝ≥0∞) *
              ∑' eventCount : ℕ,
                ∑ source : State,
                  ((rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
                    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                      initial rates lastTime eventCount source) *
                    rates.uniformizedTransitionPMF lastTime source target := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro eventCount
          rw [pow_succ']
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
          rw [Finset.mul_sum]
        _ = (rates.uniformizationRate : ℝ≥0∞) *
              ∑ source : State,
                (∑' eventCount : ℕ,
                  ((rates.uniformizationRate : ℝ≥0∞) ^ eventCount *
                    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
                      initial rates lastTime eventCount source) *
                    rates.uniformizedTransitionPMF lastTime source target) := by
          congr 1
          exact (Summable.tsum_finsetSum
            (fun source _hSource ↦ ENNReal.summable))
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro source _hSource
          rw [ENNReal.tsum_mul_right]

end

end FiniteMarkovProcesses.Probability
