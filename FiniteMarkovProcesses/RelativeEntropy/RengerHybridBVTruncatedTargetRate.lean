/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRepresentationDomain
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalHybridL1Concentration

/-!
# Bounded target-rate charts for the Renger hybrid path

This module extracts a measurable density version and the measurable instantaneous ordered flow
from a finite-rate hybrid path.  Their physical intensity ratio is truncated at a supplied finite
cutoff and bundled as the existing normalized bounded time-dependent Markov source.

The construction preserves the target's zero-flow support and never asserts that an unbounded
finite-rate target already satisfies the bounded-source contract.  Subsequent regularization must
prove convergence as the cutoff diverges before using these sources in a Girsanov lower bound.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- A measurable modification of the finite-rate target density coordinates. -/
noncomputable def rengerDirectionalFlowHybridBVMeasurableDensityAt
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    ℝ → State → NNReal :=
  AEMeasurable.mk (rengerDirectionalFlowHybridBVDensityAt path)
    (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path)

/-- The selected target density modification is measurable. -/
theorem measurable_rengerDirectionalFlowHybridBVMeasurableDensityAt
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Measurable (rengerDirectionalFlowHybridBVMeasurableDensityAt path) :=
  (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path).measurable_mk

/-- The selected target density modification agrees almost everywhere with the exact hybrid
density coordinate. -/
theorem ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVMeasurableDensityAt path =ᵐ[
        finiteOpenIntervalVolume duration]
      rengerDirectionalFlowHybridBVDensityAt path :=
  (aemeasurable_rengerDirectionalFlowHybridBVDensityAt path).ae_eq_mk.symm

/-- Measurable instantaneous ordered flow extracted from the target derivative measure. -/
noncomputable def rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (source target : State) : NNReal :=
  if hOffDiagonal : source ≠ target then
    rengerDirectionalFlowHybridBVFlowDerivativeAt path time
      ⟨(source, target), hOffDiagonal⟩
  else 0

/-- Every target ordered-flow coordinate is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt path time source target := by
  unfold rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
  split
  · rename_i hOffDiagonal
    exact measurable_real_toNNReal.comp
      (path.measurable_derivativeDensity (Sum.inr ⟨(source, target), hOffDiagonal⟩))
  · rename_i hDiagonal
    exact measurable_const

/-- Target intensity ratio, truncated at a finite source cutoff.  Zero target density uses the
canonical zero division convention; finite action will later prove that no positive target flow
is lost there almost everywhere. -/
noncomputable def rengerDirectionalFlowHybridBVTruncatedTargetRateValue
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) (source target : State) : NNReal :=
  if source = target then 0
  else min cutoff
    (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt path time source target /
      rengerDirectionalFlowHybridBVMeasurableDensityAt path time source)

/-- The truncated target intensity is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVTruncatedTargetRateValue
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVTruncatedTargetRateValue
        path cutoff time source target := by
  by_cases hDiagonal : source = target
  · simp [rengerDirectionalFlowHybridBVTruncatedTargetRateValue, hDiagonal]
  · simp only [rengerDirectionalFlowHybridBVTruncatedTargetRateValue, hDiagonal, ite_false]
    apply Measurable.min measurable_const
    exact
      (measurable_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path source target).div
        ((measurable_pi_apply source).comp
          (measurable_rengerDirectionalFlowHybridBVMeasurableDensityAt path))

/-- Every truncated target intensity is bounded by its supplied cutoff. -/
theorem rengerDirectionalFlowHybridBVTruncatedTargetRateValue_le
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) (source target : State) :
    rengerDirectionalFlowHybridBVTruncatedTargetRateValue
        path cutoff time source target ≤ cutoff := by
  unfold rengerDirectionalFlowHybridBVTruncatedTargetRateValue
  split_ifs
  · exact zero_le
  · exact min_le_left _ _

/-- The truncated target chart as a genuine bounded time-dependent Markov-rate source. -/
noncomputable def rengerDirectionalFlowHybridBVTruncatedTargetRate
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal) :
    FiniteStateTimeDependentMarkovRate State where
  rate := rengerDirectionalFlowHybridBVTruncatedTargetRateValue path cutoff
  rate_self := by
    intro time state
    simp [rengerDirectionalFlowHybridBVTruncatedTargetRateValue]
  measurable_rate :=
    measurable_rengerDirectionalFlowHybridBVTruncatedTargetRateValue path cutoff
  escapeBound := (Fintype.card State : NNReal) * cutoff
  escapeRate_le_bound := by
    intro time source
    calc
      (∑ target ∈ Finset.univ.erase source,
          rengerDirectionalFlowHybridBVTruncatedTargetRateValue
            path cutoff time source target) ≤
          ∑ _target ∈ Finset.univ.erase source, cutoff := by
        apply Finset.sum_le_sum
        intro target _hTarget
        exact rengerDirectionalFlowHybridBVTruncatedTargetRateValue_le
          path cutoff time source target
      _ ≤ ∑ _target : State, cutoff := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.erase_subset _ _
      _ = (Fintype.card State : NNReal) * cutoff := by
        simp [nsmul_eq_mul]

/-- Off the diagonal, the bundled source rate is literally the truncated target ratio. -/
theorem rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target) :
    (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
        time source target =
      min cutoff
        (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target /
          rengerDirectionalFlowHybridBVMeasurableDensityAt path time source) := by
  simp [rengerDirectionalFlowHybridBVTruncatedTargetRate,
    rengerDirectionalFlowHybridBVTruncatedTargetRateValue, hOffDiagonal]

/-- Increasing the cutoff can only increase the target intensity chart. -/
theorem rengerDirectionalFlowHybridBVTruncatedTargetRateValue_mono_cutoff
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {firstCutoff secondCutoff : NNReal} (hCutoff : firstCutoff ≤ secondCutoff)
    (time : ℝ) (source target : State) :
    rengerDirectionalFlowHybridBVTruncatedTargetRateValue
        path firstCutoff time source target ≤
      rengerDirectionalFlowHybridBVTruncatedTargetRateValue
        path secondCutoff time source target := by
  unfold rengerDirectionalFlowHybridBVTruncatedTargetRateValue
  split_ifs
  · exact le_rfl
  · exact min_le_min hCutoff le_rfl

/-- Along natural cutoffs, every off-diagonal target intensity is eventually recovered exactly.
This is stronger than pointwise convergence and keeps the later approximation proof honest about
where its remaining error can occur. -/
theorem eventually_rengerDirectionalFlowHybridBVTruncatedTargetRate_eq_ratio
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᶠ cutoff : ℕ in atTop,
      (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
          time source target =
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target /
          rengerDirectionalFlowHybridBVMeasurableDensityAt path time source := by
  let targetRatio :=
    rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt path time source target /
      rengerDirectionalFlowHybridBVMeasurableDensityAt path time source
  obtain ⟨initialCutoff, hInitialCutoff⟩ := exists_nat_ge targetRatio
  filter_upwards [eventually_ge_atTop initialCutoff] with cutoff hCutoff
  rw [rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
    path cutoff time hOffDiagonal, min_eq_right]
  exact hInitialCutoff.trans (by exact_mod_cast hCutoff)

/-- Natural cutoff charts converge pointwise to the untruncated off-diagonal target intensity. -/
theorem tendsto_rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_atTop
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target) :
    Tendsto
        (fun cutoff : ℕ ↦
          (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
            time source target)
        atTop
        (nhds
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target /
            rengerDirectionalFlowHybridBVMeasurableDensityAt path time source)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [
    eventually_rengerDirectionalFlowHybridBVTruncatedTargetRate_eq_ratio
      path time hOffDiagonal] with cutoff hCutoff
  exact hCutoff.symm

/-- A finite dynamic rate forces the target flow to vanish almost everywhere on every edge that
the reference generator forbids.  This is the path-level absolute-continuity condition needed before
any Girsanov change of law is licensed. -/
theorem ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_generator_rate_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target)
    (hGeneratorRate : generator.rate source target = 0) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path.1 time source target = 0 := by
  have hRateIntegral :
      (∫⁻ time,
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path.1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
    rw [← rengerDirectionalFlowHybridBVDynamicRate_eq_integral_on_representationDomain
      generator hDuration path]
    exact hDynamicRate
  have hLocalRateFinite :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path.1 time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time) < ⊤ :=
    ae_lt_top'
      (aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path.1)
      hRateIntegral
  filter_upwards [hLocalRateFinite] with time hLocalRate
  have hFlowZero :=
    directionalFlow_eq_zero_of_expected_eq_zero_of_rengerDirectionalFlowLocalRateRaw_ne_top
      generator
      (rengerDirectionalFlowHybridBVDensityAt path.1 time)
      (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
      ⟨(source, target), hOffDiagonal⟩
      (by simp [hGeneratorRate]) hLocalRate.ne
  simpa [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt, hOffDiagonal] using hFlowZero

/-- Every finite-action truncated target source preserves the reference generator's forbidden
edges almost everywhere. -/
theorem ae_rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_eq_zero_of_generator_rate_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (cutoff : NNReal) {source target : State} (hOffDiagonal : source ≠ target)
    (hGeneratorRate : generator.rate source target = 0) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (rengerDirectionalFlowHybridBVTruncatedTargetRate path.1 cutoff).rate
        time source target = 0 := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_generator_rate_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal hGeneratorRate] with time hTargetFlow
  rw [rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
    path.1 cutoff time hOffDiagonal, hTargetFlow]
  simp

/-- Finite dynamic rate also forbids positive target flow at zero target density, independently
of whether the reference edge itself is allowed. -/
theorem ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_density_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source = 0 →
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target = 0 := by
  have hRateIntegral :
      (∫⁻ time,
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path.1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
        ∂finiteOpenIntervalVolume duration) ≠ ⊤ := by
    rw [← rengerDirectionalFlowHybridBVDynamicRate_eq_integral_on_representationDomain
      generator hDuration path]
    exact hDynamicRate
  have hLocalRateFinite :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        rengerDirectionalFlowLocalRateRaw generator
            (rengerDirectionalFlowHybridBVDensityAt path.1 time)
            (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time) < ⊤ :=
    ae_lt_top'
      (aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator path.1)
      hRateIntegral
  filter_upwards [hLocalRateFinite,
    ae_rengerDirectionalFlowHybridBVMeasurableDensityAt_eq path.1] with
      time hLocalRate hDensityVersion hDensityZero
  have hRawDensityZero :
      rengerDirectionalFlowHybridBVDensityAt path.1 time source = 0 := by
    rw [← hDensityVersion]
    exact hDensityZero
  have hFlowZero :=
    directionalFlow_eq_zero_of_expected_eq_zero_of_rengerDirectionalFlowLocalRateRaw_ne_top
      generator
      (rengerDirectionalFlowHybridBVDensityAt path.1 time)
      (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
      ⟨(source, target), hOffDiagonal⟩
      (by simp [hRawDensityZero]) hLocalRate.ne
  simpa [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt, hOffDiagonal] using hFlowZero

/-- Directional flow generated by the measurable target density and one truncated target-rate
chart. -/
noncomputable def rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) (source target : State) : NNReal :=
  rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
    (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
      time source target

/-- Every truncated target-flow coordinate is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path cutoff time source target := by
  exact
    ((measurable_pi_apply source).comp
      (measurable_rengerDirectionalFlowHybridBVMeasurableDensityAt path)).mul
      ((rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).measurable_rate
        source target)

/-- Truncated target flow is monotone in its cutoff. -/
theorem rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_mono_cutoff
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {firstCutoff secondCutoff : NNReal} (hCutoff : firstCutoff ≤ secondCutoff)
    (time : ℝ) (source target : State) :
    rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path firstCutoff time source target ≤
      rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path secondCutoff time source target := by
  unfold rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
  gcongr
  exact rengerDirectionalFlowHybridBVTruncatedTargetRateValue_mono_cutoff
    path hCutoff time source target

/-- Truncation never creates more directional flow than the target carries. -/
theorem rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_le_flow
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target) :
    rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
        path cutoff time source target ≤
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
        path time source target := by
  rw [rengerDirectionalFlowHybridBVTruncatedTargetFlowValue,
    rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
      path cutoff time hOffDiagonal]
  by_cases hDensity :
      rengerDirectionalFlowHybridBVMeasurableDensityAt path time source = 0
  · simp [hDensity]
  · calc
      rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
          min cutoff
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path time source target /
              rengerDirectionalFlowHybridBVMeasurableDensityAt path time source) ≤
        rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target /
            rengerDirectionalFlowHybridBVMeasurableDensityAt path time source) :=
          by gcongr; exact min_le_right _ _
      _ = rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path time source target := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hDensity

/-- On a finite-action path, increasing natural cutoffs recover each exact target-flow coordinate
almost everywhere. -/
theorem ae_tendsto_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      Tendsto
          (fun cutoff : ℕ ↦
            rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 cutoff time source target)
          atTop
          (nhds
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target)) := by
  filter_upwards [
    ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_density_eq_zero
      generator hDuration path hDynamicRate hOffDiagonal] with time hZeroDensityFlow
  by_cases hDensity :
      rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source = 0
  · have hFlow :
        rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
          path.1 time source target = 0 := hZeroDensityFlow hDensity
    simp [rengerDirectionalFlowHybridBVTruncatedTargetFlowValue, hDensity, hFlow]
  · have hRate :=
      tendsto_rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_atTop
        path.1 time hOffDiagonal
    have hMul :=
      (tendsto_const_nhds
        (x := rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source)).mul hRate
    simpa only [rengerDirectionalFlowHybridBVTruncatedTargetFlowValue,
      mul_div_cancel₀ _ hDensity] using hMul

/-- Monotone convergence upgrades coordinatewise cutoff recovery to exact integrated target-flow
recovery on the physical interval. -/
theorem tendsto_lintegral_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    Tendsto
        (fun cutoff : ℕ ↦
          ∫⁻ time,
            (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
              path.1 cutoff time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration)
        atTop
        (nhds
          (∫⁻ time,
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target : ENNReal)
            ∂finiteOpenIntervalVolume duration)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro cutoff
    exact (measurable_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue
      path.1 cutoff source target).coe_nnreal_ennreal.aemeasurable
  · exact ae_of_all _ fun time first second hCutoff ↦ by
      exact ENNReal.coe_le_coe.2
        (rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_mono_cutoff
          path.1 (firstCutoff := (first : NNReal))
          (secondCutoff := (second : NNReal))
          (by exact_mod_cast hCutoff) time source target)
  · filter_upwards [
      ae_tendsto_rengerDirectionalFlowHybridBVTruncatedTargetFlowValue_atTop
        generator hDuration path hDynamicRate hOffDiagonal] with time hTendsto
    exact ((ENNReal.continuous_coe_iff.2 continuous_id).tendsto _).comp hTendsto

/-- Wherever the target density is positive and its intensity ratio lies below the cutoff, the
bounded source recovers the target directional flow exactly. -/
theorem rengerDirectionalFlowHybridBVMeasurableDensity_mul_truncatedTargetRate_eq_flow
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target)
    (hDensity : 0 < rengerDirectionalFlowHybridBVMeasurableDensityAt path time source)
    (hRatio :
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt path time source target /
          rengerDirectionalFlowHybridBVMeasurableDensityAt path time source ≤ cutoff) :
    rengerDirectionalFlowHybridBVMeasurableDensityAt path time source *
        (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
          time source target =
      rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt path time source target := by
  rw [rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_of_ne
    path cutoff time hOffDiagonal, min_eq_right hRatio]
  rw [mul_comm]
  exact div_mul_cancel₀ _ hDensity.ne'

end

end FiniteMarkovProcesses.InformationTheory
