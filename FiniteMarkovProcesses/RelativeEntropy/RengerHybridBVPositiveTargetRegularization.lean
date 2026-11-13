/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTruncatedTargetRate

/-!
# Positive reference-supported regularization of a Renger hybrid target

This module turns the bounded target chart into a pointwise reference-supported source and then
adds an explicit positive multiple of the reference generator.  The first operation differs from
the finite-action target only on a null set.  The second gives strict positivity on every allowed
reference edge while remaining zero on every forbidden edge.

No convergence of the induced mean path, Girsanov identity, or large-deviation lower bound is
asserted here.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The truncated target rate, totalized to zero on every edge forbidden by the reference
generator. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) (source target : State) : NNReal :=
  if generator.rate source target = 0 then 0
  else
    (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
      time source target

/-- The reference-supported target rate is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (source target : State) :
    Measurable fun time ↦
      rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
        generator path cutoff time source target := by
  by_cases hGeneratorRate : generator.rate source target = 0
  · simp [rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue, hGeneratorRate]
  · simpa [rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue, hGeneratorRate] using
      (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).measurable_rate
        source target

/-- Reference support totalization never increases a truncated target intensity. -/
theorem rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue_le
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) (source target : State) :
    rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
        generator path cutoff time source target ≤ cutoff := by
  unfold rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
  split_ifs
  · exact zero_le
  · exact rengerDirectionalFlowHybridBVTruncatedTargetRateValue_le
      path cutoff time source target

/-- The bounded truncated target source with pointwise reference support. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal) :
    FiniteStateTimeDependentMarkovRate State where
  rate := rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
    generator path cutoff
  rate_self := by
    intro time state
    simp [rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue,
      generator.rate_self state]
  measurable_rate :=
    measurable_rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
      generator path cutoff
  escapeBound := (Fintype.card State : NNReal) * cutoff
  escapeRate_le_bound := by
    intro time source
    calc
      (∑ target ∈ Finset.univ.erase source,
          rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue
            generator path cutoff time source target) ≤
          ∑ _target ∈ Finset.univ.erase source, cutoff := by
        apply Finset.sum_le_sum
        intro target _hTarget
        exact rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue_le
          generator path cutoff time source target
      _ ≤ ∑ _target : State, cutoff := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.erase_subset _ _
      _ = (Fintype.card State : NNReal) * cutoff := by
        simp [nsmul_eq_mul]

/-- A forbidden reference edge has zero pointwise reference-supported target rate. -/
theorem rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) {source target : State}
    (hGeneratorRate : generator.rate source target = 0) :
    (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate generator path cutoff).rate
        time source target = 0 := by
  simp [rengerDirectionalFlowHybridBVReferenceSupportedTargetRate,
    rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue, hGeneratorRate]

/-- On every allowed reference edge, support totalization leaves the truncated target rate
pointwise unchanged. -/
theorem rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_of_generator_rate_ne_zero
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff : NNReal)
    (time : ℝ) {source target : State}
    (hGeneratorRate : generator.rate source target ≠ 0) :
    (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate generator path cutoff).rate
        time source target =
      (rengerDirectionalFlowHybridBVTruncatedTargetRate path cutoff).rate
        time source target := by
  simp [rengerDirectionalFlowHybridBVReferenceSupportedTargetRate,
    rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue, hGeneratorRate]

/-- For a finite-action target, support totalization changes each channel only on a null set. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_truncatedTargetRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    (cutoff : NNReal) (source target : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
          generator path.1 cutoff).rate time source target =
        (rengerDirectionalFlowHybridBVTruncatedTargetRate path.1 cutoff).rate
          time source target := by
  by_cases hDiagonal : source = target
  · subst target
    exact ae_of_all _ fun time ↦ by
      rw [(rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
        generator path.1 cutoff).rate_self,
        (rengerDirectionalFlowHybridBVTruncatedTargetRate path.1 cutoff).rate_self]
  by_cases hGeneratorRate : generator.rate source target = 0
  · filter_upwards [
      ae_rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_eq_zero_of_generator_rate_eq_zero
        generator hDuration path hDynamicRate cutoff hDiagonal hGeneratorRate] with time hTarget
    rw [rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_zero
      generator path.1 cutoff time hGeneratorRate]
    exact hTarget.symm
  · exact ae_of_all _ fun time ↦ by
      simp [rengerDirectionalFlowHybridBVReferenceSupportedTargetRate,
        rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue,
        hGeneratorRate]

/-- Positive reference-floor regularization of the supported truncated target. -/
noncomputable def rengerDirectionalFlowHybridBVPositiveTargetRegularization
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff referenceWeight : NNReal) :
    FiniteStateTimeDependentMarkovRate State where
  rate := fun time source target ↦
    (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
        generator path cutoff).rate time source target +
      referenceWeight * generator.rate source target
  rate_self := by
    intro time state
    rw [(rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
      generator path cutoff).rate_self, generator.rate_self]
    simp
  measurable_rate := by
    intro source target
    exact
      (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
        generator path cutoff).measurable_rate source target |>.add measurable_const
  escapeBound :=
    (Fintype.card State : NNReal) * cutoff +
      referenceWeight * finiteStateTotalEscapeBound generator
  escapeRate_le_bound := by
    intro time source
    rw [Finset.sum_add_distrib]
    apply add_le_add
    · exact (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
        generator path cutoff).escapeRate_le_bound time source
    · rw [← Finset.mul_sum]
      rw [show (∑ target ∈ Finset.univ.erase source, generator.rate source target) =
          generator.escapeRate source by
        rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self source)]
        rfl]
      gcongr
      exact escapeRate_le_finiteStateTotalEscapeBound generator source

/-- The positive regularization has its exact supported-target plus reference-floor rate. -/
theorem rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff referenceWeight : NNReal)
    (time : ℝ) (source target : State) :
    (rengerDirectionalFlowHybridBVPositiveTargetRegularization
        generator path cutoff referenceWeight).rate time source target =
      (rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
          generator path cutoff).rate time source target +
        referenceWeight * generator.rate source target :=
  rfl

/-- The positive regularization remains exactly zero on forbidden reference edges. -/
theorem rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff referenceWeight : NNReal)
    (time : ℝ) {source target : State}
    (hGeneratorRate : generator.rate source target = 0) :
    (rengerDirectionalFlowHybridBVPositiveTargetRegularization
        generator path cutoff referenceWeight).rate time source target = 0 := by
  rw [rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate,
    rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_eq_zero
      generator path cutoff time hGeneratorRate, hGeneratorRate]
  simp

/-- A positive reference floor makes every allowed reference edge strictly positive. -/
theorem rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate_pos
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (cutoff referenceWeight : NNReal)
    (time : ℝ) {source target : State}
    (hReferenceWeight : 0 < referenceWeight)
    (hGeneratorRate : 0 < generator.rate source target) :
    0 < (rengerDirectionalFlowHybridBVPositiveTargetRegularization
        generator path cutoff referenceWeight).rate time source target := by
  rw [rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate]
  exact add_pos_of_nonneg_of_pos zero_le
    (mul_pos hReferenceWeight hGeneratorRate)

/-- Canonical one-parameter approximation: cutoff `n` and positive reference floor
`1 / (n + 1)`. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ) :
    FiniteStateTimeDependentMarkovRate State :=
  rengerDirectionalFlowHybridBVPositiveTargetRegularization
    generator path index (1 / ((index : NNReal) + 1))

/-- Every canonical reference floor is strictly positive. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_referenceWeight_pos
    (index : ℕ) :
    0 < (1 / ((index : NNReal) + 1) : NNReal) := by
  positivity

/-- Every allowed reference edge has strictly positive canonical regularized rate. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_pos
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (time : ℝ) {source target : State}
    (hGeneratorRate : 0 < generator.rate source target) :
    0 < (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).rate time source target := by
  exact rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate_pos
    generator path index (1 / ((index : NNReal) + 1)) time
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_referenceWeight_pos
      index)
    hGeneratorRate

/-- Every forbidden reference edge has zero canonical regularized rate. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_eq_zero
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (time : ℝ) {source target : State}
    (hGeneratorRate : generator.rate source target = 0) :
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).rate time source target = 0 := by
  exact rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate_eq_zero
    generator path index (1 / ((index : NNReal) + 1)) time hGeneratorRate

/-- On an allowed off-diagonal edge, the canonical positive regularization converges pointwise to
the exact untruncated target intensity ratio. -/
theorem tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_atTop
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) {source target : State} (hOffDiagonal : source ≠ target)
    (hGeneratorRate : generator.rate source target ≠ 0) :
    Tendsto
        (fun index : ℕ ↦
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path index).rate time source target)
        atTop
        (nhds
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path time source target /
            rengerDirectionalFlowHybridBVMeasurableDensityAt path time source)) := by
  have hTarget :=
    tendsto_rengerDirectionalFlowHybridBVTruncatedTargetRate_rate_atTop
      path time hOffDiagonal
  have hReferenceFloor :
      Tendsto
          (fun index : ℕ ↦
            (1 / ((index : NNReal) + 1)) * generator.rate source target)
          atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal)).mul
        (tendsto_const_nhds (x := generator.rate source target))
  simpa only [rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization,
    rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate,
    rengerDirectionalFlowHybridBVReferenceSupportedTargetRate_rate_of_generator_rate_ne_zero
      generator path _ _ hGeneratorRate,
    add_zero] using hTarget.add hReferenceFloor

/-- For every finite-action target and off-diagonal channel, canonical positive regularization
converges to the exact target intensity ratio almost everywhere in physical time. -/
theorem ae_tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_atTop
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hDynamicRate :
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 ≠ ⊤)
    {source target : State} (hOffDiagonal : source ≠ target) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      Tendsto
          (fun index : ℕ ↦
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path.1 index).rate time source target)
          atTop
          (nhds
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
                path.1 time source target /
              rengerDirectionalFlowHybridBVMeasurableDensityAt path.1 time source)) := by
  by_cases hGeneratorRate : generator.rate source target = 0
  · filter_upwards [
      ae_rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt_eq_zero_of_generator_rate_eq_zero
        generator hDuration path hDynamicRate hOffDiagonal hGeneratorRate] with time hTargetFlow
    have hRegularizedRate :
        (fun index : ℕ ↦
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index).rate time source target) = fun _index ↦ 0 := by
      funext index
      exact rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_eq_zero
        generator path.1 index time hGeneratorRate
    rw [hRegularizedRate, hTargetFlow]
    simp
  · exact ae_of_all _ fun time ↦
      tendsto_rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_atTop
        generator path.1 time hOffDiagonal hGeneratorRate

end

end FiniteMarkovProcesses.InformationTheory
