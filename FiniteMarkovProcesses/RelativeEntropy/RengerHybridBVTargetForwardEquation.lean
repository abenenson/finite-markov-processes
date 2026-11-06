/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTruncatedTargetRate
import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Dissipation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Forward equation associated with a finite-action Renger hybrid target

Finite-rate admissibility carries both the absolutely continuous derivative and the directional
continuity equation.  The generic hybrid-BV reconstruction theorem therefore integrates the
instantaneous incoming-minus-outgoing target flow back to the selected density coordinate.

This is the target-side Volterra equation.  It does not identify the target with the mean of a
physical jump source.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Incoming-minus-outgoing instantaneous target-flow divergence at one state. -/
noncomputable def rengerDirectionalFlowHybridBVTargetFlowDivergence
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (state : State) : ℝ :=
  (∑ source : {source : State // source ≠ state},
      rengerDirectionalFlowHybridBVFlowDerivative path time
        ⟨(source.1, state), source.property⟩) -
    ∑ target : {target : State // target ≠ state},
      rengerDirectionalFlowHybridBVFlowDerivative path time
        ⟨(state, target.1), target.property.symm⟩

/-- Raw real target flow totalized to zero on the diagonal. -/
noncomputable def rengerDirectionalFlowHybridBVRawFlowDerivativeValue
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (source target : State) : ℝ :=
  if hOffDiagonal : source ≠ target then
    rengerDirectionalFlowHybridBVFlowDerivative path time
      ⟨(source, target), hOffDiagonal⟩
  else 0

/-- The subtype-indexed target divergence is exactly the complete divergence of the totalized raw
real target flow. -/
theorem rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_rawFlowDivergence
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ) (state : State) :
    rengerDirectionalFlowHybridBVTargetFlowDivergence path time state =
      finiteStateFlowDivergence
        (rengerDirectionalFlowHybridBVRawFlowDerivativeValue path time) state := by
  unfold rengerDirectionalFlowHybridBVTargetFlowDivergence finiteStateFlowDivergence
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue
  rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
    Fintype.sum_eq_add_sum_subtype_ne _ state]
  simp only [ne_eq, not_true_eq_false, ↓reduceDIte, zero_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro source _hSource
    simp [source.property]
  · apply Finset.sum_congr rfl
    intro target _hTarget
    simp [Ne.symm target.property]

/-- The subtype-indexed target divergence is the complete finite-state divergence of the
measurable ordered-flow version. -/
theorem rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_finiteStateFlowDivergence
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (time : ℝ)
    (hFlowNonnegative : ∀ transition,
      0 ≤ rengerDirectionalFlowHybridBVFlowDerivative path time transition)
    (state : State) :
    rengerDirectionalFlowHybridBVTargetFlowDivergence path time state =
      finiteStateFlowDivergence
        (fun source target ↦
          (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
            path time source target : ℝ)) state := by
  unfold rengerDirectionalFlowHybridBVTargetFlowDivergence finiteStateFlowDivergence
  rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
    Fintype.sum_eq_add_sum_subtype_ne _ state]
  simp only [rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt,
    ne_eq, not_true_eq_false, ↓reduceDIte, NNReal.coe_zero, zero_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro source _hSource
    simp only [source.property, not_false_eq_true, dite_true,
      rengerDirectionalFlowHybridBVFlowDerivativeAt]
    exact (Real.coe_toNNReal _ (hFlowNonnegative _)).symm
  · apply Finset.sum_congr rfl
    intro target _hTarget
    have hOffDiagonal : state ≠ target.1 := Ne.symm target.property
    simp only [hOffDiagonal, not_false_eq_true, dite_true,
      rengerDirectionalFlowHybridBVFlowDerivativeAt]
    exact (Real.coe_toNNReal _ (hFlowNonnegative _)).symm

/-- On every admissible target, the raw and measurable complete target-flow divergences agree
almost everywhere on the physical interval. -/
theorem ae_rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_finiteStateFlowDivergence
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state =
        finiteStateFlowDivergence
          (fun source target ↦
            (rengerDirectionalFlowHybridBVMeasurableFlowDerivativeAt
              path.1 time source target : ℝ)) state := by
  filter_upwards [path.2.flowDerivativeNonnegativeAE] with time hFlowNonnegative
  exact rengerDirectionalFlowHybridBVTargetFlowDivergence_eq_finiteStateFlowDivergence
    path.1 time hFlowNonnegative state

/-- Every target-flow divergence coordinate is integrable on the complete physical interval. -/
theorem integrable_rengerDirectionalFlowHybridBVTargetFlowDivergence
    (path : RengerDirectionalFlowHybridBVPath State duration) (state : State) :
    Integrable
      (fun time ↦ rengerDirectionalFlowHybridBVTargetFlowDivergence path time state)
      (finiteOpenIntervalVolume duration) := by
  apply Integrable.sub
  · exact integrable_finsetSum Finset.univ fun source _hSource ↦
      integrable_rengerDirectionalFlowHybridBVFlowDerivative path
        ⟨(source.1, state), source.property⟩
  · exact integrable_finsetSum Finset.univ fun target _hTarget ↦
      integrable_rengerDirectionalFlowHybridBVFlowDerivative path
        ⟨(state, target.1), target.property.symm⟩

/-- Every admissible target density coordinate is its recovered initial trace plus the integrated
incoming-minus-outgoing directional-flow derivative. -/
theorem rengerDirectionalFlowHybridBVDensityValue_eq_initial_add_integral_flowDivergence
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityValue path.1 time state =
      path.1.initialTrace (Sum.inl state) +
        ∫ point in Ioo 0 time,
          ((∑ source : {source : State // source ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path.1 point
                ⟨(source.1, state), source.property⟩) -
            ∑ target : {target : State // target ≠ state},
              rengerDirectionalFlowHybridBVFlowDerivative path.1 point
                ⟨(state, target.1), target.property.symm⟩)
          ∂volume := by
  have hReconstruction :=
    path.1.cadlagRepresentative_eq_initial_add_integral_derivativeDensity
      path.2.absolutelyContinuousDerivative (Sum.inl state)
      hTime.1 hTime.2
  change rengerDirectionalFlowHybridBVDensityValue path.1 time state =
      path.1.initialTrace (Sum.inl state) +
        ∫ point in Ioc 0 time,
          rengerDirectionalFlowHybridBVDensityDerivative path.1 point state
          ∂finiteOpenIntervalVolume duration at hReconstruction
  have hElapsedMeasure :
      (finiteOpenIntervalVolume duration).restrict (Ioc 0 time) =
        volume.restrict (Ioo 0 time) :=
    finiteOpenIntervalVolume_restrict_Ioc_zero_eq_volume_restrict_Ioo hTime.2
  have hReconstructionOpen :
      rengerDirectionalFlowHybridBVDensityValue path.1 time state =
        path.1.initialTrace (Sum.inl state) +
          ∫ point in Ioo 0 time,
            rengerDirectionalFlowHybridBVDensityDerivative path.1 point state
            ∂volume := by
    rw [← hElapsedMeasure]
    exact hReconstruction
  rw [hReconstructionOpen]
  congr 1
  apply integral_congr_ae
  rw [← hElapsedMeasure]
  exact ae_restrict_of_ae <|
    path.2.continuityEquationAE.mono fun point hContinuity ↦ hContinuity state

/-- On the open physical interval, the target-flow divergence is almost everywhere the classical
derivative of the selected target density coordinate. -/
theorem ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (state : State) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      HasDerivAt
        (fun horizon ↦ rengerDirectionalFlowHybridBVDensityValue path.1 horizon state)
        (rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 time state)
        time := by
  have hDivergenceIntervalIntegrable : IntervalIntegrable
      (rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 · state)
      volume 0 duration := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hDuration.le]
    exact integrable_rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 state
  have hPrimitiveDerivative := hDivergenceIntervalIntegrable.ae_hasDerivAt_integral
  filter_upwards [ae_restrict_of_ae hPrimitiveDerivative,
    ae_restrict_mem measurableSet_Ioo] with time hDerivative hTime
  have hLocalEquality :
      (fun horizon ↦ rengerDirectionalFlowHybridBVDensityValue path.1 horizon state) =ᶠ[nhds time]
      fun horizon ↦
        path.1.initialTrace (Sum.inl state) +
          ∫ markedTime : ℝ in 0..horizon,
            rengerDirectionalFlowHybridBVTargetFlowDivergence path.1 markedTime state := by
    filter_upwards [Ioo_mem_nhds hTime.1 hTime.2] with horizon hHorizon
    have hEquation :=
      rengerDirectionalFlowHybridBVDensityValue_eq_initial_add_integral_flowDivergence
        hDuration path ⟨hHorizon.1.le, hHorizon.2⟩ state
    change rengerDirectionalFlowHybridBVDensityValue path.1 horizon state =
      path.1.initialTrace (Sum.inl state) +
        ∫ markedTime : ℝ in Ioo 0 horizon,
          rengerDirectionalFlowHybridBVTargetFlowDivergence
            path.1 markedTime state at hEquation
    rw [intervalIntegral.integral_of_le hHorizon.1.le,
      integral_Ioc_eq_integral_Ioo]
    exact hEquation
  apply HasDerivAt.congr_of_eventuallyEq _ hLocalEquality
  have hTimeInterval : time ∈ uIcc 0 duration := by
    rw [uIcc_of_le hDuration.le]
    exact ⟨hTime.1.le, hTime.2.le⟩
  have hZeroInterval : (0 : ℝ) ∈ uIcc 0 duration := by
    rw [uIcc_of_le hDuration.le]
    exact ⟨le_rfl, hDuration.le⟩
  exact (hDerivative hTimeInterval 0 hZeroInterval).const_add
    (path.1.initialTrace (Sum.inl state))

end

end FiniteMarkovProcesses.InformationTheory
