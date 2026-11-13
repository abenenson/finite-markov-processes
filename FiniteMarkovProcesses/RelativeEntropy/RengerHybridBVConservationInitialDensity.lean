/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1PathWeightedCoordinateIntegral
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteJumpHistoryRengerHybridBVSourceSupport
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVKinematicClosure
public import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff

/-!
# Continuous conservation recovery of the initial density

The raw initial trace of a hybrid bounded-variation path is not globally continuous in the
published topology.  On a path satisfying the integrated density--directional-flow continuity
law, however, the initial density is recoverable from a continuous strong-`L1` functional: average
the density minus incoming cumulative flow plus outgoing cumulative flow against one fixed
positive interior test.  This module constructs that functional without changing the carrier or
topology.

## Main declarations

* `rengerDirectionalFlowHybridBVConservationAveragingTest` is the fixed positive interior test.
* `rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate` is the continuous recovered
  initial coordinate on the whole hybrid carrier.
* `rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_eq_initialTrace` identifies
  it with the actual initial trace whenever integrated continuity holds.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory Set
open scoped BigOperators CompactlySupported Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability
open FiniteMarkovProcesses.Probability.PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- A fixed continuous test supported on the physical interval and positive on a nonempty
interior core.  Its integral supplies the normalization of conservation recovery. -/
noncomputable def rengerDirectionalFlowHybridBVConservationAveragingTest
    (duration : ℝ) (hDuration : 0 < duration) : C_c(ℝ, ℝ) :=
  finiteOpenIntervalCoreCutoff duration (duration / 3) (by positivity)

/-- The fixed conservation-averaging test has strictly positive physical-time integral. -/
theorem integral_rengerDirectionalFlowHybridBVConservationAveragingTest_pos
    (duration : ℝ) (hDuration : 0 < duration) :
    0 < ∫ time,
      rengerDirectionalFlowHybridBVConservationAveragingTest duration hDuration time
        ∂finiteOpenIntervalVolume duration := by
  let test := rengerDirectionalFlowHybridBVConservationAveragingTest duration hDuration
  have hTestIntegrable : IntervalIntegrable test volume 0 duration :=
    test.continuous.intervalIntegrable 0 duration
  have hCoreOrder : duration / 3 ≤ duration - duration / 3 := by linarith
  have hCoreIntegral :
      (∫ time in duration / 3..duration - duration / 3, test time) = duration / 3 := by
    rw [show (∫ time in duration / 3..duration - duration / 3, test time) =
        ∫ _time in duration / 3..duration - duration / 3, (1 : ℝ) by
      apply intervalIntegral.integral_congr
      intro time hTime
      have hTimeIcc : time ∈ Icc (duration / 3) (duration - duration / 3) := by
        simpa only [uIcc_of_le hCoreOrder] using hTime
      exact finiteOpenIntervalCoreCutoff_eq_one_of_mem_core (by positivity) hTimeIcc]
    simp
    ring
  have hCoreLe :
      (∫ time in duration / 3..duration - duration / 3, test time) ≤
        ∫ time in 0..duration, test time := by
    exact intervalIntegral.integral_mono_interval
      (by positivity) hCoreOrder (by linarith)
      (Filter.Eventually.of_forall fun time =>
        (finiteOpenIntervalCoreCutoff_mem_Icc (by positivity) time).1)
      hTestIntegrable
  have hIntervalPositive : 0 < ∫ time in 0..duration, test time := by
    calc
      0 < duration / 3 := by positivity
      _ = ∫ time in duration / 3..duration - duration / 3, test time :=
        hCoreIntegral.symm
      _ ≤ ∫ time in 0..duration, test time := hCoreLe
  have hConstant := integral_compactTest_mul_constant_finiteOpenIntervalVolume
    (duration := duration) test 1 hDuration.le
  have hMeasureIntegral :
      (∫ time, test time ∂finiteOpenIntervalVolume duration) =
        ∫ time in 0..duration, test time := by
    simpa only [mul_one, one_mul] using hConstant
  rw [hMeasureIntegral]
  exact hIntervalPositive

/-- Continuous whole-carrier recovery of one initial-density coordinate from the strong-`L1`
density and cumulative directional-flow values. -/
noncomputable def rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) (state : State) : ℝ :=
  let test := rengerDirectionalFlowHybridBVConservationAveragingTest duration hDuration
  let weightedCoordinate := fun coordinate =>
    finiteIntervalL1PathWeightedCoordinateIntegral test coordinate
      path.toDerivativePath.toL1Path
  (weightedCoordinate (Sum.inl state) -
      ∑ source : {source : State // source ≠ state},
        weightedCoordinate (Sum.inr ⟨(source, state), source.property⟩) +
      ∑ target : {target : State // target ≠ state},
        weightedCoordinate (Sum.inr ⟨(state, target), target.property.symm⟩)) /
    ∫ time, test time ∂finiteOpenIntervalVolume duration

/-- Whole finite-state coordinate family recovered continuously from pathwise conservation. -/
noncomputable def rengerDirectionalFlowHybridBVConservationInitialDensity
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) : State → ℝ :=
  fun state =>
    rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate hDuration path state

/-- Every conservation-recovered coordinate is continuous in the published hybrid topology. -/
theorem continuous_rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
    (hDuration : 0 < duration) (state : State) :
    Continuous fun path : RengerDirectionalFlowHybridBVPath State duration =>
      rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
        hDuration path state := by
  let test := rengerDirectionalFlowHybridBVConservationAveragingTest duration hDuration
  have hCoordinate (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
      Continuous fun path : RengerDirectionalFlowHybridBVPath State duration =>
        finiteIntervalL1PathWeightedCoordinateIntegral test coordinate
          path.toDerivativePath.toL1Path :=
    (continuous_finiteIntervalL1PathWeightedCoordinateIntegral test coordinate).comp
      FiniteIntervalHybridBVPath.continuous_toL1Path
  unfold rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
  dsimp only
  fun_prop

/-- Conservation recovery is continuous as a complete finite coordinate family. -/
theorem continuous_rengerDirectionalFlowHybridBVConservationInitialDensity
    (hDuration : 0 < duration) :
    Continuous fun path : RengerDirectionalFlowHybridBVPath State duration =>
      rengerDirectionalFlowHybridBVConservationInitialDensity hDuration path := by
  apply continuous_pi
  intro state
  exact continuous_rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
    hDuration state

/-- Closed coupling relation between one typed simplex point and one hybrid path whose continuous
conservation recovery has exactly those real coordinates. -/
def RengerDirectionalFlowHybridBVConservationInitialDensityGraph
    (hDuration : 0 < duration) :
    Set (FiniteStateProbabilityDensity State ×
      RengerDirectionalFlowHybridBVPath State duration) :=
  {densityPath |
    densityPath.1.realWeight =
      rengerDirectionalFlowHybridBVConservationInitialDensity hDuration densityPath.2}

/-- The conservation density--path coupling is closed in the product of the finite simplex and
the published hybrid topology. -/
theorem isClosed_rengerDirectionalFlowHybridBVConservationInitialDensityGraph
    (hDuration : 0 < duration) :
    IsClosed
      (RengerDirectionalFlowHybridBVConservationInitialDensityGraph
        (State := State) hDuration) := by
  exact isClosed_eq
    (FiniteStateProbabilityDensity.continuous_realWeight.comp continuous_fst)
    ((continuous_rengerDirectionalFlowHybridBVConservationInitialDensity hDuration).comp
      continuous_snd)

/-- The closed conservation graph is measurable in the product carrier's native measurable
structure.  This proof uses its defining coordinate equality directly and does not require the
product topology to generate that measurable structure. -/
theorem measurableSet_rengerDirectionalFlowHybridBVConservationInitialDensityGraph
    (hDuration : 0 < duration) :
    MeasurableSet
      (RengerDirectionalFlowHybridBVConservationInitialDensityGraph
        (State := State) hDuration) := by
  unfold RengerDirectionalFlowHybridBVConservationInitialDensityGraph
  exact measurableSet_eq_fun
    (FiniteStateProbabilityDensity.continuous_realWeight.measurable.comp measurable_fst)
    ((continuous_rengerDirectionalFlowHybridBVConservationInitialDensity hDuration).measurable.comp
      measurable_snd)

private theorem rengerDirectionalFlowHybridBVWeightedCoordinateIntegral_eq_representative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (test : C_c(ℝ, ℝ)) (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
    finiteIntervalL1PathWeightedCoordinateIntegral test coordinate
        path.toDerivativePath.toL1Path =
      ∫ time, test time * path.cadlagRepresentative.representative time coordinate
        ∂finiteOpenIntervalVolume duration := by
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral]
  obtain ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩ :=
    path.cadlagRepresentative.represents
  have hEventually :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq
      path.toDerivativePath.toL1Path path.cadlagRepresentative.representative
      hRepresentativeMemLp).mp ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩
  apply integral_congr_ae
  filter_upwards [hEventually] with time hTime
  rw [hTime]

/-- Integrated continuity identifies the continuous conservation recovery with the separately
carried initial density trace. -/
theorem rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_eq_initialTrace
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hContinuity : RengerDirectionalFlowHybridBVIntegratedContinuity path)
    (state : State) :
    rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate hDuration path state =
      path.initialTrace (Sum.inl state) := by
  classical
  let test := rengerDirectionalFlowHybridBVConservationAveragingTest duration hDuration
  let representative := path.cadlagRepresentative.representative
  have hRepresentativeMemLp := Classical.choose path.cadlagRepresentative.represents
  have hCoordinateIntegrable
      (coordinate : EmpiricalDensityDirectionalFlowCoordinate State) :
      Integrable (fun time => test time * representative time coordinate)
        (finiteOpenIntervalVolume duration) := by
    have hRepresentativeIntegrable : Integrable representative
        (finiteOpenIntervalVolume duration) :=
      memLp_one_iff_integrable.mp hRepresentativeMemLp
    have hScalarIntegrable : Integrable (fun time => representative time coordinate)
        (finiteOpenIntervalVolume duration) :=
      ContinuousLinearMap.integrable_comp
        (PiLp.proj (𝕜 := ℝ) (p := 1)
          (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ) coordinate)
        hRepresentativeIntegrable
    have hTestBound : ∀ᵐ time ∂finiteOpenIntervalVolume duration, ‖test time‖ ≤ 1 :=
      Filter.Eventually.of_forall fun time => by
        change ‖finiteOpenIntervalCoreCutoff duration (duration / 3) (by positivity) time‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg
          (finiteOpenIntervalCoreCutoff_mem_Icc (by positivity) time).1]
        exact (finiteOpenIntervalCoreCutoff_mem_Icc (by positivity) time).2
    exact hScalarIntegrable.bdd_mul test.continuous.aestronglyMeasurable hTestBound
  have hIncoming :
      (∑ source : {source : State // source ≠ state},
        ∫ time, test time * representative time
          (Sum.inr ⟨(source, state), source.property⟩)
          ∂finiteOpenIntervalVolume duration) =
        ∫ time, test time *
          (∑ source : {source : State // source ≠ state},
            representative time (Sum.inr ⟨(source, state), source.property⟩))
          ∂finiteOpenIntervalVolume duration := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    intro source _
    exact hCoordinateIntegrable (Sum.inr ⟨(source, state), source.property⟩)
  have hOutgoing :
      (∑ target : {target : State // target ≠ state},
        ∫ time, test time * representative time
          (Sum.inr ⟨(state, target), target.property.symm⟩)
          ∂finiteOpenIntervalVolume duration) =
        ∫ time, test time *
          (∑ target : {target : State // target ≠ state},
            representative time (Sum.inr ⟨(state, target), target.property.symm⟩))
          ∂finiteOpenIntervalVolume duration := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    intro target _
    exact hCoordinateIntegrable (Sum.inr ⟨(state, target), target.property.symm⟩)
  have hInitialIntegrable : Integrable
      (fun time => test time * path.initialTrace (Sum.inl state))
      (finiteOpenIntervalVolume duration) := by
    exact (test.continuous.memLp_top_of_hasCompactSupport test.hasCompactSupport
      (finiteOpenIntervalVolume duration)).integrable (by simp) |>.mul_const _
  have hIncomingIntegrable : Integrable
      (fun time => test time *
        (∑ source : {source : State // source ≠ state},
          representative time (Sum.inr ⟨(source, state), source.property⟩)))
      (finiteOpenIntervalVolume duration) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ fun
        (source : {source : State // source ≠ state}) _ =>
      hCoordinateIntegrable (Sum.inr ⟨(source, state), source.property⟩)
  have hOutgoingIntegrable : Integrable
      (fun time => test time *
        (∑ target : {target : State // target ≠ state},
          representative time (Sum.inr ⟨(state, target), target.property.symm⟩)))
      (finiteOpenIntervalVolume duration) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ fun
        (target : {target : State // target ≠ state}) _ =>
      hCoordinateIntegrable (Sum.inr ⟨(state, target), target.property.symm⟩)
  have hNumerator :
      (∫ time, test time * representative time (Sum.inl state)
          ∂finiteOpenIntervalVolume duration) -
        (∫ time, test time *
          (∑ source : {source : State // source ≠ state},
            representative time (Sum.inr ⟨(source, state), source.property⟩))
          ∂finiteOpenIntervalVolume duration) +
        (∫ time, test time *
          (∑ target : {target : State // target ≠ state},
            representative time (Sum.inr ⟨(state, target), target.property.symm⟩))
          ∂finiteOpenIntervalVolume duration) =
        path.initialTrace (Sum.inl state) *
          ∫ time, test time ∂finiteOpenIntervalVolume duration := by
    calc
      _ = (∫ time,
            (test time * representative time (Sum.inl state) -
              test time *
                (∑ source : {source : State // source ≠ state},
                  representative time (Sum.inr ⟨(source, state), source.property⟩)))
            ∂finiteOpenIntervalVolume duration) +
          ∫ time, test time *
              (∑ target : {target : State // target ≠ state},
                representative time (Sum.inr ⟨(state, target), target.property.symm⟩))
            ∂finiteOpenIntervalVolume duration := by
        rw [integral_sub (hCoordinateIntegrable (Sum.inl state)) hIncomingIntegrable]
      _ = ∫ time,
          (test time * representative time (Sum.inl state) -
            test time *
              (∑ source : {source : State // source ≠ state},
                representative time (Sum.inr ⟨(source, state), source.property⟩))) +
            test time *
              (∑ target : {target : State // target ≠ state},
                representative time (Sum.inr ⟨(state, target), target.property.symm⟩))
          ∂finiteOpenIntervalVolume duration := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_add
            ((hCoordinateIntegrable (Sum.inl state)).sub hIncomingIntegrable)
            hOutgoingIntegrable).symm
      _ = ∫ time, test time * path.initialTrace (Sum.inl state)
          ∂finiteOpenIntervalVolume duration := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
        have hBalance := hContinuity state time ⟨hTime.1.le, hTime.2⟩
        unfold rengerDirectionalFlowHybridBVDensityValue
          rengerDirectionalFlowHybridBVCumulativeFlowValue at hBalance
        dsimp only [representative] at hBalance ⊢
        rw [hBalance]
        ring
      _ = ∫ time, path.initialTrace (Sum.inl state) * test time
          ∂finiteOpenIntervalVolume duration := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun time => by ring
      _ = path.initialTrace (Sum.inl state) *
          ∫ time, test time ∂finiteOpenIntervalVolume duration :=
        integral_const_mul _ _
  unfold rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate
  dsimp only
  simp_rw [rengerDirectionalFlowHybridBVWeightedCoordinateIntegral_eq_representative]
  rw [hIncoming, hOutgoing, hNumerator]
  exact mul_div_cancel_right₀ _
    (ne_of_gt (integral_rengerDirectionalFlowHybridBVConservationAveragingTest_pos
      duration hDuration))

/-- On an integrated-continuity path, the full conservation-recovered family is the separately
carried real initial-density trace. -/
theorem rengerDirectionalFlowHybridBVConservationInitialDensity_eq_initialTrace
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hContinuity : RengerDirectionalFlowHybridBVIntegratedContinuity path) :
    rengerDirectionalFlowHybridBVConservationInitialDensity hDuration path =
      fun state => path.initialTrace (Sum.inl state) := by
  funext state
  exact rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_eq_initialTrace
    hDuration hContinuity state

/-- On every ordered finite empirical observation, conservation recovery is exactly the literal
empirical initial density counted from the microscopic histories. -/
theorem
    rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_explicitObservation_eq
    [MeasurableSpace State] [_unusedMeasurableSingletonClass : MeasurableSingletonClass State]
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (state : State) :
    rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate hDuration
        (empiricalDensityDirectionalFlowExplicitHybridBVPath
          successorIndex histories duration hOrdered) state =
      PositiveFiniteJumpHistoryReplicas.empiricalInitialDensity
        successorIndex histories state := by
  rw [rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_eq_initialTrace
    hDuration
      (empiricalDensityDirectionalFlowExplicitHybridBVPath_integratedContinuity
        successorIndex histories duration hDuration hOrdered)]
  rw [empiricalDensityDirectionalFlowExplicitHybridBVPath_initialTrace
    successorIndex histories duration hDuration hOrdered]
  exact empiricalDensityDirectionalFlowInitialL1Value_density
    successorIndex histories state

/-- On every ordered finite empirical observation, the complete conservation recovery is the
real coordinate embedding of the microscopic empirical initial density. -/
theorem rengerDirectionalFlowHybridBVConservationInitialDensity_explicitObservation_eq
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (successorIndex : ℕ)
    (histories : PositiveFiniteJumpHistoryReplicas State successorIndex)
    (duration : ℝ) (hDuration : 0 < duration)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    rengerDirectionalFlowHybridBVConservationInitialDensity hDuration
        (empiricalDensityDirectionalFlowExplicitHybridBVPath
          successorIndex histories duration hOrdered) =
      (finiteIIDEmpiricalProbabilityDensity
        successorIndex (fun replica => (histories replica).initialState)).realWeight := by
  funext state
  change rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate hDuration
      (empiricalDensityDirectionalFlowExplicitHybridBVPath
        successorIndex histories duration hOrdered) state = _
  rw [rengerDirectionalFlowHybridBVConservationInitialDensityCoordinate_explicitObservation_eq
    successorIndex histories duration hDuration hOrdered state]
  unfold PositiveFiniteJumpHistoryReplicas.empiricalInitialDensity
    FiniteStateProbabilityDensity.realWeight finiteIIDEmpiricalProbabilityDensity
    finiteIIDPositiveSampleStateCount
  simp only [NNReal.coe_div, NNReal.coe_natCast,
    FiniteJumpHistory.stateMembershipIndicator]
  congr 1
  have hCount :
      (∑ replica,
        if (histories replica).initialState = state then 1 else 0 : ℕ) =
        (Finset.univ.filter fun replica =>
          (histories replica).initialState = state).card :=
    Finset.sum_boole
      (fun replica => (histories replica).initialState = state) Finset.univ
  calc
    (∑ replica,
        if (histories replica).initialState = state then (1 : ℝ) else 0) =
        ((∑ replica,
          if (histories replica).initialState = state then 1 else 0 : ℕ) : ℝ) := by
      norm_cast
    _ = ((Finset.univ.filter fun replica =>
        (histories replica).initialState = state).card : ℝ) := by
      exact_mod_cast hCount

end

end FiniteMarkovProcesses.InformationTheory
