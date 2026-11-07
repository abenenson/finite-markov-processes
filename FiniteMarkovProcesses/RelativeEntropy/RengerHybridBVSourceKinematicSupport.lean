/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVKinematicClosure
import
  FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalVagueSignedMeasureBoundaryCutoff

/-!
# Source-kinematic support for Renger hybrid paths

This module isolates the topology-closed interior constraints carried by finite empirical
directional-flow observations.  Unlike finite-rate admissibility, this support permits singular
positive ordered-flow derivatives and does not impose the recovered zero initial-flow trace.
That missing trace is exactly the boundary-escape sector invisible to the relative derivative
topology and must be controlled probabilistically.

## Main declarations

* `RengerDirectionalFlowHybridBVSourceKinematicSupport` records the strong-`L1` simplex and
  cumulative-flow constraints, positive ordered-flow derivative measures, and exact derivative
  continuity.
* `rengerDirectionalFlowHybridBVSourceKinematicSupport_of_tendsto` proves sequential closure in
  the published hybrid topology without assuming finite dynamic action.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The interior source constraints retained under the boundary-blind hybrid topology.  Initial
zero flow and absolute continuity are deliberately absent. -/
structure RengerDirectionalFlowHybridBVSourceKinematicSupport
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hDuration : 0 < duration) : Prop where
  /-- Open-interval density coordinates are nonnegative almost everywhere. -/
  densityNonnegativeAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue path time state
  /-- Open-interval density coordinates sum to one almost everywhere. -/
  densityNormalizedAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∑ state, rengerDirectionalFlowHybridBVDensityValue path time state = 1
  /-- Open-interval cumulative directional flows are nonnegative almost everywhere. -/
  cumulativeFlowNonnegativeAE :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ transition,
        0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue path time transition
  /-- Every ordered-flow Stieltjes derivative is a nonnegative signed measure. -/
  flowDerivativeMeasureNonnegative :
    ∀ transition,
      0 ≤ (path.toDerivativePath.derivative
        (Sum.inr transition)).toSignedMeasure
  /-- The carried signed derivatives satisfy exact mass continuity. -/
  derivativeContinuity : RengerDirectionalFlowHybridBVDerivativeContinuity path

/-- Finite-rate admissibility lies inside source-kinematic support. -/
theorem RengerDirectionalFlowHybridBVAdmissible.sourceKinematicSupport
    {path : RengerDirectionalFlowHybridBVPath State duration}
    {hDuration : 0 < duration}
    (admissible : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    RengerDirectionalFlowHybridBVSourceKinematicSupport path hDuration where
  densityNonnegativeAE := admissible.densityNonnegativeAE
  densityNormalizedAE := admissible.densityNormalizedAE
  cumulativeFlowNonnegativeAE := admissible.cumulativeFlowNonnegativeAE
  flowDerivativeMeasureNonnegative := by
    intro transition
    rw [← path.withDensity_derivativeDensity_eq_derivative
      admissible.absolutelyContinuousDerivative (Sum.inr transition)]
    exact SignedMeasure.zero_le_withDensityᵥ_of_ae_nonnegative
      (SignedMeasure.integrable_rnDeriv _ _)
      (admissible.flowDerivativeNonnegativeAE.mono fun _ hTime => hTime transition)
  derivativeContinuity :=
    rengerDirectionalFlowHybridBVDerivativeContinuity_of_admissible admissible

private theorem finiteCoordinateL1Value_coordinate_tendsto
    {Coordinate : Type*}
    {values : ℕ → FiniteCoordinateL1Value Coordinate}
    {limit : FiniteCoordinateL1Value Coordinate}
    (hTendsto : Tendsto values atTop (nhds limit)) (coordinate : Coordinate) :
    Tendsto (fun sequenceIndex => values sequenceIndex coordinate)
      atTop (nhds (limit coordinate)) := by
  have hProjection :=
    (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).continuous
      |>.continuousAt.tendsto.comp hTendsto
  simpa only [Function.comp_def, PiLp.proj_apply] using! hProjection

/-- Exact signed-measure continuity implies the matching identity against every relative
open-interval derivative test. -/
theorem rengerDirectionalFlowHybridBVDerivativeContinuity_testIntegral
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hContinuity : RengerDirectionalFlowHybridBVDerivativeContinuity path)
    (state : State)
    (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    (path.toDerivativePath.derivative (Sum.inl state)).continuousTestIntegral test.1 =
      (∑ source : {source : State // source ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral test.1) -
      ∑ target : {target : State // target ≠ state},
        (path.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral
            test.1 := by
  classical
  let incoming : VagueSignedMeasure ℝ := VagueSignedMeasure.ofSignedMeasure <|
    ∑ source : {source : State // source ≠ state},
      (path.toDerivativePath.derivative
        (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure
  let outgoing : VagueSignedMeasure ℝ := VagueSignedMeasure.ofSignedMeasure <|
    ∑ target : {target : State // target ≠ state},
      (path.toDerivativePath.derivative
        (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure
  let balance := VagueSignedMeasure.add incoming
    (VagueSignedMeasure.realScalarMultiple (-1) outgoing)
  have hBalance : balance.toSignedMeasure =
      incoming.toSignedMeasure - outgoing.toSignedMeasure := by
    simpa only [balance, VagueSignedMeasure.add, VagueSignedMeasure.realScalarMultiple,
      VagueSignedMeasure.toSignedMeasure_ofSignedMeasure, sub_eq_add_neg] using!
      congrArg (fun measure : SignedMeasure ℝ => incoming.toSignedMeasure + measure)
        (neg_one_smul (R := ℝ) outgoing.toSignedMeasure)
  have hMeasure :
      (path.toDerivativePath.derivative (Sum.inl state)).toSignedMeasure =
        balance.toSignedMeasure := by
    rw [hBalance]
    exact hContinuity state
  calc
    (path.toDerivativePath.derivative (Sum.inl state)).continuousTestIntegral test.1 =
        balance.continuousTestIntegral test.1 := by
      exact congrArg
        (fun measure : SignedMeasure ℝ =>
          (VagueSignedMeasure.ofSignedMeasure measure).continuousTestIntegral test.1)
        hMeasure
    _ = incoming.continuousTestIntegral test.1 -
        outgoing.continuousTestIntegral test.1 := by
      simp [balance, sub_eq_add_neg]
    _ = _ := by
      rw [show incoming.continuousTestIntegral test.1 =
          ∑ source : {source : State // source ≠ state},
            (path.toDerivativePath.derivative
              (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral
                test.1 by
        simpa only [incoming] using
          VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
            (fun source : {source : State // source ≠ state} =>
              path.toDerivativePath.derivative
                (Sum.inr ⟨(source, state), source.property⟩)) test.1]
      rw [show outgoing.continuousTestIntegral test.1 =
          ∑ target : {target : State // target ≠ state},
            (path.toDerivativePath.derivative
              (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral
                test.1 by
        simpa only [outgoing] using
          VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
            (fun target : {target : State // target ≠ state} =>
              path.toDerivativePath.derivative
                (Sum.inr ⟨(state, target), target.property.symm⟩)) test.1]

/-- Source-kinematic support is sequentially closed in the published strong-`L1` plus relative
vague-derivative topology.  Boundary mass may disappear, but positivity, simplex values, and the
exact interior continuity equation survive. -/
theorem rengerDirectionalFlowHybridBVSourceKinematicSupport_of_tendsto
    (hDuration : 0 < duration)
    (paths : ℕ → RengerDirectionalFlowHybridBVPath State duration)
    (limitPath : RengerDirectionalFlowHybridBVPath State duration)
    (hPaths : ∀ sequenceIndex,
      RengerDirectionalFlowHybridBVSourceKinematicSupport
        (paths sequenceIndex) hDuration)
    (hTendsto : Tendsto paths atTop (nhds limitPath)) :
    RengerDirectionalFlowHybridBVSourceKinematicSupport limitPath hDuration := by
  classical
  have hL1Tendsto := (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).1
  obtain ⟨subsequence, _hSubsequenceMonotone, hRepresentativeTendsto⟩ :=
    exists_subsequence_tendsto_cadlagRepresentative_ae_of_tendsto_toL1Path
      paths limitPath hL1Tendsto
  have hSequenceValueConstraints :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration, ∀ sequenceIndex,
        (∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue
          (paths sequenceIndex) time state) ∧
        (∑ state, rengerDirectionalFlowHybridBVDensityValue
          (paths sequenceIndex) time state = 1) ∧
        ∀ transition, 0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue
          (paths sequenceIndex) time transition := by
    rw [ae_all_iff]
    intro sequenceIndex
    filter_upwards [(hPaths sequenceIndex).densityNonnegativeAE,
      (hPaths sequenceIndex).densityNormalizedAE,
      (hPaths sequenceIndex).cumulativeFlowNonnegativeAE] with
      time hDensity hNormalized hFlow
    exact ⟨hDensity, hNormalized, hFlow⟩
  have hLimitValueConstraints :
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        (∀ state, 0 ≤ rengerDirectionalFlowHybridBVDensityValue
          limitPath time state) ∧
        (∑ state, rengerDirectionalFlowHybridBVDensityValue
          limitPath time state = 1) ∧
        ∀ transition, 0 ≤ rengerDirectionalFlowHybridBVCumulativeFlowValue
          limitPath time transition := by
    filter_upwards [hRepresentativeTendsto, hSequenceValueConstraints] with
      time hTimeTendsto hTimeConstraints
    have hCoordinateTendsto := finiteCoordinateL1Value_coordinate_tendsto hTimeTendsto
    refine ⟨fun state => ?_, ?_, fun transition => ?_⟩
    · apply ge_of_tendsto' (hCoordinateTendsto (Sum.inl state))
      exact fun sequenceIndex => (hTimeConstraints (subsequence sequenceIndex)).1 state
    · apply tendsto_nhds_unique
        (tendsto_finsetSum Finset.univ fun state _ =>
          hCoordinateTendsto (Sum.inl state))
      exact tendsto_const_nhds.congr' <| Filter.Eventually.of_forall fun sequenceIndex =>
        (hTimeConstraints (subsequence sequenceIndex)).2.1.symm
    · apply ge_of_tendsto' (hCoordinateTendsto (Sum.inr transition))
      exact fun sequenceIndex =>
        (hTimeConstraints (subsequence sequenceIndex)).2.2 transition
  refine
    { densityNonnegativeAE := hLimitValueConstraints.mono fun _ hTime => hTime.1
      densityNormalizedAE := hLimitValueConstraints.mono fun _ hTime => hTime.2.1
      cumulativeFlowNonnegativeAE := hLimitValueConstraints.mono fun _ hTime => hTime.2.2
      flowDerivativeMeasureNonnegative := ?_
      derivativeContinuity := ?_ }
  · intro transition
    apply VagueSignedMeasure.zero_le_toSignedMeasure_of_relativeTestTendsto_of_zero_le
      (indexFilter := atTop)
      hDuration
      (fun sequenceIndex =>
        (paths sequenceIndex).toDerivativePath.derivative (Sum.inr transition))
      (limitPath.toDerivativePath.derivative (Sum.inr transition))
    · exact (Classical.choose_spec limitPath.hasCadlagDerivativeRealization).1
        (Sum.inr transition)
    · exact (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).2
        (Sum.inr transition)
    · exact fun sequenceIndex =>
        (hPaths sequenceIndex).flowDerivativeMeasureNonnegative transition
  · intro state
    let incoming : VagueSignedMeasure ℝ := VagueSignedMeasure.ofSignedMeasure <|
      ∑ source : {source : State // source ≠ state},
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure
    let outgoing : VagueSignedMeasure ℝ := VagueSignedMeasure.ofSignedMeasure <|
      ∑ target : {target : State // target ≠ state},
        (limitPath.toDerivativePath.derivative
          (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure
    let balance := VagueSignedMeasure.add incoming
      (VagueSignedMeasure.realScalarMultiple (-1) outgoing)
    have hBalance : balance.toSignedMeasure =
        incoming.toSignedMeasure - outgoing.toSignedMeasure := by
      simpa only [balance, VagueSignedMeasure.add, VagueSignedMeasure.realScalarMultiple,
        VagueSignedMeasure.toSignedMeasure_ofSignedMeasure, sub_eq_add_neg] using!
        congrArg (fun measure : SignedMeasure ℝ => incoming.toSignedMeasure + measure)
          (neg_one_smul (R := ℝ) outgoing.toSignedMeasure)
    have hEquality :
        limitPath.toDerivativePath.derivative (Sum.inl state) = balance := by
      apply VagueSignedMeasure.eq_of_restrict_openInterval_of_relativeTestIntegral_eq
        hDuration
      · exact (Classical.choose_spec limitPath.hasCadlagDerivativeRealization).1
          (Sum.inl state)
      · rw [hBalance]
        rw [VectorMeasure.restrict_sub]
        congr 1 <;> simp only [incoming, outgoing,
          VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
        · change (VectorMeasure.restrictGm (Ioo 0 duration))
              (∑ source : {source : State // source ≠ state},
                (limitPath.toDerivativePath.derivative
                  (Sum.inr ⟨(source, state), source.property⟩)).toSignedMeasure) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro source _
          exact (Classical.choose_spec limitPath.hasCadlagDerivativeRealization).1
            (Sum.inr ⟨(source, state), source.property⟩)
        · change (VectorMeasure.restrictGm (Ioo 0 duration))
              (∑ target : {target : State // target ≠ state},
                (limitPath.toDerivativePath.derivative
                  (Sum.inr ⟨(state, target), target.property.symm⟩)).toSignedMeasure) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro target _
          exact (Classical.choose_spec limitPath.hasCadlagDerivativeRealization).1
            (Sum.inr ⟨(state, target), target.property.symm⟩)
      · intro test
        have hLeft := (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).2
          (Sum.inl state) test
        have hIncoming : Tendsto
            (fun sequenceIndex =>
              ∑ source : {source : State // source ≠ state},
                ((paths sequenceIndex).toDerivativePath.derivative
                  (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral
                    test.1)
            atTop
            (nhds (∑ source : {source : State // source ≠ state},
              (limitPath.toDerivativePath.derivative
                (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral
                  test.1)) := by
          apply tendsto_finsetSum
          intro source _
          exact (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).2
            (Sum.inr ⟨(source, state), source.property⟩) test
        have hOutgoing : Tendsto
            (fun sequenceIndex =>
              ∑ target : {target : State // target ≠ state},
                ((paths sequenceIndex).toDerivativePath.derivative
                  (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral
                    test.1)
            atTop
            (nhds (∑ target : {target : State // target ≠ state},
              (limitPath.toDerivativePath.derivative
                (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral
                  test.1)) := by
          apply tendsto_finsetSum
          intro target _
          exact (FiniteIntervalHybridBVPath.tendsto_iff.mp hTendsto).2
            (Sum.inr ⟨(state, target), target.property.symm⟩) test
        have hRight := hIncoming.sub hOutgoing
        have hLimitIdentity := tendsto_nhds_unique hLeft <|
          hRight.congr' <| Filter.Eventually.of_forall fun sequenceIndex =>
            (rengerDirectionalFlowHybridBVDerivativeContinuity_testIntegral
              (hPaths sequenceIndex).derivativeContinuity state test).symm
        rw [show balance.continuousTestIntegral test.1 =
            incoming.continuousTestIntegral test.1 -
              outgoing.continuousTestIntegral test.1 by
          simp [balance, sub_eq_add_neg]]
        rw [show incoming.continuousTestIntegral test.1 =
            ∑ source : {source : State // source ≠ state},
              (limitPath.toDerivativePath.derivative
                (Sum.inr ⟨(source, state), source.property⟩)).continuousTestIntegral
                  test.1 by
          simpa only [incoming] using
            VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
              (fun source : {source : State // source ≠ state} =>
                limitPath.toDerivativePath.derivative
                  (Sum.inr ⟨(source, state), source.property⟩)) test.1]
        rw [show outgoing.continuousTestIntegral test.1 =
            ∑ target : {target : State // target ≠ state},
              (limitPath.toDerivativePath.derivative
                (Sum.inr ⟨(state, target), target.property.symm⟩)).continuousTestIntegral
                  test.1 by
          simpa only [outgoing] using
            VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
              (fun target : {target : State // target ≠ state} =>
                limitPath.toDerivativePath.derivative
                  (Sum.inr ⟨(state, target), target.property.symm⟩)) test.1]
        exact hLimitIdentity
    exact hEquality.symm ▸ hBalance

end

end FiniteMarkovProcesses.InformationTheory
