/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1PathWeightedCoordinateIntegral
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDynamicRate
import FiniteMarkovProcesses.MeasureTheory.Integral.OfRealIntegral
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureWithDensityPairing

/-!
# Continuous dual evaluations for the finite-state hybrid-BV jump rate

This module constructs the finite-state specialization of Renger's dual functional `G`.  Each
ordered channel is tested by a zero-extended continuous function on the open physical interval.
The signed-derivative pairing is native to the hybrid topology, while the Hamiltonian term is a
continuous weighted coordinate integral on the strong-`L1` quotient.

No supremum representation, lower-semicontinuity, or large-deviation bound is asserted here.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators CompactlySupported ENNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The continuous scalar map `z ↦ exp(z) - 1`, which fixes zero and therefore preserves compact
support under left composition. -/
noncomputable def rengerExponentialCompensatorContinuousMap : C(ℝ, ℝ) where
  toFun exponent := Real.exp exponent - 1
  continuous_toFun := Real.continuous_exp.sub continuous_const

/-- Compactly supported Hamiltonian weight `exp(ζ) - 1` associated with one channel test. -/
noncomputable def rengerDirectionalFlowHybridBVHamiltonianWeight
    (test : FiniteOpenIntervalVanishingContinuousTest duration) : C_c(ℝ, ℝ) :=
  test.1.compLeft rengerExponentialCompensatorContinuousMap

/-- The Hamiltonian weight evaluates pointwise to `exp(ζ) - 1`. -/
theorem rengerDirectionalFlowHybridBVHamiltonianWeight_apply
    (test : FiniteOpenIntervalVanishingContinuousTest duration) (time : ℝ) :
    rengerDirectionalFlowHybridBVHamiltonianWeight test time =
      Real.exp (test.1 time) - 1 := by
  exact CompactlySupportedContinuousMap.compLeft_apply
    (by simp [rengerExponentialCompensatorContinuousMap]) test.1 time

/-- On the absolutely continuous domain, the native vague derivative pairing is the ordinary
integral of the test times the Radon--Nikodym derivative density. -/
theorem rengerDirectionalFlowHybridBVDerivativeTestIntegral_eq
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative)
    (coordinate : EmpiricalDensityDirectionalFlowCoordinate State)
    (test : C_c(ℝ, ℝ)) :
    (path.toDerivativePath.derivative coordinate).continuousTestIntegral test =
      ∫ time, test time * path.derivativeDensity coordinate time
        ∂finiteOpenIntervalVolume duration := by
  change
    VagueSignedMeasure.continuousTestIntegral
      (VagueSignedMeasure.ofSignedMeasure
        (path.toDerivativePath.derivative coordinate).toSignedMeasure) test = _
  rw [← path.withDensity_derivativeDensity_eq_derivative
    hAbsolutelyContinuous coordinate]
  exact VagueSignedMeasure.continuousTestIntegral_withDensity
    (finiteOpenIntervalVolume duration) (path.derivativeDensity coordinate)
    (path.measurable_derivativeDensity coordinate)
    (SignedMeasure.integrable_rnDeriv _ _) test

/-- Every selected càdlàg density coordinate is integrable on the physical interval. -/
theorem integrable_rengerDirectionalFlowHybridBVDensityValue
    (path : RengerDirectionalFlowHybridBVPath State duration) (state : State) :
    Integrable (fun time =>
      rengerDirectionalFlowHybridBVDensityValue path time state)
      (finiteOpenIntervalVolume duration) := by
  obtain ⟨hRepresentativeMemLp, _hRepresentativeQuotient⟩ :=
    path.cadlagRepresentative.represents
  have hCoordinateMemLp := hRepresentativeMemLp.continuousLinearMap_comp
    (PiLp.proj (𝕜 := ℝ) (p := 1)
      (fun _ : EmpiricalDensityDirectionalFlowCoordinate State => ℝ) (Sum.inl state))
  rw [← memLp_one_iff_integrable]
  simpa only [rengerDirectionalFlowHybridBVDensityValue, PiLp.proj_apply] using
    hCoordinateMemLp

/-- Every Radon--Nikodym directional-flow derivative is integrable. -/
theorem integrable_rengerDirectionalFlowHybridBVFlowDerivative
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    Integrable (fun time =>
      rengerDirectionalFlowHybridBVFlowDerivative path time transition)
      (finiteOpenIntervalVolume duration) := by
  exact SignedMeasure.integrable_rnDeriv _ _

/-- The quotient-level weighted coordinate integral may be evaluated on the selected càdlàg
representative. -/
theorem rengerDirectionalFlowHybridBVWeightedDensityIntegral_eq
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (test : C_c(ℝ, ℝ)) (state : State) :
    finiteIntervalL1PathWeightedCoordinateIntegral test (Sum.inl state)
        path.toDerivativePath.toL1Path =
      ∫ time, test time *
        rengerDirectionalFlowHybridBVDensityValue path time state
        ∂finiteOpenIntervalVolume duration := by
  rw [finiteIntervalL1PathWeightedCoordinateIntegral_eq_integral]
  obtain ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩ :=
    path.cadlagRepresentative.represents
  have hEventually :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq
      path.toDerivativePath.toL1Path path.cadlagRepresentative.representative
      hRepresentativeMemLp).mp
        ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩
  apply integral_congr_ae
  filter_upwards [hEventually] with time hTime
  simp only [rengerDirectionalFlowHybridBVDensityValue, hTime]

/-- Real one-time dual integrand, summed over every ordered off-diagonal channel. -/
noncomputable def rengerDirectionalFlowHybridBVDualIntegrand
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration)
  (time : ℝ) : ℝ :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ((test transition).1 time *
          rengerDirectionalFlowHybridBVFlowDerivative path time transition -
        (generator.rate transition.1.1 transition.1.2 : ℝ) *
          ((Real.exp ((test transition).1 time) - 1) *
            rengerDirectionalFlowHybridBVDensityValue path time transition.1.1))

/-- The real dual integrand is integrable for every hybrid path. -/
theorem integrable_rengerDirectionalFlowHybridBVDualIntegrand
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Integrable (rengerDirectionalFlowHybridBVDualIntegrand generator test path)
      (finiteOpenIntervalVolume duration) := by
  unfold rengerDirectionalFlowHybridBVDualIntegrand
  apply integrable_finsetSum
  intro transition _hTransition
  apply Integrable.sub
  · exact integrable_compactlySupportedContinuousMap_mul_of_integrable_right
      (test transition).1
      (integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition)
  · apply Integrable.const_mul
    simpa only [rengerDirectionalFlowHybridBVHamiltonianWeight_apply] using
      integrable_compactlySupportedContinuousMap_mul_of_integrable_right
        (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
        (integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1)

/-- `ofReal` is subadditive over an arbitrary finite real sum. -/
theorem ofReal_finset_sum_le_sum_ofReal
    {Index : Type*} (indices : Finset Index) (value : Index → ℝ) :
    ENNReal.ofReal (∑ index ∈ indices, value index) ≤
      ∑ index ∈ indices, ENNReal.ofReal (value index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hNotMem inductionHypothesis =>
      rw [Finset.sum_insert hNotMem, Finset.sum_insert hNotMem]
      exact ENNReal.ofReal_add_le.trans
        (by simpa only [add_comm] using
          add_le_add_left inductionHypothesis (ENNReal.ofReal (value index)))

/-- On the admissible domain, the real dual integrand is pointwise below the extended local rate
almost everywhere, including zero-rate channels. -/
theorem rengerDirectionalFlowHybridBVDualIntegrand_le_localRate_ae
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    {hDuration : 0 < duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ENNReal.ofReal
          (rengerDirectionalFlowHybridBVDualIntegrand generator test path time) ≤
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time) := by
  filter_upwards [hPath.densityNonnegativeAE, hPath.flowDerivativeNonnegativeAE] with
      time hDensityNonnegative hFlowNonnegative
  unfold rengerDirectionalFlowHybridBVDualIntegrand
  unfold rengerDirectionalFlowLocalRateRaw
  calc
    ENNReal.ofReal
        (∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ((test transition).1 time *
              rengerDirectionalFlowHybridBVFlowDerivative path time transition -
            (generator.rate transition.1.1 transition.1.2 : ℝ) *
              ((Real.exp ((test transition).1 time) - 1) *
                rengerDirectionalFlowHybridBVDensityValue
                  path time transition.1.1))) ≤
      ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ENNReal.ofReal
          ((test transition).1 time *
              rengerDirectionalFlowHybridBVFlowDerivative path time transition -
            (generator.rate transition.1.1 transition.1.2 : ℝ) *
              ((Real.exp ((test transition).1 time) - 1) *
                rengerDirectionalFlowHybridBVDensityValue
                  path time transition.1.1)) := by
        simpa only [Finset.sum_const_zero, add_zero] using
          ofReal_finset_sum_le_sum_ofReal Finset.univ (fun transition =>
            (test transition).1 time *
                rengerDirectionalFlowHybridBVFlowDerivative path time transition -
              (generator.rate transition.1.1 transition.1.2 : ℝ) *
                ((Real.exp ((test transition).1 time) - 1) *
                  rengerDirectionalFlowHybridBVDensityValue
                    path time transition.1.1))
    _ ≤ ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2) := by
      apply Finset.sum_le_sum
      intro transition _hTransition
      have hChannel :=
        ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path time transition)
          (rengerDirectionalFlowHybridBVDensityAt path time transition.1.1 *
            generator.rate transition.1.1 transition.1.2)
          ((test transition).1 time)
      simpa only [rengerDirectionalFlowHybridBVFlowDerivativeAt,
        rengerDirectionalFlowHybridBVDensityAt,
        Real.coe_toNNReal _ (hFlowNonnegative transition),
        Real.coe_toNNReal _ (hDensityNonnegative transition.1.1), NNReal.coe_mul,
        mul_comm, mul_left_comm, mul_assoc] using hChannel

/-- Renger's real dual evaluation on the total hybrid-BV carrier.  It is defined before imposing
absolute continuity or the continuity equation: the first term pairs the test with the carried
signed derivative measure, and the second is the source-dependent exponential compensator. -/
noncomputable def rengerDirectionalFlowHybridBVDualEvaluation
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ℝ :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ((path.toDerivativePath.derivative (Sum.inr transition)).continuousTestIntegral
          (test transition).1 -
        (generator.rate transition.1.1 transition.1.2 : ℝ) *
          finiteIntervalL1PathWeightedCoordinateIntegral
            (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
            (Sum.inl transition.1.1) path.toDerivativePath.toL1Path)

/-- On the absolutely continuous domain, the topological dual evaluation is exactly the ordinary
time integral of the real dual integrand. -/
theorem rengerDirectionalFlowHybridBVDualEvaluation_eq_integral
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration)
    (hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative) :
    rengerDirectionalFlowHybridBVDualEvaluation generator test path =
      ∫ time, rengerDirectionalFlowHybridBVDualIntegrand generator test path time
        ∂finiteOpenIntervalVolume duration := by
  unfold rengerDirectionalFlowHybridBVDualEvaluation
  unfold rengerDirectionalFlowHybridBVDualIntegrand
  calc
    _ = ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
        ∫ time,
          ((test transition).1 time *
              rengerDirectionalFlowHybridBVFlowDerivative path time transition -
            (generator.rate transition.1.1 transition.1.2 : ℝ) *
              ((Real.exp ((test transition).1 time) - 1) *
                rengerDirectionalFlowHybridBVDensityValue
                  path time transition.1.1))
          ∂finiteOpenIntervalVolume duration := by
      apply Finset.sum_congr rfl
      intro transition _hTransition
      rw [rengerDirectionalFlowHybridBVDerivativeTestIntegral_eq
          path hAbsolutelyContinuous (Sum.inr transition) (test transition).1,
        rengerDirectionalFlowHybridBVWeightedDensityIntegral_eq
          path (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
            transition.1.1]
      have hFlowTest :=
        integrable_compactlySupportedContinuousMap_mul_of_integrable_right
          (test transition).1
          (integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition)
      have hHamiltonianTest :=
        integrable_compactlySupportedContinuousMap_mul_of_integrable_right
          (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
          (integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1)
      simp only [rengerDirectionalFlowHybridBVFlowDerivative] at hFlowTest ⊢
      simp only [rengerDirectionalFlowHybridBVHamiltonianWeight_apply] at hHamiltonianTest
      simp only [rengerDirectionalFlowHybridBVHamiltonianWeight_apply]
      rw [integral_sub hFlowTest (hHamiltonianTest.const_mul _), integral_const_mul]
    _ = _ := by
      rw [integral_finsetSum Finset.univ]
      intro transition _hTransition
      apply Integrable.sub
      · exact integrable_compactlySupportedContinuousMap_mul_of_integrable_right
          (test transition).1
          (integrable_rengerDirectionalFlowHybridBVFlowDerivative path transition)
      · apply Integrable.const_mul
        simpa only [rengerDirectionalFlowHybridBVHamiltonianWeight_apply] using
          integrable_compactlySupportedContinuousMap_mul_of_integrable_right
            (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
            (integrable_rengerDirectionalFlowHybridBVDensityValue path transition.1.1)

/-- The native strong-`L1` projection is continuous on the hybrid-BV graph. -/
theorem continuous_rengerDirectionalFlowHybridBVToL1Path :
    Continuous fun path : RengerDirectionalFlowHybridBVPath State duration =>
      path.toDerivativePath.toL1Path :=
  FiniteIntervalL1DerivativePath.continuous_toL1Path.comp
    FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous

/-- Every fixed Renger dual test defines a continuous real functional in the exact hybrid
topology. -/
theorem continuous_rengerDirectionalFlowHybridBVDualEvaluation
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    Continuous (rengerDirectionalFlowHybridBVDualEvaluation generator test) := by
  unfold rengerDirectionalFlowHybridBVDualEvaluation
  apply continuous_finsetSum
  intro transition _hTransition
  apply Continuous.sub
  · exact
      (FiniteIntervalL1DerivativePath.continuous_derivativeTestIntegral
        (Sum.inr transition) (test transition)).comp
          FiniteIntervalHybridBVPath.isEmbedding_toDerivativePath.continuous
  · apply continuous_const.mul
    exact
      (continuous_finiteIntervalL1PathWeightedCoordinateIntegral
        (rengerDirectionalFlowHybridBVHamiltonianWeight (test transition))
        (Sum.inl transition.1.1)).comp
          continuous_rengerDirectionalFlowHybridBVToL1Path

/-- One fixed dual evaluation, embedded nonnegatively into extended reals. -/
noncomputable def rengerDirectionalFlowHybridBVExtendedDualEvaluation
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  ENNReal.ofReal (rengerDirectionalFlowHybridBVDualEvaluation generator test path)

/-- Every fixed extended dual evaluation is continuous in the hybrid topology. -/
theorem continuous_rengerDirectionalFlowHybridBVExtendedDualEvaluation
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    Continuous (rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test) :=
  ENNReal.continuous_ofReal.comp
    (continuous_rengerDirectionalFlowHybridBVDualEvaluation generator test)

/-- Every fixed extended dual test lies below the dynamic rate on the physical domain. -/
theorem rengerDirectionalFlowHybridBVExtendedDualEvaluation_le_dynamicRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test path ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
  rw [rengerDirectionalFlowHybridBVExtendedDualEvaluation,
    rengerDirectionalFlowHybridBVDualEvaluation_eq_integral
      generator test path hPath.absolutelyContinuousDerivative,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
      generator hDuration hPath]
  exact
    (_root_.MeasureTheory.ofReal_integral_le_lintegral_ofReal
      (integrable_rengerDirectionalFlowHybridBVDualIntegrand generator test path)).trans
        (lintegral_mono_ae
          (rengerDirectionalFlowHybridBVDualIntegrand_le_localRate_ae
            generator test path hPath))

/-- Supremum of all compactly supported continuous directional-flow dual tests. -/
noncomputable def rengerDirectionalFlowHybridBVDualRate
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  ⨆ test : RengerDirectionalFlowHybridBVDualTest State duration,
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test path

/-- The complete dual supremum lies below the dynamic rate on every admissible path. -/
theorem rengerDirectionalFlowHybridBVDualRate_le_dynamicRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVDualRate generator path ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
  apply iSup_le
  intro test
  exact rengerDirectionalFlowHybridBVExtendedDualEvaluation_le_dynamicRate
    generator hDuration test hPath

/-- The dual rate is lower semicontinuous on the total hybrid-BV carrier. -/
theorem lowerSemicontinuous_rengerDirectionalFlowHybridBVDualRate
    (generator : FiniteStateMarkovGenerator State) :
    LowerSemicontinuous
      (rengerDirectionalFlowHybridBVDualRate (duration := duration) generator) := by
  apply lowerSemicontinuous_iSup
  intro test
  exact Continuous.lowerSemicontinuous
    (continuous_rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test)

/-- Every individual compactly supported dual test lies below the dual rate. -/
theorem rengerDirectionalFlowHybridBVExtendedDualEvaluation_le_dualRate
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test path ≤
      rengerDirectionalFlowHybridBVDualRate generator path :=
  le_iSup (fun candidate : RengerDirectionalFlowHybridBVDualTest State duration =>
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator candidate path) test

end

end FiniteMarkovProcesses.InformationTheory
