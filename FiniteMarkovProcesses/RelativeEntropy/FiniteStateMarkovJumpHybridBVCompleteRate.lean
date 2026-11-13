/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVDynamicRate

/-!
# Complete theorem-specific rates on the hybrid-BV jump carrier

The dynamic density--directional-flow action is only one sector of Renger's finite-horizon rate.
This module recovers the separately carried initial trace as a finite probability density and
lifts an independently specified initial rate onto the complete hybrid path.  It then instantiates
that construction for the three distinct initial regimes of Renger Theorems 4.1, 4.2, and
Corollary 4.16.

These declarations construct the complete rate functions.  They do not prove the corresponding
initial-law large-deviation bounds, hybrid compactness, lower semicontinuity, or path LDP.

## Main declarations

- `rengerDirectionalFlowHybridBVInitialProbabilityDensityOption`: total recovery of the initial
  simplex point, returning `none` off normalization.
- `rengerDirectionalFlowHybridBVLiftedInitialCost`: a supplied simplex rate lifted with infinite
  cost when no initial simplex point is recovered.
- `rengerDirectionalFlowHybridBVCompleteRate`: the initial plus dynamic complete path rate.
- `rengerTheoremFourOneHybridBVCompleteRate`, `rengerTheoremFourTwoHybridBVCompleteRate`, and
  `rengerCorollaryFourSixteenHybridBVCompleteRate`: the three theorem-specific rates.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Recover the separately carried initial trace as a finite probability density when its
nonnegative coordinates have total mass one. -/
noncomputable def rengerDirectionalFlowHybridBVInitialProbabilityDensityOption
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    Option (FiniteStateProbabilityDensity State) := by
  classical
  exact if hNormalized : ∑ state, rengerDirectionalFlowHybridBVInitialDensity path state = 1 then
    some ⟨rengerDirectionalFlowHybridBVInitialDensity path, hNormalized⟩
  else none

/-- Every finite-rate admissible path recovers its exact initial simplex point. -/
theorem rengerDirectionalFlowHybridBVInitialProbabilityDensityOption_eq_some_of_admissible
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVInitialProbabilityDensityOption path =
      some
        { weight := rengerDirectionalFlowHybridBVInitialDensity path
          sum_weight := by
            apply NNReal.eq
            simp only [NNReal.coe_sum, NNReal.coe_one,
              rengerDirectionalFlowHybridBVInitialDensity]
            simp_rw [Real.coe_toNNReal _ (hPath.initialDensityNonnegative _)]
            exact hPath.initialDensityNormalized } := by
  have hNormalized :
      ∑ state, rengerDirectionalFlowHybridBVInitialDensity path state = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_one,
      rengerDirectionalFlowHybridBVInitialDensity]
    simp_rw [Real.coe_toNNReal _ (hPath.initialDensityNonnegative _)]
    exact hPath.initialDensityNormalized
  simp only [rengerDirectionalFlowHybridBVInitialProbabilityDensityOption,
    dite_eq_left hNormalized]

/-- Lift an initial simplex rate to the hybrid carrier.  Failure to recover a normalized initial
density receives infinite cost rather than a fabricated default law. -/
noncomputable def rengerDirectionalFlowHybridBVLiftedInitialCost
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  (rengerDirectionalFlowHybridBVInitialProbabilityDensityOption path).elim ∞ initialRate

/-- On every admissible path, the lifted cost is exactly the supplied cost of the recovered
initial simplex point. -/
theorem rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (hDuration : 0 < duration)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path =
      initialRate
        { weight := rengerDirectionalFlowHybridBVInitialDensity path
          sum_weight := by
            apply NNReal.eq
            simp only [NNReal.coe_sum, NNReal.coe_one,
              rengerDirectionalFlowHybridBVInitialDensity]
            simp_rw [Real.coe_toNNReal _ (hPath.initialDensityNonnegative _)]
            exact hPath.initialDensityNormalized } := by
  unfold rengerDirectionalFlowHybridBVLiftedInitialCost
  rw [rengerDirectionalFlowHybridBVInitialProbabilityDensityOption_eq_some_of_admissible
    hDuration hPath]
  rfl

/-- Complete hybrid path-rate data obtained by replacing the dynamic-only zero initial sector by
one independently supplied initial simplex rate. -/
noncomputable def rengerDirectionalFlowHybridBVCompleteRateData
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal) :
    DensityFluxPathRateData
      (RengerDirectionalFlowHybridBVPath State duration) ℝ
      (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal) where
  densityAt := rengerDirectionalFlowHybridBVDensityAt
  fluxAt := rengerDirectionalFlowHybridBVFlowDerivativeAt
  terminalDensity := fun path => rengerDirectionalFlowHybridBVTerminalDensity path hDuration
  timeMeasure := finiteOpenIntervalVolume duration
  localAction := rengerDirectionalFlowLocalRateRaw generator
  localAction_aemeasurable := aemeasurable_rengerDirectionalFlowHybridBVLocalRate generator
  initialCost := rengerDirectionalFlowHybridBVLiftedInitialCost initialRate
  boundaryCost := fun _path => 0
  continuityAdmissible := fun path => RengerDirectionalFlowHybridBVAdmissible path hDuration

/-- Complete theorem-specific path rate: independently supplied initial cost plus the exact dynamic
density--directional-flow action on the admissible domain, and infinity off it. -/
noncomputable def rengerDirectionalFlowHybridBVCompleteRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) : ENNReal :=
  (rengerDirectionalFlowHybridBVCompleteRateData generator hDuration initialRate).pathRate path

/-- On the admissible domain, the complete rate exposes the initial and dynamic sectors exactly. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path =
      rengerDirectionalFlowHybridBVLiftedInitialCost initialRate path +
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
  rw [rengerDirectionalFlowHybridBVCompleteRate,
    DensityFluxPathRateData.pathRate_eq_of_continuityAdmissible _ hPath,
    rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible generator hDuration hPath]
  simp [rengerDirectionalFlowHybridBVCompleteRateData]

/-- Off the finite-rate physical domain, every complete theorem-specific rate is infinite. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_top_of_not_admissible
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    {path : RengerDirectionalFlowHybridBVPath State duration}
    (hPath : ¬RengerDirectionalFlowHybridBVAdmissible path hDuration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = ∞ :=
  DensityFluxPathRateData.pathRate_eq_top_of_not_continuityAdmissible
    (rengerDirectionalFlowHybridBVCompleteRateData generator hDuration initialRate) hPath

/-- Theorem 4.1's complete hybrid rate, with the deterministic limiting-density indicator as its
initial sector. -/
noncomputable def rengerTheoremFourOneHybridBVCompleteRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    RengerDirectionalFlowHybridBVPath State duration → ENNReal :=
  rengerDirectionalFlowHybridBVCompleteRate generator hDuration
    (rengerTheoremFourOneInitialRate initialData)

/-- Theorem 4.2's complete hybrid rate, retaining the independently proved good initial rate and
its lower-boundary left-continuity contract. -/
noncomputable def rengerTheoremFourTwoHybridBVCompleteRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerTheoremFourTwoInitialData State) :
    RengerDirectionalFlowHybridBVPath State duration → ENNReal :=
  rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialData.initialRate

/-- Corollary 4.16's complete hybrid rate, with invariant-law relative information as its initial
sector.  Uniqueness remains in the corollary's source-data contract rather than this scalar. -/
noncomputable def rengerCorollaryFourSixteenHybridBVCompleteRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (initialData : RengerCorollaryFourSixteenInitialData generator) :
    RengerDirectionalFlowHybridBVPath State duration → ENNReal :=
  rengerDirectionalFlowHybridBVCompleteRate generator hDuration
    (rengerInvariantInitialCost initialData.stationary)

end

end FiniteMarkovProcesses.InformationTheory
