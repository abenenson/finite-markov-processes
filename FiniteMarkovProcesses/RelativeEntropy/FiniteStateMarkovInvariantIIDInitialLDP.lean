/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateJumpDirectionalFlowLDPBoundary
import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensityLargeDeviation

/-!
# Invariant-IID initial LDP for finite-state Markov jumps

This module instantiates the generic finite-alphabet empirical-density large-deviation theorem at
the strictly positive stationary law used by Renger's Corollary 4.16.  It proves that Renger's
coordinatewise extended Poisson initial cost is exactly the generic relative entropy, supplies
the literal closed/open bounds and good-rate theorem, and packages the complete initial-law
contract including lower-boundary continuity.

No dynamic path-space large-deviation bound is asserted here.

## Main declarations

- `FiniteStateMarkovStationaryDistribution.probabilityDensity`.
- `rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy`.
- `rengerInvariantIIDInitialLargeDeviationData`.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State]

namespace FiniteStateMarkovStationaryDistribution

/-- Finite-simplex density represented by a strictly positive stationary distribution. -/
def probabilityDensity
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    FiniteStateProbabilityDensity State where
  weight := stationary.weight
  sum_weight := stationary.sum_weight

/-- The stationary finite-simplex density recovers every stationary coordinate. -/
@[simp]
theorem probabilityDensity_weight
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) (state : State) :
    (probabilityDensity stationary).weight state = stationary.weight state :=
  rfl

/-- Strict positivity of the stationary distribution is exactly simplex interiority. -/
theorem probabilityDensity_isInterior
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    (probabilityDensity stationary).IsInterior :=
  stationary.weight_pos

variable [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State]

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The generic finite-simplex PMF adapter is literally the existing stationary PMF. -/
theorem probabilityDensity_probabilityMassFunction_eq_pmf
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    (probabilityDensity stationary).probabilityMassFunction = stationary.pmf := by
  apply PMF.ext
  intro state
  simp

end FiniteStateMarkovStationaryDistribution

/-- Renger's invariant initial cost is exactly finite-state relative entropy against the
stationary density, including simplex boundary points. -/
theorem rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (density : FiniteStateProbabilityDensity State) :
    rengerInvariantInitialCost stationary density =
      finiteStateProbabilityDensityRelativeEntropy
        (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary) density := by
  rw [rengerInvariantInitialCost, finiteStateProbabilityDensityRelativeEntropy,
    finiteStateProbabilityDensityRelativeEntropyReal,
    ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro state _hState
    exact rengerExtendedPoissonRateCost_of_expected_pos
      (density.weight state) (stationary.weight_pos state)
  · intro state _hState
    exact poissonRateDiscrimination_nonneg (by positivity)
      (by exact_mod_cast stationary.weight_pos state)

variable [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Renger's invariant-IID empirical initial densities satisfy the literal closed-set upper
bound at exact particle-number speed. -/
theorem rengerInvariantIIDInitialLaw_closedUpperBound
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun successorIndex =>
          FiniteMarkovProcesses.Probability.finiteIIDEmpiricalProbabilityDensityLaw successorIndex
            stationary.pmf)
        (fun _ => id) FiniteMarkovProcesses.Probability.finiteIIDPositiveSampleSpeed)
      (rengerInvariantInitialCost stationary) := by
  have hRate : rengerInvariantInitialCost stationary =
      finiteStateProbabilityDensityRelativeEntropy
        (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary) := by
    funext density
    exact rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy
      stationary density
  rw [hRate]
  simpa only [
    FiniteStateMarkovStationaryDistribution.probabilityDensity_probabilityMassFunction_eq_pmf]
    using
    FiniteMarkovProcesses.Probability.finiteIIDEmpiricalProbabilityDensityLaw_closedUpperBound
      (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary)
      (FiniteStateMarkovStationaryDistribution.probabilityDensity_isInterior stationary)

/-- Renger's invariant-IID empirical initial densities satisfy the literal open-set lower bound
at exact particle-number speed. -/
theorem rengerInvariantIIDInitialLaw_openLowerBound
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    HasLargeDeviationLowerBound
      (scaledEventLogProbability
        (fun successorIndex =>
          FiniteMarkovProcesses.Probability.finiteIIDEmpiricalProbabilityDensityLaw successorIndex
            stationary.pmf)
        (fun _ => id) FiniteMarkovProcesses.Probability.finiteIIDPositiveSampleSpeed)
      (rengerInvariantInitialCost stationary) := by
  have hRate : rengerInvariantInitialCost stationary =
      finiteStateProbabilityDensityRelativeEntropy
        (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary) := by
    funext density
    exact rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy
      stationary density
  rw [hRate]
  simpa only [
    FiniteStateMarkovStationaryDistribution.probabilityDensity_probabilityMassFunction_eq_pmf]
    using
    FiniteMarkovProcesses.Probability.finiteIIDEmpiricalProbabilityDensityLaw_openLowerBound
      (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary)
      (FiniteStateMarkovStationaryDistribution.probabilityDensity_isInterior stationary)

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The invariant initial cost is a good rate function on the closed finite simplex. -/
theorem rengerInvariantInitialCost_isGoodRateFunction
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    IsGoodRateFunction (rengerInvariantInitialCost stationary) := by
  have hRate : rengerInvariantInitialCost stationary =
      finiteStateProbabilityDensityRelativeEntropy
        (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary) := by
    funext density
    exact rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy
      stationary density
  rw [hRate]
  exact
FiniteMarkovProcesses.Probability.finiteStateProbabilityDensityRelativeEntropy_isGoodRateFunction
      (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary)
      (FiniteStateMarkovStationaryDistribution.probabilityDensity_isInterior stationary)

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The invariant initial cost is continuous when an interior sequence approaches any lower
simplex boundary point; in fact the proof uses continuity on the entire closed simplex. -/
theorem rengerInvariantInitialCost_leftContinuousAtLowerBoundary
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    FiniteStateProbabilityDensity.InitialRateIsLeftContinuousAtLowerBoundary
      (rengerInvariantInitialCost stationary) := by
  intro boundaryDensity _hBoundary sequence _hSequenceInterior hSequence
  have hRate : rengerInvariantInitialCost stationary =
      finiteStateProbabilityDensityRelativeEntropy
        (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary) := by
    funext density
    exact rengerInvariantInitialCost_eq_finiteStateProbabilityDensityRelativeEntropy
      stationary density
  rw [hRate]
  exact
    (continuous_finiteStateProbabilityDensityRelativeEntropy
      (FiniteStateMarkovStationaryDistribution.probabilityDensity stationary)
      (FiniteStateMarkovStationaryDistribution.probabilityDensity_isInterior stationary)).tendsto
        boundaryDensity |>.comp
      (FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise.mpr hSequence)

/-- Complete theorem-specific initial-law contract for the invariant-IID regime.  The laws are
the exact finite empirical-density pushforwards, and all asymptotic fields are proved rather than
supplied by a caller. -/
def rengerInvariantIIDInitialLargeDeviationData
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) :
    RengerTheoremFourTwoInitialData State where
  initialLaw successorIndex :=
    FiniteMarkovProcesses.Probability.finiteIIDEmpiricalProbabilityDensityLaw successorIndex
      stationary.pmf
  initialLaw_probability _ := inferInstance
  initialEmpiricalTypeLaw successorIndex :=
    FiniteMarkovProcesses.Probability.finiteIIDPositiveEmpiricalTypeLaw
      successorIndex stationary.pmf
  initialEmpiricalTypeLaw_probability _ := inferInstance
  initialLaw_eq_map_probabilityDensity successorIndex :=
    (map_probabilityDensity_finiteIIDPositiveEmpiricalTypeLaw
      successorIndex stationary.pmf).symm
  initialRate := rengerInvariantInitialCost stationary
  topology_generates_measurableSpace := rfl
  initialRate_good := rengerInvariantInitialCost_isGoodRateFunction stationary
  initialUpperBound := rengerInvariantIIDInitialLaw_closedUpperBound stationary
  initialLowerBound := rengerInvariantIIDInitialLaw_openLowerBound stationary
  initialRate_leftContinuousAtLowerBoundary :=
    rengerInvariantInitialCost_leftContinuousAtLowerBoundary stationary

end

end FiniteMarkovProcesses.InformationTheory
