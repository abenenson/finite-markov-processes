/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.PathLargeDeviations
public import FiniteMarkovProcesses.EffectiveEvolution
public import FiniteMarkovProcessesExamples.CTMC
public import FiniteMarkovProcessesExamples.Sanov

/-!
# Checking the public path APIs

These examples use the existing constructors and equality classification without supplying
replacement probability laws, LDP bounds, or uniqueness fields. `initialData` below contains the
exact deterministic empirical convergence and positive limiting-density premises of Theorem 4.1.
The concrete fair flip example below constructs that initial data from rounded empirical types
and projects both LDP bounds without an unproved initial-law or convergence premise.
-/

@[expose] public section

open FiniteMarkovProcesses.InformationTheory FiniteMarkovProcesses.Probability
open scoped ENNReal

noncomputable section

variable {State : Type} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
  {duration : ℝ}

example (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    Nonempty (DensityFluxLargeDeviationRepresentation
      (FiniteStateMarkovJumpPositiveReplicaFamily State)
      (RengerDirectionalFlowHybridBVPath State duration)
      ℝ (State → NNReal)
      (FiniteStateOrderedOffDiagonalTransition State → NNReal)
      Renger2018DirectionalFlowProvenance) :=
  ⟨rengerTheoremFourOneHybridBVLargeDeviationRepresentation generator hDuration initialData⟩

-- The named constructor fixes the actual deterministic source, beyond inhabiting an interface.
example (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialData : RengerTheoremFourOneInitialData State) :
    (rengerTheoremFourOneHybridBVLargeDeviationRepresentation
      generator hDuration initialData).microscopicLaw = fun index =>
        finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw
          index (initialData.initialState index) generator duration hDuration.le := rfl

example (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = 0 ↔
      ∃ initial : FiniteStateProbabilityDensity State, initialRate initial = 0 ∧
        path = finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ :=
  rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_exists_initialDensity
    generator hDuration initialRate path

#check rengerTheoremFourTwoHybridBVLargeDeviationRepresentation
#check rengerCorollaryFourSixteenHybridBVLargeDeviationRepresentation
#check measure_iid_totalHybridBVObservation_deviation_le_exponential
#check exists_distinct_zeroRatePaths_twoState_zeroGenerator

end

namespace FiniteMarkovProcessesExamples.PathLargeDeviations

noncomputable section

/-- Deterministic binary configurations with exact rounded counts converging to the fair law.
All fields of Theorem 4.1's initial-data contract are discharged by the rounding construction. -/
def fairInitialData : RengerTheoremFourOneInitialData Bool where
  initialState := finiteStateProbabilityDensityRoundedInitialConfiguration Sanov.fairBinary
  empiricalInitialDensity := finiteStateRoundedEmpiricalProbabilityDensity Sanov.fairBinary
  empiricalInitialDensity_eq index state := by
    rw [← finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration Sanov.fairBinary index]
    rfl
  limitingDensity := Sanov.fairBinary
  limitingDensity_interior := Sanov.fairBinary_isInterior
  empiricalInitialDensity_tendsto :=
    FiniteStateProbabilityDensity.tendsto_iff_tendstoCoordinatewise.mp
      (finiteStateProbabilityDensityRoundedPositiveEmpiricalType_probabilityDensity_tendsto
        Sanov.fairBinary)

/-- The actual unit-duration, unit-rate two-state process satisfies the full path LDP from
deterministically rounded fair initial configurations, at particle speed `n + 1`. -/
def fairFlipRepresentation :
    DensityFluxLargeDeviationRepresentation
      (FiniteStateMarkovJumpPositiveReplicaFamily Bool)
      (RengerDirectionalFlowHybridBVPath Bool 1) ℝ (Bool → NNReal)
      (FiniteStateOrderedOffDiagonalTransition Bool → NNReal)
      Renger2018DirectionalFlowProvenance :=
  rengerTheoremFourOneHybridBVLargeDeviationRepresentation
    CTMC.flipGenerator (by norm_num) fairInitialData

/-- The concrete representation retains the original deterministic positive-replica source. -/
theorem fairFlip_microscopicLaw (index : ℕ) :
    fairFlipRepresentation.microscopicLaw index =
      finiteStateMarkovJumpDeterministicInitialPositiveReplicaFamilyLaw index
        (finiteStateProbabilityDensityRoundedInitialConfiguration Sanov.fairBinary index)
        CTMC.flipGenerator 1 (by norm_num) := rfl

/-- Closed hybrid-BV events satisfy the concrete flip process's complete-rate upper bound. -/
theorem fairFlip_closedUpperBound :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability fairFlipRepresentation.microscopicLaw
        fairFlipRepresentation.observation fairFlipRepresentation.speed)
      fairFlipRepresentation.rateData.pathRate :=
  fairFlipRepresentation.upperBound

/-- Open hybrid-BV events satisfy the same concrete process's complete-rate lower bound. -/
theorem fairFlip_openLowerBound :
    HasLargeDeviationLowerBound
      (scaledEventLogProbability fairFlipRepresentation.microscopicLaw
        fairFlipRepresentation.observation fairFlipRepresentation.speed)
      fairFlipRepresentation.rateData.pathRate :=
  fairFlipRepresentation.lowerBound

end

end FiniteMarkovProcessesExamples.PathLargeDeviations
