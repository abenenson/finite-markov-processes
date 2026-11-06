/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.PathLargeDeviations
import FiniteMarkovProcesses.EffectiveEvolution

/-!
# Checking the public path APIs

These examples use the existing constructors and equality classification without supplying
replacement probability laws, LDP bounds, or uniqueness fields. `initialData` below contains the
exact deterministic empirical convergence and positive limiting-density premises of Theorem 4.1.
-/

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
