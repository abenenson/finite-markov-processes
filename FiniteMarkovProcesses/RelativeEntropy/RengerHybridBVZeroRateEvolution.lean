/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVForwardUniqueness
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovMeanHybridBVRepresentationPath
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVReferenceEvolutionPath

/-!
# Complete-rate zero paths are actual finite-state mean evolutions

Every admissible generator-flow path equals the existing generated mean path from its recovered
initial density. Consequently the complete-rate zero set is precisely the image of the supplied
initial zero set under that mean evolution. Initial-trace recovery makes the map injective.

## Main results

- `rengerDirectionalFlowHybridBVPath_eq_referenceEvolution_of_generatorFlow`.
- `rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_exists_initialDensity`.
- `finiteStateMarkovMeanHybridBVPath_initialDensity_injective`.

No uniqueness or existence of an initial zero is assumed silently. Equality is in the full
hybrid carrier, with both derivative and boundary data retained.

## References

The complete density/flux rate is the finite-state action of M. Renger (2018),
https://doi.org/10.1007/s10955-018-2083-0. Its entropy equality case and finite-state
forward uniqueness are classical. This module assembles them with the existing Markov mean
path and hybrid reconstruction: the arbitrary supplied initial cost determines the zero family.
The zero-set theorem is deterministic; it does not itself assert concentration of random paths.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State] {duration : ℝ}

/-- The actual arbitrary-initial-PMF Markov mean path has exactly its occupied-source
generator flow, with no stationarity or positive-rate requirement. -/
theorem finiteStateMarkovMeanHybridBVRepresentationPath_hasGeneratorFlow
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    RengerDirectionalFlowHybridBVHasGeneratorFlow generator
      (finiteStateMarkovMeanHybridBVRepresentationPath initial generator hDuration).1 := by
  apply (rengerDirectionalFlowHybridBVHasGeneratorFlow_iff_raw generator hDuration
    (finiteStateMarkovMeanHybridBVRepresentationPath initial generator hDuration).2).mpr
  rw [ae_all_iff]
  intro transition
  filter_upwards
    [ae_finiteStateTimeDependentMarkovMeanHybridBVPath_derivativeDensity_eq
        initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ (Sum.inr transition),
      ae_restrict_mem measurableSet_Ioo] with time hDerivative hTime
  change (finiteStateTimeDependentMarkovMeanHybridBVPath initial
      generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩).derivativeDensity
      (Sum.inr transition) time = _
  rw [hDerivative]
  unfold rengerDirectionalFlowHybridBVDensityValue
  rw (transparency := .default)
    [finiteStateMarkovMeanHybridBVRepresentationPath_toHybridBVPath,
    finiteStateTimeDependentMarkovMeanHybridBVPath_cadlagRepresentative_eq
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      ⟨hTime.1.le, hTime.2⟩,
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
      initial generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩
      hTime.1.le hTime.2.le transition.val.1]
  rfl

/-- An admissible generator-flow path is literally the existing reference mean evolution
from its own recovered initial PMF. No new witness or initial law is chosen. -/
theorem rengerDirectionalFlowHybridBVPath_eq_referenceEvolution_of_generatorFlow
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (hFlow : RengerDirectionalFlowHybridBVHasGeneratorFlow generator path.1) :
    path.1 = (rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath
      generator path).1 := by
  apply rengerDirectionalFlowHybridBVPath_eq_of_generatorFlow_initialDensity
    generator hDuration path
    (rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath generator path)
    hFlow
    (finiteStateMarkovMeanHybridBVRepresentationPath_hasGeneratorFlow
      (rengerDirectionalFlowHybridBVTargetInitialPMF path) generator hDuration)
  intro state
  exact (rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialDensity
    generator path state).symm

/-- Recovering the initial simplex point of the actual mean path returns the supplied density
exactly, rather than a default or an existentially selected initial law. -/
theorem finiteStateMarkovMeanHybridBVPath_initialProbabilityDensityOption
    (initial : FiniteStateProbabilityDensity State)
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration) :
    rengerDirectionalFlowHybridBVInitialProbabilityDensityOption
        (finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩) = some initial := by
  change rengerDirectionalFlowHybridBVInitialProbabilityDensityOption
    (finiteStateMarkovMeanHybridBVRepresentationPath
      initial.probabilityMassFunction generator hDuration).1 = some initial
  rw [rengerDirectionalFlowHybridBVInitialProbabilityDensityOption_eq_some_of_admissible
    hDuration
      (finiteStateMarkovMeanHybridBVRepresentationPath
        initial.probabilityMassFunction generator hDuration).2]
  congr 1
  apply FiniteStateProbabilityDensity.ext
  intro state
  change rengerDirectionalFlowHybridBVInitialDensity
    (finiteStateMarkovMeanHybridBVRepresentationPath
      initial.probabilityMassFunction generator hDuration).1 state = initial.weight state
  rw [finiteStateMarkovMeanHybridBVRepresentationPath_initialDensity]
  simp

/-- On an actual generator mean path, the complete rate is exactly the independently supplied
initial cost; the entire dynamic sector vanishes. -/
theorem finiteStateMarkovMeanHybridBVPath_completeRate_eq_initialRate
    (initial : FiniteStateProbabilityDensity State)
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate
        (finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩) = initialRate initial := by
  have hPath := (finiteStateMarkovMeanHybridBVRepresentationPath
    initial.probabilityMassFunction generator hDuration).2
  have hDynamic := (rengerDirectionalFlowHybridBVDynamicRate_eq_zero_iff
    generator hDuration _).mpr ⟨hPath,
      finiteStateMarkovMeanHybridBVRepresentationPath_hasGeneratorFlow
        initial.probabilityMassFunction generator hDuration⟩
  change rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate
    (finiteStateMarkovMeanHybridBVRepresentationPath
      initial.probabilityMassFunction generator hDuration).1 = initialRate initial
  rw [rengerDirectionalFlowHybridBVCompleteRate_eq_initialCost_add_dynamicRate_of_admissible
    generator hDuration initialRate hPath, hDynamic, add_zero]
  unfold rengerDirectionalFlowHybridBVLiftedInitialCost
  rw (transparency := .default)
    [finiteStateMarkovMeanHybridBVRepresentationPath_toHybridBVPath,
    finiteStateMarkovMeanHybridBVPath_initialProbabilityDensityOption initial generator hDuration]
  rfl

/-- The complete-rate zero set on the entire hybrid carrier is exactly the image of the supplied
initial zero set under actual constant-generator mean evolution. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_exists_initialDensity
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = 0 ↔
      ∃ initial : FiniteStateProbabilityDensity State, initialRate initial = 0 ∧
        path = finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
          generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ := by
  constructor
  · intro hZero
    obtain ⟨hPath, hInitial, hFlow⟩ :=
      (rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff
        generator hDuration initialRate path).mp hZero
    let admitted : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
      ⟨path, hPath⟩
    refine ⟨rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity admitted, ?_, ?_⟩
    · rw [rengerDirectionalFlowHybridBVLiftedInitialCost_eq_of_admissible
        initialRate hDuration hPath] at hInitial
      exact hInitial
    · exact rengerDirectionalFlowHybridBVPath_eq_referenceEvolution_of_generatorFlow
        generator hDuration admitted hFlow
  · rintro ⟨initial, hInitial, rfl⟩
    rw [finiteStateMarkovMeanHybridBVPath_completeRate_eq_initialRate, hInitial]

/-- Initial-trace recovery makes the mean-evolution map injective on finite probability densities.
Distinct initial zeros therefore remain distinct full-carrier zero-rate paths. -/
theorem finiteStateMarkovMeanHybridBVPath_initialDensity_injective
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration) :
    Function.Injective (fun initial : FiniteStateProbabilityDensity State ↦
      finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩) := by
  intro first second hPaths
  have hInitial := congrArg rengerDirectionalFlowHybridBVInitialProbabilityDensityOption hPaths
  rw [finiteStateMarkovMeanHybridBVPath_initialProbabilityDensityOption first generator hDuration,
    finiteStateMarkovMeanHybridBVPath_initialProbabilityDensityOption second generator hDuration]
    at hInitial
  exact Option.some.inj hInitial

/-- An independently proved singleton initial zero set gives exactly one full-carrier zero path. -/
theorem rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_eq_meanPath
    (generator : FiniteStateMarkovGenerator State) (hDuration : 0 < duration)
    (initialRate : FiniteStateProbabilityDensity State → ENNReal)
    (initial : FiniteStateProbabilityDensity State)
    (hInitial : ∀ candidate, initialRate candidate = 0 ↔ candidate = initial)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    rengerDirectionalFlowHybridBVCompleteRate generator hDuration initialRate path = 0 ↔
      path = finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
        generator.toTimeDependentMarkovRate ⟨duration, hDuration.le⟩ := by
  rw [rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_exists_initialDensity]
  simp only [hInitial, exists_eq_left]

/-- Two states already refute unconditional global zero-path uniqueness: the zero generator
and identically zero initial cost admit two distinct point-mass mean paths. -/
theorem exists_distinct_zeroRatePaths_twoState_zeroGenerator :
    ∃ generator : FiniteStateMarkovGenerator (Fin 2),
      (∀ source target, generator.rate source target = 0) ∧
      ∃ first second : RengerDirectionalFlowHybridBVPath (Fin 2) 1,
        first ≠ second ∧
        rengerDirectionalFlowHybridBVCompleteRate generator (by norm_num)
          (fun _initial ↦ 0) first = 0 ∧
        rengerDirectionalFlowHybridBVCompleteRate generator (by norm_num)
          (fun _initial ↦ 0) second = 0 := by
  let generator : FiniteStateMarkovGenerator (Fin 2) :=
    { rate := fun _source _target ↦ 0
      rate_self := fun _state ↦ rfl }
  let firstInitial : FiniteStateProbabilityDensity (Fin 2) :=
    { weight := fun state ↦ if state = 0 then 1 else 0
      sum_weight := by simp }
  let secondInitial : FiniteStateProbabilityDensity (Fin 2) :=
    { weight := fun state ↦ if state = 1 then 1 else 0
      sum_weight := by simp }
  have hDistinct : firstInitial ≠ secondInitial := by
    intro hEqual
    have hZero := congrArg (fun density : FiniteStateProbabilityDensity (Fin 2) ↦
      density.weight 0) hEqual
    simp [firstInitial, secondInitial] at hZero
  let mean := fun initial : FiniteStateProbabilityDensity (Fin 2) ↦
    finiteStateTimeDependentMarkovMeanHybridBVPath initial.probabilityMassFunction
      generator.toTimeDependentMarkovRate (1 : NNReal)
  refine ⟨generator, fun _source _target ↦ rfl,
    mean firstInitial, mean secondInitial, ?_, ?_, ?_⟩
  · intro hPaths
    exact hDistinct (finiteStateMarkovMeanHybridBVPath_initialDensity_injective
      generator (by norm_num : (0 : ℝ) < 1) hPaths)
  · exact finiteStateMarkovMeanHybridBVPath_completeRate_eq_initialRate firstInitial
      generator (by norm_num : (0 : ℝ) < 1) (fun _initial ↦ 0)
  · exact finiteStateMarkovMeanHybridBVPath_completeRate_eq_initialRate secondInitial
      generator (by norm_num : (0 : ℝ) < 1) (fun _initial ↦ 0)

end

end FiniteMarkovProcesses.InformationTheory
