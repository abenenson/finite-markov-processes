/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpConservationInitialDensity
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpHybridBVCompactContainment

/-!
# Compact containment for random empirical-type hybrid paths

This module transports the deterministic configuration-uniform jump-count Chernoff estimate
through exact disintegration over a random empirical initial type.  The result controls the path
tail of the exact probability-density/hybrid-path joint law without restricting its density
coordinate.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open _root_.MeasureTheory
open Set
open scoped ENNReal NNReal Topology

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Uniform compact-containment tail for the mixed density/path joint law.  The density coordinate
is unrestricted; the path tail inherits the deterministic configuration-uniform Chernoff bound
after exact disintegration over the random empirical type. -/
theorem finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw_pathTail_le
    (successorIndex : ℕ)
    (initialEmpiricalTypeLaw :
      Measure (FiniteIIDPositiveEmpiricalType State successorIndex))
    [IsProbabilityMeasure initialEmpiricalTypeLaw]
    (generator : FiniteStateMarkovGenerator State) (duration : NNReal)
    (hDuration : 0 < duration) {exponent : ℝ} (hExponent : 0 < exponent)
    (countCutoff : ℝ) :
    finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
        initialEmpiricalTypeLaw generator duration hDuration.le
        (univ ×ˢ
          (finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
            (State := State) duration countCutoff)ᶜ) ≤
      ENNReal.ofReal
        (Real.exp
          (((successorIndex + 1 : ℕ) : ℝ) *
              (((generator.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp exponent - 1)) -
            (((successorIndex + 1 : ℕ) : ℝ) * countCutoff) * exponent)) := by
  let pathTail :=
    (finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) (duration : ℝ) countCutoff)ᶜ
  have hPathTailMeasurable : MeasurableSet pathTail :=
    (isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff
        (by exact_mod_cast hDuration)).isClosed.measurableSet.compl
  let jointLaw := finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw successorIndex
    initialEmpiricalTypeLaw generator duration hDuration.le
  let tailBound : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp
      (((successorIndex + 1 : ℕ) : ℝ) *
          (((generator.uniformizationRate * duration : NNReal) : ℝ) *
            (Real.exp exponent - 1)) -
        (((successorIndex + 1 : ℕ) : ℝ) * countCutoff) * exponent))
  have hConditional : ∀ empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex,
      finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw empiricalType generator duration
          hDuration.le pathTail ≤ tailBound := by
    intro empiricalType
    unfold finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw
    exact finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_compl_compactContainer_le
      successorIndex empiricalType.representative generator duration hDuration hExponent
        countCutoff
  calc
    jointLaw (univ ×ˢ pathTail) = jointLaw (Prod.snd ⁻¹' pathTail) := by
      congr 1
      ext densityPath
      simp
    _ = jointLaw.snd pathTail :=
      (Measure.snd_apply hPathTailMeasurable).symm
    _ = finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw successorIndex
          initialEmpiricalTypeLaw generator duration hDuration.le pathTail := by
      rw (transparency := .default)
        [snd_finiteStateMarkovJumpRandomEmpiricalTypeDensityHybridBVJointLaw]
    _ = ∫⁻ empiricalType,
          finiteStateMarkovJumpEmpiricalTypeHybridBVObservationLaw empiricalType generator duration
            hDuration.le pathTail ∂initialEmpiricalTypeLaw :=
      finiteStateMarkovJumpRandomEmpiricalTypeHybridBVObservationLaw_apply successorIndex
        initialEmpiricalTypeLaw generator duration hDuration.le hPathTailMeasurable
    _ ≤ ∫⁻ _empiricalType, tailBound ∂initialEmpiricalTypeLaw :=
      lintegral_mono hConditional
    _ = tailBound := by simp

end

end FiniteMarkovProcesses.Probability
