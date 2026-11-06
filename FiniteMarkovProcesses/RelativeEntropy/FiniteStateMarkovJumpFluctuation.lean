/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpRadonNikodym

/-!
# Finite-state Markov jump fluctuation identities

Under common support, the candidate law is an exponential tilt of its reference by the complete
physical jump action. When both density measures are normalized, this gives the integral
fluctuation theorem. With action integrability, the candidate expectation is the finite
Kullback--Leibler divergence.

## Main results

- `finiteStateMarkovJumpDensityMeasure_withDensity_exp_logAction`: exponential action tilt.
- `lintegral_exp_neg_finiteStateMarkovJumpLogAction`: extended-real fluctuation identity.
- `integral_exp_neg_finiteStateMarkovJumpLogAction`: real fluctuation identity and integrability.
- `integral_finiteStateMarkovJumpLogAction_eq_klDiv`: expected action is finite KL.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped ENNReal NNReal

open _root_.InformationTheory
open FiniteMarkovProcesses.Probability

universe u

variable {State : Type u} [Fintype State]

/-- Extended-real exponential of the complete physical jump action. -/
noncomputable def finiteStateMarkovJumpExpLogActionENNReal
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    FiniteJumpHistory State → ℝ≥0∞ :=
  fun history => ENNReal.ofReal
    (Real.exp (finiteStateMarkovJumpLogAction initial referenceInitial generator
      referenceGenerator T history))

/-- The extended-real exponential action is measurable. -/
theorem measurable_finiteStateMarkovJumpExpLogActionENNReal
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measurable (finiteStateMarkovJumpExpLogActionENNReal initial referenceInitial generator
      referenceGenerator T) :=
  ((measurable_finiteStateMarkovJumpLogAction initial referenceInitial generator
    referenceGenerator T).exp).ennreal_ofReal

/-- The candidate density measure is exactly the reference measure exponentially tilted by the
complete physical jump action. -/
theorem finiteStateMarkovJumpDensityMeasure_withDensity_exp_logAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ) :
    (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T).withDensity
        (finiteStateMarkovJumpExpLogActionENNReal initial referenceInitial generator
          referenceGenerator T) =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  calc
    _ = (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T).withDensity
        (finiteStateMarkovJumpDensityRatioENNReal initial referenceInitial generator
          referenceGenerator T) :=
      withDensity_congr_ae
        (finiteStateMarkovJumpDensityRatioENNReal_eq_exp_logAction
          hInitialSupport hRateSupport T).symm
    _ = _ := finiteStateMarkovJumpDensityMeasure_withDensity_ratio
      hInitialSupport hRateSupport T

/-- The positive and negative exponential action factors multiply to one pointwise. -/
theorem finiteStateMarkovJumpExpLogActionENNReal_mul_neg
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (T : ℝ) (history : FiniteJumpHistory State) :
    finiteStateMarkovJumpExpLogActionENNReal initial referenceInitial generator
        referenceGenerator T history *
      ENNReal.ofReal
        (Real.exp (-finiteStateMarkovJumpLogAction initial referenceInitial generator
          referenceGenerator T history)) = 1 := by
  unfold finiteStateMarkovJumpExpLogActionENNReal
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

/-- Exact extended-real integral fluctuation theorem. Both density measures must be independently
normalized before they are interpreted as probability laws. -/
theorem lintegral_exp_neg_finiteStateMarkovJumpLogAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ)
    (_hCandidateNormalized :
      FiniteStateMarkovJumpDensityIsNormalized initial generator T)
    (hReferenceNormalized :
      FiniteStateMarkovJumpDensityIsNormalized referenceInitial referenceGenerator T) :
    ∫⁻ history,
        ENNReal.ofReal
          (Real.exp (-finiteStateMarkovJumpLogAction initial referenceInitial generator
            referenceGenerator T history))
        ∂finiteStateMarkovJumpDensityMeasure initial generator T = 1 := by
  rw [← finiteStateMarkovJumpDensityMeasure_withDensity_exp_logAction
    hInitialSupport hRateSupport T]
  rw (transparency := .default) [lintegral_withDensity_eq_lintegral_mul _
    (measurable_finiteStateMarkovJumpExpLogActionENNReal
      initial referenceInitial generator referenceGenerator T)
    (((measurable_finiteStateMarkovJumpLogAction initial referenceInitial generator
      referenceGenerator T).neg.exp).ennreal_ofReal)]
  change ∫⁻ history,
      finiteStateMarkovJumpExpLogActionENNReal initial referenceInitial generator
          referenceGenerator T history *
        ENNReal.ofReal (Real.exp (-(finiteStateMarkovJumpLogAction initial referenceInitial
          generator referenceGenerator T history)))
      ∂finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T = 1
  simp_rw [finiteStateMarkovJumpExpLogActionENNReal_mul_neg]
  simpa [FiniteStateMarkovJumpDensityIsNormalized] using hReferenceNormalized

/-- The real exponential fluctuation observable is integrable and has expectation one. -/
theorem integral_exp_neg_finiteStateMarkovJumpLogAction
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ)
    (hCandidateNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator T)
    (hReferenceNormalized :
      FiniteStateMarkovJumpDensityIsNormalized referenceInitial referenceGenerator T) :
    Integrable
        (fun history => Real.exp
          (-finiteStateMarkovJumpLogAction initial referenceInitial generator
            referenceGenerator T history))
        (finiteStateMarkovJumpDensityMeasure initial generator T) ∧
      ∫ history, Real.exp
          (-finiteStateMarkovJumpLogAction initial referenceInitial generator
            referenceGenerator T history)
          ∂finiteStateMarkovJumpDensityMeasure initial generator T = 1 := by
  have hLIntegral := lintegral_exp_neg_finiteStateMarkovJumpLogAction
    hInitialSupport hRateSupport T hCandidateNormalized hReferenceNormalized
  have hMeasurable : Measurable fun history => Real.exp
      (-finiteStateMarkovJumpLogAction initial referenceInitial generator
        referenceGenerator T history) :=
    (measurable_finiteStateMarkovJumpLogAction initial referenceInitial generator
      referenceGenerator T).neg.exp
  have hNonnegative : ∀ᵐ history
      ∂finiteStateMarkovJumpDensityMeasure initial generator T,
      0 ≤ Real.exp (-finiteStateMarkovJumpLogAction initial referenceInitial generator
        referenceGenerator T history) :=
    ae_of_all _ fun _ => (Real.exp_pos _).le
  have hIntegrable : Integrable
      (fun history => Real.exp
        (-finiteStateMarkovJumpLogAction initial referenceInitial generator
          referenceGenerator T history))
      (finiteStateMarkovJumpDensityMeasure initial generator T) := by
    constructor
    · exact hMeasurable.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_ofReal hNonnegative, hLIntegral]
      exact ENNReal.one_lt_top
  refine ⟨hIntegrable, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hNonnegative hMeasurable.aestronglyMeasurable,
    hLIntegral]
  norm_num

/-- With an integrable action, its candidate expectation is the finite real KL divergence. -/
theorem integral_finiteStateMarkovJumpLogAction_eq_klDiv
    [MeasurableSpace State] [MeasurableSingletonClass State]
    {initial referenceInitial : PMF State}
    {generator referenceGenerator : FiniteStateMarkovGenerator State}
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (T : ℝ)
    (hCandidateNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator T)
    (hReferenceNormalized :
      FiniteStateMarkovJumpDensityIsNormalized referenceInitial referenceGenerator T)
    (hActionIntegrable : Integrable
      (finiteStateMarkovJumpLogAction initial referenceInitial generator referenceGenerator T)
      (finiteStateMarkovJumpDensityMeasure initial generator T)) :
    klDiv (finiteStateMarkovJumpDensityMeasure initial generator T)
        (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T) ≠ ⊤ ∧
      ∫ history, finiteStateMarkovJumpLogAction initial referenceInitial generator
          referenceGenerator T history
          ∂finiteStateMarkovJumpDensityMeasure initial generator T =
        (klDiv (finiteStateMarkovJumpDensityMeasure initial generator T)
          (finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T)).toReal := by
  let candidate := finiteStateMarkovJumpDensityMeasure initial generator T
  let reference := finiteStateMarkovJumpDensityMeasure referenceInitial referenceGenerator T
  let : IsProbabilityMeasure candidate := ⟨hCandidateNormalized⟩
  let : IsProbabilityMeasure reference := ⟨hReferenceNormalized⟩
  have hAC : candidate ≪ reference :=
    finiteStateMarkovJumpDensityMeasure_absolutelyContinuous
      hInitialSupport hRateSupport T
  have hLLR := llr_finiteStateMarkovJumpDensityMeasure hInitialSupport hRateSupport T
  have hLLRIntegrable : Integrable (llr candidate reference) candidate :=
    hActionIntegrable.congr hLLR.symm
  constructor
  · exact klDiv_ne_top_iff.mpr ⟨hAC, hLLRIntegrable⟩
  · calc
      _ = ∫ history, llr candidate reference history ∂candidate :=
        integral_congr_ae hLLR.symm
      _ = _ := (toReal_klDiv_of_measure_eq hAC (by simp)).symm

end FiniteMarkovProcesses.InformationTheory
