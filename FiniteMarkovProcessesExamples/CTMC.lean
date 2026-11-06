/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.CTMC

/-!
# Finite-state jump-process examples

A concrete two-state generator and applications that discharge the normalization premises of
the integral fluctuation identity. The measurable state-space structure remains explicit.
-/

namespace FiniteMarkovProcessesExamples.CTMC

open MeasureTheory
open FiniteMarkovProcesses.Probability FiniteMarkovProcesses.InformationTheory
open scoped ENNReal NNReal

/-- A two-state chain that flips at unit rate in either direction. -/
def flipGenerator : FiniteStateMarkovGenerator Bool where
  rate source target := if source = target then 0 else 1
  rate_self state := by simp

/-- A reference two-state chain that flips at twice the candidate rate. -/
def doubleFlipGenerator : FiniteStateMarkovGenerator Bool where
  rate source target := if source = target then 0 else 2
  rate_self state := by simp

/-- The two generators have identical directed support despite different positive rates. -/
theorem flipGenerators_haveSameDirectedSupport :
    flipGenerator.HaveSameDirectedSupport doubleFlipGenerator := by
  intro source target
  by_cases h : source = target <;> simp [flipGenerator, doubleFlipGenerator, h]

/-- The physical density of the two-state chain is normalized at each finite horizon. -/
theorem flipLaw_normalized [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (duration : ℝ≥0) :
    FiniteStateMarkovJumpDensityIsNormalized (PMF.pure false) flipGenerator duration :=
  finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
    (PMF.pure false) flipGenerator duration duration.coe_nonneg

/-- The stopped generative law agrees with the physical density, including at time zero. -/
theorem flipStoppedLaw_eq_density [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (duration : ℝ≥0) :
    FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
        (PMF.pure false) flipGenerator duration =
      finiteStateMarkovJumpDensityMeasure (PMF.pure false) flipGenerator duration :=
  finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    (PMF.pure false) flipGenerator duration duration.coe_nonneg

/-- Common support and a finite nonnegative horizon suffice for the extended-real IFT;
normalization is supplied by the constructive CTMC theorem. -/
theorem fluctuationIdentity
    {State : Type*} [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial referenceInitial : PMF State)
    (generator referenceGenerator : FiniteStateMarkovGenerator State)
    (hInitialSupport : FiniteInitialDistributionsHaveSameSupport initial referenceInitial)
    (hRateSupport : generator.HaveSameDirectedSupport referenceGenerator)
    (duration : ℝ≥0) :
    ∫⁻ history,
        ENNReal.ofReal (Real.exp (-finiteStateMarkovJumpLogAction initial referenceInitial
          generator referenceGenerator duration history))
        ∂finiteStateMarkovJumpDensityMeasure initial generator duration = 1 :=
  lintegral_exp_neg_finiteStateMarkovJumpLogAction hInitialSupport hRateSupport duration
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      initial generator duration duration.coe_nonneg)
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      referenceInitial referenceGenerator duration duration.coe_nonneg)

/-- The IFT for a unit-rate chain compared with a double-rate reference over duration two.
Both chains start at `false`; common support and normalization are proved explicitly. -/
theorem unitToDoubleFlip_fluctuationIdentity
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool] :
    ∫⁻ history,
        ENNReal.ofReal (Real.exp (-finiteStateMarkovJumpLogAction
          (PMF.pure false) (PMF.pure false) flipGenerator doubleFlipGenerator 2 history))
        ∂finiteStateMarkovJumpDensityMeasure (PMF.pure false) flipGenerator 2 = 1 :=
  lintegral_exp_neg_finiteStateMarkovJumpLogAction
    (initial := PMF.pure false) (referenceInitial := PMF.pure false)
    (generator := flipGenerator) (referenceGenerator := doubleFlipGenerator)
    (fun _ => Iff.rfl) flipGenerators_haveSameDirectedSupport 2
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure false) flipGenerator 2 (by norm_num))
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      (PMF.pure false) doubleFlipGenerator 2 (by norm_num))

/-- A bounded measurable time-dependent rate family has a normalized physical history law. -/
theorem timeDependentLaw_normalized
    {State : Type*} [Fintype State] [DecidableEq State]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    finiteStateTimeDependentMarkovJumpDensityMeasure initial rates duration Set.univ = 1 :=
  finiteStateTimeDependentMarkovJumpDensityMeasure_univ initial rates duration.coe_nonneg

end FiniteMarkovProcessesExamples.CTMC
