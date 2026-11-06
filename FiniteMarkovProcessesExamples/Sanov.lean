/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Sanov

/-!
# Binary finite-alphabet Sanov examples

A fair reference satisfies the explicit interior hypothesis. A sample consisting entirely of
`true` has a boundary empirical density, and its type still satisfies the finite-sample lower
bound. Positive sample size does not require every state to occur.
-/

namespace FiniteMarkovProcessesExamples.Sanov

open FiniteMarkovProcesses.InformationTheory FiniteMarkovProcesses.Probability
open scoped BigOperators ENNReal NNReal

noncomputable section

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

/-- Uniform binary reference distribution. -/
def fairBinary : FiniteStateProbabilityDensity Bool where
  weight _ := (1 / 2 : NNReal)
  sum_weight := by norm_num [Fintype.sum_bool]

/-- Both reference coordinates are strictly positive. -/
theorem fairBinary_isInterior : fairBinary.IsInterior := by
  intro state
  norm_num [fairBinary]

/-- The literal upper bound for the fair binary empirical law. -/
example :
    HasLargeDeviationUpperBound
      (scaledEventLogProbability
        (fun n => finiteIIDEmpiricalProbabilityDensityLaw n fairBinary.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (finiteStateProbabilityDensityRelativeEntropy fairBinary) :=
  finiteIIDEmpiricalProbabilityDensityLaw_closedUpperBound fairBinary fairBinary_isInterior

/-- The literal lower bound includes neighborhoods of boundary empirical points. -/
example :
    HasLargeDeviationLowerBound
      (scaledEventLogProbability
        (fun n => finiteIIDEmpiricalProbabilityDensityLaw n fairBinary.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed)
      (finiteStateProbabilityDensityRelativeEntropy fairBinary) :=
  finiteIIDEmpiricalProbabilityDensityLaw_openLowerBound fairBinary fairBinary_isInterior

/-- The binary relative-entropy rate is good on the closed simplex. -/
example : IsGoodRateFunction (finiteStateProbabilityDensityRelativeEntropy fairBinary) :=
  finiteStateProbabilityDensityRelativeEntropy_isGoodRateFunction fairBinary fairBinary_isInterior

/-- Every positive sample made entirely of `true` has an empirical zero coordinate. -/
example (n : ℕ) :
    (finiteIIDEmpiricalProbabilityDensity n (fun _ => true)).IsOnLowerBoundary := by
  refine ⟨false, ?_⟩
  simp [finiteIIDEmpiricalProbabilityDensity, finiteIIDPositiveSampleStateCount]

/-- A concrete boundary count type: every observation is `true`. -/
def allTrueType (n : ℕ) : FiniteIIDPositiveEmpiricalType Bool n where
  count state := if state then ⟨n + 1, Nat.lt_succ_self _⟩ else 0
  sum_count := by simp

/-- Its normalized count vector lies on the closed-simplex boundary. -/
example (n : ℕ) : (allTrueType n).probabilityDensity.IsOnLowerBoundary := by
  refine ⟨false, ?_⟩
  simp [allTrueType, FiniteIIDPositiveEmpiricalType.probabilityDensity]

/-- The finite-sample lower bound applies at a boundary point for any measurable event containing
that type. -/
example (n : ℕ) {event : Set (FiniteStateProbabilityDensity Bool)}
    (hEvent : MeasurableSet event)
    (hMem : (allTrueType n).probabilityDensity ∈ event) :
    (-(finiteStateProbabilityDensityRelativeEntropyReal fairBinary
        (allTrueType n).probabilityDensity) -
      finiteEmpiricalTypeLogarithmicOverhead (Fintype.card Bool) n : ℝ) ≤
      scaledEventLogProbability
        (fun index => finiteIIDEmpiricalProbabilityDensityLaw index
          fairBinary.probabilityMassFunction)
        (fun _ => id) finiteIIDPositiveSampleSpeed n event :=
  scaledEventLogProbability_finiteIIDEmpiricalProbabilityDensityLaw_lowerBound_of_type_mem
    fairBinary fairBinary_isInterior n (allTrueType n) hEvent hMem

/-- Successor index three means exactly four samples. -/
example : finiteIIDPositiveSampleSpeed 3 = 4 := rfl

end

end FiniteMarkovProcessesExamples.Sanov
