/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateProbabilityDensity

/-!
# Empirical probability density of a positive finite IID sample

This module constructs the simplex-valued empirical distribution of a nonempty finite sample and
its exact pushforward law under a finite IID product measure.  It is generic finite-alphabet
probability infrastructure; no Markov-jump, Renger, or large-deviation claim enters here.

## Main declarations

- `finiteIIDPositiveSampleStateCount`: exact state count in a positive finite sample.
- `finiteIIDEmpiricalProbabilityDensity`: empirical simplex point of a positive finite sample.
- `finiteIIDPositiveSampleLaw`: exact positive finite IID product law.
- `finiteIIDEmpiricalProbabilityDensityLaw`: empirical-density pushforward law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Number of coordinates of a positive finite sample equal to one selected state. -/
def finiteIIDPositiveSampleStateCount
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State)
    (state : State) : ℕ :=
  (Finset.univ.filter fun replica => sample replica = state).card

/-- State counts partition every positive finite sample exactly. -/
theorem sum_finiteIIDPositiveSampleStateCount
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State) :
    ∑ state, finiteIIDPositiveSampleStateCount successorIndex sample state =
      successorIndex + 1 := by
  unfold finiteIIDPositiveSampleStateCount
  calc
    (∑ state, (Finset.univ.filter fun replica => sample replica = state).card) =
        ∑ state, ∑ replica, if sample replica = state then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro state _hState
      exact (Finset.sum_boole
        (fun replica => sample replica = state) Finset.univ).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp

/-- Empirical probability density of a sample containing `successorIndex + 1` observations. -/
def finiteIIDEmpiricalProbabilityDensity
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State) :
    FiniteStateProbabilityDensity State where
  weight state :=
    (finiteIIDPositiveSampleStateCount successorIndex sample state : NNReal) /
      (successorIndex + 1 : NNReal)
  sum_weight := by
    rw [← Finset.sum_div]
    have hSum :
        ∑ state,
            (finiteIIDPositiveSampleStateCount successorIndex sample state : NNReal) =
          (successorIndex + 1 : NNReal) := by
      exact_mod_cast sum_finiteIIDPositiveSampleStateCount successorIndex sample
    rw [hSum]
    simp

/-- Each empirical coordinate is its exact sample count divided by positive sample size. -/
theorem finiteIIDEmpiricalProbabilityDensity_weight
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State) (state : State) :
    (finiteIIDEmpiricalProbabilityDensity successorIndex sample).weight state =
      (finiteIIDPositiveSampleStateCount successorIndex sample state : NNReal) /
        (successorIndex + 1 : NNReal) := by
  rfl

/-- Every real-valued replica average is exactly the corresponding empirical-density-weighted
state average.  This is the finite regrouping identity behind deterministic heterogeneous
particle mixtures. -/
theorem sum_div_eq_sum_finiteIIDEmpiricalProbabilityDensity_weight_mul
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State)
    (value : State → ℝ) :
    (∑ replica, value (sample replica)) / (successorIndex + 1 : ℝ) =
      ∑ state,
        ((finiteIIDEmpiricalProbabilityDensity successorIndex sample).weight state : ℝ) *
          value state := by
  rw [show (∑ replica, value (sample replica)) =
      ∑ state, ∑ replica ∈ Finset.univ with sample replica = state, value state by
    exact (Finset.sum_fiberwise' Finset.univ sample value).symm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [finiteIIDEmpiricalProbabilityDensity_weight, NNReal.coe_div, NNReal.coe_natCast]
  simp only [finiteIIDPositiveSampleStateCount, Finset.sum_const, nsmul_eq_mul]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

variable [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The empirical-density observation is measurable on every positive finite sample space. -/
theorem measurable_finiteIIDEmpiricalProbabilityDensity (successorIndex : ℕ) :
    Measurable (finiteIIDEmpiricalProbabilityDensity (State := State) successorIndex) :=
  measurable_of_finite _

/-- The exact product law of `successorIndex + 1` IID observations from one finite PMF. -/
noncomputable def finiteIIDPositiveSampleLaw
    (successorIndex : ℕ) (law : PMF State) :
    Measure (Fin (successorIndex + 1) → State) :=
  Measure.pi fun _ => law.toMeasure

/-- The positive finite IID sample law is exactly normalized. -/
noncomputable instance instIsProbabilityMeasureFiniteIIDPositiveSampleLaw
    (successorIndex : ℕ) (law : PMF State) :
    IsProbabilityMeasure (finiteIIDPositiveSampleLaw successorIndex law) := by
  unfold finiteIIDPositiveSampleLaw
  infer_instance

omit [Fintype State] [DecidableEq State] [MeasurableSingletonClass State] in
/-- Every coordinate projection of the positive finite IID sample law has the supplied PMF. -/
theorem finiteIIDPositiveSampleLaw_coordinate_map
    (successorIndex : ℕ) (law : PMF State) (replica : Fin (successorIndex + 1)) :
    Measure.map (Function.eval replica) (finiteIIDPositiveSampleLaw successorIndex law) =
      law.toMeasure := by
  unfold finiteIIDPositiveSampleLaw
  exact (measurePreserving_eval (fun _ : Fin (successorIndex + 1) => law.toMeasure) replica).map_eq

omit [Fintype State] [DecidableEq State] in
/-- Every complete positive IID sample word has exactly the product of its coordinate masses. -/
theorem finiteIIDPositiveSampleLaw_apply_singleton
    (successorIndex : ℕ) (law : PMF State)
    (sample : Fin (successorIndex + 1) → State) :
    finiteIIDPositiveSampleLaw successorIndex law {sample} =
      ∏ replica, law (sample replica) := by
  unfold finiteIIDPositiveSampleLaw
  have hSingleton :
      ({sample} : Set (Fin (successorIndex + 1) → State)) =
        Set.pi Set.univ (fun replica => {sample replica}) := by
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      forall_const]
    constructor
    · intro hCandidate
      subst candidate
      exact fun _ => rfl
    · intro hCandidate
      funext replica
      exact hCandidate replica
  rw [hSingleton, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro replica _hReplica
  exact PMF.toMeasure_apply_singleton law (sample replica)
    (MeasurableSet.singleton _)

/-- Pushforward law of the empirical probability density of a positive finite IID sample. -/
noncomputable def finiteIIDEmpiricalProbabilityDensityLaw
    (successorIndex : ℕ) (law : PMF State) :
    Measure (FiniteStateProbabilityDensity State) :=
  Measure.map (finiteIIDEmpiricalProbabilityDensity successorIndex)
    (finiteIIDPositiveSampleLaw successorIndex law)

/-- The empirical probability-density law is exactly normalized. -/
noncomputable instance instIsProbabilityMeasureFiniteIIDEmpiricalProbabilityDensityLaw
    (successorIndex : ℕ) (law : PMF State) :
    IsProbabilityMeasure (finiteIIDEmpiricalProbabilityDensityLaw successorIndex law) := by
  unfold finiteIIDEmpiricalProbabilityDensityLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_finiteIIDEmpiricalProbabilityDensity successorIndex).aemeasurable).2
    inferInstance

end

end FiniteMarkovProcesses.Probability
