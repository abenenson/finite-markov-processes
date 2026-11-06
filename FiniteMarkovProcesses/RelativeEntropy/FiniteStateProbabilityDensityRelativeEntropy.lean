/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateProbabilityDensity
import FiniteMarkovProcesses.RelativeEntropy.PoissonRateDiscrimination

/-!
# Relative entropy of finite-state probability densities

This module defines the finite-simplex relative entropy against a strictly positive reference.
The real-valued definition is a sum of Poisson discrimination terms.  Because both densities
have total mass one, its linear terms cancel exactly and leave the familiar oriented
`sum p * log (p / q)` formula.  The extended nonnegative wrapper is finite and continuous on the
entire closed simplex whenever the reference is in its interior.

The construction is source-neutral.  It does not identify an initial Markov law or assert any
large-deviation bound.

## Main declarations

- `finiteStateProbabilityDensityRelativeEntropyReal`: real finite-simplex relative entropy.
- `finiteStateProbabilityDensityRelativeEntropy`: its nonnegative extended-real wrapper.
- `continuous_finiteStateProbabilityDensityRelativeEntropy`: continuity for positive reference.
-/

namespace FiniteMarkovProcesses.InformationTheory

open scoped BigOperators ENNReal NNReal

open _root_.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State]

/-- Real-valued relative entropy between finite-state probability densities, expressed as the
sum of Poisson discrimination coordinates so the zero-density boundary remains continuous. -/
def finiteStateProbabilityDensityRelativeEntropyReal
    (reference density : FiniteStateProbabilityDensity State) : ℝ :=
  ∑ state,
    poissonRateDiscrimination (density.weight state) (reference.weight state)

/-- The linear terms in the coordinatewise Poisson discriminations cancel on the simplex,
leaving the ordinary oriented finite relative-entropy formula. -/
theorem finiteStateProbabilityDensityRelativeEntropyReal_eq_sum_mul_log
    (reference density : FiniteStateProbabilityDensity State) :
    finiteStateProbabilityDensityRelativeEntropyReal reference density =
      ∑ state, (density.weight state : ℝ) *
        Real.log ((density.weight state : ℝ) / (reference.weight state : ℝ)) := by
  unfold finiteStateProbabilityDensityRelativeEntropyReal poissonRateDiscrimination
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hDensity : ∑ state, (density.weight state : ℝ) = 1 := by
    exact_mod_cast density.sum_weight
  have hReference : ∑ state, (reference.weight state : ℝ) = 1 := by
    exact_mod_cast reference.sum_weight
  rw [hDensity, hReference]
  ring

/-- Relative entropy against an interior reference is nonnegative on the entire closed finite
simplex. -/
theorem finiteStateProbabilityDensityRelativeEntropyReal_nonneg
    (reference density : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    0 ≤ finiteStateProbabilityDensityRelativeEntropyReal reference density := by
  unfold finiteStateProbabilityDensityRelativeEntropyReal
  exact Finset.sum_nonneg fun state _hState =>
    poissonRateDiscrimination_nonneg (by positivity)
      (by exact_mod_cast hReference state)

/-- Relative entropy against a fixed interior reference is continuous on the closed finite
simplex, including at zero density coordinates. -/
theorem continuous_finiteStateProbabilityDensityRelativeEntropyReal
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    Continuous fun density =>
      finiteStateProbabilityDensityRelativeEntropyReal reference density := by
  unfold finiteStateProbabilityDensityRelativeEntropyReal
  apply continuous_finsetSum
  intro state _hState
  have hReferenceReal : 0 < (reference.weight state : ℝ) := by
    exact_mod_cast hReference state
  rw [show (fun density : FiniteStateProbabilityDensity State =>
      poissonRateDiscrimination (density.weight state) (reference.weight state)) =
    fun density => (reference.weight state : ℝ) *
      klFun ((density.weight state : ℝ) / (reference.weight state : ℝ)) by
      funext density
      exact poissonRateDiscrimination_eq_reference_mul_klFun hReferenceReal]
  have hCoordinate :
      Continuous fun density : FiniteStateProbabilityDensity State =>
        (density.weight state : ℝ) :=
    NNReal.continuous_coe.comp
      (FiniteStateProbabilityDensity.continuous_weight_apply state)
  exact continuous_const.mul (continuous_klFun.comp
    (hCoordinate.div_const (reference.weight state : ℝ)))

/-- Nonnegative extended-real finite-state relative entropy.  With an interior reference this is
always finite because it is the `ofReal` image of the continuous real formula. -/
def finiteStateProbabilityDensityRelativeEntropy
    (reference density : FiniteStateProbabilityDensity State) : ENNReal :=
  ENNReal.ofReal (finiteStateProbabilityDensityRelativeEntropyReal reference density)

/-- Relative entropy against an interior reference never equals infinity. -/
theorem finiteStateProbabilityDensityRelativeEntropy_ne_top
    (reference density : FiniteStateProbabilityDensity State) :
    finiteStateProbabilityDensityRelativeEntropy reference density ≠ ∞ := by
  exact ENNReal.ofReal_ne_top

/-- The extended finite-state relative entropy is continuous for an interior reference. -/
theorem continuous_finiteStateProbabilityDensityRelativeEntropy
    (reference : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    Continuous fun density =>
      finiteStateProbabilityDensityRelativeEntropy reference density := by
  exact ENNReal.continuous_ofReal.comp
    (continuous_finiteStateProbabilityDensityRelativeEntropyReal reference hReference)

/-- The extended rate's real value is the literal real relative entropy against an interior
reference. -/
theorem finiteStateProbabilityDensityRelativeEntropy_toReal
    (reference density : FiniteStateProbabilityDensity State)
    (hReference : reference.IsInterior) :
    (finiteStateProbabilityDensityRelativeEntropy reference density).toReal =
      finiteStateProbabilityDensityRelativeEntropyReal reference density := by
  rw [finiteStateProbabilityDensityRelativeEntropy,
    ENNReal.toReal_ofReal
      (finiteStateProbabilityDensityRelativeEntropyReal_nonneg
        reference density hReference)]

end

end FiniteMarkovProcesses.InformationTheory
