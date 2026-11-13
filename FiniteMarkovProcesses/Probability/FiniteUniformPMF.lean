/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform probability mass functions on finite types

The uniform mass function is constructed with `PMF.ofFintype`. Its pointwise law is the inverse
cardinality of the nonempty carrier, so the construction needs no decidable-equality assumption.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped ENNReal

/-- The probability mass function assigning the same mass to every point of a finite type. -/
noncomputable def finiteUniformPMF (State : Type*) [Fintype State] [Nonempty State] : PMF State :=
  PMF.ofFintype (fun _state => (Fintype.card State : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp)
      (ENNReal.natCast_ne_top _))

/-- Every point of the uniform finite mass function has exactly the inverse-cardinality mass. -/
@[simp]
theorem finiteUniformPMF_apply (State : Type*) [Fintype State] [Nonempty State] (state : State) :
    finiteUniformPMF State state = (Fintype.card State : ℝ≥0∞)⁻¹ :=
  rfl

end FiniteMarkovProcesses.Probability
