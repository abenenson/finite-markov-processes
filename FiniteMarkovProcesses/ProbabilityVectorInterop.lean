/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateProbabilityDensity
import FiniteMarkovKernels.PMFAdapter

/-!
# Probability simplex interoperability

The empirical-density API uses nonnegative-real coordinates, while the public finite-kernel API
uses real coordinates with an explicit nonnegativity proof. The coordinate maps below are exact
inverses, preserve support and strict positivity, and produce the same probability mass function.
Both public types already carry their coordinatewise topology, so their equivalence is also a
homeomorphism without introducing any additional topology instance.
-/

namespace FiniteMarkovProcesses.InformationTheory.FiniteStateProbabilityDensity

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State]

/-- Regard nonnegative-real empirical-density coordinates as a public real probability vector. -/
def toProbabilityVector (density : FiniteStateProbabilityDensity State) :
    FiniteMarkovKernels.ProbabilityVector State where
  prob := density.realWeight
  nonneg state := (density.weight state).coe_nonneg
  sum_eq_one := by
    change (∑ state, (density.weight state : ℝ)) = 1
    exact_mod_cast density.sum_weight

/-- Regard a public probability vector as a typed empirical density with the same coordinates. -/
def ofProbabilityVector (law : FiniteMarkovKernels.ProbabilityVector State) :
    FiniteStateProbabilityDensity State where
  weight state := ⟨law state, law.nonneg state⟩
  sum_weight := by
    apply NNReal.eq
    rw [NNReal.coe_sum]
    exact law.sum_eq_one

/-- Conversion to a real probability vector preserves each coordinate. -/
@[simp]
theorem toProbabilityVector_apply (density : FiniteStateProbabilityDensity State) (state : State) :
    density.toProbabilityVector state = (density.weight state : ℝ) :=
  rfl

/-- Conversion to a nonnegative-real density preserves each real coordinate. -/
@[simp]
theorem ofProbabilityVector_weight_coe
    (law : FiniteMarkovKernels.ProbabilityVector State) (state : State) :
    ((ofProbabilityVector law).weight state : ℝ) = law state :=
  rfl

/-- Converting a density to a probability vector and back recovers the same density. -/
@[simp]
theorem ofProbabilityVector_toProbabilityVector (density : FiniteStateProbabilityDensity State) :
    ofProbabilityVector density.toProbabilityVector = density := by
  apply FiniteStateProbabilityDensity.ext
  intro state
  apply NNReal.eq
  rfl

/-- Converting a probability vector to a density and back recovers the same probability vector. -/
@[simp]
theorem toProbabilityVector_ofProbabilityVector
    (law : FiniteMarkovKernels.ProbabilityVector State) :
    (ofProbabilityVector law).toProbabilityVector = law := by
  apply FiniteMarkovKernels.ProbabilityVector.ext
  intro state
  rfl

/-- Exact equivalence between the empirical-density and public finite-kernel simplex carriers. -/
def probabilityVectorEquiv :
    FiniteStateProbabilityDensity State ≃ FiniteMarkovKernels.ProbabilityVector State where
  toFun := toProbabilityVector
  invFun := ofProbabilityVector
  left_inv := ofProbabilityVector_toProbabilityVector
  right_inv := toProbabilityVector_ofProbabilityVector

/-- The map to real probability vectors is continuous for the existing coordinate topologies. -/
theorem continuous_toProbabilityVector :
    Continuous (toProbabilityVector (State := State)) := by
  exact continuous_induced_rng.mpr continuous_realWeight

/-- The inverse map is continuous for the existing coordinate topologies. -/
theorem continuous_ofProbabilityVector :
    Continuous (ofProbabilityVector (State := State)) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro state
  exact (FiniteMarkovKernels.ProbabilityVector.continuous_apply state).subtype_mk _

/-- The two existing coordinatewise probability simplices are homeomorphic. -/
def probabilityVectorHomeomorph :
    FiniteStateProbabilityDensity State ≃ₜ FiniteMarkovKernels.ProbabilityVector State where
  toEquiv := probabilityVectorEquiv
  continuous_toFun := continuous_toProbabilityVector
  continuous_invFun := continuous_ofProbabilityVector

/-- A coordinate vanishes in one representation exactly when it vanishes in the other. -/
@[simp]
theorem toProbabilityVector_apply_eq_zero_iff
    (density : FiniteStateProbabilityDensity State) (state : State) :
    density.toProbabilityVector state = 0 ↔ density.weight state = 0 := by
  simp only [toProbabilityVector_apply, NNReal.coe_eq_zero]

/-- Positive support coordinates agree in the two simplex representations. -/
@[simp]
theorem toProbabilityVector_apply_pos_iff
    (density : FiniteStateProbabilityDensity State) (state : State) :
    0 < density.toProbabilityVector state ↔ 0 < density.weight state := by
  simp only [toProbabilityVector_apply, NNReal.coe_pos]

/-- Strictly positive empirical densities are exactly full-support public probability vectors. -/
@[simp]
theorem toProbabilityVector_fullSupport_iff (density : FiniteStateProbabilityDensity State) :
    density.toProbabilityVector.FullSupport ↔ density.IsInterior := by
  constructor <;> intro h state <;> exact_mod_cast h state

/-- Lower-boundary points correspond to probability vectors with a zero coordinate. -/
theorem toProbabilityVector_exists_zero_iff (density : FiniteStateProbabilityDensity State) :
    (∃ state, density.toProbabilityVector state = 0) ↔ density.IsOnLowerBoundary := by
  simp only [toProbabilityVector_apply_eq_zero_iff, IsOnLowerBoundary]

/-- Conversion preserves the complete zero-coordinate support relation. -/
theorem toProbabilityVector_absolutelyContinuous_iff
    (density reference : FiniteStateProbabilityDensity State) :
    density.toProbabilityVector.AbsolutelyContinuous reference.toProbabilityVector ↔
      ∀ state, reference.weight state = 0 → density.weight state = 0 := by
  simp only [FiniteMarkovKernels.ProbabilityVector.AbsolutelyContinuous,
    toProbabilityVector_apply_eq_zero_iff]

/-- Both public PMF adapters assign exactly the same mass at every finite state. -/
@[simp]
theorem toProbabilityVector_toPMF (density : FiniteStateProbabilityDensity State) :
    density.toProbabilityVector.toPMF = density.probabilityMassFunction := by
  apply PMF.ext
  intro state
  simp only [FiniteMarkovKernels.ProbabilityVector.toPMF_apply, toProbabilityVector_apply,
    probabilityMassFunction_apply, ENNReal.ofReal_coe_nnreal]

/-- Transporting a public probability vector to a density preserves its canonical PMF. -/
@[simp]
theorem ofProbabilityVector_probabilityMassFunction
    (law : FiniteMarkovKernels.ProbabilityVector State) :
    (ofProbabilityVector law).probabilityMassFunction = law.toPMF := by
  rw [← toProbabilityVector_toPMF, toProbabilityVector_ofProbabilityVector]

end FiniteMarkovProcesses.InformationTheory.FiniteStateProbabilityDensity
