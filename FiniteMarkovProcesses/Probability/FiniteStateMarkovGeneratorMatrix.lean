/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.LinearAlgebra.Matrix.Defs
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpLaw

/-!
# Matrix convention for finite-state Markov generators

This module relates the repository's zero-diagonal nonnegative jump-rate convention with a
separately stored escape rate to the standard signed generator-matrix convention.  Off-diagonal
entries are the jump rates, diagonal entries are negative escape rates, and every row sums to zero.

## Main results

- `FiniteStateMarkovGenerator.matrixEntry_self`: the diagonal is negative escape rate.
- `FiniteStateMarkovGenerator.matrixEntry_of_ne`: off-diagonal matrix entries are jump rates.
- `FiniteStateMarkovGenerator.sum_matrixEntry`: every matrix row sums to zero.
- `FiniteStateMarkovGenerator.ofMatrix`: recover jump rates from a signed matrix.
- `FiniteStateMarkovGenerator.toMatrix_ofMatrix`: recover the input matrix when rows sum to zero.
- `FiniteStateMarkovGenerator.ofMatrix_toMatrix`: recover the original generator.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Signed generator-matrix entry corresponding to the repository's nonnegative off-diagonal rate
and separate escape-rate convention. -/
def FiniteStateMarkovGenerator.matrixEntry
    (generator : FiniteStateMarkovGenerator State) (source target : State) : ℝ :=
  if source = target then -(generator.escapeRate source : ℝ)
  else generator.rate source target

/-- A signed generator-matrix diagonal is the negative escape rate. -/
theorem FiniteStateMarkovGenerator.matrixEntry_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.matrixEntry state state = -(generator.escapeRate state : ℝ) := by
  simp [FiniteStateMarkovGenerator.matrixEntry]

/-- Every signed off-diagonal generator-matrix entry is the corresponding nonnegative jump rate. -/
theorem FiniteStateMarkovGenerator.matrixEntry_of_ne
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hDistinct : source ≠ target) :
    generator.matrixEntry source target = generator.rate source target := by
  simp [FiniteStateMarkovGenerator.matrixEntry, hDistinct]

/-- Every signed generator-matrix row sums to zero. -/
theorem FiniteStateMarkovGenerator.sum_matrixEntry
    (generator : FiniteStateMarkovGenerator State) (source : State) :
    ∑ target, generator.matrixEntry source target = 0 := by
  classical
  unfold FiniteStateMarkovGenerator.matrixEntry
  calc
    _ = (∑ target, if source = target then
          -(generator.escapeRate source : ℝ) else 0) +
        ∑ target, (generator.rate source target : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro target
      by_cases hTarget : source = target
      · subst target
        simp [generator.rate_self]
      · simp [hTarget]
    _ = -(generator.escapeRate source : ℝ) +
        ∑ target, (generator.rate source target : ℝ) := by
      rw [Fintype.sum_ite_eq source]
    _ = 0 := by
      simp [FiniteStateMarkovGenerator.escapeRate]

/-- The signed square matrix of a finite-state generator. -/
def FiniteStateMarkovGenerator.toMatrix
    (generator : FiniteStateMarkovGenerator State) : Matrix State State ℝ :=
  Matrix.of generator.matrixEntry

/-- Computing an entry of the signed matrix uses the signed-entry convention. -/
@[simp]
theorem FiniteStateMarkovGenerator.toMatrix_apply
    (generator : FiniteStateMarkovGenerator State) (source target : State) :
    generator.toMatrix source target = generator.matrixEntry source target := rfl

/-- Exported matrices have nonnegative off-diagonal entries. -/
theorem FiniteStateMarkovGenerator.toMatrix_offDiag_nonneg
    (generator : FiniteStateMarkovGenerator State) (source target : State)
    (hDistinct : source ≠ target) : 0 ≤ generator.toMatrix source target := by
  rw [toMatrix_apply, matrixEntry_of_ne _ hDistinct]
  exact NNReal.coe_nonneg _

/-- Recover physical jump rates from a signed matrix with nonnegative off-diagonal entries.
The input diagonal is redundant when the rows sum to zero, as in `toMatrix_ofMatrix`. -/
def FiniteStateMarkovGenerator.ofMatrix (matrix : Matrix State State ℝ)
    (hOffDiag : ∀ source target, source ≠ target → 0 ≤ matrix source target) :
    FiniteStateMarkovGenerator State where
  rate source target := if h : source = target then 0 else ⟨matrix source target, hOffDiag _ _ h⟩
  rate_self state := by simp

omit [Fintype State] in
/-- A recovered off-diagonal jump rate is the corresponding input matrix entry. -/
theorem FiniteStateMarkovGenerator.rate_ofMatrix_of_ne (matrix : Matrix State State ℝ)
    (hOffDiag : ∀ source target, source ≠ target → 0 ≤ matrix source target)
    {source target : State} (hDistinct : source ≠ target) :
    ((ofMatrix matrix hOffDiag).rate source target : ℝ) = matrix source target := by
  simp [ofMatrix, hDistinct]
  rfl

/-- Turning recovered rates back into a signed matrix preserves every entry of a zero-row-sum
matrix, including diagonal entries of absorbing states. -/
@[simp]
theorem FiniteStateMarkovGenerator.toMatrix_ofMatrix (matrix : Matrix State State ℝ)
    (hOffDiag : ∀ source target, source ≠ target → 0 ≤ matrix source target)
    (hRowSum : ∀ source, ∑ target, matrix source target = 0) :
    (ofMatrix matrix hOffDiag).toMatrix = matrix := by
  ext source target
  by_cases hDistinct : source ≠ target
  · rw [toMatrix_apply, matrixEntry_of_ne _ hDistinct,
      rate_ofMatrix_of_ne _ _ hDistinct]
  · have hTarget : target = source := (not_ne_iff.mp hDistinct).symm
    subst target
    have hOffDiagSum : ∑ target ∈ Finset.univ.erase source,
        (ofMatrix matrix hOffDiag).matrixEntry source target =
        ∑ target ∈ Finset.univ.erase source, matrix source target := by
      apply Finset.sum_congr rfl
      intro target hTarget
      have hDistinct := (Finset.mem_erase.mp hTarget).1.symm
      rw [matrixEntry_of_ne _ hDistinct, rate_ofMatrix_of_ne _ _ hDistinct]
    have hRecovered := (ofMatrix matrix hOffDiag).sum_matrixEntry source
    have hOriginal := hRowSum source
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ source), hOffDiagSum] at hRecovered
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ source)] at hOriginal
    rw [toMatrix_apply]
    exact add_left_cancel (hRecovered.trans hOriginal.symm)

/-- In a zero-row-sum matrix the negative diagonal is the recovered escape rate. -/
theorem FiniteStateMarkovGenerator.escapeRate_ofMatrix (matrix : Matrix State State ℝ)
    (hOffDiag : ∀ source target, source ≠ target → 0 ≤ matrix source target)
    (hRowSum : ∀ source, ∑ target, matrix source target = 0) (source : State) :
    ((ofMatrix matrix hOffDiag).escapeRate source : ℝ) = -matrix source source := by
  have hDiag := congrFun (congrFun (toMatrix_ofMatrix matrix hOffDiag hRowSum) source) source
  rw [toMatrix_apply, matrixEntry_self] at hDiag
  simp [← hDiag]

/-- Decoding a generator's signed matrix recovers the original generator. -/
@[simp]
theorem FiniteStateMarkovGenerator.ofMatrix_toMatrix
    (generator : FiniteStateMarkovGenerator State) :
    ofMatrix generator.toMatrix generator.toMatrix_offDiag_nonneg = generator := by
  apply FiniteStateMarkovGenerator.ext
  funext source target
  by_cases hDistinct : source ≠ target
  · apply Subtype.ext
    change ((ofMatrix generator.toMatrix _).rate source target : ℝ) = generator.rate source target
    rw [rate_ofMatrix_of_ne _ _ hDistinct, toMatrix_apply, matrixEntry_of_ne _ hDistinct]
  · have hTarget : target = source := (not_ne_iff.mp hDistinct).symm
    subst target
    rw [rate_self, rate_self]

end FiniteMarkovProcesses.Probability
