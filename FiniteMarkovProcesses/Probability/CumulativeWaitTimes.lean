/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import FiniteMarkovProcesses.Probability.FiniteJumpHistory

/-!
# Cumulative waiting-time coordinates

This module identifies positive waiting-time increments with ordered event times through the
lower-triangular cumulative-sum map. Its determinant is one, so the change of variables preserves
finite-dimensional Lebesgue measure exactly.

## Main results

- `cumulativeWaitTimes`: the linear map from waiting increments to cumulative event times.
- `cumulativeWaitTimes_injective`: cumulative waiting times determine every increment.
- `cumulativeWaitTimes_mem_orderedJumpTimes_iff`: positive increments whose total is below the
  horizon are exactly the preimage of the ordered event-time simplex.
- `cumulativeWaitTimes_map_volume`: the cumulative-sum map preserves Lebesgue measure.
- `cumulativeWaitTimes_map_restrict_preimage_orderedJumpTimes`: the exact restricted-volume
  transport onto the ordered event-time simplex.
- `FiniteJumpHistory.dwellTimeVector_cumulativeWaitTimes_castSucc`: cumulative coordinates recover
  every preterminal wait.
- `FiniteJumpHistory.dwellTimeVector_cumulativeWaitTimes_last`: the terminal dwell is the remaining
  horizon.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The lower-triangular matrix whose action takes prefix sums. -/
def cumulativeWaitMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j ≤ i then 1 else 0

/-- The linear map from waiting-time increments to cumulative event times. -/
def cumulativeWaitTimes (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (cumulativeWaitMatrix n)

/-- The cumulative waiting time at one coordinate is the sum of all preceding increments,
including the increment at that coordinate. -/
@[simp 900]
theorem cumulativeWaitTimes_apply (n : ℕ) (waits : Fin n → ℝ) (i : Fin n) :
    cumulativeWaitTimes n waits i = ∑ j ∈ Finset.Iic i, waits j := by
  simp only [cumulativeWaitTimes, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    cumulativeWaitMatrix, ite_mul, one_mul, zero_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j hj
    rfl

/-- The first cumulative event time is the first waiting-time increment. -/
@[simp]
theorem cumulativeWaitTimes_zero (waits : Fin (n + 1) → ℝ) :
    cumulativeWaitTimes (n + 1) waits 0 = waits 0 := by
  rw [cumulativeWaitTimes_apply]
  have hIic : Finset.Iic (0 : Fin (n + 1)) = {0} := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    exact Fin.le_zero_iff
  rw [hIic]
  simp

/-- The final cumulative event time is the sum of every waiting-time increment. -/
@[simp]
theorem cumulativeWaitTimes_last (waits : Fin (n + 1) → ℝ) :
    cumulativeWaitTimes (n + 1) waits (Fin.last n) = ∑ i, waits i := by
  rw [cumulativeWaitTimes_apply]
  have hIic : Finset.Iic (Fin.last n) = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last i
  rw [hIic]

/-- Every noninitial cumulative event time is the previous cumulative time plus its own
waiting-time increment. -/
theorem cumulativeWaitTimes_eq_previous_add
    (waits : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : i ≠ 0) :
    cumulativeWaitTimes (n + 1) waits i =
      cumulativeWaitTimes (n + 1) waits (i.pred hi).castSucc + waits i := by
  rw [cumulativeWaitTimes_apply, cumulativeWaitTimes_apply]
  have hIic :
      Finset.Iic i =
        Finset.cons i (Finset.Iic (i.pred hi).castSucc) (by
          simp [Fin.castSucc_pred_lt hi]) := by
    rw [Finset.Iic_eq_cons_Iio]
    congr 1
    ext j
    simp [Fin.le_castSucc_pred_iff hi]
  rw [hIic, Finset.sum_cons]
  ring

/-- Strictly positive increments produce strictly increasing cumulative event times. -/
theorem strictMono_cumulativeWaitTimes_of_pos
    {n : ℕ} {waits : Fin n → ℝ} (hWaits : ∀ i, 0 < waits i) :
    StrictMono (cumulativeWaitTimes n waits) := by
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply Fin.strictMono_iff_lt_succ.2
      intro i
      rw [cumulativeWaitTimes_eq_previous_add waits i.succ (Fin.succ_ne_zero i)]
      have hPred : (i.succ.pred (Fin.succ_ne_zero i)).castSucc = i.castSucc := by
        ext
        simp
      rw [hPred]
      linarith [hWaits i.succ]

/-- For a nonempty increment vector, the ordered event-time simplex is exactly the condition that
all increments are positive and their total remains below the horizon. The empty vector is kept
separate because its ordered-time condition is vacuous even at a zero horizon. -/
theorem cumulativeWaitTimes_mem_orderedJumpTimes_iff
    (waits : Fin (n + 1) → ℝ) (T : ℝ) :
    cumulativeWaitTimes (n + 1) waits ∈ orderedJumpTimes (n + 1) T ↔
      (∀ i, 0 < waits i) ∧ ∑ i, waits i < T := by
  constructor
  · intro hOrdered
    constructor
    · intro i
      by_cases hi : i = 0
      · subst i
        have hZero := (hOrdered.1 0).1
        rw [cumulativeWaitTimes_zero] at hZero
        exact hZero
      · have hPrevious :
            cumulativeWaitTimes (n + 1) waits (i.pred hi).castSucc <
              cumulativeWaitTimes (n + 1) waits i :=
          hOrdered.2 (Fin.castSucc_pred_lt hi)
        rw [cumulativeWaitTimes_eq_previous_add waits i hi] at hPrevious
        linarith
    · have hLast := (hOrdered.1 (Fin.last n)).2
      rw [cumulativeWaitTimes_last] at hLast
      exact hLast
  · rintro ⟨hPositive, hTotal⟩
    have hStrict : StrictMono (cumulativeWaitTimes (n + 1) waits) :=
      strictMono_cumulativeWaitTimes_of_pos hPositive
    constructor
    · intro i
      constructor
      · calc
          0 < waits 0 := hPositive 0
          _ = cumulativeWaitTimes (n + 1) waits 0 :=
            (cumulativeWaitTimes_zero waits).symm
          _ ≤ cumulativeWaitTimes (n + 1) waits i :=
            hStrict.monotone (Fin.zero_le i)
      · calc
          cumulativeWaitTimes (n + 1) waits i ≤
              cumulativeWaitTimes (n + 1) waits (Fin.last n) :=
            hStrict.monotone (Fin.le_last i)
          _ = ∑ j, waits j := cumulativeWaitTimes_last waits
          _ < T := hTotal
    · exact hStrict

/-- The cumulative-sum matrix is lower triangular. -/
theorem cumulativeWaitMatrix_blockTriangular (n : ℕ) :
    (cumulativeWaitMatrix n).BlockTriangular OrderDual.toDual := by
  intro i j h
  have hij : i < j := h
  simp [cumulativeWaitMatrix, not_le.mpr hij]

/-- The cumulative-sum matrix has determinant one in every dimension. -/
@[simp]
theorem cumulativeWaitMatrix_det (n : ℕ) :
    Matrix.det (cumulativeWaitMatrix n) = 1 := by
  rw [Matrix.det_of_isLowerTriangular
    (cumulativeWaitMatrix n) (cumulativeWaitMatrix_blockTriangular n)]
  simp [cumulativeWaitMatrix]

/-- Cumulative event times determine the waiting-time increments uniquely. -/
theorem cumulativeWaitTimes_injective (n : ℕ) :
    Function.Injective (cumulativeWaitTimes n) := by
  change Function.Injective (cumulativeWaitMatrix n).mulVec
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    cumulativeWaitMatrix_det]
  exact isUnit_one

/-- The cumulative waiting-time map is measurable. -/
@[fun_prop]
theorem measurable_cumulativeWaitTimes (n : ℕ) :
    Measurable (cumulativeWaitTimes n) :=
  (cumulativeWaitTimes n).continuous_of_finiteDimensional.measurable

/-- The determinant-one cumulative waiting-time map preserves Lebesgue measure. -/
theorem cumulativeWaitTimes_map_volume (n : ℕ) :
    Measure.map (cumulativeWaitTimes n) volume = volume := by
  unfold cumulativeWaitTimes
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi]
  · rw [cumulativeWaitMatrix_det]
    simp
  · rw [cumulativeWaitMatrix_det]
    exact one_ne_zero

/-- Restricting waiting increments to the preimage of the ordered event-time simplex and then
taking cumulative sums gives exactly restricted Lebesgue measure on that simplex. -/
theorem cumulativeWaitTimes_map_restrict_preimage_orderedJumpTimes (n : ℕ) (T : ℝ) :
    Measure.map (cumulativeWaitTimes n)
        (volume.restrict (cumulativeWaitTimes n ⁻¹' orderedJumpTimes n T)) =
      volume.restrict (orderedJumpTimes n T) := by
  calc
    Measure.map (cumulativeWaitTimes n)
        (volume.restrict (cumulativeWaitTimes n ⁻¹' orderedJumpTimes n T)) =
        (Measure.map (cumulativeWaitTimes n) volume).restrict (orderedJumpTimes n T) :=
      (Measure.restrict_map (measurable_cumulativeWaitTimes n)
        (measurableSet_orderedJumpTimes n T)).symm
    _ = volume.restrict (orderedJumpTimes n T) := by
      rw [cumulativeWaitTimes_map_volume]

/-- The initial boundary of any finite jump-time vector is zero. -/
theorem FiniteJumpHistory.boundaryTimeVector_zero
    {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    FiniteJumpHistory.boundaryTimeVector T times 0 = 0 := by
  simp [FiniteJumpHistory.boundaryTimeVector]

/-- A noninitial boundary is the corresponding jump time, except at the terminal boundary. -/
theorem FiniteJumpHistory.boundaryTimeVector_succ
    {n : ℕ} (T : ℝ) (times : Fin n → ℝ)
    (i : Fin (n + 1)) :
    FiniteJumpHistory.boundaryTimeVector T times i.succ = Fin.lastCases T times i := by
  simp [FiniteJumpHistory.boundaryTimeVector]

/-- The boundary immediately following a physical jump index is that jump time. -/
theorem FiniteJumpHistory.boundaryTimeVector_castSucc_succ {n : ℕ} (T : ℝ)
    (times : Fin n → ℝ) (i : Fin n) :
    FiniteJumpHistory.boundaryTimeVector T times i.castSucc.succ = times i := by
  rw [FiniteJumpHistory.boundaryTimeVector_succ]
  simp

/-- Before a noninitial state index, the boundary is the preceding physical jump time. -/
theorem FiniteJumpHistory.boundaryTimeVector_castSucc_castSucc {n : ℕ} (T : ℝ)
    (times : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : i ≠ 0) :
    FiniteJumpHistory.boundaryTimeVector T times i.castSucc.castSucc =
      times (i.pred hi).castSucc := by
  have hIndex : i.castSucc.castSucc = (i.pred hi).castSucc.castSucc.succ := by
    ext
    rw [Fin.val_succ]
    change i.1 = (i.pred hi).1 + 1
    rw [Fin.val_pred]
    have hiVal : i.1 ≠ 0 := by
      intro hZero
      apply hi
      ext
      exact hZero
    omega
  rw [hIndex, FiniteJumpHistory.boundaryTimeVector_succ]
  simp

/-- The final boundary of a finite jump-time vector is the observation horizon. -/
theorem FiniteJumpHistory.boundaryTimeVector_last
    {n : ℕ} (T : ℝ) (times : Fin n → ℝ) :
    FiniteJumpHistory.boundaryTimeVector T times (Fin.last (n + 1)) = T := by
  have hLast : Fin.last (n + 1) = (Fin.last n).succ := by rfl
  rw [hLast, FiniteJumpHistory.boundaryTimeVector_succ]
  simp

/-- The physical preterminal dwell vector of cumulative waiting coordinates recovers the
original waiting increments exactly. -/
@[simp]
theorem FiniteJumpHistory.dwellTimeVector_cumulativeWaitTimes_castSucc
    {n : ℕ} (T : ℝ) (waits : Fin n → ℝ) (i : Fin n) :
    FiniteJumpHistory.dwellTimeVector T (cumulativeWaitTimes n waits) i.castSucc = waits i := by
  unfold FiniteJumpHistory.dwellTimeVector
  rw [FiniteJumpHistory.boundaryTimeVector_castSucc_succ]
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hi : i = 0
      · subst i
        change cumulativeWaitTimes (n + 1) waits 0 -
          FiniteJumpHistory.boundaryTimeVector T
            (cumulativeWaitTimes (n + 1) waits) 0 = waits 0
        rw [FiniteJumpHistory.boundaryTimeVector_zero, cumulativeWaitTimes_zero]
        ring
      · rw [FiniteJumpHistory.boundaryTimeVector_castSucc_castSucc _ _ i hi]
        rw [cumulativeWaitTimes_eq_previous_add waits i hi]
        ring

/-- The terminal dwell vector of cumulative waiting coordinates is exactly the observation
horizon minus the sum of all preterminal waits. -/
@[simp]
theorem FiniteJumpHistory.dwellTimeVector_cumulativeWaitTimes_last
    {n : ℕ} (T : ℝ) (waits : Fin n → ℝ) :
    FiniteJumpHistory.dwellTimeVector T (cumulativeWaitTimes n waits) (Fin.last n) =
      T - ∑ i, waits i := by
  unfold FiniteJumpHistory.dwellTimeVector
  rw [FiniteJumpHistory.boundaryTimeVector_succ, Fin.lastCases_last]
  cases n with
  | zero =>
      have hIndex : (Fin.last 0).castSucc = (0 : Fin 2) := rfl
      rw [hIndex, FiniteJumpHistory.boundaryTimeVector_zero]
      simp
  | succ n =>
      have hIndex : (Fin.last (n + 1)).castSucc =
          (Fin.last n).castSucc.succ := by rfl
      rw [hIndex, FiniteJumpHistory.boundaryTimeVector_castSucc_succ,
        cumulativeWaitTimes_last]

end

end FiniteMarkovProcesses.Probability
