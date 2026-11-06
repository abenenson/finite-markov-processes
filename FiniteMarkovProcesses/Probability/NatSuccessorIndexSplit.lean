/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Splitting a natural total at a successor-bounded index

A total count together with an index in `Fin (total + 1)` is canonically equivalent to a pair of
natural counts: the index itself and the remaining count.  The accompanying `ENNReal` theorem
reindexes a total-count sum with a finite inner sum into an unrestricted before/after double sum.

## Main results

- `natSuccessorIndexSplitEquiv`.
- `ENNReal.tsum_nat_sum_finSucc_eq_tsum_tsum_split`.
-/

/-- Split a total natural count at one index between zero and the total, inclusive. -/
def natSuccessorIndexSplitEquiv :
    (Σ total : ℕ, Fin (total + 1)) ≃ ℕ × ℕ where
  toFun indexed := (indexed.2.val, indexed.1 - indexed.2.val)
  invFun counts := ⟨counts.1 + counts.2, ⟨counts.1, by omega⟩⟩
  left_inv indexed := by
    rcases indexed with ⟨total, index⟩
    rcases index with ⟨index, hIndex⟩
    have hIndexLe : index ≤ total := by omega
    have hTotal : index + (total - index) = total :=
      Nat.add_sub_of_le hIndexLe
    apply Sigma.ext hTotal
    apply (Fin.heq_ext_iff (congrArg (fun count ↦ count + 1) hTotal)).2
    rfl
  right_inv counts := by
    rcases counts with ⟨earlierCount, laterCount⟩
    apply Prod.ext
    · simp
    · simp

/-- Split a positive total event count at a marked event into the numbers of events strictly
before and strictly after it. -/
def natMarkedIndexSplitEquiv :
    (Σ total : ℕ, Fin total) ≃ ℕ × ℕ where
  toFun indexed :=
    (indexed.2.val, indexed.1 - (indexed.2.val + 1))
  invFun counts :=
    ⟨counts.1 + 1 + counts.2, ⟨counts.1, by omega⟩⟩
  left_inv indexed := by
    rcases indexed with ⟨total, index⟩
    rcases index with ⟨index, hIndex⟩
    have hIndexSuccLe : index + 1 ≤ total := by omega
    have hTotal : index + 1 + (total - (index + 1)) = total :=
      Nat.add_sub_of_le hIndexSuccLe
    apply Sigma.ext hTotal
    apply (Fin.heq_ext_iff hTotal).2
    rfl
  right_inv counts := by
    rcases counts with ⟨earlierCount, laterCount⟩
    apply Prod.ext
    · rfl
    · simp

namespace ENNReal

/-- Reindex a total-count sum with a finite cut-position sum into unrestricted before/after
counts. -/
theorem tsum_nat_sum_finSucc_eq_tsum_tsum_split
    (summand : (total : ℕ) → Fin (total + 1) → ℝ≥0∞) :
    (∑' total : ℕ, ∑ index : Fin (total + 1), summand total index) =
      ∑' earlierCount : ℕ, ∑' laterCount : ℕ,
        summand (earlierCount + laterCount)
          ⟨earlierCount, by omega⟩ := by
  calc
    (∑' total : ℕ, ∑ index : Fin (total + 1), summand total index) =
        ∑' total : ℕ, ∑' index : Fin (total + 1),
          summand total index := by
      simp_rw [tsum_fintype]
    _ = ∑' indexed : Σ total : ℕ, Fin (total + 1),
        summand indexed.1 indexed.2 := by
      rw [ENNReal.tsum_sigma]
    _ = ∑' counts : ℕ × ℕ,
        summand (counts.1 + counts.2) ⟨counts.1, by omega⟩ := by
      rw [← natSuccessorIndexSplitEquiv.symm.tsum_eq]
      apply tsum_congr
      intro counts
      rfl
    _ = ∑' earlierCount : ℕ, ∑' laterCount : ℕ,
        summand (earlierCount + laterCount)
          ⟨earlierCount, by omega⟩ := by
      rw [ENNReal.tsum_prod']

/-- Reindex a total-count sum over actual event positions into the number of events before and
after the marked event. -/
theorem tsum_nat_sum_fin_eq_tsum_tsum_marked
    (summand : (total : ℕ) → Fin total → ℝ≥0∞) :
    (∑' total : ℕ, ∑ index : Fin total, summand total index) =
      ∑' earlierCount : ℕ, ∑' laterCount : ℕ,
        summand (earlierCount + 1 + laterCount)
          ⟨earlierCount, by omega⟩ := by
  calc
    (∑' total : ℕ, ∑ index : Fin total, summand total index) =
        ∑' total : ℕ, ∑' index : Fin total, summand total index := by
      simp_rw [tsum_fintype]
    _ = ∑' indexed : Σ total : ℕ, Fin total,
        summand indexed.1 indexed.2 := by
      rw [ENNReal.tsum_sigma]
    _ = ∑' counts : ℕ × ℕ,
        summand (counts.1 + 1 + counts.2) ⟨counts.1, by omega⟩ := by
      rw [← natMarkedIndexSplitEquiv.symm.tsum_eq]
      apply tsum_congr
      intro counts
      rfl
    _ = ∑' earlierCount : ℕ, ∑' laterCount : ℕ,
        summand (earlierCount + 1 + laterCount)
          ⟨earlierCount, by omega⟩ := by
      rw [ENNReal.tsum_prod']

end ENNReal
