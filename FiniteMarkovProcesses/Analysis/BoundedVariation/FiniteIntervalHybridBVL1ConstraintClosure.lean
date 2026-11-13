/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath

/-!
# Strong-L1 constraint closure for hybrid bounded-variation paths

This module exposes the reusable almost-everywhere subsequence mechanism behind closure of
pointwise constraints on finite-interval hybrid-BV paths.  Strong `L1` convergence gives a
subsequence of the selected representatives converging almost everywhere to the selected
representative of the limit path.

Derivative-measure constraints and boundary traces are deliberately outside this module.

## Main result

* `exists_subsequence_tendsto_cadlagRepresentative_ae_of_tendsto_toL1Path` recovers pointwise
  almost-everywhere convergence along a strictly monotone subsequence.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Strong-`L1` convergence of hybrid paths admits a strictly monotone subsequence whose selected
càdlàg representatives converge almost everywhere to the selected representative of the limit. -/
theorem exists_subsequence_tendsto_cadlagRepresentative_ae_of_tendsto_toL1Path
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limitPath : FiniteIntervalHybridBVPath Coordinate duration)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limitPath.toDerivativePath.toL1Path)) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∀ᵐ time ∂finiteOpenIntervalVolume duration,
        Tendsto
          (fun sequenceIndex =>
            (paths (subsequence sequenceIndex)).cadlagRepresentative.representative time)
          atTop
          (nhds (limitPath.cadlagRepresentative.representative time)) := by
  let representative : ℕ → ℝ → FiniteCoordinateL1Value Coordinate :=
    fun sequenceIndex => (paths sequenceIndex).cadlagRepresentative.representative
  have hRepresentativeEventually (sequenceIndex : ℕ) :
      representative sequenceIndex =ᵐ[finiteOpenIntervalVolume duration]
        (paths sequenceIndex).toDerivativePath.toL1Path := by
    obtain ⟨hMemLp, hQuotient⟩ :=
      (paths sequenceIndex).cadlagRepresentative.represents
    exact (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (paths sequenceIndex).toDerivativePath.toL1Path
      (representative sequenceIndex) hMemLp).mp ⟨hMemLp, hQuotient⟩
  have hInMeasure : TendstoInMeasure (finiteOpenIntervalVolume duration)
      representative atTop limitPath.toDerivativePath.toL1Path := by
    exact (tendstoInMeasure_of_tendsto_Lp hTendsto).congr_left
      (fun sequenceIndex => (hRepresentativeEventually sequenceIndex).symm)
  obtain ⟨subsequence, hSubsequenceMonotone, hSubsequenceTendsto⟩ :=
    hInMeasure.exists_seq_tendsto_ae
  have hLimitRepresentativeEventually :
      limitPath.cadlagRepresentative.representative
        =ᵐ[finiteOpenIntervalVolume duration] limitPath.toDerivativePath.toL1Path := by
    obtain ⟨hMemLp, hQuotient⟩ := limitPath.cadlagRepresentative.represents
    exact (FiniteIntervalL1Path.represents_iff_eventuallyEq
      limitPath.toDerivativePath.toL1Path
      limitPath.cadlagRepresentative.representative hMemLp).mp ⟨hMemLp, hQuotient⟩
  refine ⟨subsequence, hSubsequenceMonotone, ?_⟩
  filter_upwards [hSubsequenceTendsto, hLimitRepresentativeEventually] with
    time hTimeTendsto hTimeLimit
  simpa only [representative, hTimeLimit] using hTimeTendsto

end

end FiniteMarkovProcesses
