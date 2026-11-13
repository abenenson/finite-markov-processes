/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVSequentialCompactness
public import
  FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVVariationSublevels
public import Mathlib.Topology.Sequences

/-!
# Compact hybrid-BV containers for uniform quantitative envelopes

The strong-`L1` projection of a finite uniform `L1`/derivative-variation envelope has compact
closure.  This module proves that every projected closure point has a unique hybrid-BV lift with
the same variation budget.  The lift is sequentially continuous by the existing uniform-
variation hybrid subsequence theorem, and that sequential result is upgraded to continuity only
on the metric projected-closure subtype.

Compactness is then transported back to the published hybrid topology.  The construction is
admissibility-free: it imposes no absolute continuity, continuity equation, positivity, or
boundary-trace condition.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter Set
open scoped ENNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Compact strong-`L1` closure of the projection of one uniform quantitative hybrid envelope. -/
noncomputable def finiteIntervalHybridBVUniformEnvelopeProjectedClosure
    (l1Bound variationBound : ENNReal) :
    Set (FiniteIntervalL1Path Coordinate duration) :=
  closure
    ((fun path : FiniteIntervalHybridBVPath Coordinate duration =>
        path.toDerivativePath.toL1Path) ''
      finiteIntervalHybridBVUniformL1VariationEnvelope l1Bound variationBound)

/-- Every point in the compact projected closure has a hybrid-BV lift retaining the original
derivative-variation budget. -/
theorem exists_hybridLift_of_mem_uniformEnvelopeProjectedClosure
    (hDuration : 0 < duration) {l1Bound variationBound : ENNReal}
    (hVariationBound : variationBound < ∞)
    {projectedPath : FiniteIntervalL1Path Coordinate duration}
    (hProjectedPath : projectedPath ∈
      finiteIntervalHybridBVUniformEnvelopeProjectedClosure
        l1Bound variationBound) :
    ∃ path : FiniteIntervalHybridBVPath Coordinate duration,
      path.toDerivativePath.toL1Path = projectedPath ∧
        finiteIntervalHybridBVDerivativeTotalVariation path ≤ variationBound := by
  rw [finiteIntervalHybridBVUniformEnvelopeProjectedClosure,
    mem_closure_iff_seq_limit] at hProjectedPath
  obtain ⟨projectedPaths, hProjectedPaths, hProjectedTendsto⟩ := hProjectedPath
  choose paths hPathsEnvelope hPathsProjection using hProjectedPaths
  have hPathsVariation (sequenceIndex : ℕ) :
      finiteIntervalHybridBVDerivativeTotalVariation (paths sequenceIndex) ≤
        variationBound :=
    (mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff.mp
      (hPathsEnvelope sequenceIndex)).2
  have hPathsTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds projectedPath) := by
    simpa only [hPathsProjection] using hProjectedTendsto
  obtain ⟨subsequence, _hSubsequenceMonotone, hybridLimit,
      hHybridLimitProjection, hHybridTendsto⟩ :=
    exists_subsequence_tendsto_hybrid_of_tendsto_toL1Path_of_uniformVariation
      hDuration paths projectedPath hVariationBound hPathsVariation hPathsTendsto
  have hHybridLimitVariation :
      finiteIntervalHybridBVDerivativeTotalVariation hybridLimit ≤ variationBound := by
    have hClosed :=
      (lowerSemicontinuous_finiteIntervalHybridBVDerivativeTotalVariation
        (Coordinate := Coordinate) hDuration).isClosed_preimage variationBound
    exact hClosed.mem_of_tendsto hHybridTendsto <|
      Eventually.of_forall fun sequenceIndex =>
        hPathsVariation (subsequence sequenceIndex)
  exact ⟨hybridLimit, hHybridLimitProjection, hHybridLimitVariation⟩

/-- Hybrid paths whose strong-`L1` projections lie in the compact projected closure.  The theorem
below proves that this preimage is compact despite compact preimages not being compact in
general: derivative uniqueness supplies a continuous inverse on the metric closure subtype. -/
noncomputable def finiteIntervalHybridBVUniformL1VariationCompactContainer
    (l1Bound variationBound : ENNReal) :
    Set (FiniteIntervalHybridBVPath Coordinate duration) :=
  {path | path.toDerivativePath.toL1Path ∈
    finiteIntervalHybridBVUniformEnvelopeProjectedClosure l1Bound variationBound}

/-- Projected closure points as a metric subtype. -/
abbrev FiniteIntervalHybridBVUniformEnvelopeProjectedPath
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ)
    (l1Bound variationBound : ENNReal) :=
  finiteIntervalHybridBVUniformEnvelopeProjectedClosure
    (Coordinate := Coordinate) (duration := duration) l1Bound variationBound

/-- Hybrid paths in the compact uniform-envelope container. -/
abbrev FiniteIntervalHybridBVUniformL1VariationCompactPath
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ)
    (l1Bound variationBound : ENNReal) :=
  finiteIntervalHybridBVUniformL1VariationCompactContainer
    (Coordinate := Coordinate) (duration := duration) l1Bound variationBound

/-- The unique hybrid lift of a point in the compact projected closure. -/
noncomputable def finiteIntervalHybridBVUniformEnvelopeL1Inverse
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞)
    (projectedPath : FiniteIntervalHybridBVUniformEnvelopeProjectedPath
      Coordinate duration l1Bound variationBound) :
    FiniteIntervalHybridBVUniformL1VariationCompactPath
      Coordinate duration l1Bound variationBound := by
  let path := Classical.choose
    (exists_hybridLift_of_mem_uniformEnvelopeProjectedClosure
      hDuration hVariationBound projectedPath.2)
  refine ⟨path, ?_⟩
  change path.toDerivativePath.toL1Path ∈
    finiteIntervalHybridBVUniformEnvelopeProjectedClosure l1Bound variationBound
  rw [(Classical.choose_spec
    (exists_hybridLift_of_mem_uniformEnvelopeProjectedClosure
      hDuration hVariationBound projectedPath.2)).1]
  exact projectedPath.2

/-- Projecting the canonical hybrid lift recovers the supplied strong-`L1` path. -/
@[simp]
theorem finiteIntervalHybridBVUniformEnvelopeL1Inverse_projection
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞)
    (projectedPath : FiniteIntervalHybridBVUniformEnvelopeProjectedPath
      Coordinate duration l1Bound variationBound) :
    (finiteIntervalHybridBVUniformEnvelopeL1Inverse
      hDuration l1Bound variationBound hVariationBound projectedPath).1.toDerivativePath.toL1Path =
        projectedPath.1 :=
  (Classical.choose_spec
    (exists_hybridLift_of_mem_uniformEnvelopeProjectedClosure
      hDuration hVariationBound projectedPath.2)).1

/-- The canonical hybrid lift retains the uniform derivative-variation budget. -/
theorem finiteIntervalHybridBVUniformEnvelopeL1Inverse_variation_le
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞)
    (projectedPath : FiniteIntervalHybridBVUniformEnvelopeProjectedPath
      Coordinate duration l1Bound variationBound) :
    finiteIntervalHybridBVDerivativeTotalVariation
        (finiteIntervalHybridBVUniformEnvelopeL1Inverse
          hDuration l1Bound variationBound hVariationBound projectedPath).1 ≤
      variationBound :=
  (Classical.choose_spec
    (exists_hybridLift_of_mem_uniformEnvelopeProjectedClosure
      hDuration hVariationBound projectedPath.2)).2

/-- Every path in the uniform compact container is the canonical lift of its strong-`L1`
projection. -/
theorem finiteIntervalHybridBVUniformEnvelopeL1Inverse_surjective
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞) :
    Function.Surjective
      (finiteIntervalHybridBVUniformEnvelopeL1Inverse
        (Coordinate := Coordinate) hDuration l1Bound variationBound hVariationBound) := by
  intro path
  let projectedPath : FiniteIntervalHybridBVUniformEnvelopeProjectedPath
      Coordinate duration l1Bound variationBound :=
    ⟨path.1.toDerivativePath.toL1Path, path.2⟩
  refine ⟨projectedPath, Subtype.ext ?_⟩
  apply FiniteIntervalHybridBVPath.injective_toL1Path
  exact finiteIntervalHybridBVUniformEnvelopeL1Inverse_projection
    hDuration l1Bound variationBound hVariationBound projectedPath

/-- The unique hybrid lift is sequentially continuous on the compact projected closure.  Every
subsequence has a further hybrid-convergent subsequence, and derivative uniqueness identifies
its limit with the lift of the projected limit. -/
theorem seqContinuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞) :
    SeqContinuous
      (finiteIntervalHybridBVUniformEnvelopeL1Inverse
        (Coordinate := Coordinate) hDuration l1Bound variationBound hVariationBound) := by
  intro projectedPaths projectedLimit hProjectedTendsto
  apply tendsto_of_subseq_tendsto
  intro indices hIndices
  let hybridPaths : ℕ →
      FiniteIntervalHybridBVUniformL1VariationCompactPath
        Coordinate duration l1Bound variationBound :=
    fun sequenceIndex =>
      finiteIntervalHybridBVUniformEnvelopeL1Inverse
        hDuration l1Bound variationBound hVariationBound
          (projectedPaths (indices sequenceIndex))
  have hHybridPathsVariation (sequenceIndex : ℕ) :
      finiteIntervalHybridBVDerivativeTotalVariation (hybridPaths sequenceIndex).1 ≤
        variationBound :=
    finiteIntervalHybridBVUniformEnvelopeL1Inverse_variation_le
      hDuration l1Bound variationBound hVariationBound _
  have hHybridPathsL1Tendsto : Tendsto
      (fun sequenceIndex =>
        (hybridPaths sequenceIndex).1.toDerivativePath.toL1Path)
      atTop (nhds projectedLimit.1) := by
    have hProjectedSubsequenceTendsto :=
      tendsto_subtype_rng.mp (hProjectedTendsto.comp hIndices)
    simpa only [hybridPaths, Function.comp_def,
      finiteIntervalHybridBVUniformEnvelopeL1Inverse_projection] using
        hProjectedSubsequenceTendsto
  obtain ⟨subsequence, _hSubsequenceMonotone, hybridLimit,
      hHybridLimitProjection, hHybridTendsto⟩ :=
    exists_subsequence_tendsto_hybrid_of_tendsto_toL1Path_of_uniformVariation
      hDuration (fun sequenceIndex => (hybridPaths sequenceIndex).1)
        projectedLimit.1 hVariationBound hHybridPathsVariation hHybridPathsL1Tendsto
  have hHybridLimit :
      hybridLimit =
        (finiteIntervalHybridBVUniformEnvelopeL1Inverse
          hDuration l1Bound variationBound hVariationBound projectedLimit).1 := by
    apply FiniteIntervalHybridBVPath.injective_toL1Path
    change hybridLimit.toDerivativePath.toL1Path =
      ((finiteIntervalHybridBVUniformEnvelopeL1Inverse
        hDuration l1Bound variationBound
          hVariationBound projectedLimit).1).toDerivativePath.toL1Path
    rw [hHybridLimitProjection,
      finiteIntervalHybridBVUniformEnvelopeL1Inverse_projection]
  refine ⟨subsequence, ?_⟩
  rw [tendsto_subtype_rng]
  simpa only [Function.comp_apply, hybridPaths, hHybridLimit] using hHybridTendsto

/-- The unique hybrid lift is continuous.  Sequential-to-topological conversion is used only on
the metric strong-`L1` projected-closure subtype, never on the ambient hybrid carrier. -/
theorem continuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
    (hDuration : 0 < duration) (l1Bound variationBound : ENNReal)
    (hVariationBound : variationBound < ∞) :
    Continuous
      (finiteIntervalHybridBVUniformEnvelopeL1Inverse
        (Coordinate := Coordinate) hDuration l1Bound variationBound hVariationBound) :=
  continuous_iff_seqContinuous.mpr
    (seqContinuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
      hDuration l1Bound variationBound hVariationBound)

/-- Every finite uniform quantitative envelope lies in its hybrid compact container. -/
theorem finiteIntervalHybridBVUniformL1VariationEnvelope_subset_compactContainer
    (l1Bound variationBound : ENNReal) :
    finiteIntervalHybridBVUniformL1VariationEnvelope
        (Coordinate := Coordinate) (duration := duration) l1Bound variationBound ⊆
      finiteIntervalHybridBVUniformL1VariationCompactContainer
        l1Bound variationBound := by
  intro path hPath
  apply subset_closure
  exact ⟨path, hPath, rfl⟩

/-- The admissibility-free uniform `L1`/derivative-variation envelope lies in one compact set in
the published hybrid topology. -/
theorem isCompact_finiteIntervalHybridBVUniformL1VariationCompactContainer
    [DecidableEq Coordinate]
    (hDuration : 0 < duration) {l1Bound variationBound : ENNReal}
    (hL1Bound : l1Bound < ∞) (hVariationBound : variationBound < ∞) :
    IsCompact
      (finiteIntervalHybridBVUniformL1VariationCompactContainer
        (Coordinate := Coordinate) (duration := duration) l1Bound variationBound) := by
  rw [isCompact_iff_compactSpace]
  let : CompactSpace
      (FiniteIntervalHybridBVUniformEnvelopeProjectedPath
        Coordinate duration l1Bound variationBound) :=
    isCompact_iff_compactSpace.mp
      (isCompact_closure_toL1Path_image_uniformL1VariationEnvelope
        hDuration hL1Bound hVariationBound)
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr <|
    finiteIntervalHybridBVUniformEnvelopeL1Inverse_surjective
      hDuration l1Bound variationBound hVariationBound]
  simpa only [image_univ] using
    isCompact_univ.image
      (continuous_finiteIntervalHybridBVUniformEnvelopeL1Inverse
        hDuration l1Bound variationBound hVariationBound)

end

end FiniteMarkovProcesses
