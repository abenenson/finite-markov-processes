/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVCompactness

/-!
# Sequential compactness for finite-interval hybrid bounded-variation paths

This module composes the strong-`L1` compactness and finite-mesh derivative-test machinery into
the sequential HPR compactness upgrade used by dynamic-rate sublevels.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

universe u

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- A strong-`L1` convergent sequence with one finite uniform derivative-variation budget admits
a subsequence converging in the full strong-`L1` plus open-interval vague-derivative topology to
a genuine hybrid BV path over the same `L1` limit.  This is the sequential HPR compactness
upgrade needed by finite-interval dynamic-rate sublevels. -/
theorem exists_subsequence_tendsto_hybrid_of_tendsto_toL1Path_of_uniformVariation
    (hDuration : 0 < duration)
    (paths : ℕ → FiniteIntervalHybridBVPath Coordinate duration)
    (limit : FiniteIntervalL1Path Coordinate duration)
    {variationBound : ENNReal} (hVariationBound : variationBound < ∞)
    (hPaths : ∀ sequenceIndex,
      finiteIntervalHybridBVDerivativeTotalVariation (paths sequenceIndex) ≤ variationBound)
    (hTendsto : Tendsto
      (fun sequenceIndex => (paths sequenceIndex).toDerivativePath.toL1Path)
      atTop (nhds limit)) :
    ∃ (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∃ limitPath : FiniteIntervalHybridBVPath Coordinate duration,
        limitPath.toDerivativePath.toL1Path = limit ∧
        Tendsto (fun sequenceIndex => paths (subsequence sequenceIndex))
          atTop (nhds limitPath) := by
  have hLimitVariation :=
    hasBoundedVariation_of_tendsto_toL1Path_of_uniform_derivativeVariation
      hDuration paths limit hVariationBound hPaths hTendsto
  obtain ⟨limitPath, hLimitPath⟩ :=
    FiniteIntervalHybridBVPath.exists_with_toL1Path_eq
      limit hDuration hLimitVariation
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
      representative atTop limit := by
    exact (tendstoInMeasure_of_tendsto_Lp hTendsto).congr_left
      (fun sequenceIndex => (hRepresentativeEventually sequenceIndex).symm)
  obtain ⟨subsequence, hSubsequenceMonotone, hSubsequenceTendsto⟩ :=
    hInMeasure.exists_seq_tendsto_ae
  have hLimitRepresentativeEventually :
      limitPath.cadlagRepresentative.representative
        =ᵐ[finiteOpenIntervalVolume duration] limit := by
    obtain ⟨hMemLp, hQuotient⟩ := limitPath.cadlagRepresentative.represents
    have hEventually := (FiniteIntervalL1Path.represents_iff_eventuallyEq
      limitPath.toDerivativePath.toL1Path
      limitPath.cadlagRepresentative.representative hMemLp).mp
        ⟨hMemLp, hQuotient⟩
    simpa only [hLimitPath] using hEventually
  let goodSet : Set ℝ :=
    {time |
      Tendsto (fun sequenceIndex => representative (subsequence sequenceIndex) time)
        atTop (nhds (limit time)) ∧
      limitPath.cadlagRepresentative.representative time = limit time}
  have hGoodEventually : ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      time ∈ goodSet := by
    filter_upwards [hSubsequenceTendsto, hLimitRepresentativeEventually] with
      time hTimeTendsto hTimeLimit
    exact ⟨hTimeTendsto, hTimeLimit⟩
  have hGoodImplication : ∀ᵐ time ∂volume,
      time ∈ Set.Ioo 0 duration → time ∈ goodSet := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    simpa only [finiteOpenIntervalVolume] using hGoodEventually
  have hGoodDense : Dense
      {time | time ∈ Set.Ioo 0 duration → time ∈ goodSet} :=
    volume.dense_of_ae hGoodImplication
  have hVariation (sequenceIndex : ℕ) :
      finiteIntervalHybridBVDerivativeTotalVariation
          (paths (subsequence sequenceIndex)) < ∞ ∧
        (finiteIntervalHybridBVDerivativeTotalVariation
          (paths (subsequence sequenceIndex))).toReal ≤ variationBound.toReal := by
    have hBound := hPaths (subsequence sequenceIndex)
    exact ⟨hBound.trans_lt hVariationBound,
      ENNReal.toReal_mono hVariationBound.ne hBound⟩
  refine ⟨subsequence, hSubsequenceMonotone, limitPath, hLimitPath, ?_⟩
  apply FiniteIntervalHybridBVPath.tendsto_iff.mpr
  constructor
  · simpa only [hLimitPath, Function.comp_def] using
      hTendsto.comp hSubsequenceMonotone.tendsto_atTop
  · intro coordinate test
    apply tendsto_derivativeTestIntegral_of_uniformVariation_of_tendsto_on_dense
      hDuration (fun sequenceIndex => paths (subsequence sequenceIndex)) limitPath
        coordinate test goodSet hGoodDense
    · intro time hTime
      have hTimeTendsto := hTime.1
      have hTimeLimit := hTime.2
      have hCoordinateTendsto :=
        (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).continuous
          |>.continuousAt.tendsto.comp hTimeTendsto
      simpa only [representative, Function.comp_def, PiLp.proj_apply, hTimeLimit] using
        hCoordinateTendsto
    · exact (ENNReal.toReal_nonneg : 0 ≤ variationBound.toReal)
    · exact hVariation

end

end FiniteMarkovProcesses
