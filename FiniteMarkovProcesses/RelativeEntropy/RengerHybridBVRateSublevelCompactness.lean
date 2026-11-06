/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVSequentialCompactness
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVOrderedFlowMeasureClosure
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateCoercivity
import Mathlib.Topology.Sequences

/-!
# Compact rate sublevels for the Renger hybrid-BV action

This module upgrades the existing sequential HPR compactness machinery without changing the
published hybrid topology.  It first projects a genuinely finite dynamic-rate sublevel through
the continuous injective strong-`L1` path map.  Metric closure sequences in that projection lift
to uniformly coercive hybrid paths; the existing hybrid subsequence theorem, bounded-rate
admissible-limit closure, and scoped dual lower semicontinuity then close the projected sublevel.

No first-countability or metrizability instance is asserted for the ambient uncountable-test
hybrid carrier.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter _root_.FiniteMarkovProcesses.MeasureTheory Set
open scoped ENNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Uniform complete-derivative variation budget supplied by one finite dynamic-rate sublevel. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateVariationBound
    (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (level : ENNReal) : ENNReal :=
  3 * (level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
    ENNReal.ofReal duration)

/-- Uniform strong-`L1` budget supplied by one finite dynamic-rate sublevel. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateL1Bound
    (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) (level : ENNReal) : ENNReal :=
  (1 + (level + rengerDirectionalFlowHybridBVGeneratorCorrection generator *
    ENNReal.ofReal duration)) * ENNReal.ofReal duration

/-- A genuinely finite level gives a genuinely finite complete-variation budget. -/
theorem rengerDirectionalFlowHybridBVFiniteRateVariationBound_lt_top
    (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateVariationBound generator duration level < ∞ := by
  rw [lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top (by norm_num) <|
    ENNReal.add_ne_top.mpr
      ⟨hLevel.ne,
        ENNReal.mul_ne_top
          (rengerDirectionalFlowHybridBVGeneratorCorrection_ne_top generator)
          ENNReal.ofReal_ne_top⟩

/-- A genuinely finite level gives a genuinely finite strong-`L1` budget. -/
theorem rengerDirectionalFlowHybridBVFiniteRateL1Bound_lt_top
    (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateL1Bound generator duration level < ∞ := by
  rw [lt_top_iff_ne_top]
  apply ENNReal.mul_ne_top
  · exact ENNReal.add_ne_top.mpr
      ⟨by norm_num,
        ENNReal.add_ne_top.mpr
          ⟨hLevel.ne,
            ENNReal.mul_ne_top
              (rengerDirectionalFlowHybridBVGeneratorCorrection_ne_top generator)
              ENNReal.ofReal_ne_top⟩⟩
  · exact ENNReal.ofReal_ne_top

/-- Strong-`L1` projection of one exact ambient dynamic-rate sublevel. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :
    Set (FiniteIntervalL1Path
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  (fun path : RengerDirectionalFlowHybridBVPath State duration =>
      path.toDerivativePath.toL1Path) ''
    rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level

/-- One hybrid path together with membership in a fixed dynamic-rate sublevel. -/
abbrev RengerDirectionalFlowHybridBVFiniteRateSublevelPath
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :=
  rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level

/-- One strong-`L1` path together with membership in the projected dynamic-rate sublevel. -/
abbrev RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :=
  rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image generator hDuration level

/-- The unique hybrid-BV lift of a projected finite-rate path. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
      generator hDuration level) :
    RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level :=
  ⟨Classical.choose path.2, (Classical.choose_spec path.2).1⟩

/-- Projecting the canonical finite-rate lift recovers the supplied strong-`L1` path. -/
@[simp]
theorem rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
      generator hDuration level) :
    (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
      generator hDuration level path).1.toDerivativePath.toL1Path = path.1 :=
  (Classical.choose_spec path.2).2

/-- Every path in the finite-rate sublevel is the canonical lift of its strong-`L1` projection. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_surjective
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :
    Function.Surjective
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level) := by
  intro path
  let projectedPath :
      RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
        generator hDuration level :=
    ⟨path.1.toDerivativePath.toL1Path, ⟨path.1, path.2, rfl⟩⟩
  refine ⟨projectedPath, Subtype.ext ?_⟩
  apply FiniteIntervalHybridBVPath.injective_toL1Path
  exact rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection
    generator hDuration level projectedPath

/-- Strong-`L1` projection from a finite-rate hybrid sublevel to its exact image. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level) :
    RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
      generator hDuration level :=
  ⟨path.1.toDerivativePath.toL1Path, ⟨path.1, path.2, rfl⟩⟩

/-- The finite-rate strong-`L1` projection is continuous. -/
theorem continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal) :
    Continuous
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
        generator hDuration level) := by
  exact
    ((FiniteIntervalHybridBVPath.continuous_toL1Path
      (Coordinate := EmpiricalDensityDirectionalFlowCoordinate State)
      (duration := duration)).comp continuous_subtype_val).subtype_mk _

/-- Initial hybrid trace recovered from a path in the projected finite-rate sublevel. -/
noncomputable def rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
      generator hDuration level) :
    FiniteCoordinateL1Value (EmpiricalDensityDirectionalFlowCoordinate State) :=
  (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
    generator hDuration level path).1.initialTrace

/-- The projected finite-rate initial trace is sequentially continuous in strong `L1`. -/
theorem seqContinuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    SeqContinuous
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
        generator hDuration level) := by
  intro projectedPaths projectedLimit hProjectedTendsto
  let paths : ℕ → RengerDirectionalFlowHybridBVPath State duration :=
    fun sequenceIndex =>
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level (projectedPaths sequenceIndex)).1
  let limitPath : RengerDirectionalFlowHybridBVPath State duration :=
    (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
      generator hDuration level projectedLimit).1
  apply
    rengerDirectionalFlowHybridBVTendstoInitialTraceOfTendstoToL1PathOfUniformlyBoundedDynamicRate
      generator hDuration paths limitPath
  · intro sequenceIndex
    exact
      (rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet
        generator hDuration hLevel
          (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
            generator hDuration level (projectedPaths sequenceIndex)).2).1
  · exact hLevel.ne
  · intro sequenceIndex
    exact
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level (projectedPaths sequenceIndex)).2
  · have hProjectedUnderlyingTendsto := tendsto_subtype_rng.mp hProjectedTendsto
    simpa only [paths, limitPath,
      rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection] using
        hProjectedUnderlyingTendsto

/-- The projected finite-rate initial trace is continuous in strong `L1`. -/
theorem continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    Continuous
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
        generator hDuration level) :=
  continuous_iff_seqContinuous.mpr
    (seqContinuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
      generator hDuration hLevel)

/-- Lift and projection preserve the initial trace of every finite-rate path. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace_projection
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) (level : ENNReal)
    (path : RengerDirectionalFlowHybridBVFiniteRateSublevelPath
      generator hDuration level) :
    rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
        generator hDuration level
        (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
          generator hDuration level path) =
      path.1.initialTrace := by
  have hPath :
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level
          (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
            generator hDuration level path)).1 = path.1 := by
    apply FiniteIntervalHybridBVPath.injective_toL1Path
    change
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level
          (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
            generator hDuration level path)).1.toDerivativePath.toL1Path =
        path.1.toDerivativePath.toL1Path
    rw [rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection]
    rfl
  exact congrArg FiniteIntervalHybridBVPath.initialTrace hPath

/-- The separately recovered initial trace is continuous on every finite dynamic-rate
sublevel. -/
theorem continuous_rengerDirectionalFlowHybridBVInitialTrace_on_finiteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    Continuous fun path :
        RengerDirectionalFlowHybridBVFiniteRateSublevelPath
          generator hDuration level =>
      path.1.initialTrace := by
  convert
    (continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace
      generator hDuration hLevel).comp
      (continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Projection
        generator hDuration level) using 1
  funext path
  exact
    (rengerDirectionalFlowHybridBVFiniteRateSublevelL1InitialTrace_projection
      generator hDuration level path).symm

/-- Every genuinely finite rate sublevel enters its explicit uniform strong-`L1` and complete-
variation envelope. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_explicitEnvelope
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level ⊆
      finiteIntervalHybridBVUniformL1VariationEnvelope
        (rengerDirectionalFlowHybridBVFiniteRateL1Bound generator duration level)
        (rengerDirectionalFlowHybridBVFiniteRateVariationBound generator duration level) := by
  simpa only [rengerDirectionalFlowHybridBVFiniteRateL1Bound,
    rengerDirectionalFlowHybridBVFiniteRateVariationBound] using
      rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_uniformL1VariationEnvelope
        generator hDuration hLevel

/-- The strong-`L1` projection of every genuinely finite dynamic-rate sublevel is closed.  The
proof uses first countability only in the metric `L1` carrier. -/
theorem isClosed_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    IsClosed
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
        generator hDuration level) := by
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm
  · intro limitPath hLimitPath
    rw [mem_closure_iff_seq_limit] at hLimitPath
    obtain ⟨projectedPaths, hProjectedPaths, hProjectedTendsto⟩ := hLimitPath
    choose paths hPathsRate hPathsProjection using hProjectedPaths
    have hPathsAdmissible : ∀ sequenceIndex,
        RengerDirectionalFlowHybridBVAdmissible (paths sequenceIndex) hDuration := by
      intro sequenceIndex
      exact
        (rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_finiteRateCoerciveSet
          generator hDuration hLevel (hPathsRate sequenceIndex)).1
    have hPathsVariation : ∀ sequenceIndex,
        finiteIntervalHybridBVDerivativeTotalVariation (paths sequenceIndex) ≤
          rengerDirectionalFlowHybridBVFiniteRateVariationBound
            generator duration level := by
      intro sequenceIndex
      exact
        (mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff.mp <|
          rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_explicitEnvelope
            generator hDuration hLevel (hPathsRate sequenceIndex)).2
    have hPathsTendsto : Tendsto
        (fun sequenceIndex =>
          (paths sequenceIndex).toDerivativePath.toL1Path)
        atTop (nhds limitPath) := by
      simpa only [hPathsProjection] using hProjectedTendsto
    obtain ⟨subsequence, _hSubsequenceMonotone, hybridLimit,
        hHybridLimitProjection, hHybridTendsto⟩ :=
      exists_subsequence_tendsto_hybrid_of_tendsto_toL1Path_of_uniformVariation
        hDuration paths limitPath
          (rengerDirectionalFlowHybridBVFiniteRateVariationBound_lt_top
            generator duration hLevel)
          hPathsVariation hPathsTendsto
    have hHybridLimitAdmissible :
        RengerDirectionalFlowHybridBVAdmissible hybridLimit hDuration :=
      rengerDirectionalFlowHybridBVAdmissibleOfTendstoOfUniformlyBoundedDynamicRate
        generator hDuration (fun sequenceIndex => paths (subsequence sequenceIndex))
          hybridLimit (fun sequenceIndex => hPathsAdmissible (subsequence sequenceIndex))
          hLevel.ne (fun sequenceIndex => hPathsRate (subsequence sequenceIndex))
          hHybridTendsto
    let representationPaths : ℕ →
        RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
      fun sequenceIndex =>
        ⟨paths (subsequence sequenceIndex),
          hPathsAdmissible (subsequence sequenceIndex)⟩
    let representationLimit :
        RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration :=
      ⟨hybridLimit, hHybridLimitAdmissible⟩
    have hRepresentationTendsto : Tendsto representationPaths atTop
        (nhds representationLimit) := by
      rw [tendsto_subtype_rng]
      exact hHybridTendsto
    have hHybridLimitRate :
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration hybridLimit ≤ level := by
      have hClosed :=
        (lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate_on_representationDomain
          generator hDuration).isClosed_preimage level
      have hRepresentationLimitMem := hClosed.mem_of_tendsto hRepresentationTendsto <|
        Eventually.of_forall fun sequenceIndex => hPathsRate (subsequence sequenceIndex)
      exact hRepresentationLimitMem
    exact ⟨hybridLimit, hHybridLimitRate, hHybridLimitProjection⟩
  · exact subset_closure

/-- The projected finite-rate sublevel lies in the compact strong-`L1` closure of its explicit
coercive envelope. -/
theorem rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image_subset_compactEnvelope
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image generator hDuration level ⊆
      closure
        ((fun path : RengerDirectionalFlowHybridBVPath State duration =>
            path.toDerivativePath.toL1Path) ''
          finiteIntervalHybridBVUniformL1VariationEnvelope
            (rengerDirectionalFlowHybridBVFiniteRateL1Bound generator duration level)
            (rengerDirectionalFlowHybridBVFiniteRateVariationBound
              generator duration level)) := by
  rintro _ ⟨path, hPathRate, rfl⟩
  apply subset_closure
  exact ⟨path,
    rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_explicitEnvelope
      generator hDuration hLevel hPathRate, rfl⟩

/-- The strong-`L1` image of every genuinely finite dynamic-rate sublevel is compact. -/
theorem isCompact_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    IsCompact
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
        generator hDuration level) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_closure_toL1Path_image_uniformL1VariationEnvelope
      hDuration
      (rengerDirectionalFlowHybridBVFiniteRateL1Bound_lt_top
        generator duration hLevel)
      (rengerDirectionalFlowHybridBVFiniteRateVariationBound_lt_top
        generator duration hLevel))
    (isClosed_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
      generator hDuration hLevel)
  exact rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image_subset_compactEnvelope
    generator hDuration hLevel

/-- The unique hybrid lift is sequentially continuous on every genuinely finite projected
sublevel.  A failure of convergence would have a bad subsequence, while coercivity gives that
subsequence a further hybrid-convergent subsequence with the unique possible `L1` limit. -/
theorem seqContinuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    SeqContinuous
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level) := by
  intro projectedPaths projectedLimit hProjectedTendsto
  apply tendsto_of_subseq_tendsto
  intro indices hIndices
  let hybridPaths : ℕ →
      RengerDirectionalFlowHybridBVFiniteRateSublevelPath
        generator hDuration level :=
    fun sequenceIndex =>
      rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level (projectedPaths (indices sequenceIndex))
  have hHybridPathsVariation : ∀ sequenceIndex,
      finiteIntervalHybridBVDerivativeTotalVariation (hybridPaths sequenceIndex).1 ≤
        rengerDirectionalFlowHybridBVFiniteRateVariationBound
          generator duration level := by
    intro sequenceIndex
    exact
      (mem_finiteIntervalHybridBVUniformL1VariationEnvelope_iff.mp <|
        rengerDirectionalFlowHybridBVFiniteRateSublevel_subset_explicitEnvelope
          generator hDuration hLevel (hybridPaths sequenceIndex).2).2
  have hHybridPathsL1Tendsto : Tendsto
      (fun sequenceIndex =>
        (hybridPaths sequenceIndex).1.toDerivativePath.toL1Path)
      atTop (nhds projectedLimit.1) := by
    have hProjectedSubsequenceTendsto :=
      tendsto_subtype_rng.mp (hProjectedTendsto.comp hIndices)
    simpa only [hybridPaths, Function.comp_def,
      rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection] using!
        hProjectedSubsequenceTendsto
  obtain ⟨subsequence, _hSubsequenceMonotone, hybridLimit,
      hHybridLimitProjection, hHybridTendsto⟩ :=
    exists_subsequence_tendsto_hybrid_of_tendsto_toL1Path_of_uniformVariation
      hDuration (fun sequenceIndex => (hybridPaths sequenceIndex).1) projectedLimit.1
        (rengerDirectionalFlowHybridBVFiniteRateVariationBound_lt_top
          generator duration hLevel)
        hHybridPathsVariation hHybridPathsL1Tendsto
  have hHybridLimit :
      hybridLimit =
        (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
          generator hDuration level projectedLimit).1 := by
    apply FiniteIntervalHybridBVPath.injective_toL1Path
    change hybridLimit.toDerivativePath.toL1Path =
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level projectedLimit).1.toDerivativePath.toL1Path
    rw [hHybridLimitProjection,
      rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_projection]
  refine ⟨subsequence, ?_⟩
  rw [tendsto_subtype_rng]
  simpa only [Function.comp_apply, hybridPaths, hHybridLimit] using hHybridTendsto

/-- The unique hybrid lift is continuous on every genuinely finite projected sublevel.  The
sequential-to-topological upgrade occurs only on the metric strong-`L1` subtype. -/
theorem continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    Continuous
      (rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration level) :=
  continuous_iff_seqContinuous.mpr
    (seqContinuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
      generator hDuration hLevel)

/-- Every genuinely finite ambient dynamic-rate sublevel is compact in the published hybrid
topology.  Compactness is transported from its compact strong-`L1` image through the continuous
unique lift; no topology on the ambient hybrid carrier is replaced or strengthened. -/
theorem isCompact_rengerDirectionalFlowHybridBVFiniteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    IsCompact
      (rengerDirectionalFlowHybridBVFiniteRateSublevel
        generator hDuration level) := by
  rw [isCompact_iff_compactSpace]
  let : CompactSpace
      (RengerDirectionalFlowHybridBVFiniteRateSublevelL1Path
        generator hDuration level) :=
    isCompact_iff_compactSpace.mp
      (isCompact_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Image
        generator hDuration hLevel)
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr <|
    rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse_surjective
      generator hDuration level]
  simpa only [image_univ] using
    isCompact_univ.image
      (continuous_rengerDirectionalFlowHybridBVFiniteRateSublevelL1Inverse
        generator hDuration hLevel)

/-- Every genuinely finite ambient dynamic-rate sublevel is closed in the Hausdorff hybrid
carrier. -/
theorem isClosed_rengerDirectionalFlowHybridBVFiniteRateSublevel
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) {level : ENNReal} (hLevel : level < ∞) :
    IsClosed
      (rengerDirectionalFlowHybridBVFiniteRateSublevel
        generator hDuration level) :=
  (isCompact_rengerDirectionalFlowHybridBVFiniteRateSublevel
    generator hDuration hLevel).isClosed

/-- The totalized Renger dynamic rate is lower semicontinuous on the complete ambient hybrid
carrier.  Inadmissible paths retain infinite rate; no ambient dual identity is asserted. -/
theorem lowerSemicontinuous_rengerDirectionalFlowHybridBVDynamicRate
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    LowerSemicontinuous fun path :
        RengerDirectionalFlowHybridBVPath State duration =>
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro level
  change IsClosed
    (rengerDirectionalFlowHybridBVFiniteRateSublevel generator hDuration level)
  by_cases hLevel : level = ∞
  · subst level
    simpa only [rengerDirectionalFlowHybridBVFiniteRateSublevel,
      le_top, Set.ofPred_true] using
        (isClosed_univ : IsClosed
          (Set.univ : Set (RengerDirectionalFlowHybridBVPath State duration)))
  · exact isClosed_rengerDirectionalFlowHybridBVFiniteRateSublevel
      generator hDuration (lt_top_iff_ne_top.mpr hLevel)

end

end FiniteMarkovProcesses.InformationTheory
