/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.DensityFluxLargeDeviationRepresentation
import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVExponentialBound
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVExtendedDualSupport
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpHybridBVCompactContainment

/-!
# Conditional upper bounds for finite-state hybrid-BV jump observations

This module converts the exact finite-test exponential estimate into its particle-speed
logarithmic form.  The initial configuration may vary arbitrarily with particle count.  The
result is deliberately stated first against the ambient dual rate; specialization to the
published dynamic rate requires a separately licensed source-support or representation-domain
theorem.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open _root_.MeasureTheory
open Set
open scoped ENNReal Topology

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- The extended logarithm of one deterministic-initial hybrid-BV event probability, divided by
the exact positive particle count. -/
noncomputable def
    finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration) (successorIndex : ℕ)
    (event : Set (RengerDirectionalFlowHybridBVPath State duration)) : EReal :=
  (finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
      successorIndex (initialConfiguration successorIndex) generator duration hDuration event).log /
    ((((successorIndex + 1 : ℕ) : ℝ) : EReal))

/-- A fixed finite prefactor contributes zero at particle-number speed. -/
theorem fixedFinitePrefactorLog_div_particleCount_tendsto_zero (prefactor : ℕ) :
    Tendsto (fun successorIndex : ℕ =>
      Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ))
      atTop (nhds 0) := by
  apply tendsto_const_nhds.div_atTop
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

/-- Finite-sample logarithmic upper bound on a compact target lying strictly above one
nonnegative level of the ambient dual rate.  The only residual is a fixed finite-cover
prefactor, independent of particle count and the labelled initial configurations. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability_le_of_lt_dualRate
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    ∃ prefactor : ℕ, ∀ successorIndex,
      finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration successorIndex compactTarget ≤
        (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) := by
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVCompact_le_of_lt_dualRate
      generator duration compactTarget hCompactTarget level hLevel hDualRate with
    ⟨tests, hTests⟩
  refine ⟨tests.card, ?_⟩
  intro successorIndex
  have hProbability :
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex (initialConfiguration successorIndex) generator duration hDuration
          compactTarget ≤
        ((tests.card + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
    refine (hTests successorIndex (initialConfiguration successorIndex) hDuration).trans ?_
    gcongr
    exact_mod_cast Nat.le_add_right tests.card 1
  unfold finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
  refine (EReal.monotone_div_right_of_nonneg
    (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
    (ENNReal.log_monotone hProbability)).trans_eq ?_
  have hPrefactorPositive : 0 < (tests.card + 1 : ℝ) := by positivity
  rw [show (((tests.card + 1 : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal (tests.card + 1 : ℝ) by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ENNReal.ofReal_natCast (tests.card + 1)).symm]
  rw [ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos hPrefactorPositive,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hReal :
      (Real.log (tests.card + 1 : ℝ) +
          -(successorIndex + 1 : ℝ) * level) /
        (successorIndex + 1 : ℝ) =
      Real.log (tests.card + 1 : ℝ) / (successorIndex + 1 : ℝ) - level := by
    field_simp
    ring
  simpa only [EReal.coe_add, EReal.coe_div, Nat.cast_add, Nat.cast_one,
    EReal.coe_natCast] using
    congrArg (fun value : ℝ => (value : EReal)) hReal

/-- Compact ambient-dual upper bound in literal particle-speed limsup form. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVCompactLimsup_le_neg_of_lt_dualRate
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration successorIndex compactTarget)
        atTop ≤ (-level : ℝ) := by
  rcases
      finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability_le_of_lt_dualRate
        initialConfiguration generator duration hDuration compactTarget hCompactTarget level
          hLevel hDualRate with
    ⟨prefactor, hUpper⟩
  have hUpperLimit : Tendsto (fun successorIndex =>
      (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) :
        ℕ → EReal) atTop (nhds ((-level : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using
      (fixedFinitePrefactorLog_div_particleCount_tendsto_zero prefactor).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => level) atTop (nhds level))
  calc
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration successorIndex compactTarget)
        atTop ≤
      limsup (fun successorIndex =>
        (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) :
          ℕ → EReal) atTop :=
        limsup_le_limsup (Eventually.of_forall hUpper)
    _ = ((-level : ℝ) : EReal) := hUpperLimit.limsup_eq

/-- Configuration-uniform finite-sample upper bound on an arbitrary closed target whose ambient
dual rate lies strictly above one nonnegative level.  Compact containment supplies the missing
compactness: the count cutoff is chosen so that its Chernoff complement has exactly the same
exponential level as the compact dual-test cover. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVClosed_le_of_lt_dualRate
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    ∃ prefactor : ℕ, ∀ (successorIndex : ℕ)
      (initialConfiguration : Fin (successorIndex + 1) → State),
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
          successorIndex initialConfiguration generator duration hDuration.le closedTarget ≤
        ((prefactor + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  let durationNNReal : NNReal := ⟨duration, hDuration.le⟩
  let sourceExponentCoefficient : ℝ :=
    ((generator.uniformizationRate * durationNNReal : NNReal) : ℝ) *
      (Real.exp 1 - 1)
  let countCutoff : ℝ := sourceExponentCoefficient + level
  let compactContainer :=
    finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      (State := State) duration countCutoff
  have hCompactContainer : IsCompact compactContainer := by
    exact isCompact_finiteStateMarkovJumpEmpiricalHybridBVCompactContainer
      duration countCutoff hDuration
  have hCompactTarget : IsCompact (closedTarget ∩ compactContainer) :=
    by simpa only [inter_comm] using hCompactContainer.inter_right hClosedTarget
  have hCompactDualRate : ∀ path ∈ closedTarget ∩ compactContainer,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path := by
    intro path hPath
    exact hDualRate path hPath.1
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVCompact_le_of_lt_dualRate
      generator duration (closedTarget ∩ compactContainer) hCompactTarget level hLevel
        hCompactDualRate with
    ⟨tests, hCompactBound⟩
  refine ⟨tests.card, ?_⟩
  intro successorIndex initialConfiguration
  let law := finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    successorIndex initialConfiguration generator duration hDuration.le
  let exponentialLevel : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level))
  have hTail : law compactContainerᶜ ≤ exponentialLevel := by
    have hChernoff :=
      finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_compl_compactContainer_le
        successorIndex initialConfiguration generator durationNNReal
          (by exact_mod_cast hDuration) (by norm_num : (0 : ℝ) < 1) countCutoff
    change law compactContainerᶜ ≤ exponentialLevel
    refine hChernoff.trans_eq ?_
    apply congrArg ENNReal.ofReal
    dsimp only [countCutoff, sourceExponentCoefficient, durationNNReal]
    push_cast
    ring_nf
  have hCompact : law (closedTarget ∩ compactContainer) ≤
      (tests.card : ℝ≥0∞) * exponentialLevel := by
    exact hCompactBound successorIndex initialConfiguration hDuration.le
  have hTargetSubset : closedTarget ⊆
      (closedTarget ∩ compactContainer) ∪ compactContainerᶜ := by
    intro path hPath
    by_cases hContainer : path ∈ compactContainer
    · exact Or.inl ⟨hPath, hContainer⟩
    · exact Or.inr hContainer
  change law closedTarget ≤ ((tests.card + 1 : ℕ) : ℝ≥0∞) * exponentialLevel
  calc
    law closedTarget ≤
        law ((closedTarget ∩ compactContainer) ∪ compactContainerᶜ) :=
      measure_mono hTargetSubset
    _ ≤ law (closedTarget ∩ compactContainer) + law compactContainerᶜ :=
      measure_union_le _ _
    _ ≤ (tests.card : ℝ≥0∞) * exponentialLevel + exponentialLevel :=
      add_le_add hCompact hTail
    _ = ((tests.card + 1 : ℕ) : ℝ≥0∞) * exponentialLevel := by
      push_cast
      ring

/-- Full closed-set ambient-dual upper bound in literal particle-speed limsup form. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_neg_of_lt_dualRate
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget)
        atTop ≤ (-level : ℝ) := by
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVClosed_le_of_lt_dualRate
      generator duration hDuration closedTarget hClosedTarget level hLevel hDualRate with
    ⟨prefactor, hProbability⟩
  have hUpper : ∀ successorIndex,
      finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget ≤
        (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) := by
    intro successorIndex
    unfold finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
    refine (EReal.monotone_div_right_of_nonneg
      (by positivity : (0 : EReal) ≤ ((((successorIndex + 1 : ℕ) : ℝ) : EReal)))
      (ENNReal.log_monotone
        (hProbability successorIndex (initialConfiguration successorIndex)))).trans_eq ?_
    have hPrefactorPositive : 0 < (prefactor + 1 : ℝ) := by positivity
    rw [show (((prefactor + 1 : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal (prefactor + 1 : ℝ) by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (ENNReal.ofReal_natCast (prefactor + 1)).symm]
    rw [ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos hPrefactorPositive,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    have hReal :
        (Real.log (prefactor + 1 : ℝ) +
            -(successorIndex + 1 : ℝ) * level) /
          (successorIndex + 1 : ℝ) =
        Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level := by
      field_simp
      ring
    simpa only [EReal.coe_add, EReal.coe_div, Nat.cast_add, Nat.cast_one,
      EReal.coe_natCast] using
      congrArg (fun value : ℝ => (value : EReal)) hReal
  have hUpperLimit : Tendsto (fun successorIndex =>
      (Real.log (prefactor + 1 : ℝ) / (successorIndex + 1 : ℝ) - level : ℝ) :
        ℕ → EReal) atTop (nhds ((-level : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa using
      (fixedFinitePrefactorLog_div_particleCount_tendsto_zero prefactor).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => level) atTop (nhds level))
  exact (limsup_le_limsup (Eventually.of_forall hUpper)).trans_eq hUpperLimit.limsup_eq

/-- The full closed upper estimate transfers to the published dynamic rate on any closed target
where a separately proved pointwise dual representation is available.  This theorem isolates the
exact support bridge needed for targets containing singular finite-particle observations; it does
not manufacture that bridge from lower semicontinuity or compact containment. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate_of_dualEq
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRateEq : ∀ path ∈ closedTarget,
      rengerDirectionalFlowHybridBVDualRate generator path =
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path)
    (hDynamicRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget)
        atTop ≤ (-level : ℝ) := by
  apply
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_neg_of_lt_dualRate
      initialConfiguration generator duration hDuration closedTarget hClosedTarget level hLevel
  intro path hPath
  rw [hDualRateEq path hPath]
  exact hDynamicRate path hPath

/-- Dynamic-rate specialization on a closed target wholly contained in the exact finite-rate
representation domain. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate_of_admissible
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hAdmissible : ∀ path ∈ closedTarget,
      RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (hDynamicRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget)
        atTop ≤ (-level : ℝ) := by
  apply
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate_of_dualEq
      initialConfiguration generator duration hDuration closedTarget hClosedTarget level hLevel
  · intro path hPath
    exact rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain
      generator hDuration ⟨path, hAdmissible path hPath⟩
  · exact hDynamicRate

/-- Dynamic-rate specialization on a closed target whose points are independently known to be
either finite-rate admissible or to carry a positive singular ordered-flow channel. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate_of_dualSupported
    (initialConfiguration : ∀ successorIndex,
      Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (closedTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hClosedTarget : IsClosed closedTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hSupport : ∀ path ∈ closedTarget,
      RengerDirectionalFlowHybridBVFiniteRateOrSingularFlow path hDuration)
    (hDynamicRate : ∀ path ∈ closedTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    limsup (fun successorIndex =>
        finiteStateMarkovJumpDeterministicInitialHybridBVScaledEventLogProbability
          initialConfiguration generator duration hDuration.le successorIndex closedTarget)
        atTop ≤ (-level : ℝ) := by
  apply
    finiteStateMarkovJumpDeterministicInitialHybridBVClosedLimsup_le_dynamicRate_of_dualEq
      initialConfiguration generator duration hDuration closedTarget hClosedTarget level hLevel
  · intro path hPath
    exact
      rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_of_finiteRateOrSingularFlow
        hDuration generator (hSupport path hPath)
  · exact hDynamicRate

end

end FiniteMarkovProcesses.InformationTheory
