/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Independence.Integration
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovJumpHybridBVExponentialMoment
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVFiniteChannelDual
public import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDeterministicInitialHybridBVObservation

/-!
# Exponential bounds for deterministic-initial hybrid-BV jump observations

This module tensors the one-history exponential-tilt estimate through the exact heterogeneous
deterministic-initial product law.  It then transports the result through the almost-surely
ordered total hybrid-BV observation and the exact microscopic-to-macroscopic representation.
The configuration entries need not be identical.

## Main results

- `lintegral_prod_exp_rengerDirectionalFlowMicroscopicDualEvaluation_le_one`: heterogeneous
  product exponential estimate.
- `lintegral_exp_sum_rengerDirectionalFlowMicroscopicDualEvaluation_le_one`: equivalent summed
  microscopic-score estimate.
- `lintegral_exp_particleCount_mul_rengerDirectionalFlowHybridBVDualEvaluation_le_one`: exact
  macroscopic fixed-test exponential estimate on the total observation.
- `finiteStateMarkovJumpDeterministicInitialHybridBVDualEvaluation_ge_le_exponential`: the
  corresponding particle-speed fixed-test event bound on the macroscopic law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open FiniteMarkovProcesses.Probability
open PositiveFiniteJumpHistoryReplicas

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The product of all microscopic exponential weights has expectation at most one under every
heterogeneous deterministic-initial replica law. -/
theorem lintegral_prod_exp_rengerDirectionalFlowMicroscopicDualEvaluation_le_one
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (hDuration : 0 ≤ duration) :
    ∫⁻ histories,
      ∏ replica : Fin replicaCount,
        ENNReal.ofReal (Real.exp
          (rengerDirectionalFlowMicroscopicDualEvaluation generator test
            (histories replica)))
      ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure ≤ 1 := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
  let exponentialWeight : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ≥0∞ :=
    fun replica histories => ENNReal.ofReal (Real.exp
      (rengerDirectionalFlowMicroscopicDualEvaluation generator test
        (histories replica)))
  have hWeightMeasurable : ∀ replica, Measurable (exponentialWeight replica) := by
    intro replica
    exact ((measurable_rengerDirectionalFlowMicroscopicDualEvaluation
      generator test).comp (measurable_pi_apply replica)).exp.ennreal_ofReal
  have hIndependent : iIndepFun exponentialWeight law := by
    have hHistoryIndependent :=
      finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinates_iIndepFun
        initialConfiguration generator duration hDuration
    exact iIndepFun.comp
      (β := fun _ : Fin replicaCount => FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount => ℝ≥0∞) hHistoryIndependent
      (fun _ history => ENNReal.ofReal (Real.exp
        (rengerDirectionalFlowMicroscopicDualEvaluation generator test history)))
      (fun _ => (measurable_rengerDirectionalFlowMicroscopicDualEvaluation
        generator test).exp.ennreal_ofReal)
  have hCoordinateMoment (replica : Fin replicaCount) :
      ∫⁻ histories, exponentialWeight replica histories ∂law ≤ 1 := by
    calc
      (∫⁻ histories, exponentialWeight replica histories ∂law) =
          ∫⁻ history, ENNReal.ofReal (Real.exp
            (rengerDirectionalFlowMicroscopicDualEvaluation generator test history))
            ∂Measure.map (Function.eval replica) law := by
        rw [lintegral_map
          ((measurable_rengerDirectionalFlowMicroscopicDualEvaluation
            generator test).exp.ennreal_ofReal)
          (measurable_pi_apply replica)]
      _ = ∫⁻ history, ENNReal.ofReal (Real.exp
            (rengerDirectionalFlowMicroscopicDualEvaluation generator test history))
          ∂finiteStateMarkovJumpDensityMeasure
            (PMF.pure (initialConfiguration replica)) generator duration := by
        rw [finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure_coordinate_map
          initialConfiguration generator duration hDuration replica]
      _ ≤ 1 :=
        lintegral_exp_rengerDirectionalFlowMicroscopicDualEvaluation_le_one
          (PMF.pure (initialConfiguration replica)) generator test hDuration
  change (∫⁻ histories, ∏ replica : Fin replicaCount,
      exponentialWeight replica histories ∂law) ≤ 1
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun
    Finset.univ exponentialWeight hIndependent hWeightMeasurable]
  calc
    (∏ replica : Fin replicaCount,
        ∫⁻ histories, exponentialWeight replica histories ∂law) ≤
      ∏ _replica : Fin replicaCount, (1 : ℝ≥0∞) := by
        apply Finset.prod_le_prod₀
        · intro replica _hReplica
          exact bot_le
        · intro replica _hReplica
          exact hCoordinateMoment replica
    _ = 1 := by simp

/-- Equivalently, the exponential of the sum of all microscopic scores has expectation at most
one under every heterogeneous deterministic-initial replica law. -/
theorem lintegral_exp_sum_rengerDirectionalFlowMicroscopicDualEvaluation_le_one
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (hDuration : 0 ≤ duration) :
    ∫⁻ histories,
      ENNReal.ofReal (Real.exp
        (∑ replica : Fin replicaCount,
          rengerDirectionalFlowMicroscopicDualEvaluation generator test
            (histories replica)))
      ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure ≤ 1 := by
  calc
    _ = ∫⁻ histories,
        ∏ replica : Fin replicaCount,
          ENNReal.ofReal (Real.exp
            (rengerDirectionalFlowMicroscopicDualEvaluation generator test
              (histories replica)))
        ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
      apply lintegral_congr
      intro histories
      rw [Real.exp_sum]
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro replica _hReplica
      exact (Real.exp_pos _).le
    _ ≤ 1 :=
      lintegral_prod_exp_rengerDirectionalFlowMicroscopicDualEvaluation_le_one
        initialConfiguration generator duration test hDuration

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

omit [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] in
/-- The exponential of particle count times one fixed macroscopic dual evaluation has expectation
at most one under the total deterministic-initial hybrid-BV observation. -/
theorem
    lintegral_exp_particleCount_mul_rengerDirectionalFlowHybridBVDualEvaluation_le_one
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (hDuration : 0 ≤ duration) :
    ∫⁻ histories,
      ENNReal.ofReal (Real.exp
        ((successorIndex + 1 : ℝ) *
          rengerDirectionalFlowHybridBVDualEvaluation generator test
            (empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories)))
      ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration).toMeasure ≤ 1 := by
  calc
    _ = ∫⁻ histories,
        ENNReal.ofReal (Real.exp
          (∑ replica : Fin (successorIndex + 1),
            rengerDirectionalFlowMicroscopicDualEvaluation generator test
              (histories replica)))
        ∂(finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration).toMeasure := by
      apply lintegral_congr_ae
      filter_upwards [
        ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration generator duration hDuration
      ] with histories hOrdered
      rw [empiricalDensityDirectionalFlowTotalHybridBVObservation_eq_ordered
        successorIndex duration histories hOrdered]
      rw [rengerDirectionalFlowHybridBVDualEvaluation_eq_averageMicroscopicDualEvaluation
        successorIndex duration (fun replica => ⟨histories replica, hOrdered replica⟩)
        generator test hDuration]
      congr 2
      field_simp
      simp only [orderedReplicaHistories]
    _ ≤ 1 :=
      lintegral_exp_sum_rengerDirectionalFlowMicroscopicDualEvaluation_le_one
        initialConfiguration generator duration test hDuration

/-- A configuration-uniform particle-speed exponential bound for exceeding one fixed continuous
hybrid-BV dual evaluation, stated first on the heterogeneous microscopic product law. -/
theorem finiteStateMarkovJumpDeterministicInitialReplicaHybridBVDualEvaluation_ge_le_exponential
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (hDuration : 0 ≤ duration) (threshold : ℝ) :
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
        {histories |
          threshold ≤ rengerDirectionalFlowHybridBVDualEvaluation generator test
            (empiricalDensityDirectionalFlowTotalHybridBVObservation
              successorIndex duration histories)} ≤
      ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) * threshold)) := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
  let exponentialEvaluation :
      (Fin (successorIndex + 1) → FiniteJumpHistory State) → ℝ≥0∞ :=
    fun histories => ENNReal.ofReal (Real.exp
      ((successorIndex + 1 : ℝ) *
        rengerDirectionalFlowHybridBVDualEvaluation generator test
          (empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories)))
  let exponentialThreshold : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp ((successorIndex + 1 : ℝ) * threshold))
  have hExponentialEvaluationMeasurable : Measurable exponentialEvaluation := by
    exact (((continuous_rengerDirectionalFlowHybridBVDualEvaluation
      generator test).measurable.comp
        (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
          successorIndex duration)).const_mul
            (successorIndex + 1 : ℝ)).exp.ennreal_ofReal
  have hThresholdPositive : exponentialThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hEventSubset :
      {histories : Fin (successorIndex + 1) → FiniteJumpHistory State |
        threshold ≤ rengerDirectionalFlowHybridBVDualEvaluation generator test
          (empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories)} ⊆
        {histories | exponentialThreshold ≤ exponentialEvaluation histories} := by
    intro histories hHistories
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hHistories (by positivity)
  have hMoment :=
    lintegral_exp_particleCount_mul_rengerDirectionalFlowHybridBVDualEvaluation_le_one
      successorIndex initialConfiguration generator duration test hDuration
  change law
      {histories |
        threshold ≤ rengerDirectionalFlowHybridBVDualEvaluation generator test
          (empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories)} ≤ _
  calc
    _ ≤ law {histories | exponentialThreshold ≤ exponentialEvaluation histories} :=
      measure_mono hEventSubset
    _ ≤ (∫⁻ histories, exponentialEvaluation histories ∂law) / exponentialThreshold :=
      meas_ge_le_lintegral_div hExponentialEvaluationMeasurable.aemeasurable
        hThresholdPositive ENNReal.ofReal_ne_top
    _ ≤ 1 / exponentialThreshold := by
      apply ENNReal.div_le_div_right
      simpa only [law, exponentialEvaluation] using hMoment
    _ = ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) * threshold)) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp 0) by norm_num]
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      ring

/-- The fixed-test exponential bound transported to the exact total hybrid-BV observation law. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVDualEvaluation_ge_le_exponential
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (hDuration : 0 ≤ duration) (threshold : ℝ) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration
        {path | threshold ≤
          rengerDirectionalFlowHybridBVDualEvaluation generator test path} ≤
      ENNReal.ofReal
        (Real.exp (-(successorIndex + 1 : ℝ) * threshold)) := by
  rw [finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw_eq_map_replicaLaw]
  rw [Measure.map_apply
    (measurable_empiricalDensityDirectionalFlowTotalHybridBVObservation
      successorIndex duration)
    (measurableSet_le measurable_const
      (continuous_rengerDirectionalFlowHybridBVDualEvaluation generator test).measurable)]
  exact
    finiteStateMarkovJumpDeterministicInitialReplicaHybridBVDualEvaluation_ge_le_exponential
      successorIndex initialConfiguration generator duration test hDuration threshold

omit [MeasurableSpace State] [MeasurableSingletonClass State]
  [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State] in
/-- A compact target lying strictly above one real level of the exact ambient dual rate admits a
finite cover by strict superlevel neighborhoods of individual continuous tests.  The tests and
their number depend only on the compact target, generator, and level, not on particle count or
initial configuration. -/
theorem exists_finset_rengerDirectionalFlowHybridBVDualTest_cover_of_compact
    (generator : FiniteStateMarkovGenerator State)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    ∃ tests : Finset (RengerDirectionalFlowHybridBVDualTest State duration),
      compactTarget ⊆
        ⋃ test ∈ tests,
          {path | level <
            rengerDirectionalFlowHybridBVDualEvaluation generator test path} := by
  classical
  have hTestExists (path : compactTarget) :
      ∃ test : RengerDirectionalFlowHybridBVDualTest State duration,
        level < rengerDirectionalFlowHybridBVDualEvaluation generator test path.1 := by
    have hRate := hDualRate path.1 path.2
    unfold rengerDirectionalFlowHybridBVDualRate at hRate
    rcases lt_iSup_iff.mp hRate with ⟨test, hTest⟩
    exact ⟨test, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hLevel).mp hTest⟩
  choose chosenTest hChosenTest using hTestExists
  let neighborhood := fun path : compactTarget =>
    {candidate | level <
      rengerDirectionalFlowHybridBVDualEvaluation generator
        (chosenTest path) candidate}
  have hNeighborhoodOpen : ∀ path, IsOpen (neighborhood path) := by
    intro path
    exact isOpen_lt continuous_const
      (continuous_rengerDirectionalFlowHybridBVDualEvaluation
        generator (chosenTest path))
  have hNeighborhoodCover : compactTarget ⊆ ⋃ path, neighborhood path := by
    intro path hPath
    exact mem_iUnion.mpr ⟨⟨path, hPath⟩, hChosenTest ⟨path, hPath⟩⟩
  rcases hCompactTarget.elim_finite_subcover neighborhood hNeighborhoodOpen
      hNeighborhoodCover with ⟨points, hPoints⟩
  refine ⟨points.image chosenTest, ?_⟩
  intro path hPath
  rcases mem_iUnion.mp (hPoints hPath) with ⟨point, hPoint⟩
  rcases mem_iUnion.mp hPoint with ⟨hPointMem, hNeighborhood⟩
  rw [mem_iUnion]
  refine ⟨chosenTest point, ?_⟩
  rw [mem_iUnion]
  exact ⟨Finset.mem_image.mpr ⟨point, hPointMem, rfl⟩, hNeighborhood⟩

/-- Any specified finite strict dual-test cover gives the corresponding conditional compact-set
probability bound with its exact finite prefactor. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVTarget_le_of_dualTest_cover
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 ≤ duration)
    (target : Set (RengerDirectionalFlowHybridBVPath State duration))
    (level : ℝ)
    (tests : Finset (RengerDirectionalFlowHybridBVDualTest State duration))
    (hCover : target ⊆
      ⋃ test ∈ tests,
        {path | level <
          rengerDirectionalFlowHybridBVDualEvaluation generator test path}) :
    finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
        successorIndex initialConfiguration generator duration hDuration target ≤
      (tests.card : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  let law := finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
    successorIndex initialConfiguration generator duration hDuration
  have hWeakCover : target ⊆
      ⋃ test ∈ tests,
        {path | level ≤
          rengerDirectionalFlowHybridBVDualEvaluation generator test path} := by
    intro path hPath
    rcases mem_iUnion.mp (hCover hPath) with ⟨test, hTest⟩
    rcases mem_iUnion.mp hTest with ⟨hTestMem, hEvaluation⟩
    rw [mem_iUnion]
    refine ⟨test, ?_⟩
    rw [mem_iUnion]
    refine ⟨hTestMem, ?_⟩
    change level ≤ rengerDirectionalFlowHybridBVDualEvaluation generator test path
    exact hEvaluation.le
  change law target ≤ _
  calc
    _ ≤ law (⋃ test ∈ tests,
        {path | level ≤
          rengerDirectionalFlowHybridBVDualEvaluation generator test path}) :=
      measure_mono hWeakCover
    _ ≤ ∑ test ∈ tests, law
        {path | level ≤
          rengerDirectionalFlowHybridBVDualEvaluation generator test path} :=
      measure_biUnion_finset_le tests _
    _ ≤ ∑ _test ∈ tests,
        ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
      apply Finset.sum_le_sum
      intro test _hTest
      exact
        finiteStateMarkovJumpDeterministicInitialHybridBVDualEvaluation_ge_le_exponential
          successorIndex initialConfiguration generator duration test hDuration level
    _ = _ := by simp

/-- Conditional compact-set upper bound at every nonnegative level strictly below the exact
ambient dual rate throughout the target.  The returned finite prefactor is independent of
particle count and the labelled deterministic initial configuration. -/
theorem finiteStateMarkovJumpDeterministicInitialHybridBVCompact_le_of_lt_dualRate
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hDualRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path) :
    ∃ tests : Finset (RengerDirectionalFlowHybridBVDualTest State duration),
      ∀ (successorIndex : ℕ)
        (initialConfiguration : Fin (successorIndex + 1) → State)
        (hDuration : 0 ≤ duration),
        finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
            successorIndex initialConfiguration generator duration hDuration compactTarget ≤
          (tests.card : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  rcases exists_finset_rengerDirectionalFlowHybridBVDualTest_cover_of_compact
      generator compactTarget hCompactTarget level hLevel hDualRate with ⟨tests, hCover⟩
  refine ⟨tests, ?_⟩
  intro successorIndex initialConfiguration hDuration
  exact finiteStateMarkovJumpDeterministicInitialHybridBVTarget_le_of_dualTest_cover
    successorIndex initialConfiguration generator duration hDuration compactTarget level
      tests hCover

/-- Conditional compact-set upper bound on a target contained in the exact finite-rate
representation domain.  This is the licensed dynamic-rate specialization of the ambient dual
bound: it does not identify the dual and dynamic rates away from admissible paths. -/
theorem
    finiteStateMarkovJumpDeterministicInitialHybridBVCompact_le_of_lt_dynamicRate_of_admissible
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hDuration : 0 < duration)
    (compactTarget : Set (RengerDirectionalFlowHybridBVPath State duration))
    (hCompactTarget : IsCompact compactTarget)
    (level : ℝ) (hLevel : 0 ≤ level)
    (hAdmissible : ∀ path ∈ compactTarget,
      RengerDirectionalFlowHybridBVAdmissible path hDuration)
    (hDynamicRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level <
        rengerDirectionalFlowHybridBVDynamicRate generator hDuration path) :
    ∃ tests : Finset (RengerDirectionalFlowHybridBVDualTest State duration),
      ∀ (successorIndex : ℕ)
        (initialConfiguration : Fin (successorIndex + 1) → State),
        finiteStateMarkovJumpDeterministicInitialHybridBVObservationLaw
            successorIndex initialConfiguration generator duration hDuration.le compactTarget ≤
          (tests.card : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(successorIndex + 1 : ℝ) * level)) := by
  have hDualRate : ∀ path ∈ compactTarget,
      ENNReal.ofReal level < rengerDirectionalFlowHybridBVDualRate generator path := by
    intro path hPath
    rw [rengerDirectionalFlowHybridBVDualRate_eq_dynamicRate_on_representationDomain
      generator hDuration ⟨path, hAdmissible path hPath⟩]
    exact hDynamicRate path hPath
  rcases finiteStateMarkovJumpDeterministicInitialHybridBVCompact_le_of_lt_dualRate
      generator duration compactTarget hCompactTarget level hLevel hDualRate with
    ⟨tests, hTests⟩
  exact ⟨tests, fun successorIndex initialConfiguration =>
    hTests successorIndex initialConfiguration hDuration.le⟩

end

end FiniteMarkovProcesses.InformationTheory
