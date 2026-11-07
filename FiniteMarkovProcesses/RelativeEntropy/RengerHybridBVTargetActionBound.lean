/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.TimeDependentMarkovJumpReplicaRadonNikodym
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVPositiveTargetGirsanov
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryReplicaJumpCount
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCountMoment
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalTestConcentration

/-!
# Canonical Renger target pathwise action bounds

For one fixed positive regularization, the canonical target-to-reference jump log ratio has an
explicit finite upper bound depending only on the cutoff and the frozen finite generator.  The
generic ordered-history action estimate then bounds the summed replica action by total physical
jump count plus a deterministic escape term.

This is a finite-regularization, finite-particle estimate.  It does not assert concentration,
an open-set lower bound, or a regularization limit.

## Main results

- `rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound`: explicit bound.
- `rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_le`: one-history action cap.
- `rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction_le`: replica cap.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- Sum of inverse positive directed rates of a finite reference generator.  It is a deliberately
coarse but explicit upper bound for the inverse of every individual positive reference rate. -/
noncomputable def finiteStateMarkovGeneratorPositiveRateInverseMass
    (generator : FiniteStateMarkovGenerator State) : ℝ :=
  ∑ transition : State × State,
    if generator.rate transition.1 transition.2 = 0 then 0
    else 1 / (generator.rate transition.1 transition.2 : ℝ)

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every positive reference-rate inverse is controlled by the finite inverse-rate mass. -/
theorem one_div_finiteStateMarkovGeneratorRate_le_positiveRateInverseMass
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hRate : 0 < generator.rate source target) :
    1 / (generator.rate source target : ℝ) ≤
      finiteStateMarkovGeneratorPositiveRateInverseMass generator := by
  unfold finiteStateMarkovGeneratorPositiveRateInverseMass
  have hNonnegative : ∀ transition : State × State,
      0 ≤ if generator.rate transition.1 transition.2 = 0 then 0
        else 1 / (generator.rate transition.1 transition.2 : ℝ) := by
    intro transition
    split_ifs
    · exact le_rfl
    · positivity
  have hSingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun transition : State × State ↦
      if generator.rate transition.1 transition.2 = 0 then 0
      else 1 / (generator.rate transition.1 transition.2 : ℝ))
    (fun transition _hTransition ↦ hNonnegative transition)
    (Finset.mem_univ (source, target))
  simpa [hRate.ne'] using hSingle

/-- Explicit finite upper bound on every canonical target-to-reference jump log ratio. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
    (generator : FiniteStateMarkovGenerator State) (index : ℕ) : ℝ :=
  Real.log ((index : ℝ) * finiteStateMarkovGeneratorPositiveRateInverseMass generator + 1)

/-- Time-labelled canonical target-to-reference jump log ratio on one directed channel. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (source target : State) (time : ℝ) : ℝ :=
  Real.log
    (((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ℝ) /
      (generator.rate source target : ℝ))

/-- Explicit absolute ceiling for every canonical target-to-reference jump log ratio. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
    (generator : FiniteStateMarkovGenerator State) (index : ℕ) : ℝ :=
  |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
      generator index| +
    |Real.log (1 / ((index : ℝ) + 1))|

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every canonical jump-log-ratio weight is measurable in physical time. -/
theorem measurable_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (source target : State) :
    Measurable
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
        generator path index source target) := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
  exact (((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    generator path index).measurable_rate source target).coe_nnreal_real.div
      measurable_const).log

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every positive canonical target jump has log rate ratio at most the explicit finite bound. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTarget_jumpLogRatio_le
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (time : ℝ) (source target : State)
    (hTargetRate : 0 <
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path index).rate time source target : ℝ)) :
    Real.log
        (((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
              generator path index).rate time source target : ℝ) /
          (generator.rate source target : ℝ)) ≤
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
        generator index := by
  have hReferenceRate : 0 < (generator.rate source target : ℝ) := by
    by_contra hNotPositive
    have hZero : generator.rate source target = 0 := by
      have hZeroReal : (generator.rate source target : ℝ) = 0 :=
        le_antisymm (not_lt.mp hNotPositive) (NNReal.coe_nonneg _)
      exact_mod_cast hZeroReal
    exact hTargetRate.ne'
      (congrArg NNReal.toReal
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_eq_zero
          generator path index time hZero))
  have hSupportedRate :
      ((rengerDirectionalFlowHybridBVReferenceSupportedTargetRate
          generator path index).rate time source target : ℝ) ≤ (index : ℝ) := by
    exact_mod_cast rengerDirectionalFlowHybridBVReferenceSupportedTargetRateValue_le
      generator path index time source target
  have hReferenceWeightLeOne :
      ((1 / ((index : NNReal) + 1) : NNReal) : ℝ) ≤ 1 := by
    push_cast
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg index)
  have hTargetRateLe :
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ℝ) ≤
        (index : ℝ) + (generator.rate source target : ℝ) := by
    rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization,
      rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate]
    push_cast
    exact add_le_add hSupportedRate
      (mul_le_of_le_one_left (NNReal.coe_nonneg _) hReferenceWeightLeOne)
  have hRatioLe :
      ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ℝ) /
          (generator.rate source target : ℝ) ≤
        (index : ℝ) * finiteStateMarkovGeneratorPositiveRateInverseMass generator + 1 := by
    calc
      _ ≤ ((index : ℝ) + (generator.rate source target : ℝ)) /
          (generator.rate source target : ℝ) :=
        (div_le_div_iff_of_pos_right hReferenceRate).2 hTargetRateLe
      _ = (index : ℝ) * (1 / (generator.rate source target : ℝ)) + 1 := by
        field_simp
      _ ≤ (index : ℝ) * finiteStateMarkovGeneratorPositiveRateInverseMass generator + 1 := by
        gcongr
        exact one_div_finiteStateMarkovGeneratorRate_le_positiveRateInverseMass
          generator (by exact_mod_cast hReferenceRate)
  apply Real.log_le_log
  · exact div_pos hTargetRate hReferenceRate
  · exact hRatioLe

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every channel's canonical target-to-reference jump log ratio obeys the explicit absolute
ceiling, including forbidden reference edges where both rates vanish. -/
theorem abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight_le
    (generator : FiniteStateMarkovGenerator State)
    (path : RengerDirectionalFlowHybridBVPath State duration) (index : ℕ)
    (source target : State) (time : ℝ) :
    |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
        generator path index source target time| ≤
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
        generator index := by
  by_cases hReferenceZero : generator.rate source target = 0
  · rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight,
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_eq_zero
        generator path index time hReferenceZero, hReferenceZero]
    simp [rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound]
    positivity
  · have hReferencePositiveNN : 0 < generator.rate source target :=
      lt_of_le_of_ne zero_le (Ne.symm hReferenceZero)
    have hReferencePositive : 0 < (generator.rate source target : ℝ) := by
      exact_mod_cast hReferencePositiveNN
    have hTargetPositive : 0 <
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ℝ) := by
      exact_mod_cast
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization_rate_pos
          generator path index time hReferencePositiveNN
    let referenceWeight : ℝ := 1 / ((index : ℝ) + 1)
    have hReferenceWeightPositive : 0 < referenceWeight := by
      dsimp only [referenceWeight]
      positivity
    have hTargetRateLower :
        referenceWeight * (generator.rate source target : ℝ) ≤
          ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path index).rate time source target : ℝ) := by
      rw [rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization,
        rengerDirectionalFlowHybridBVPositiveTargetRegularization_rate]
      push_cast
      exact le_add_of_nonneg_left (NNReal.coe_nonneg _)
    have hRatioLower : referenceWeight ≤
        ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path index).rate time source target : ℝ) /
            (generator.rate source target : ℝ) := by
      exact (le_div_iff₀ hReferencePositive).2 hTargetRateLower
    have hLogLower : Real.log referenceWeight ≤
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
          generator path index source target time := by
      exact Real.log_le_log hReferenceWeightPositive hRatioLower
    have hLogUpper :
        rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
            generator path index source target time ≤
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
            generator index := by
      exact rengerDirectionalFlowHybridBVCanonicalPositiveTarget_jumpLogRatio_le
        generator path index time source target hTargetPositive
    unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
    change |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight
        generator path index source target time| ≤
      |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
        generator index| + |Real.log referenceWeight|
    rw [abs_le]
    constructor
    · calc
        -(|rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
              generator index| + |Real.log referenceWeight|) ≤
            -|Real.log referenceWeight| := by
          linarith [abs_nonneg
            (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
              generator index)]
        _ ≤ Real.log referenceWeight := neg_abs_le _
        _ ≤ _ := hLogLower
    · calc
        _ ≤ rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
              generator index := hLogUpper
        _ ≤ |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
              generator index| := le_abs_self _
        _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On an ordered positive-density history, the canonical target's complete physical action is
bounded by physical jump count times the explicit log-ratio bound plus reference escape mass. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (history : FiniteJumpHistory State)
    (hOrdered : history.OrderedBefore duration)
    (hPositive : FiniteStateTimeDependentMarkovJumpDensityPositiveAt
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      history) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index history ≤
      (history.jumpCount : ℝ) *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
            generator index +
        (generator.toTimeDependentMarkovRate.escapeBound : ℝ) * duration := by
  exact finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBound
    (rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    generator.toTimeDependentMarkovRate hDuration.le
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
      generator index)
    (fun time source target hTargetRate ↦
      rengerDirectionalFlowHybridBVCanonicalPositiveTarget_jumpLogRatio_le
        generator path.1 index time source target hTargetRate)
    history hOrdered hPositive

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On an ordered positive-density history, the canonical target action has an explicit absolute
count-plus-escape bound. -/
theorem abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (history : FiniteJumpHistory State)
    (hOrdered : history.OrderedBefore duration)
    (hPositive : FiniteStateTimeDependentMarkovJumpDensityPositiveAt
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      history) :
    |rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index history| ≤
      (history.jumpCount : ℝ) *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
            generator index +
        ((generator.toTimeDependentMarkovRate.escapeBound : ℝ) +
          ((rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index).escapeBound : ℝ)) * duration := by
  exact abs_finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBounds
    (rengerDirectionalFlowHybridBVTargetInitialPMF path)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    generator.toTimeDependentMarkovRate hDuration.le
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
      generator index)
    (fun time source target _hTargetRate ↦
      abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight_le
        generator path.1 index source target time)
    history hOrdered hPositive

/-- For every common initial law, the canonical regularized target action has a finite second
moment under its normalized physical source. -/
theorem memLp_two_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initial : PMF State) :
    MemLp
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index)
      2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure initial
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩) := by
  let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
    generator path.1 index
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates ⟨duration, hDuration.le⟩
  let jumpBound :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioAbsoluteBound
      generator index
  let escapeBudget :=
    ((generator.toTimeDependentMarkovRate.escapeBound : ℝ) +
      (rates.escapeBound : ℝ)) * duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial rates ⟨duration, hDuration.le⟩⟩
  have hCount : MemLp
      (fun history : FiniteJumpHistory State ↦ (history.jumpCount : ℝ)) 2 law :=
    memLp_two_jumpCount_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates ⟨duration, hDuration.le⟩
  have hDominating : MemLp
      (fun history : FiniteJumpHistory State ↦
        jumpBound * (history.jumpCount : ℝ) + escapeBudget) 2 law := by
    have hSum := (hCount.const_mul jumpBound).add (memLp_const escapeBudget)
    simpa only [Pi.add_apply] using! hSum
  have hActionMeasurable : Measurable
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index) :=
    measurable_finiteStateTimeDependentMarkovJumpLogAction
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      rates generator.toTimeDependentMarkovRate duration
  have hOrdered : ∀ᵐ history ∂law, history.OrderedBefore duration := by
    exact ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial rates ⟨duration, hDuration.le⟩
  have hPositive : ∀ᵐ history ∂law,
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history := by
    have hDensityPositive :=
      ae_finiteStateTimeDependentMarkovJumpDensityPositiveAt initial rates duration
    change ∀ᵐ history ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates ⟨duration, hDuration.le⟩,
      FiniteStateTimeDependentMarkovJumpDensityPositiveAt initial rates history
    rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_jumpDensityMeasure
      initial rates ⟨duration, hDuration.le⟩]
    simpa only [NNReal.coe_mk] using! hDensityPositive
  apply hDominating.mono' hActionMeasurable.aestronglyMeasurable
  filter_upwards [hOrdered, hPositive] with history hHistoryOrdered hHistoryPositive
  have hInitialIndependence := congrFun
    (finiteStateTimeDependentMarkovJumpLogAction_sameInitial_eq
      (rengerDirectionalFlowHybridBVTargetInitialPMF path) initial
      rates generator.toTimeDependentMarkovRate duration) history
  have hBound :=
    abs_finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBounds
      initial rates generator.toTimeDependentMarkovRate hDuration.le jumpBound
      (fun time source target _hTargetRate ↦
        abs_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioWeight_le
          generator path.1 index source target time)
      history hHistoryOrdered hHistoryPositive
  change
    |finiteStateTimeDependentMarkovJumpLogAction
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      rates generator.toTimeDependentMarkovRate duration history| ≤
      jumpBound * (history.jumpCount : ℝ) + escapeBudget
  rw [hInitialIndependence]
  simpa only [jumpBound, escapeBudget, rates, mul_comm] using hBound

/-- Uniform finite-state variance ceiling for one canonical regularized target action. -/
noncomputable def
rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) : ℝ :=
  ∑ state, variance
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
      generator path index)
    (finiteStateTimeDependentMarkovReducedHistoryMeasure (PMF.pure state)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      ⟨duration, hDuration.le⟩)

omit [MeasurableSingletonClass State] in
/-- Every deterministic initial state's action variance lies below the finite-state sum ceiling. -/
theorem variance_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_le
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (state : State) :
    variance
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
          generator path index)
        (finiteStateTimeDependentMarkovReducedHistoryMeasure (PMF.pure state)
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          ⟨duration, hDuration.le⟩) ≤
      rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
        generator path index := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
  exact Finset.single_le_sum
    (f := fun otherState : State ↦ variance
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure (PMF.pure otherState)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩))
    (fun otherState _hOtherState ↦ variance_nonneg
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator path index)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure (PMF.pure otherState)
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        ⟨duration, hDuration.le⟩))
    (Finset.mem_univ state)

/-- At fixed regularization, the summed complete physical action of heterogeneous independent
replicas concentrates at particle speed around the sum of its exact coordinate expectations. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogActionDeviation_le
    {replicaCount : ℕ} (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initialConfiguration : Fin replicaCount → State)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
    law {histories |
        deviation ≤
          |∑ replica,
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                generator path index (histories replica) -
            ∑ replica, ∫ history,
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                generator path index history
              ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                (PMF.pure (initialConfiguration replica)) rates
                ⟨duration, hDuration.le⟩|} ≤
      ENNReal.ofReal
        ((replicaCount : ℝ) *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
            generator path index / deviation ^ 2) := by
  dsimp only
  exact finiteStateTimeDependentMarkovDeterministicInitialReplica_testSumDeviation_le
    initialConfiguration
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    ⟨duration, hDuration.le⟩
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
      generator path index)
    (measurable_finiteStateTimeDependentMarkovJumpLogAction
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVTargetInitialPMF path)
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      generator.toTimeDependentMarkovRate duration)
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
      generator path index)
    (fun state ↦
      memLp_two_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
        generator hDuration path index (PMF.pure state))
    (fun state ↦
      variance_rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction_le
        generator hDuration path index state)
    hDeviation

/-- At positive particle count, the probability that the complete canonical target action
misses its exact coordinate mean by `replicaCount * tolerance` is bounded by the one-particle
variance ceiling divided by `replicaCount * tolerance ^ 2`.  This is the particle-speed form
used by the open-neighborhood lower estimate. -/
theorem
rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogActionParticleSpeedDeviation_le
    {replicaCount : ℕ} (hReplicaCount : 0 < replicaCount)
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initialConfiguration : Fin replicaCount → State)
    {tolerance : ℝ} (hTolerance : 0 < tolerance) :
    let rates := rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates ⟨duration, hDuration.le⟩).toMeasure
    law {histories |
        (replicaCount : ℝ) * tolerance ≤
          |∑ replica,
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                generator path index (histories replica) -
            ∑ replica, ∫ history,
              rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogAction
                generator path index history
              ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                (PMF.pure (initialConfiguration replica)) rates
                ⟨duration, hDuration.le⟩|} ≤
      ENNReal.ofReal
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogActionVarianceBound
            generator path index /
          ((replicaCount : ℝ) * tolerance ^ 2)) := by
  dsimp only
  have hParticleCountReal : (0 : ℝ) < replicaCount := by exact_mod_cast hReplicaCount
  have hDeviation : 0 < (replicaCount : ℝ) * tolerance :=
    mul_pos hParticleCountReal hTolerance
  have hBound :=
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogActionDeviation_le
      generator hDuration path index initialConfiguration hDeviation
  convert hBound using 1
  congr 1
  field_simp [ne_of_gt hParticleCountReal, ne_of_gt hTolerance]

/-- Summed complete canonical target action for a heterogeneous deterministic-initial replica
family. -/
noncomputable def rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
    {replicaCount : ℕ} (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initialConfiguration : Fin replicaCount → State) :
    (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
  finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
    initialConfiguration
    (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
      generator path.1 index)
    generator.toTimeDependentMarkovRate duration

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On ordered positive-density replica histories, total jump count controls the summed complete
canonical target action with an explicit linear particle correction. -/
theorem rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction_le
    {replicaCount : ℕ} (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (index : ℕ) (initialConfiguration : Fin replicaCount → State)
    (histories : Fin replicaCount → FiniteJumpHistory State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration)
    (hPositive : ∀ replica, FiniteStateTimeDependentMarkovJumpDensityPositiveAt
      (PMF.pure (initialConfiguration replica))
      (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
        generator path.1 index)
      (histories replica)) :
    rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
        generator path index initialConfiguration histories ≤
      (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
            generator index +
        (replicaCount : ℝ) *
          (generator.toTimeDependentMarkovRate.escapeBound : ℝ) * duration := by
  unfold rengerDirectionalFlowHybridBVCanonicalPositiveTargetReplicaJumpLogAction
    finiteStateTimeDependentMarkovDeterministicInitialReplicaJumpLogAction
  calc
    (∑ replica,
        finiteStateTimeDependentMarkovJumpLogAction
          (PMF.pure (initialConfiguration replica))
          (PMF.pure (initialConfiguration replica))
          (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
            generator path.1 index)
          generator.toTimeDependentMarkovRate duration (histories replica)) ≤
      ∑ replica, (
        ((histories replica).jumpCount : ℝ) *
            rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
              generator index +
          (generator.toTimeDependentMarkovRate.escapeBound : ℝ) * duration) := by
      apply Finset.sum_le_sum
      intro replica _hReplica
      exact finiteStateTimeDependentMarkovJumpLogAction_le_count_mul_add_escapeBound
        (PMF.pure (initialConfiguration replica))
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetRegularization
          generator path.1 index)
        generator.toTimeDependentMarkovRate hDuration.le
        (rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
          generator index)
        (fun time source target hTargetRate ↦
          rengerDirectionalFlowHybridBVCanonicalPositiveTarget_jumpLogRatio_le
            generator path.1 index time source target hTargetRate)
        (histories replica) (hOrdered replica) (hPositive replica)
    _ = (finiteJumpHistoryReplicaTotalJumpCount histories : ℝ) *
          rengerDirectionalFlowHybridBVCanonicalPositiveTargetJumpLogRatioUpperBound
            generator index +
        (replicaCount : ℝ) *
          (generator.toTimeDependentMarkovRate.escapeBound : ℝ) * duration := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fin, coe_finiteJumpHistoryReplicaTotalJumpCount]
      ring

end

end FiniteMarkovProcesses.InformationTheory
