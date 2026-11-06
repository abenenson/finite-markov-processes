/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVLinearCombination
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVReferenceEvolutionPath

/-!
# Admissible reference-evolution perturbations of hybrid-BV paths

An admissible target path is mixed with the unchanged reference evolution from its own initial
law.  The construction is performed on the genuine hybrid derivative graph.  It preserves every
Renger admissibility field, keeps the initial law fixed, and exposes exact convex formulas for
the density and ordered-flow derivatives used by the dynamic-action estimate.
-/

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {duration : ℝ}

/-- Genuine hybrid-BV convex perturbation of a target by its unchanged reference evolution. -/
noncomputable def rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) : RengerDirectionalFlowHybridBVPath State duration :=
  FiniteIntervalHybridBVPath.linearCombination
    (1 - mixingWeight) mixingWeight path.1
    (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Reference-evolution perturbations converge to the target in the genuine hybrid topology as
their real mixing weight tends to zero. -/
theorem tendsto_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
    {Index : Type*} {filter : Filter Index}
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    {mixingWeight : Index → ℝ}
    (hMixingWeight : Tendsto mixingWeight filter (𝓝 0)) :
    Tendsto
      (fun index => rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path (mixingWeight index))
      filter (𝓝 path.1) := by
  have hTargetCoefficient :
      Tendsto (fun index => (1 : ℝ) - mixingWeight index) filter (𝓝 1) := by
    simpa only [sub_zero] using
      (show Tendsto (fun _ : Index => (1 : ℝ)) filter (𝓝 1) from
        tendsto_const_nhds).sub hMixingWeight
  simpa only [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
    sub_zero, FiniteIntervalHybridBVPath.linearCombination_one_zero] using
    FiniteIntervalHybridBVPath.tendsto_linearCombination path.1
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
      hTargetCoefficient hMixingWeight

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every reference-evolution perturbation retains the target's initial density coordinate
exactly. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_initialDensity
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) (state : State) :
    (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path mixingWeight).initialTrace (Sum.inl state) =
      path.1.initialTrace (Sum.inl state) := by
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
  rw [FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialDensity]
  ring

/-- The perturbed path's density coordinate is the exact pointwise convex perturbation on the
physical half-open interval. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityValue
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (hTimeDuration : time < duration) (state : State) :
    rengerDirectionalFlowHybridBVDensityValue
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time state =
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue
        generator path mixingWeight time state := by
  unfold rengerDirectionalFlowHybridBVDensityValue
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue
  rw [FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq
    _ _ _ _ ⟨hTimeNonnegative, hTimeDuration⟩]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change (1 - mixingWeight) *
      rengerDirectionalFlowHybridBVDensityValue path.1 time state +
    mixingWeight * rengerDirectionalFlowHybridBVDensityValue
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path) time state = _
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityValue
    generator path hTimeNonnegative hTimeDuration state]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The perturbed cumulative ordered flow is the exact convex combination on the physical
half-open interval. -/
theorem rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_cumulativeFlowValue
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (hTimeDuration : time < duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) :
    rengerDirectionalFlowHybridBVCumulativeFlowValue
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight) time transition =
      (1 - mixingWeight) *
          rengerDirectionalFlowHybridBVCumulativeFlowValue path.1 time transition +
        mixingWeight *
          rengerDirectionalFlowHybridBVCumulativeFlowValue
            (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
            time transition := by
  unfold rengerDirectionalFlowHybridBVCumulativeFlowValue
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
  rw [FiniteIntervalHybridBVPath.linearCombination_cadlagRepresentative_eq
    _ _ _ _ ⟨hTimeNonnegative, hTimeDuration⟩]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- Almost everywhere, each perturbed ordered-flow derivative is its exact convex formula. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivative_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ transition,
        rengerDirectionalFlowHybridBVFlowDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
              generator path mixingWeight) time transition =
          rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
            generator path mixingWeight time transition.val.1 transition.val.2 := by
  have hCoordinate (transition : FiniteStateOrderedOffDiagonalTransition State) :=
    FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
      (1 - mixingWeight) mixingWeight path.1
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
      path.2.absolutelyContinuousDerivative
      (rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath
        generator path).2.absolutelyContinuousDerivative
      (Sum.inr transition)
  rw [ae_all_iff]
  intro transition
  filter_upwards
      [hCoordinate transition,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_flowDerivative_eq
          generator path] with time hCombination hReference
  rw [rengerDirectionalFlowHybridBVFlowDerivative,
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
    hCombination]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (1 - mixingWeight) *
        rengerDirectionalFlowHybridBVFlowDerivative path.1 time transition +
      mixingWeight * rengerDirectionalFlowHybridBVFlowDerivative
        (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
        time transition = _
  rw [hReference transition]
  unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
    rengerDirectionalFlowHybridBVRawFlowDerivativeValue
  rw [dite_eq_left transition.property]

/-- Almost everywhere, each perturbed density derivative is its exact convex formula. -/
theorem ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityDerivative_eq
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      ∀ state,
        rengerDirectionalFlowHybridBVDensityDerivative
            (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
              generator path mixingWeight) time state =
          (1 - mixingWeight) *
              rengerDirectionalFlowHybridBVDensityDerivative path.1 time state +
            mixingWeight *
              rengerDirectionalFlowHybridBVReferenceEvolutionFlowDivergence
                generator path time state := by
  have hCoordinate (state : State) :=
    FiniteIntervalHybridBVPath.ae_linearCombination_derivativeDensity_eq
      (1 - mixingWeight) mixingWeight path.1
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
      path.2.absolutelyContinuousDerivative
      (rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath
        generator path).2.absolutelyContinuousDerivative
      (Sum.inl state)
  rw [ae_all_iff]
  intro state
  filter_upwards
      [hCoordinate state,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPath_densityDerivative_eq
          generator path] with time hCombination hReference
  rw [rengerDirectionalFlowHybridBVDensityDerivative,
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
    hCombination]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (1 - mixingWeight) *
        rengerDirectionalFlowHybridBVDensityDerivative path.1 time state +
      mixingWeight * rengerDirectionalFlowHybridBVDensityDerivative
        (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
        time state = _
  rw [hReference state]

/-- Every convex reference-evolution perturbation is a genuine admissible representation path. -/
noncomputable def
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) (hMixingWeightNonnegative : 0 ≤ mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1) :
    RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration := by
  let perturbed :=
    rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
      generator path mixingWeight
  have hTargetCoefficient : 0 ≤ 1 - mixingWeight := sub_nonneg.mpr hMixingWeightLeOne
  have hReferenceAdmissible : RengerDirectionalFlowHybridBVAdmissible
      (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path) hDuration := by
    exact (rengerDirectionalFlowHybridBVReferenceEvolutionRepresentationPath
      generator path).2
  refine ⟨perturbed, ?_⟩
  refine
    { absolutelyContinuousDerivative :=
        FiniteIntervalHybridBVPath.linearCombination_hasAbsolutelyContinuousDerivative
          (1 - mixingWeight) mixingWeight path.1
          (rengerDirectionalFlowHybridBVReferenceEvolutionPath generator path)
          path.2.absolutelyContinuousDerivative
          hReferenceAdmissible.absolutelyContinuousDerivative
      densityNonnegativeAE := ?_
      densityNormalizedAE := ?_
      cumulativeFlowNonnegativeAE := ?_
      flowDerivativeNonnegativeAE := ?_
      continuityEquationAE := ?_
      initialDensityNormalized := ?_
      initialDensityNonnegative := ?_
      cumulativeFlowInitiallyZero := ?_
      terminalDensityNormalized := ?_
      terminalDensityNonnegative := ?_
      terminalCumulativeFlowNonnegative := ?_ }
  · filter_upwards
      [path.2.densityNonnegativeAE, ae_restrict_mem measurableSet_Ioo]
      with time hTarget hTime
    intro state
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityValue
        generator path mixingWeight hTime.1.le hTime.2 state]
    unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue
    exact add_nonneg (mul_nonneg hTargetCoefficient (hTarget state))
      (mul_nonneg hMixingWeightNonnegative
        (by
          unfold rengerDirectionalFlowHybridBVReferenceEvolutionDensityValue
          exact ENNReal.toReal_nonneg))
  · filter_upwards
      [path.2.densityNormalizedAE, ae_restrict_mem measurableSet_Ioo]
      with time hTarget hTime
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl]
    simp_rw [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityValue
      generator path mixingWeight hTime.1.le hTime.2]
    exact sum_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedDensityValue
      generator path mixingWeight time hTime.1.le hTarget
  · filter_upwards
      [path.2.cumulativeFlowNonnegativeAE,
        hReferenceAdmissible.cumulativeFlowNonnegativeAE,
        ae_restrict_mem measurableSet_Ioo] with time hTarget hReference hTime
    intro transition
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_cumulativeFlowValue
        generator path mixingWeight hTime.1.le hTime.2 transition]
    exact add_nonneg (mul_nonneg hTargetCoefficient (hTarget transition))
      (mul_nonneg hMixingWeightNonnegative (hReference transition))
  · filter_upwards
      [path.2.flowDerivativeNonnegativeAE,
        hReferenceAdmissible.flowDerivativeNonnegativeAE,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivative_eq
          generator path mixingWeight] with time hTarget hReference hPerturbed
    intro transition
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      hPerturbed transition]
    exact rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue_nonnegative
      generator path hMixingWeightNonnegative hMixingWeightLeOne time
      transition.val.1 transition.val.2 (by
        unfold rengerDirectionalFlowHybridBVRawFlowDerivativeValue
        rw [dite_eq_left transition.property]
        exact hTarget transition)
  · filter_upwards
      [path.2.continuityEquationAE,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_densityDerivative_eq
          generator path mixingWeight,
        ae_rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_flowDerivative_eq
          generator path mixingWeight]
      with time hTarget hDensity hFlow
    intro state
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      hDensity state]
    have hIncoming :
        (∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative
              (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
                generator path mixingWeight)
              time ⟨(source, state), source.property⟩) =
          ∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
              generator path mixingWeight time source state := by
      apply Finset.sum_congr rfl
      intro source _hSource
      exact hFlow ⟨(source, state), source.property⟩
    have hOutgoing :
        (∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative
              (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
                generator path mixingWeight)
              time ⟨(state, target), target.property.symm⟩) =
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
              generator path mixingWeight time state target := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact hFlow ⟨(state, target), target.property.symm⟩
    have hRawIncoming :
        (∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVRawFlowDerivativeValue
              path.1 time source state) =
          ∑ source : {source : State // source ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative
              path.1 time ⟨(source, state), source.property⟩ := by
      apply Finset.sum_congr rfl
      intro source _hSource
      unfold rengerDirectionalFlowHybridBVRawFlowDerivativeValue
      rw [dite_eq_left source.property]
    have hRawOutgoing :
        (∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVRawFlowDerivativeValue
              path.1 time state target) =
          ∑ target : {target : State // target ≠ state},
            rengerDirectionalFlowHybridBVFlowDerivative
              path.1 time ⟨(state, target), target.property.symm⟩ := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      unfold rengerDirectionalFlowHybridBVRawFlowDerivativeValue
      rw [dite_eq_left target.property.symm]
    rw [hIncoming, hOutgoing]
    unfold rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedFlowValue
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hTarget state]
    rw [rengerDirectionalFlowHybridBVReferenceEvolutionFlowDivergence]
    unfold finiteStateFlowDivergence
    rw [Fintype.sum_eq_add_sum_subtype_ne _ state,
      Fintype.sum_eq_add_sum_subtype_ne _ state]
    simp [rengerDirectionalFlowHybridBVReferenceEvolutionFlowValue,
      generator.rate_self]
    rw [hRawIncoming, hRawOutgoing]
    ring
  · rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hReferenceAdmissible.initialDensityNormalized, path.2.initialDensityNormalized]
    ring
  · intro state
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hTargetCoefficient (path.2.initialDensityNonnegative state))
      (mul_nonneg hMixingWeightNonnegative
        (hReferenceAdmissible.initialDensityNonnegative state))
  · intro transition
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_initialTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      path.2.cumulativeFlowInitiallyZero transition, mul_zero, zero_add]
    rw [rengerDirectionalFlowHybridBVReferenceEvolutionPath_initialCumulativeFlow]
    simp
  · rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp_rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hReferenceAdmissible.terminalDensityNormalized,
      path.2.terminalDensityNormalized]
    ring
  · intro state
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hTargetCoefficient
      (path.2.terminalDensityNonnegative state))
      (mul_nonneg hMixingWeightNonnegative
        (hReferenceAdmissible.terminalDensityNonnegative state))
  · intro transition
    rw [show perturbed =
        rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
          generator path mixingWeight by rfl,
      rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath,
      FiniteIntervalHybridBVPath.linearCombination_terminalTrace _ _ _ _ hDuration]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hTargetCoefficient
      (path.2.terminalCumulativeFlowNonnegative transition))
      (mul_nonneg hMixingWeightNonnegative
        (hReferenceAdmissible.terminalCumulativeFlowNonnegative transition))

/-- The admissible perturbation retains the exact finite initial probability density used by the
microscopic reference source. -/
theorem
rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath_initialProbabilityDensity
    (generator : FiniteStateMarkovGenerator State)
    {hDuration : 0 < duration}
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (mixingWeight : ℝ) (hMixingWeightNonnegative : 0 ≤ mixingWeight)
    (hMixingWeightLeOne : mixingWeight ≤ 1) :
    rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
        (rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedRepresentationPath
          generator path mixingWeight hMixingWeightNonnegative hMixingWeightLeOne) =
      rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity path := by
  apply FiniteStateProbabilityDensity.ext
  intro state
  unfold rengerDirectionalFlowHybridBVTargetInitialProbabilityDensity
    rengerDirectionalFlowHybridBVInitialDensity
  dsimp only
  change Real.toNNReal
      ((rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath
        generator path mixingWeight).initialTrace (Sum.inl state)) = _
  rw [rengerDirectionalFlowHybridBVReferenceEvolutionPerturbedPath_initialDensity]

end

end FiniteMarkovProcesses.InformationTheory
