/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.NonnegativeDensityVariation
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Finite-step derivatives on a bounded physical interval

This module constructs explicit scalar càdlàg Stieltjes witnesses for constants, sums, scalar
multiples, and right-continuous event steps.  The event-step derivative is the correspondingly
weighted Dirac measure restricted to the open physical interval.  These constructors let finite
jump observations inhabit the hybrid BV graph with derivatives that remain explicit functions of
the microscopic event times.

## Main declarations

- `ScalarFiniteIntervalCadlagDerivativeWitness.constant`: the zero-derivative witness;
- `ScalarFiniteIntervalCadlagDerivativeWitness.add` and `.smul`: witness algebra;
- `scalarRightEventStep`: a right-continuous scalar event step;
- `scalarRightEventStepDerivativeWitness`: its exact restricted-Dirac derivative witness.
- `finiteRestrictedWeightedDiracVagueSignedMeasure_totalVariation_apply_univ_le`: the total
  variation of a finite restricted atomic derivative is bounded by its absolute coefficient sum.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

noncomputable section

namespace ScalarFiniteIntervalCadlagDerivativeWitness

variable {first second : ℝ → ℝ} {duration : ℝ}

/-- Transporting a scalar derivative witness along equality of its represented path leaves the
explicit right-continuous modification unchanged. -/
@[simp]
theorem modification_transport
    {source target : ℝ → ℝ} (hPath : source = target)
    (witness : ScalarFiniteIntervalCadlagDerivativeWitness source duration) :
    (hPath ▸ witness).modification = witness.modification := by
  subst target
  rfl

/-- Transporting a scalar derivative witness along equality of its represented path leaves the
explicit signed derivative unchanged. -/
@[simp]
theorem derivative_transport
    {source target : ℝ → ℝ} (hPath : source = target)
    (witness : ScalarFiniteIntervalCadlagDerivativeWitness source duration) :
    (hPath ▸ witness).derivative = witness.derivative := by
  subst target
  rfl

/-- A constant scalar path has the zero signed derivative. -/
def constant (value duration : ℝ) :
    ScalarFiniteIntervalCadlagDerivativeWitness (fun _ => value) duration where
  modification := fun _ => value
  derivative := VagueSignedMeasure.ofSignedMeasure (0 : SignedMeasure ℝ)
  derivative_restrict_openInterval := by
    change (0 : SignedMeasure ℝ).restrict (Ioo 0 duration) = 0
    exact VectorMeasure.restrict_zero
  eventuallyEq := Filter.Eventually.of_forall fun _ => rfl
  rightContinuous := fun _ => continuousWithinAt_const
  hasLeftLimit := fun _ => ⟨value, tendsto_const_nhds⟩
  derivative_Ioc := by
    intro start finish _hStart _hOrder _hFinish
    simp

/-- Pointwise addition adds the two explicit signed derivatives. -/
def add
    (firstWitness : ScalarFiniteIntervalCadlagDerivativeWitness first duration)
    (secondWitness : ScalarFiniteIntervalCadlagDerivativeWitness second duration) :
    ScalarFiniteIntervalCadlagDerivativeWitness (first + second) duration where
  modification := firstWitness.modification + secondWitness.modification
  derivative := VagueSignedMeasure.ofSignedMeasure
    (firstWitness.derivative.toSignedMeasure + secondWitness.derivative.toSignedMeasure)
  derivative_restrict_openInterval := by
    change (firstWitness.derivative.toSignedMeasure +
      secondWitness.derivative.toSignedMeasure).restrict (Ioo 0 duration) =
        (VagueSignedMeasure.ofSignedMeasure
          (firstWitness.derivative.toSignedMeasure +
            secondWitness.derivative.toSignedMeasure)).toSignedMeasure
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    rw [VectorMeasure.restrict_add, firstWitness.derivative_restrict_openInterval,
      secondWitness.derivative_restrict_openInterval]
  eventuallyEq := firstWitness.eventuallyEq.add secondWitness.eventuallyEq
  rightContinuous := fun time =>
    (firstWitness.rightContinuous time).add (secondWitness.rightContinuous time)
  hasLeftLimit := by
    intro time
    obtain ⟨firstTrace, hFirstTrace⟩ := firstWitness.hasLeftLimit time
    obtain ⟨secondTrace, hSecondTrace⟩ := secondWitness.hasLeftLimit time
    exact ⟨firstTrace + secondTrace, hFirstTrace.add hSecondTrace⟩
  derivative_Ioc := by
    intro start finish hStart hOrder hFinish
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      add_apply,
      firstWitness.derivative_Ioc hStart hOrder hFinish,
      secondWitness.derivative_Ioc hStart hOrder hFinish]
    simp only [Pi.add_apply]
    ring

/-- Multiplication by a real scalar scales the explicit signed derivative. -/
def smul (coefficient : ℝ)
    (witness : ScalarFiniteIntervalCadlagDerivativeWitness first duration) :
    ScalarFiniteIntervalCadlagDerivativeWitness (coefficient • first) duration where
  modification := coefficient • witness.modification
  derivative := VagueSignedMeasure.ofSignedMeasure
    (coefficient • witness.derivative.toSignedMeasure)
  derivative_restrict_openInterval := by
    change (coefficient • witness.derivative.toSignedMeasure).restrict
      (Ioo 0 duration) = (VagueSignedMeasure.ofSignedMeasure
        (coefficient • witness.derivative.toSignedMeasure)).toSignedMeasure
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    rw [VectorMeasure.restrict_smul, witness.derivative_restrict_openInterval]
  eventuallyEq := witness.eventuallyEq.const_smul coefficient
  rightContinuous := fun time => (witness.rightContinuous time).const_smul coefficient
  hasLeftLimit := by
    intro time
    obtain ⟨trace, hTrace⟩ := witness.hasLeftLimit time
    exact ⟨coefficient • trace, hTrace.const_smul coefficient⟩
  derivative_Ioc := by
    intro start finish hStart hOrder hFinish
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      smul_apply,
      witness.derivative_Ioc hStart hOrder hFinish]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- A finite pointwise sum carries the literal sum of its supplied explicit derivatives. -/
def fintypeSum {Index : Type*} [Fintype Index]
    (path : Index → ℝ → ℝ)
    (witness : ∀ index,
      ScalarFiniteIntervalCadlagDerivativeWitness (path index) duration) :
    ScalarFiniteIntervalCadlagDerivativeWitness
      (fun time => ∑ index, path index time) duration where
  modification := fun time => ∑ index, (witness index).modification time
  derivative := VagueSignedMeasure.ofSignedMeasure <|
    ∑ index, (witness index).derivative.toSignedMeasure
  derivative_restrict_openInterval := by
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    calc
      (∑ index, (witness index).derivative.toSignedMeasure).restrict
          (Ioo 0 duration) =
        ∑ index, (witness index).derivative.toSignedMeasure.restrict
          (Ioo 0 duration) :=
        map_sum (VectorMeasure.restrictGm (Ioo 0 duration)) _ Finset.univ
      _ = ∑ index, (witness index).derivative.toSignedMeasure := by
        apply Finset.sum_congr rfl
        intro index _hIndex
        exact (witness index).derivative_restrict_openInterval
  eventuallyEq := by
    have hCoordinate : ∀ index,
        (witness index).modification =ᵐ[finiteOpenIntervalVolume duration]
          path index := fun index => (witness index).eventuallyEq
    filter_upwards [ae_all_iff.mpr hCoordinate] with time hTime
    apply Finset.sum_congr rfl
    intro index _hIndex
    exact hTime index
  rightContinuous := by
    intro time
    exact tendsto_finsetSum Finset.univ fun index _hIndex =>
      (witness index).rightContinuous time
  hasLeftLimit := by
    intro time
    choose trace hTrace using fun index => (witness index).hasLeftLimit time
    exact ⟨∑ index, trace index,
      tendsto_finsetSum Finset.univ fun index _hIndex => hTrace index⟩
  derivative_Ioc := by
    intro start finish hStart hOrder hFinish
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    let evaluation : SignedMeasure ℝ →+ ℝ :=
      { toFun := fun measure => measure (Ioc start finish)
        map_zero' := zero_apply _
        map_add' := fun first second =>
          add_apply first second (Ioc start finish) }
    change evaluation (∑ index,
      (witness index).derivative.toSignedMeasure) = _
    rw [map_sum]
    change (∑ index,
      (witness index).derivative.toSignedMeasure (Ioc start finish)) = _
    simp_rw [(witness _).derivative_Ioc hStart hOrder hFinish]
    rw [Finset.sum_sub_distrib]

end ScalarFiniteIntervalCadlagDerivativeWitness

/-- A weighted Dirac signed measure on the vague carrier. -/
def weightedDiracVagueSignedMeasure
    (eventTime coefficient : ℝ) : VagueSignedMeasure ℝ :=
  VagueSignedMeasure.ofSignedMeasure
    (coefficient • (Measure.dirac eventTime).toSignedMeasure)

/-- The weighted-Dirac map is jointly continuous in event time and weight for the vague topology. -/
theorem continuous_weightedDiracVagueSignedMeasure :
    Continuous fun pair : ℝ × ℝ =>
      weightedDiracVagueSignedMeasure pair.1 pair.2 := by
  rw [VagueSignedMeasure.continuous_iff_continuousTestIntegral]
  intro test
  simp only [weightedDiracVagueSignedMeasure,
    VagueSignedMeasure.continuousTestIntegral_smul_toSignedMeasure,
    integral_dirac]
  exact continuous_snd.mul (test.continuous.comp continuous_fst)

/-- A weighted Dirac derivative confined to the open physical interval. -/
def restrictedWeightedDiracVagueSignedMeasure
    (duration eventTime coefficient : ℝ) : VagueSignedMeasure ℝ :=
  VagueSignedMeasure.ofSignedMeasure <|
    coefficient • ((Measure.dirac eventTime).restrict (Ioo 0 duration)).toSignedMeasure

/-- Restricting a weighted Dirac to physical time either retains the atom or returns zero. -/
theorem restrictedWeightedDiracVagueSignedMeasure_eq_if
    (duration eventTime coefficient : ℝ) :
    restrictedWeightedDiracVagueSignedMeasure duration eventTime coefficient =
      if eventTime ∈ Ioo 0 duration then
        weightedDiracVagueSignedMeasure eventTime coefficient
      else VagueSignedMeasure.zero := by
  unfold restrictedWeightedDiracVagueSignedMeasure
    weightedDiracVagueSignedMeasure VagueSignedMeasure.zero
  by_cases hPhysical : eventTime ∈ Ioo 0 duration
  · rw [ite_eq_left hPhysical]
    apply congrArg VagueSignedMeasure.ofSignedMeasure
    apply congrArg (coefficient • ·)
    apply Measure.toSignedMeasure_congr
    simpa only [ite_eq_left hPhysical] using
      (restrict_dirac (s := Ioo 0 duration) (a := eventTime))
  · rw [ite_eq_right hPhysical]
    apply congrArg VagueSignedMeasure.ofSignedMeasure
    have hRestriction : (Measure.dirac eventTime).restrict (Ioo 0 duration) = 0 := by
      simpa only [ite_eq_right hPhysical] using
        (restrict_dirac (s := Ioo 0 duration) (a := eventTime))
    calc
      coefficient • ((Measure.dirac eventTime).restrict
          (Ioo 0 duration)).toSignedMeasure =
          coefficient • (0 : Measure ℝ).toSignedMeasure := by
        exact congrArg (coefficient • ·)
          (Measure.toSignedMeasure_congr hRestriction)
      _ = 0 := by simp

/-- The physically restricted weighted-Dirac map is Borel measurable.  It is continuous on the
interior and constant off the physical interval, with the boundary split kept explicit. -/
theorem measurable_restrictedWeightedDiracVagueSignedMeasure (duration : ℝ) :
    Measurable fun pair : ℝ × ℝ =>
      restrictedWeightedDiracVagueSignedMeasure duration pair.1 pair.2 := by
  have hPhysical : MeasurableSet {pair : ℝ × ℝ | pair.1 ∈ Ioo 0 duration} :=
    measurableSet_Ioo.preimage measurable_fst
  have hRetained : Measurable fun pair : ℝ × ℝ =>
      weightedDiracVagueSignedMeasure pair.1 pair.2 :=
    continuous_weightedDiracVagueSignedMeasure.measurable
  have hZero : Measurable fun _ : ℝ × ℝ =>
      (VagueSignedMeasure.zero : VagueSignedMeasure ℝ) :=
    measurable_const
  simpa only [restrictedWeightedDiracVagueSignedMeasure_eq_if] using
    Measurable.ite hPhysical hRetained hZero

/-- Finite sum of weighted Dirac atoms on the vague signed-measure carrier. -/
def finiteWeightedDiracVagueSignedMeasure
    {Index : Type*} [Fintype Index]
    (eventTime coefficient : Index → ℝ) : VagueSignedMeasure ℝ :=
  VagueSignedMeasure.ofSignedMeasure <|
    ∑ index, coefficient index • (Measure.dirac (eventTime index)).toSignedMeasure

/-- A continuous test evaluates a finite weighted-Dirac sum by the literal finite weighted
point-evaluation formula. -/
theorem finiteWeightedDiracVagueSignedMeasure_continuousTestIntegral
    {Index : Type*} [Fintype Index]
    (eventTime coefficient : Index → ℝ) (test : C_c(ℝ, ℝ)) :
    (finiteWeightedDiracVagueSignedMeasure eventTime coefficient).continuousTestIntegral test =
      ∑ index, coefficient index * test (eventTime index) := by
  classical
  calc
    _ = ∑ index,
        (weightedDiracVagueSignedMeasure
          (eventTime index) (coefficient index)).continuousTestIntegral test := by
      simpa only [finiteWeightedDiracVagueSignedMeasure,
        weightedDiracVagueSignedMeasure,
        VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
        Finset.sum_filter, Finset.filter_true_of_mem] using
          VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
            (fun index => weightedDiracVagueSignedMeasure
              (eventTime index) (coefficient index)) test
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      unfold weightedDiracVagueSignedMeasure
      rw [VagueSignedMeasure.continuousTestIntegral_smul_toSignedMeasure,
        integral_dirac]

/-- A finite weighted-Dirac sum is continuous whenever every event time and weight is. -/
theorem continuous_finiteWeightedDiracVagueSignedMeasure
    {Index Source : Type*} [Fintype Index] [TopologicalSpace Source]
    (eventTime coefficient : Index → Source → ℝ)
    (hEventTime : ∀ index, Continuous (eventTime index))
    (hCoefficient : ∀ index, Continuous (coefficient index)) :
    Continuous fun source => finiteWeightedDiracVagueSignedMeasure
      (fun index => eventTime index source)
      (fun index => coefficient index source) := by
  classical
  rw [VagueSignedMeasure.continuous_iff_continuousTestIntegral]
  intro test
  rw [show (fun source => (finiteWeightedDiracVagueSignedMeasure
      (fun index => eventTime index source)
      (fun index => coefficient index source)).continuousTestIntegral test) =
      (fun source => ∑ index,
        coefficient index source * test (eventTime index source)) by
    funext source
    exact finiteWeightedDiracVagueSignedMeasure_continuousTestIntegral
      (fun index => eventTime index source)
      (fun index => coefficient index source) test]
  apply continuous_finsetSum Finset.univ
  intro index _hIndex
  exact (hCoefficient index).mul (test.continuous.comp (hEventTime index))

/-- Finite sum of weighted Dirac derivatives after restriction to physical time. -/
def finiteRestrictedWeightedDiracVagueSignedMeasure
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (eventTime coefficient : Index → ℝ) :
    VagueSignedMeasure ℝ :=
  VagueSignedMeasure.ofSignedMeasure <|
    ∑ index, coefficient index •
      ((Measure.dirac (eventTime index)).restrict (Ioo 0 duration)).toSignedMeasure

/-- The total variation of a finite restricted weighted-Dirac derivative is bounded by the sum of
the absolute weights. Atoms outside physical time contribute zero. -/
theorem finiteRestrictedWeightedDiracVagueSignedMeasure_totalVariation_apply_univ_le
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (eventTime coefficient : Index → ℝ) :
    (finiteRestrictedWeightedDiracVagueSignedMeasure
      duration eventTime coefficient).toSignedMeasure.totalVariation Set.univ ≤
        ∑ index, ENNReal.ofReal |coefficient index| := by
  classical
  unfold finiteRestrictedWeightedDiracVagueSignedMeasure
  rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
  calc
    (∑ index, coefficient index •
        ((Measure.dirac (eventTime index)).restrict
          (Ioo 0 duration)).toSignedMeasure).totalVariation Set.univ ≤
        ∑ index,
          (coefficient index •
            ((Measure.dirac (eventTime index)).restrict
              (Ioo 0 duration)).toSignedMeasure).totalVariation Set.univ :=
      SignedMeasure.totalVariation_fintypeSum_apply_univ_le _
    _ = ∑ index, ENNReal.ofReal |coefficient index| *
          ((Measure.dirac (eventTime index)).restrict
            (Ioo 0 duration)).toSignedMeasure.totalVariation Set.univ := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      exact SignedMeasure.totalVariation_smul_apply_univ _ _
    _ ≤ ∑ index, ENNReal.ofReal |coefficient index| := by
      apply Finset.sum_le_sum
      intro index _hIndex
      rw [SignedMeasure.totalVariation_toSignedMeasure]
      by_cases hPhysical : eventTime index ∈ Ioo 0 duration
      · simp [restrict_dirac, hPhysical]
      · simp [restrict_dirac, hPhysical]

/-- When every atom lies strictly inside physical time, restriction preserves the complete
finite weighted-Dirac sum. -/
theorem finiteRestrictedWeightedDiracVagueSignedMeasure_eq_finiteWeighted_of_mem
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (eventTime coefficient : Index → ℝ)
    (hPhysical : ∀ index, eventTime index ∈ Ioo 0 duration) :
    finiteRestrictedWeightedDiracVagueSignedMeasure duration eventTime coefficient =
      finiteWeightedDiracVagueSignedMeasure eventTime coefficient := by
  classical
  unfold finiteRestrictedWeightedDiracVagueSignedMeasure
    finiteWeightedDiracVagueSignedMeasure
  apply congrArg VagueSignedMeasure.ofSignedMeasure
  apply Finset.sum_congr rfl
  intro index _hIndex
  apply congrArg (coefficient index • ·)
  apply Measure.toSignedMeasure_congr
  simpa only [ite_eq_left (hPhysical index)] using
    (restrict_dirac (s := Ioo 0 duration) (a := eventTime index))

/-- Decode one natural number as a candidate finite physical-membership pattern. -/
def decodedFiniteAtomicPattern
    {Index : Type*} [_unusedFintypeIndex : Fintype Index] [Encodable Index]
    (code : ℕ) : Finset Index :=
  (Encodable.decode code).getD ∅

/-- A candidate physical-membership pattern agrees with all supplied event times. -/
def FiniteAtomicPhysicalPatternMatches
    {Index Source : Type*} [_unusedFintypeIndex : Fintype Index]
    (duration : ℝ) (pattern : Finset Index)
    (eventTime : Index → Source → ℝ) (source : Source) : Prop :=
  ∀ index, index ∈ pattern ↔ eventTime index source ∈ Ioo 0 duration

/-- Every finite event family has a coded exact physical-membership pattern. -/
theorem exists_decodedFiniteAtomicPattern_matches
    {Index Source : Type*} [Fintype Index] [Encodable Index]
    (duration : ℝ) (eventTime : Index → Source → ℝ) (source : Source) :
    ∃ code, FiniteAtomicPhysicalPatternMatches duration
      (decodedFiniteAtomicPattern code) eventTime source := by
  classical
  let pattern := Finset.univ.filter fun index =>
    eventTime index source ∈ Ioo 0 duration
  refine ⟨Encodable.encode pattern, ?_⟩
  unfold decodedFiniteAtomicPattern FiniteAtomicPhysicalPatternMatches
  rw [Encodable.encodek]
  intro index
  simp only [Option.getD_some, pattern, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Matching a fixed finite physical-membership pattern is a measurable condition. -/
theorem measurableSet_finiteAtomicPhysicalPatternMatches
    {Index Source : Type*} [Fintype Index] [MeasurableSpace Source]
    (duration : ℝ) (pattern : Finset Index)
    (eventTime : Index → Source → ℝ)
    (hEventTime : ∀ index, Measurable (eventTime index)) :
    MeasurableSet {source | FiniteAtomicPhysicalPatternMatches
      duration pattern eventTime source} := by
  classical
  have hCoordinate (index : Index) : MeasurableSet
      {source | index ∈ pattern ↔ eventTime index source ∈ Ioo 0 duration} := by
    by_cases hIndex : index ∈ pattern
    · have hSet : {source | index ∈ pattern ↔
          eventTime index source ∈ Ioo 0 duration} =
          eventTime index ⁻¹' Ioo 0 duration := by
        ext source
        simp only [Set.mem_ofPred_eq, hIndex, true_iff, Set.mem_preimage]
      rw [hSet]
      exact measurableSet_Ioo.preimage (hEventTime index)
    · have hSet : {source | index ∈ pattern ↔
          eventTime index source ∈ Ioo 0 duration} =
          (eventTime index ⁻¹' Ioo 0 duration)ᶜ := by
        ext source
        simp only [Set.mem_ofPred_eq, hIndex, false_iff,
          Set.mem_compl_iff, Set.mem_preimage]
      rw [hSet]
      exact (measurableSet_Ioo.preimage (hEventTime index)).compl
  have hSet : {source | FiniteAtomicPhysicalPatternMatches
      duration pattern eventTime source} =
      ⋂ index : Index,
        {source | index ∈ pattern ↔ eventTime index source ∈ Ioo 0 duration} := by
    ext source
    simp only [FiniteAtomicPhysicalPatternMatches, Set.mem_ofPred_eq,
      Set.mem_iInter]
  rw [hSet]
  exact MeasurableSet.iInter hCoordinate

/-- Full weighted-Dirac candidate selected by one fixed physical-membership pattern. -/
noncomputable def finiteWeightedDiracVagueSignedMeasureForPattern
    {Index : Type*} [Fintype Index]
    (pattern : Finset Index) (eventTime coefficient : Index → ℝ) :
    VagueSignedMeasure ℝ := by
  classical
  exact VagueSignedMeasure.ofSignedMeasure <|
    ∑ index, if index ∈ pattern then
        coefficient index • (Measure.dirac (eventTime index)).toSignedMeasure
      else 0

/-- A fixed-pattern finite atomic candidate is continuous in all event times and weights. -/
theorem continuous_finiteWeightedDiracVagueSignedMeasureForPattern
    {Index Source : Type*} [Fintype Index] [TopologicalSpace Source]
    (pattern : Finset Index)
    (eventTime coefficient : Index → Source → ℝ)
    (hEventTime : ∀ index, Continuous (eventTime index))
    (hCoefficient : ∀ index, Continuous (coefficient index)) :
    Continuous fun source => finiteWeightedDiracVagueSignedMeasureForPattern pattern
      (fun index => eventTime index source)
      (fun index => coefficient index source) := by
  classical
  rw [VagueSignedMeasure.continuous_iff_continuousTestIntegral]
  intro test
  have hIntegral (source : Source) :
      (finiteWeightedDiracVagueSignedMeasureForPattern pattern
        (fun index => eventTime index source)
        (fun index => coefficient index source)).continuousTestIntegral test =
        ∑ index, if index ∈ pattern then
          coefficient index source * test (eventTime index source) else 0 := by
    calc
      _ = ∑ index,
          (if index ∈ pattern then
            weightedDiracVagueSignedMeasure
              (eventTime index source) (coefficient index source)
          else VagueSignedMeasure.zero).continuousTestIntegral test := by
        simpa only [finiteWeightedDiracVagueSignedMeasureForPattern,
          weightedDiracVagueSignedMeasure, VagueSignedMeasure.zero, apply_ite,
          VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
          Finset.sum_filter, Finset.filter_true_of_mem] using
            VagueSignedMeasure.continuousTestIntegral_finsetSum Finset.univ
              (fun index => if index ∈ pattern then
                weightedDiracVagueSignedMeasure
                  (eventTime index source) (coefficient index source)
                else VagueSignedMeasure.zero) test
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index _hIndex
        by_cases hPattern : index ∈ pattern
        · simp only [hPattern, ite_true]
          unfold weightedDiracVagueSignedMeasure
          rw [VagueSignedMeasure.continuousTestIntegral_smul_toSignedMeasure,
            integral_dirac]
        · simp only [hPattern, ite_false]
          exact VagueSignedMeasure.continuousTestIntegral_zero test
  rw [show (fun source =>
      (finiteWeightedDiracVagueSignedMeasureForPattern pattern
        (fun index => eventTime index source)
        (fun index => coefficient index source)).continuousTestIntegral test) =
      (fun source => ∑ index, if index ∈ pattern then
        coefficient index source * test (eventTime index source) else 0) by
    funext source
    exact hIntegral source]
  apply continuous_finsetSum Finset.univ
  intro index _hIndex
  by_cases hPattern : index ∈ pattern
  · simp only [hPattern, ite_true]
    exact (hCoefficient index).mul (test.continuous.comp (hEventTime index))
  · simp only [hPattern, ite_false]
    exact continuous_const

/-- A matching pattern turns the restricted finite atomic sum into its full-Dirac candidate. -/
theorem finiteRestrictedWeightedDiracVagueSignedMeasure_eq_forPattern
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (pattern : Finset Index)
    (eventTime coefficient : Index → ℝ)
    (hPattern : FiniteAtomicPhysicalPatternMatches duration pattern
      (fun index (_ : Unit) => eventTime index) ()) :
    finiteRestrictedWeightedDiracVagueSignedMeasure duration eventTime coefficient =
      finiteWeightedDiracVagueSignedMeasureForPattern pattern eventTime coefficient := by
  classical
  unfold finiteRestrictedWeightedDiracVagueSignedMeasure
    finiteWeightedDiracVagueSignedMeasureForPattern
  apply congrArg VagueSignedMeasure.ofSignedMeasure
  apply Finset.sum_congr rfl
  intro index _hIndex
  have hMembership := hPattern index
  by_cases hPhysical : eventTime index ∈ Ioo 0 duration
  · rw [ite_eq_left (hMembership.mpr hPhysical)]
    apply congrArg (coefficient index • ·)
    apply Measure.toSignedMeasure_congr
    simpa only [ite_eq_left hPhysical] using
      (restrict_dirac (s := Ioo 0 duration) (a := eventTime index))
  · rw [ite_eq_right (fun hIndex => hPhysical (hMembership.mp hIndex))]
    have hRestriction : (Measure.dirac (eventTime index)).restrict
        (Ioo 0 duration) = 0 := by
      simpa only [ite_eq_right hPhysical] using
        (restrict_dirac (s := Ioo 0 duration) (a := eventTime index))
    calc
      coefficient index • ((Measure.dirac (eventTime index)).restrict
          (Ioo 0 duration)).toSignedMeasure =
          coefficient index • (0 : Measure ℝ).toSignedMeasure := by
        exact congrArg (coefficient index • ·)
          (Measure.toSignedMeasure_congr hRestriction)
      _ = 0 := by simp

/-- A finite family of physically restricted weighted Diracs is Borel measurable. -/
theorem measurable_finiteRestrictedWeightedDiracVagueSignedMeasure
    {Index Source : Type*} [Fintype Index]
    [Encodable Index]
    [MeasurableSpace Source] [TopologicalSpace Source] [OpensMeasurableSpace Source]
    (duration : ℝ) (eventTime coefficient : Index → Source → ℝ)
    (hEventTimeContinuous : ∀ index, Continuous (eventTime index))
    (hCoefficientContinuous : ∀ index, Continuous (coefficient index)) :
    Measurable fun source => finiteRestrictedWeightedDiracVagueSignedMeasure duration
      (fun index => eventTime index source)
      (fun index => coefficient index source) := by
  classical
  let candidate (code : ℕ) (source : Source) :=
    finiteWeightedDiracVagueSignedMeasureForPattern
      (decodedFiniteAtomicPattern code)
      (fun index => eventTime index source)
      (fun index => coefficient index source)
  let patternMatches (code : ℕ) (source : Source) :=
    FiniteAtomicPhysicalPatternMatches duration
      (decodedFiniteAtomicPattern code) eventTime source
  have hCandidate (code : ℕ) : Measurable (candidate code) :=
    (continuous_finiteWeightedDiracVagueSignedMeasureForPattern
      (decodedFiniteAtomicPattern code) eventTime coefficient
      hEventTimeContinuous hCoefficientContinuous).measurable
  have hMatches (code : ℕ) : MeasurableSet {source | patternMatches code source} :=
    measurableSet_finiteAtomicPhysicalPatternMatches duration
      (decodedFiniteAtomicPattern code) eventTime
      (fun index => (hEventTimeContinuous index).measurable)
  have hExists (source : Source) : ∃ code, patternMatches code source :=
    exists_decodedFiniteAtomicPattern_matches duration eventTime source
  have hSelected : Measurable fun source => candidate (Nat.find (hExists source)) source :=
    Measurable.find hCandidate hMatches hExists
  convert hSelected using 1
  funext source
  apply finiteRestrictedWeightedDiracVagueSignedMeasure_eq_forPattern
  intro index
  exact Nat.find_spec (hExists source) index

/-- Right-continuous scalar event step: zero before the event and `coefficient` at and after it. -/
def scalarRightEventStep (eventTime coefficient time : ℝ) : ℝ :=
  if eventTime ≤ time then coefficient else 0

/-- The explicit restricted-Dirac derivative witness of one right-continuous event step. -/
def scalarRightEventStepDerivativeWitness (eventTime coefficient duration : ℝ) :
    ScalarFiniteIntervalCadlagDerivativeWitness
      (scalarRightEventStep eventTime coefficient) duration where
  modification := scalarRightEventStep eventTime coefficient
  derivative := restrictedWeightedDiracVagueSignedMeasure duration eventTime coefficient
  derivative_restrict_openInterval := by
    change (coefficient •
      ((Measure.dirac eventTime).restrict (Ioo 0 duration)).toSignedMeasure).restrict
        (Ioo 0 duration) = (VagueSignedMeasure.ofSignedMeasure
          (coefficient • ((Measure.dirac eventTime).restrict
            (Ioo 0 duration)).toSignedMeasure)).toSignedMeasure
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
    rw [VectorMeasure.restrict_smul,
      Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure
        ((Measure.dirac eventTime).restrict (Ioo 0 duration))
        (Ioo 0 duration) measurableSet_Ioo]
    apply congrArg (coefficient • ·)
    apply Measure.toSignedMeasure_congr
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_self]
  eventuallyEq := Filter.Eventually.of_forall fun _ => rfl
  rightContinuous := by
    intro time
    by_cases hEvent : eventTime ≤ time
    · simpa only [ContinuousWithinAt, scalarRightEventStep, ite_eq_left hEvent] using
        tendsto_const_nhds.congr' (by
          filter_upwards [self_mem_nhdsWithin] with later hLater
          change time ≤ later at hLater
          simp only [scalarRightEventStep, ite_eq_left (hEvent.trans hLater)])
    · have hBefore : time < eventTime := lt_of_not_ge hEvent
      simpa only [ContinuousWithinAt, scalarRightEventStep, ite_eq_right hEvent] using
        tendsto_const_nhds.congr' (by
          filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hBefore)]
            with later hLater
          change later < eventTime at hLater
          simp only [scalarRightEventStep, ite_eq_right (not_le_of_gt hLater)])
  hasLeftLimit := by
    intro time
    by_cases hEvent : eventTime < time
    · refine ⟨coefficient, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hEvent)]
        with earlier hEarlier
      change eventTime < earlier at hEarlier
      simp only [scalarRightEventStep, ite_eq_left hEarlier.le]
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with earlier hEarlier
      have hNotObserved : ¬eventTime ≤ earlier := by
        exact fun hObserved => hEvent (hObserved.trans_lt hEarlier)
      simp only [scalarRightEventStep, ite_eq_right hNotObserved]
  derivative_Ioc := by
    intro start finish hStart hOrder hFinish
    unfold restrictedWeightedDiracVagueSignedMeasure
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      smul_apply,
      Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      measureReal_def,
      Measure.restrict_apply measurableSet_Ioc,
      Measure.dirac_apply' _ (measurableSet_Ioc.inter measurableSet_Ioo)]
    by_cases hEvent : eventTime ∈ Ioc start finish
    · have hPhysical : eventTime ∈ Ioo 0 duration :=
        ⟨hStart.trans_lt hEvent.1, hEvent.2.trans_lt hFinish⟩
      have hCombined : eventTime ∈ Ioc start finish ∩ Ioo 0 duration :=
        ⟨hEvent, hPhysical⟩
      rw [Set.indicator_of_mem hCombined, Pi.one_apply, ENNReal.toReal_one,
        smul_eq_mul, mul_one]
      simp only [scalarRightEventStep, ite_eq_left hEvent.2,
        ite_eq_right (not_le_of_gt hEvent.1), sub_zero]
    · have hIntersection : eventTime ∉ Ioc start finish ∩ Ioo 0 duration :=
        fun membership => hEvent membership.1
      rw [Set.indicator_of_notMem hIntersection, ENNReal.toReal_zero,
        smul_eq_mul, mul_zero]
      rcases not_and_or.mp hEvent with hAtOrBeforeStart | hAfterFinish
      · have hStartObserved : eventTime ≤ start := not_lt.mp hAtOrBeforeStart
        have hFinishObserved : eventTime ≤ finish := hStartObserved.trans hOrder
        simp only [scalarRightEventStep, ite_eq_left hFinishObserved,
          ite_eq_left hStartObserved, sub_self]
      · have hStartNotObserved : ¬eventTime ≤ start :=
          fun hObserved => hAfterFinish (hObserved.trans hOrder)
        simp only [scalarRightEventStep, ite_eq_right hAfterFinish,
          ite_eq_right hStartNotObserved, sub_self]

end

end FiniteMarkovProcesses
