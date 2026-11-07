/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalStepDerivative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Finite-step paths in L1 on a bounded physical interval

This module realizes a right-continuous event step as a genuine element of the open-interval
`L1` quotient.  Moving the event time is continuous in the strong `L1` topology because the
Lebesgue measure of the symmetric difference of two terminal half-lines is their separation.

## Main declarations

- `scalarRightEventStepL1Path`: the exact scalar `L1` event step;
- `continuous_scalarRightEventStepL1Path`: joint strong-`L1` continuity in time and weight;
- `scalarRightEventStepL1Path_eventuallyEq`: recovery of the raw right-continuous step.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The strong-`L1` class of a constant path on the open physical interval. -/
def finiteIntervalConstantL1Path
    {Value : Type*} [NormedAddCommGroup Value]
    (duration : ℝ) (value : Value) : Lp Value 1 (finiteOpenIntervalVolume duration) :=
  indicatorConstLp 1 MeasurableSet.univ
    (measure_ne_top (finiteOpenIntervalVolume duration) Set.univ) value

/-- The quotient constant path equals its raw constant representative almost everywhere. -/
theorem finiteIntervalConstantL1Path_eventuallyEq
    {Value : Type*} [NormedAddCommGroup Value]
    (duration : ℝ) (value : Value) :
    (finiteIntervalConstantL1Path duration value : ℝ → Value)
      =ᵐ[finiteOpenIntervalVolume duration] fun _ => value := by
  have hIndicator := indicatorConstLp_coeFn
    (p := (1 : ENNReal)) (μ := finiteOpenIntervalVolume duration)
    (hs := MeasurableSet.univ)
    (hμs := measure_ne_top (finiteOpenIntervalVolume duration) Set.univ)
    (c := value)
  filter_upwards [hIndicator] with time hTime
  change (indicatorConstLp 1 MeasurableSet.univ
    (measure_ne_top (finiteOpenIntervalVolume duration) Set.univ) value : ℝ → Value) time =
      value
  simpa only [Set.indicator_univ] using hTime

/-- Constant-path insertion is a continuous real-linear map into the bounded-interval `L1`
carrier. -/
def finiteIntervalConstantL1PathContinuousLinearMap
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (duration : ℝ) :
    Value →L[ℝ] Lp Value 1 (finiteOpenIntervalVolume duration) :=
  LinearMap.mkContinuous
    { toFun := finiteIntervalConstantL1Path duration
      map_add' := fun first second => by
        exact indicatorConstLp_add.symm
      map_smul' := fun coefficient value => by
        unfold finiteIntervalConstantL1Path indicatorConstLp
        simp only [Set.indicator_univ, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun _ => by simp }
    ((finiteOpenIntervalVolume duration Set.univ).toReal)
    fun value => by
      change ‖indicatorConstLp 1 MeasurableSet.univ
        (measure_ne_top (finiteOpenIntervalVolume duration) Set.univ) value‖ ≤
          ((finiteOpenIntervalVolume duration) Set.univ).toReal * ‖value‖
      simpa only [Measure.real_def, ENNReal.toReal_one,
        one_div, inv_one, Real.rpow_one, mul_comm] using
          (norm_indicatorConstLp_le
            (p := (1 : ENNReal))
            (hs := MeasurableSet.univ)
            (hμs := measure_ne_top
              (finiteOpenIntervalVolume duration) Set.univ)
            (c := value))

/-- Constant strong-`L1` paths depend continuously on their value. -/
theorem continuous_finiteIntervalConstantL1Path
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (duration : ℝ) :
    Continuous fun value : Value => finiteIntervalConstantL1Path duration value :=
  (finiteIntervalConstantL1PathContinuousLinearMap duration).continuous

/-- The volume of the symmetric difference of two terminal half-lines is their separation. -/
theorem volume_symmDiff_Ici (first second : ℝ) :
    volume (symmDiff (Ici first) (Ici second)) =
      ENNReal.ofReal |second - first| := by
  rcases le_total first second with hOrder | hOrder
  · have hSet : symmDiff (Ici first) (Ici second) = Ico first second := by
      ext point
      simp only [mem_symmDiff, mem_Ici, mem_Ico]
      constructor
      · rintro (hFirst | hSecond)
        · exact ⟨hFirst.1, lt_of_not_ge hFirst.2⟩
        · exact False.elim (hSecond.2 (hOrder.trans hSecond.1))
      · intro hPoint
        exact Or.inl ⟨hPoint.1, not_le_of_gt hPoint.2⟩
    rw [hSet, Real.volume_Ico, abs_of_nonneg (sub_nonneg.mpr hOrder)]
  · have hSet : symmDiff (Ici first) (Ici second) = Ico second first := by
      ext point
      simp only [mem_symmDiff, mem_Ici, mem_Ico]
      constructor
      · rintro (hFirst | hSecond)
        · exact False.elim (hFirst.2 (hOrder.trans hFirst.1))
        · exact ⟨hSecond.1, lt_of_not_ge hSecond.2⟩
      · intro hPoint
        exact Or.inr ⟨hPoint.1, not_le_of_gt hPoint.2⟩
    rw [hSet, Real.volume_Ico, abs_of_nonpos (sub_nonpos.mpr hOrder)]
    ring_nf

/-- Terminal half-lines vary continuously in symmetric-difference measure after restriction to
the bounded physical interval. -/
theorem tendsto_finiteOpenIntervalVolume_symmDiff_Ici
    (duration eventTime : ℝ) :
    Tendsto (fun later => finiteOpenIntervalVolume duration
      (symmDiff (Ici later) (Ici eventTime)))
      (nhds eventTime) (nhds 0) := by
  have hUpper : Tendsto (fun later : ℝ => ENNReal.ofReal |eventTime - later|)
      (nhds eventTime) (nhds 0) := by
    have hContinuous : Continuous fun later : ℝ =>
        ENNReal.ofReal |eventTime - later| :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_const.sub continuous_id))
    simpa only [sub_self, abs_zero, ENNReal.ofReal_zero] using
      hContinuous.tendsto eventTime
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · apply Filter.Eventually.of_forall
    intro later
    rw [finiteOpenIntervalVolume,
      Measure.restrict_apply (measurableSet_Ici.symmDiff measurableSet_Ici)]
    calc
      volume (symmDiff (Ici later) (Ici eventTime) ∩ Ioo 0 duration) ≤
          volume (symmDiff (Ici later) (Ici eventTime)) :=
        measure_mono inter_subset_left
      _ = ENNReal.ofReal |eventTime - later| :=
        volume_symmDiff_Ici later eventTime

/-- The scalar strong-`L1` class of a weighted right-continuous event step. -/
def scalarRightEventStepL1Path
    (duration eventTime coefficient : ℝ) : Lp ℝ 1 (finiteOpenIntervalVolume duration) :=
  coefficient • indicatorConstLp 1 measurableSet_Ici
    (measure_ne_top (finiteOpenIntervalVolume duration) (Ici eventTime)) (1 : ℝ)

/-- Moving an event time and its scalar weight is jointly continuous in strong `L1`. -/
theorem continuous_scalarRightEventStepL1Path (duration : ℝ) :
    Continuous fun pair : ℝ × ℝ =>
      scalarRightEventStepL1Path duration pair.1 pair.2 := by
  have hEvent : Continuous fun eventTime : ℝ =>
      indicatorConstLp 1 measurableSet_Ici
        (measure_ne_top (finiteOpenIntervalVolume duration) (Ici eventTime)) (1 : ℝ) :=
    continuous_indicatorConstLp_set ENNReal.one_ne_top fun eventTime =>
      tendsto_finiteOpenIntervalVolume_symmDiff_Ici duration eventTime
  exact continuous_snd.smul (hEvent.comp continuous_fst)

/-- The scalar quotient has the raw right-continuous event step as a representative. -/
theorem scalarRightEventStepL1Path_eventuallyEq
    (duration eventTime coefficient : ℝ) :
    (scalarRightEventStepL1Path duration eventTime coefficient : ℝ → ℝ)
      =ᵐ[finiteOpenIntervalVolume duration]
        scalarRightEventStep eventTime coefficient := by
  have hIndicator := indicatorConstLp_coeFn
    (p := (1 : ENNReal)) (μ := finiteOpenIntervalVolume duration)
    (hs := measurableSet_Ici)
    (hμs := measure_ne_top (finiteOpenIntervalVolume duration) (Ici eventTime))
    (c := (1 : ℝ))
  have hScalar := Lp.coeFn_smul coefficient
    (indicatorConstLp 1 measurableSet_Ici
      (measure_ne_top (finiteOpenIntervalVolume duration) (Ici eventTime)) (1 : ℝ))
  filter_upwards [hIndicator, hScalar] with time hTime hScalarTime
  unfold scalarRightEventStepL1Path scalarRightEventStep
  rw [hScalarTime, Pi.smul_apply, hTime]
  by_cases hObserved : eventTime ≤ time
  · simp [hObserved]
  · simp [hObserved]

universe u

variable {Coordinate : Type u} [Fintype Coordinate] [DecidableEq Coordinate]

/-- The unit vector of one coordinate in the finite `l1` value space. -/
def finiteCoordinateL1BasisVector
    (coordinate : Coordinate) : FiniteCoordinateL1Value Coordinate :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Coordinate => ℝ)).symm
    (Pi.single coordinate 1)

omit [Fintype Coordinate] in
/-- Evaluation of a finite `l1` unit vector. -/
@[simp]
theorem finiteCoordinateL1BasisVector_apply
    (coordinate query : Coordinate) :
    finiteCoordinateL1BasisVector coordinate query =
      if coordinate = query then 1 else 0 := by
  have hCoordinate := congrFun
    ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Coordinate => ℝ)).apply_symm_apply
      (Pi.single coordinate 1)) query
  simpa only [finiteCoordinateL1BasisVector,
    PiLp.continuousLinearEquiv_apply, Pi.single_apply, eq_comm] using hCoordinate

/-- Embed a scalar `L1` path into one named coordinate of a finite-coordinate path. -/
def embedScalarFiniteIntervalL1PathAtCoordinate
    (duration : ℝ) (coordinate : Coordinate) :
    Lp ℝ 1 (finiteOpenIntervalVolume duration) →L[ℝ]
      FiniteIntervalL1Path Coordinate duration :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (finiteCoordinateL1BasisVector coordinate)).compLpL
      1 (finiteOpenIntervalVolume duration)

/-- One weighted event step embedded into a named coordinate of the finite path carrier. -/
def finiteCoordinateRightEventStepL1Path
    (duration : ℝ) (coordinate : Coordinate)
    (eventTime coefficient : ℝ) : FiniteIntervalL1Path Coordinate duration :=
  embedScalarFiniteIntervalL1PathAtCoordinate duration coordinate
    (scalarRightEventStepL1Path duration eventTime coefficient)

/-- A named-coordinate event step is jointly continuous in event time and weight. -/
theorem continuous_finiteCoordinateRightEventStepL1Path
    (duration : ℝ) (coordinate : Coordinate) :
    Continuous fun pair : ℝ × ℝ =>
      finiteCoordinateRightEventStepL1Path
        duration coordinate pair.1 pair.2 :=
  (embedScalarFiniteIntervalL1PathAtCoordinate duration coordinate).continuous.comp
    (continuous_scalarRightEventStepL1Path duration)

/-- A named-coordinate event step is Borel measurable. -/
theorem measurable_finiteCoordinateRightEventStepL1Path
    (duration : ℝ) (coordinate : Coordinate) :
    Measurable fun pair : ℝ × ℝ =>
      finiteCoordinateRightEventStepL1Path
        duration coordinate pair.1 pair.2 :=
  (continuous_finiteCoordinateRightEventStepL1Path duration coordinate).measurable

/-- The named-coordinate event-step constructor is jointly measurable when the coordinate is
drawn from a finite measurable space. -/
theorem measurable_finiteCoordinateRightEventStepL1Path_joint
    [MeasurableSpace Coordinate] [MeasurableSingletonClass Coordinate]
    (duration : ℝ) :
    Measurable fun input : Coordinate × (ℝ × ℝ) =>
      finiteCoordinateRightEventStepL1Path
        duration input.1 input.2.1 input.2.2 := by
  let summand (coordinate : Coordinate) (input : Coordinate × (ℝ × ℝ)) :=
    if input.1 = coordinate then
      finiteCoordinateRightEventStepL1Path
        duration coordinate input.2.1 input.2.2
    else 0
  have hSummand (coordinate : Coordinate) :
      Measurable (summand coordinate) := by
    have hCoordinate : MeasurableSet
        {input : Coordinate × (ℝ × ℝ) | input.1 = coordinate} :=
      (measurable_fst.eq measurable_const).setOf
    have hStep : Measurable fun input : Coordinate × (ℝ × ℝ) =>
        finiteCoordinateRightEventStepL1Path
          duration coordinate input.2.1 input.2.2 :=
      (measurable_finiteCoordinateRightEventStepL1Path duration coordinate).comp
        measurable_snd
    exact Measurable.ite hCoordinate hStep measurable_const
  have hSum : Measurable fun input : Coordinate × (ℝ × ℝ) =>
      ∑ coordinate, summand coordinate input :=
    Finset.measurable_sum Finset.univ fun coordinate _hCoordinate =>
      hSummand coordinate
  convert hSum using 1
  funext input
  simp only [summand]
  rw [Finset.sum_eq_single input.1]
  · simp
  · intro coordinate _hCoordinate hDifferent
    simp [Ne.symm hDifferent]
  · simp

/-- The embedded quotient recovers the corresponding basis-valued raw event step almost
everywhere on physical time. -/
theorem finiteCoordinateRightEventStepL1Path_eventuallyEq
    (duration : ℝ) (coordinate : Coordinate)
    (eventTime coefficient : ℝ) :
    (finiteCoordinateRightEventStepL1Path duration coordinate eventTime coefficient :
        ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[finiteOpenIntervalVolume duration]
        fun time => scalarRightEventStep eventTime coefficient time •
          finiteCoordinateL1BasisVector coordinate := by
  have hEmbedding :=
    (ContinuousLinearMap.toSpanSingleton ℝ
      (finiteCoordinateL1BasisVector coordinate)).coeFn_compLp
        (scalarRightEventStepL1Path duration eventTime coefficient)
  have hScalar := scalarRightEventStepL1Path_eventuallyEq
    duration eventTime coefficient
  filter_upwards [hEmbedding, hScalar] with time hEmbeddingTime hScalarTime
  unfold finiteCoordinateRightEventStepL1Path
    embedScalarFiniteIntervalL1PathAtCoordinate
  change (((ContinuousLinearMap.toSpanSingleton ℝ
      (finiteCoordinateL1BasisVector coordinate)).compLp
        (scalarRightEventStepL1Path duration eventTime coefficient) :
          FiniteIntervalL1Path Coordinate duration) :
            ℝ → FiniteCoordinateL1Value Coordinate) time = _
  rw [hEmbeddingTime, ContinuousLinearMap.toSpanSingleton_apply, hScalarTime]

/-- A finite family of coordinate-labelled event steps in the strong `L1` carrier. -/
def finiteCoordinateEventStepL1PathSum
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (coordinate : Index → Coordinate)
    (eventTime coefficient : Index → ℝ) :
    FiniteIntervalL1Path Coordinate duration :=
  ∑ index, finiteCoordinateRightEventStepL1Path
    duration (coordinate index) (eventTime index) (coefficient index)

/-- The finite strong-`L1` sum recovers the literal sum of its basis-valued event steps almost
everywhere. -/
theorem finiteCoordinateEventStepL1PathSum_eventuallyEq
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (coordinate : Index → Coordinate)
    (eventTime coefficient : Index → ℝ) :
    (finiteCoordinateEventStepL1PathSum duration coordinate eventTime coefficient :
        ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[finiteOpenIntervalVolume duration]
        fun time => ∑ index, scalarRightEventStep
          (eventTime index) (coefficient index) time •
            finiteCoordinateL1BasisVector (coordinate index) := by
  have hTerm (index : Index) := finiteCoordinateRightEventStepL1Path_eventuallyEq
    duration (coordinate index) (eventTime index) (coefficient index)
  have hFinset : ∀ indices : Finset Index,
      ((∑ index ∈ indices, finiteCoordinateRightEventStepL1Path
          duration (coordinate index) (eventTime index) (coefficient index) :
            FiniteIntervalL1Path Coordinate duration) :
              ℝ → FiniteCoordinateL1Value Coordinate)
        =ᵐ[finiteOpenIntervalVolume duration]
          fun time => ∑ index ∈ indices, scalarRightEventStep
            (eventTime index) (coefficient index) time •
              finiteCoordinateL1BasisVector (coordinate index) := by
    classical
    intro indices
    induction indices using Finset.induction_on with
    | empty =>
        have hZero := Lp.coeFn_zero (E := FiniteCoordinateL1Value Coordinate)
          (p := (1 : ENNReal)) (μ := finiteOpenIntervalVolume duration)
        filter_upwards [hZero] with time hTime
        simpa only [Finset.sum_empty, Pi.zero_apply] using hTime
    | @insert index indices hFresh hInduction =>
        have hAdd := Lp.coeFn_add
          (finiteCoordinateRightEventStepL1Path
            duration (coordinate index) (eventTime index) (coefficient index))
          (∑ other ∈ indices, finiteCoordinateRightEventStepL1Path
            duration (coordinate other) (eventTime other) (coefficient other))
        have hTotal := hAdd.trans ((hTerm index).add hInduction)
        filter_upwards [hTotal] with time hTime
        simpa only [Finset.sum_insert hFresh, Finset.sum_apply, Pi.add_apply] using hTime
  simpa only [finiteCoordinateEventStepL1PathSum, Finset.sum_apply] using
    hFinset Finset.univ

/-- Every finite `l1` value is the sum of its named-coordinate basis components. -/
theorem sum_apply_smul_finiteCoordinateL1BasisVector
    (value : FiniteCoordinateL1Value Coordinate) :
    ∑ coordinate, value coordinate • finiteCoordinateL1BasisVector coordinate = value := by
  apply (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Coordinate => ℝ)).injective
  funext query
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul,
    PiLp.continuousLinearEquiv_apply, Pi.smul_apply, smul_eq_mul,
    finiteCoordinateL1BasisVector_apply]
  change (∑ coordinate, value coordinate *
    (if coordinate = query then 1 else 0)) = value query
  rw [Finset.sum_eq_single query]
  · simp
  · intro coordinate _hCoordinate hDifferent
    simp [hDifferent]
  · simp

/-- One vector-valued right event step, expanded over the named finite coordinates. -/
def finiteCoordinateVectorRightEventStepL1Path
    (duration eventTime : ℝ) (value : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path Coordinate duration :=
  ∑ coordinate, finiteCoordinateRightEventStepL1Path
    duration coordinate eventTime (value coordinate)

/-- At a fixed event time, vector-valued right-event insertion is a continuous linear map into
the strong-`L1` path carrier. -/
def finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap
    (duration eventTime : ℝ) :
    FiniteCoordinateL1Value Coordinate →L[ℝ]
      FiniteIntervalL1Path Coordinate duration :=
  ∑ coordinate,
    (embedScalarFiniteIntervalL1PathAtCoordinate duration coordinate).comp
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (indicatorConstLp 1 measurableSet_Ici
          (measure_ne_top (finiteOpenIntervalVolume duration) (Ici eventTime)) (1 : ℝ))).comp
        (PiLp.proj (𝕜 := ℝ) (p := 1)
          (fun _ : Coordinate => ℝ) coordinate))

/-- The fixed-time continuous linear event insertion agrees with the pointwise constructor. -/
@[simp]
theorem finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap_apply
    (duration eventTime : ℝ) (value : FiniteCoordinateL1Value Coordinate) :
    finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap
        duration eventTime value =
      finiteCoordinateVectorRightEventStepL1Path duration eventTime value := by
  unfold finiteCoordinateVectorRightEventStepL1PathContinuousLinearMap
    finiteCoordinateVectorRightEventStepL1Path
    finiteCoordinateRightEventStepL1Path scalarRightEventStepL1Path
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, PiLp.proj_apply]

/-- A vector-valued event step is jointly continuous in its event time and increment. -/
theorem continuous_finiteCoordinateVectorRightEventStepL1Path
    (duration : ℝ) :
    Continuous fun pair : ℝ × FiniteCoordinateL1Value Coordinate =>
      finiteCoordinateVectorRightEventStepL1Path duration pair.1 pair.2 := by
  apply continuous_finsetSum Finset.univ
  intro coordinate _hCoordinate
  exact (continuous_finiteCoordinateRightEventStepL1Path duration coordinate).comp
    (continuous_fst.prodMk
      ((PiLp.proj (𝕜 := ℝ) (p := 1)
        (fun _ : Coordinate => ℝ) coordinate).continuous.comp continuous_snd))

/-- The vector-valued quotient event step recovers the corresponding raw step almost
everywhere. -/
theorem finiteCoordinateVectorRightEventStepL1Path_eventuallyEq
    (duration eventTime : ℝ) (value : FiniteCoordinateL1Value Coordinate) :
    (finiteCoordinateVectorRightEventStepL1Path duration eventTime value :
        ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[finiteOpenIntervalVolume duration]
        fun time => scalarRightEventStep eventTime 1 time • value := by
  have hSum := finiteCoordinateEventStepL1PathSum_eventuallyEq
    (Coordinate := Coordinate) duration (fun coordinate => coordinate)
      (fun _coordinate => eventTime) (fun coordinate => value coordinate)
  filter_upwards [hSum] with time hTime
  have hExpanded :
      (finiteCoordinateVectorRightEventStepL1Path duration eventTime value :
          ℝ → FiniteCoordinateL1Value Coordinate) time =
        ∑ coordinate, scalarRightEventStep eventTime (value coordinate) time •
          finiteCoordinateL1BasisVector coordinate := by
    simpa only [finiteCoordinateVectorRightEventStepL1Path,
      finiteCoordinateEventStepL1PathSum] using hTime
  rw [hExpanded]
  by_cases hObserved : eventTime ≤ time
  · simp only [scalarRightEventStep, ite_eq_left hObserved, one_smul]
    exact sum_apply_smul_finiteCoordinateL1BasisVector value
  · simp only [scalarRightEventStep, ite_eq_right hObserved, zero_smul,
      Finset.sum_const_zero]

/-- A finite family of vector-valued right event steps in the strong `L1` carrier. -/
def finiteCoordinateVectorEventStepL1PathSum
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (eventTime : Index → ℝ)
    (value : Index → FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path Coordinate duration :=
  ∑ index, finiteCoordinateVectorRightEventStepL1Path
    duration (eventTime index) (value index)

/-- A finite vector-event sum recovers the literal sum of raw vector steps almost everywhere. -/
theorem finiteCoordinateVectorEventStepL1PathSum_eventuallyEq
    {Index : Type*} [Fintype Index]
    (duration : ℝ) (eventTime : Index → ℝ)
    (value : Index → FiniteCoordinateL1Value Coordinate) :
    (finiteCoordinateVectorEventStepL1PathSum duration eventTime value :
        ℝ → FiniteCoordinateL1Value Coordinate)
      =ᵐ[finiteOpenIntervalVolume duration]
        fun time => ∑ index,
          scalarRightEventStep (eventTime index) 1 time • value index := by
  have hTerm (index : Index) :=
    finiteCoordinateVectorRightEventStepL1Path_eventuallyEq
      duration (eventTime index) (value index)
  have hFinset : ∀ indices : Finset Index,
      ((∑ index ∈ indices, finiteCoordinateVectorRightEventStepL1Path
          duration (eventTime index) (value index) :
            FiniteIntervalL1Path Coordinate duration) :
              ℝ → FiniteCoordinateL1Value Coordinate)
        =ᵐ[finiteOpenIntervalVolume duration]
          fun time => ∑ index ∈ indices,
            scalarRightEventStep (eventTime index) 1 time • value index := by
    classical
    intro indices
    induction indices using Finset.induction_on with
    | empty =>
        have hZero := Lp.coeFn_zero (E := FiniteCoordinateL1Value Coordinate)
          (p := (1 : ENNReal)) (μ := finiteOpenIntervalVolume duration)
        filter_upwards [hZero] with time hTime
        simpa only [Finset.sum_empty, Pi.zero_apply] using hTime
    | @insert index indices hFresh hInduction =>
        have hAdd := Lp.coeFn_add
          (finiteCoordinateVectorRightEventStepL1Path
            duration (eventTime index) (value index))
          (∑ other ∈ indices, finiteCoordinateVectorRightEventStepL1Path
            duration (eventTime other) (value other))
        have hTotal := hAdd.trans ((hTerm index).add hInduction)
        filter_upwards [hTotal] with time hTime
        simpa only [Finset.sum_insert hFresh, Finset.sum_apply, Pi.add_apply] using hTime
  simpa only [finiteCoordinateVectorEventStepL1PathSum, Finset.sum_apply] using
    hFinset Finset.univ

end

end FiniteMarkovProcesses
