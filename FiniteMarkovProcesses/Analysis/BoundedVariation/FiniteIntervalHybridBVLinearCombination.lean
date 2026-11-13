/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath

/-!
# Linear combinations of finite-interval hybrid BV paths

This module constructs a linear combination on the actual hybrid derivative graph.  The
strong-`L1` representative, every signed Stieltjes derivative, and both recovered boundary traces
are combined with the same two real coefficients.  In particular, the construction does not use
an arbitrary bounded-variation derivative witness.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

universe u

noncomputable section

namespace FiniteIntervalHybridBVPath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Pointwise linear combination of the selected càdlàg representatives. -/
def linearCombinationRepresentative
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    ℝ → FiniteCoordinateL1Value Coordinate :=
  fun time =>
    firstCoefficient • first.cadlagRepresentative.representative time +
      secondCoefficient • second.cadlagRepresentative.representative time

/-- The linear combination of two selected representatives is integrable on physical time. -/
theorem memLp_linearCombinationRepresentative
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    MemLp
      (linearCombinationRepresentative firstCoefficient secondCoefficient first second)
      1 (finiteOpenIntervalVolume duration) := by
  have hFirst :
      MemLp first.cadlagRepresentative.representative 1
        (finiteOpenIntervalVolume duration) :=
    Classical.choose first.cadlagRepresentative.represents
  have hSecond :
      MemLp second.cadlagRepresentative.representative 1
        (finiteOpenIntervalVolume duration) :=
    Classical.choose second.cadlagRepresentative.represents
  simpa only [linearCombinationRepresentative] using!
    (hFirst.const_smul firstCoefficient).add (hSecond.const_smul secondCoefficient)

/-- Strong-`L1` quotient of the pointwise representative linear combination. -/
noncomputable def linearCombinationL1Path
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalL1Path Coordinate duration :=
  FiniteIntervalL1Path.ofFunction
    (linearCombinationRepresentative firstCoefficient secondCoefficient first second)
    (memLp_linearCombinationRepresentative firstCoefficient secondCoefficient first second)

/-- The raw linear combination represents its quotient definitionally. -/
theorem linearCombinationRepresentative_represents
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalL1Path.Represents
      (linearCombinationL1Path firstCoefficient secondCoefficient first second)
      (linearCombinationRepresentative firstCoefficient secondCoefficient first second) := by
  exact
    ⟨memLp_linearCombinationRepresentative
      firstCoefficient secondCoefficient first second, rfl⟩

/-- The linear-combination quotient has bounded variation. -/
theorem linearCombinationL1Path_hasBoundedVariation
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalL1Path.HasBoundedVariation
      (linearCombinationL1Path firstCoefficient secondCoefficient first second) := by
  obtain ⟨firstRepresentative, hFirstRepresents, hFirstVariation⟩ :=
    (FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative
      first.toDerivativePath.toL1Path).mp first.hasBoundedVariation
  obtain ⟨secondRepresentative, hSecondRepresents, hSecondVariation⟩ :=
    (FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative
      second.toDerivativePath.toL1Path).mp second.hasBoundedVariation
  let representative : ℝ → FiniteCoordinateL1Value Coordinate := fun time =>
    firstCoefficient • firstRepresentative time +
      secondCoefficient • secondRepresentative time
  have hFirstMemLp :
      MemLp firstRepresentative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose hFirstRepresents
  have hSecondMemLp :
      MemLp secondRepresentative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose hSecondRepresents
  have hRepresentativeMemLp :
      MemLp representative 1 (finiteOpenIntervalVolume duration) := by
    exact (hFirstMemLp.const_smul firstCoefficient).add
      (hSecondMemLp.const_smul secondCoefficient)
  have hFirstEventually :
      firstRepresentative =ᵐ[finiteOpenIntervalVolume duration]
        first.cadlagRepresentative.representative := by
    have hFirstCadlagMemLp :
        MemLp first.cadlagRepresentative.representative 1
          (finiteOpenIntervalVolume duration) :=
      Classical.choose first.cadlagRepresentative.represents
    exact
      ((FiniteIntervalL1Path.represents_iff_eventuallyEq
        first.toDerivativePath.toL1Path firstRepresentative hFirstMemLp).mp
          hFirstRepresents).trans
        ((FiniteIntervalL1Path.represents_iff_eventuallyEq
          first.toDerivativePath.toL1Path first.cadlagRepresentative.representative
            hFirstCadlagMemLp).mp first.cadlagRepresentative.represents).symm
  have hSecondEventually :
      secondRepresentative =ᵐ[finiteOpenIntervalVolume duration]
        second.cadlagRepresentative.representative := by
    have hSecondCadlagMemLp :
        MemLp second.cadlagRepresentative.representative 1
          (finiteOpenIntervalVolume duration) :=
      Classical.choose second.cadlagRepresentative.represents
    exact
      ((FiniteIntervalL1Path.represents_iff_eventuallyEq
        second.toDerivativePath.toL1Path secondRepresentative hSecondMemLp).mp
          hSecondRepresents).trans
        ((FiniteIntervalL1Path.represents_iff_eventuallyEq
          second.toDerivativePath.toL1Path second.cadlagRepresentative.representative
            hSecondCadlagMemLp).mp second.cadlagRepresentative.represents).symm
  have hEventually :
      representative =ᵐ[finiteOpenIntervalVolume duration]
        linearCombinationRepresentative
          firstCoefficient secondCoefficient first second := by
    filter_upwards [hFirstEventually, hSecondEventually] with time hFirstTime hSecondTime
    simp only [representative, linearCombinationRepresentative, hFirstTime, hSecondTime]
  have hRepresents :
      FiniteIntervalL1Path.Represents
        (linearCombinationL1Path firstCoefficient secondCoefficient first second)
        representative := by
    apply (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (linearCombinationL1Path firstCoefficient secondCoefficient first second)
      representative hRepresentativeMemLp).mpr
    exact hEventually.trans <|
      (FiniteIntervalL1Path.represents_iff_eventuallyEq
        (linearCombinationL1Path firstCoefficient secondCoefficient first second)
        (linearCombinationRepresentative firstCoefficient secondCoefficient first second)
        (memLp_linearCombinationRepresentative
          firstCoefficient secondCoefficient first second)).mp
          (linearCombinationRepresentative_represents
            firstCoefficient secondCoefficient first second)
  apply FiniteIntervalL1Path.hasBoundedVariation_of_represents
    (linearCombinationL1Path firstCoefficient secondCoefficient first second)
    representative hRepresents
  exact FiniteIntervalBVAlgebra.boundedVariationOn_add
    ((lipschitzWith_smul firstCoefficient).comp_boundedVariationOn hFirstVariation)
    ((lipschitzWith_smul secondCoefficient).comp_boundedVariationOn hSecondVariation)

/-- The explicit càdlàg representative of the linear-combination quotient. -/
noncomputable def linearCombinationCadlagRepresentative
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalCadlagRepresentative
      (linearCombinationL1Path firstCoefficient secondCoefficient first second) where
  representative :=
    linearCombinationRepresentative firstCoefficient secondCoefficient first second
  represents := linearCombinationRepresentative_represents
    firstCoefficient secondCoefficient first second
  rightContinuous := by
    intro time hTime
    exact
      ((first.cadlagRepresentative.rightContinuous time hTime).const_smul firstCoefficient).add
        ((second.cadlagRepresentative.rightContinuous time hTime).const_smul secondCoefficient)
  hasLeftLimit := by
    intro time hTime
    obtain ⟨firstTrace, hFirstTrace⟩ :=
      first.cadlagRepresentative.hasLeftLimit time hTime
    obtain ⟨secondTrace, hSecondTrace⟩ :=
      second.cadlagRepresentative.hasLeftLimit time hTime
    exact
      ⟨firstCoefficient • firstTrace + secondCoefficient • secondTrace,
        (hFirstTrace.const_smul firstCoefficient).add
          (hSecondTrace.const_smul secondCoefficient)⟩

/-- Linear combination on the genuine hybrid derivative graph. -/
noncomputable def linearCombination
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalHybridBVPath Coordinate duration := by
  let derivativePath : FiniteIntervalL1DerivativePath Coordinate duration :=
    { toL1Path :=
        linearCombinationL1Path firstCoefficient secondCoefficient first second
      derivative := fun coordinate => VagueSignedMeasure.ofSignedMeasure <|
        firstCoefficient •
            (first.toDerivativePath.derivative coordinate).toSignedMeasure +
          secondCoefficient •
            (second.toDerivativePath.derivative coordinate).toSignedMeasure }
  refine
    { toDerivativePath := derivativePath
      hasBoundedVariation :=
        linearCombinationL1Path_hasBoundedVariation
          firstCoefficient secondCoefficient first second
      hasCadlagDerivativeRealization := ?_ }
  refine
    ⟨linearCombinationCadlagRepresentative
      firstCoefficient secondCoefficient first second, ?_, ?_⟩
  · intro coordinate
    change
      (firstCoefficient •
          (first.toDerivativePath.derivative coordinate).toSignedMeasure +
        secondCoefficient •
          (second.toDerivativePath.derivative coordinate).toSignedMeasure).restrict
          (Ioo 0 duration) = _
    rw [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_smul,
      (Classical.choose_spec first.hasCadlagDerivativeRealization).1 coordinate,
      (Classical.choose_spec second.hasCadlagDerivativeRealization).1 coordinate]
  · intro coordinate start finish hStart hOrder hFinish
    rw [show derivativePath.derivative coordinate = VagueSignedMeasure.ofSignedMeasure
        (firstCoefficient •
            (first.toDerivativePath.derivative coordinate).toSignedMeasure +
          secondCoefficient •
            (second.toDerivativePath.derivative coordinate).toSignedMeasure) by rfl,
      VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
      _root_.add_apply, _root_.smul_apply, _root_.smul_apply,
      first.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
        hStart hOrder hFinish,
      second.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
        hStart hOrder hFinish]
    simp only [linearCombinationCadlagRepresentative,
      linearCombinationRepresentative, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring

/-- Every derivative coordinate is the literal signed-measure linear combination. -/
@[simp]
theorem linearCombination_derivative
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate) :
    (linearCombination firstCoefficient secondCoefficient first second).toDerivativePath.derivative
        coordinate =
      VagueSignedMeasure.ofSignedMeasure
        (firstCoefficient •
            (first.toDerivativePath.derivative coordinate).toSignedMeasure +
          secondCoefficient •
            (second.toDerivativePath.derivative coordinate).toSignedMeasure) := by
  rfl

/-- The canonical representative agrees with the explicit pointwise combination on `[0,T)`. -/
theorem linearCombination_cadlagRepresentative_eq
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (FiniteIntervalHybridBVPath.cadlagRepresentative
      (linearCombination firstCoefficient secondCoefficient first second)).representative time =
      firstCoefficient • first.cadlagRepresentative.representative time +
        secondCoefficient • second.cadlagRepresentative.representative time := by
  exact FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
    (linearCombination firstCoefficient secondCoefficient first second).cadlagRepresentative
    (linearCombinationCadlagRepresentative
      firstCoefficient secondCoefficient first second) hTime

/-- Recovered initial traces combine with the same two coefficients. -/
theorem linearCombination_initialTrace
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) :
    (linearCombination firstCoefficient secondCoefficient first second).initialTrace =
      firstCoefficient • first.initialTrace + secondCoefficient • second.initialTrace := by
  rw [FiniteIntervalHybridBVPath.initialTrace_eq_of_cadlagRepresentative
    (linearCombination firstCoefficient secondCoefficient first second)
    (linearCombinationCadlagRepresentative
      firstCoefficient secondCoefficient first second) hDuration]
  rfl

/-- Recovered terminal traces combine with the same two coefficients. -/
theorem linearCombination_terminalTrace
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) :
    (linearCombination firstCoefficient secondCoefficient first second).terminalTrace hDuration =
      firstCoefficient • first.terminalTrace hDuration +
        secondCoefficient • second.terminalTrace hDuration := by
  apply tendsto_nhds_unique
    (FiniteIntervalHybridBVPath.tendsto_terminalTrace
      (linearCombination firstCoefficient secondCoefficient first second) hDuration)
  have hExplicit :
      Tendsto
        (fun time =>
          firstCoefficient • first.cadlagRepresentative.representative time +
            secondCoefficient • second.cadlagRepresentative.representative time)
        (𝓝[<] duration)
        (𝓝 (firstCoefficient • first.terminalTrace hDuration +
          secondCoefficient • second.terminalTrace hDuration)) :=
    (first.tendsto_terminalTrace hDuration).const_smul firstCoefficient |>.add
      ((second.tendsto_terminalTrace hDuration).const_smul secondCoefficient)
  apply hExplicit.congr'
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hDuration), self_mem_nhdsWithin]
      with time hTimePositive hTimeUpper
  exact linearCombination_cadlagRepresentative_eq
    firstCoefficient secondCoefficient first second
    ⟨le_of_lt hTimePositive, hTimeUpper⟩ |>.symm

/-- The `L1` component of a hybrid linear combination is the native module combination. -/
theorem linearCombination_toL1Path
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    (linearCombination firstCoefficient secondCoefficient first second).toDerivativePath.toL1Path =
      firstCoefficient • first.toDerivativePath.toL1Path +
        secondCoefficient • second.toDerivativePath.toL1Path := by
  let firstMemLp : MemLp first.cadlagRepresentative.representative 1
      (finiteOpenIntervalVolume duration) :=
    Classical.choose first.cadlagRepresentative.represents
  let secondMemLp : MemLp second.cadlagRepresentative.representative 1
      (finiteOpenIntervalVolume duration) :=
    Classical.choose second.cadlagRepresentative.represents
  have hFirst : firstMemLp.toLp first.cadlagRepresentative.representative =
      first.toDerivativePath.toL1Path :=
    Classical.choose_spec first.cadlagRepresentative.represents
  have hSecond : secondMemLp.toLp second.cadlagRepresentative.representative =
      second.toDerivativePath.toL1Path :=
    Classical.choose_spec second.cadlagRepresentative.represents
  change linearCombinationL1Path firstCoefficient secondCoefficient first second = _
  unfold linearCombinationL1Path FiniteIntervalL1Path.ofFunction
  calc
    _ = ((firstMemLp.const_smul firstCoefficient).add
          (secondMemLp.const_smul secondCoefficient)).toLp
        (firstCoefficient • first.cadlagRepresentative.representative +
          secondCoefficient • second.cadlagRepresentative.representative) := by
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall fun _time => rfl
    _ = _ := by
      rw [MemLp.toLp_add
          (firstMemLp.const_smul firstCoefficient)
          (secondMemLp.const_smul secondCoefficient),
        MemLp.toLp_const_smul firstCoefficient firstMemLp,
        MemLp.toLp_const_smul secondCoefficient secondMemLp,
        hFirst, hSecond]

/-- Coefficients one and zero recover the first hybrid path exactly. -/
@[simp]
theorem linearCombination_one_zero
    (first second : FiniteIntervalHybridBVPath Coordinate duration) :
    linearCombination 1 0 first second = first := by
  apply FiniteIntervalHybridBVPath.injective_toL1Path
  change (linearCombination 1 0 first second).toDerivativePath.toL1Path =
    first.toDerivativePath.toL1Path
  rw [linearCombination_toL1Path]
  simp

/-- Linear combinations converge in the hybrid topology whenever their two coefficients
converge, including simultaneously in strong `L1` and against every derivative test. -/
theorem tendsto_linearCombination
    {Index : Type*} {filter : Filter Index}
    {firstCoefficient secondCoefficient : Index → ℝ}
    {firstCoefficientLimit secondCoefficientLimit : ℝ}
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hFirstCoefficient :
      Tendsto firstCoefficient filter (𝓝 firstCoefficientLimit))
    (hSecondCoefficient :
      Tendsto secondCoefficient filter (𝓝 secondCoefficientLimit)) :
    Tendsto
      (fun index => linearCombination
        (firstCoefficient index) (secondCoefficient index) first second)
      filter
      (𝓝 (linearCombination
        firstCoefficientLimit secondCoefficientLimit first second)) := by
  rw [FiniteIntervalHybridBVPath.tendsto_iff]
  constructor
  · simp_rw [linearCombination_toL1Path]
    exact (hFirstCoefficient.smul tendsto_const_nhds).add
      (hSecondCoefficient.smul tendsto_const_nhds)
  · intro coordinate test
    have hFormula (firstValue secondValue : ℝ) :
        ((linearCombination firstValue secondValue first second).toDerivativePath.derivative
            coordinate).continuousTestIntegral test.1 =
          firstValue *
              (first.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 +
            secondValue *
              (second.toDerivativePath.derivative coordinate).continuousTestIntegral test.1 := by
      rw [linearCombination_derivative]
      calc
        _ = VagueSignedMeasure.continuousTestIntegral
              (VagueSignedMeasure.ofSignedMeasure
                (firstValue •
                  (first.toDerivativePath.derivative coordinate).toSignedMeasure)) test.1 +
            VagueSignedMeasure.continuousTestIntegral
              (VagueSignedMeasure.ofSignedMeasure
                (secondValue •
                  (second.toDerivativePath.derivative coordinate).toSignedMeasure)) test.1 := by
          simpa only [VagueSignedMeasure.toSignedMeasure_ofSignedMeasure] using
            VagueSignedMeasure.continuousTestIntegral_add
              (VagueSignedMeasure.ofSignedMeasure
                (firstValue •
                  (first.toDerivativePath.derivative coordinate).toSignedMeasure))
              (VagueSignedMeasure.ofSignedMeasure
                (secondValue •
                  (second.toDerivativePath.derivative coordinate).toSignedMeasure)) test.1
        _ = _ := by
          rw [VagueSignedMeasure.continuousTestIntegral_smul,
            VagueSignedMeasure.continuousTestIntegral_smul]
    simp_rw [hFormula]
    exact (hFirstCoefficient.mul_const _).add
      (hSecondCoefficient.mul_const _)

/-- Absolute continuity of both derivative families is preserved by a real linear combination. -/
theorem linearCombination_hasAbsolutelyContinuousDerivative
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hFirst : first.HasAbsolutelyContinuousDerivative)
    (hSecond : second.HasAbsolutelyContinuousDerivative) :
    (linearCombination firstCoefficient secondCoefficient first second)
      |>.HasAbsolutelyContinuousDerivative := by
  intro coordinate
  rw [linearCombination_derivative, VagueSignedMeasure.toSignedMeasure_ofSignedMeasure]
  exact ((hFirst coordinate).smul (r := firstCoefficient)).add
    ((hSecond coordinate).smul (r := secondCoefficient))

/-- The Radon--Nikodym derivative of an absolutely continuous path combination is the almost-
everywhere pointwise combination of the two derivative densities. -/
theorem ae_linearCombination_derivativeDensity_eq
    (firstCoefficient secondCoefficient : ℝ)
    (first second : FiniteIntervalHybridBVPath Coordinate duration)
    (hFirst : first.HasAbsolutelyContinuousDerivative)
    (hSecond : second.HasAbsolutelyContinuousDerivative)
    (coordinate : Coordinate) :
    ∀ᵐ time ∂finiteOpenIntervalVolume duration,
      (linearCombination firstCoefficient secondCoefficient first second).derivativeDensity
          coordinate time =
        (firstCoefficient • first.derivativeDensity coordinate +
          secondCoefficient • second.derivativeDensity coordinate) time := by
  let combined := linearCombination firstCoefficient secondCoefficient first second
  have hCombinedAC := linearCombination_hasAbsolutelyContinuousDerivative
    firstCoefficient secondCoefficient first second hFirst hSecond
  have hCombinedIntegrable : Integrable (combined.derivativeDensity coordinate)
      (finiteOpenIntervalVolume duration) :=
    SignedMeasure.integrable_rnDeriv
      (combined.toDerivativePath.derivative coordinate).toSignedMeasure
      (finiteOpenIntervalVolume duration)
  have hFirstIntegrable : Integrable (first.derivativeDensity coordinate)
      (finiteOpenIntervalVolume duration) :=
    SignedMeasure.integrable_rnDeriv
      (first.toDerivativePath.derivative coordinate).toSignedMeasure
      (finiteOpenIntervalVolume duration)
  have hSecondIntegrable : Integrable (second.derivativeDensity coordinate)
      (finiteOpenIntervalVolume duration) :=
    SignedMeasure.integrable_rnDeriv
      (second.toDerivativePath.derivative coordinate).toSignedMeasure
      (finiteOpenIntervalVolume duration)
  have hFirstScaled : Integrable
      (firstCoefficient • first.derivativeDensity coordinate)
      (finiteOpenIntervalVolume duration) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      hFirstIntegrable.const_mul firstCoefficient
  have hSecondScaled : Integrable
      (secondCoefficient • second.derivativeDensity coordinate)
      (finiteOpenIntervalVolume duration) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      hSecondIntegrable.const_mul secondCoefficient
  apply hCombinedIntegrable.ae_eq_of_withDensityᵥ_eq
    (hFirstScaled.add hSecondScaled)
  rw [combined.withDensity_derivativeDensity_eq_derivative hCombinedAC coordinate,
    show combined.toDerivativePath.derivative coordinate =
        VagueSignedMeasure.ofSignedMeasure
          (firstCoefficient •
              (first.toDerivativePath.derivative coordinate).toSignedMeasure +
            secondCoefficient •
              (second.toDerivativePath.derivative coordinate).toSignedMeasure) by
      exact linearCombination_derivative
        firstCoefficient secondCoefficient first second coordinate,
    VagueSignedMeasure.toSignedMeasure_ofSignedMeasure,
    withDensityᵥ_add hFirstScaled hSecondScaled,
    withDensityᵥ_smul, withDensityᵥ_smul,
    first.withDensity_derivativeDensity_eq_derivative hFirst coordinate,
    second.withDensity_derivativeDensity_eq_derivative hSecond coordinate]

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses
