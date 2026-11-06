/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalHybridBVPath

/-!
# Constant translations of finite-interval hybrid BV paths

This module constructs the source-neutral translation of every carried path coordinate by one
time-independent finite vector.  The strong-`L1` component is translated, the Stieltjes derivative
is retained exactly, and the separately recovered initial trace records the translation.  The
construction is useful for testing whether a derivative-only functional sees boundary data.

## Main declarations

- `FiniteIntervalHybridBVPath.constantTranslate`: translate a hybrid path by a constant vector;
- `FiniteIntervalHybridBVPath.constantTranslate_derivative`: the derivative is unchanged;
- `FiniteIntervalHybridBVPath.constantTranslate_initialTrace`: the initial trace is translated.
-/

namespace FiniteMarkovProcesses

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

universe u

noncomputable section

namespace FiniteIntervalHybridBVPath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- The raw representative obtained by translating the selected càdlàg representative by one
time-independent coordinate vector. -/
def constantTranslateRepresentative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    ℝ → FiniteCoordinateL1Value Coordinate :=
  fun time => path.cadlagRepresentative.representative time + translation

/-- A constant translation of the selected representative remains integrable on finite physical
time. -/
theorem memLp_constantTranslateRepresentative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    MemLp (constantTranslateRepresentative path translation) 1
      (finiteOpenIntervalVolume duration) := by
  have hPath :
      MemLp path.cadlagRepresentative.representative 1
        (finiteOpenIntervalVolume duration) :=
    Classical.choose path.cadlagRepresentative.represents
  have hTranslation :
      MemLp (fun _ : ℝ => translation) 1
        (finiteOpenIntervalVolume duration) :=
    MeasureTheory.memLp_const (μ := finiteOpenIntervalVolume duration) (c := translation)
  have hFunction :
      (path.cadlagRepresentative.representative + (fun _ : ℝ => translation)) =
        constantTranslateRepresentative path translation := by
    funext time
    rfl
  rw [← hFunction]
  exact hPath.add hTranslation

/-- The translated strong-`L1` quotient. -/
noncomputable def constantTranslateL1Path
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path Coordinate duration :=
  FiniteIntervalL1Path.ofFunction
    (constantTranslateRepresentative path translation)
    (memLp_constantTranslateRepresentative path translation)

/-- The translated raw path represents its translated quotient definitionally. -/
theorem constantTranslateRepresentative_represents
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path.Represents
      (constantTranslateL1Path path translation)
      (constantTranslateRepresentative path translation) := by
  refine ⟨memLp_constantTranslateRepresentative path translation, rfl⟩

/-- Constant translation preserves quotient-level bounded variation. -/
theorem constantTranslateL1Path_hasBoundedVariation
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalL1Path.HasBoundedVariation
      (constantTranslateL1Path path translation) := by
  obtain ⟨representative, hRepresents, hVariation⟩ :=
    (FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative
      path.toDerivativePath.toL1Path).mp path.hasBoundedVariation
  let translatedRepresentative : ℝ → FiniteCoordinateL1Value Coordinate :=
    fun time => representative time + translation
  have hRepresentativeMemLp :
      MemLp representative 1 (finiteOpenIntervalVolume duration) :=
    Classical.choose hRepresents
  have hTranslatedMemLp :
      MemLp translatedRepresentative 1 (finiteOpenIntervalVolume duration) := by
    have hTranslation :
        MemLp (fun _ : ℝ => translation) 1
          (finiteOpenIntervalVolume duration) :=
      MeasureTheory.memLp_const (μ := finiteOpenIntervalVolume duration) (c := translation)
    have hFunction :
        (representative + (fun _ : ℝ => translation)) = translatedRepresentative := by
      funext time
      rfl
    rw [← hFunction]
    exact hRepresentativeMemLp.add hTranslation
  have hRepresentativeEventually :
      representative =ᵐ[finiteOpenIntervalVolume duration]
        path.cadlagRepresentative.representative := by
    have hFirst :=
      (FiniteIntervalL1Path.represents_iff_eventuallyEq
        path.toDerivativePath.toL1Path representative hRepresentativeMemLp).mp hRepresents
    have hSecondMemLp :
        MemLp path.cadlagRepresentative.representative 1
          (finiteOpenIntervalVolume duration) :=
      Classical.choose path.cadlagRepresentative.represents
    have hSecond :=
      (FiniteIntervalL1Path.represents_iff_eventuallyEq
        path.toDerivativePath.toL1Path path.cadlagRepresentative.representative
          hSecondMemLp).mp path.cadlagRepresentative.represents
    exact hFirst.trans hSecond.symm
  have hTranslatedEventually :
      translatedRepresentative =ᵐ[finiteOpenIntervalVolume duration]
        constantTranslateRepresentative path translation := by
    filter_upwards [hRepresentativeEventually] with time hTime
    simp only [translatedRepresentative, constantTranslateRepresentative, hTime]
  have hTranslatedRepresents :
      FiniteIntervalL1Path.Represents
        (constantTranslateL1Path path translation) translatedRepresentative := by
    apply (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (constantTranslateL1Path path translation) translatedRepresentative
        hTranslatedMemLp).mpr
    have hCanonicalMemLp := memLp_constantTranslateRepresentative path translation
    have hCanonical :=
      (FiniteIntervalL1Path.represents_iff_eventuallyEq
        (constantTranslateL1Path path translation)
        (constantTranslateRepresentative path translation) hCanonicalMemLp).mp
          (constantTranslateRepresentative_represents path translation)
    exact hTranslatedEventually.trans hCanonical
  apply FiniteIntervalL1Path.hasBoundedVariation_of_represents
    (constantTranslateL1Path path translation) translatedRepresentative hTranslatedRepresents
  have hFunction :
      (representative + (fun _ : ℝ => translation)) = translatedRepresentative := by
    funext time
    rfl
  rw [← hFunction]
  exact FiniteIntervalBVAlgebra.boundedVariationOn_add
    (Value := FiniteCoordinateL1Value Coordinate) hVariation
    (FiniteIntervalBVAlgebra.boundedVariationOn_const
      (Value := FiniteCoordinateL1Value Coordinate) translation (Ioo 0 duration))

/-- The explicitly translated càdlàg representative of the translated quotient. -/
noncomputable def constantTranslateCadlagRepresentative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalCadlagRepresentative (constantTranslateL1Path path translation) where
  representative := constantTranslateRepresentative path translation
  represents := constantTranslateRepresentative_represents path translation
  rightContinuous := by
    intro time hTime
    exact (path.cadlagRepresentative.rightContinuous time hTime).add continuousWithinAt_const
  hasLeftLimit := by
    intro time hTime
    obtain ⟨leftTrace, hLeftTrace⟩ :=
      path.cadlagRepresentative.hasLeftLimit time hTime
    exact ⟨leftTrace + translation, hLeftTrace.add tendsto_const_nhds⟩

/-- Translate every path coordinate by one constant vector while retaining every derivative
measure exactly. -/
noncomputable def constantTranslate
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate) :
    FiniteIntervalHybridBVPath Coordinate duration := by
  let derivativePath : FiniteIntervalL1DerivativePath Coordinate duration :=
    { toL1Path := constantTranslateL1Path path translation
      derivative := path.toDerivativePath.derivative }
  refine
    { toDerivativePath := derivativePath
      hasBoundedVariation := constantTranslateL1Path_hasBoundedVariation path translation
      hasCadlagDerivativeRealization := ?_ }
  refine ⟨constantTranslateCadlagRepresentative path translation, ?_, ?_⟩
  · exact (Classical.choose_spec path.hasCadlagDerivativeRealization).1
  · intro coordinate start finish hStart hOrder hFinish
    rw [show derivativePath.derivative coordinate =
        path.toDerivativePath.derivative coordinate by rfl,
      path.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
        hStart hOrder hFinish]
    simp only [constantTranslateCadlagRepresentative, constantTranslateRepresentative,
      PiLp.add_apply]
    abel_nf

/-- Constant translation retains every carried signed derivative definitionally. -/
@[simp]
theorem constantTranslate_derivative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate)
    (coordinate : Coordinate) :
    (constantTranslate path translation).toDerivativePath.derivative coordinate =
      path.toDerivativePath.derivative coordinate := by
  rfl

/-- The canonical translated representative agrees with the explicit translated representative
at every physical half-open time. -/
theorem constantTranslate_cadlagRepresentative_eq
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate)
    {time : ℝ} (hTime : time ∈ Ico 0 duration) :
    (constantTranslate path translation).cadlagRepresentative.representative time =
      path.cadlagRepresentative.representative time + translation := by
  exact FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
    (constantTranslate path translation).cadlagRepresentative
    (constantTranslateCadlagRepresentative path translation) hTime

/-- The separately recovered initial trace records the constant translation exactly. -/
theorem constantTranslate_initialTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate)
    (hDuration : 0 < duration) :
    (constantTranslate path translation).initialTrace =
      path.initialTrace + translation := by
  rw [(constantTranslate path translation).initialTrace_eq_of_cadlagRepresentative
    (constantTranslateCadlagRepresentative path translation) hDuration]
  rfl

/-- The separately recovered terminal left trace records the same constant translation. -/
theorem constantTranslate_terminalTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (translation : FiniteCoordinateL1Value Coordinate)
    (hDuration : 0 < duration) :
    (constantTranslate path translation).terminalTrace hDuration =
      path.terminalTrace hDuration + translation := by
  apply tendsto_nhds_unique
    ((constantTranslate path translation).tendsto_terminalTrace hDuration)
  have hExplicit :
      Tendsto
        (fun time => path.cadlagRepresentative.representative time + translation)
        (𝓝[<] duration)
        (𝓝 (path.terminalTrace hDuration + translation)) :=
    (path.tendsto_terminalTrace hDuration).add tendsto_const_nhds
  apply hExplicit.congr'
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hDuration), self_mem_nhdsWithin]
      with time hTimePositive hTimeUpper
  exact constantTranslate_cadlagRepresentative_eq path translation
    ⟨le_of_lt hTimePositive, hTimeUpper⟩ |>.symm

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses
