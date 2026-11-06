/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Finite-coordinate L1 paths and essential bounded variation

This module constructs the open-finite-interval `L1` path quotient used by finite-dimensional
bounded-variation trajectory spaces.  Path equality is Mathlib's genuine almost-everywhere `Lp`
equality, not pointwise equality of a chosen representative.

The essential variation of a quotient path is the infimum of `eVariationOn` over all `L1`
representatives.  The main characterization proves that this infimum is finite exactly when the
quotient has a representative of bounded pointwise variation.  This separates the quotient-level
predicate from later choices of a cadlag representative and boundary traces.

## Main declarations

- `FiniteCoordinateL1Value`: a finite real coordinate family with its `l1` norm;
- `FiniteIntervalL1Path`: `L1((0,T); l1(Coordinate))` as an almost-everywhere quotient;
- `FiniteIntervalL1Path.Represents`: a raw function represents a quotient path;
- `FiniteIntervalL1Path.essentialVariation`: infimum of representative variations;
- `FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative`: exact representative
  characterization of quotient-level bounded variation.
-/

namespace FiniteMarkovProcesses

open MeasureTheory Set
open scoped ENNReal NNReal Topology

universe u

noncomputable section

/-- The fixed exponent used by every finite-interval path is strictly below infinity. -/
instance instFactOneNeTopENNReal : Fact ((1 : ENNReal) ≠ ∞) :=
  ⟨ENNReal.one_ne_top⟩

/-- A finite real coordinate family carrying the exact finite `l1` norm. -/
abbrev FiniteCoordinateL1Value (Coordinate : Type u) [Fintype Coordinate] :=
  PiLp 1 fun _ : Coordinate => ℝ

/-- Lebesgue measure restricted to the open physical interval `(0,T)`.  Boundary traces are not
part of this measure and must be recovered separately. -/
noncomputable def finiteOpenIntervalVolume (duration : ℝ) : Measure ℝ :=
  volume.restrict (Ioo 0 duration)

/-- The total mass of the physical-time measure is the nonnegative duration. -/
@[simp]
theorem finiteOpenIntervalVolume_apply_univ (duration : ℝ) :
    finiteOpenIntervalVolume duration Set.univ = ENNReal.ofReal duration := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  simp

/-- The finite-interval volume gives no mass to times outside its physical open interval. -/
@[simp]
theorem finiteOpenIntervalVolume_apply_compl_Ioo (duration : ℝ) :
    finiteOpenIntervalVolume duration (Ioo 0 duration)ᶜ = 0 := by
  rw [finiteOpenIntervalVolume, Measure.restrict_apply measurableSet_Ioo.compl]
  simp

/-- Restricting the physical-time measure to an elapsed half-open interval agrees with ordinary
Lebesgue measure on the corresponding open interval.  The endpoint convention is immaterial
because Lebesgue measure has no atoms. -/
theorem finiteOpenIntervalVolume_restrict_Ioc_zero_eq_volume_restrict_Ioo
    {duration time : ℝ} (hTimeDuration : time < duration) :
    (finiteOpenIntervalVolume duration).restrict (Ioc 0 time) =
      volume.restrict (Ioo 0 time) := by
  rw [finiteOpenIntervalVolume]
  have hSubset : Ioc 0 time ⊆ Ioo 0 duration := by
    intro point hPoint
    exact ⟨hPoint.1, hPoint.2.trans_lt hTimeDuration⟩
  rw [Measure.restrict_restrict_of_subset hSubset]
  exact restrict_Ioo_eq_restrict_Ioc.symm

/-- Lebesgue measure on every bounded open physical interval is finite, including the empty
interval at nonpositive duration. -/
noncomputable instance instIsFiniteMeasureFiniteOpenIntervalVolume (duration : ℝ) :
    IsFiniteMeasure (finiteOpenIntervalVolume duration) := by
  refine ⟨?_⟩
  rw [finiteOpenIntervalVolume_apply_univ]
  exact ENNReal.ofReal_lt_top

/-- The genuine almost-everywhere `L1` quotient of finite-coordinate paths on `(0,T)`. -/
abbrev FiniteIntervalL1Path
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ) :=
  Lp (FiniteCoordinateL1Value Coordinate) 1 (finiteOpenIntervalVolume duration)

/-- The strong `L1` path carrier uses its norm-topology Borel sigma algebra. -/
noncomputable instance instMeasurableSpaceFiniteIntervalL1Path
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ) :
    MeasurableSpace (FiniteIntervalL1Path Coordinate duration) :=
  borel (FiniteIntervalL1Path Coordinate duration)

/-- Borel compatibility for the strong `L1` path carrier is definitional. -/
instance instBorelSpaceFiniteIntervalL1Path
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ) :
    BorelSpace (FiniteIntervalL1Path Coordinate duration) :=
  ⟨rfl⟩

namespace FiniteIntervalL1Path

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- A raw path represents an `L1` quotient path when it is in `L1` and its canonical quotient is
the supplied path. -/
def Represents (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate) : Prop :=
  ∃ hRepresentative : MemLp representative 1 (finiteOpenIntervalVolume duration),
    hRepresentative.toLp representative = path

/-- Every `L1` path, viewed through Mathlib's chosen coefficient function, represents itself. -/
theorem represents_coeFn (path : FiniteIntervalL1Path Coordinate duration) :
    Represents path path := by
  refine ⟨Lp.memLp path, ?_⟩
  exact Lp.toLp_coeFn path (Lp.memLp path)

/-- For a fixed `L1` proof, representation is equivalent to almost-everywhere equality with the
quotient path. -/
theorem represents_iff_eventuallyEq
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresentative : MemLp representative 1 (finiteOpenIntervalVolume duration)) :
    Represents path representative ↔
      representative =ᵐ[finiteOpenIntervalVolume duration] path := by
  constructor
  · rintro ⟨_, hQuotient⟩
    have hCoefficient := hRepresentative.coeFn_toLp
    rw [hQuotient] at hCoefficient
    exact hCoefficient.symm
  · intro hEventually
    refine ⟨hRepresentative, ?_⟩
    calc
      hRepresentative.toLp representative = (Lp.memLp path).toLp path :=
        hRepresentative.toLp_congr (Lp.memLp path) hEventually
      _ = path := Lp.toLp_coeFn path (Lp.memLp path)

/-- Construct an `L1` quotient path from a raw representative and its `L1` proof. -/
def ofFunction (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresentative : MemLp representative 1 (finiteOpenIntervalVolume duration)) :
    FiniteIntervalL1Path Coordinate duration :=
  hRepresentative.toLp representative

/-- Two integrable raw paths define the same quotient exactly when they agree almost everywhere
on the open interval. -/
theorem ofFunction_eq_iff_eventuallyEq
    (first second : ℝ → FiniteCoordinateL1Value Coordinate)
    (hFirst : MemLp first 1 (finiteOpenIntervalVolume duration))
    (hSecond : MemLp second 1 (finiteOpenIntervalVolume duration)) :
    ofFunction first hFirst = ofFunction second hSecond ↔
      first =ᵐ[finiteOpenIntervalVolume duration] second :=
  hFirst.toLp_eq_toLp_iff hSecond

/-- All extended pointwise variations attained by representatives of one `L1` quotient path. -/
def representativeVariationSet
    (path : FiniteIntervalL1Path Coordinate duration) : Set ℝ≥0∞ :=
  { variation | ∃ representative : ℝ → FiniteCoordinateL1Value Coordinate,
      Represents path representative ∧
        variation = eVariationOn representative (Ioo 0 duration) }

/-- The representative-variation set is never empty; the chosen `Lp` coefficient function is a
representative even when its pointwise variation is infinite. -/
theorem representativeVariationSet_nonempty
    (path : FiniteIntervalL1Path Coordinate duration) :
    (representativeVariationSet path).Nonempty := by
  exact ⟨eVariationOn path (Ioo 0 duration), path, represents_coeFn path, rfl⟩

/-- Essential variation of an `L1` quotient path: the infimum of pointwise variations over every
representative of the same almost-everywhere class. -/
noncomputable def essentialVariation
    (path : FiniteIntervalL1Path Coordinate duration) : ℝ≥0∞ :=
  sInf (representativeVariationSet path)

/-- Every representative's pointwise variation bounds the quotient's essential variation. -/
theorem essentialVariation_le_of_represents
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresents : Represents path representative) :
    essentialVariation path ≤ eVariationOn representative (Ioo 0 duration) :=
  sInf_le ⟨representative, hRepresents, rfl⟩

/-- Quotient-level bounded variation means finite essential representative variation. -/
def HasBoundedVariation
    (path : FiniteIntervalL1Path Coordinate duration) : Prop :=
  essentialVariation path < ∞

/-- A bounded-variation representative makes the quotient path essentially bounded variation. -/
theorem hasBoundedVariation_of_represents
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresents : Represents path representative)
    (hVariation : BoundedVariationOn representative (Ioo 0 duration)) :
    HasBoundedVariation path :=
  (essentialVariation_le_of_represents path representative hRepresents).trans_lt
    (lt_top_iff_ne_top.mpr hVariation)

/-- Finite essential variation is equivalent to the existence of an actual pointwise
bounded-variation representative. -/
theorem hasBoundedVariation_iff_exists_representative
    (path : FiniteIntervalL1Path Coordinate duration) :
    HasBoundedVariation path ↔
      ∃ representative : ℝ → FiniteCoordinateL1Value Coordinate,
        Represents path representative ∧
          BoundedVariationOn representative (Ioo 0 duration) := by
  constructor
  · intro hEssential
    obtain ⟨variation, hVariationMember, hVariationFinite⟩ :=
      sInf_lt_iff.mp hEssential
    obtain ⟨representative, hRepresents, rfl⟩ := hVariationMember
    exact ⟨representative, hRepresents, hVariationFinite.ne⟩
  · rintro ⟨representative, hRepresents, hVariation⟩
    exact hasBoundedVariation_of_represents path representative hRepresents hVariation

end FiniteIntervalL1Path

end

end FiniteMarkovProcesses
