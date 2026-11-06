/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1Path
import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.VagueSignedMeasureTopology

/-!
# Strong-L1 plus open-interval vague-derivative path topology

This module constructs the exact hybrid ambient topology used for finite-coordinate
bounded-variation paths: strong `L1` convergence of the path together with vague convergence of
each coordinate derivative measure **on the open physical interval**.  The derivative data remain
finite signed measures on `ℝ` so their Stieltjes increments can use ordinary real intervals.  The
topology tests zero-extended members of `C₀((0,T), ℝ)`: continuous functions that vanish outside
the open interval, whose support may accumulate at either boundary.

This relative test family is essential.  A sequence of interior Dirac masses approaching `0` must
converge vaguely to zero on `(0,T)`; testing against all of `C_c(ℝ)` would instead expose an
endpoint Dirac mass.  Requiring topological support compactly contained in `(0,T)` would encode the
smaller metrizable `C_c((0,T), ℝ)` variant, not the published nonmetrizable `C₀` topology.

The measurable space is definitionally the Borel sigma algebra of this hybrid topology.  Thus a
later observation cannot use one measurable carrier while an LDP statement silently uses another
topology.

## Main declarations

- `FiniteOpenIntervalVanishingContinuousTest`: zero-extended `C₀((0,T), ℝ)` tests.
- `FiniteIntervalL1DerivativePath`: an `L1` path with one finite signed derivative measure per
  coordinate.
- `FiniteIntervalL1DerivativePath.tendsto_iff`: exact strong-`L1` plus coordinatewise
  open-interval-vague convergence characterization.
- `FiniteIntervalL1DerivativePath.measurableSpace_eq_borel`: definitional Borel compatibility.
-/

namespace FiniteMarkovProcesses

open Filter Set
open scoped CompactlySupported Topology

universe u

noncomputable section

/-- Zero-extended continuous real tests that vanish outside the open physical interval.  Because
the interval is bounded, these are compactly supported on `ℝ`; allowing their topological support
to reach `0` or `T` realizes the published `C₀((0,T), ℝ)` test family rather than only its smaller
compact-interior subfamily. -/
abbrev FiniteOpenIntervalVanishingContinuousTest (duration : ℝ) :=
  {test : C_c(ℝ, ℝ) // Set.EqOn test 0 (Ioo 0 duration)ᶜ}

namespace FiniteOpenIntervalVanishingContinuousTest

/-- Every zero-extended compact test on the open physical interval vanishes at the initial
boundary.  Consequently a derivative atom escaping to time zero is invisible to this test
family, as required by vague convergence on `(0,T)`. -/
theorem leftBoundary_eq_zero {duration : ℝ}
    (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    test.1 0 = 0 :=
  test.property (by simp)

/-- Every zero-extended compact test on the open physical interval vanishes at the terminal
boundary.  Thus the hybrid derivative topology does not manufacture a terminal atom from mass
escaping through physical time `T`. -/
theorem rightBoundary_eq_zero {duration : ℝ}
    (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    test.1 duration = 0 :=
  test.property (by simp)

end FiniteOpenIntervalVanishingContinuousTest

/-- Ambient hybrid data: an open-interval `L1` path and one finite signed real-line measure for
each finite coordinate.  The topology below sees each measure only through zero-extended `C₀`
tests that vanish off the open physical interval.  Distributional-derivative compatibility is
deliberately not asserted by the structure alone. -/
structure FiniteIntervalL1DerivativePath
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ) where
  /-- Almost-everywhere path coordinate, carrying the native strong `L1` topology. -/
  toL1Path : FiniteIntervalL1Path Coordinate duration
  /-- Candidate distributional derivative in each coordinate. -/
  derivative : Coordinate → VagueSignedMeasure ℝ

namespace FiniteIntervalL1DerivativePath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Equality of ambient derivative paths is coordinatewise equality of the `L1` path and the
finite signed derivative family. -/
@[ext]
theorem ext
    {first second : FiniteIntervalL1DerivativePath Coordinate duration}
    (hPath : first.toL1Path = second.toL1Path)
    (hDerivative : first.derivative = second.derivative) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Complete family of open-interval derivative test integrals. -/
noncomputable def interiorDerivativeTestIntegralFamily
    (path : FiniteIntervalL1DerivativePath Coordinate duration) :
    Coordinate → FiniteOpenIntervalVanishingContinuousTest duration → ℝ :=
  fun coordinate test =>
    (path.derivative coordinate).continuousTestIntegral test.1

/-- The map whose induced topology is strong `L1` on paths and product-vague on derivatives over
the open physical interval. -/
noncomputable def hybridTopologyEmbedding
    (path : FiniteIntervalL1DerivativePath Coordinate duration) :
    FiniteIntervalL1Path Coordinate duration ×
      (Coordinate → FiniteOpenIntervalVanishingContinuousTest duration → ℝ) :=
  (path.toL1Path, interiorDerivativeTestIntegralFamily path)

/-- The published hybrid topology: strong `L1` path topology plus open-interval vague derivative
topology. -/
noncomputable instance instTopologicalSpace :
    TopologicalSpace (FiniteIntervalL1DerivativePath Coordinate duration) :=
  TopologicalSpace.induced hybridTopologyEmbedding inferInstance

/-- The macroscopic measurable carrier is exactly the Borel sigma algebra of the hybrid
topology. -/
noncomputable instance instMeasurableSpace :
    MeasurableSpace (FiniteIntervalL1DerivativePath Coordinate duration) :=
  borel (FiniteIntervalL1DerivativePath Coordinate duration)

/-- The ambient hybrid measurable structure is registered as its Borel structure. -/
noncomputable instance instBorelSpace :
    BorelSpace (FiniteIntervalL1DerivativePath Coordinate duration) :=
  ⟨rfl⟩

/-- Borel compatibility is definitional rather than caller supplied. -/
theorem measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace
      (FiniteIntervalL1DerivativePath Coordinate duration)) =
        borel (FiniteIntervalL1DerivativePath Coordinate duration) :=
  rfl

/-- The complete path-and-interior-test map induces the hybrid topology. -/
theorem isInducing_hybridTopologyEmbedding :
    Topology.IsInducing
      (hybridTopologyEmbedding (Coordinate := Coordinate) (duration := duration)) :=
  ⟨rfl⟩

/-- The strong `L1` path projection is continuous in the hybrid topology. -/
theorem continuous_toL1Path :
    Continuous fun path : FiniteIntervalL1DerivativePath Coordinate duration =>
      path.toL1Path := by
  simpa only [hybridTopologyEmbedding, Function.comp_def] using
    continuous_fst.comp
      (isInducing_hybridTopologyEmbedding
        (Coordinate := Coordinate) (duration := duration)).continuous

/-- The complete open-interval derivative-test family is continuous in the hybrid topology. -/
theorem continuous_interiorDerivativeTestIntegralFamily :
    Continuous fun path : FiniteIntervalL1DerivativePath Coordinate duration =>
      interiorDerivativeTestIntegralFamily path := by
  simpa only [hybridTopologyEmbedding, Function.comp_def] using
    continuous_snd.comp
      (isInducing_hybridTopologyEmbedding
        (Coordinate := Coordinate) (duration := duration)).continuous

/-- Every individual interior derivative test integral is continuous. -/
theorem continuous_derivativeTestIntegral
    (coordinate : Coordinate) (test : FiniteOpenIntervalVanishingContinuousTest duration) :
    Continuous fun path : FiniteIntervalL1DerivativePath Coordinate duration =>
      (path.derivative coordinate).continuousTestIntegral test.1 :=
  (continuous_apply test).comp ((continuous_apply coordinate).comp
    continuous_interiorDerivativeTestIntegralFamily)

/-- Exact convergence characterization for the hybrid topology.  The first clause is native
strong `L1`; the second is convergence against every zero-extended `C₀` derivative test that
vanishes off the open physical interval. -/
theorem tendsto_iff
    {Index : Type*} {filter : Filter Index}
    {paths : Index → FiniteIntervalL1DerivativePath Coordinate duration}
    {limit : FiniteIntervalL1DerivativePath Coordinate duration} :
    Tendsto paths filter (nhds limit) ↔
      Tendsto (fun index => (paths index).toL1Path) filter
          (nhds limit.toL1Path) ∧
        ∀ coordinate (test : FiniteOpenIntervalVanishingContinuousTest duration),
          Tendsto (fun index =>
              ((paths index).derivative coordinate).continuousTestIntegral test.1)
            filter
            (nhds ((limit.derivative coordinate).continuousTestIntegral test.1)) := by
  rw [isInducing_hybridTopologyEmbedding.tendsto_nhds_iff]
  simp only [hybridTopologyEmbedding, Function.comp_apply, Prod.tendsto_iff,
    tendsto_pi_nhds, interiorDerivativeTestIntegralFamily]

/-- Every neighborhood in the hybrid topology contains a strong-`L1` ball intersected with
finitely many open-interval derivative-test constraints.  The derivative tolerances may depend
on the selected coordinate and test; keeping those radii explicit avoids imposing an artificial
metric on the nonmetrizable complete test family.

This is the finite-cylinder reduction needed to turn strong-`L1` and finite-test probabilistic
concentration estimates into an arbitrary open-neighborhood estimate. -/
theorem exists_finiteDerivativeTestCylinder_subset_of_mem_nhds
    (path : FiniteIntervalL1DerivativePath Coordinate duration)
    {neighborhood : Set (FiniteIntervalL1DerivativePath Coordinate duration)}
    (hNeighborhood : neighborhood ∈ 𝓝 path) :
    ∃ l1Tolerance : ℝ, 0 < l1Tolerance ∧
      ∃ selectedTests : Finset
          (Coordinate × FiniteOpenIntervalVanishingContinuousTest duration),
        ∃ derivativeTolerance :
            Coordinate → FiniteOpenIntervalVanishingContinuousTest duration → ℝ,
          (∀ selectedTest ∈ selectedTests,
            0 < derivativeTolerance selectedTest.1 selectedTest.2) ∧
          {candidate |
              ‖candidate.toL1Path - path.toL1Path‖ < l1Tolerance ∧
                ∀ selectedTest ∈ selectedTests,
                  |(candidate.derivative selectedTest.1).continuousTestIntegral
                        selectedTest.2.1 -
                    (path.derivative selectedTest.1).continuousTestIntegral
                        selectedTest.2.1| <
                      derivativeTolerance selectedTest.1 selectedTest.2} ⊆ neighborhood := by
  classical
  rw [nhds_induced] at hNeighborhood
  rcases Filter.mem_comap.mp hNeighborhood with
    ⟨ambientNeighborhood, hAmbientNeighborhood, hAmbientSubset⟩
  rcases mem_nhds_prod_iff.mp hAmbientNeighborhood with
    ⟨l1Neighborhood, hL1Neighborhood, derivativeNeighborhood,
      hDerivativeNeighborhood, hProductSubset⟩
  rcases Metric.mem_nhds_iff.mp hL1Neighborhood with
    ⟨l1Tolerance, hL1Tolerance, hL1BallSubset⟩
  rw [nhds_pi, Filter.mem_pi'] at hDerivativeNeighborhood
  rcases hDerivativeNeighborhood with
    ⟨selectedCoordinates, coordinateNeighborhood, hCoordinateNeighborhood,
      hCoordinateCylinderSubset⟩
  have hTestNeighborhood (coordinate : Coordinate) :
      coordinateNeighborhood coordinate ∈
        𝓝 (interiorDerivativeTestIntegralFamily path coordinate) :=
    hCoordinateNeighborhood coordinate
  have hTestNeighborhoodData (coordinate : Coordinate) :
      ∃ selectedTests : Finset (FiniteOpenIntervalVanishingContinuousTest duration),
        ∃ testNeighborhood :
            FiniteOpenIntervalVanishingContinuousTest duration → Set ℝ,
          (∀ test, testNeighborhood test ∈
            𝓝 (interiorDerivativeTestIntegralFamily path coordinate test)) ∧
          Set.pi (↑selectedTests) testNeighborhood ⊆
            coordinateNeighborhood coordinate := by
    have hCoordinateNeighborhood := hTestNeighborhood coordinate
    rw [nhds_pi, Filter.mem_pi'] at hCoordinateNeighborhood
    exact hCoordinateNeighborhood
  choose coordinateTests testNeighborhood hTestNeighborhood
    hTestCylinderSubset using hTestNeighborhoodData
  have hValueNeighborhood (coordinate : Coordinate)
      (test : FiniteOpenIntervalVanishingContinuousTest duration) :
      testNeighborhood coordinate test ∈
        𝓝 ((path.derivative coordinate).continuousTestIntegral test.1) := by
    simpa only [interiorDerivativeTestIntegralFamily] using
      hTestNeighborhood coordinate test
  choose derivativeTolerance hDerivativeTolerance hDerivativeBallSubset using
    fun coordinate test => Metric.mem_nhds_iff.mp (hValueNeighborhood coordinate test)
  let selectedTests : Finset
      (Coordinate × FiniteOpenIntervalVanishingContinuousTest duration) :=
    selectedCoordinates.biUnion fun coordinate =>
      (coordinateTests coordinate).image fun test => (coordinate, test)
  refine ⟨l1Tolerance, hL1Tolerance, selectedTests, derivativeTolerance, ?_, ?_⟩
  · intro selectedTest hSelectedTest
    exact hDerivativeTolerance selectedTest.1 selectedTest.2
  · intro candidate hCandidate
    apply hAmbientSubset
    apply hProductSubset
    constructor
    · apply hL1BallSubset
      simpa only [hybridTopologyEmbedding, Metric.mem_ball, dist_eq_norm] using
        hCandidate.1
    · apply hCoordinateCylinderSubset
      intro coordinate hCoordinate
      apply hTestCylinderSubset coordinate
      intro test hTest
      apply hDerivativeBallSubset coordinate test
      have hSelected : (coordinate, test) ∈ selectedTests := by
        simp only [selectedTests, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨coordinate, hCoordinate, test, hTest, rfl⟩
      simpa only [hybridTopologyEmbedding, interiorDerivativeTestIntegralFamily,
        Metric.mem_ball, Real.dist_eq, abs_sub_comm] using
        hCandidate.2 (coordinate, test) hSelected

end FiniteIntervalL1DerivativePath

end

end FiniteMarkovProcesses

attribute [inherit_doc FiniteMarkovProcesses.FiniteIntervalL1DerivativePath.ext]
  FiniteMarkovProcesses.FiniteIntervalL1DerivativePath.ext_iff
