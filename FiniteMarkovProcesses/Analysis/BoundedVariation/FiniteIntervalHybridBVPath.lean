/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalCadlagRepresentative
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1DerivativeTopology
public import FiniteMarkovProcesses.MeasureTheory.VectorMeasure.FiniteIntervalSupportedSignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Finite-interval hybrid bounded-variation paths

This module binds the open-interval `L1` quotient to its finite signed distributional derivative.
The derivative is characterized on every half-open interval compactly contained in physical time;
for a right-continuous representative it has increment `d path ((a,b]) = path(b) - path(a)`.
This is the Stieltjes measure characterization of the distributional derivative, not a separate
pointwise or product-topology surrogate.

## Main declarations

- `ScalarFiniteIntervalCadlagDerivativeWitness`: scalar right-continuous modification, boundary
  limits, and finite signed Stieltjes derivative;
- `exists_scalarFiniteIntervalCadlagDerivativeWitness`: construction from scalar BV;
- `FiniteIntervalHybridBVPath`: finite-coordinate BV derivative graph carrying the induced
  strong-`L1` plus vague-derivative topology and its Borel sigma algebra.
-/

@[expose] public section

namespace FiniteMarkovProcesses

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

universe u

noncomputable section

namespace FiniteIntervalBVAlgebra

variable {Time Value Coordinate : Type*} [LinearOrder Time]
  [SeminormedAddCommGroup Value] [Fintype Coordinate]

/-- Variation of a pointwise sum is at most the sum of the two variations. -/
theorem eVariationOn_add_le (first second : Time → Value) (interval : Set Time) :
    eVariationOn (first + second) interval ≤
      eVariationOn first interval + eVariationOn second interval := by
  apply iSup_le
  rintro ⟨count, path, hMonotone, hPath⟩
  calc
    (∑ index ∈ Finset.range count,
        edist ((first + second) (path (index + 1)))
          ((first + second) (path index))) ≤
        ∑ index ∈ Finset.range count,
          (edist (first (path (index + 1))) (first (path index)) +
            edist (second (path (index + 1))) (second (path index))) := by
      apply Finset.sum_le_sum
      intro index _hIndex
      simpa only [Pi.add_apply] using edist_add_add_le
        (first (path (index + 1))) (second (path (index + 1)))
        (first (path index)) (second (path index))
    _ = (∑ index ∈ Finset.range count,
          edist (first (path (index + 1))) (first (path index))) +
        ∑ index ∈ Finset.range count,
          edist (second (path (index + 1))) (second (path index)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn first interval + eVariationOn second interval :=
      add_le_add
        (eVariationOn.sum_le (f := first) (n := count) hMonotone hPath)
        (eVariationOn.sum_le (f := second) (n := count) hMonotone hPath)

/-- Bounded variation is closed under pointwise addition. -/
theorem boundedVariationOn_add
    {first second : Time → Value} {interval : Set Time}
    (hFirst : BoundedVariationOn first interval)
    (hSecond : BoundedVariationOn second interval) :
    BoundedVariationOn (first + second) interval :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hFirst, hSecond⟩)
    (eVariationOn_add_le first second interval)

/-- Negation preserves total variation exactly. -/
theorem eVariationOn_neg (path : Time → Value) (interval : Set Time) :
    eVariationOn (-path) interval = eVariationOn path interval := by
  unfold eVariationOn
  simp only [Pi.neg_apply, edist_neg_neg]

/-- Bounded variation is closed under pointwise negation. -/
theorem boundedVariationOn_neg
    {path : Time → Value} {interval : Set Time}
    (hPath : BoundedVariationOn path interval) :
    BoundedVariationOn (-path) interval := by
  rw [BoundedVariationOn, eVariationOn_neg]
  exact hPath

/-- Bounded variation is closed under pointwise subtraction. -/
theorem boundedVariationOn_sub
    {first second : Time → Value} {interval : Set Time}
    (hFirst : BoundedVariationOn first interval)
    (hSecond : BoundedVariationOn second interval) :
    BoundedVariationOn (first - second) interval := by
  rw [sub_eq_add_neg]
  exact boundedVariationOn_add hFirst (boundedVariationOn_neg hSecond)

/-- Every constant path has bounded variation. -/
theorem boundedVariationOn_const (value : Value) (interval : Set Time) :
    BoundedVariationOn (fun _ : Time => value) interval := by
  rw [BoundedVariationOn]
  have hZero : eVariationOn (fun _ : Time => value) interval = 0 :=
    eVariationOn.constant_on (f := fun _ : Time => value)
      (s := interval) (by
        rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
        rfl)
  rw [hZero]
  exact ENNReal.zero_ne_top

/-- A finite pointwise sum of bounded-variation paths has bounded variation. -/
theorem boundedVariationOn_finite_sum
    (path : Coordinate → Time → Value) (interval : Set Time)
    (hPath : ∀ coordinate, BoundedVariationOn (path coordinate) interval) :
    BoundedVariationOn (fun time => ∑ coordinate, path coordinate time) interval := by
  classical
  have hFinset : ∀ coordinates : Finset Coordinate,
      BoundedVariationOn
        (fun time => ∑ coordinate ∈ coordinates, path coordinate time) interval := by
    intro coordinates
    induction coordinates using Finset.induction_on with
    | empty =>
        simpa using boundedVariationOn_const (Time := Time) (0 : Value) interval
    | @insert coordinate coordinates hCoordinate hInduction =>
        have hHead := hPath coordinate
        simpa only [Finset.sum_insert hCoordinate, Pi.add_def] using
          boundedVariationOn_add hHead hInduction
  exact hFinset Finset.univ

/-- A globally monotone real path has bounded variation on every bounded open interval. -/
theorem boundedVariationOn_Ioo_of_monotone
    {path : ℝ → ℝ} (hPath : Monotone path) (start finish : ℝ) :
    BoundedVariationOn path (Ioo start finish) := by
  by_cases hOrder : start ≤ finish
  · have hClosedBound :
        eVariationOn path (Icc start finish) ≤
          ENNReal.ofReal (path finish - path start) := by
      simpa only [univ_inter] using
        (MonotoneOn.eVariationOn_eq (hPath.monotoneOn univ)
          (a := start) (b := finish) (mem_univ start) (mem_univ finish)).le
    have hClosed : BoundedVariationOn path (Icc start finish) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hClosedBound
    exact hClosed.mono Ioo_subset_Icc_self
  · have hEmpty : Ioo start finish = ∅ :=
      Ioo_eq_empty (not_lt.mpr (le_of_not_ge hOrder))
    rw [hEmpty]
    rw [BoundedVariationOn, eVariationOn.subsingleton path subsingleton_empty]
    exact ENNReal.zero_ne_top

/-- Finite-coordinate `l1` paths have bounded variation when every scalar coordinate does. -/
theorem boundedVariationOn_finiteCoordinateL1Value_of_coordinate
    (path : Time → FiniteCoordinateL1Value Coordinate) (interval : Set Time)
    (hCoordinate : ∀ coordinate,
      BoundedVariationOn (fun time => path time coordinate) interval) :
    BoundedVariationOn path interval := by
  have hVariationBound :
      eVariationOn path interval ≤
        ∑ coordinate, eVariationOn (fun time => path time coordinate) interval := by
    apply iSup_le
    rintro ⟨count, sampledPath, hMonotone, hSampledPath⟩
    calc
      (∑ index ∈ Finset.range count,
          edist (path (sampledPath (index + 1))) (path (sampledPath index))) =
          ∑ index ∈ Finset.range count, ∑ coordinate,
            edist (path (sampledPath (index + 1)) coordinate)
              (path (sampledPath index) coordinate) := by
        apply Finset.sum_congr rfl
        intro index _hIndex
        exact PiLp.edist_eq_of_L1 _ _
      _ = ∑ coordinate, ∑ index ∈ Finset.range count,
          edist (path (sampledPath (index + 1)) coordinate)
            (path (sampledPath index) coordinate) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ coordinate,
          eVariationOn (fun time => path time coordinate) interval := by
        apply Finset.sum_le_sum
        intro coordinate _hCoordinate
        exact eVariationOn.sum_le (f := fun time => path time coordinate)
          (n := count) hMonotone hSampledPath
  apply ne_top_of_le_ne_top
  · have hFiniteSum :=
      (ENNReal.sum_ne_top
        (s := Finset.univ)
        (f := fun coordinate =>
          eVariationOn (fun time => path time coordinate) interval)).mpr
        (fun coordinate _hCoordinate => hCoordinate coordinate)
    exact hFiniteSum
  · exact hVariationBound

end FiniteIntervalBVAlgebra

/-- Scalar BV data with a right-continuous modification and its finite signed interior
Stieltjes derivative. -/
structure ScalarFiniteIntervalCadlagDerivativeWitness
    (representative : ℝ → ℝ) (duration : ℝ) where
  /-- Right-continuous modification of the original scalar representative. -/
  modification : ℝ → ℝ
  /-- Finite signed derivative restricted to the open physical interval. -/
  derivative : VagueSignedMeasure ℝ
  /-- The derivative has no mass outside the open physical interval. -/
  derivative_restrict_openInterval :
    derivative.toSignedMeasure.restrict (Ioo 0 duration) = derivative.toSignedMeasure
  /-- Equality with the original representative in the open-interval Lebesgue class. -/
  eventuallyEq :
    modification =ᵐ[finiteOpenIntervalVolume duration] representative
  /-- Global right continuity of the selected modification. -/
  rightContinuous : ∀ time, ContinuousWithinAt modification (Ici time) time
  /-- Existence of every finite left limit, including the physical terminal trace. -/
  hasLeftLimit : ∀ time, ∃ leftTrace : ℝ,
    Tendsto modification (𝓝[<] time) (𝓝 leftTrace)
  /-- Exact signed-measure increment on every compact interior half-open interval. -/
  derivative_Ioc : ∀ {start finish : ℝ},
    0 ≤ start → start ≤ finish → finish < duration →
      derivative.toSignedMeasure (Ioc start finish) =
        modification finish - modification start

namespace ScalarFiniteIntervalCadlagDerivativeWitness

/-- Construct the finite signed interior Stieltjes derivative of a scalar BV representative. -/
theorem exists_of_boundedVariationOn
    {representative : ℝ → ℝ} {duration : ℝ}
    (hDuration : 0 < duration)
    (hVariation : BoundedVariationOn representative (Ioo 0 duration)) :
    Nonempty (ScalarFiniteIntervalCadlagDerivativeWitness representative duration) := by
  obtain ⟨positivePart, negativePart, hPositiveMonotone, hNegativeMonotone,
      hAgreement⟩ :=
    FiniteIntervalCadlagConstruction.exists_global_monotone_decomposition_of_boundedVariationOn
      (nonempty_Ioo.mpr hDuration) hVariation
  let positiveCadlag : StieltjesFunction ℝ := hPositiveMonotone.stieltjesFunction
  let negativeCadlag : StieltjesFunction ℝ := hNegativeMonotone.stieltjesFunction
  let modification : ℝ → ℝ := positiveCadlag - negativeCadlag
  let positiveMeasure : Measure ℝ := positiveCadlag.measure.restrict (Ioo 0 duration)
  let negativeMeasure : Measure ℝ := negativeCadlag.measure.restrict (Ioo 0 duration)
  have hPositiveMeasureFinite : positiveCadlag.measure (Ioo 0 duration) ≠ ∞ := by
    rw [positiveCadlag.measure_Ioo]
    exact ENNReal.ofReal_ne_top
  have hNegativeMeasureFinite : negativeCadlag.measure (Ioo 0 duration) ≠ ∞ := by
    rw [negativeCadlag.measure_Ioo]
    exact ENNReal.ofReal_ne_top
  let : IsFiniteMeasure positiveMeasure :=
    isFiniteMeasure_restrict.mpr hPositiveMeasureFinite
  let : IsFiniteMeasure negativeMeasure :=
    isFiniteMeasure_restrict.mpr hNegativeMeasureFinite
  let derivative : VagueSignedMeasure ℝ :=
    positiveMeasure.toSignedMeasure - negativeMeasure.toSignedMeasure
  let exceptional : Set ℝ :=
    {time | ¬ContinuousAt positivePart time} ∪
      {time | ¬ContinuousAt negativePart time}
  have hExceptional : exceptional.Countable :=
    hPositiveMonotone.countable_not_continuousAt.union
      hNegativeMonotone.countable_not_continuousAt
  have hEventually :
      modification =ᵐ[finiteOpenIntervalVolume duration] representative := by
    change ∀ᵐ time ∂volume.restrict (Ioo 0 duration),
      modification time = representative time
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hExceptional.ae_notMem volume] with time hTime
    intro hMembership
    have hPositiveContinuous : ContinuousAt positivePart time := by
      exact Classical.not_not.mp fun hNot => hTime (Or.inl hNot)
    have hNegativeContinuous : ContinuousAt negativePart time := by
      exact Classical.not_not.mp fun hNot => hTime (Or.inr hNot)
    have hPositiveRight : positiveCadlag time = positivePart time := by
      change rightLim positivePart time = positivePart time
      exact hPositiveContinuous.continuousWithinAt.rightLim_eq
    have hNegativeRight : negativeCadlag time = negativePart time := by
      change rightLim negativePart time = negativePart time
      exact hNegativeContinuous.continuousWithinAt.rightLim_eq
    rw [show modification time = positiveCadlag time - negativeCadlag time by rfl,
      hPositiveRight, hNegativeRight, ← Pi.sub_apply, ← hAgreement hMembership]
  have hDerivativeRestriction :
      derivative.toSignedMeasure.restrict (Ioo 0 duration) =
        derivative.toSignedMeasure := by
    have hPositiveRestriction :
        positiveMeasure.restrict (Ioo 0 duration) = positiveMeasure := by
      dsimp only [positiveMeasure]
      rw [Measure.restrict_restrict measurableSet_Ioo, inter_self]
    have hNegativeRestriction :
        negativeMeasure.restrict (Ioo 0 duration) = negativeMeasure := by
      dsimp only [negativeMeasure]
      rw [Measure.restrict_restrict measurableSet_Ioo, inter_self]
    change (positiveMeasure.toSignedMeasure - negativeMeasure.toSignedMeasure).restrict
        (Ioo 0 duration) = positiveMeasure.toSignedMeasure - negativeMeasure.toSignedMeasure
    rw [VectorMeasure.restrict_sub,
      Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure
        positiveMeasure (Ioo 0 duration) measurableSet_Ioo,
      Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure
        negativeMeasure (Ioo 0 duration) measurableSet_Ioo]
    congr 1
    · exact Measure.toSignedMeasure_congr hPositiveRestriction
    · exact Measure.toSignedMeasure_congr hNegativeRestriction
  refine ⟨⟨modification, derivative, hDerivativeRestriction, hEventually, ?_, ?_, ?_⟩⟩
  · intro time
    exact (positiveCadlag.right_continuous time).sub
      (negativeCadlag.right_continuous time)
  · intro time
    refine ⟨leftLim positiveCadlag time - leftLim negativeCadlag time, ?_⟩
    exact (positiveCadlag.mono.tendsto_leftLim time).sub
      (negativeCadlag.mono.tendsto_leftLim time)
  · intro start finish hStart hOrder hFinish
    have hSubset : Ioc start finish ⊆ Ioo 0 duration := by
      intro time hTime
      exact ⟨hStart.trans_lt hTime.1, hTime.2.trans_lt hFinish⟩
    have hIntersection : Ioc start finish ∩ Ioo 0 duration = Ioc start finish :=
      inter_eq_left.mpr hSubset
    rw [show derivative.toSignedMeasure =
        positiveMeasure.toSignedMeasure - negativeMeasure.toSignedMeasure by rfl,
      Measure.toSignedMeasure_sub_apply measurableSet_Ioc]
    change positiveMeasure.real (Ioc start finish) -
        negativeMeasure.real (Ioc start finish) = _
    dsimp only [positiveMeasure, negativeMeasure]
    rw [measureReal_def, measureReal_def,
      Measure.restrict_apply measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc, hIntersection,
      positiveCadlag.measure_Ioc, negativeCadlag.measure_Ioc,
      ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
    · dsimp only [modification]
      simp only [Pi.sub_apply]
      ring
    · exact sub_nonneg.mpr (negativeCadlag.mono hOrder)
    · exact sub_nonneg.mpr (positiveCadlag.mono hOrder)

end ScalarFiniteIntervalCadlagDerivativeWitness

/-- The candidate derivative measures genuinely arise from one right-continuous representative of
the `L1` class, with exact Stieltjes increments on every compact interior half-open interval. -/
def HasFiniteIntervalCadlagDerivativeRealization
    {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}
    (path : FiniteIntervalL1DerivativePath Coordinate duration) : Prop :=
  ∃ representative : FiniteIntervalCadlagRepresentative path.toL1Path,
    (∀ coordinate,
      (path.derivative coordinate).toSignedMeasure.restrict (Ioo 0 duration) =
        (path.derivative coordinate).toSignedMeasure) ∧
      ∀ (coordinate : Coordinate) {start finish : ℝ},
        0 ≤ start → start ≤ finish → finish < duration →
          (path.derivative coordinate).toSignedMeasure (Ioc start finish) =
            representative.representative finish coordinate -
              representative.representative start coordinate

/-- The actual finite-coordinate hybrid BV derivative graph.  The only data field is the native
strong-`L1` plus vague-derivative carrier; bounded variation and derivative compatibility are
proofs.  Thus different representative witnesses do not create duplicate macroscopic states. -/
structure FiniteIntervalHybridBVPath
    (Coordinate : Type u) [Fintype Coordinate] (duration : ℝ) where
  /-- Native path-and-derivative data carrying the published hybrid topology. -/
  toDerivativePath : FiniteIntervalL1DerivativePath Coordinate duration
  /-- Quotient-level finite essential variation. -/
  hasBoundedVariation :
    FiniteIntervalL1Path.HasBoundedVariation toDerivativePath.toL1Path
  /-- Existence of a compatible right-continuous Stieltjes realization. -/
  hasCadlagDerivativeRealization :
    HasFiniteIntervalCadlagDerivativeRealization toDerivativePath

namespace FiniteIntervalHybridBVPath

variable {Coordinate : Type u} [Fintype Coordinate] {duration : ℝ}

/-- Equality of hybrid BV paths is equality of their `L1` quotient and derivative measures;
representative witnesses are proof-irrelevant. -/
@[ext]
theorem ext {first second : FiniteIntervalHybridBVPath Coordinate duration}
    (hData : first.toDerivativePath = second.toDerivativePath) : first = second := by
  cases first
  cases second
  simp_all

/-- The published topology is exactly the subspace topology inherited from the native
strong-`L1` plus vague-derivative graph data. -/
instance instTopologicalSpace :
    TopologicalSpace (FiniteIntervalHybridBVPath Coordinate duration) :=
  TopologicalSpace.induced toDerivativePath inferInstance

/-- The carrier's measurable structure is definitionally the Borel sigma algebra of its hybrid
topology. -/
instance instMeasurableSpace :
    MeasurableSpace (FiniteIntervalHybridBVPath Coordinate duration) :=
  borel (FiniteIntervalHybridBVPath Coordinate duration)

/-- The published measurable structure is registered as the Borel structure of the hybrid
topology. -/
instance instBorelSpace :
    BorelSpace (FiniteIntervalHybridBVPath Coordinate duration) :=
  ⟨rfl⟩

/-- Borel compatibility is definitional, not an imported measurability assumption. -/
theorem measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace
      (FiniteIntervalHybridBVPath Coordinate duration)) =
        borel (FiniteIntervalHybridBVPath Coordinate duration) :=
  rfl

/-- Forgetting the graph proofs induces the exact hybrid topology. -/
theorem isInducing_toDerivativePath :
    Topology.IsInducing
      (toDerivativePath : FiniteIntervalHybridBVPath Coordinate duration →
        FiniteIntervalL1DerivativePath Coordinate duration) :=
  ⟨rfl⟩

/-- The graph inclusion is injective because all remaining fields are propositions. -/
theorem injective_toDerivativePath :
    Function.Injective
      (toDerivativePath : FiniteIntervalHybridBVPath Coordinate duration →
        FiniteIntervalL1DerivativePath Coordinate duration) :=
  fun _ _ => ext

/-- The hybrid BV graph is topologically embedded in its native strong-`L1` plus vague ambient
carrier. -/
theorem isEmbedding_toDerivativePath :
    Topology.IsEmbedding
      (toDerivativePath : FiniteIntervalHybridBVPath Coordinate duration →
        FiniteIntervalL1DerivativePath Coordinate duration) :=
  ⟨isInducing_toDerivativePath, injective_toDerivativePath⟩

/-- Exact convergence characterization on the graph: strong `L1` path convergence and convergence
against every zero-extended `C₀` derivative test vanishing off the open physical interval. -/
theorem tendsto_iff
    {Index : Type*} {filter : Filter Index}
    {paths : Index → FiniteIntervalHybridBVPath Coordinate duration}
    {limit : FiniteIntervalHybridBVPath Coordinate duration} :
    Tendsto paths filter (𝓝 limit) ↔
      Tendsto
          (fun index => (paths index).toDerivativePath.toL1Path)
          filter (𝓝 limit.toDerivativePath.toL1Path) ∧
        ∀ coordinate (test : FiniteOpenIntervalVanishingContinuousTest duration),
          Tendsto
            (fun index => ((paths index).toDerivativePath.derivative coordinate)
              |>.continuousTestIntegral test.1)
            filter (nhds ((limit.toDerivativePath.derivative coordinate)
              |>.continuousTestIntegral test.1)) := by
  rw [isInducing_toDerivativePath.tendsto_nhds_iff,
    FiniteIntervalL1DerivativePath.tendsto_iff]
  rfl

/-- Canonically selected càdlàg representative whose Stieltjes derivatives are the derivative
coordinates carried by the hybrid graph.  The choice is used only to expose pointwise traces;
hybrid-path equality remains equality of quotient and derivative data. -/
noncomputable def cadlagRepresentative
    (path : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteIntervalCadlagRepresentative path.toDerivativePath.toL1Path :=
  Classical.choose path.hasCadlagDerivativeRealization

/-- Every selected hybrid representative recovers the carried derivative measures on compact
interior half-open intervals. -/
theorem derivative_apply_Ioc_eq_cadlagRepresentative_sub
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate) {start finish : ℝ}
    (hStart : 0 ≤ start) (hOrder : start ≤ finish) (hFinish : finish < duration) :
    (path.toDerivativePath.derivative coordinate).toSignedMeasure (Ioc start finish) =
      path.cadlagRepresentative.representative finish coordinate -
        path.cadlagRepresentative.representative start coordinate :=
  (Classical.choose_spec path.hasCadlagDerivativeRealization).2
    coordinate hStart hOrder hFinish

/-- On the admissible hybrid graph, the strong-`L1` path determines the entire derivative data.
The selected càdlàg realizations agree on `[0,T)`, so their Stieltjes increments agree on every
compact interior interval.  An increasing interior exhaustion then recovers each derivative,
whose support is restricted to `(0,T)`. -/
theorem injective_toL1Path :
    Function.Injective
      (fun path : FiniteIntervalHybridBVPath Coordinate duration =>
        path.toDerivativePath.toL1Path) := by
  intro first second hL1Path
  have hRepresentativeEquality :
      Set.EqOn first.cadlagRepresentative.representative
        second.cadlagRepresentative.representative (Ico 0 duration) :=
    FiniteIntervalCadlagRepresentative.eqOn_Ico_of_paths_eq
      first.cadlagRepresentative second.cadlagRepresentative hL1Path
  have hDerivative :
      first.toDerivativePath.derivative = second.toDerivativePath.derivative := by
    funext coordinate
    let firstDerivative :=
      (first.toDerivativePath.derivative coordinate).toSignedMeasure
    let secondDerivative :=
      (second.toDerivativePath.derivative coordinate).toSignedMeasure
    have hFirstSupport :
        firstDerivative.restrict (Ioo 0 duration) = firstDerivative :=
      (Classical.choose_spec first.hasCadlagDerivativeRealization).1 coordinate
    have hSecondSupport :
        secondDerivative.restrict (Ioo 0 duration) = secondDerivative :=
      (Classical.choose_spec second.hasCadlagDerivativeRealization).1 coordinate
    apply signedMeasure_eq_of_apply_Ioc_eq_of_restrict_openInterval
      firstDerivative secondDerivative hFirstSupport hSecondSupport
    intro start finish hStart hOrder hFinish
    rw [show firstDerivative =
          (first.toDerivativePath.derivative coordinate).toSignedMeasure by rfl,
      show secondDerivative =
          (second.toDerivativePath.derivative coordinate).toSignedMeasure by rfl,
      first.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
        hStart hOrder hFinish,
      second.derivative_apply_Ioc_eq_cadlagRepresentative_sub coordinate
        hStart hOrder hFinish]
    have hStartMembership : start ∈ Ico 0 duration :=
      ⟨hStart, hOrder.trans_lt hFinish⟩
    have hFinishMembership : finish ∈ Ico 0 duration :=
      ⟨hStart.trans hOrder, hFinish⟩
    rw [hRepresentativeEquality hStartMembership,
      hRepresentativeEquality hFinishMembership]
  apply FiniteIntervalHybridBVPath.ext
  exact FiniteIntervalL1DerivativePath.ext hL1Path hDerivative

/-- The strong-`L1` projection is continuous from the published hybrid topology. -/
theorem continuous_toL1Path :
    Continuous
      (fun path : FiniteIntervalHybridBVPath Coordinate duration =>
        path.toDerivativePath.toL1Path) :=
  FiniteIntervalL1DerivativePath.continuous_toL1Path.comp
    isEmbedding_toDerivativePath.continuous

/-- The hybrid BV graph is Hausdorff even though its ambient derivative carrier deliberately
forgets endpoint atoms and need not be `T0`.  Separation is inherited from the continuous,
injective strong-`L1` projection after derivative uniqueness on the admissible graph. -/
instance instT2Space : T2Space (FiniteIntervalHybridBVPath Coordinate duration) :=
  T2Space.of_injective_continuous injective_toL1Path continuous_toL1Path

/-- The selected hybrid representative's initial trace is recovered separately from the open
physical-interval `L1` quotient. -/
noncomputable def initialTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration) :
    FiniteCoordinateL1Value Coordinate :=
  path.cadlagRepresentative.initialTrace

/-- Any explicitly supplied càdlàg representative of the same hybrid path recovers the
canonical initial trace on a positive physical interval. -/
theorem initialTrace_eq_of_cadlagRepresentative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (representative : FiniteIntervalCadlagRepresentative
      path.toDerivativePath.toL1Path)
    (hDuration : 0 < duration) :
    path.initialTrace = representative.initialTrace :=
  FiniteIntervalCadlagRepresentative.eqOn_Ico_of_same_path
    path.cadlagRepresentative representative ⟨le_rfl, hDuration⟩

/-- The selected hybrid representative's terminal left trace is recovered separately from the
open physical-interval `L1` quotient. -/
noncomputable def terminalTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) : FiniteCoordinateL1Value Coordinate :=
  path.cadlagRepresentative.terminalTrace hDuration

/-- The selected representative converges from physical time zero to the separately recovered
initial trace. -/
theorem tendsto_initialTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) :
    Tendsto path.cadlagRepresentative.representative (𝓝[Ici 0] 0)
      (𝓝 path.initialTrace) :=
  path.cadlagRepresentative.tendsto_initialTrace hDuration

/-- The selected representative converges from the left to the separately recovered terminal
trace. -/
theorem tendsto_terminalTrace
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hDuration : 0 < duration) :
    Tendsto path.cadlagRepresentative.representative (𝓝[<] duration)
      (𝓝 (path.terminalTrace hDuration)) :=
  path.cadlagRepresentative.tendsto_terminalTrace hDuration

/-- Build a hybrid path from coordinatewise scalar Stieltjes witnesses.  The resulting derivative
is definitionally the supplied family; this constructor is useful when a finite-step observation
needs an explicit, measurably parameterized derivative rather than an existence choice. -/
noncomputable def ofScalarDerivativeWitnesses
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresents : FiniteIntervalL1Path.Represents path representative)
    (hVariation : FiniteIntervalL1Path.HasBoundedVariation path)
    (coordinateWitness : ∀ coordinate : Coordinate,
      ScalarFiniteIntervalCadlagDerivativeWitness
        (fun time => representative time coordinate) duration) :
    FiniteIntervalHybridBVPath Coordinate duration := by
  let coordinatePath : ℝ → Coordinate → ℝ :=
    fun time coordinate => (coordinateWitness coordinate).modification time
  let coordinateEquivalence :
      FiniteCoordinateL1Value Coordinate ≃L[ℝ] (Coordinate → ℝ) :=
    PiLp.continuousLinearEquiv 1 ℝ fun _ : Coordinate => ℝ
  let modification : ℝ → FiniteCoordinateL1Value Coordinate :=
    fun time => coordinateEquivalence.symm (coordinatePath time)
  have hModificationCoordinate (time : ℝ) (coordinate : Coordinate) :
      modification time coordinate =
        (coordinateWitness coordinate).modification time := by
    change (coordinateEquivalence (coordinateEquivalence.symm
      (coordinatePath time))) coordinate = coordinatePath time coordinate
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hModificationEventually :
      modification =ᵐ[finiteOpenIntervalVolume duration] representative := by
    have hCoordinateEventually : ∀ coordinate : Coordinate,
        (coordinateWitness coordinate).modification
          =ᵐ[finiteOpenIntervalVolume duration]
            (fun time => representative time coordinate) :=
      fun coordinate => (coordinateWitness coordinate).eventuallyEq
    filter_upwards [ae_all_iff.mpr hCoordinateEventually] with time hTime
    apply coordinateEquivalence.injective
    funext coordinate
    change modification time coordinate = representative time coordinate
    rw [hModificationCoordinate]
    exact hTime coordinate
  let hRepresentativeMemLp := Classical.choose hRepresents
  have hRepresentativeQuotient := Classical.choose_spec hRepresents
  have hModificationMemLp :
      MemLp modification 1 (finiteOpenIntervalVolume duration) :=
    hRepresentativeMemLp.ae_eq hModificationEventually.symm
  have hModificationRepresents :
      FiniteIntervalL1Path.Represents path modification := by
    refine ⟨hModificationMemLp, ?_⟩
    exact hModificationMemLp.toLp_congr hRepresentativeMemLp
      hModificationEventually |>.trans hRepresentativeQuotient
  let cadlagRepresentative : FiniteIntervalCadlagRepresentative path :=
    { representative := modification
      represents := hModificationRepresents
      rightContinuous := by
        intro time _hTime
        apply coordinateEquivalence.symm.continuous.continuousAt.comp_continuousWithinAt
        exact continuousWithinAt_pi.mpr fun coordinate =>
          (coordinateWitness coordinate).rightContinuous time
      hasLeftLimit := by
        intro time _hTime
        choose coordinateTrace hCoordinateTrace using fun coordinate =>
          (coordinateWitness coordinate).hasLeftLimit time
        refine ⟨coordinateEquivalence.symm coordinateTrace, ?_⟩
        apply coordinateEquivalence.symm.continuousAt.tendsto.comp
        exact tendsto_pi_nhds.mpr hCoordinateTrace }
  let derivativePath : FiniteIntervalL1DerivativePath Coordinate duration :=
    { toL1Path := path
      derivative := fun coordinate => (coordinateWitness coordinate).derivative }
  refine
    { toDerivativePath := derivativePath
      hasBoundedVariation := hVariation
      hasCadlagDerivativeRealization := ?_ }
  refine ⟨cadlagRepresentative, ?_, ?_⟩
  · intro coordinate
    exact (coordinateWitness coordinate).derivative_restrict_openInterval
  · intro coordinate start finish hStart hOrder hFinish
    have hIncrement := (coordinateWitness coordinate).derivative_Ioc
      hStart hOrder hFinish
    change (coordinateWitness coordinate).derivative.toSignedMeasure
      (Ioc start finish) =
        modification finish coordinate - modification start coordinate
    rw [hModificationCoordinate, hModificationCoordinate]
    exact hIncrement

/-- The explicit-witness constructor retains the supplied `L1` quotient definitionally. -/
@[simp]
theorem ofScalarDerivativeWitnesses_toL1Path
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresents : FiniteIntervalL1Path.Represents path representative)
    (hVariation : FiniteIntervalL1Path.HasBoundedVariation path)
    (coordinateWitness : ∀ coordinate : Coordinate,
      ScalarFiniteIntervalCadlagDerivativeWitness
        (fun time => representative time coordinate) duration) :
    (ofScalarDerivativeWitnesses path representative hRepresents hVariation
      coordinateWitness).toDerivativePath.toL1Path = path := by
  simp only [ofScalarDerivativeWitnesses]

/-- The explicit-witness constructor retains each supplied derivative definitionally. -/
@[simp]
theorem ofScalarDerivativeWitnesses_derivative
    (path : FiniteIntervalL1Path Coordinate duration)
    (representative : ℝ → FiniteCoordinateL1Value Coordinate)
    (hRepresents : FiniteIntervalL1Path.Represents path representative)
    (hVariation : FiniteIntervalL1Path.HasBoundedVariation path)
    (coordinateWitness : ∀ coordinate : Coordinate,
      ScalarFiniteIntervalCadlagDerivativeWitness
        (fun time => representative time coordinate) duration)
    (coordinate : Coordinate) :
    (ofScalarDerivativeWitnesses path representative hRepresents hVariation
      coordinateWitness).toDerivativePath.derivative coordinate =
        (coordinateWitness coordinate).derivative := by
  simp only [ofScalarDerivativeWitnesses]

/-- Every positive-duration essentially BV finite-coordinate `L1` path has an inhabitant of the
hybrid derivative graph whose path quotient is exactly the supplied path. -/
theorem exists_with_toL1Path_eq
    (path : FiniteIntervalL1Path Coordinate duration)
    (hDuration : 0 < duration)
    (hVariation : FiniteIntervalL1Path.HasBoundedVariation path) :
    ∃ hybridPath : FiniteIntervalHybridBVPath Coordinate duration,
      hybridPath.toDerivativePath.toL1Path = path := by
  obtain ⟨representative, hRepresents, hRepresentativeVariation⟩ :=
    FiniteIntervalL1Path.hasBoundedVariation_iff_exists_representative path |>.mp hVariation
  have hCoordinateVariation (coordinate : Coordinate) :
      BoundedVariationOn (fun time => representative time coordinate) (Ioo 0 duration) := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) (p := 1) (fun _ : Coordinate => ℝ) coordinate).lipschitzWith
        |>.comp_boundedVariationOn hRepresentativeVariation
  have hCoordinateWitness : ∀ coordinate : Coordinate,
      Nonempty (ScalarFiniteIntervalCadlagDerivativeWitness
        (fun time => representative time coordinate) duration) := by
    intro coordinate
    exact ScalarFiniteIntervalCadlagDerivativeWitness.exists_of_boundedVariationOn
      hDuration (hCoordinateVariation coordinate)
  let coordinateWitness (coordinate : Coordinate) :
      ScalarFiniteIntervalCadlagDerivativeWitness
        (fun time => representative time coordinate) duration :=
    Classical.choice (hCoordinateWitness coordinate)
  let coordinatePath : ℝ → Coordinate → ℝ :=
    fun time coordinate => (coordinateWitness coordinate).modification time
  let coordinateEquivalence :
      FiniteCoordinateL1Value Coordinate ≃L[ℝ] (Coordinate → ℝ) :=
    PiLp.continuousLinearEquiv 1 ℝ fun _ : Coordinate => ℝ
  let modification : ℝ → FiniteCoordinateL1Value Coordinate :=
    fun time => coordinateEquivalence.symm (coordinatePath time)
  have hModificationCoordinate (time : ℝ) (coordinate : Coordinate) :
      modification time coordinate =
        (coordinateWitness coordinate).modification time := by
    change (coordinateEquivalence (coordinateEquivalence.symm
      (coordinatePath time))) coordinate = coordinatePath time coordinate
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hModificationEventually :
      modification =ᵐ[finiteOpenIntervalVolume duration] representative := by
    have hCoordinateEventually : ∀ coordinate : Coordinate,
        (coordinateWitness coordinate).modification
          =ᵐ[finiteOpenIntervalVolume duration]
            (fun time => representative time coordinate) :=
      fun coordinate => (coordinateWitness coordinate).eventuallyEq
    filter_upwards [ae_all_iff.mpr hCoordinateEventually] with time hTime
    apply coordinateEquivalence.injective
    funext coordinate
    change modification time coordinate = representative time coordinate
    rw [hModificationCoordinate]
    exact hTime coordinate
  obtain ⟨hRepresentativeMemLp, hRepresentativeQuotient⟩ := hRepresents
  have hModificationMemLp :
      MemLp modification 1 (finiteOpenIntervalVolume duration) :=
    hRepresentativeMemLp.ae_eq hModificationEventually.symm
  have hModificationRepresents :
      FiniteIntervalL1Path.Represents path modification := by
    refine ⟨hModificationMemLp, ?_⟩
    exact hModificationMemLp.toLp_congr hRepresentativeMemLp
      hModificationEventually |>.trans hRepresentativeQuotient
  let cadlagRepresentative : FiniteIntervalCadlagRepresentative path :=
    { representative := modification
      represents := hModificationRepresents
      rightContinuous := by
        intro time _hTime
        apply coordinateEquivalence.symm.continuous.continuousAt.comp_continuousWithinAt
        exact continuousWithinAt_pi.mpr fun coordinate =>
          (coordinateWitness coordinate).rightContinuous time
      hasLeftLimit := by
        intro time _hTime
        choose coordinateTrace hCoordinateTrace using fun coordinate =>
          (coordinateWitness coordinate).hasLeftLimit time
        refine ⟨coordinateEquivalence.symm coordinateTrace, ?_⟩
        apply coordinateEquivalence.symm.continuousAt.tendsto.comp
        exact tendsto_pi_nhds.mpr hCoordinateTrace }
  let derivativePath : FiniteIntervalL1DerivativePath Coordinate duration :=
    { toL1Path := path
      derivative := fun coordinate => (coordinateWitness coordinate).derivative }
  have hDerivativeRealization :
      HasFiniteIntervalCadlagDerivativeRealization derivativePath := by
    refine ⟨cadlagRepresentative, ?_, ?_⟩
    · intro coordinate
      exact (coordinateWitness coordinate).derivative_restrict_openInterval
    intro coordinate start finish hStart hOrder hFinish
    have hIncrement := (coordinateWitness coordinate).derivative_Ioc
      hStart hOrder hFinish
    change (coordinateWitness coordinate).derivative.toSignedMeasure
      (Ioc start finish) =
        modification finish coordinate - modification start coordinate
    rw [hModificationCoordinate, hModificationCoordinate]
    exact hIncrement
  refine ⟨⟨derivativePath, hVariation, hDerivativeRealization⟩, rfl⟩

/-- Finite-rate entry requires every signed coordinate derivative to be absolutely continuous
with respect to Lebesgue measure restricted to the open physical interval.  This is a proper
subdomain predicate on the BV carrier, not part of carrier identity. -/
def HasAbsolutelyContinuousDerivative
    (path : FiniteIntervalHybridBVPath Coordinate duration) : Prop :=
  ∀ coordinate,
    (path.toDerivativePath.derivative coordinate).toSignedMeasure ≪ᵥ
      (finiteOpenIntervalVolume duration).toENNRealVectorMeasure

/-- Radon--Nikodym time derivative of one coordinate on the absolutely continuous subdomain.  The
definition is total, while the reconstruction theorem below requires the named domain predicate. -/
noncomputable def derivativeDensity
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate) : ℝ → ℝ :=
  SignedMeasure.rnDeriv
    (path.toDerivativePath.derivative coordinate).toSignedMeasure
    (finiteOpenIntervalVolume duration)

/-- The derivative density is measurable for every coordinate. -/
theorem measurable_derivativeDensity
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (coordinate : Coordinate) :
    Measurable (path.derivativeDensity coordinate) :=
  SignedMeasure.measurable_rnDeriv _ _

/-- On the absolutely continuous finite-rate subdomain, integrating the Radon--Nikodym derivative
reconstructs the exact signed derivative measure. -/
theorem withDensity_derivativeDensity_eq_derivative
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative)
    (coordinate : Coordinate) :
    (finiteOpenIntervalVolume duration).withDensityᵥ
        (path.derivativeDensity coordinate) =
      (path.toDerivativePath.derivative coordinate).toSignedMeasure := by
  let : SigmaFinite (finiteOpenIntervalVolume duration) := by
    dsimp only [finiteOpenIntervalVolume]
    infer_instance
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
    (hAbsolutelyContinuous coordinate)

/-- On the absolutely continuous subdomain, every selected càdlàg coordinate is reconstructed
from its initial value and the integral of its Radon--Nikodym derivative over the elapsed
half-open physical interval. -/
theorem cadlagRepresentative_eq_initial_add_integral_derivativeDensity
    (path : FiniteIntervalHybridBVPath Coordinate duration)
    (hAbsolutelyContinuous : path.HasAbsolutelyContinuousDerivative)
    (coordinate : Coordinate) {time : ℝ}
    (hTimeNonnegative : 0 ≤ time) (hTimeDuration : time < duration) :
    path.cadlagRepresentative.representative time coordinate =
      path.cadlagRepresentative.representative 0 coordinate +
        ∫ point in Ioc 0 time, path.derivativeDensity coordinate point
          ∂finiteOpenIntervalVolume duration := by
  have hDerivativeIncrement :=
    path.derivative_apply_Ioc_eq_cadlagRepresentative_sub
      coordinate (start := 0) (finish := time) (by positivity)
        hTimeNonnegative hTimeDuration
  have hDerivativeIntegral :
      (path.toDerivativePath.derivative coordinate).toSignedMeasure (Ioc 0 time) =
        ∫ point in Ioc 0 time, path.derivativeDensity coordinate point
          ∂finiteOpenIntervalVolume duration := by
    rw [← path.withDensity_derivativeDensity_eq_derivative
      hAbsolutelyContinuous coordinate]
    exact withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv
        (path.toDerivativePath.derivative coordinate).toSignedMeasure
        (finiteOpenIntervalVolume duration))
      measurableSet_Ioc
  rw [hDerivativeIntegral] at hDerivativeIncrement
  linarith

end FiniteIntervalHybridBVPath

end

end FiniteMarkovProcesses

attribute [inherit_doc FiniteMarkovProcesses.FiniteIntervalHybridBVPath.ext]
  FiniteMarkovProcesses.FiniteIntervalHybridBVPath.ext_iff
