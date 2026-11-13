/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Data.ZMod.Basic
public import FiniteMarkovProcesses.Probability.FiniteUniformPMF
public import FiniteMarkovProcesses.Probability.PoissonContactHistory
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Complete driven Poisson-cycle histories

This file constructs a complete registered fixed-horizon history from independent clockwise and
counterclockwise Poisson counts, a uniform state on the three-cycle, and two independent infinite
Haar clock tapes. Reversal exchanges the directional clocks, reflects their registered labels,
and transports the initial state to the terminal cycle state.

The reversal is a measurable involution. Pushing a history law through it exchanges the two
directional intensities exactly. This is a generative point-history carrier, not a càdlàg path.

## Main results

- `drivenCycleHistoryMeasure_clockwiseCountMarginal`: exact clockwise Poisson marginal.
- `drivenCycleHistoryMeasure_counterclockwiseCountMarginal`: exact counterclockwise marginal.
- `drivenCycleHistoryMeasure_injective`: pair-rate identifiability.
- `drivenCycleHistoryReversal_involutive`: exact history-level reversal.
- `map_drivenCycleHistoryReversal`: reversal exchanges the directional history laws.
- `drivenCycleHistoryMeasure_terminalStateMarginal`: stationary uniform endpoint ensemble.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- Complete history: two counts, a three-cycle initial state, and two registered clock tapes. -/
abbrev DrivenCycleHistory :=
  (ℕ × ℕ) × (ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle)))

/-- Uniform probability measure on the three-state cycle. -/
noncomputable def uniformZModThreeMeasure : Measure (ZMod 3) :=
  (finiteUniformPMF (ZMod 3)).toMeasure

/-- The original uniform law on the three cycle states has total mass one. -/
noncomputable instance instIsProbabilityMeasureUniformZModThreeMeasure :
    IsProbabilityMeasure uniformZModThreeMeasure := by
  unfold uniformZModThreeMeasure
  infer_instance

/-- Intensity-independent three-cycle state and two-tape apparatus law. -/
noncomputable def drivenCycleConditionalMeasure :
    Measure (ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))) :=
  uniformZModThreeMeasure.prod (unitClockTapeMeasure.prod unitClockTapeMeasure)

/-- The original cycle-state and two-tape apparatus law has total mass one. -/
noncomputable instance instIsProbabilityMeasureDrivenCycleConditionalMeasure :
    IsProbabilityMeasure drivenCycleConditionalMeasure := by
  unfold drivenCycleConditionalMeasure
  infer_instance

/-- Independent directional Poisson count law. -/
noncomputable def drivenCycleCountMeasure
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) : Measure (ℕ × ℕ) :=
  (poissonMeasure clockwiseIntensity).prod (poissonMeasure counterclockwiseIntensity)

/-- The original product of the two directional Poisson count laws has total mass one. -/
noncomputable instance instIsProbabilityMeasureDrivenCycleCountMeasure
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    IsProbabilityMeasure
      (drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity) := by
  unfold drivenCycleCountMeasure
  infer_instance

/-- Complete driven-cycle history law at two integrated directional intensities. -/
noncomputable def drivenCycleHistoryMeasure
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) : Measure DrivenCycleHistory :=
  (drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity).prod
    drivenCycleConditionalMeasure

/-- The original complete driven-cycle history law has total mass one. -/
noncomputable instance instIsProbabilityMeasureDrivenCycleHistoryMeasure
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    IsProbabilityMeasure
      (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) := by
  unfold drivenCycleHistoryMeasure
  infer_instance

/-- Pair of registered directional contact counts. -/
def DrivenCycleHistory.counts (history : DrivenCycleHistory) : ℕ × ℕ := history.1

/-- Registered clockwise contact count. -/
def DrivenCycleHistory.clockwiseCount (history : DrivenCycleHistory) : ℕ := history.1.1

/-- Registered counterclockwise contact count. -/
def DrivenCycleHistory.counterclockwiseCount (history : DrivenCycleHistory) : ℕ := history.1.2

/-- Initial state on the three-cycle. -/
def DrivenCycleHistory.initialState (history : DrivenCycleHistory) : ZMod 3 := history.2.1

/-- Entire clockwise clock tape, including its inactive suffix. -/
def DrivenCycleHistory.clockwiseTape
    (history : DrivenCycleHistory) : ℕ → UnitAddCircle :=
  history.2.2.1

/-- Entire counterclockwise clock tape, including its inactive suffix. -/
def DrivenCycleHistory.counterclockwiseTape
    (history : DrivenCycleHistory) : ℕ → UnitAddCircle :=
  history.2.2.2

/-- Pair of complete directional clock tapes. -/
def DrivenCycleHistory.clockTapes
    (history : DrivenCycleHistory) : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) :=
  history.2.2

/-- Count-independent state and apparatus record. -/
def DrivenCycleHistory.conditionalRecord
    (history : DrivenCycleHistory) :
    ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle)) :=
  history.2

/-- The count-pair observable is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleCounts : Measurable DrivenCycleHistory.counts := by
  unfold DrivenCycleHistory.counts
  fun_prop

/-- The clockwise-count observable is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleClockwiseCount :
    Measurable DrivenCycleHistory.clockwiseCount := by
  unfold DrivenCycleHistory.clockwiseCount
  fun_prop

/-- The counterclockwise-count observable is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleCounterclockwiseCount :
    Measurable DrivenCycleHistory.counterclockwiseCount := by
  unfold DrivenCycleHistory.counterclockwiseCount
  fun_prop

/-- The initial-state observable is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleInitialState :
    Measurable DrivenCycleHistory.initialState := by
  unfold DrivenCycleHistory.initialState
  fun_prop

/-- The pair of registered tapes is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleClockTapes :
    Measurable DrivenCycleHistory.clockTapes := by
  unfold DrivenCycleHistory.clockTapes
  fun_prop

/-- The clockwise tape is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleClockwiseTape :
    Measurable DrivenCycleHistory.clockwiseTape := by
  unfold DrivenCycleHistory.clockwiseTape
  fun_prop

/-- The counterclockwise tape is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleCounterclockwiseTape :
    Measurable DrivenCycleHistory.counterclockwiseTape := by
  unfold DrivenCycleHistory.counterclockwiseTape
  fun_prop

/-- The conditional state/apparatus record is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleConditionalRecord :
    Measurable DrivenCycleHistory.conditionalRecord := by
  unfold DrivenCycleHistory.conditionalRecord
  fun_prop

/-- Every singleton of the original cycle-state and two-tape apparatus law has zero mass. -/
noncomputable instance instNoAtomsDrivenCycleConditionalMeasure :
    NullSingletonClass drivenCycleConditionalMeasure := by
  unfold drivenCycleConditionalMeasure
  infer_instance

/-- Every singleton of the original complete driven-cycle history law has zero mass. -/
noncomputable instance instNoAtomsDrivenCycleHistoryMeasure
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    NullSingletonClass
      (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) := by
  unfold drivenCycleHistoryMeasure
  infer_instance

/-- Every complete driven-cycle history singleton has zero mass. -/
theorem drivenCycleHistoryMeasure_singleton
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0)
    (history : DrivenCycleHistory) :
    drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity {history} = 0 := by
  exact measure_singleton _

/-- The complete history law has total mass one. -/
theorem drivenCycleHistoryMeasure_univ
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity Set.univ = 1 := by
  exact measure_univ

/-- The joint directional-count marginal is its defining independent Poisson product. -/
theorem drivenCycleHistoryMeasure_countsMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.counts
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity := by
  have hObservable : DrivenCycleHistory.counts =
      (Prod.fst : DrivenCycleHistory → ℕ × ℕ) := by
    funext history
    rfl
  rw [hObservable, drivenCycleHistoryMeasure]
  exact (measurePreserving_fst
      (μ := drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity)
      (ν := drivenCycleConditionalMeasure)).map_eq

/-- The clockwise count marginal is exactly its Poisson law. -/
theorem drivenCycleHistoryMeasure_clockwiseCountMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.clockwiseCount
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      poissonMeasure clockwiseIntensity := by
  have hCounts := measurePreserving_fst
    (μ := drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity)
    (ν := drivenCycleConditionalMeasure)
  have hClockwise := measurePreserving_fst
    (μ := poissonMeasure clockwiseIntensity)
    (ν := poissonMeasure counterclockwiseIntensity)
  have hObservable : DrivenCycleHistory.clockwiseCount =
      (Prod.fst ∘ Prod.fst : DrivenCycleHistory → ℕ) := by
    funext history
    rfl
  rw [hObservable, drivenCycleHistoryMeasure]
  exact (hClockwise.comp hCounts).map_eq

/-- The counterclockwise count marginal is exactly its Poisson law. -/
theorem drivenCycleHistoryMeasure_counterclockwiseCountMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.counterclockwiseCount
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      poissonMeasure counterclockwiseIntensity := by
  have hCounts := measurePreserving_fst
    (μ := drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity)
    (ν := drivenCycleConditionalMeasure)
  have hCounterclockwise := measurePreserving_snd
    (μ := poissonMeasure clockwiseIntensity)
    (ν := poissonMeasure counterclockwiseIntensity)
  have hObservable : DrivenCycleHistory.counterclockwiseCount =
      (Prod.snd ∘ Prod.fst : DrivenCycleHistory → ℕ) := by
    funext history
    rfl
  rw [hObservable, drivenCycleHistoryMeasure]
  exact (hCounterclockwise.comp hCounts).map_eq

/-- The initial three-cycle state is uniformly distributed for every directional rate pair. -/
theorem drivenCycleHistoryMeasure_initialStateMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.initialState
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      uniformZModThreeMeasure := by
  have hConditional := measurePreserving_snd
    (μ := drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity)
    (ν := drivenCycleConditionalMeasure)
  have hState := measurePreserving_fst
    (μ := uniformZModThreeMeasure)
    (ν := unitClockTapeMeasure.prod unitClockTapeMeasure)
  have hObservable : DrivenCycleHistory.initialState =
      (Prod.fst ∘ Prod.snd : DrivenCycleHistory → ZMod 3) := by
    funext history
    rfl
  rw [hObservable, drivenCycleHistoryMeasure]
  exact (hState.comp hConditional).map_eq

/-- Both complete clock tapes have the same independent Haar-product law at every rate pair. -/
theorem drivenCycleHistoryMeasure_clockTapesMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.clockTapes
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      unitClockTapeMeasure.prod unitClockTapeMeasure := by
  have hConditional := measurePreserving_snd
    (μ := drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity)
    (ν := drivenCycleConditionalMeasure)
  have hTapes := measurePreserving_snd
    (μ := uniformZModThreeMeasure)
    (ν := unitClockTapeMeasure.prod unitClockTapeMeasure)
  have hObservable : DrivenCycleHistory.clockTapes =
      (Prod.snd ∘ Prod.snd :
        DrivenCycleHistory → (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle)) := by
    funext history
    rfl
  rw [hObservable, drivenCycleHistoryMeasure]
  exact (hTapes.comp hConditional).map_eq

/-- The clockwise clock tape has the common Haar-product marginal. -/
theorem drivenCycleHistoryMeasure_clockwiseTapeMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.clockwiseTape
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      unitClockTapeMeasure := by
  have hTapes : MeasurePreserving DrivenCycleHistory.clockTapes
      (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity)
      (unitClockTapeMeasure.prod unitClockTapeMeasure) :=
    ⟨measurable_drivenCycleClockTapes,
      drivenCycleHistoryMeasure_clockTapesMarginal _ _⟩
  have hClockwise := measurePreserving_fst
    (μ := unitClockTapeMeasure) (ν := unitClockTapeMeasure)
  have hObservable : DrivenCycleHistory.clockwiseTape =
      (Prod.fst ∘ DrivenCycleHistory.clockTapes : DrivenCycleHistory → ℕ → UnitAddCircle) := by
    funext history
    rfl
  rw [hObservable]
  exact (hClockwise.comp hTapes).map_eq

/-- The counterclockwise clock tape has the common Haar-product marginal. -/
theorem drivenCycleHistoryMeasure_counterclockwiseTapeMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.counterclockwiseTape
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      unitClockTapeMeasure := by
  have hTapes : MeasurePreserving DrivenCycleHistory.clockTapes
      (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity)
      (unitClockTapeMeasure.prod unitClockTapeMeasure) :=
    ⟨measurable_drivenCycleClockTapes,
      drivenCycleHistoryMeasure_clockTapesMarginal _ _⟩
  have hCounterclockwise := measurePreserving_snd
    (μ := unitClockTapeMeasure) (ν := unitClockTapeMeasure)
  have hObservable : DrivenCycleHistory.counterclockwiseTape =
      (Prod.snd ∘ DrivenCycleHistory.clockTapes : DrivenCycleHistory → ℕ → UnitAddCircle) := by
    funext history
    rfl
  rw [hObservable]
  exact (hCounterclockwise.comp hTapes).map_eq

/-- The conditional state/tape law is literally common to the whole two-rate family. -/
theorem drivenCycleHistoryMeasure_commonConditionalFactorization
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity =
      (drivenCycleCountMeasure clockwiseIntensity counterclockwiseIntensity).prod
        drivenCycleConditionalMeasure := rfl

/-- Every exact clockwise count has positive probability at positive clockwise intensity. -/
theorem drivenCycleHistoryMeasure_clockwiseCountSingleton_pos
    {clockwiseIntensity counterclockwiseIntensity : ℝ≥0}
    (hClockwise : 0 < clockwiseIntensity) (count : ℕ) :
    0 < drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity
      (DrivenCycleHistory.clockwiseCount ⁻¹' {count}) := by
  calc
    _ = poissonMeasure clockwiseIntensity {count} := by
      rw [← drivenCycleHistoryMeasure_clockwiseCountMarginal
        clockwiseIntensity counterclockwiseIntensity]
      rw [Measure.map_apply measurable_drivenCycleClockwiseCount
        (MeasurableSet.singleton _)]
    _ = ENNReal.ofReal (poissonCountMassReal clockwiseIntensity count) :=
      poissonMeasure_singleton _ _
    _ > 0 := ENNReal.ofReal_pos.mpr (poissonCountMassReal_pos hClockwise)

/-- Every exact counterclockwise count has positive probability at positive intensity. -/
theorem drivenCycleHistoryMeasure_counterclockwiseCountSingleton_pos
    {clockwiseIntensity counterclockwiseIntensity : ℝ≥0}
    (hCounterclockwise : 0 < counterclockwiseIntensity) (count : ℕ) :
    0 < drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity
      (DrivenCycleHistory.counterclockwiseCount ⁻¹' {count}) := by
  calc
    _ = poissonMeasure counterclockwiseIntensity {count} := by
      rw [← drivenCycleHistoryMeasure_counterclockwiseCountMarginal
        clockwiseIntensity counterclockwiseIntensity]
      rw [Measure.map_apply measurable_drivenCycleCounterclockwiseCount
        (MeasurableSet.singleton _)]
    _ = ENNReal.ofReal (poissonCountMassReal counterclockwiseIntensity count) :=
      poissonMeasure_singleton _ _
    _ > 0 := ENNReal.ofReal_pos.mpr (poissonCountMassReal_pos hCounterclockwise)

/-- Clockwise counts have positive mass above every finite cutoff. -/
theorem drivenCycleHistoryMeasure_unboundedClockwiseCount
    {clockwiseIntensity counterclockwiseIntensity : ℝ≥0}
    (hClockwise : 0 < clockwiseIntensity) (cutoff : ℕ) :
    0 < drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity
      {history | cutoff ≤ history.clockwiseCount} := by
  refine lt_of_lt_of_le
    (drivenCycleHistoryMeasure_clockwiseCountSingleton_pos
      (counterclockwiseIntensity := counterclockwiseIntensity) hClockwise cutoff) ?_
  apply measure_mono
  intro history hExact
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hExact
  simp [hExact]

/-- Counterclockwise counts have positive mass above every finite cutoff. -/
theorem drivenCycleHistoryMeasure_unboundedCounterclockwiseCount
    {clockwiseIntensity counterclockwiseIntensity : ℝ≥0}
    (hCounterclockwise : 0 < counterclockwiseIntensity) (cutoff : ℕ) :
    0 < drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity
      {history | cutoff ≤ history.counterclockwiseCount} := by
  refine lt_of_lt_of_le
    (drivenCycleHistoryMeasure_counterclockwiseCountSingleton_pos
      (clockwiseIntensity := clockwiseIntensity) hCounterclockwise cutoff) ?_
  apply measure_mono
  intro history hExact
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hExact
  simp [hExact]

/-- The complete registered law identifies both directional Poisson intensities. -/
theorem drivenCycleHistoryMeasure_injective
    {clockwiseIntensity₁ counterclockwiseIntensity₁ : ℝ≥0}
    {clockwiseIntensity₂ counterclockwiseIntensity₂ : ℝ≥0}
    (hMeasure :
      drivenCycleHistoryMeasure clockwiseIntensity₁ counterclockwiseIntensity₁ =
        drivenCycleHistoryMeasure clockwiseIntensity₂ counterclockwiseIntensity₂) :
    clockwiseIntensity₁ = clockwiseIntensity₂ ∧
      counterclockwiseIntensity₁ = counterclockwiseIntensity₂ := by
  constructor
  · apply poissonMeasure_injective
    rw [← drivenCycleHistoryMeasure_clockwiseCountMarginal
      clockwiseIntensity₁ counterclockwiseIntensity₁]
    rw [← drivenCycleHistoryMeasure_clockwiseCountMarginal
      clockwiseIntensity₂ counterclockwiseIntensity₂, hMeasure]
  · apply poissonMeasure_injective
    rw [← drivenCycleHistoryMeasure_counterclockwiseCountMarginal
      clockwiseIntensity₁ counterclockwiseIntensity₁]
    rw [← drivenCycleHistoryMeasure_counterclockwiseCountMarginal
      clockwiseIntensity₂ counterclockwiseIntensity₂, hMeasure]

/-- Mapping a finite uniform PMF through a bijection preserves it. -/
theorem map_uniformOfFintype_of_bijective
    {α : Type*} [Fintype α] [Nonempty α] (f : α → α) (hf : Bijective f) :
    PMF.map f (finiteUniformPMF α) = finiteUniformPMF α := by
  ext target
  obtain ⟨source, rfl⟩ := hf.2 target
  rw [PMF.map_apply, tsum_eq_single source]
  · simp [finiteUniformPMF_apply]
  · intro other hOther
    simp [hf.1.ne hOther.symm]

/-- Net displacement on the three-cycle for a directional count pair. -/
def drivenCycleDisplacement (counts : ℕ × ℕ) : ZMod 3 :=
  (counts.1 : ZMod 3) - (counts.2 : ZMod 3)

/-- Swapping directional counts negates the net cycle displacement. -/
@[simp]
theorem drivenCycleDisplacement_swap (counts : ℕ × ℕ) :
    drivenCycleDisplacement counts.swap = -drivenCycleDisplacement counts := by
  rcases counts with ⟨clockwiseCount, counterclockwiseCount⟩
  simp [drivenCycleDisplacement]

/-- Translate a cycle state by the realized net directional displacement. -/
def drivenCycleStateTranslation (counts : ℕ × ℕ) (state : ZMod 3) : ZMod 3 :=
  state + drivenCycleDisplacement counts

/-- Count-dependent cycle translation is bijective. -/
theorem drivenCycleStateTranslation_bijective (counts : ℕ × ℕ) :
    Bijective (drivenCycleStateTranslation counts) := by
  exact (Equiv.addRight (drivenCycleDisplacement counts)).bijective

/-- Count-dependent cycle translation preserves the uniform three-state law. -/
theorem drivenCycleStateTranslation_measurePreserving (counts : ℕ × ℕ) :
    MeasurePreserving (drivenCycleStateTranslation counts)
      uniformZModThreeMeasure uniformZModThreeMeasure := by
  refine ⟨measurable_of_countable _, ?_⟩
  rw [uniformZModThreeMeasure,
    PMF.toMeasure_map _ (finiteUniformPMF (ZMod 3)) (measurable_of_countable _)]
  rw [map_uniformOfFintype_of_bijective _
    (drivenCycleStateTranslation_bijective counts)]

/-- Reflect both tapes and exchange their directional roles. -/
def reverseSwapClockTapes
    (tapes : (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle)) :
    (ℕ → UnitAddCircle) × (ℕ → UnitAddCircle) :=
  (reverseClockTape tapes.2, reverseClockTape tapes.1)

/-- Reflecting and exchanging two tapes is an involution. -/
theorem reverseSwapClockTapes_involutive : Involutive reverseSwapClockTapes := by
  intro tapes
  apply Prod.ext
  · exact reverseClockTape_involutive tapes.1
  · exact reverseClockTape_involutive tapes.2

/-- Reflecting and exchanging the tape pair is measurable. -/
@[fun_prop]
theorem measurable_reverseSwapClockTapes : Measurable reverseSwapClockTapes := by
  unfold reverseSwapClockTapes
  fun_prop

/-- Reflecting and exchanging the tape pair preserves its Haar-product law. -/
theorem reverseSwapClockTapes_measurePreserving :
    MeasurePreserving reverseSwapClockTapes
      (unitClockTapeMeasure.prod unitClockTapeMeasure)
      (unitClockTapeMeasure.prod unitClockTapeMeasure) := by
  have hReverse := reverseClockTape_measurePreserving.prod
    reverseClockTape_measurePreserving
  have hSwap := Measure.measurePreserving_swap
    (μ := unitClockTapeMeasure) (ν := unitClockTapeMeasure)
  have hReversal : reverseSwapClockTapes =
      Prod.swap ∘ Prod.map reverseClockTape reverseClockTape := by
    funext tapes
    rfl
  rw [hReversal]
  exact hSwap.comp hReverse

/-- Count-dependent reversal of the three-cycle state and two directional tapes. -/
def drivenCycleConditionalReversal
    (counts : ℕ × ℕ)
    (data : ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))) :
    ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle)) :=
  (drivenCycleStateTranslation counts data.1, reverseSwapClockTapes data.2)

/-- Conditional reversal is undone after swapping the directional counts. -/
theorem drivenCycleConditionalReversal_swap_involutive (counts : ℕ × ℕ) (data) :
    drivenCycleConditionalReversal counts.swap
        (drivenCycleConditionalReversal counts data) = data := by
  apply Prod.ext
  · simp [drivenCycleConditionalReversal, drivenCycleStateTranslation,
      drivenCycleDisplacement_swap]
  · exact reverseSwapClockTapes_involutive data.2

/-- Joint count-dependent conditional reversal is measurable. -/
theorem measurable_uncurry_drivenCycleConditionalReversal :
    Measurable (Function.uncurry drivenCycleConditionalReversal) := by
  have hStateCore : Measurable
      (fun core : (ℕ × ℕ) × ZMod 3 ↦
        drivenCycleStateTranslation core.1 core.2) :=
    measurable_of_countable _
  have hState : Measurable
      (fun pair : (ℕ × ℕ) ×
          (ZMod 3 × ((ℕ → UnitAddCircle) × (ℕ → UnitAddCircle))) ↦
        drivenCycleStateTranslation pair.1 pair.2.1) :=
    hStateCore.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact hState.prodMk
    (measurable_reverseSwapClockTapes.comp (measurable_snd.comp measurable_snd))

/-- Conditional reversal preserves the common state/tape apparatus law at every count pair. -/
theorem drivenCycleConditionalReversal_measurePreserving (counts : ℕ × ℕ) :
    MeasurePreserving (drivenCycleConditionalReversal counts)
      drivenCycleConditionalMeasure drivenCycleConditionalMeasure := by
  have hReversal : drivenCycleConditionalReversal counts =
      Prod.map (drivenCycleStateTranslation counts) reverseSwapClockTapes := by
    funext data
    rfl
  rw [hReversal, drivenCycleConditionalMeasure]
  exact (drivenCycleStateTranslation_measurePreserving counts).prod
    reverseSwapClockTapes_measurePreserving

/-- Complete driven-cycle reversal on registered histories. -/
def drivenCycleHistoryReversal (history : DrivenCycleHistory) : DrivenCycleHistory :=
  (history.counts.swap,
    drivenCycleConditionalReversal history.counts history.conditionalRecord)

/-- Reversal exchanges the registered clockwise and counterclockwise counts. -/
@[simp]
theorem drivenCycleHistoryReversal_clockwiseCount (history : DrivenCycleHistory) :
    (drivenCycleHistoryReversal history).clockwiseCount = history.counterclockwiseCount := rfl

/-- Reversal exchanges the registered counterclockwise and clockwise counts. -/
@[simp]
theorem drivenCycleHistoryReversal_counterclockwiseCount (history : DrivenCycleHistory) :
    (drivenCycleHistoryReversal history).counterclockwiseCount = history.clockwiseCount := rfl

/-- Complete driven-cycle reversal is an involution. -/
theorem drivenCycleHistoryReversal_involutive :
    Involutive drivenCycleHistoryReversal := by
  intro history
  apply Prod.ext
  · simp [drivenCycleHistoryReversal, DrivenCycleHistory.counts]
  · exact drivenCycleConditionalReversal_swap_involutive history.counts
      history.conditionalRecord

/-- Complete driven-cycle reversal is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleHistoryReversal :
    Measurable drivenCycleHistoryReversal := by
  have hCounts : Measurable fun history : DrivenCycleHistory ↦ history.counts.swap :=
    (measurable_of_countable (fun counts : ℕ × ℕ ↦ counts.swap)).comp
      measurable_drivenCycleCounts
  exact hCounts.prodMk measurable_uncurry_drivenCycleConditionalReversal

/-- Complete reversal maps a directional law to the law with exchanged intensities. -/
theorem drivenCycleHistoryReversal_measurePreserving
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    MeasurePreserving drivenCycleHistoryReversal
      (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity)
      (drivenCycleHistoryMeasure counterclockwiseIntensity clockwiseIntensity) := by
  have hCounts := Measure.measurePreserving_swap
    (μ := poissonMeasure clockwiseIntensity)
    (ν := poissonMeasure counterclockwiseIntensity)
  have hSkew := hCounts.skew_product
    measurable_uncurry_drivenCycleConditionalReversal
    (ae_of_all _ fun counts ↦
      (drivenCycleConditionalReversal_measurePreserving counts).map_eq)
  have hReversal : drivenCycleHistoryReversal =
      fun history : DrivenCycleHistory ↦
        (history.1.swap, drivenCycleConditionalReversal history.1 history.2) := by
    funext history
    rfl
  rw [hReversal]
  simpa only [drivenCycleHistoryMeasure, drivenCycleCountMeasure] using hSkew

/-- Pushing a complete driven law through reversal exchanges its directional intensities. -/
theorem map_drivenCycleHistoryReversal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map drivenCycleHistoryReversal
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      drivenCycleHistoryMeasure counterclockwiseIntensity clockwiseIntensity :=
  (drivenCycleHistoryReversal_measurePreserving
    clockwiseIntensity counterclockwiseIntensity).map_eq

/-- Terminal substrate state after the registered directional contacts. -/
def DrivenCycleHistory.terminalState (history : DrivenCycleHistory) : ZMod 3 :=
  drivenCycleStateTranslation history.counts history.initialState

/-- Reversal starts at the original terminal cycle state. -/
@[simp]
theorem drivenCycleHistoryReversal_initialState (history : DrivenCycleHistory) :
    (drivenCycleHistoryReversal history).initialState = history.terminalState := rfl

/-- The terminal cycle-state observable is measurable. -/
@[fun_prop]
theorem measurable_drivenCycleTerminalState :
    Measurable DrivenCycleHistory.terminalState := by
  have hCore : Measurable
      (fun core : (ℕ × ℕ) × ZMod 3 ↦
        drivenCycleStateTranslation core.1 core.2) :=
    measurable_of_countable _
  exact hCore.comp
    (measurable_drivenCycleCounts.prodMk measurable_drivenCycleInitialState)

/-- The terminal ensemble remains uniform for every positive or zero directional pair. -/
theorem drivenCycleHistoryMeasure_terminalStateMarginal
    (clockwiseIntensity counterclockwiseIntensity : ℝ≥0) :
    Measure.map DrivenCycleHistory.terminalState
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) =
      uniformZModThreeMeasure := by
  calc
    _ = Measure.map
        (DrivenCycleHistory.initialState ∘ drivenCycleHistoryReversal)
        (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity) := by
      rfl
    _ = Measure.map DrivenCycleHistory.initialState
        (Measure.map drivenCycleHistoryReversal
          (drivenCycleHistoryMeasure clockwiseIntensity counterclockwiseIntensity)) := by
      exact (Measure.map_map measurable_drivenCycleInitialState
        measurable_drivenCycleHistoryReversal).symm
    _ = Measure.map DrivenCycleHistory.initialState
        (drivenCycleHistoryMeasure counterclockwiseIntensity clockwiseIntensity) := by
      rw [map_drivenCycleHistoryReversal]
    _ = uniformZModThreeMeasure :=
      drivenCycleHistoryMeasure_initialStateMarginal _ _

end FiniteMarkovProcesses.Probability
