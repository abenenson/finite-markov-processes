/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.PoissonCountExpectation
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Fin.Rev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Probability.Distributions.Poisson.Basic
public import FiniteMarkovProcesses.Probability.FiniteUniformPMF
public import Mathlib.Probability.ProductMeasure

/-!
# Complete fixed-horizon Poisson contact histories

This file constructs a registered fixed-horizon contact history from a Poisson count, a uniform
binary initial state, and an infinite independent Haar tape on the unit additive circle. The first
`n` tape entries are active when the count is `n`; the suffix remains an explicitly registered
randomizer reserve common to every intensity.

Time reversal keeps the count, transports the initial state to the parity-determined terminal
state, and negates every clock label. The resulting map is a measurable involution preserving the
complete history law. This carrier is a generative point history, not a càdlàg path-space model.

## Main results

- `poissonContactHistoryMeasure_countMarginal`: exact Poisson count marginal.
- `poissonContactHistoryMeasure_clockTapeMarginal`: common infinite Haar tape marginal.
- `poissonContactHistoryMeasure_countSingleton`: exact mass of every count fibre.
- `poissonContactHistoryMeasure_unboundedCount`: positive mass above every count cutoff.
- `poissonContactHistoryMeasure_injective`: identifiability of the intensity.
- `poissonContactHistoryReversal_involutive`: exact history-level involution.
- `poissonContactHistoryReversal_measurePreserving`: complete-law reversal invariance.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

attribute [local instance] ZeroLEOneClass.factZeroLtOne

/-- Complete registered history: count, binary initial state, and infinite unit-clock tape. -/
abbrev PoissonContactHistory := ℕ × Fin 2 × (ℕ → UnitAddCircle)

/-- Uniform law on the two possible initial substrate states. -/
noncomputable def uniformFinTwoMeasure : Measure (Fin 2) :=
  (finiteUniformPMF (Fin 2)).toMeasure

/-- The original uniform law on the two initial substrate states has total mass one. -/
noncomputable instance instIsProbabilityMeasureUniformFinTwoMeasure :
    IsProbabilityMeasure uniformFinTwoMeasure := by
  unfold uniformFinTwoMeasure
  infer_instance

/-- Independent Haar clock labels indexed by all natural registration slots. -/
noncomputable def unitClockTapeMeasure : Measure (ℕ → UnitAddCircle) :=
  Measure.infinitePi fun _ : ℕ ↦
    (AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- The original infinite product of Haar clock-label laws has total mass one. -/
noncomputable instance instIsProbabilityMeasureUnitClockTapeMeasure :
    IsProbabilityMeasure unitClockTapeMeasure := by
  unfold unitClockTapeMeasure
  infer_instance

/-- Intensity-independent state and clock-tape law. -/
noncomputable def poissonContactConditionalMeasure :
    Measure (Fin 2 × (ℕ → UnitAddCircle)) :=
  uniformFinTwoMeasure.prod unitClockTapeMeasure

/-- The original intensity-independent substrate-state and clock-tape law has total mass one. -/
noncomputable instance instIsProbabilityMeasurePoissonContactConditionalMeasure :
    IsProbabilityMeasure poissonContactConditionalMeasure := by
  unfold poissonContactConditionalMeasure
  infer_instance

/-- Complete registered history law at an integrated Poisson contact intensity. -/
noncomputable def poissonContactHistoryMeasure
    (intensity : ℝ≥0) : Measure PoissonContactHistory :=
  (poissonMeasure intensity).prod poissonContactConditionalMeasure

/-- The original complete registered Poisson contact-history law has total mass one. -/
noncomputable instance instIsProbabilityMeasurePoissonContactHistoryMeasure
    (intensity : ℝ≥0) : IsProbabilityMeasure (poissonContactHistoryMeasure intensity) := by
  unfold poissonContactHistoryMeasure
  infer_instance

/-- Registered contact count. -/
def PoissonContactHistory.contactCount (history : PoissonContactHistory) : ℕ := history.1

/-- Initial binary substrate state. -/
def PoissonContactHistory.initialState (history : PoissonContactHistory) : Fin 2 := history.2.1

/-- Entire registered clock tape, including its inactive suffix. -/
def PoissonContactHistory.clockTape
    (history : PoissonContactHistory) : ℕ → UnitAddCircle :=
  history.2.2

/-- Count and initial state, explicitly excluding the clock randomizer reserve. -/
def PoissonContactHistory.contactSkeleton
    (history : PoissonContactHistory) : ℕ × Fin 2 :=
  (history.contactCount, history.initialState)

/-- Contact count paired with the entire registered randomizer tape. -/
def PoissonContactHistory.countClockTape
    (history : PoissonContactHistory) : ℕ × (ℕ → UnitAddCircle) :=
  (history.contactCount, history.clockTape)

/-- The registered label at a fixed clock-tape index. -/
def PoissonContactHistory.registeredContactLabel
    (history : PoissonContactHistory) (index : ℕ) : UnitAddCircle :=
  history.clockTape index

/-- An active label, whose index is statically bounded by the realized contact count. -/
def PoissonContactHistory.activeContactLabel
    (history : PoissonContactHistory) (index : Fin history.contactCount) : UnitAddCircle :=
  history.clockTape index

/-- An explicitly inactive clock label beyond the active prefix. -/
def PoissonContactHistory.inactiveRandomizerLabel
    (history : PoissonContactHistory) (offset : ℕ) : UnitAddCircle :=
  history.clockTape (history.contactCount + offset)

/-- The contact-count observable is measurable. -/
@[fun_prop]
theorem measurable_contactCount : Measurable PoissonContactHistory.contactCount := by
  unfold PoissonContactHistory.contactCount
  fun_prop

/-- The initial-state observable is measurable. -/
@[fun_prop]
theorem measurable_initialState : Measurable PoissonContactHistory.initialState := by
  unfold PoissonContactHistory.initialState
  fun_prop

/-- The complete clock-tape observable is measurable. -/
@[fun_prop]
theorem measurable_clockTape : Measurable PoissonContactHistory.clockTape := by
  unfold PoissonContactHistory.clockTape
  fun_prop

/-- The count/tape observable is measurable. -/
@[fun_prop]
theorem measurable_countClockTape :
    Measurable PoissonContactHistory.countClockTape := by
  unfold PoissonContactHistory.countClockTape
  exact measurable_contactCount.prodMk measurable_clockTape

/-- The tape label at each fixed registration index is measurable. -/
@[fun_prop]
theorem measurable_registeredContactLabel (index : ℕ) :
    Measurable fun history : PoissonContactHistory ↦
      history.registeredContactLabel index := by
  unfold PoissonContactHistory.registeredContactLabel
  exact (measurable_pi_apply index).comp measurable_clockTape

/-- Haar measure on the unit additive circle has no point masses. -/
noncomputable instance instNoAtomsUnitAddCircleVolume :
    NullSingletonClass (volume : Measure UnitAddCircle) := by
  refine ⟨fun point ↦ ?_⟩
  let intervalEquiv : UnitAddCircle → Set.Ioc (0 : ℝ) (0 + 1) :=
    AddCircle.equivIoc 1 0
  have hPreserving :
      MeasurePreserving intervalEquiv (volume : Measure UnitAddCircle)
        (Measure.comap Subtype.val (volume : Measure ℝ)) :=
    AddCircle.measurePreserving_equivIoc (T := 1) (a := 0)
  have hPreimage : intervalEquiv ⁻¹' {intervalEquiv point} = {point} := by
    ext other
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (AddCircle.equivIoc 1 0).injective.eq_iff
  calc
    (volume : Measure UnitAddCircle) {point} =
        Measure.map intervalEquiv (volume : Measure UnitAddCircle)
          {intervalEquiv point} := by
      rw [Measure.map_apply hPreserving.measurable (MeasurableSet.singleton _), hPreimage]
    _ = Measure.comap Subtype.val volume {intervalEquiv point} := by
      rw [hPreserving.map_eq]
    _ = 0 := by
      rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
      simp

/-- The normalized Haar probability measure on the unit circle is atomless. -/
noncomputable instance instNoAtomsUnitAddCircleHaar :
    NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hVolume :
      (volume : Measure UnitAddCircle) =
        (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
  rw [← hVolume]
  infer_instance

/-- The infinite registered clock tape is atomless. -/
noncomputable instance instNoAtomsUnitClockTapeMeasure :
    NullSingletonClass unitClockTapeMeasure where
  measure_singleton tape := by
    rw [unitClockTapeMeasure, Measure.infinitePi_singleton]
    exact tprod_of_exists_eq_zero ⟨0, measure_singleton _⟩

/-- Every singleton of the original substrate-state and clock-tape law has zero mass. -/
noncomputable instance instNoAtomsPoissonContactConditionalMeasure :
    NullSingletonClass poissonContactConditionalMeasure := by
  unfold poissonContactConditionalMeasure
  infer_instance

/-- Every singleton of the original complete Poisson contact-history law has zero mass. -/
noncomputable instance instNoAtomsPoissonContactHistoryMeasure (intensity : ℝ≥0) :
    NullSingletonClass (poissonContactHistoryMeasure intensity) := by
  unfold poissonContactHistoryMeasure
  infer_instance

/-- The complete history law has total mass one. -/
theorem poissonContactHistoryMeasure_univ (intensity : ℝ≥0) :
    poissonContactHistoryMeasure intensity Set.univ = 1 := by
  exact measure_univ

/-- Every complete registered history singleton has zero mass. -/
theorem poissonContactHistoryMeasure_singleton
    (intensity : ℝ≥0) (history : PoissonContactHistory) :
    poissonContactHistoryMeasure intensity {history} = 0 := by
  exact measure_singleton _

/-- The count marginal is exactly Mathlib's Poisson measure. -/
theorem poissonContactHistoryMeasure_countMarginal (intensity : ℝ≥0) :
    Measure.map PoissonContactHistory.contactCount
        (poissonContactHistoryMeasure intensity) =
      poissonMeasure intensity := by
  have hProjection : PoissonContactHistory.contactCount =
      (Prod.fst : PoissonContactHistory → ℕ) := rfl
  rw [hProjection, poissonContactHistoryMeasure]
  exact (measurePreserving_fst
      (μ := poissonMeasure intensity)
      (ν := poissonContactConditionalMeasure)).map_eq

/-- The initial-state marginal is the same uniform binary law at every intensity. -/
theorem poissonContactHistoryMeasure_initialStateMarginal (intensity : ℝ≥0) :
    Measure.map PoissonContactHistory.initialState
        (poissonContactHistoryMeasure intensity) =
      uniformFinTwoMeasure := by
  have hConditional := measurePreserving_snd
    (μ := poissonMeasure intensity) (ν := poissonContactConditionalMeasure)
  have hState := measurePreserving_fst
    (μ := uniformFinTwoMeasure) (ν := unitClockTapeMeasure)
  have hProjection : PoissonContactHistory.initialState =
      (Prod.fst : Fin 2 × (ℕ → UnitAddCircle) → Fin 2) ∘
        (Prod.snd : PoissonContactHistory → Fin 2 × (ℕ → UnitAddCircle)) := rfl
  rw [hProjection, poissonContactHistoryMeasure]
  exact (hState.comp hConditional).map_eq

/-- The entire registered clock tape has the same Haar-product law at every intensity. -/
theorem poissonContactHistoryMeasure_clockTapeMarginal (intensity : ℝ≥0) :
    Measure.map PoissonContactHistory.clockTape
        (poissonContactHistoryMeasure intensity) =
      unitClockTapeMeasure := by
  have hConditional := measurePreserving_snd
    (μ := poissonMeasure intensity) (ν := poissonContactConditionalMeasure)
  have hTape := measurePreserving_snd
    (μ := uniformFinTwoMeasure) (ν := unitClockTapeMeasure)
  have hProjection : PoissonContactHistory.clockTape =
      (Prod.snd : Fin 2 × (ℕ → UnitAddCircle) → (ℕ → UnitAddCircle)) ∘
        (Prod.snd : PoissonContactHistory → Fin 2 × (ℕ → UnitAddCircle)) := rfl
  rw [hProjection, poissonContactHistoryMeasure]
  exact (hTape.comp hConditional).map_eq

/-- Each registered tape coordinate has the normalized Haar clock law. -/
theorem unitClockTapeMeasure_coordinateMarginal (index : ℕ) :
    Measure.map (fun tape : ℕ → UnitAddCircle ↦ tape index)
        unitClockTapeMeasure =
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  unfold unitClockTapeMeasure
  exact Measure.infinitePi_map_eval
    (fun _ : ℕ ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle)) index

/-- Every fixed registered history label has the same Haar law at every intensity. -/
theorem poissonContactHistoryMeasure_registeredContactLabelMarginal
    (intensity : ℝ≥0) (index : ℕ) :
    Measure.map (fun history : PoissonContactHistory ↦
        history.registeredContactLabel index)
        (poissonContactHistoryMeasure intensity) =
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hHistoryTape : MeasurePreserving PoissonContactHistory.clockTape
      (poissonContactHistoryMeasure intensity) unitClockTapeMeasure :=
    ⟨measurable_clockTape,
      poissonContactHistoryMeasure_clockTapeMarginal intensity⟩
  have hCoordinate :
      MeasurePreserving (fun tape : ℕ → UnitAddCircle ↦ tape index)
        unitClockTapeMeasure
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    ⟨measurable_pi_apply index, unitClockTapeMeasure_coordinateMarginal index⟩
  have hLabel : (fun history : PoissonContactHistory ↦ history.registeredContactLabel index) =
      (fun tape : ℕ → UnitAddCircle ↦ tape index) ∘ PoissonContactHistory.clockTape := rfl
  rw [hLabel]
  exact (hCoordinate.comp hHistoryTape).map_eq

/-- Removing the clock reserve leaves the independent Poisson-count/uniform-state skeleton. -/
theorem poissonContactHistoryMeasure_contactSkeletonMarginal (intensity : ℝ≥0) :
    Measure.map PoissonContactHistory.contactSkeleton
        (poissonContactHistoryMeasure intensity) =
      (poissonMeasure intensity).prod uniformFinTwoMeasure := by
  have hIdentity :
      MeasurePreserving id (poissonMeasure intensity) (poissonMeasure intensity) :=
    MeasurePreserving.id _
  have hState := measurePreserving_fst
    (μ := uniformFinTwoMeasure) (ν := unitClockTapeMeasure)
  have hProjection : PoissonContactHistory.contactSkeleton =
      Prod.map (id : ℕ → ℕ) (Prod.fst : Fin 2 × (ℕ → UnitAddCircle) → Fin 2) := rfl
  rw [hProjection, poissonContactHistoryMeasure, poissonContactConditionalMeasure]
  exact (hIdentity.prod hState).map_eq

/-- Count and complete clock tape retain their defining independent product law. -/
theorem poissonContactHistoryMeasure_countClockTapeMarginal (intensity : ℝ≥0) :
    Measure.map PoissonContactHistory.countClockTape
        (poissonContactHistoryMeasure intensity) =
      (poissonMeasure intensity).prod unitClockTapeMeasure := by
  have hIdentity :
      MeasurePreserving id (poissonMeasure intensity) (poissonMeasure intensity) :=
    MeasurePreserving.id _
  have hTape := measurePreserving_snd
    (μ := uniformFinTwoMeasure) (ν := unitClockTapeMeasure)
  have hProjection : PoissonContactHistory.countClockTape =
      Prod.map (id : ℕ → ℕ)
        (Prod.snd : Fin 2 × (ℕ → UnitAddCircle) → (ℕ → UnitAddCircle)) := rfl
  rw [hProjection, poissonContactHistoryMeasure, poissonContactConditionalMeasure]
  exact (hIdentity.prod hTape).map_eq

/-- The conditional state/tape law is literally common to the entire intensity family. -/
theorem poissonContactHistoryMeasure_commonConditionalFactorization (intensity : ℝ≥0) :
    poissonContactHistoryMeasure intensity =
      (poissonMeasure intensity).prod poissonContactConditionalMeasure := rfl

/-- Mathlib's Poisson measure assigns its defining probability mass to each singleton. -/
theorem poissonMeasure_singleton (intensity : ℝ≥0) (count : ℕ) :
    poissonMeasure intensity {count} =
      ENNReal.ofReal (poissonCountMassReal intensity count) := by
  simpa only [poissonCountMassReal] using
    ProbabilityTheory.poissonMeasure_singleton intensity count

/-- A Poisson intensity is identifiable from its entire count law. -/
theorem poissonMeasure_injective {firstIntensity secondIntensity : ℝ≥0}
    (hMeasure : poissonMeasure firstIntensity = poissonMeasure secondIntensity) :
    firstIntensity = secondIntensity := by
  have hMass := congrArg (fun measure : Measure ℕ ↦ measure {0}) hMeasure
  change poissonMeasure firstIntensity {0} = poissonMeasure secondIntensity {0} at hMass
  rw [poissonMeasure_singleton, poissonMeasure_singleton] at hMass
  have hReal :
      poissonCountMassReal firstIntensity 0 = poissonCountMassReal secondIntensity 0 :=
    (ENNReal.ofReal_eq_ofReal_iff
      poissonCountMassReal_nonneg poissonCountMassReal_nonneg).mp hMass
  simp only [poissonCountMassReal, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    mul_one] at hReal
  have hNeg : -(firstIntensity : ℝ) = -(secondIntensity : ℝ) :=
    Real.exp_injective hReal
  exact NNReal.eq (neg_injective hNeg)

/-- The complete registered history law identifies its Poisson intensity. -/
theorem poissonContactHistoryMeasure_injective
    {firstIntensity secondIntensity : ℝ≥0}
    (hMeasure : poissonContactHistoryMeasure firstIntensity =
      poissonContactHistoryMeasure secondIntensity) :
    firstIntensity = secondIntensity := by
  apply poissonMeasure_injective
  rw [← poissonContactHistoryMeasure_countMarginal firstIntensity,
    ← poissonContactHistoryMeasure_countMarginal secondIntensity, hMeasure]

/-- The mass of a fixed count fibre is exactly its Poisson probability. -/
theorem poissonContactHistoryMeasure_countSingleton
    (intensity : ℝ≥0) (count : ℕ) :
    poissonContactHistoryMeasure intensity
        (PoissonContactHistory.contactCount ⁻¹' {count}) =
      poissonMeasure intensity {count} := by
  rw [← poissonContactHistoryMeasure_countMarginal intensity,
    Measure.map_apply measurable_contactCount (MeasurableSet.singleton _)]

/-- Every exact count has positive mass at a positive intensity. -/
theorem poissonContactHistoryMeasure_countSingleton_pos
    {intensity : ℝ≥0} (hIntensity : 0 < intensity) (count : ℕ) :
    0 < poissonContactHistoryMeasure intensity
      (PoissonContactHistory.contactCount ⁻¹' {count}) := by
  rw [poissonContactHistoryMeasure_countSingleton, poissonMeasure_singleton]
  exact ENNReal.ofReal_pos.mpr (poissonCountMassReal_pos hIntensity)

/-- The complete history law has positive mass above every finite count cutoff. -/
theorem poissonContactHistoryMeasure_unboundedCount
    {intensity : ℝ≥0} (hIntensity : 0 < intensity) (cutoff : ℕ) :
    0 < poissonContactHistoryMeasure intensity
      {history | cutoff ≤ history.contactCount} := by
  refine lt_of_lt_of_le
    (poissonContactHistoryMeasure_countSingleton_pos hIntensity cutoff) ?_
  apply measure_mono
  intro history hExact
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hExact
  simp [hExact]

/-- The terminal substrate state after toggling once for every active contact. -/
def terminalContactState (contactCount : ℕ) (initialState : Fin 2) : Fin 2 :=
  if Even contactCount then initialState else Fin.rev initialState

/-- Applying the parity transport twice returns the initial state. -/
theorem terminalContactState_involutive (contactCount : ℕ) :
    Function.Involutive (terminalContactState contactCount) := by
  intro initialState
  by_cases hEven : Even contactCount
  · simp [terminalContactState, hEven]
  · simp [terminalContactState, hEven]

/-- Reflect every registered clock label about the chosen clock cut. -/
def reverseClockTape (tape : ℕ → UnitAddCircle) : ℕ → UnitAddCircle :=
  fun index ↦ -tape index

/-- Clock-tape reflection is involutive. -/
theorem reverseClockTape_involutive : Function.Involutive reverseClockTape := by
  intro tape
  funext index
  simp [reverseClockTape]

/-- Conditional reversal at a fixed contact count. -/
def poissonContactConditionalReversal
    (contactCount : ℕ) (data : Fin 2 × (ℕ → UnitAddCircle)) :
    Fin 2 × (ℕ → UnitAddCircle) :=
  (terminalContactState contactCount data.1, reverseClockTape data.2)

/-- Complete physical time reversal on registered histories. -/
def poissonContactHistoryReversal
    (history : PoissonContactHistory) : PoissonContactHistory :=
  (history.contactCount,
    poissonContactConditionalReversal history.contactCount history.2)

/-- Conditional reversal is an involution for each realized contact count. -/
theorem poissonContactConditionalReversal_involutive (contactCount : ℕ) :
    Function.Involutive (poissonContactConditionalReversal contactCount) := by
  intro data
  apply Prod.ext
  · exact terminalContactState_involutive contactCount data.1
  · exact reverseClockTape_involutive data.2

/-- Complete registered-history reversal is an involution. -/
theorem poissonContactHistoryReversal_involutive :
    Function.Involutive poissonContactHistoryReversal := by
  intro history
  apply Prod.ext
  · rfl
  · exact poissonContactConditionalReversal_involutive history.contactCount history.2

/-- The uniform binary state law is invariant under `Fin.rev`. -/
theorem map_finRev_uniformFinTwoMeasure :
    Measure.map Fin.rev uniformFinTwoMeasure = uniformFinTwoMeasure := by
  rw [uniformFinTwoMeasure,
    PMF.toMeasure_map Fin.rev (finiteUniformPMF (Fin 2)) (by fun_prop)]
  congr 1
  ext state
  fin_cases state <;>
    simp [PMF.map_apply, finiteUniformPMF_apply, tsum_fintype]

/-- Parity transport preserves the uniform initial-state law at every count. -/
theorem terminalContactState_measurePreserving (contactCount : ℕ) :
    MeasurePreserving (terminalContactState contactCount)
      uniformFinTwoMeasure uniformFinTwoMeasure := by
  refine ⟨?_, ?_⟩
  · unfold terminalContactState
    fun_prop
  · by_cases hEven : Even contactCount
    · have hTerminal : terminalContactState contactCount = id := by
        funext state
        simp [terminalContactState, hEven]
      rw [hTerminal, Measure.map_id]
    · have hTerminal : terminalContactState contactCount = Fin.rev := by
        funext state
        simp [terminalContactState, hEven]
      rw [hTerminal, map_finRev_uniformFinTwoMeasure]

/-- Clock-tape reflection is measurable. -/
@[fun_prop]
theorem measurable_reverseClockTape : Measurable reverseClockTape := by
  unfold reverseClockTape
  fun_prop

/-- The infinite Haar clock-tape law is invariant under coordinatewise reflection. -/
theorem map_reverseClockTape_unitClockTapeMeasure :
    Measure.map reverseClockTape unitClockTapeMeasure = unitClockTapeMeasure := by
  unfold reverseClockTape unitClockTapeMeasure
  rw [Measure.infinitePi_map_pi
    (fun _ : ℕ ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (fun _ ↦ measurable_neg)]
  simp only [Measure.map_neg_eq_self]

/-- Clock-tape reflection preserves the infinite Haar product law. -/
theorem reverseClockTape_measurePreserving :
    MeasurePreserving reverseClockTape unitClockTapeMeasure unitClockTapeMeasure :=
  ⟨measurable_reverseClockTape, map_reverseClockTape_unitClockTapeMeasure⟩

/-- The joint count-dependent conditional reversal is measurable. -/
theorem measurable_uncurry_poissonContactConditionalReversal :
    Measurable (Function.uncurry poissonContactConditionalReversal) := by
  have hStatePair :
      Measurable fun pair : ℕ × Fin 2 ↦ terminalContactState pair.1 pair.2 :=
    measurable_of_countable _
  have hState : Measurable
      (fun pair : ℕ × (Fin 2 × (ℕ → UnitAddCircle)) ↦
        terminalContactState pair.1 pair.2.1) :=
    hStatePair.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact hState.prodMk
    (measurable_reverseClockTape.comp (measurable_snd.comp measurable_snd))

/-- Conditional reversal preserves the common state/tape law at every count. -/
theorem poissonContactConditionalReversal_measurePreserving (contactCount : ℕ) :
    MeasurePreserving (poissonContactConditionalReversal contactCount)
      poissonContactConditionalMeasure poissonContactConditionalMeasure := by
  have hReversal : poissonContactConditionalReversal contactCount =
      Prod.map (terminalContactState contactCount) reverseClockTape := rfl
  rw [hReversal, poissonContactConditionalMeasure]
  exact (terminalContactState_measurePreserving contactCount).prod
    reverseClockTape_measurePreserving

/-- Complete history reversal is measurable. -/
@[fun_prop]
theorem measurable_poissonContactHistoryReversal :
    Measurable poissonContactHistoryReversal := by
  exact measurable_contactCount.prodMk measurable_uncurry_poissonContactConditionalReversal

/-- Complete physical reversal preserves the registered Poisson-contact history law. -/
theorem poissonContactHistoryReversal_measurePreserving (intensity : ℝ≥0) :
    MeasurePreserving poissonContactHistoryReversal
      (poissonContactHistoryMeasure intensity)
      (poissonContactHistoryMeasure intensity) := by
  have hIdentity :
      MeasurePreserving id (poissonMeasure intensity) (poissonMeasure intensity) :=
    MeasurePreserving.id _
  have hSkew := hIdentity.skew_product
    measurable_uncurry_poissonContactConditionalReversal
    (ae_of_all _ fun contactCount ↦
      (poissonContactConditionalReversal_measurePreserving contactCount).map_eq)
  have hReversal : poissonContactHistoryReversal =
      (fun history : PoissonContactHistory ↦
        ((id : ℕ → ℕ) history.1,
          poissonContactConditionalReversal history.1 history.2)) := rfl
  rw [hReversal, poissonContactHistoryMeasure]
  exact hSkew

/-- Pushing the complete history law through physical reversal leaves it unchanged. -/
theorem map_poissonContactHistoryReversal (intensity : ℝ≥0) :
    Measure.map poissonContactHistoryReversal
        (poissonContactHistoryMeasure intensity) =
      poissonContactHistoryMeasure intensity :=
  (poissonContactHistoryReversal_measurePreserving intensity).map_eq

end FiniteMarkovProcesses.Probability
