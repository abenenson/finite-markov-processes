/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.MeasureTheory.Measure.PiWithDensity
public import FiniteMarkovProcesses.Probability.CumulativeWaitTimes
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpStoppedLaw
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpTapeMarginal

/-!
# Identifying generative and density laws for finite-state jump processes

This module identifies the stopped normalized Gillespie construction with the canonical physical
jump-history density. It first expresses exact horizon crossing in waiting-time coordinates,
factors all positive-rate preterminal holding laws over Lebesgue measure, and integrates the final
dwell through its survival function. Cumulative waiting times then transport the result to the
ordered jump-time simplex.

Absorbing preterminal rows are handled separately: their deterministic fallback wait forces an
earlier crossing, while the corresponding physical jump-rate factor vanishes. Thus the proof does
not assign a fictitious Lebesgue density to an absorbing holding law.

## Main Results

- `finiteStateWaitingFirstCrosses`: the exact first-crossing event in waiting coordinates.
- `firstCrossesJumpHorizonAt_iff_waitingFirstCrosses`: samplewise crossing equivalence under
  positive waits.
- `finiteStateMarkovCumulativeJumpTimesAt_eq_cumulativeWaitTimes`: equality of tape and linear
  cumulative-time readouts.
- `finiteStateMarkovPreterminalHoldingMeasure_eq_withDensity`: the positive-rate preterminal
  product law as an explicit Lebesgue density.
- `finiteStateMarkovPreterminalWaitingMeasure_firstCrossing`: exact integration of the terminal
  crossing dwell into its physical survival density.
- `finiteStateMarkovPositiveStateWordCumulativeMeasure_eq_densitySlice`: equality of the
  normalized generative and physical density measures on every positive-rate fixed state word.
- `finiteStateMarkovStateWordCumulativeMeasure_eq_densitySlice`: the same equality for every
  fixed state word, including words blocked by an absorbing preterminal row.
- `finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure`: global equality of the
  normalized stopped Gillespie construction and the canonical physical density measure.
- `ae_physicalAt_finiteStateMarkovStoppedHistoryMeasure`: the stopped law is concentrated on the
  exact ordered reduced history carrier.
- `finiteStateMarkovJumpDensityIsNormalized_of_nonnegative`: constructive normalization of the
  physical density at every nonnegative finite horizon.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Waiting vectors whose preterminal cumulative sums lie in the ordered jump-time simplex and
whose terminal dwell reaches the remaining horizon. -/
def finiteStateWaitingFirstCrosses (n : ℕ) (T : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {waits |
    cumulativeWaitTimes n (fun i => waits i.castSucc) ∈ orderedJumpTimes n T ∧
      T - ∑ i : Fin n, waits i.castSucc ≤ waits (Fin.last n)}

/-- The first-crossing event in finite waiting-time coordinates is measurable. -/
theorem measurableSet_finiteStateWaitingFirstCrosses (n : ℕ) (T : ℝ) :
    MeasurableSet (finiteStateWaitingFirstCrosses n T) := by
  unfold finiteStateWaitingFirstCrosses
  apply MeasurableSet.inter
  · exact (measurableSet_orderedJumpTimes n T).preimage <| by fun_prop
  · exact measurableSet_le
      (show Measurable (fun waits : Fin (n + 1) → ℝ =>
        T - ∑ i : Fin n, waits i.castSucc) by fun_prop)
      (show Measurable (fun waits : Fin (n + 1) → ℝ => waits (Fin.last n)) by
        fun_prop)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- For positive tape waits, first crossing at one jump count is equivalent to the canonical
waiting-time event. -/
theorem firstCrossesJumpHorizonAt_iff_waitingFirstCrosses
    (tape : ℕ → State × ℝ) (T : ℝ) (n : ℕ)
    (hPositive : HasPositiveWaitingTimes tape) :
    FirstCrossesJumpHorizonAt tape T n ↔
      (fun i : Fin (n + 1) => (tape i.1).2) ∈ finiteStateWaitingFirstCrosses n T := by
  cases n with
  | zero =>
      simp [FirstCrossesJumpHorizonAt, finiteStateWaitingFirstCrosses,
        timedStateCumulativeTime]
      intro h
      constructor
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n =>
      simp only [finiteStateWaitingFirstCrosses, Set.mem_ofPred_eq]
      rw [cumulativeWaitTimes_mem_orderedJumpTimes_iff]
      simp only [Fin.val_castSucc]
      rw [Fin.sum_univ_eq_sum_range (fun k => (tape k).2) (n + 1)]
      constructor
      · intro hCrossing
        constructor
        · constructor
          · intro i
            exact hPositive i.1
          · exact hCrossing.2 n (Nat.lt_succ_self n)
        · have hTerminalCrossing := hCrossing.1
          change T ≤ timedStateCumulativeTime tape (n + 2) at hTerminalCrossing
          rw [timedStateCumulativeTime, Finset.sum_range_succ] at hTerminalCrossing
          change T - (∑ i ∈ Finset.range (n + 1), (tape i).2) ≤
            (tape (n + 1)).2
          linarith
      · rintro ⟨⟨hPrePositive, hPreHorizon⟩, hTerminal⟩
        constructor
        · rw [timedStateCumulativeTime, Finset.sum_range_succ]
          change T - (∑ i ∈ Finset.range (n + 1), (tape i).2) ≤
            (tape (n + 1)).2 at hTerminal
          linarith
        · intro earlier hEarlier
          have hMono :=
            (TimedStateTrajectory.cumulativeTime_strictMono hPositive).monotone hEarlier
          change timedStateCumulativeTime tape (earlier + 1) < T
          calc
            timedStateCumulativeTime tape (earlier + 1) ≤
                timedStateCumulativeTime tape (n + 1) := hMono
            _ < T := by
              simpa [timedStateCumulativeTime] using hPreHorizon

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The tape's cumulative jump-time readout is exactly the determinant-one cumulative-wait map. -/
theorem finiteStateMarkovCumulativeJumpTimesAt_eq_cumulativeWaitTimes
    (n : ℕ) (tape : ℕ → State × ℝ) :
    FiniteStateMarkovStoppedLaw.finiteStateMarkovCumulativeJumpTimesAt n tape =
      cumulativeWaitTimes n (fun i => (tape i.1).2) := by
  funext i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      induction i using Fin.induction with
      | zero =>
          rw [cumulativeWaitTimes_zero]
          simp [FiniteStateMarkovStoppedLaw.finiteStateMarkovCumulativeJumpTimesAt,
            timedStateCumulativeTime]
      | succ i inductionHypothesis =>
          rw [cumulativeWaitTimes_eq_previous_add _ i.succ (Fin.succ_ne_zero i)]
          have hPred : (i.succ.pred (Fin.succ_ne_zero i)).castSucc = i.castSucc := by
            ext
            simp
          rw [hPred]
          change (∑ index ∈ Finset.range (i.1 + 2), (tape index).2) = _
          rw [Finset.sum_range_succ]
          change (∑ index ∈ Finset.range (i.1 + 1), (tape index).2) +
            (tape (i.1 + 1)).2 = _
          change (∑ index ∈ Finset.range (i.1 + 1), (tape index).2) =
            cumulativeWaitTimes (n + 1) (fun j => (tape j.1).2) i.castSucc
            at inductionHypothesis
          rw [inductionHypothesis]
          rfl

/-- Product density of all preterminal positive-rate holding times. -/
noncomputable def finiteStateMarkovPreterminalHoldingDensity
    (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) (waits : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal
    ((generator.escapeRate (states i.castSucc) : ℝ) *
      Real.exp (-((generator.escapeRate (states i.castSucc) : ℝ) * waits i)))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The preterminal holding-time product density is measurable. -/
theorem measurable_finiteStateMarkovPreterminalHoldingDensity
    (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) :
    Measurable (finiteStateMarkovPreterminalHoldingDensity generator states) := by
  unfold finiteStateMarkovPreterminalHoldingDensity
  fun_prop

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- When every preterminal escape rate is nonzero, the product holding-time law has its exact
coordinatewise exponential density over the nonnegative orthant. -/
theorem finiteStateMarkovPreterminalHoldingMeasure_eq_withDensity
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State)
    (hEscape : ∀ i : Fin n, generator.escapeRate (states i.castSucc) ≠ 0) :
    Measure.pi (fun i : Fin n =>
        finiteStateHoldingTimeMeasure generator T (states i.castSucc)) =
      (volume.restrict (Set.Ici 0)).withDensity
        (finiteStateMarkovPreterminalHoldingDensity generator states) := by
  let base := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ici 0)
  let density := fun i : Fin n => fun wait : ℝ => ENNReal.ofReal
    ((generator.escapeRate (states i.castSucc) : ℝ) *
      Real.exp (-((generator.escapeRate (states i.castSucc) : ℝ) * wait)))
  have hPositive (i : Fin n) : 0 < (generator.escapeRate (states i.castSucc) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (hEscape i))
  have hHolding (i : Fin n) :
      finiteStateHoldingTimeMeasure generator T (states i.castSucc) =
        (base i).withDensity (density i) := by
    rw [finiteStateHoldingTimeMeasure_eq_expMeasure generator T _ (hPositive i)]
    exact FiniteMarkovProcesses.InformationTheory.expMeasure_eq_restrict_withDensity _
  let (i : Fin n) : IsProbabilityMeasure
      (finiteStateHoldingTimeMeasure generator T (states i.castSucc)) :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T _
  let (i : Fin n) : SigmaFinite ((base i).withDensity (density i)) := by
    rw [← hHolding i]
    infer_instance
  rw [show (fun i : Fin n => finiteStateHoldingTimeMeasure generator T
    (states i.castSucc)) = (fun i => (base i).withDensity (density i)) from funext hHolding]
  rw [Measure.pi_withDensity_fin base density (by intro i; fun_prop)]
  have hBase : Measure.pi base = volume.restrict (Set.Ici 0) := by
    rw [← MeasureTheory.Measure.restrict_pi_pi
      (fun _ : Fin n => (volume : Measure ℝ)) (fun _ => Set.Ici (0 : ℝ))]
    rw [← MeasureTheory.volume_pi]
    rw [Set.pi_univ_Ici]
    rfl
  rw [hBase]
  congr 1

/-- Forget the terminal waiting coordinate of a finite waiting vector. -/
def finiteStatePreterminalWaits {n : ℕ} (waits : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => waits i.castSucc

/-- Preterminal waits whose cumulative event times lie in the ordered physical simplex. -/
def finiteStateOrderedPreterminalWaits (n : ℕ) (T : ℝ) : Set (Fin n → ℝ) :=
  cumulativeWaitTimes n ⁻¹' orderedJumpTimes n T

/-- Horizon duration remaining after all preterminal waits. -/
def finiteStateHorizonRemainingAfterWaits {n : ℕ} (T : ℝ) (waits : Fin n → ℝ) : ℝ :=
  T - ∑ i, waits i

/-- Physical survival density contributed by the terminal dwell after all preterminal waits. -/
noncomputable def finiteStateMarkovTerminalSurvivalDensity
    (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) {n : ℕ} (states : Fin (n + 1) → State) (waits : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-((generator.escapeRate (states (Fin.last n)) : ℝ) *
      finiteStateHorizonRemainingAfterWaits T waits)))

/-- On the ordered preterminal domain, the horizon duration remaining after the waits is
nonnegative. -/
theorem finiteStateHorizonRemainingAfterWaits_nonneg
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    {waits : Fin n → ℝ} (hWaits : waits ∈ finiteStateOrderedPreterminalWaits n T) :
    0 ≤ finiteStateHorizonRemainingAfterWaits T waits := by
  cases n with
  | zero => simpa [finiteStateHorizonRemainingAfterWaits]
  | succ n =>
      rw [finiteStateOrderedPreterminalWaits, Set.mem_preimage,
        cumulativeWaitTimes_mem_orderedJumpTimes_iff] at hWaits
      unfold finiteStateHorizonRemainingAfterWaits
      linarith [hWaits.2]

/-- On the ordered preterminal domain, the remaining horizon precedes the absorbing fallback
time used by the normalized Gillespie construction. -/
theorem finiteStateHorizonRemainingAfterWaits_le_fallback
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    {waits : Fin n → ℝ} (hWaits : waits ∈ finiteStateOrderedPreterminalWaits n T) :
    finiteStateHorizonRemainingAfterWaits T waits ≤ max T 0 + 1 := by
  have hSum : 0 ≤ ∑ i, waits i := by
    cases n with
    | zero => simp
    | succ n =>
        rw [finiteStateOrderedPreterminalWaits, Set.mem_preimage,
          cumulativeWaitTimes_mem_orderedJumpTimes_iff] at hWaits
        exact Finset.sum_nonneg fun i _ => (hWaits.1 i).le
  unfold finiteStateHorizonRemainingAfterWaits
  rw [max_eq_left hT]
  linarith

/-- Splitting off the terminal wait carries the canonical waiting-vector crossing event to the
ordered preterminal domain and state-dependent terminal upper tail. -/
theorem finiteStateTerminalFirstWaitSplit_preimage_firstCrossing
    (n : ℕ) (T : ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) ⁻¹'
        {pair : ℝ × (Fin n → ℝ) |
          pair.2 ∈ finiteStateOrderedPreterminalWaits n T ∧
            finiteStateHorizonRemainingAfterWaits T pair.2 ≤ pair.1} =
      finiteStateWaitingFirstCrosses n T := by
  ext waits
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, finiteStateWaitingFirstCrosses,
    finiteStateOrderedPreterminalWaits, finiteStateHorizonRemainingAfterWaits]
  dsimp [MeasurableEquiv.piFinSuccAbove]
  simp [Fin.init_def]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Splitting the full holding-time product at its terminal coordinate yields the terminal law
times the product of all preterminal laws. -/
theorem finiteStateTerminalFirstWaitSplit_map_holdingMeasure
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) :
    Measure.map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
        (Measure.pi fun i : Fin (n + 1) =>
          finiteStateHoldingTimeMeasure generator T (states i)) =
      (finiteStateHoldingTimeMeasure generator T (states (Fin.last n))).prod
        (Measure.pi fun i : Fin n =>
          finiteStateHoldingTimeMeasure generator T (states i.castSucc)) := by
  let (i : Fin (n + 1)) : IsProbabilityMeasure
      (finiteStateHoldingTimeMeasure generator T (states i)) :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T _
  rw [(MeasureTheory.measurePreserving_piFinSuccAbove
    (fun i : Fin (n + 1) => finiteStateHoldingTimeMeasure generator T (states i))
    (Fin.last n)).map_eq]
  simp only [Fin.succAbove_last_apply]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Integrating the terminal crossing dwell from the complete holding-time product gives exactly
the physical terminal survival density on the ordered preterminal waiting domain. This includes
an absorbing terminal row without assigning it a Lebesgue density. -/
theorem finiteStateMarkovPreterminalWaitingMeasure_firstCrossing
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T)
    {n : ℕ} (states : Fin (n + 1) → State) :
    Measure.map finiteStatePreterminalWaits
        ((Measure.pi fun i : Fin (n + 1) =>
            finiteStateHoldingTimeMeasure generator T (states i)).restrict
          (finiteStateWaitingFirstCrosses n T)) =
      ((Measure.pi fun i : Fin n =>
          finiteStateHoldingTimeMeasure generator T (states i.castSucc)).restrict
        (finiteStateOrderedPreterminalWaits n T)).withDensity
          (finiteStateMarkovTerminalSurvivalDensity generator T states) := by
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let terminal := finiteStateHoldingTimeMeasure generator T (states (Fin.last n))
  let preterminal := Measure.pi fun i : Fin n =>
    finiteStateHoldingTimeMeasure generator T (states i.castSucc)
  have hPreterminalWaits : finiteStatePreterminalWaits (n := n) = Prod.snd ∘ split := by
    funext waits index
    change waits index.castSucc = waits ((Fin.last n).succAbove index)
    rw [Fin.succAbove_last_apply]
  have hDomain : MeasurableSet (finiteStateOrderedPreterminalWaits n T) :=
    (measurableSet_orderedJumpTimes n T).preimage (measurable_cumulativeWaitTimes n)
  have hRemaining : Measurable (finiteStateHorizonRemainingAfterWaits (n := n) T) := by
    unfold finiteStateHorizonRemainingAfterWaits
    fun_prop
  have hSurvival (waits : Fin n → ℝ)
      (hWaits : waits ∈ finiteStateOrderedPreterminalWaits n T) :
      terminal (Set.Ici (finiteStateHorizonRemainingAfterWaits T waits)) =
        finiteStateMarkovTerminalSurvivalDensity generator T states waits := by
    unfold terminal finiteStateMarkovTerminalSurvivalDensity
    exact finiteStateHoldingTimeMeasure_Ici generator T _
      (finiteStateHorizonRemainingAfterWaits_nonneg n T hT hWaits)
      (finiteStateHorizonRemainingAfterWaits_le_fallback n T hT hWaits) _
  let : IsProbabilityMeasure terminal :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T _
  let (i : Fin n) : IsProbabilityMeasure
      (finiteStateHoldingTimeMeasure generator T (states i.castSucc)) :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T _
  have : SFinite preterminal := by
    unfold preterminal
    infer_instance
  rw [hPreterminalWaits]
  rw [← Measure.map_map measurable_snd split.measurable]
  rw [← finiteStateTerminalFirstWaitSplit_preimage_firstCrossing n T]
  rw [← split.restrict_map
    (Measure.pi fun i : Fin (n + 1) =>
      finiteStateHoldingTimeMeasure generator T (states i))
    {pair : ℝ × (Fin n → ℝ) |
      pair.2 ∈ finiteStateOrderedPreterminalWaits n T ∧
        finiteStateHorizonRemainingAfterWaits T pair.2 ≤ pair.1}]
  rw [finiteStateTerminalFirstWaitSplit_map_holdingMeasure generator T states]
  exact Measure.map_snd_restrict_terminalIci terminal preterminal
    (finiteStateOrderedPreterminalWaits n T) hDomain
    (finiteStateHorizonRemainingAfterWaits T) hRemaining
    (finiteStateMarkovTerminalSurvivalDensity generator T states) hSurvival

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On cumulative waiting-time coordinates, the integrated escape equals the sum of the
preterminal holding contributions and the terminal survival contribution. -/
theorem finiteStateMarkovIntegratedEscape_cumulativeWaitTimes
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) (waits : Fin n → ℝ) :
    finiteStateMarkovIntegratedEscape generator T states (cumulativeWaitTimes n waits) =
      (∑ i : Fin n,
        (generator.escapeRate (states i.castSucc) : ℝ) * waits i) +
      (generator.escapeRate (states (Fin.last n)) : ℝ) *
        finiteStateHorizonRemainingAfterWaits T waits := by
  unfold finiteStateMarkovIntegratedEscape
  rw [Fin.sum_univ_castSucc]
  simp [finiteStateHorizonRemainingAfterWaits]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A nonabsorbing row's escape rate cancels its normalized jump-destination probability to
recover the original jump rate, as an extended nonnegative-real identity. -/
theorem escapeRate_mul_jumpDestinationPMF
    (generator : FiniteStateMarkovGenerator State) (state target : State)
    (hEscape : generator.escapeRate state ≠ 0) :
    (generator.escapeRate state : ℝ≥0∞) *
        finiteStateJumpDestinationPMF generator state target =
      (generator.rate state target : ℝ≥0∞) := by
  rw [finiteStateJumpDestinationPMF_apply_of_ne_zero generator state target hEscape]
  norm_cast
  exact mul_div_cancel₀ (generator.rate state target) hEscape

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a state word with nonabsorbing preterminal rows, the state-word coefficient, holding-time
density, and terminal survival density multiply to the physical jump-slice density. -/
theorem finiteStateMarkovStateWordWaitingDensity_eq_jumpSliceDensity
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) (waits : Fin n → ℝ)
    (hEscape : ∀ i : Fin n, generator.escapeRate (states i.castSucc) ≠ 0) :
    finiteStateMarkovStateWordProbability initial generator states *
        (finiteStateMarkovPreterminalHoldingDensity generator states waits *
          finiteStateMarkovTerminalSurvivalDensity generator T states waits) =
      ENNReal.ofReal (finiteStateMarkovJumpSliceDensity initial generator T states
        (cumulativeWaitTimes n waits)) := by
  unfold finiteStateMarkovStateWordProbability
  unfold finiteStateMarkovPreterminalHoldingDensity
  unfold finiteStateMarkovTerminalSurvivalDensity
  unfold finiteStateMarkovJumpSliceDensity finiteStateMarkovJumpRateProduct
  simp_rw [ENNReal.ofReal_mul
    (FiniteStateMarkovGenerator.escapeRate_toReal_nonneg generator _)]
  rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg
    (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _))]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun _ _ => NNReal.coe_nonneg (generator.rate _ _))]
  rw [ENNReal.ofReal_toReal (initial.apply_ne_top (states 0))]
  simp only [ENNReal.ofReal_coe_nnreal]
  rw [Finset.prod_mul_distrib]
  simp_rw [mul_assoc]
  have hRates :
      (∏ i : Fin n,
          finiteStateJumpDestinationPMF generator (states i.castSucc) (states i.succ)) *
        ∏ i : Fin n, (generator.escapeRate (states i.castSucc) : ℝ≥0∞) =
      ∏ i : Fin n, (generator.rate (states i.castSucc) (states i.succ) : ℝ≥0∞) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [mul_comm]
    exact escapeRate_mul_jumpDestinationPMF generator _ _ (hEscape i)
  rw [← hRates]
  rw [mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [← Real.exp_sum, ← Real.exp_add]
  rw [finiteStateMarkovIntegratedEscape_cumulativeWaitTimes]
  rw [Finset.sum_neg_distrib]
  ring_nf

/-- Every ordered preterminal waiting vector lies in the coordinatewise nonnegative orthant. -/
theorem finiteStateOrderedPreterminalWaits_subset_nonnegative (n : ℕ) (T : ℝ) :
    finiteStateOrderedPreterminalWaits n T ⊆ Set.Ici 0 := by
  intro waits hWaits
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n =>
      rw [finiteStateOrderedPreterminalWaits, Set.mem_preimage,
        cumulativeWaitTimes_mem_orderedJumpTimes_iff] at hWaits
      exact fun i => (hWaits.1 i).le

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a fixed state word whose preterminal rows are nonabsorbing, the normalized generative
waiting-time law, transported to cumulative jump times, equals the canonical physical density
measure on the ordered jump-time simplex. -/
theorem finiteStateMarkovPositiveStateWordCumulativeMeasure_eq_densitySlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State)
    (hEscape : ∀ i : Fin n, generator.escapeRate (states i.castSucc) ≠ 0) :
    finiteStateMarkovStateWordProbability initial generator states •
        Measure.map (cumulativeWaitTimes n)
          (((Measure.pi fun i : Fin n =>
              finiteStateHoldingTimeMeasure generator T (states i.castSucc)).restrict
            (finiteStateOrderedPreterminalWaits n T)).withDensity
              (finiteStateMarkovTerminalSurvivalDensity generator T states)) =
      (volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times => ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity initial generator T states times)) := by
  let coefficient := finiteStateMarkovStateWordProbability initial generator states
  let preDensity := finiteStateMarkovPreterminalHoldingDensity generator states
  let survival := finiteStateMarkovTerminalSurvivalDensity generator T states
  let physicalDensity := fun times => ENNReal.ofReal
    (finiteStateMarkovJumpSliceDensity initial generator T states times)
  have hDomain : MeasurableSet (finiteStateOrderedPreterminalWaits n T) :=
    (measurableSet_orderedJumpTimes n T).preimage (measurable_cumulativeWaitTimes n)
  have hPreDensity : Measurable preDensity :=
    measurable_finiteStateMarkovPreterminalHoldingDensity generator states
  have hSurvival : Measurable survival := by
    change Measurable (fun waits : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (-((generator.escapeRate (states (Fin.last n)) : ℝ) *
        (T - ∑ i, waits i)))))
    fun_prop
  have hPhysicalDensity : Measurable physicalDensity := by
    dsimp [physicalDensity]
    exact (measurable_finiteStateMarkovJumpSliceDensity initial generator T states).ennreal_ofReal
  rw [finiteStateMarkovPreterminalHoldingMeasure_eq_withDensity
    generator T states hEscape]
  rw [restrict_withDensity hDomain]
  rw [Measure.restrict_restrict_of_subset
    (finiteStateOrderedPreterminalWaits_subset_nonnegative n T)]
  rw [← withDensity_mul (volume.restrict (finiteStateOrderedPreterminalWaits n T))
    hPreDensity hSurvival]
  rw [← Measure.map_smul coefficient (measurable_cumulativeWaitTimes n).aemeasurable]
  change Measure.map (cumulativeWaitTimes n)
    (coefficient • (volume.restrict (finiteStateOrderedPreterminalWaits n T)).withDensity
      (preDensity * survival)) = _
  have hWeighted :
      coefficient • (volume.restrict
          (finiteStateOrderedPreterminalWaits n T)).withDensity (preDensity * survival) =
        (volume.restrict (finiteStateOrderedPreterminalWaits n T)).withDensity
          (coefficient • (preDensity * survival)) :=
    (withDensity_smul coefficient (hPreDensity.mul hSurvival)).symm
  rw [hWeighted]
  have hPullback :
      coefficient • (preDensity * survival) = physicalDensity ∘ cumulativeWaitTimes n := by
    funext waits
    exact finiteStateMarkovStateWordWaitingDensity_eq_jumpSliceDensity
      initial generator T states waits hEscape
  rw [hPullback]
  rw [Measure.map_withDensity_comp
    (volume.restrict (finiteStateOrderedPreterminalWaits n T))
    (measurable_cumulativeWaitTimes n) physicalDensity hPhysicalDensity]
  exact congrArg (fun μ : Measure (Fin n → ℝ) => μ.withDensity physicalDensity)
    (cumulativeWaitTimes_map_restrict_preimage_orderedJumpTimes n T)

/-- Every ordered preterminal waiting vector makes each of its coordinates strictly shorter than
the observation horizon. -/
theorem finiteStateOrderedPreterminalWaits_subset_eval_Iio
    (n : ℕ) (T : ℝ) (i : Fin n) :
    finiteStateOrderedPreterminalWaits n T ⊆ Function.eval i ⁻¹' Set.Iio T := by
  intro waits hWaits
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [finiteStateOrderedPreterminalWaits, Set.mem_preimage,
        cumulativeWaitTimes_mem_orderedJumpTimes_iff] at hWaits
      change waits i < T
      calc
        waits i ≤ ∑ j, waits j :=
          Finset.single_le_sum (fun j _ => (hWaits.1 j).le) (Finset.mem_univ i)
        _ < T := hWaits.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- If one preterminal state is absorbing, the product holding-time law gives zero mass to the
ordered preterminal waiting domain. -/
theorem finiteStateMarkovPreterminalHoldingMeasure_restrict_eq_zero_of_absorbing
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T)
    {n : ℕ} (states : Fin (n + 1) → State) (i : Fin n)
    (hEscape : generator.escapeRate (states i.castSucc) = 0) :
    (Measure.pi fun j : Fin n =>
        finiteStateHoldingTimeMeasure generator T (states j.castSucc)).restrict
      (finiteStateOrderedPreterminalWaits n T) = 0 := by
  let holding := fun j : Fin n =>
    finiteStateHoldingTimeMeasure generator T (states j.castSucc)
  let (j : Fin n) : IsProbabilityMeasure (holding j) :=
    finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T _
  apply Measure.restrict_eq_zero.mpr
  apply measure_mono_null (finiteStateOrderedPreterminalWaits_subset_eval_Iio n T i)
  apply Measure.pi_eval_preimage_null
  exact finiteStateHoldingTimeMeasure_Iio_eq_zero_of_escapeRate_eq_zero
    generator T hT _ hEscape

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A fixed state word containing an absorbing preterminal row has zero physical jump-rate
product. -/
theorem finiteStateMarkovJumpRateProduct_eq_zero_of_absorbing
    (generator : FiniteStateMarkovGenerator State)
    {n : ℕ} (states : Fin (n + 1) → State) (i : Fin n)
    (hEscape : generator.escapeRate (states i.castSucc) = 0) :
    finiteStateMarkovJumpRateProduct generator states = 0 := by
  unfold finiteStateMarkovJumpRateProduct
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  norm_cast
  exact generator.rate_eq_zero_of_escapeRate_eq_zero _ _ hEscape

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A fixed state word containing an absorbing preterminal row has identically zero physical
jump-slice density. -/
theorem finiteStateMarkovJumpSliceDensity_eq_zero_of_absorbing
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    {n : ℕ} (states : Fin (n + 1) → State) (i : Fin n)
    (hEscape : generator.escapeRate (states i.castSucc) = 0) :
    finiteStateMarkovJumpSliceDensity initial generator T states = 0 := by
  funext times
  unfold finiteStateMarkovJumpSliceDensity
  rw [finiteStateMarkovJumpRateProduct_eq_zero_of_absorbing generator states i hEscape]
  simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- On a state word containing an absorbing preterminal row, both the normalized generative
first-crossing measure and the physical density measure vanish. -/
theorem finiteStateMarkovAbsorbingStateWordCumulativeMeasure_eq_densitySlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) {n : ℕ} (states : Fin (n + 1) → State) (i : Fin n)
    (hEscape : generator.escapeRate (states i.castSucc) = 0) :
    finiteStateMarkovStateWordProbability initial generator states •
        Measure.map (cumulativeWaitTimes n)
          (((Measure.pi fun j : Fin n =>
              finiteStateHoldingTimeMeasure generator T (states j.castSucc)).restrict
            (finiteStateOrderedPreterminalWaits n T)).withDensity
              (finiteStateMarkovTerminalSurvivalDensity generator T states)) =
      (volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times => ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity initial generator T states times)) := by
  rw [finiteStateMarkovPreterminalHoldingMeasure_restrict_eq_zero_of_absorbing
    generator T hT states i hEscape]
  rw [withDensity_zero_left, Measure.map_zero, smul_zero]
  rw [finiteStateMarkovJumpSliceDensity_eq_zero_of_absorbing
    initial generator T states i hEscape]
  simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- For every fixed state word, the normalized generative first-crossing law transported to
cumulative jump times equals the canonical physical density measure. Positive-rate words use
Lebesgue density cancellation; words blocked by an absorbing preterminal row vanish on both
sides. -/
theorem finiteStateMarkovStateWordCumulativeMeasure_eq_densitySlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) {n : ℕ} (states : Fin (n + 1) → State) :
    finiteStateMarkovStateWordProbability initial generator states •
        Measure.map (cumulativeWaitTimes n)
          (((Measure.pi fun i : Fin n =>
              finiteStateHoldingTimeMeasure generator T (states i.castSucc)).restrict
            (finiteStateOrderedPreterminalWaits n T)).withDensity
              (finiteStateMarkovTerminalSurvivalDensity generator T states)) =
      (volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times => ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity initial generator T states times)) := by
  by_cases hEscape : ∀ i : Fin n, generator.escapeRate (states i.castSucc) ≠ 0
  · exact finiteStateMarkovPositiveStateWordCumulativeMeasure_eq_densitySlice
      initial generator T states hEscape
  · simp only [not_forall, Classical.not_not] at hEscape
    obtain ⟨i, hi⟩ := hEscape
    exact finiteStateMarkovAbsorbingStateWordCumulativeMeasure_eq_densitySlice
      initial generator T hT states i hi

/-- Restricting the finite timed-prefix law to one state word and exact first crossing, then
reading its waits, gives the corresponding scaled product holding law restricted to the exact
waiting-coordinate crossing event. -/
theorem finiteStateMarkovTimedPrefixWaitingTimes_firstCrossingStateWordSlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (n : ℕ) (states : Fin (n + 1) → State) :
    Measure.map finiteStateTimedPrefixWaitingTimes
        ((finiteStateMarkovTimedPrefixMeasure initial generator T n).restrict
          (finiteStateTimedPrefixWaitingTimes ⁻¹' finiteStateWaitingFirstCrosses n T ∩
            FiniteStateTimedPrefixHasStateWord states)) =
      finiteStateMarkovStateWordProbability initial generator states •
        (Measure.pi fun i : Fin (n + 1) =>
          finiteStateHoldingTimeMeasure generator T (states i)).restrict
            (finiteStateWaitingFirstCrosses n T) := by
  have hCrossing : MeasurableSet
      (finiteStateTimedPrefixWaitingTimes (State := State) ⁻¹'
        finiteStateWaitingFirstCrosses n T) :=
    (measurableSet_finiteStateWaitingFirstCrosses n T).preimage
      (measurable_finiteStateTimedPrefixWaitingTimes n)
  rw [← Measure.restrict_restrict hCrossing]
  rw [← Measure.restrict_map
    (measurable_finiteStateTimedPrefixWaitingTimes n)
    (measurableSet_finiteStateWaitingFirstCrosses n T)]
  rw [finiteStateMarkovTimedPrefixWaitingTimes_stateWordSlice]
  rw [Measure.restrict_smul]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Forgetting the terminal first-crossing dwell and accumulating the preterminal waits carries
the fixed-word waiting law to its terminal-survival-weighted cumulative-time measure. -/
theorem finiteStateMarkovCumulativeFirstCrossingMeasure_stateWordSlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (states : Fin (n + 1) → State) :
    Measure.map (cumulativeWaitTimes n ∘ finiteStatePreterminalWaits)
        (finiteStateMarkovStateWordProbability initial generator states •
          (Measure.pi fun i : Fin (n + 1) =>
            finiteStateHoldingTimeMeasure generator T (states i)).restrict
              (finiteStateWaitingFirstCrosses n T)) =
      finiteStateMarkovStateWordProbability initial generator states •
        Measure.map (cumulativeWaitTimes n)
          (((Measure.pi fun i : Fin n =>
              finiteStateHoldingTimeMeasure generator T (states i.castSucc)).restrict
            (finiteStateOrderedPreterminalWaits n T)).withDensity
              (finiteStateMarkovTerminalSurvivalDensity generator T states)) := by
  have hPreterminal : Measurable (finiteStatePreterminalWaits (n := n)) := by
    unfold finiteStatePreterminalWaits
    fun_prop
  rw [Measure.map_smul (finiteStateMarkovStateWordProbability initial generator states)
    ((measurable_cumulativeWaitTimes n).comp hPreterminal).aemeasurable]
  rw [← Measure.map_map (measurable_cumulativeWaitTimes n) hPreterminal]
  rw [finiteStateMarkovPreterminalWaitingMeasure_firstCrossing generator T hT states]

/-- Under the normalized infinite tape law, a fixed crossing-and-state-word event is almost
everywhere the pullback of the corresponding finite-prefix waiting-coordinate event. The
almost-everywhere qualification records that strict wait positivity is a theorem of the tape law,
not a definitional property of arbitrary tapes. -/
theorem tapeCrossingStateWord_ae_eq_prefixFirstCrossingStateWord
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (states : Fin (n + 1) → State) :
    Set.inter
        ({tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T n} :
          Set (ℕ → State × ℝ))
        ({tape : ℕ → State × ℝ |
          FiniteStateMarkovStoppedLaw.TapeHasStateWord n states tape} :
            Set (ℕ → State × ℝ)) =ᵐ[
      finiteStateMarkovJumpTapeMeasure initial generator T]
      finiteStateMarkovTapePrefix n ⁻¹'
        (finiteStateTimedPrefixWaitingTimes ⁻¹' finiteStateWaitingFirstCrosses n T ∩
          FiniteStateTimedPrefixHasStateWord states) := by
  filter_upwards [
    FiniteStateMarkovJumpTrajectory.ae_hasPositiveWaitingTimes_finiteStateMarkovJumpTapeMeasure
      initial generator T hT] with tape hPositive
  apply propext
  change
    (FirstCrossesJumpHorizonAt tape T n ∧
        FiniteStateMarkovStoppedLaw.TapeHasStateWord n states tape) ↔
      (finiteStateTimedPrefixWaitingTimes (finiteStateMarkovTapePrefix n tape) ∈
          finiteStateWaitingFirstCrosses n T ∧
        finiteStateMarkovTapePrefix n tape ∈ FiniteStateTimedPrefixHasStateWord states)
  constructor
  · rintro ⟨hCrossing, hWord⟩
    exact ⟨(firstCrossesJumpHorizonAt_iff_waitingFirstCrosses
      tape T n hPositive).mp hCrossing, hWord⟩
  · rintro ⟨hCrossing, hWord⟩
    exact ⟨(firstCrossesJumpHorizonAt_iff_waitingFirstCrosses
      tape T n hPositive).mpr hCrossing, hWord⟩

/-- On one jump count and state word, the normalized tape's cumulative first-crossing measure is
exactly the canonical physical jump-density slice. -/
theorem finiteStateMarkovTapeCumulativeFirstCrossingMeasure_stateWordSlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (states : Fin (n + 1) → State) :
    Measure.map (FiniteStateMarkovStoppedLaw.finiteStateMarkovCumulativeJumpTimesAt n)
        ((finiteStateMarkovJumpTapeMeasure initial generator T).restrict
          ({tape : ℕ → State × ℝ | FirstCrossesJumpHorizonAt tape T n} ∩
            {tape : ℕ → State × ℝ |
              FiniteStateMarkovStoppedLaw.TapeHasStateWord n states tape})) =
      (volume.restrict (orderedJumpTimes n T)).withDensity
        (fun times => ENNReal.ofReal
          (finiteStateMarkovJumpSliceDensity initial generator T states times)) := by
  let prefixReadout := finiteStateMarkovTapePrefix (State := State) n
  let waits := finiteStateTimedPrefixWaitingTimes (State := State) (n := n)
  let preterminal := finiteStatePreterminalWaits (n := n)
  let cumulative := cumulativeWaitTimes n
  let tapeEvent : Set (ℕ → State × ℝ) :=
    {tape | FirstCrossesJumpHorizonAt tape T n} ∩
      {tape | FiniteStateMarkovStoppedLaw.TapeHasStateWord n states tape}
  let prefixEvent := waits ⁻¹' finiteStateWaitingFirstCrosses n T ∩
    FiniteStateTimedPrefixHasStateWord states
  have hPrefix : Measurable prefixReadout := measurable_finiteStateMarkovTapePrefix n
  have hWaits : Measurable waits := measurable_finiteStateTimedPrefixWaitingTimes n
  have hPreterminal : Measurable preterminal := by
    unfold preterminal finiteStatePreterminalWaits
    fun_prop
  have hCumulative : Measurable cumulative := measurable_cumulativeWaitTimes n
  have hOutput : Measurable (cumulative ∘ preterminal ∘ waits) :=
    (hCumulative.comp hPreterminal).comp hWaits
  have hPrefixEvent : MeasurableSet prefixEvent :=
    ((measurableSet_finiteStateWaitingFirstCrosses n T).preimage hWaits).inter
      (measurableSet_finiteStateTimedPrefixHasStateWord states)
  have hCumulativePrefix :
      FiniteStateMarkovStoppedLaw.finiteStateMarkovCumulativeJumpTimesAt
          (State := State) n =
        (cumulative ∘ preterminal ∘ waits) ∘ prefixReadout := by
    funext tape
    rw [finiteStateMarkovCumulativeJumpTimesAt_eq_cumulativeWaitTimes]
    rfl
  have hEventAE : tapeEvent =ᵐ[finiteStateMarkovJumpTapeMeasure initial generator T]
      prefixReadout ⁻¹' prefixEvent :=
    tapeCrossingStateWord_ae_eq_prefixFirstCrossingStateWord
      initial generator T hT n states
  have hRestrict :
      (finiteStateMarkovJumpTapeMeasure initial generator T).restrict tapeEvent =
        (finiteStateMarkovJumpTapeMeasure initial generator T).restrict
          (prefixReadout ⁻¹' prefixEvent) :=
    Measure.restrict_congr_set hEventAE
  change Measure.map
    (FiniteStateMarkovStoppedLaw.finiteStateMarkovCumulativeJumpTimesAt n)
      ((finiteStateMarkovJumpTapeMeasure initial generator T).restrict tapeEvent) = _
  rw [hRestrict]
  rw [hCumulativePrefix]
  rw [← Measure.map_map hOutput hPrefix]
  rw [← Measure.restrict_map hPrefix hPrefixEvent]
  rw [finiteStateMarkovJumpTapePrefixMeasure_eq_timedPrefixMeasure]
  change Measure.map ((cumulative ∘ preterminal) ∘ waits)
    ((finiteStateMarkovTimedPrefixMeasure initial generator T n).restrict
      (waits ⁻¹' finiteStateWaitingFirstCrosses n T ∩
        FiniteStateTimedPrefixHasStateWord states)) = _
  rw [← Measure.map_map (hCumulative.comp hPreterminal) hWaits]
  rw [finiteStateMarkovTimedPrefixWaitingTimes_firstCrossingStateWordSlice]
  rw [finiteStateMarkovCumulativeFirstCrossingMeasure_stateWordSlice
    initial generator T hT n states]
  exact finiteStateMarkovStateWordCumulativeMeasure_eq_densitySlice
    initial generator T hT states

/-- At every nonnegative finite horizon, the normalized stopped Gillespie history construction is
identically the canonical physical CTMC density measure on the unbounded finite-jump-history
carrier. -/
theorem finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
        initial generator T =
      finiteStateMarkovJumpDensityMeasure initial generator T := by
  rw [FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure_eq_sum_stateWordSlices]
  rw [finiteStateMarkovJumpDensityMeasure_eq_sum_slices]
  congr 1
  funext n
  congr 1
  funext states
  congr 1
  exact finiteStateMarkovTapeCumulativeFirstCrossingMeasure_stateWordSlice
    initial generator T hT n states

/-- The normalized stopped Gillespie history law is concentrated on the exact ordered reduced
history carrier at every nonnegative observation horizon. -/
theorem ae_physicalAt_finiteStateMarkovStoppedHistoryMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ history ∂
        FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure
          initial generator T,
      history.PhysicalAt T := by
  rw [finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    initial generator T hT]
  exact ae_physicalAt_finiteStateMarkovJumpDensityMeasure initial generator T

/-- The canonical physical finite-state jump density is exactly normalized at every nonnegative
finite horizon. -/
theorem finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    FiniteStateMarkovJumpDensityIsNormalized initial generator T := by
  unfold FiniteStateMarkovJumpDensityIsNormalized
  rw [← finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure
    initial generator T hT]
  exact FiniteStateMarkovStoppedLaw.finiteStateMarkovStoppedHistoryMeasure_univ
    initial generator T hT

end FiniteMarkovProcesses.Probability
