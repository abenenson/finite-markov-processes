/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import FiniteMarkovProcesses.RelativeEntropy.ExponentialWaitingTime
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpLaw

/-!
# Generative finite-state Markov jump trajectories

This module constructs a normalized infinite Gillespie tape for a finite-state Markov jump
generator. Each coordinate records the state occupied during one dwell and the duration of that
dwell. Positive escape rates use Mathlib's normalized exponential measure; an absorbing state
uses a deterministic duration beyond the observation horizon. The jump-destination law is the
normalized row of off-diagonal rates, with an absorbing self-loop used only when the row vanishes.

The Ionescu--Tulcea trajectory is an actual probability measure. It is deliberately kept distinct
from the stopped physical-history law: proving almost-sure nonexplosion and identifying the
stopped tape's density against `finiteJumpHistoryBaseMeasure` are subsequent theorems.

## Main results

- `finiteStateHoldingTimeKernel`: normalized state-dependent holding-time kernel.
- `finiteStateJumpDestinationKernel`: normalized physical jump-destination kernel.
- `finiteStateTimedStepKernel`: one normalized destination-and-next-dwell step.
- `finiteStateMarkovJumpTapeMeasure`: normalized infinite Gillespie tape.
- `instIsProbabilityMeasureFiniteStateMarkovJumpTapeMeasure`: exact tape normalization.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Holding-time measure at one state. Positive escape rates use the exponential law. An
absorbing state receives a deterministic duration strictly beyond every nonnegative horizon. -/
noncomputable def finiteStateHoldingTimeMeasure
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State) : Measure ℝ :=
  if 0 < (generator.escapeRate state : ℝ) then
    expMeasure (generator.escapeRate state : ℝ)
  else Measure.dirac (max T 0 + 1)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every finite-state holding-time measure is normalized, including at absorbing states. -/
theorem finiteStateHoldingTimeMeasure_isProbabilityMeasure
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State) :
    IsProbabilityMeasure (finiteStateHoldingTimeMeasure generator T state) := by
  by_cases hEscape : 0 < (generator.escapeRate state : ℝ)
  · rw [finiteStateHoldingTimeMeasure, ite_eq_left hEscape]
    exact isProbabilityMeasure_expMeasure hEscape
  · rw [finiteStateHoldingTimeMeasure, ite_eq_right hEscape]
    infer_instance

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- At a positive escape rate, the holding-time measure is the corresponding exponential law. -/
theorem finiteStateHoldingTimeMeasure_eq_expMeasure
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State)
    (hEscape : 0 < (generator.escapeRate state : ℝ)) :
    finiteStateHoldingTimeMeasure generator T state =
      expMeasure (generator.escapeRate state : ℝ) := by
  rw [finiteStateHoldingTimeMeasure, ite_eq_left hEscape]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A zero-rate absorbing state has a deterministic wait beyond the observation horizon. -/
theorem finiteStateHoldingTimeMeasure_eq_dirac
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State)
    (hEscape : generator.escapeRate state = 0) :
    finiteStateHoldingTimeMeasure generator T state = Measure.dirac (max T 0 + 1) := by
  simp [finiteStateHoldingTimeMeasure, hEscape]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- An absorbing row's deterministic fallback dwell cannot end before a nonnegative observation
horizon. -/
theorem finiteStateHoldingTimeMeasure_Iio_eq_zero_of_escapeRate_eq_zero
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T) (state : State)
    (hEscape : generator.escapeRate state = 0) :
    finiteStateHoldingTimeMeasure generator T state (Set.Iio T) = 0 := by
  rw [finiteStateHoldingTimeMeasure_eq_dirac generator T state hEscape]
  rw [Measure.dirac_apply' _ measurableSet_Iio]
  have hNotMem : max T 0 + 1 ∉ Set.Iio T := by
    rw [Set.mem_Iio, max_eq_left hT]
    linarith
  simp [Set.indicator, hNotMem]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The survival function of a positive-rate exponential holding law. -/
theorem expMeasure_Ici
    {rate remaining : ℝ} (hRate : 0 < rate) (hRemaining : 0 ≤ remaining) :
    expMeasure rate (Set.Ici remaining) =
      ENNReal.ofReal (Real.exp (-(rate * remaining))) := by
  let := isProbabilityMeasure_expMeasure hRate
  rw [← Set.compl_Iio]
  rw [measure_compl measurableSet_Iio (measure_ne_top _ _), measure_univ]
  have hIio : expMeasure rate (Set.Iio remaining) =
      ENNReal.ofReal (1 - Real.exp (-(rate * remaining))) := by
    calc
      expMeasure rate (Set.Iio remaining) = expMeasure rate (Set.Iic remaining) :=
        measure_congr Iio_ae_eq_Iic
      _ = ENNReal.ofReal (1 - Real.exp (-(rate * remaining))) := by
        rw [← ofReal_cdf, cdf_expMeasure_eq hRate, ite_eq_left hRemaining]
  rw [hIio]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · congr 1
    ring
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every generative holding law has the physical exponential survival factor before the
absorbing fallback time. -/
theorem finiteStateHoldingTimeMeasure_Ici
    (generator : FiniteStateMarkovGenerator State) (T remaining : ℝ)
    (hRemaining : 0 ≤ remaining)
    (hBeforeFallback : remaining ≤ max T 0 + 1) (state : State) :
    finiteStateHoldingTimeMeasure generator T state (Set.Ici remaining) =
      ENNReal.ofReal
        (Real.exp (-((generator.escapeRate state : ℝ) * remaining))) := by
  by_cases hEscape : 0 < (generator.escapeRate state : ℝ)
  · rw [finiteStateHoldingTimeMeasure_eq_expMeasure generator T state hEscape]
    exact expMeasure_Ici hEscape hRemaining
  · have hEscapeZero : generator.escapeRate state = 0 := by
      apply le_antisymm
      · exact_mod_cast not_lt.mp hEscape
      · exact bot_le
    rw [finiteStateHoldingTimeMeasure_eq_dirac generator T state hEscapeZero]
    rw [Measure.dirac_apply' _ measurableSet_Ici]
    simp [Set.indicator, hBeforeFallback, hEscapeZero]

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A positive-rate exponential waiting law is concentrated on strictly positive durations. -/
theorem ae_positive_expMeasure {rate : ℝ} (hRate : 0 < rate) :
    ∀ᵐ wait ∂expMeasure rate, 0 < wait := by
  rw [ae_iff]
  simp only [not_lt]
  change expMeasure rate (Set.Iic 0) = 0
  let := isProbabilityMeasure_expMeasure hRate
  rw [← ofReal_cdf, cdf_expMeasure_eq hRate]
  simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every generative holding duration is strictly positive almost surely at a nonnegative
observation horizon. -/
theorem ae_positive_finiteStateHoldingTimeMeasure
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T) (state : State) :
    ∀ᵐ wait ∂finiteStateHoldingTimeMeasure generator T state, 0 < wait := by
  by_cases hEscape : 0 < (generator.escapeRate state : ℝ)
  · rw [finiteStateHoldingTimeMeasure_eq_expMeasure generator T state hEscape]
    exact ae_positive_expMeasure hEscape
  · have hEscapeZero : generator.escapeRate state = 0 := by
      apply le_antisymm
      · exact_mod_cast not_lt.mp hEscape
      · exact bot_le
    rw [finiteStateHoldingTimeMeasure_eq_dirac generator T state hEscapeZero]
    apply (ae_dirac_iff (measurable_const.lt measurable_id).setOf).2
    change 0 < max T 0 + 1
    rw [max_eq_left hT]
    linarith

/-- Sum of all state escape rates. It is a finite uniform bound on every individual escape
rate, used to obtain a state-independent finite-horizon tail estimate. -/
noncomputable def finiteStateTotalEscapeBound
    (generator : FiniteStateMarkovGenerator State) : ℝ≥0 :=
  ∑ state, generator.escapeRate state

/-- A block length strictly larger than every nonnegative observation horizon. -/
def finiteJumpHorizonBlockLength (T : ℝ) : ℝ :=
  max T 0 + 1

/-- Uniform upper bound on the probability that one holding time is shorter than the horizon
block. -/
noncomputable def finiteStateShortWaitBound
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (1 - Real.exp
      (-((finiteStateTotalEscapeBound generator : ℝ) * finiteJumpHorizonBlockLength T)))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The horizon block has strictly positive length. -/
theorem finiteJumpHorizonBlockLength_pos (T : ℝ) :
    0 < finiteJumpHorizonBlockLength T := by
  unfold finiteJumpHorizonBlockLength
  linarith [le_max_right T 0]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every state escape rate is bounded by the total finite-state escape rate. -/
theorem escapeRate_le_finiteStateTotalEscapeBound
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.escapeRate state ≤ finiteStateTotalEscapeBound generator := by
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ state)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The uniform short-wait bound is strictly below one. -/
theorem finiteStateShortWaitBound_lt_one
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateShortWaitBound generator T < 1 := by
  rw [finiteStateShortWaitBound, ENNReal.ofReal_lt_one]
  linarith [Real.exp_pos
    (-((finiteStateTotalEscapeBound generator : ℝ) * finiteJumpHorizonBlockLength T))]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every state-dependent holding law assigns at most the uniform short-wait bound to the
horizon block's open lower interval. -/
theorem finiteStateHoldingTimeMeasure_Iio_le_shortWaitBound
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State) :
    finiteStateHoldingTimeMeasure generator T state
        (Set.Iio (finiteJumpHorizonBlockLength T)) ≤
      finiteStateShortWaitBound generator T := by
  by_cases hEscape : 0 < (generator.escapeRate state : ℝ)
  · rw [finiteStateHoldingTimeMeasure_eq_expMeasure generator T state hEscape]
    calc
      expMeasure (generator.escapeRate state : ℝ)
          (Set.Iio (finiteJumpHorizonBlockLength T)) ≤
          expMeasure (generator.escapeRate state : ℝ)
            (Set.Iic (finiteJumpHorizonBlockLength T)) :=
        measure_mono Set.Iio_subset_Iic_self
      _ = ENNReal.ofReal
          (1 - Real.exp
            (-((generator.escapeRate state : ℝ) * finiteJumpHorizonBlockLength T))) := by
        let := isProbabilityMeasure_expMeasure hEscape
        rw [← ofReal_cdf, cdf_expMeasure_eq hEscape,
          ite_eq_left (finiteJumpHorizonBlockLength_pos T).le]
      _ ≤ finiteStateShortWaitBound generator T := by
        rw [finiteStateShortWaitBound]
        apply ENNReal.ofReal_le_ofReal
        have hRate : (generator.escapeRate state : ℝ) ≤
            (finiteStateTotalEscapeBound generator : ℝ) := by
          exact_mod_cast escapeRate_le_finiteStateTotalEscapeBound generator state
        have hExp :
            Real.exp
                (-((finiteStateTotalEscapeBound generator : ℝ) *
                  finiteJumpHorizonBlockLength T)) ≤
              Real.exp
                (-((generator.escapeRate state : ℝ) * finiteJumpHorizonBlockLength T)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [finiteJumpHorizonBlockLength_pos T]
        linarith
  · have hEscapeZero : generator.escapeRate state = 0 := by
      apply le_antisymm
      · exact_mod_cast not_lt.mp hEscape
      · exact bot_le
    rw [finiteStateHoldingTimeMeasure_eq_dirac generator T state hEscapeZero]
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp [finiteJumpHorizonBlockLength, Set.indicator]

/-- Markov kernel of state-dependent holding durations. -/
noncomputable def finiteStateHoldingTimeKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) : Kernel State ℝ :=
  Kernel.ofFunOfCountable (finiteStateHoldingTimeMeasure generator T)

/-- The original state-dependent holding-time kernel is Markov. -/
noncomputable instance instIsMarkovKernelFiniteStateHoldingTimeKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    IsMarkovKernel (finiteStateHoldingTimeKernel generator T) :=
  ⟨finiteStateHoldingTimeMeasure_isProbabilityMeasure generator T⟩

/-- Destination law obtained by normalizing one nonzero generator row. A zero row is represented
by a deterministic absorbing self-loop so that the generative tape remains infinite. -/
noncomputable def finiteStateJumpDestinationPMF
    (generator : FiniteStateMarkovGenerator State) (state : State) : PMF State :=
  if hEscape : generator.escapeRate state = 0 then pure state
  else PMF.ofFintype
    (fun target => (generator.rate state target / generator.escapeRate state : ℝ≥0))
    (by
      rw [← ENNReal.ofNNReal_finsetSum]
      congr 1
      rw [← Finset.sum_div]
      exact div_self hEscape)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A positive-rate destination probability is exactly the corresponding rate divided by the
escape rate. -/
theorem finiteStateJumpDestinationPMF_apply_of_ne_zero
    (generator : FiniteStateMarkovGenerator State) (state target : State)
    (hEscape : generator.escapeRate state ≠ 0) :
    finiteStateJumpDestinationPMF generator state target =
      (generator.rate state target / generator.escapeRate state : ℝ≥0) := by
  rw [finiteStateJumpDestinationPMF, dite_eq_right hEscape, PMF.ofFintype_apply]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- At a nonabsorbing state, multiplying a destination probability by the escape rate recovers
the physical directed jump rate. -/
theorem escapeRate_mul_jumpDestinationPMF_toReal
    (generator : FiniteStateMarkovGenerator State) (state target : State)
    (hEscape : generator.escapeRate state ≠ 0) :
    (generator.escapeRate state : ℝ) *
        (finiteStateJumpDestinationPMF generator state target).toReal =
      (generator.rate state target : ℝ) := by
  rw [finiteStateJumpDestinationPMF_apply_of_ne_zero generator state target hEscape]
  rw [ENNReal.coe_toReal]
  norm_cast
  exact mul_div_cancel₀ (generator.rate state target) hEscape

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- An absorbing generator row stays at its current state on the infinite tape. -/
theorem finiteStateJumpDestinationPMF_eq_pure
    (generator : FiniteStateMarkovGenerator State) (state : State)
    (hEscape : generator.escapeRate state = 0) :
    finiteStateJumpDestinationPMF generator state = pure state := by
  rw [finiteStateJumpDestinationPMF, dite_eq_left hEscape]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A positive-rate physical destination law assigns zero probability to virtual self-jumps. -/
@[simp]
theorem finiteStateJumpDestinationPMF_self
    (generator : FiniteStateMarkovGenerator State) (state : State)
    (hEscape : generator.escapeRate state ≠ 0) :
    finiteStateJumpDestinationPMF generator state state = 0 := by
  rw [finiteStateJumpDestinationPMF_apply_of_ne_zero generator state state hEscape,
    generator.rate_self, zero_div]
  rfl

/-- Markov kernel of physical jump destinations. -/
noncomputable def finiteStateJumpDestinationKernel
    (generator : FiniteStateMarkovGenerator State) : Kernel State State :=
  Kernel.ofFunOfCountable fun state =>
    (finiteStateJumpDestinationPMF generator state).toMeasure

/-- The original destination kernel, including its absorbing-row fallback, is Markov. -/
noncomputable instance instIsMarkovKernelFiniteStateJumpDestinationKernel
    (generator : FiniteStateMarkovGenerator State) :
    IsMarkovKernel (finiteStateJumpDestinationKernel generator) :=
  ⟨fun state => by
    change IsProbabilityMeasure (finiteStateJumpDestinationPMF generator state).toMeasure
    infer_instance⟩

/-- One Gillespie step: choose the physical destination and then draw that destination's next
holding duration. -/
noncomputable def finiteStateTimedStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Kernel State (State × ℝ) :=
  finiteStateJumpDestinationKernel generator ⊗ₖ
    (finiteStateHoldingTimeKernel generator T).comap Prod.snd measurable_snd

/-- The original destination and subsequent holding-time product kernel is Markov. -/
noncomputable instance instIsMarkovKernelFiniteStateTimedStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    IsMarkovKernel (finiteStateTimedStepKernel generator T) := by
  unfold finiteStateTimedStepKernel
  infer_instance

/-- Every one-step timed-state output has a strictly positive dwell almost surely. -/
theorem ae_positive_finiteStateTimedStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (hT : 0 ≤ T) (state : State) :
    ∀ᵐ timedState ∂finiteStateTimedStepKernel generator T state, 0 < timedState.2 := by
  rw [finiteStateTimedStepKernel]
  apply Kernel.ae_compProd_of_ae_ae (measurable_const.lt measurable_snd).setOf
  filter_upwards with target
  change ∀ᵐ wait ∂finiteStateHoldingTimeKernel generator T target, 0 < wait
  exact ae_positive_finiteStateHoldingTimeMeasure generator T hT target

/-- Every timed transition is shorter than the horizon block with probability at most the
state-independent short-wait bound. -/
theorem finiteStateTimedStepKernel_shortWait_le
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (state : State) :
    finiteStateTimedStepKernel generator T state
        {timedState | timedState.2 < finiteJumpHorizonBlockLength T} ≤
      finiteStateShortWaitBound generator T := by
  rw [finiteStateTimedStepKernel, Kernel.compProd_apply
    (measurableSet_lt measurable_snd measurable_const)]
  calc
    (∫⁻ target,
        ((finiteStateHoldingTimeKernel generator T).comap Prod.snd measurable_snd)
          (state, target)
          (Prod.mk target ⁻¹'
            {timedState | timedState.2 < finiteJumpHorizonBlockLength T})
        ∂finiteStateJumpDestinationKernel generator state) =
        ∫⁻ target,
          finiteStateHoldingTimeMeasure generator T target
            (Set.Iio (finiteJumpHorizonBlockLength T))
          ∂finiteStateJumpDestinationKernel generator state := by
      rfl
    _ ≤ ∫⁻ _target, finiteStateShortWaitBound generator T
          ∂finiteStateJumpDestinationKernel generator state :=
      lintegral_mono fun target =>
        finiteStateHoldingTimeMeasure_Iio_le_shortWaitBound generator T target
    _ = finiteStateShortWaitBound generator T := by
      simp

/-- Last coordinate in an Ionescu--Tulcea finite trajectory prefix. -/
def finiteTrajectoryCurrentIndex (n : ℕ) : Finset.Iic n :=
  ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- State occupied by the last timed coordinate in a finite trajectory prefix. -/
def finiteTimedTrajectoryCurrentState
    (n : ℕ) (history : (i : Finset.Iic n) → State × ℝ) : State :=
  (history (finiteTrajectoryCurrentIndex n)).1

omit [Fintype State] [MeasurableSingletonClass State] in
/-- Reading the current state from a finite timed trajectory is measurable. -/
theorem measurable_finiteTimedTrajectoryCurrentState (n : ℕ) :
    Measurable (finiteTimedTrajectoryCurrentState (State := State) n) :=
  (measurable_pi_apply (finiteTrajectoryCurrentIndex n)).fst

/-- History-dependent step kernel used by the Ionescu--Tulcea construction. It depends only on
the current state, while retaining the full prefix in its typed input. -/
noncomputable def finiteStateMarkovJumpTrajectoryStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State × ℝ) (State × ℝ) :=
  (finiteStateTimedStepKernel generator T).comap
    (finiteTimedTrajectoryCurrentState n) (measurable_finiteTimedTrajectoryCurrentState n)

/-- The original current-state comap of the timed trajectory step kernel is Markov. -/
noncomputable instance instIsMarkovKernelFiniteStateMarkovJumpTrajectoryStepKernel
    (generator : FiniteStateMarkovGenerator State) (T : ℝ) (n : ℕ) :
    IsMarkovKernel (finiteStateMarkovJumpTrajectoryStepKernel generator T n) := by
  unfold finiteStateMarkovJumpTrajectoryStepKernel
  infer_instance

/-- Joint initial-state and first-holding-time measure. -/
noncomputable def finiteStateInitialTimedStateMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (State × ℝ) :=
  initial.toMeasure ⊗ₘ finiteStateHoldingTimeKernel generator T

/-- The original initial-state and first-holding-time law has total mass one. -/
noncomputable instance instIsProbabilityMeasureFiniteStateInitialTimedStateMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    IsProbabilityMeasure (finiteStateInitialTimedStateMeasure initial generator T) := by
  unfold finiteStateInitialTimedStateMeasure
  infer_instance

/-- The initial timed state has a strictly positive first dwell almost surely. -/
theorem ae_positive_finiteStateInitialTimedStateMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ timedState ∂finiteStateInitialTimedStateMeasure initial generator T,
      0 < timedState.2 := by
  rw [finiteStateInitialTimedStateMeasure]
  apply Measure.ae_compProd_of_ae_ae (measurable_const.lt measurable_snd).setOf
  filter_upwards with state
  exact ae_positive_finiteStateHoldingTimeMeasure generator T hT state

/-- The initial state-and-wait law is shorter than the horizon block with probability at most
the same uniform short-wait bound as every later transition. -/
theorem finiteStateInitialTimedStateMeasure_shortWait_le
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateInitialTimedStateMeasure initial generator T
        {timedState | timedState.2 < finiteJumpHorizonBlockLength T} ≤
      finiteStateShortWaitBound generator T := by
  rw [finiteStateInitialTimedStateMeasure, Measure.compProd_apply
    (measurableSet_lt measurable_snd measurable_const)]
  calc
    (∫⁻ state,
        finiteStateHoldingTimeKernel generator T state
          (Prod.mk state ⁻¹'
            {timedState | timedState.2 < finiteJumpHorizonBlockLength T})
        ∂initial.toMeasure) =
        ∫⁻ state,
          finiteStateHoldingTimeMeasure generator T state
            (Set.Iio (finiteJumpHorizonBlockLength T))
          ∂initial.toMeasure := by
      rfl
    _ ≤ ∫⁻ _state, finiteStateShortWaitBound generator T ∂initial.toMeasure :=
      lintegral_mono fun state =>
        finiteStateHoldingTimeMeasure_Iio_le_shortWaitBound generator T state
    _ = finiteStateShortWaitBound generator T := by
      simp

/-- Embed one timed state as the unique coordinate of an `Iic 0` trajectory seed. -/
def finiteStateMarkovJumpTrajectorySeed
    (timedState : State × ℝ) : (_unusedIndex : Finset.Iic 0) → State × ℝ :=
  fun _ => timedState

omit [Fintype State] [MeasurableSingletonClass State] in
/-- The singleton trajectory seed embedding is measurable. -/
theorem measurable_finiteStateMarkovJumpTrajectorySeed :
    Measurable (finiteStateMarkovJumpTrajectorySeed (State := State)) := by
  apply Measurable.of_eval
  intro index
  exact measurable_id

/-- Initial measure on the one-coordinate seed expected by `Kernel.traj`. -/
noncomputable def finiteStateMarkovJumpTrajectorySeedMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure ((i : Finset.Iic 0) → State × ℝ) :=
  (finiteStateInitialTimedStateMeasure initial generator T).map
    finiteStateMarkovJumpTrajectorySeed

/-- The original singleton-coordinate trajectory seed pushforward has total mass one. -/
noncomputable instance instIsProbabilityMeasureFiniteStateMarkovJumpTrajectorySeedMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpTrajectorySeedMeasure initial generator T) := by
  unfold finiteStateMarkovJumpTrajectorySeedMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_finiteStateMarkovJumpTrajectorySeed.aemeasurable).2 inferInstance

/-- Normalized infinite Gillespie tape. Coordinate `n` stores the state occupied during the
`n`th dwell and that dwell's duration. Absorbing rows continue with deterministic out-of-horizon
coordinates, so the carrier remains a total sequence. -/
noncomputable def finiteStateMarkovJumpTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (ℕ → State × ℝ) :=
  Kernel.traj (X := fun _ => State × ℝ)
      (finiteStateMarkovJumpTrajectoryStepKernel generator T) 0 ∘ₘ
    finiteStateMarkovJumpTrajectorySeedMeasure initial generator T

/-- The original infinite Gillespie tape law has total mass one. -/
noncomputable instance instIsProbabilityMeasureFiniteStateMarkovJumpTapeMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    IsProbabilityMeasure (finiteStateMarkovJumpTapeMeasure initial generator T) := by
  unfold finiteStateMarkovJumpTapeMeasure
  infer_instance

/-- Exact normalization of the infinite Gillespie tape. -/
theorem finiteStateMarkovJumpTapeMeasure_univ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateMarkovJumpTapeMeasure initial generator T Set.univ = 1 :=
  measure_univ

end FiniteMarkovProcesses.Probability
