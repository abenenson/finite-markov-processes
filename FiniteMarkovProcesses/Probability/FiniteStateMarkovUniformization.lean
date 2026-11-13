/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovPartialConjugateLaw

/-!
# Uniformized finite-state Markov transition chains

This module constructs a strictly dominating clock for every finite-state Markov jump generator
and the corresponding stochastic transition row with an explicit virtual self-event. The clock
is fixed as one plus the sum of all escape rates, so it remains positive even for an absorbing
generator. A stationary distribution of the physical generator is proved stationary for the
uniformized discrete transition chain.

The virtual transition chain is an expectation and normalization device. It is not a physical
jump law; a later theorem must delete self-events and identify the resulting history law with the
canonical physical-jump density before transferring any action claim.

## Main Results

- `FiniteStateMarkovGenerator.uniformizationRate`: a strictly positive uniform clock.
- `FiniteStateMarkovGenerator.uniformizedTransitionPMF`: the normalized virtual-event row.
- `FiniteStateMarkovStationaryDistribution.uniformizedTransition_stationary`: stationarity of
  the physical weights under one uniformized transition.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- Strictly positive clock rate dominating every state escape rate. -/
noncomputable def uniformizationRate (generator : FiniteStateMarkovGenerator State) : ℝ≥0 :=
  finiteStateTotalEscapeBound generator + 1

omit [DecidableEq State] in
/-- The uniformization clock is strictly positive. -/
theorem uniformizationRate_pos (generator : FiniteStateMarkovGenerator State) :
    0 < generator.uniformizationRate := by
  unfold uniformizationRate
  exact lt_add_of_le_of_pos zero_le zero_lt_one

omit [DecidableEq State] in
/-- Every source escape rate is bounded by the uniformization clock. -/
theorem escapeRate_le_uniformizationRate
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.escapeRate state ≤ generator.uniformizationRate :=
  (escapeRate_le_finiteStateTotalEscapeBound generator state).trans <|
    le_add_of_nonneg_right zero_le_one

/-- One uniformized transition weight. A genuine off-diagonal transition has weight `q/Λ`;
the diagonal carries the remaining virtual-event probability `1 - escape/Λ`. -/
noncomputable def uniformizedTransitionWeight
    (generator : FiniteStateMarkovGenerator State) (source target : State) : ℝ≥0 :=
  if source = target then
    1 - generator.escapeRate source / generator.uniformizationRate
  else generator.rate source target / generator.uniformizationRate

/-- An off-diagonal uniformized transition has its exact rate-over-clock weight. -/
theorem uniformizedTransitionWeight_of_ne
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hNe : source ≠ target) :
    generator.uniformizedTransitionWeight source target =
      generator.rate source target / generator.uniformizationRate := by
  simp [uniformizedTransitionWeight, hNe]

/-- A uniformized self-event has the exact unused escape fraction. -/
theorem uniformizedTransitionWeight_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.uniformizedTransitionWeight state state =
      1 - generator.escapeRate state / generator.uniformizationRate := by
  simp [uniformizedTransitionWeight]

/-- Each uniformized transition row has total weight one. -/
theorem sum_uniformizedTransitionWeight
    (generator : FiniteStateMarkovGenerator State) (source : State) :
    ∑ target, generator.uniformizedTransitionWeight source target = 1 := by
  classical
  rw [show (∑ target, generator.uniformizedTransitionWeight source target) =
      generator.uniformizedTransitionWeight source source +
        ∑ target ∈ Finset.univ.erase source,
          generator.uniformizedTransitionWeight source target by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ source), add_comm]]
  rw [generator.uniformizedTransitionWeight_self]
  have hOffDiagonal (target : State) (hTarget : target ∈ Finset.univ.erase source) :
      generator.uniformizedTransitionWeight source target =
        generator.rate source target / generator.uniformizationRate := by
    apply generator.uniformizedTransitionWeight_of_ne
    exact fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm
  rw [Finset.sum_congr rfl hOffDiagonal]
  rw [← Finset.sum_div]
  have hRateSum :
      ∑ target ∈ Finset.univ.erase source, generator.rate source target =
        generator.escapeRate source := by
    rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self source)]
    rfl
  rw [hRateSum]
  exact tsub_add_cancel_of_le <| by
    exact (div_le_one generator.uniformizationRate_pos).mpr
      (generator.escapeRate_le_uniformizationRate source)

/-- Probability mass function of one uniformized virtual-event transition. -/
noncomputable def uniformizedTransitionPMF
    (generator : FiniteStateMarkovGenerator State) (source : State) : PMF State :=
  PMF.ofFintype
    (fun target ↦ (generator.uniformizedTransitionWeight source target : ℝ≥0∞))
    (by
      rw [← ENNReal.ofNNReal_finsetSum]
      congr 1
      exact generator.sum_uniformizedTransitionWeight source)

/-- Evaluating the uniformized PMF recovers the corresponding transition weight. -/
@[simp]
theorem uniformizedTransitionPMF_apply
    (generator : FiniteStateMarkovGenerator State) (source target : State) :
    generator.uniformizedTransitionPMF source target =
      generator.uniformizedTransitionWeight source target := by
  simp [uniformizedTransitionPMF]

/-- Real weight of an off-diagonal uniformized transition. -/
theorem uniformizedTransitionPMF_toReal_of_ne
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hNe : source ≠ target) :
    (generator.uniformizedTransitionPMF source target).toReal =
      (generator.rate source target : ℝ) / generator.uniformizationRate := by
  rw [generator.uniformizedTransitionPMF_apply,
    generator.uniformizedTransitionWeight_of_ne hNe, ENNReal.coe_toReal]
  norm_cast

/-- Real weight of a uniformized virtual self-event. -/
theorem uniformizedTransitionPMF_toReal_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    (generator.uniformizedTransitionPMF state state).toReal =
      1 - (generator.escapeRate state : ℝ) / generator.uniformizationRate := by
  rw [generator.uniformizedTransitionPMF_apply,
    generator.uniformizedTransitionWeight_self, ENNReal.coe_toReal]
  norm_cast
  rw [NNReal.coe_sub <| (div_le_one generator.uniformizationRate_pos).mpr
    (generator.escapeRate_le_uniformizationRate state)]
  norm_num

end FiniteStateMarkovGenerator

namespace FiniteStateMarkovStationaryDistribution

/-- A physical stationary distribution is stationary under one virtual uniformized event. -/
theorem uniformizedTransition_stationary
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteMarkovProcesses.Probability.FiniteStateMarkovStationaryDistribution
      generator) (target : State) :
    ∑ source, (stationary.weight source : ℝ) *
        (generator.uniformizedTransitionPMF source target).toReal =
      stationary.weight target := by
  classical
  rw [show (∑ source, (stationary.weight source : ℝ) *
      (generator.uniformizedTransitionPMF source target).toReal) =
      (stationary.weight target : ℝ) *
          (generator.uniformizedTransitionPMF target target).toReal +
        ∑ source ∈ Finset.univ.erase target,
          (stationary.weight source : ℝ) *
            (generator.uniformizedTransitionPMF source target).toReal by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ target), add_comm]]
  rw [generator.uniformizedTransitionPMF_toReal_self]
  have hOffDiagonal (source : State) (hSource : source ∈ Finset.univ.erase target) :
      (generator.uniformizedTransitionPMF source target).toReal =
        (generator.rate source target : ℝ) / generator.uniformizationRate := by
    apply generator.uniformizedTransitionPMF_toReal_of_ne
    exact (Finset.mem_erase.mp hSource).1
  have hOffDiagonalTerm (source : State) (hSource : source ∈ Finset.univ.erase target) :
      (stationary.weight source : ℝ) *
          (generator.uniformizedTransitionPMF source target).toReal =
        (stationary.weight source : ℝ) *
          ((generator.rate source target : ℝ) / generator.uniformizationRate) := by
    rw [hOffDiagonal source hSource]
  rw [Finset.sum_congr rfl hOffDiagonalTerm]
  rw [show (∑ source ∈ Finset.univ.erase target,
      (stationary.weight source : ℝ) *
        ((generator.rate source target : ℝ) / generator.uniformizationRate)) =
      (∑ source ∈ Finset.univ.erase target,
        (stationary.weight source : ℝ) * (generator.rate source target : ℝ)) /
          generator.uniformizationRate by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro source _
    ring]
  have hIncoming :
      ∑ source ∈ Finset.univ.erase target,
          (stationary.weight source : ℝ) * (generator.rate source target : ℝ) =
        (stationary.weight target : ℝ) * (generator.escapeRate target : ℝ) := by
    have hBalance := stationary.balance target
    rw [← Finset.sum_erase (s := Finset.univ) (a := target) (f := fun source ↦
      stationary.weight source * generator.rate source target) (by
        change stationary.weight target * generator.rate target target = 0
        rw [generator.rate_self, mul_zero])] at hBalance
    exact_mod_cast hBalance.symm
  rw [hIncoming]
  field_simp [(generator.uniformizationRate_pos).ne']
  ring

end FiniteStateMarkovStationaryDistribution

end FiniteMarkovProcesses.Probability
