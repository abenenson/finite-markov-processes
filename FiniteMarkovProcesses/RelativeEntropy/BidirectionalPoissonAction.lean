/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.PoissonRateDiscrimination

/-!
# Bidirectional Poisson action and activity selection

This file classifies a pair of positive directional Poisson intensities. It separates the
current/affinity entropy action from total traffic, proves the unique total-activity tilt of a
passive pair, and identifies exactly when an independently fixed comparison pair supplies an
affinely opposite action on the full positive pair fibre.

The results are source-neutral. In particular, the comparison action is not identified here as a
physical time reverse or as a frenetic path action.

## Main results

- `bidirectionalPoissonEntropyAction_eq_current_mul_affinity`: exact entropy-action formula.
- `bidirectionalPoissonActivityObjective_eq_gauge_sub_action`: full-fibre selection identity.
- `bidirectionalPoissonActivityObjective_eq_selected_iff`: literal optimizer uniqueness.
- `bidirectionalPoissonOperationalCompatibility_iff`: two-coordinate compatibility classifier.
- `bidirectionalPoissonEntropyActionMinimizer_iff`: diagonal physical-action minimizers.
- `no_fullFibre_affineEntropyActionIdentity`: driven selection cannot equal entropy action alone.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

/-- Integrated clockwise and counterclockwise Poisson intensities over one experiment.
Their strict positivity is expressed separately by `BidirectionalPoissonRates.Positive`. -/
@[ext]
structure BidirectionalPoissonRates where
  /-- Clockwise Poisson intensity integrated over the experiment. -/
  clockwise : ℝ
  /-- Counterclockwise Poisson intensity integrated over the experiment. -/
  counterclockwise : ℝ

/-- Equality of both directed intensities determines equality of bidirectional rate pairs. -/
add_decl_doc BidirectionalPoissonRates.ext

/-- Two bidirectional rate pairs are equal exactly when their clockwise and counterclockwise
intensities agree. -/
add_decl_doc BidirectionalPoissonRates.ext_iff

namespace BidirectionalPoissonRates

/-- Both directional intensities are strictly positive. -/
def Positive (rates : BidirectionalPoissonRates) : Prop :=
  0 < rates.clockwise ∧ 0 < rates.counterclockwise

/-- Expected unoriented traffic over one experiment. -/
def traffic (rates : BidirectionalPoissonRates) : ℝ :=
  rates.clockwise + rates.counterclockwise

/-- Expected oriented current over one experiment. -/
def current (rates : BidirectionalPoissonRates) : ℝ :=
  rates.clockwise - rates.counterclockwise

/-- Dimensionless directional affinity. -/
noncomputable def affinity (rates : BidirectionalPoissonRates) : ℝ :=
  Real.log (rates.clockwise / rates.counterclockwise)

/-- Positive symmetric reactivity written in exponential coordinates. -/
noncomputable def reactivity (rates : BidirectionalPoissonRates) : ℝ :=
  Real.exp ((Real.log rates.clockwise + Real.log rates.counterclockwise) / 2)

/-- Exponential-coordinate reactivity is strictly positive. -/
theorem reactivity_pos (rates : BidirectionalPoissonRates) : 0 < rates.reactivity :=
  Real.exp_pos _

/-- Reactivity paired with positive half-affinity recovers the clockwise intensity. -/
theorem reactivity_mul_exp_half_affinity_eq_clockwise
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    rates.reactivity * Real.exp (rates.affinity / 2) = rates.clockwise := by
  rw [reactivity, affinity, ← Real.exp_add,
    Real.log_div hRates.1.ne' hRates.2.ne']
  convert Real.exp_log hRates.1 using 1
  ring_nf

/-- Reactivity paired with negative half-affinity recovers the counterclockwise intensity. -/
theorem reactivity_mul_exp_neg_half_affinity_eq_counterclockwise
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    rates.reactivity * Real.exp (-rates.affinity / 2) = rates.counterclockwise := by
  rw [reactivity, affinity, ← Real.exp_add,
    Real.log_div hRates.1.ne' hRates.2.ne']
  convert Real.exp_log hRates.2 using 1
  ring_nf

end BidirectionalPoissonRates

/-- Sum of the two directional Poisson discriminations. -/
noncomputable def bidirectionalPoissonDiscrimination
    (lawRates referenceRates : BidirectionalPoissonRates) : ℝ :=
  poissonRateDiscrimination lawRates.clockwise referenceRates.clockwise +
    poissonRateDiscrimination lawRates.counterclockwise referenceRates.counterclockwise

/-- Bidirectional discrimination is nonnegative on the positive pair fibre. -/
theorem bidirectionalPoissonDiscrimination_nonneg
    {lawRates referenceRates : BidirectionalPoissonRates}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive) :
    0 ≤ bidirectionalPoissonDiscrimination lawRates referenceRates := by
  exact add_nonneg
    (poissonRateDiscrimination_nonneg hLaw.1.le hReference.1)
    (poissonRateDiscrimination_nonneg hLaw.2.le hReference.2)

/-- Positive pair discrimination vanishes exactly at literal equality. -/
theorem bidirectionalPoissonDiscrimination_eq_zero_iff
    {lawRates referenceRates : BidirectionalPoissonRates}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive) :
    bidirectionalPoissonDiscrimination lawRates referenceRates = 0 ↔
      lawRates = referenceRates := by
  have hClockwise := poissonRateDiscrimination_nonneg hLaw.1.le hReference.1
  have hCounterclockwise := poissonRateDiscrimination_nonneg hLaw.2.le hReference.2
  constructor
  · intro hZero
    have hClockwiseZero :
        poissonRateDiscrimination lawRates.clockwise referenceRates.clockwise = 0 := by
      unfold bidirectionalPoissonDiscrimination at hZero
      linarith
    have hCounterclockwiseZero :
        poissonRateDiscrimination lawRates.counterclockwise
          referenceRates.counterclockwise = 0 := by
      unfold bidirectionalPoissonDiscrimination at hZero
      linarith
    ext
    · exact (poissonRateDiscrimination_eq_zero_iff hLaw.1 hReference.1).mp hClockwiseZero
    · exact (poissonRateDiscrimination_eq_zero_iff hLaw.2 hReference.2).mp
        hCounterclockwiseZero
  · rintro rfl
    unfold bidirectionalPoissonDiscrimination
    rw [(poissonRateDiscrimination_eq_zero_iff hReference.1 hReference.1).2 rfl,
      (poissonRateDiscrimination_eq_zero_iff hReference.2 hReference.2).2 rfl, add_zero]

/-- Distinct positive pairs have strictly positive discrimination. -/
theorem bidirectionalPoissonDiscrimination_pos
    {lawRates referenceRates : BidirectionalPoissonRates}
    (hLaw : lawRates.Positive) (hReference : referenceRates.Positive)
    (hDistinct : lawRates ≠ referenceRates) :
    0 < bidirectionalPoissonDiscrimination lawRates referenceRates := by
  exact lt_of_le_of_ne
    (bidirectionalPoissonDiscrimination_nonneg hLaw hReference)
    (Ne.symm (mt (bidirectionalPoissonDiscrimination_eq_zero_iff hLaw hReference).mp hDistinct))

/-- Mean forward-versus-direction-swapped Poisson entropy action. -/
noncomputable def bidirectionalPoissonEntropyAction
    (rates : BidirectionalPoissonRates) : ℝ :=
  poissonRateDiscrimination rates.clockwise rates.counterclockwise +
    poissonRateDiscrimination rates.counterclockwise rates.clockwise

/-- The entropy action is current times affinity. -/
theorem bidirectionalPoissonEntropyAction_eq_current_mul_affinity
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    bidirectionalPoissonEntropyAction rates = rates.current * rates.affinity := by
  unfold bidirectionalPoissonEntropyAction poissonRateDiscrimination
  unfold BidirectionalPoissonRates.current BidirectionalPoissonRates.affinity
  rw [Real.log_div hRates.1.ne' hRates.2.ne',
    Real.log_div hRates.2.ne' hRates.1.ne']
  ring

/-- The bidirectional entropy action is nonnegative. -/
theorem bidirectionalPoissonEntropyAction_nonneg
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    0 ≤ bidirectionalPoissonEntropyAction rates := by
  exact add_nonneg
    (poissonRateDiscrimination_nonneg hRates.1.le hRates.2)
    (poissonRateDiscrimination_nonneg hRates.2.le hRates.1)

/-- The entropy action vanishes exactly on the detailed-balance diagonal. -/
theorem bidirectionalPoissonEntropyAction_eq_zero_iff
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    bidirectionalPoissonEntropyAction rates = 0 ↔
      rates.clockwise = rates.counterclockwise := by
  have hFirst := poissonRateDiscrimination_nonneg hRates.1.le hRates.2
  have hSecond := poissonRateDiscrimination_nonneg hRates.2.le hRates.1
  constructor
  · intro hZero
    have hFirstZero :
        poissonRateDiscrimination rates.clockwise rates.counterclockwise = 0 := by
      unfold bidirectionalPoissonEntropyAction at hZero
      linarith
    exact (poissonRateDiscrimination_eq_zero_iff hRates.1 hRates.2).mp hFirstZero
  · intro hEqual
    rw [bidirectionalPoissonEntropyAction_eq_current_mul_affinity hRates]
    simp [BidirectionalPoissonRates.current, hEqual]

/-- A positive rate pair is driven exactly when its entropy action is strictly positive. -/
theorem bidirectionalPoissonEntropyAction_pos_iff
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    0 < bidirectionalPoissonEntropyAction rates ↔
      rates.clockwise ≠ rates.counterclockwise := by
  constructor
  · intro hPositive hDiagonal
    rw [(bidirectionalPoissonEntropyAction_eq_zero_iff hRates).2 hDiagonal] at hPositive
    exact (lt_irrefl 0) hPositive
  · intro hDriven
    exact lt_of_le_of_ne
      (bidirectionalPoissonEntropyAction_nonneg hRates)
      (Ne.symm (mt (bidirectionalPoissonEntropyAction_eq_zero_iff hRates).mp hDriven))

/-- Passive-relative information for a directional pair. -/
noncomputable def bidirectionalPoissonPassiveInformation
    (baseRates controlledRates : BidirectionalPoissonRates) : ℝ :=
  -bidirectionalPoissonDiscrimination controlledRates baseRates

/-- Total expected contact activity of a directional pair. -/
def bidirectionalPoissonContactActivity (rates : BidirectionalPoissonRates) : ℝ :=
  rates.traffic

/-- Passive information minus one covector paired with total contact activity. -/
noncomputable def bidirectionalPoissonActivityObjective
    (baseRates : BidirectionalPoissonRates) (multiplier : ℝ)
    (controlledRates : BidirectionalPoissonRates) : ℝ :=
  bidirectionalPoissonPassiveInformation baseRates controlledRates -
    multiplier * bidirectionalPoissonContactActivity controlledRates

/-- Coordinatewise total-activity tilt of a passive directional pair. -/
noncomputable def selectedBidirectionalPoissonRates
    (baseRates : BidirectionalPoissonRates) (multiplier : ℝ) :
    BidirectionalPoissonRates where
  clockwise := selectedPoissonIntensity baseRates.clockwise multiplier
  counterclockwise := selectedPoissonIntensity baseRates.counterclockwise multiplier

/-- Positive passive rates give a positive selected pair. -/
theorem selectedBidirectionalPoissonRates_positive
    {baseRates : BidirectionalPoissonRates} (hBase : baseRates.Positive)
    (multiplier : ℝ) :
    (selectedBidirectionalPoissonRates baseRates multiplier).Positive := by
  exact ⟨selectedPoissonIntensity_pos hBase.1, selectedPoissonIntensity_pos hBase.2⟩

/-- The pair objective is a gauge minus discrimination from the selected pair. -/
theorem bidirectionalPoissonActivityObjective_eq_gauge_sub_action
    {baseRates controlledRates : BidirectionalPoissonRates} {multiplier : ℝ}
    (hBase : baseRates.Positive) (hControlled : controlledRates.Positive) :
    bidirectionalPoissonActivityObjective baseRates multiplier controlledRates =
      (selectedBidirectionalPoissonRates baseRates multiplier).traffic - baseRates.traffic -
        bidirectionalPoissonDiscrimination controlledRates
          (selectedBidirectionalPoissonRates baseRates multiplier) := by
  have hClockwise := poissonActivityObjective_eq_gauge_sub_discrimination
    (multiplier := multiplier) hBase.1 hControlled.1
  have hCounterclockwise := poissonActivityObjective_eq_gauge_sub_discrimination
    (multiplier := multiplier) hBase.2 hControlled.2
  unfold bidirectionalPoissonActivityObjective bidirectionalPoissonPassiveInformation
  unfold bidirectionalPoissonContactActivity bidirectionalPoissonDiscrimination
  unfold BidirectionalPoissonRates.traffic selectedBidirectionalPoissonRates
  unfold poissonActivityObjective poissonPassiveInformation poissonContactActivity at hClockwise
  unfold poissonActivityObjective poissonPassiveInformation at hCounterclockwise
  unfold poissonContactActivity at hCounterclockwise
  linarith

/-- The selected pair dominates the entire positive pair fibre. -/
theorem bidirectionalPoissonActivityObjective_le_selected
    {baseRates controlledRates : BidirectionalPoissonRates} {multiplier : ℝ}
    (hBase : baseRates.Positive) (hControlled : controlledRates.Positive) :
    bidirectionalPoissonActivityObjective baseRates multiplier controlledRates ≤
      bidirectionalPoissonActivityObjective baseRates multiplier
        (selectedBidirectionalPoissonRates baseRates multiplier) := by
  have hSelected := selectedBidirectionalPoissonRates_positive hBase multiplier
  rw [bidirectionalPoissonActivityObjective_eq_gauge_sub_action hBase hControlled,
    bidirectionalPoissonActivityObjective_eq_gauge_sub_action hBase hSelected]
  rw [(bidirectionalPoissonDiscrimination_eq_zero_iff hSelected hSelected).2 rfl, sub_zero]
  exact sub_le_self _ (bidirectionalPoissonDiscrimination_nonneg hControlled hSelected)

/-- Objective equality with the selected value holds exactly at the selected pair. -/
theorem bidirectionalPoissonActivityObjective_eq_selected_iff
    {baseRates controlledRates : BidirectionalPoissonRates} {multiplier : ℝ}
    (hBase : baseRates.Positive) (hControlled : controlledRates.Positive) :
    bidirectionalPoissonActivityObjective baseRates multiplier controlledRates =
        bidirectionalPoissonActivityObjective baseRates multiplier
          (selectedBidirectionalPoissonRates baseRates multiplier) ↔
      controlledRates = selectedBidirectionalPoissonRates baseRates multiplier := by
  have hSelected := selectedBidirectionalPoissonRates_positive hBase multiplier
  rw [bidirectionalPoissonActivityObjective_eq_gauge_sub_action hBase hControlled,
    bidirectionalPoissonActivityObjective_eq_gauge_sub_action hBase hSelected]
  rw [(bidirectionalPoissonDiscrimination_eq_zero_iff hSelected hSelected).2 rfl, sub_zero]
  constructor
  · intro hEqual
    apply (bidirectionalPoissonDiscrimination_eq_zero_iff hControlled hSelected).mp
    linarith
  · rintro rfl
    rw [(bidirectionalPoissonDiscrimination_eq_zero_iff hSelected hSelected).2 rfl]
    ring

/-- Action against an independently fixed directional comparison pair. -/
noncomputable def bidirectionalPoissonOperationalAction
    (referenceRates controlledRates : BidirectionalPoissonRates) : ℝ :=
  bidirectionalPoissonDiscrimination controlledRates referenceRates

/-- Exact affine defect between the pair objective and comparison action. -/
theorem bidirectionalPoissonActivityObjective_add_operationalAction
    {baseRates referenceRates controlledRates : BidirectionalPoissonRates}
    {multiplier : ℝ} (hBase : baseRates.Positive)
    (hReference : referenceRates.Positive) (hControlled : controlledRates.Positive) :
    bidirectionalPoissonActivityObjective baseRates multiplier controlledRates +
        bidirectionalPoissonOperationalAction referenceRates controlledRates =
      referenceRates.traffic - baseRates.traffic +
        controlledRates.clockwise *
          (Real.log (baseRates.clockwise / referenceRates.clockwise) - multiplier) +
        controlledRates.counterclockwise *
          (Real.log (baseRates.counterclockwise / referenceRates.counterclockwise) -
            multiplier) := by
  have hClockwise := poissonActivityObjective_add_operationalAction
    (multiplier := multiplier) hBase.1 hReference.1 hControlled.1
  have hCounterclockwise := poissonActivityObjective_add_operationalAction
    (multiplier := multiplier) hBase.2 hReference.2 hControlled.2
  unfold bidirectionalPoissonActivityObjective bidirectionalPoissonPassiveInformation
  unfold bidirectionalPoissonContactActivity bidirectionalPoissonOperationalAction
  unfold bidirectionalPoissonDiscrimination BidirectionalPoissonRates.traffic
  unfold poissonActivityObjective poissonPassiveInformation poissonContactActivity at hClockwise
  unfold poissonOperationalAction at hClockwise
  unfold poissonActivityObjective poissonPassiveInformation at hCounterclockwise
  unfold poissonContactActivity at hCounterclockwise
  unfold poissonOperationalAction at hCounterclockwise
  linarith

/-- Full-pair compatibility identifies both directional load slopes and the visible gauge. -/
theorem bidirectionalPoissonOperationalCompatibility_iff
    {baseRates referenceRates : BidirectionalPoissonRates} {multiplier gauge : ℝ}
    (hBase : baseRates.Positive) (hReference : referenceRates.Positive) :
    (∀ controlledRates, controlledRates.Positive →
      bidirectionalPoissonActivityObjective baseRates multiplier controlledRates =
        gauge - bidirectionalPoissonOperationalAction referenceRates controlledRates) ↔
      multiplier = Real.log (baseRates.clockwise / referenceRates.clockwise) ∧
        multiplier = Real.log
          (baseRates.counterclockwise / referenceRates.counterclockwise) ∧
        gauge = referenceRates.traffic - baseRates.traffic := by
  let oneOne : BidirectionalPoissonRates := ⟨1, 1⟩
  let twoOne : BidirectionalPoissonRates := ⟨2, 1⟩
  let oneTwo : BidirectionalPoissonRates := ⟨1, 2⟩
  have hOneOne : oneOne.Positive := by simp [oneOne, BidirectionalPoissonRates.Positive]
  have hTwoOne : twoOne.Positive := by simp [twoOne, BidirectionalPoissonRates.Positive]
  have hOneTwo : oneTwo.Positive := by simp [oneTwo, BidirectionalPoissonRates.Positive]
  constructor
  · intro h
    have hDefectOneOne := bidirectionalPoissonActivityObjective_add_operationalAction
      (multiplier := multiplier) hBase hReference hOneOne
    have hDefectTwoOne := bidirectionalPoissonActivityObjective_add_operationalAction
      (multiplier := multiplier) hBase hReference hTwoOne
    have hDefectOneTwo := bidirectionalPoissonActivityObjective_add_operationalAction
      (multiplier := multiplier) hBase hReference hOneTwo
    have hAtOneOne := h oneOne hOneOne
    have hAtTwoOne := h twoOne hTwoOne
    have hAtOneTwo := h oneTwo hOneTwo
    have hClockwise :
        Real.log (baseRates.clockwise / referenceRates.clockwise) - multiplier = 0 := by
      dsimp [oneOne, twoOne, BidirectionalPoissonRates.traffic] at hDefectOneOne hDefectTwoOne
      dsimp [oneOne, twoOne] at hAtOneOne hAtTwoOne
      linarith
    have hCounterclockwise :
        Real.log (baseRates.counterclockwise / referenceRates.counterclockwise) -
          multiplier = 0 := by
      dsimp [oneOne, oneTwo, BidirectionalPoissonRates.traffic] at hDefectOneOne hDefectOneTwo
      dsimp [oneOne, oneTwo] at hAtOneOne hAtOneTwo
      linarith
    have hGauge : gauge = referenceRates.traffic - baseRates.traffic := by
      dsimp [oneOne, BidirectionalPoissonRates.traffic] at hDefectOneOne hAtOneOne
      linarith
    exact ⟨by linarith, by linarith, hGauge⟩
  · rintro ⟨hClockwise, hCounterclockwise, hGauge⟩ controlledRates hControlled
    have hDefect := bidirectionalPoissonActivityObjective_add_operationalAction
      (multiplier := multiplier) hBase hReference hControlled
    have hEqualLogs :
        Real.log (baseRates.clockwise / referenceRates.clockwise) =
          Real.log (baseRates.counterclockwise / referenceRates.counterclockwise) :=
      hClockwise.symm.trans hCounterclockwise
    apply (eq_sub_iff_add_eq).2
    rw [hGauge]
    simpa [hClockwise, hEqualLogs] using hDefect

/-- Common-barrier loading applies the same activity tilt to both directional rates. -/
noncomputable def commonBarrierPoissonLoad
    (baseRates : BidirectionalPoissonRates) (multiplier : ℝ) :
    BidirectionalPoissonRates :=
  selectedBidirectionalPoissonRates baseRates multiplier

/-- Common-barrier loading preserves directional affinity. -/
theorem commonBarrierPoissonLoad_affinity
    (baseRates : BidirectionalPoissonRates) (multiplier : ℝ) :
    (commonBarrierPoissonLoad baseRates multiplier).affinity = baseRates.affinity := by
  unfold commonBarrierPoissonLoad selectedBidirectionalPoissonRates
  unfold BidirectionalPoissonRates.affinity selectedPoissonIntensity
  congr 1
  field_simp [Real.exp_ne_zero]

/-- Common-barrier loading is exactly the full-fibre compatible comparison. -/
theorem commonBarrierPoissonLoad_compatibility
    {baseRates : BidirectionalPoissonRates} (hBase : baseRates.Positive)
    (multiplier : ℝ) :
    ∀ controlledRates, controlledRates.Positive →
      bidirectionalPoissonActivityObjective baseRates multiplier controlledRates =
        (commonBarrierPoissonLoad baseRates multiplier).traffic - baseRates.traffic -
          bidirectionalPoissonOperationalAction
            (commonBarrierPoissonLoad baseRates multiplier) controlledRates := by
  intro controlledRates hControlled
  exact bidirectionalPoissonActivityObjective_eq_gauge_sub_action
    hBase hControlled

/-- A positive pair minimizes entropy action when it is no larger than every positive pair. -/
def IsBidirectionalPoissonEntropyActionMinimizer
    (rates : BidirectionalPoissonRates) : Prop :=
  ∀ candidate, candidate.Positive →
    bidirectionalPoissonEntropyAction rates ≤ bidirectionalPoissonEntropyAction candidate

/-- Physical entropy-action minimizers are exactly the detailed-balance diagonal. -/
theorem bidirectionalPoissonEntropyActionMinimizer_iff
    {rates : BidirectionalPoissonRates} (hRates : rates.Positive) :
    IsBidirectionalPoissonEntropyActionMinimizer rates ↔
      rates.clockwise = rates.counterclockwise := by
  constructor
  · intro hMinimizer
    let diagonal : BidirectionalPoissonRates := ⟨1, 1⟩
    have hDiagonal : diagonal.Positive := by
      simp [diagonal, BidirectionalPoissonRates.Positive]
    have hUpper := hMinimizer diagonal hDiagonal
    have hDiagonalAction : bidirectionalPoissonEntropyAction diagonal = 0 :=
      (bidirectionalPoissonEntropyAction_eq_zero_iff hDiagonal).2 rfl
    have hZero : bidirectionalPoissonEntropyAction rates = 0 := by
      rw [hDiagonalAction] at hUpper
      exact le_antisymm hUpper (bidirectionalPoissonEntropyAction_nonneg hRates)
    exact (bidirectionalPoissonEntropyAction_eq_zero_iff hRates).mp hZero
  · intro hDiagonal candidate hCandidate
    rw [(bidirectionalPoissonEntropyAction_eq_zero_iff hRates).2 hDiagonal]
    exact bidirectionalPoissonEntropyAction_nonneg hCandidate

/-- A driven passive pair remains driven after every common-barrier load. -/
theorem commonBarrierPoissonLoad_ne_diagonal
    {baseRates : BidirectionalPoissonRates}
    (hDriven : baseRates.clockwise ≠ baseRates.counterclockwise) (multiplier : ℝ) :
    (commonBarrierPoissonLoad baseRates multiplier).clockwise ≠
      (commonBarrierPoissonLoad baseRates multiplier).counterclockwise := by
  intro hEqual
  apply hDriven
  dsimp [commonBarrierPoissonLoad, selectedBidirectionalPoissonRates,
    selectedPoissonIntensity] at hEqual
  nlinarith [Real.exp_pos (-multiplier)]

/-- A driven common-barrier selected law is not an entropy-action minimizer. -/
theorem commonBarrierPoissonLoad_not_entropyActionMinimizer
    {baseRates : BidirectionalPoissonRates} (hBase : baseRates.Positive)
    (hDriven : baseRates.clockwise ≠ baseRates.counterclockwise) (multiplier : ℝ) :
    ¬ IsBidirectionalPoissonEntropyActionMinimizer
      (commonBarrierPoissonLoad baseRates multiplier) := by
  intro hMinimizer
  have hDiagonal := (bidirectionalPoissonEntropyActionMinimizer_iff
    (selectedBidirectionalPoissonRates_positive hBase multiplier)).mp hMinimizer
  exact (commonBarrierPoissonLoad_ne_diagonal hDriven multiplier) hDiagonal

/-- No full-fibre affine identity equates driven activity selection with entropy action alone. -/
theorem no_fullFibre_affineEntropyActionIdentity
    {baseRates : BidirectionalPoissonRates} (hBase : baseRates.Positive)
    (hDriven : baseRates.clockwise ≠ baseRates.counterclockwise) (multiplier : ℝ) :
    ¬ ∃ gauge, ∀ controlledRates, controlledRates.Positive →
      bidirectionalPoissonActivityObjective baseRates multiplier controlledRates =
        gauge - bidirectionalPoissonEntropyAction controlledRates := by
  rintro ⟨gauge, hIdentity⟩
  let selected := commonBarrierPoissonLoad baseRates multiplier
  let diagonal : BidirectionalPoissonRates := ⟨1, 1⟩
  have hSelected : selected.Positive := selectedBidirectionalPoissonRates_positive hBase multiplier
  have hDiagonal : diagonal.Positive := by
    simp [diagonal, BidirectionalPoissonRates.Positive]
  have hSelectedDriven : selected.clockwise ≠ selected.counterclockwise :=
    commonBarrierPoissonLoad_ne_diagonal hDriven multiplier
  have hSelectedAction : 0 < bidirectionalPoissonEntropyAction selected :=
    (bidirectionalPoissonEntropyAction_pos_iff hSelected).2 hSelectedDriven
  have hDiagonalAction : bidirectionalPoissonEntropyAction diagonal = 0 :=
    (bidirectionalPoissonEntropyAction_eq_zero_iff hDiagonal).2 rfl
  have hSelectedIdentity := hIdentity selected hSelected
  have hDiagonalIdentity := hIdentity diagonal hDiagonal
  have hOptimal := bidirectionalPoissonActivityObjective_le_selected
    (multiplier := multiplier) hBase hDiagonal
  change bidirectionalPoissonActivityObjective baseRates multiplier diagonal ≤
    bidirectionalPoissonActivityObjective baseRates multiplier selected at hOptimal
  rw [hDiagonalAction] at hDiagonalIdentity
  linarith

/-- Frozen primary pair assay: a common factor two load preserves affinity and fixes gauge `-3`. -/
theorem bidirectionalPoissonPrimaryAssay :
    commonBarrierPoissonLoad ⟨4, 2⟩ (Real.log 2) = ⟨2, 1⟩ ∧
      ∀ controlledRates, controlledRates.Positive →
        bidirectionalPoissonActivityObjective ⟨4, 2⟩ (Real.log 2) controlledRates =
          -3 - bidirectionalPoissonOperationalAction ⟨2, 1⟩ controlledRates := by
  have hBase : (⟨4, 2⟩ : BidirectionalPoissonRates).Positive := by
    norm_num [BidirectionalPoissonRates.Positive]
  have hReference : (⟨2, 1⟩ : BidirectionalPoissonRates).Positive := by
    norm_num [BidirectionalPoissonRates.Positive]
  constructor
  · ext
    · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) (by norm_num)
    · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) (by norm_num)
  · apply (bidirectionalPoissonOperationalCompatibility_iff hBase hReference).2
    constructor
    · norm_num
    constructor <;> norm_num [BidirectionalPoissonRates.traffic]

/-- Frozen held-out assay: a factor three load at different affinity fixes gauge `-8`. -/
theorem bidirectionalPoissonHeldoutAssay :
    commonBarrierPoissonLoad ⟨9, 3⟩ (Real.log 3) = ⟨3, 1⟩ ∧
      ∀ controlledRates, controlledRates.Positive →
        bidirectionalPoissonActivityObjective ⟨9, 3⟩ (Real.log 3) controlledRates =
          -8 - bidirectionalPoissonOperationalAction ⟨3, 1⟩ controlledRates := by
  have hBase : (⟨9, 3⟩ : BidirectionalPoissonRates).Positive := by
    norm_num [BidirectionalPoissonRates.Positive]
  have hReference : (⟨3, 1⟩ : BidirectionalPoissonRates).Positive := by
    norm_num [BidirectionalPoissonRates.Positive]
  constructor
  · ext
    · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) (by norm_num)
    · exact selectedPoissonIntensity_eq_reference (by norm_num) (by norm_num) (by norm_num)
  · apply (bidirectionalPoissonOperationalCompatibility_iff hBase hReference).2
    constructor
    · norm_num
    constructor <;> norm_num [BidirectionalPoissonRates.traffic]

/-- Convert physical directional rates to integrated intensities over a fixed clock. -/
def integratedBidirectionalPoissonRates
    (clockDuration : ℝ) (physicalRates : BidirectionalPoissonRates) :
    BidirectionalPoissonRates where
  clockwise := contactIntensity clockDuration physicalRates.clockwise
  counterclockwise := contactIntensity clockDuration physicalRates.counterclockwise

/-- Covariant clock and physical-rate changes preserve both integrated intensities. -/
theorem integratedBidirectionalPoissonRates_clockChange
    {scale clockDuration : ℝ} {physicalRates : BidirectionalPoissonRates}
    (hScale : scale ≠ 0) :
    integratedBidirectionalPoissonRates (scale * clockDuration)
        ⟨physicalRates.clockwise / scale, physicalRates.counterclockwise / scale⟩ =
      integratedBidirectionalPoissonRates clockDuration physicalRates := by
  ext <;> exact contactIntensity_clockChange hScale

/-- Entropy action is invariant under a covariant physical clock change. -/
theorem bidirectionalPoissonEntropyAction_clockChange
    {scale clockDuration : ℝ} {physicalRates : BidirectionalPoissonRates}
    (hScale : scale ≠ 0) :
    bidirectionalPoissonEntropyAction
        (integratedBidirectionalPoissonRates (scale * clockDuration)
          ⟨physicalRates.clockwise / scale, physicalRates.counterclockwise / scale⟩) =
      bidirectionalPoissonEntropyAction
        (integratedBidirectionalPoissonRates clockDuration physicalRates) := by
  rw [integratedBidirectionalPoissonRates_clockChange hScale]

/-- Pair comparison action is invariant under a common covariant clock change. -/
theorem bidirectionalPoissonOperationalAction_clockChange
    {scale clockDuration : ℝ}
    {referencePhysicalRates controlledPhysicalRates : BidirectionalPoissonRates}
    (hScale : scale ≠ 0) :
    bidirectionalPoissonOperationalAction
        (integratedBidirectionalPoissonRates (scale * clockDuration)
          ⟨referencePhysicalRates.clockwise / scale,
            referencePhysicalRates.counterclockwise / scale⟩)
        (integratedBidirectionalPoissonRates (scale * clockDuration)
          ⟨controlledPhysicalRates.clockwise / scale,
            controlledPhysicalRates.counterclockwise / scale⟩) =
      bidirectionalPoissonOperationalAction
        (integratedBidirectionalPoissonRates clockDuration referencePhysicalRates)
        (integratedBidirectionalPoissonRates clockDuration controlledPhysicalRates) := by
  rw [integratedBidirectionalPoissonRates_clockChange hScale,
    integratedBidirectionalPoissonRates_clockChange hScale]

/-- Pair activity selection is invariant under a common covariant clock change. -/
theorem bidirectionalPoissonActivityObjective_clockChange
    {scale clockDuration multiplier : ℝ}
    {basePhysicalRates controlledPhysicalRates : BidirectionalPoissonRates}
    (hScale : scale ≠ 0) :
    bidirectionalPoissonActivityObjective
        (integratedBidirectionalPoissonRates (scale * clockDuration)
          ⟨basePhysicalRates.clockwise / scale,
            basePhysicalRates.counterclockwise / scale⟩)
        multiplier
        (integratedBidirectionalPoissonRates (scale * clockDuration)
          ⟨controlledPhysicalRates.clockwise / scale,
            controlledPhysicalRates.counterclockwise / scale⟩) =
      bidirectionalPoissonActivityObjective
        (integratedBidirectionalPoissonRates clockDuration basePhysicalRates)
        multiplier
        (integratedBidirectionalPoissonRates clockDuration controlledPhysicalRates) := by
  rw [integratedBidirectionalPoissonRates_clockChange hScale,
    integratedBidirectionalPoissonRates_clockChange hScale]

end FiniteMarkovProcesses.InformationTheory
