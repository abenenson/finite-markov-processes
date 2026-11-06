/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import FiniteMarkovProcesses.MeasureTheory.Measure.MapWithDensity

/-!
# Densities of finite product measures

This module identifies a finite product of coordinatewise density measures with the product base
measure weighted by the pointwise product density. The proof transports through the measurable
head--tail equivalence and iterates the binary product-density identity.

## Main Result

- `Measure.pi_withDensity_fin`: finite products commute with coordinatewise densities.
- `Measure.map_snd_restrict_eq_withDensity_fibre`: forgetting the first coordinate of a
  restricted product measure weights the second marginal by exact fibre mass.
- `Measure.map_snd_withDensity_eq_withDensity_lintegral`: forgetting the first coordinate of a
  weighted product measure integrates the complete density over the first-coordinate fibre.
- `Measure.map_snd_restrict_withDensity_eq_withDensity_setLIntegral`: the corresponding exact
  fibre integral when the product carrier is restricted first.
- `Measure.map_snd_restrict_terminalIci`: integrating a terminal threshold produces its survival
  density on the retained coordinates.
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace MeasureTheory.Measure

/-- A finite product of coordinatewise density measures is the product base measure weighted by
the pointwise product density. -/
theorem pi_withDensity_fin
    {n : ℕ} {X : Fin n → Type u} {mX : ∀ i, MeasurableSpace (X i)}
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (density : ∀ i, X i → ℝ≥0∞) (hDensity : ∀ i, Measurable (density i))
    [∀ i, SigmaFinite ((μ i).withDensity (density i))] :
    Measure.pi (fun i => (μ i).withDensity (density i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, density i (x i)) := by
  induction n with
  | zero =>
      have hProduct :
          (fun x : (i : Fin 0) → X i => ∏ i : Fin 0, density i (x i)) = 1 := by
        funext x
        simp
      rw [hProduct, withDensity_one]
      rw [Measure.pi_of_empty (fun i => (μ i).withDensity (density i))]
      rw [Measure.pi_of_empty μ]
  | succ n inductionHypothesis =>
      let split := MeasurableEquiv.piFinSuccAbove X (0 : Fin (n + 1))
      apply split.map_measurableEquiv_injective
      rw [(measurePreserving_piFinSuccAbove
        (fun i => (μ i).withDensity (density i)) 0).map_eq]
      rw [inductionHypothesis (fun i => μ (Fin.succAbove 0 i))
        (fun i => density (Fin.succAbove 0 i))
        (fun i => hDensity (Fin.succAbove 0 i))]
      let tailDensity := fun x : (i : Fin n) → X (Fin.succAbove 0 i) =>
        ∏ i : Fin n, density (Fin.succAbove 0 i) (x i)
      have hTailDensity : Measurable tailDensity := by
        dsimp [tailDensity]
        fun_prop
      rw [prod_withDensity (hDensity 0) hTailDensity]
      let pairDensity := fun pair : X 0 × ((i : Fin n) → X (Fin.succAbove 0 i)) =>
        density 0 pair.1 * tailDensity pair.2
      have hPairDensity : Measurable pairDensity := by
        dsimp [pairDensity]
        fun_prop
      have hGlobalDensity :
          (fun x : (i : Fin (n + 1)) → X i => ∏ i, density i (x i)) =
            pairDensity ∘ split := by
        funext x
        dsimp [pairDensity, tailDensity, split, MeasurableEquiv.piFinSuccAbove]
        rw [Fin.prod_univ_succ]
        congr 1
      rw [hGlobalDensity]
      rw [Measure.map_withDensity_comp (Measure.pi μ) split.measurable
        pairDensity hPairDensity]
      rw [(measurePreserving_piFinSuccAbove μ 0).map_eq]

/-- Forgetting the first coordinate of a product measure restricted to a measurable set weights
the second marginal by the measure of the corresponding first-coordinate fibre. -/
theorem map_snd_restrict_eq_withDensity_fibre
    {A X : Type u} [MeasurableSpace A] [MeasurableSpace X]
    (first : Measure A) (second : Measure X) [SFinite first] [SFinite second]
    (fibre : Set (A × X)) (hFibre : MeasurableSet fibre) :
    Measure.map Prod.snd ((first.prod second).restrict fibre) =
      second.withDensity fun x ↦ first ((fun a ↦ (a, x)) ⁻¹' fibre) := by
  have hDensity : Measurable fun x ↦ first ((fun a ↦ (a, x)) ⁻¹' fibre) :=
    measurable_measure_prodMk_right hFibre
  ext event hEvent
  rw [Measure.map_apply measurable_snd hEvent]
  rw [Measure.restrict_apply (hEvent.preimage measurable_snd)]
  rw [Measure.prod_apply_symm ((hEvent.preimage measurable_snd).inter hFibre)]
  rw [withDensity_apply _ hEvent]
  rw [← lintegral_indicator hEvent]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ event
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext a
    simp [hx]
  · rw [Set.indicator_of_notMem hx]
    have hEmpty :
        (fun a ↦ (a, x)) ⁻¹' (Prod.snd ⁻¹' event ∩ fibre) = ∅ := by
      ext a
      simp [hx]
    rw [hEmpty, measure_empty]

/-- Forgetting the first coordinate of a weighted product measure weights the second marginal by
the exact first-coordinate integral of the complete density. -/
theorem map_snd_withDensity_eq_withDensity_lintegral
    {A X : Type u} [MeasurableSpace A] [MeasurableSpace X]
    (first : Measure A) (second : Measure X) [SFinite first] [SFinite second]
    (density : A × X → ℝ≥0∞) (hDensity : Measurable density) :
    Measure.map Prod.snd ((first.prod second).withDensity density) =
      second.withDensity fun x ↦ ∫⁻ a, density (a, x) ∂first := by
  have hMarginalDensity : Measurable fun x ↦ ∫⁻ a, density (a, x) ∂first :=
    hDensity.lintegral_prod_left'
  ext event hEvent
  rw [Measure.map_apply measurable_snd hEvent]
  rw [withDensity_apply _ (hEvent.preimage measurable_snd)]
  rw [withDensity_apply _ hEvent]
  rw [← lintegral_indicator (hEvent.preimage measurable_snd)]
  rw [← lintegral_indicator hEvent]
  rw [lintegral_prod_symm' _
    (hDensity.indicator (hEvent.preimage measurable_snd))]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ event
  · rw [Set.indicator_of_mem hx]
    apply lintegral_congr
    intro a
    rw [Set.indicator_of_mem]
    exact hx
  · rw [Set.indicator_of_notMem hx]
    have hOutside (a : A) : (a, x) ∉ Prod.snd ⁻¹' event := hx
    simp_rw [Set.indicator_of_notMem (hOutside _)]
    exact lintegral_zero

/-- Forgetting the first coordinate after restricting and weighting a product measure gives the
exact set integral of the density over each first-coordinate fibre. -/
theorem map_snd_restrict_withDensity_eq_withDensity_setLIntegral
    {A X : Type u} [MeasurableSpace A] [MeasurableSpace X]
    (first : Measure A) (second : Measure X) [SFinite first] [SFinite second]
    (fibre : Set (A × X)) (hFibre : MeasurableSet fibre)
    (density : A × X → ℝ≥0∞) (hDensity : Measurable density) :
    Measure.map Prod.snd (((first.prod second).restrict fibre).withDensity density) =
      second.withDensity fun x ↦
        ∫⁻ a in (fun a ↦ (a, x)) ⁻¹' fibre, density (a, x) ∂first := by
  rw [← withDensity_indicator hFibre]
  rw [map_snd_withDensity_eq_withDensity_lintegral first second
    (fibre.indicator density) (hDensity.indicator hFibre)]
  congr 1
  funext x
  rw [← lintegral_indicator]
  · apply lintegral_congr
    intro a
    rfl
  · exact measurable_prodMk_right hFibre

/-- Restricting a product law to a state-dependent terminal upper-tail event and then forgetting
the terminal coordinate weights the retained base measure by the terminal survival function. -/
theorem map_snd_restrict_terminalIci
    {X : Type u} [MeasurableSpace X]
    (terminal : Measure ℝ) (base : Measure X) [SFinite terminal] [SFinite base]
    (domain : Set X) (hDomain : MeasurableSet domain)
    (remaining : X → ℝ) (hRemaining : Measurable remaining)
    (survival : X → ℝ≥0∞)
    (hSurvival : ∀ x ∈ domain,
      terminal (Set.Ici (remaining x)) = survival x) :
    Measure.map Prod.snd
        ((terminal.prod base).restrict
          {pair | pair.2 ∈ domain ∧ remaining pair.2 ≤ pair.1}) =
      (base.restrict domain).withDensity survival := by
  have hCrossing : MeasurableSet
      {pair : ℝ × X | pair.2 ∈ domain ∧ remaining pair.2 ≤ pair.1} :=
    (hDomain.preimage measurable_snd).inter
      (measurableSet_le (hRemaining.comp measurable_snd) measurable_fst)
  ext event hEvent
  rw [Measure.map_apply measurable_snd hEvent]
  rw [Measure.restrict_apply (hEvent.preimage measurable_snd)]
  rw [Measure.prod_apply_symm ((hEvent.preimage measurable_snd).inter hCrossing)]
  have hSection (x : X) :
      terminal ((fun wait => (wait, x)) ⁻¹'
          (Prod.snd ⁻¹' event ∩
            {pair : ℝ × X | pair.2 ∈ domain ∧ remaining pair.2 ≤ pair.1})) =
        Set.indicator (event ∩ domain) survival x := by
    by_cases hEventX : x ∈ event
    · by_cases hDomainX : x ∈ domain
      · have hEventDomain : x ∈ event ∩ domain := ⟨hEventX, hDomainX⟩
        rw [Set.indicator_of_mem hEventDomain]
        have hSet :
            (fun wait => (wait, x)) ⁻¹'
                (Prod.snd ⁻¹' event ∩
                  {pair : ℝ × X | pair.2 ∈ domain ∧ remaining pair.2 ≤ pair.1}) =
              Set.Ici (remaining x) := by
          ext wait
          simp [hEventX, hDomainX]
        rw [hSet, hSurvival x hDomainX]
      · rw [Set.indicator_of_notMem (fun h => hDomainX h.2)]
        simp [hDomainX]
    · rw [Set.indicator_of_notMem (fun h => hEventX h.1)]
      have hEmpty :
          (fun wait => (wait, x)) ⁻¹'
              (Prod.snd ⁻¹' event ∩
                {pair : ℝ × X | pair.2 ∈ domain ∧ remaining pair.2 ≤ pair.1}) = ∅ := by
        ext wait
        simp [hEventX]
      rw [hEmpty, measure_empty]
  simp_rw [hSection]
  rw [withDensity_apply survival hEvent]
  rw [← lintegral_indicator hEvent]
  rw [← lintegral_indicator hDomain]
  apply lintegral_congr
  intro x
  by_cases hEventX : x ∈ event <;> by_cases hDomainX : x ∈ domain <;>
    simp [Set.indicator, hEventX, hDomainX]

end MeasureTheory.Measure
