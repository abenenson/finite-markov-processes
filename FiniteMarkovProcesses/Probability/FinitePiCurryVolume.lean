/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Lebesgue volume under finite dependent currying

A scalar coordinate vector indexed by a finite sigma type can equivalently be read as a finite
outer vector of inner coordinate vectors. This module proves that the canonical dependent
currying equivalence preserves Lebesgue volume exactly.

## Main Result

- `volume_measurePreserving_piCurry_real`: dependent currying of finitely many finite real
  coordinate blocks has unit Jacobian.
-/

open MeasureTheory

universe u

namespace FiniteMarkovProcesses.Probability

/-- Separate the zero fibre from all successor fibres of a sigma type indexed by `Fin (n + 1)`. -/
def finSuccSigmaEquiv {n : ℕ} (κ : Fin (n + 1) → Type u) :
    (κ 0 ⊕ ((index : Fin n) × κ index.succ)) ≃
      ((index : Fin (n + 1)) × κ index) where
  toFun
    | Sum.inl value => ⟨0, value⟩
    | Sum.inr ⟨index, value⟩ => ⟨index.succ, value⟩
  invFun pair :=
    Fin.cases (fun value ↦ Sum.inl value)
      (fun index value ↦ Sum.inr ⟨index, value⟩) pair.1 pair.2
  left_inv coordinate := by
    rcases coordinate with value | ⟨index, value⟩
    · rfl
    · rfl
  right_inv pair := by
    rcases pair with ⟨index, value⟩
    cases index using Fin.cases <;> rfl

/-- Dependent currying of finitely many finite real coordinate blocks preserves Lebesgue volume
exactly. -/
theorem volume_measurePreserving_piCurry_real {n : ℕ}
    (κ : Fin n → Type u) [∀ index, Fintype (κ index)] :
    MeasurePreserving (Equiv.piCurry fun index (_ : κ index) ↦ ℝ)
      (Measure.pi fun _ : (index : Fin n) × κ index ↦ (volume : Measure ℝ))
      (Measure.pi fun index : Fin n ↦
        Measure.pi fun _ : κ index ↦ (volume : Measure ℝ)) := by
  induction n with
  | zero =>
      let source := ((coordinate : (index : Fin 0) × κ index) → ℝ)
      let target := ((index : Fin 0) → κ index → ℝ)
      let sourceEquiv := MeasurableEquiv.ofUniqueOfUnique source Unit
      let targetEquiv := MeasurableEquiv.ofUniqueOfUnique target Unit
      have hSource : MeasurePreserving
          sourceEquiv volume volume :=
        volume_preserving_pi_empty (fun _ : (index : Fin 0) × κ index ↦ ℝ)
      have hTarget : MeasurePreserving
          targetEquiv volume volume :=
        volume_preserving_pi_empty (fun _ : Fin 0 ↦ κ _ → ℝ)
      have hComposite := hTarget.symm.comp hSource
      have hFunctions :
          (fun value ↦ targetEquiv.symm (sourceEquiv value)) =
            Equiv.piCurry (fun index (_ : κ index) ↦ ℝ) := by
        funext value
        exact Subsingleton.elim _ _
      rw [← hFunctions]
      exact hComposite
  | succ n inductionHypothesis =>
      let coordinateEquiv := finSuccSigmaEquiv κ
      let regroup :=
        (MeasurableEquiv.piCongrLeft
          (fun _ : (index : Fin (n + 1)) × κ index ↦ ℝ)
          coordinateEquiv).symm
      let split := MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ 0 ⊕ ((index : Fin n) × κ index.succ) ↦ ℝ)
      let join := MeasurableEquiv.piFinSuccAbove
        (fun index : Fin (n + 1) ↦ κ index → ℝ) 0
      let tailCurry := Equiv.piCurry fun (index : Fin n) (_ : κ index.succ) ↦ ℝ
      have hRegroup : MeasurePreserving regroup volume volume :=
        (volume_measurePreserving_piCongrLeft
          (fun _ : (index : Fin (n + 1)) × κ index ↦ ℝ)
          coordinateEquiv).symm
      have hSplit : MeasurePreserving split volume volume :=
        volume_measurePreserving_sumPiEquivProdPi
          (fun _ : κ 0 ⊕ ((index : Fin n) × κ index.succ) ↦ ℝ)
      have hHead : MeasurePreserving (id : (κ 0 → ℝ) → κ 0 → ℝ)
          (Measure.pi fun _ : κ 0 ↦ (volume : Measure ℝ))
          (Measure.pi fun _ : κ 0 ↦ (volume : Measure ℝ)) :=
        MeasurePreserving.id _
      have hTail := inductionHypothesis (fun index ↦ κ index.succ)
      have hRecurse := hHead.prod hTail
      have hJoin : MeasurePreserving join volume volume :=
        volume_preserving_piFinSuccAbove
          (fun index : Fin (n + 1) ↦ κ index → ℝ) 0
      have hComposite := hJoin.symm.comp <| hRecurse.comp <| hSplit.comp hRegroup
      have hFunctions :
          (fun values ↦ join.symm
            (Prod.map id tailCurry (split (regroup values)))) =
            Equiv.piCurry (fun index (_ : κ index) ↦ ℝ) := by
        funext values index
        refine Fin.cases ?_ (fun previous ↦ ?_) index
        · funext localIndex
          rw [show (join.symm :
              ((κ 0 → ℝ) × ((index : Fin n) → κ index.succ → ℝ)) →
                (index : Fin (n + 1)) → κ index → ℝ) =
              Fin.insertNthEquiv (fun index : Fin (n + 1) ↦ κ index → ℝ) 0 by
            exact MeasurableEquiv.piFinSuccAbove_symm_apply _ _]
          rw [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same]
          change (regroup values) (Sum.inl localIndex) = values ⟨0, localIndex⟩
          rw [show regroup =
              (MeasurableEquiv.piCongrLeft
                (fun _ : (index : Fin (n + 1)) × κ index ↦ ℝ)
                coordinateEquiv).symm by rfl]
          change values (coordinateEquiv (Sum.inl localIndex)) = values ⟨0, localIndex⟩
          rfl
        · funext localIndex
          rw [show (join.symm :
              ((κ 0 → ℝ) × ((index : Fin n) → κ index.succ → ℝ)) →
                (index : Fin (n + 1)) → κ index → ℝ) =
              Fin.insertNthEquiv (fun index : Fin (n + 1) ↦ κ index → ℝ) 0 by
            exact MeasurableEquiv.piFinSuccAbove_symm_apply _ _]
          change (Fin.insertNthEquiv
              (fun index : Fin (n + 1) ↦ κ index → ℝ) 0
                (Prod.map id tailCurry (split (regroup values))))
              ((0 : Fin (n + 1)).succAbove previous) localIndex = _
          rw [Fin.insertNthEquiv_apply, Fin.insertNth_apply_succAbove]
          change (regroup values) (Sum.inr ⟨previous, localIndex⟩) =
            values ⟨previous.succ, localIndex⟩
          rw [show regroup =
              (MeasurableEquiv.piCongrLeft
                (fun _ : (index : Fin (n + 1)) × κ index ↦ ℝ)
                coordinateEquiv).symm by rfl]
          change values (coordinateEquiv (Sum.inr ⟨previous, localIndex⟩)) =
            values ⟨previous.succ, localIndex⟩
          rfl
      rw [← hFunctions]
      exact hComposite

end FiniteMarkovProcesses.Probability
