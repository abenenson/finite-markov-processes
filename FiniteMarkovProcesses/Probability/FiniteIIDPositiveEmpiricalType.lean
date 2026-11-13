/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.DomMulAct
public import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensity

/-!
# Count types of positive finite IID samples

This module packages the integer count vector of a nonempty finite sample.  The carrier records
the exact total count and bounds every coordinate by the sample size.  It therefore gives the
polynomial finite type space used by method-of-types estimates, while retaining an exact map to
the ordinary finite probability simplex.

No probability estimate or asymptotic large-deviation statement is asserted here.

## Main declarations

- `FiniteIIDPositiveEmpiricalType`: bounded integer count vector of total positive sample size.
- `finiteIIDPositiveSampleEmpiricalType`: exact type of a sample word.
- `FiniteIIDPositiveEmpiricalType.representative`: canonical sample word realizing a count type.
- `FiniteIIDPositiveEmpiricalType.probabilityMassFunction`: normalized law owned by a count type.
- `finiteIIDPositiveSampleEmpiricalType_fiber_card`: exact multinomial fibre cardinal.
- `FiniteIIDPositiveEmpiricalType.probabilityDensity`: associated simplex point.
- `card_finiteIIDPositiveEmpiricalType_le`: polynomial ambient cardinal bound.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators NNReal

open FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Bounded integer count vector of a sample with `successorIndex + 1` observations.  Each count
lies in `Fin (successorIndex + 2)`, so it is at most the sample size, and the counts sum exactly to
that size. -/
structure FiniteIIDPositiveEmpiricalType (State : Type u) [Fintype State]
    (successorIndex : ℕ) where
  /-- Count assigned to each state. -/
  count : State → Fin (successorIndex + 2)
  /-- The state counts exhaust the positive sample. -/
  sum_count : ∑ state, (count state : ℕ) = successorIndex + 1

namespace FiniteIIDPositiveEmpiricalType

variable {successorIndex : ℕ}

omit [DecidableEq State] in
/-- Empirical types are equal exactly when all state counts agree. -/
@[ext]
theorem ext {first second : FiniteIIDPositiveEmpiricalType State successorIndex}
    (hCount : ∀ state, first.count state = second.count state) :
    first = second := by
  cases first
  cases second
  simp only [mk.injEq]
  funext state
  exact hCount state

omit [DecidableEq State] in
/-- Exact finite enumeration inherited from the bounded coordinate-count family. -/
noncomputable instance instFintype :
    Fintype (FiniteIIDPositiveEmpiricalType State successorIndex) :=
  Fintype.ofInjective FiniteIIDPositiveEmpiricalType.count fun _first _second hCount =>
    ext fun state => congrFun hCount state

/-- The probability simplex point associated with a positive empirical count type. -/
def probabilityDensity
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    FiniteStateProbabilityDensity State where
  weight state :=
    (empiricalType.count state : NNReal) / (successorIndex + 1 : NNReal)
  sum_weight := by
    rw [← Finset.sum_div]
    have hSum :
        ∑ state, (empiricalType.count state : NNReal) =
          (successorIndex + 1 : NNReal) := by
      exact_mod_cast empiricalType.sum_count
    rw [hSum]
    simp

omit [DecidableEq State] in
/-- The simplex coordinate of one empirical count type is its normalized integer count. -/
@[simp]
theorem probabilityDensity_weight
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (state : State) :
    empiricalType.probabilityDensity.weight state =
      (empiricalType.count state : NNReal) / (successorIndex + 1 : NNReal) :=
  rfl

/-- The probability mass function obtained by normalizing an empirical type's integer counts.
This is the prospective law under which the type itself is a multinomial mode. -/
def probabilityMassFunction
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) : PMF State :=
  empiricalType.probabilityDensity.probabilityMassFunction

omit [DecidableEq State] in
/-- The mass of a state under an empirical type's normalized law is its integer count divided by
the positive sample size. -/
@[simp]
theorem probabilityMassFunction_apply
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (state : State) :
    empiricalType.probabilityMassFunction state =
      (empiricalType.count state : ENNReal) / (successorIndex + 1 : ENNReal) := by
  rw [probabilityMassFunction,
    FiniteStateProbabilityDensity.probabilityMassFunction_apply,
    probabilityDensity_weight, ENNReal.coe_div (by positivity)]
  simp

/-- Symmetric word having exactly the counts specified by an empirical type. -/
def symmetricWord
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    Sym State (successorIndex + 1) :=
  (Sym.equivNatSumOfFintype State (successorIndex + 1)).symm
    ⟨fun state => empiricalType.count state, empiricalType.sum_count⟩

/-- A vector representative of the symmetric word specified by an empirical type. -/
def representativeVector
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    List.Vector State (successorIndex + 1) :=
  ⟨(empiricalType.symmetricWord : Multiset State).toList, by
    rw [Multiset.length_toList]
    exact empiricalType.symmetricWord.2⟩

/-- Canonical positive sample word realizing an empirical type.  The choice of word order carries
no probabilistic content; it only witnesses nonemptiness of the exact count fibre. -/
def representative
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    Fin (successorIndex + 1) → State :=
  empiricalType.representativeVector.get

/-- The canonical representative realizes every specified state count exactly. -/
theorem stateCount_representative
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex)
    (state : State) :
    finiteIIDPositiveSampleStateCount successorIndex
      empiricalType.representative state = empiricalType.count state := by
  unfold finiteIIDPositiveSampleStateCount representative
  rw [Fin.card_filter_univ_eq_vector_get_eq_count]
  change (empiricalType.symmetricWord : Multiset State).toList.count state =
    empiricalType.count state
  rw [← Multiset.coe_count, Multiset.coe_toList]
  rw [← Sym.coe_equivNatSumOfFintype_apply_apply State (successorIndex + 1)
    empiricalType.symmetricWord state]
  simp [symmetricWord]

end FiniteIIDPositiveEmpiricalType

/-- Exact empirical count type of one positive finite sample word. -/
def finiteIIDPositiveSampleEmpiricalType
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State) :
    FiniteIIDPositiveEmpiricalType State successorIndex where
  count state :=
    ⟨finiteIIDPositiveSampleStateCount successorIndex sample state, by
      have hCount :
          finiteIIDPositiveSampleStateCount successorIndex sample state ≤
            successorIndex + 1 := by
        unfold finiteIIDPositiveSampleStateCount
        simpa using Finset.card_le_card
          (Finset.filter_subset (fun replica => sample replica = state) Finset.univ)
      omega⟩
  sum_count := sum_finiteIIDPositiveSampleStateCount successorIndex sample

/-- Passing through the exact count type recovers the original empirical simplex observation. -/
theorem finiteIIDPositiveSampleEmpiricalType_probabilityDensity
    (successorIndex : ℕ) (sample : Fin (successorIndex + 1) → State) :
    (finiteIIDPositiveSampleEmpiricalType successorIndex sample).probabilityDensity =
      finiteIIDEmpiricalProbabilityDensity successorIndex sample := by
  ext state
  rfl

/-- Taking the exact empirical type of its canonical word returns the original count type. -/
@[simp]
theorem finiteIIDPositiveSampleEmpiricalType_representative
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    finiteIIDPositiveSampleEmpiricalType successorIndex empiricalType.representative =
      empiricalType := by
  ext state
  exact empiricalType.stateCount_representative state

omit [Fintype State] in
/-- A permutation of sample coordinates preserves every state count. -/
theorem finiteIIDPositiveSampleStateCount_domPermutation
    (sample : Fin (successorIndex + 1) → State)
    (permutation : (Equiv.Perm (Fin (successorIndex + 1)))ᵈᵐᵃ)
    (state : State) :
    finiteIIDPositiveSampleStateCount successorIndex
        (permutation • sample) state =
      finiteIIDPositiveSampleStateCount successorIndex sample state := by
  unfold finiteIIDPositiveSampleStateCount
  let indexEquivalence : Equiv.Perm (Fin (successorIndex + 1)) :=
    DomMulAct.mk.symm permutation
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv indexEquivalence fun _index => by rfl)

/-- Permuting sample coordinates preserves the complete empirical count type. -/
theorem finiteIIDPositiveSampleEmpiricalType_domPermutation
    (sample : Fin (successorIndex + 1) → State)
    (permutation : (Equiv.Perm (Fin (successorIndex + 1)))ᵈᵐᵃ) :
    finiteIIDPositiveSampleEmpiricalType successorIndex (permutation • sample) =
      finiteIIDPositiveSampleEmpiricalType successorIndex sample := by
  ext state
  exact finiteIIDPositiveSampleStateCount_domPermutation sample permutation state

omit [Fintype State] in
/-- Any two positive finite sample words with the same state counts differ only by a permutation
of sample coordinates. -/
theorem exists_domPermutation_smul_eq_of_stateCount_eq
    (first second : Fin (successorIndex + 1) → State)
    (hCount : ∀ state,
      finiteIIDPositiveSampleStateCount successorIndex first state =
        finiteIIDPositiveSampleStateCount successorIndex second state) :
    ∃ permutation : (Equiv.Perm (Fin (successorIndex + 1)))ᵈᵐᵃ,
      permutation • first = second := by
  let fibreEquivalence (state : State) :
      {index // first index = state} ≃ {index // second index = state} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact hCount state)
  let indexEquivalence : Equiv.Perm (Fin (successorIndex + 1)) :=
    Equiv.ofFiberEquiv fibreEquivalence
  have hMap (index : Fin (successorIndex + 1)) :
      second (indexEquivalence index) = first index :=
    Equiv.ofFiberEquiv_map fibreEquivalence index
  refine ⟨DomMulAct.mk indexEquivalence.symm, ?_⟩
  have hAction :
      DomMulAct.mk indexEquivalence.symm • first =
        first ∘ indexEquivalence.symm := rfl
  rw [hAction]
  funext index
  simpa using (hMap (indexEquivalence.symm index)).symm

/-- The exact word fibre of one empirical count type is one orbit under coordinate
permutations. -/
theorem finiteIIDPositiveSampleEmpiricalType_fiber_eq_orbit
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    {sample | finiteIIDPositiveSampleEmpiricalType successorIndex sample = empiricalType} =
      MulAction.orbit (Equiv.Perm (Fin (successorIndex + 1)))ᵈᵐᵃ
        empiricalType.representative := by
  ext sample
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro hType
    apply exists_domPermutation_smul_eq_of_stateCount_eq
    intro state
    have hCoordinate := congrArg
      (fun candidate : FiniteIIDPositiveEmpiricalType State successorIndex =>
        (candidate.count state : ℕ)) hType
    simpa [finiteIIDPositiveSampleEmpiricalType] using
      (hCoordinate.trans (empiricalType.stateCount_representative state).symm).symm
  · rintro ⟨permutation, rfl⟩
    change finiteIIDPositiveSampleEmpiricalType successorIndex
      (permutation • empiricalType.representative) = empiricalType
    rw [finiteIIDPositiveSampleEmpiricalType_domPermutation,
      finiteIIDPositiveSampleEmpiricalType_representative]

/-- The exact word fibre of an empirical count type has its multinomial cardinality.  The proof
identifies the fibre with one domain-permutation orbit and then applies orbit--stabilizer; no word
enumeration or asymptotic approximation enters. -/
theorem finiteIIDPositiveSampleEmpiricalType_fiber_card
    (empiricalType : FiniteIIDPositiveEmpiricalType State successorIndex) :
    Nat.card {sample : Fin (successorIndex + 1) → State //
      finiteIIDPositiveSampleEmpiricalType successorIndex sample = empiricalType} =
      Nat.multinomial Finset.univ
        (fun state => (empiricalType.count state : ℕ)) := by
  classical
  let permutationGroup :=
    (Equiv.Perm (Fin (successorIndex + 1)))ᵈᵐᵃ
  let representative := empiricalType.representative
  let stabilizerEquivalence :
      MulAction.stabilizer permutationGroup representative ≃
        {permutation : Equiv.Perm (Fin (successorIndex + 1)) //
          representative ∘ permutation = representative} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm
      (fun _ => DomMulAct.mem_stabilizer_iff)
  let : Fintype permutationGroup :=
    Fintype.ofEquiv (Equiv.Perm (Fin (successorIndex + 1))) DomMulAct.mk
  let : Fintype (MulAction.orbit permutationGroup representative) :=
    Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer permutationGroup representative) :=
    Fintype.ofEquiv _ stabilizerEquivalence.symm
  have hFiberOrbit :
      Nat.card {sample : Fin (successorIndex + 1) → State //
          finiteIIDPositiveSampleEmpiricalType successorIndex sample = empiricalType} =
        Fintype.card (MulAction.orbit permutationGroup representative) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Set.equivOfEq
      (finiteIIDPositiveSampleEmpiricalType_fiber_eq_orbit empiricalType))
  rw [hFiberOrbit]
  have hStabilizer :
      Fintype.card (MulAction.stabilizer permutationGroup representative) =
        ∏ state, Nat.factorial (empiricalType.count state) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr stabilizerEquivalence,
      Nat.card_eq_fintype_card, DomMulAct.stabilizer_card representative]
    apply Finset.prod_congr rfl
    intro state _hState
    congr 1
    rw [Fintype.card_subtype]
    exact empiricalType.stateCount_representative state
  have hGroupCard :
      Fintype.card permutationGroup = Nat.factorial (successorIndex + 1) := by
    exact (Fintype.card_congr DomMulAct.mk).symm.trans
      (Fintype.card_perm.trans
        (congrArg Nat.factorial (Fintype.card_fin (successorIndex + 1))))
  have hOrbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      permutationGroup representative
  have hMultinomial := Nat.multinomial_spec Finset.univ
    (fun state => (empiricalType.count state : ℕ))
  rw [hStabilizer, hGroupCard] at hOrbit
  rw [empiricalType.sum_count] at hMultinomial
  apply Nat.eq_of_mul_eq_mul_left (by positivity :
    0 < ∏ state, Nat.factorial (empiricalType.count state))
  calc
    (∏ state, Nat.factorial (empiricalType.count state)) *
        Fintype.card (MulAction.orbit permutationGroup representative) =
      Fintype.card (MulAction.orbit permutationGroup representative) *
        ∏ state, Nat.factorial (empiricalType.count state) := Nat.mul_comm _ _
    _ = Nat.factorial (successorIndex + 1) := hOrbit
    _ = (∏ state, Nat.factorial (empiricalType.count state)) *
        Nat.multinomial Finset.univ
          (fun state => (empiricalType.count state : ℕ)) := hMultinomial.symm

/-- The number of exact positive-sample count types is bounded by the full bounded-count function
space, hence by `(successorIndex + 2) ^ |State|`. -/
theorem card_finiteIIDPositiveEmpiricalType_le (successorIndex : ℕ) :
    Nat.card (FiniteIIDPositiveEmpiricalType State successorIndex) ≤
      (successorIndex + 2) ^ Fintype.card State := by
  let countEmbedding : FiniteIIDPositiveEmpiricalType State successorIndex →
      State → Fin (successorIndex + 2) :=
    FiniteIIDPositiveEmpiricalType.count
  have hInjective : Function.Injective countEmbedding := by
    intro first second hCount
    exact FiniteIIDPositiveEmpiricalType.ext fun state => congrFun hCount state
  simpa [countEmbedding, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective countEmbedding hInjective

end

end FiniteMarkovProcesses.Probability

attribute [inherit_doc FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalType.ext]
  FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalType.ext_iff
