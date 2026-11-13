/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Projections of Ionescu--Tulcea trajectories

This module develops transport tools for recursively generated probability laws.
It first proves that two finite measures on a countable trajectory space agree when every finite
initial-segment marginal agrees. It then proves the measure--kernel composition-product
naturality needed to transport a finite recursive prefix through coordinatewise measurable maps.

These results isolate measure-theoretic infrastructure from any particular Markov generator.

## Main Results

- `Measure.eq_of_map_frestrictLe_eq`: equality from all finite initial-segment marginals.
- `Measure.map_compProd_of_map_kernel`: simultaneous transport of a source measure and its
  conditional kernel.
- `map_ionescuTulceaTrajectoryMeasure`: coordinatewise one-step transport determines the full
  infinite trajectory pushforward.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Preorder

universe u v w x

namespace Measure

/-- Two finite measures on a countable dependent trajectory space are equal when all their
finite initial-segment marginals are equal. -/
theorem eq_of_map_frestrictLe_eq
    {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    (measure reference : Measure (∀ n, X n))
    [IsFiniteMeasure measure] [_unusedReferenceFinite : IsFiniteMeasure reference]
    (hPrefix : ∀ n,
      Measure.map (frestrictLe n) measure =
        Measure.map (frestrictLe n) reference) :
    measure = reference := by
  let marginals : (n : ℕ) → Measure ((i : Finset.Iic n) → X i) :=
    fun n ↦ Measure.map (frestrictLe n) measure
  have hMarginals (first second : ℕ) (hFirstSecond : first ≤ second) :
      Measure.map (frestrictLe₂ hFirstSecond) (marginals second) =
        marginals first := by
    unfold marginals
    rw [Measure.map_map (measurable_frestrictLe₂ hFirstSecond)
      (measurable_frestrictLe second)]
    rfl
  let family := inducedFamily marginals
  have hFamily : IsProjectiveMeasureFamily family := by
    unfold family
    exact isProjectiveMeasureFamily_inducedFamily marginals hMarginals
  have hMeasure : IsProjectiveLimit measure family := by
    apply (isProjectiveLimit_nat_iff hFamily measure).2
    intro n
    unfold family
    rw [inducedFamily_Iic]
  have hReference : IsProjectiveLimit reference family := by
    apply (isProjectiveLimit_nat_iff hFamily reference).2
    intro n
    unfold family
    rw [inducedFamily_Iic]
    exact (hPrefix n).symm
  exact hMeasure.unique hReference

/-- Simultaneously mapping a source measure and every row of its conditional kernel maps their
composition product coordinatewise. -/
theorem map_compProd_of_map_kernel
    {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (measure : Measure A) [SFinite measure]
    (kernel : Kernel A B) [IsSFiniteKernel kernel]
    (targetKernel : Kernel C D) [IsSFiniteKernel targetKernel]
    (sourceMap : A → C) (targetMap : B → D)
    (hSourceMap : Measurable sourceMap) (hTargetMap : Measurable targetMap)
    (hKernel : ∀ source,
      Measure.map targetMap (kernel source) = targetKernel (sourceMap source)) :
    Measure.map (Prod.map sourceMap targetMap) (measure ⊗ₘ kernel) =
      Measure.map sourceMap measure ⊗ₘ targetKernel := by
  ext event hEvent
  rw [Measure.map_apply (hSourceMap.prodMap hTargetMap) hEvent]
  rw [Measure.compProd_apply (hEvent.preimage (hSourceMap.prodMap hTargetMap))]
  rw [Measure.compProd_apply hEvent]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hEvent) hSourceMap]
  apply lintegral_congr
  intro source
  have hSection :
      Prod.mk source ⁻¹' (Prod.map sourceMap targetMap ⁻¹' event) =
        targetMap ⁻¹' (Prod.mk (sourceMap source) ⁻¹' event) := by
    rfl
  rw [hSection]
  rw [← Measure.map_apply hTargetMap (hEvent.preimage measurable_prodMk_left)]
  rw [hKernel source]

end Measure

/-- Apply one function coordinatewise to a finite initial trajectory. -/
def finiteTrajectoryCoordinateMap
    {A : Type u} {B : Type v} (map : A → B) (n : ℕ) :
    ((i : Finset.Iic n) → A) → ((i : Finset.Iic n) → B) :=
  fun trajectory i ↦ map (trajectory i)

/-- A measurable coordinate map induces a measurable map on every finite trajectory. -/
theorem measurable_finiteTrajectoryCoordinateMap
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (map : A → B) (hMap : Measurable map) (n : ℕ) :
    Measurable (finiteTrajectoryCoordinateMap map n) := by
  apply Measurable.of_eval
  intro i
  exact hMap.comp (measurable_pi_apply i)

/-- Append one coordinate to an `Iic`-indexed finite trajectory. -/
def appendIicTrajectory
    {A : Type u} [MeasurableSpace A] (n : ℕ) :
    ((i : Finset.Iic n) → A) × A → ((i : Finset.Iic (n + 1)) → A) :=
  fun pair ↦
    IicProdIoc (X := fun _ : ℕ ↦ A) n (n + 1)
      (pair.1, MeasurableEquiv.piSingleton
        (X := fun _ : ℕ ↦ A) n pair.2)

/-- Appending one coordinate to a finite trajectory is measurable. -/
theorem measurable_appendIicTrajectory
    {A : Type u} [MeasurableSpace A] (n : ℕ) :
    Measurable (appendIicTrajectory (A := A) n) := by
  exact measurable_IicProdIoc.comp <|
    measurable_fst.prodMk <|
      (MeasurableEquiv.piSingleton
        (X := fun _ : ℕ ↦ A) n).measurable.comp measurable_snd

/-- Coordinatewise mapping commutes with finite-trajectory append. -/
theorem finiteTrajectoryCoordinateMap_comp_appendIicTrajectory
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (map : A → B) (n : ℕ) :
    finiteTrajectoryCoordinateMap map (n + 1) ∘ appendIicTrajectory (A := A) n =
      appendIicTrajectory (A := B) n ∘
        Prod.map (finiteTrajectoryCoordinateMap map n) map := by
  funext pair
  funext index
  simp only [Function.comp_apply, finiteTrajectoryCoordinateMap,
    appendIicTrajectory, Prod.map, IicProdIoc_def]
  split_ifs with h
  · rfl
  · have hLe : index.1 ≤ n + 1 := Finset.mem_Iic.mp index.2
    have hIndex : index.1 = n + 1 := by omega
    simp [hIndex, MeasurableEquiv.piSingleton]

/-- Finite initial-segment law obtained by mixing an Ionescu--Tulcea partial trajectory over its
seed measure. -/
noncomputable def ionescuTulceaPrefixMeasure
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [_unusedMarkovStep : ∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) (n : ℕ) :
    Measure ((i : Finset.Iic n) → A) :=
  Kernel.partialTraj (X := fun _ ↦ A) step 0 n ∘ₘ seed

/-- A probability seed and Markov transition rows give a probability law on every finite
initial segment. -/
noncomputable instance instIsProbabilityMeasureIonescuTulceaPrefixMeasure
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [IsProbabilityMeasure seed]
    (n : ℕ) :
    IsProbabilityMeasure (ionescuTulceaPrefixMeasure step seed n) := by
  unfold ionescuTulceaPrefixMeasure
  infer_instance

/-- The initial prefix law is the seed law. -/
theorem ionescuTulceaPrefixMeasure_zero
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) :
    ionescuTulceaPrefixMeasure step seed 0 = seed := by
  rw [ionescuTulceaPrefixMeasure, Kernel.partialTraj_self, Measure.id_comp]

/-- A successor prefix appends one conditional transition to the previous prefix law. -/
theorem ionescuTulceaPrefixMeasure_succ
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [SFinite seed] (n : ℕ) :
    ionescuTulceaPrefixMeasure step seed (n + 1) =
      Measure.map (appendIicTrajectory n)
        (ionescuTulceaPrefixMeasure step seed n ⊗ₘ step n) := by
  rw [ionescuTulceaPrefixMeasure,
    Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc]
  rw [Kernel.partialTraj_succ_self]
  rw [← Measure.map_comp]
  rw [← Measure.compProd_eq_comp_prod]
  rw [Measure.compProd_map]
  rw [Measure.map_map]
  rfl
  all_goals first
    | exact measurable_IicProdIoc (X := fun _ : ℕ ↦ A)
    | exact measurable_id.prodMap
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ A) n).measurable
    | exact (MeasurableEquiv.piSingleton
        (X := fun _ : ℕ ↦ A) n).measurable

/-- Coordinatewise one-step compatibility transports every finite Ionescu--Tulcea prefix. -/
theorem map_ionescuTulceaPrefixMeasure
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (targetStep : (n : ℕ) → Kernel ((i : Finset.Iic n) → B) B)
    [∀ n, IsMarkovKernel (targetStep n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [IsProbabilityMeasure seed]
    (targetSeed : Measure ((i : Finset.Iic 0) → B))
    [IsProbabilityMeasure targetSeed]
    (map : A → B) (hMap : Measurable map)
    (hSeed : Measure.map (finiteTrajectoryCoordinateMap map 0) seed = targetSeed)
    (hStep : ∀ n trajectory,
      Measure.map map (step n trajectory) =
        targetStep n (finiteTrajectoryCoordinateMap map n trajectory))
    (n : ℕ) :
    Measure.map (finiteTrajectoryCoordinateMap map n)
        (ionescuTulceaPrefixMeasure step seed n) =
      ionescuTulceaPrefixMeasure targetStep targetSeed n := by
  induction n with
  | zero =>
      rw [ionescuTulceaPrefixMeasure_zero, ionescuTulceaPrefixMeasure_zero]
      exact hSeed
  | succ n inductionHypothesis =>
      rw [ionescuTulceaPrefixMeasure_succ, ionescuTulceaPrefixMeasure_succ]
      calc
        Measure.map (finiteTrajectoryCoordinateMap map (n + 1))
            (Measure.map (appendIicTrajectory n)
              (ionescuTulceaPrefixMeasure step seed n ⊗ₘ step n)) =
          Measure.map
            (finiteTrajectoryCoordinateMap map (n + 1) ∘ appendIicTrajectory n)
            (ionescuTulceaPrefixMeasure step seed n ⊗ₘ step n) := by
              rw [Measure.map_map
                (measurable_finiteTrajectoryCoordinateMap map hMap (n + 1))
                (measurable_appendIicTrajectory n)]
        _ = Measure.map
            (appendIicTrajectory n ∘
              Prod.map (finiteTrajectoryCoordinateMap map n) map)
            (ionescuTulceaPrefixMeasure step seed n ⊗ₘ step n) := by
              rw [finiteTrajectoryCoordinateMap_comp_appendIicTrajectory]
        _ = Measure.map (appendIicTrajectory n)
            (Measure.map (Prod.map (finiteTrajectoryCoordinateMap map n) map)
              (ionescuTulceaPrefixMeasure step seed n ⊗ₘ step n)) := by
                rw [Measure.map_map (measurable_appendIicTrajectory n)
                  ((measurable_finiteTrajectoryCoordinateMap map hMap n).prodMap hMap)]
        _ = Measure.map (appendIicTrajectory n)
            (Measure.map (finiteTrajectoryCoordinateMap map n)
                (ionescuTulceaPrefixMeasure step seed n) ⊗ₘ targetStep n) := by
                  rw [Measure.map_compProd_of_map_kernel
                    (measure := ionescuTulceaPrefixMeasure step seed n)
                    (kernel := step n) (targetKernel := targetStep n)
                    (sourceMap := finiteTrajectoryCoordinateMap map n)
                    (targetMap := map)
                    (hSourceMap :=
                      measurable_finiteTrajectoryCoordinateMap map hMap n)
                    (hTargetMap := hMap) (hKernel := hStep n)]
        _ = Measure.map (appendIicTrajectory n)
            (ionescuTulceaPrefixMeasure targetStep targetSeed n ⊗ₘ
              targetStep n) := by
                rw [inductionHypothesis]

/-- Infinite trajectory law obtained by mixing Ionescu--Tulcea trajectories over a seed law. -/
noncomputable def ionescuTulceaTrajectoryMeasure
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) :
    Measure (ℕ → A) :=
  Kernel.traj (X := fun _ ↦ A) step 0 ∘ₘ seed

/-- A probability seed and Markov transition rows give a probability law on the infinite
trajectory. -/
noncomputable instance instIsProbabilityMeasureIonescuTulceaTrajectoryMeasure
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [IsProbabilityMeasure seed] :
    IsProbabilityMeasure (ionescuTulceaTrajectoryMeasure step seed) := by
  unfold ionescuTulceaTrajectoryMeasure
  infer_instance

/-- Every finite marginal of the infinite trajectory is the corresponding mixed partial law. -/
theorem map_frestrictLe_ionescuTulceaTrajectoryMeasure
    {A : Type u} [MeasurableSpace A]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [_unusedSeedSFinite : SFinite seed] (n : ℕ) :
    Measure.map (frestrictLe n) (ionescuTulceaTrajectoryMeasure step seed) =
      ionescuTulceaPrefixMeasure step seed n := by
  unfold ionescuTulceaTrajectoryMeasure ionescuTulceaPrefixMeasure
  rw [Measure.map_comp]
  rw [Kernel.traj_map_frestrictLe]
  exact measurable_frestrictLe n

/-- Apply one function coordinatewise to an infinite trajectory. -/
def trajectoryCoordinateMap
    {A : Type u} {B : Type v} (map : A → B) : (ℕ → A) → (ℕ → B) :=
  fun trajectory n ↦ map (trajectory n)

/-- A measurable coordinate map induces a measurable map on infinite trajectories. -/
theorem measurable_trajectoryCoordinateMap
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (map : A → B) (hMap : Measurable map) :
    Measurable (trajectoryCoordinateMap map) := by
  apply Measurable.of_eval
  intro n
  exact hMap.comp (measurable_pi_apply n)

/-- Finite restriction commutes with coordinatewise mapping. -/
theorem frestrictLe_comp_trajectoryCoordinateMap
    {A : Type u} {B : Type v} (map : A → B) (n : ℕ) :
    frestrictLe n ∘ trajectoryCoordinateMap map =
      finiteTrajectoryCoordinateMap map n ∘ frestrictLe n :=
  rfl

/-- Coordinatewise seed and one-step compatibility determine the exact pushforward of the full
Ionescu--Tulcea trajectory law. -/
theorem map_ionescuTulceaTrajectoryMeasure
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    (step : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (step n)]
    (targetStep : (n : ℕ) → Kernel ((i : Finset.Iic n) → B) B)
    [∀ n, IsMarkovKernel (targetStep n)]
    (seed : Measure ((i : Finset.Iic 0) → A)) [IsProbabilityMeasure seed]
    (targetSeed : Measure ((i : Finset.Iic 0) → B))
    [IsProbabilityMeasure targetSeed]
    (map : A → B) (hMap : Measurable map)
    (hSeed : Measure.map (finiteTrajectoryCoordinateMap map 0) seed = targetSeed)
    (hStep : ∀ n trajectory,
      Measure.map map (step n trajectory) =
        targetStep n (finiteTrajectoryCoordinateMap map n trajectory)) :
    Measure.map (trajectoryCoordinateMap map)
        (ionescuTulceaTrajectoryMeasure step seed) =
      ionescuTulceaTrajectoryMeasure targetStep targetSeed := by
  apply Measure.eq_of_map_frestrictLe_eq
  intro n
  rw [Measure.map_map (measurable_frestrictLe n)
    (measurable_trajectoryCoordinateMap map hMap)]
  rw [frestrictLe_comp_trajectoryCoordinateMap]
  rw [← Measure.map_map
    (measurable_finiteTrajectoryCoordinateMap map hMap n)
    (measurable_frestrictLe n)]
  rw [map_frestrictLe_ionescuTulceaTrajectoryMeasure]
  rw [map_ionescuTulceaPrefixMeasure step targetStep seed targetSeed
    map hMap hSeed hStep n]
  rw [map_frestrictLe_ionescuTulceaTrajectoryMeasure]

end FiniteMarkovProcesses.Probability
