/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpLaw

/-!
# Independent finite-state Markov jump replicas

This module constructs the finite product of an exactly normalized finite-state Markov jump law.
It proves genuine coordinate independence and exact single-coordinate marginals.  The construction
also covers the empty finite product; empirical normalizations belong to separate positive-count
observations.

This is particle replication, not a rescaling of one path's clock or jump intensity.

## Main results

- `finiteStateMarkovJumpReplicaProbabilityMeasure`: the normalized finite product law.
- `finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure`: its underlying `Measure.pi` law.
- `finiteStateMarkovJumpReplicaProbabilityMeasure_coordinates_iIndepFun`: genuine coordinate
  independence.
- `finiteStateMarkovJumpReplicaProbabilityMeasure_coordinate_map`: every coordinate has the exact
  original finite-state Markov jump law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]

/-- The finite product of identical normalized finite-state Markov jump history laws.

At replica count zero this is the normalized empty product.  No empirical division by the replica
count occurs in this definition. -/
noncomputable def finiteStateMarkovJumpReplicaProbabilityMeasure
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    ProbabilityMeasure (Fin replicaCount → FiniteJumpHistory State) :=
  ProbabilityMeasure.pi fun _ =>
    finiteStateMarkovJumpProbabilityMeasure initial generator duration hNormalized

/-- The underlying replica measure is literally the finite product of the normalized single-history
density measure. -/
@[simp]
theorem finiteStateMarkovJumpReplicaProbabilityMeasure_toMeasure
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    (finiteStateMarkovJumpReplicaProbabilityMeasure
      replicaCount initial generator duration hNormalized).toMeasure =
      Measure.pi fun _ : Fin replicaCount =>
        finiteStateMarkovJumpDensityMeasure initial generator duration := by
  rw [finiteStateMarkovJumpReplicaProbabilityMeasure, ProbabilityMeasure.toMeasure_pi]
  congr 1

/-- The coordinate histories under the replica law are mutually independent.  This is the exact
product-law witness required to distinguish particle replication from clock scaling. -/
theorem finiteStateMarkovJumpReplicaProbabilityMeasure_coordinates_iIndepFun
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration) :
    iIndepFun
      (fun replica : Fin replicaCount =>
        fun histories : Fin replicaCount → FiniteJumpHistory State => histories replica)
      (finiteStateMarkovJumpReplicaProbabilityMeasure
        replicaCount initial generator duration hNormalized).toMeasure := by
  unfold finiteStateMarkovJumpReplicaProbabilityMeasure
  rw [ProbabilityMeasure.toMeasure_pi]
  exact iIndepFun_pi fun _ => measurable_id.aemeasurable

/-- Each coordinate projection of the replica law is exactly the original normalized
finite-state Markov jump density measure. -/
theorem finiteStateMarkovJumpReplicaProbabilityMeasure_coordinate_map
    (replicaCount : ℕ) (initial : PMF State)
    (generator : FiniteStateMarkovGenerator State) (duration : ℝ)
    (hNormalized : FiniteStateMarkovJumpDensityIsNormalized initial generator duration)
    (replica : Fin replicaCount) :
    Measure.map
        (fun histories : Fin replicaCount → FiniteJumpHistory State => histories replica)
        (finiteStateMarkovJumpReplicaProbabilityMeasure
          replicaCount initial generator duration hNormalized).toMeasure =
      finiteStateMarkovJumpDensityMeasure initial generator duration := by
  unfold finiteStateMarkovJumpReplicaProbabilityMeasure
  change Measure.map (Function.eval replica)
      (Measure.pi fun _ : Fin replicaCount =>
        (finiteStateMarkovJumpProbabilityMeasure
          initial generator duration hNormalized).toMeasure) =
    finiteStateMarkovJumpDensityMeasure initial generator duration
  rw [(measurePreserving_eval
    (fun _ : Fin replicaCount =>
      (finiteStateMarkovJumpProbabilityMeasure
        initial generator duration hNormalized).toMeasure) replica).map_eq]
  exact finiteStateMarkovJumpProbabilityMeasure_toMeasure
    initial generator duration hNormalized

end FiniteMarkovProcesses.Probability
