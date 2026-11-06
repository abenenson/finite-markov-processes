/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventDeletion
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedCrossing

/-!
# Reduced stopped laws of finite-state uniformized trajectories

This module maps the normalized stopped uniformized history law through canonical measurable
self-event deletion. The resulting reduced pushforward is again exactly normalized.

The named physical-identification predicate is intentionally not discharged here. Equality with
the canonical `finiteStateMarkovJumpDensityMeasure` requires the state-dependent Poisson thinning
and density calculation that turns deleted virtual events into physical escape survival.

## Main Results

- `finiteStateUniformizedReducedHistoryMeasure`: deletion pushforward of the stopped virtual law.
- `finiteStateUniformizedReducedHistoryMeasure_univ`: exact normalization.
- `FiniteStateUniformizedDeletionIdentifiesPhysicalLaw`: named remaining pushforward identity.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open FiniteStateMarkovUniformizedTrajectory
open FiniteStateMarkovUniformizedStoppedLaw

universe u

variable {State : Type u} [Fintype State] [DecidableEq State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Reduced history law obtained by deleting virtual self-events from the normalized stopped
uniformized law. -/
noncomputable def finiteStateUniformizedReducedHistoryMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    Measure (FiniteJumpHistory State) :=
  Measure.map FiniteJumpHistory.deleteSelfEvents
    (finiteStateUniformizedStoppedHistoryMeasure initial generator T)

/-- Deletion preserves exact normalization of the stopped uniformized law. -/
theorem finiteStateUniformizedReducedHistoryMeasure_univ
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedReducedHistoryMeasure initial generator T Set.univ = 1 := by
  rw [finiteStateUniformizedReducedHistoryMeasure,
    Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents MeasurableSet.univ]
  rw [preimage_univ, finiteStateUniformizedStoppedHistoryMeasure_univ]

/-- Bundled normalized reduced uniformized history law. -/
noncomputable def finiteStateUniformizedReducedHistoryProbabilityMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    ProbabilityMeasure (FiniteJumpHistory State) :=
  ⟨finiteStateUniformizedReducedHistoryMeasure initial generator T,
    ⟨finiteStateUniformizedReducedHistoryMeasure_univ initial generator T⟩⟩

/-- Bundling the reduced law leaves its underlying measure unchanged. -/
@[simp]
theorem finiteStateUniformizedReducedHistoryProbabilityMeasure_toMeasure
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    (finiteStateUniformizedReducedHistoryProbabilityMeasure initial generator T).toMeasure =
      finiteStateUniformizedReducedHistoryMeasure initial generator T :=
  rfl

/-- Named remaining uniformization theorem: measurable deletion of virtual self-events identifies
the normalized reduced pushforward with the canonical physical finite-jump density law. -/
def FiniteStateUniformizedDeletionIdentifiesPhysicalLaw
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) : Prop :=
  finiteStateUniformizedReducedHistoryMeasure initial generator T =
    finiteStateMarkovJumpDensityMeasure initial generator T

/-- The named identification predicate is literally the required measure equality. -/
theorem finiteStateUniformizedReducedHistoryMeasure_eq_physical_iff
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State) (T : ℝ) :
    finiteStateUniformizedReducedHistoryMeasure initial generator T =
        finiteStateMarkovJumpDensityMeasure initial generator T ↔
      FiniteStateUniformizedDeletionIdentifiesPhysicalLaw initial generator T :=
  Iff.rfl

end FiniteMarkovProcesses.Probability
