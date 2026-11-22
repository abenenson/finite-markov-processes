/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteSampleConfidence
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovGeneratorMatrix
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovIIDHybridFiniteSample

/-!
# Finite-particle confidence from a signed rate matrix

The input matrix, with rows and columns ordered `false`, `true`, is `[[-1, 1], [0, 0]]` in
inverse seconds. The chain starts at `false` and jumps at rate one to the absorbing state `true`.
The one-second experiment observes both state occupancies and both cumulative directed transition
counts per particle. The integrated sum of absolute coordinate errors from the unconditional mean
is measured in seconds.
-/

@[expose] public section

namespace FiniteMarkovProcessesExamples.SignedGeneratorConfidence

open MeasureTheory
open FiniteMarkovProcesses.Probability
open PositiveFiniteJumpHistoryReplicas
open scoped BigOperators ENNReal NNReal

/-- Conventional signed matrix in inverse seconds, using the order `false`, `true`. -/
def signedMatrix : Matrix Bool Bool ℝ := Matrix.of fun source target ↦
  match source, target with
  | false, false => -1
  | false, true => 1
  | true, _ => 0

/-- The signed input has nonnegative off-diagonal entries. -/
theorem signedMatrix_offDiag_nonneg (source target : Bool) (hDistinct : source ≠ target) :
    0 ≤ signedMatrix source target := by
  cases source <;> cases target <;> simp_all [signedMatrix]

/-- Both rows of the signed input sum to zero. -/
theorem signedMatrix_sum_row (source : Bool) : ∑ target, signedMatrix source target = 0 := by
  cases source <;> norm_num [Fintype.sum_bool, signedMatrix]

/-- The physical generator recovered from the signed input. -/
def generator : FiniteStateMarkovGenerator Bool :=
  FiniteStateMarkovGenerator.ofMatrix signedMatrix signedMatrix_offDiag_nonneg

/-- The full matrix is recovered, including the absorbing row. -/
theorem generator_toMatrix : generator.toMatrix = signedMatrix :=
  FiniteStateMarkovGenerator.toMatrix_ofMatrix _ _ signedMatrix_sum_row

/-- The initial state has strictly positive jump rate to the absorbing state. -/
theorem generator_rate_false_true : generator.rate false true = 1 := by
  apply Subtype.ext
  change (generator.rate false true : ℝ) = 1
  rw [generator, FiniteStateMarkovGenerator.rate_ofMatrix_of_ne _ _ Bool.false_ne_true]
  rfl

/-- The rate of leaving the initial state is one inverse second. -/
theorem generator_escapeRate_false : generator.escapeRate false = 1 := by
  apply Subtype.ext
  change (generator.escapeRate false : ℝ) = 1
  rw [generator, FiniteStateMarkovGenerator.escapeRate_ofMatrix _ _ signedMatrix_sum_row]
  norm_num [signedMatrix]

/-- The second state is absorbing. -/
theorem generator_escapeRate_true : generator.escapeRate true = 0 := by
  apply Subtype.ext
  change (generator.escapeRate true : ℝ) = 0
  rw [generator, FiniteStateMarkovGenerator.escapeRate_ofMatrix _ _ signedMatrix_sum_row]
  norm_num [signedMatrix]

/-- Use the recovered rates at every time through the homogeneous embedding. -/
noncomputable def rates : FiniteStateTimeDependentMarkovRate Bool :=
  generator.toTimeDependentMarkovRate

/-- The common uniformization clock has rate two inverse seconds. -/
theorem rates_uniformizationRate : rates.uniformizationRate = 2 := by
  norm_num [rates, FiniteStateMarkovGenerator.toTimeDependentMarkovRate_uniformizationRate,
    FiniteStateMarkovGenerator.uniformizationRate, finiteStateTotalEscapeBound, Fintype.sum_bool,
    generator_escapeRate_false, generator_escapeRate_true]

noncomputable section

/-- All particles start in the only state with a positive escape rate. -/
def initial : PMF Bool := PMF.pure false

/-- The observation horizon, measured in seconds. -/
def duration : ℝ≥0 := 1

/-- The product of the physical laws of `successorIndex + 1` independent replicas. -/
def replicaLaw (successorIndex : ℕ) :
    Measure (PositiveFiniteJumpHistoryReplicas Bool successorIndex) :=
  Measure.pi fun _ : Fin (successorIndex + 1) ↦
    finiteStateMarkovJumpDensityMeasure initial generator duration

/-- The integrated absolute error of all density and cumulative ordered-flow coordinates
reaches the specified radius. -/
def deviationEvent (successorIndex : ℕ) (radius : ℝ) :
    Set (PositiveFiniteJumpHistoryReplicas Bool successorIndex) :=
  {histories | radius ≤
    ‖(empiricalDensityDirectionalFlowTotalHybridBVObservation
        successorIndex duration histories).toDerivativePath.toL1Path -
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        initial rates duration).toDerivativePath.toL1Path‖}

private theorem card_edges : Fintype.card (FiniteStateOffDiagonalEdge Bool) = 2 := by
  decide

private theorem card_coordinates :
    Fintype.card (EmpiricalDensityDirectionalFlowCoordinate Bool) = 4 := by
  rw [Fintype.card_sum, Fintype.card_bool, card_edges]

/-- The uniformization clock is two per second. The envelope uses two density coordinates and two
ordered-flow coordinates, including the identically zero reverse-flow coordinate. -/
theorem finiteSampleConstant_eq :
    finiteStateMarkovIIDHybridFiniteSampleConstant rates duration = 56 := by
  rw [finiteStateMarkovIIDHybridFiniteSampleConstant, rates_uniformizationRate,
    card_coordinates, Fintype.card_bool, card_edges]
  norm_num [duration]

/-- The variance envelope for this experiment comes from the actual physical product law. -/
theorem measure_deviation_le_polynomial (successorIndex : ℕ) {radius : ℝ}
    (hRadius : 0 < radius) :
    replicaLaw successorIndex (deviationEvent successorIndex radius) ≤
      ENNReal.ofReal (56 / ((successorIndex + 1 : ℝ) * radius ^ 2)) := by
  have hEnvelope := measure_iid_totalHybridBVObservation_projection_deviation_ge_le
    successorIndex initial rates duration (by norm_num [duration]) hRadius
  rw [finiteSampleConstant_eq] at hEnvelope
  simpa only [replicaLaw, deviationEvent, rates,
    finiteStateTimeDependentMarkovReducedHistoryMeasure_constant] using hEnvelope

/-- A radius of half a second and failure tolerance of one twentieth give 4,480 particles. -/
theorem particleBudget_eq : polynomialParticleBudget 56 (1 / 2) (1 / 20) = 4480 := by
  norm_num [polynomialParticleBudget]

/-- At 4,480 independent particles the probability of an integrated error of at least half a
second is at most one twentieth. The path API indexes 4,480 replicas by 4,479. -/
theorem measure_deviation_at_budget :
    replicaLaw 4479 (deviationEvent 4479 (1 / 2)) ≤ ENNReal.ofReal (1 / 20) := by
  have h := le_of_polynomialParticleBudget
    (mass := replicaLaw 4479 (deviationEvent 4479 (1 / 2))) (constant := 56) (radius := 1 / 2)
    (failure := 1 / 20) (count := 4480) (by norm_num) (by norm_num)
    (le_of_eq particleBudget_eq)
    (by
      have hEnvelope := measure_deviation_le_polynomial 4479 (radius := 1 / 2) (by norm_num)
      norm_num at hEnvelope ⊢
      exact hEnvelope)
  norm_num at h
  exact h

end

end FiniteMarkovProcessesExamples.SignedGeneratorConfidence
