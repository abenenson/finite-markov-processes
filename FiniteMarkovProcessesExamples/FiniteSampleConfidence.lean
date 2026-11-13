/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteSampleConfidence

/-!
# Rational confidence-budget examples

The polynomial constant twelve and exponential scale two are illustrative inputs to independently
proved envelopes. A polynomial envelope reaches failure tolerance `1/20` at 240 samples;
an exponential envelope reaches five confidence bits at 96 samples. The large-radius example
exercises the linear branch. Zero-radius computations illustrate why positivity is a hypothesis
of each guarantee: total rational division still returns a number outside the theorem's domain.
-/

@[expose] public section

namespace FiniteMarkovProcessesExamples

open FiniteMarkovProcesses.Probability

example : polynomialParticleBudget 12 1 (1 / 20) = 240 := by
  norm_num [polynomialParticleBudget]

example : polynomialParticleBudget 12 2 (1 / 20) = 60 := by
  norm_num [polynomialParticleBudget]

example : exponentialParticleBudget 2 1 5 = 96 := by
  norm_num [exponentialParticleBudget, exponentialRateRat]

example : exponentialRateRat 2 (1 / 2) = 1 / 64 := by
  norm_num [exponentialRateRat]

example : exponentialParticleBudget 2 (1 / 2) 5 = 384 := by
  norm_num [exponentialParticleBudget, exponentialRateRat]

example : exponentialRateRat 2 4 = 1 / 4 := by
  norm_num [exponentialRateRat]

example : exponentialParticleBudget 2 4 5 = 24 := by
  norm_num [exponentialParticleBudget, exponentialRateRat]

example {mass : ENNReal}
    (hEnvelope : mass ≤ ENNReal.ofReal (12 / (240 * (1 : ℝ) ^ 2))) :
    mass ≤ ENNReal.ofReal (1 / 20) := by
  have h := le_of_polynomialParticleBudget (mass := mass) (constant := 12) (radius := 1)
    (failure := 1 / 20) (count := 240) (by norm_num) (by norm_num)
    (by norm_num [polynomialParticleBudget])
    (by norm_num at hEnvelope ⊢; exact hEnvelope)
  norm_num at h
  exact h

example {mass : ENNReal}
    (hEnvelope : mass ≤ ENNReal.ofReal (2 * Real.exp (-(96 : ℝ) / 16))) :
    mass ≤ ENNReal.ofReal (1 / 32) := by
  have h := le_dyadic_of_exponentialParticleBudget (mass := mass) (scale := 2) (radius := 1)
    (by norm_num) (by norm_num) 5 (count := 96)
    (by norm_num [exponentialParticleBudget, exponentialRateRat])
    (by norm_num [exponentialRateRat] at hEnvelope ⊢; exact hEnvelope)
  norm_num at h
  exact h

example : polynomialParticleBudget 12 0 (1 / 20) = 1 := by
  norm_num [polynomialParticleBudget]

example : exponentialParticleBudget 2 0 5 = 1 := by
  norm_num [exponentialParticleBudget, exponentialRateRat]

example : ¬ (1 : ENNReal) ≤ ENNReal.ofReal (1 / 20) := by
  norm_num

example : ¬ (1 : ℝ) ≤ 96 * (exponentialRateRat 2 1 - exponentialRateRat 2 1) := by
  norm_num

end FiniteMarkovProcessesExamples
