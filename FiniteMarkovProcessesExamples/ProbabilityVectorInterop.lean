/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.ProbabilityVectorInterop
import FiniteMarkovProcessesExamples.Sanov

/-!
# Empirical densities with public finite Markov kernels

These examples transport a binary reference and empirical samples to the public kernel API.
Converting the resulting probability vector back preserves its canonical probability law.
-/

namespace FiniteMarkovProcessesExamples.ProbabilityVectorInterop

open FiniteMarkovProcesses.InformationTheory FiniteMarkovProcesses.Probability
open FiniteStateProbabilityDensity

/-- The fair binary reference supplies a full-support public probability vector. -/
example : Sanov.fairBinary.toProbabilityVector.FullSupport :=
  (toProbabilityVector_fullSupport_iff Sanov.fairBinary).mpr Sanov.fairBinary_isInterior

/-- A public finite Markov kernel can act directly on a converted empirical sample; conversion
back to the empirical-density carrier preserves the resulting PMF. -/
example (n : ℕ) (sample : Fin (n + 1) → Bool)
    (kernel : FiniteMarkovKernels.FiniteMarkovKernel Bool Bool) :
    let transformed :=
      kernel.apply (finiteIIDEmpiricalProbabilityDensity n sample).toProbabilityVector
    (ofProbabilityVector transformed).probabilityMassFunction = transformed.toPMF :=
  ofProbabilityVector_probabilityMassFunction _

end FiniteMarkovProcessesExamples.ProbabilityVectorInterop
