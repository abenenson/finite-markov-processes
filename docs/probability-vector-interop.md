# Reusing public finite Markov kernels

Import `FiniteMarkovProcesses.ProbabilityVectorInterop` to connect the empirical
simplex with `FiniteMarkovKernels.ProbabilityVector` from the public
[`finite-markov-kernels`](https://github.com/abenenson/finite-markov-kernels)
package. The package dependency is pinned to an exact public commit.

For a finite alphabet, a `FiniteStateProbabilityDensity` stores `NNReal` weights.
A public `ProbabilityVector` stores real weights and an explicit nonnegativity
proof. `density.toProbabilityVector` and
`FiniteStateProbabilityDensity.ofProbabilityVector vector` retain every
coordinate and are mutual inverses. `probabilityVectorEquiv` packages those maps.
Both carriers already have their coordinatewise topology, and
`probabilityVectorHomeomorph` proves that the existing topologies agree through
the conversion. The module introduces no new topology instances.

The conversion preserves zero coordinates, full support, and the coordinate
support relation expressing absolute continuity. In particular, an interior
empirical density converts to a public vector with `FullSupport`, and boundary
points retain their zero coordinates. Its canonical `toPMF` equals the original
`probabilityMassFunction` exactly.

A public `FiniteMarkovKernel` can therefore act on an empirical density by
`kernel.apply density.toProbabilityVector`. Converting the result back supplies
a typed empirical-simplex point with exactly the same law. See
`FiniteMarkovProcessesExamples.ProbabilityVectorInterop` for binary examples.

The two carriers remain distinct to preserve the extracted empirical-law and
large-deviation proof APIs. This bridge is the compatibility surface for the
current release; a complete carrier consolidation would also need to migrate
record constructors and proofs using their different coordinate embeddings.
