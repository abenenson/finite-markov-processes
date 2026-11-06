# Finite-alphabet Sanov theorem

Import `FiniteMarkovProcesses.Sanov`. The finite method of types proves Sanov's
large-deviation bounds for independent samples on any finite alphabet. The result
is classical; see I. N. Sanov, “On the probability of large deviations of random
variables,” *Matematicheskii Sbornik* **42(84)** (1957), 11–44. The implementation
and extracted proofs are by Adam Benenson.
The source is `the standalone mathematical library` at
`recorded-source-baseline`; `source-plan.json` records the exact
original paths and SHA-256 checksums.

For a finite alphabet `State`, `FiniteStateProbabilityDensity State` is the closed
probability simplex: its nonnegative coordinates sum to one. It has the
coordinatewise topology and its Borel measurable space. The reference density
`reference` must satisfy `reference.IsInterior`, meaning that **every reference
coordinate is strictly positive**. Target densities can have zero coordinates.
The alphabet also carries a measurable space with measurable singletons for the
IID product measure.

`finiteIIDEmpiricalProbabilityDensityLaw n reference.probabilityMassFunction`
is the exact law of the empirical density of **n + 1 observations**. Index zero
therefore means one observation. Its speed is
`finiteIIDPositiveSampleSpeed n = ((n + 1 : ℕ) : ℝ)`, which is positive and tends
to infinity. The good rate is

\[
I(q)=D(q\Vert p)=\sum_x q_x\log(q_x/p_x),\qquad p=\mathrm{reference}.
\]

The zero-coordinate convention is retained by the coordinatewise Poisson
representation. Under the interior-reference assumption this rate is continuous
on the entire closed simplex and nonnegative. Its extended nonnegative-real
wrapper is `finiteStateProbabilityDensityRelativeEntropy reference`.

For every closed simplex event F and every open simplex event G, the theorems
`finiteIIDEmpiricalProbabilityDensityLaw_closedUpperBound` and
`finiteIIDEmpiricalProbabilityDensityLaw_openLowerBound` give literally

\[
\limsup_{n\to\infty}\frac{\log\mathbb P(L_{n+1}\in F)}{n+1}
\le -\inf_{q\in F} I(q),\qquad
-\inf_{q\in G} I(q)
\le\liminf_{n\to\infty}\frac{\log\mathbb P(L_{n+1}\in G)}{n+1}.
\]

The extended logarithm sends probability zero to negative infinity. Neither
bound converts a zero probability to a finite real logarithm.
`finiteStateProbabilityDensityRelativeEntropy_isGoodRateFunction` proves
compactness of every finite rate sublevel in this same topology.

The proof uses exact integer count types. Their number is at most
`(n + 2) ^ Fintype.card State`. The logarithmic correction per sample is
`finiteEmpiricalTypeLogarithmicOverhead (Fintype.card State) n`; it tends to zero.
A deterministic rounded empirical type approaches every point of the closed
simplex, including its boundary. Thus the open lower bound covers open
neighborhoods of boundary points without an interior-target assumption.

`FiniteMarkovProcessesExamples.Sanov` instantiates the theorem for a fair binary
reference, includes empirical points supported at a single state, and applies
the finite-sample lower bound at such a boundary point. "Positive sample" means
a positive **sample size**, not positive counts at every state.

The extracted dependency cone also includes Poisson discrimination and finite
oriented graph action tools. Product-measure discrimination is imported from
the public `MeasureDiscrimination.ProductDiscrimination` package and is not
redefined here. The only shared CTMC dependency is `PoissonCountExpectation`.
