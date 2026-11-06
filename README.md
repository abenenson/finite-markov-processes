# Finite Markov Processes

Finite-state jump processes and large deviations in Lean 4, built on Mathlib.

The library develops finite-horizon history laws from generators and connects
their explicit densities with normalized generative constructions. The planned
upper layers formalize finite-alphabet Sanov bounds, density/flux path large
deviations, zero-action evolution, and quantitative particle confidence.

This is an extraction under verification. Source preparation and a successful
build are separate milestones; the qualification reports record which exact
sources have passed builds, full source lint, and transitive axiom checks.

## Continuous-time jump processes

```lean
import FiniteMarkovProcesses.CTMC
```

The core includes:

- Finite-horizon Gillespie histories, with absorbing states handled explicitly.
- Equality of the stopped generative law and its counting/Lebesgue density,
  including a proof of normalization for every nonnegative finite horizon.
- Uniformization and exact deletion of virtual self-events, with a bounded
  measurable time-dependent extension.
- Common-support likelihood-ratio, integral fluctuation, and expected-KL
  identities.
- Stationary path-KL rates and complete-trajectory Fisher response for explicitly
  identified affine generator charts.

The hypotheses are part of the API: common support, integrability, stationarity,
and chart identification are retained where needed. See
[the CTMC guide](docs/CTMC.md) and [checked examples](FiniteMarkovProcessesExamples/CTMC.lean).

## Dependencies and verification

The supported pair is Lean **4.34.1** and Mathlib
**`d13f23b723b8a846827a245b89c10fc7d3f11612`**. Public dependencies use exact
commit pins. The finite-simplex interface composes with
[`finite-markov-kernels`](https://github.com/abenenson/finite-markov-kernels),
and product-measure transport uses
[`measure-discrimination`](https://github.com/abenenson/measure-discrimination).

```sh
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

The verifier inventories every authored Lean file, clears its compiled artifacts
before the initial build, runs all 16 source linters, and audits each explicit
named public declaration's transitive axioms. It admits only `propext`,
`Classical.choice`, and `Quot.sound`. It does not claim to enumerate every
anonymous or generated declaration independently.

Long verification runs can resume with `--resume --evidence-dir DIR`. Completed
stages are reusable only with matching source, dependency, compiler, configuration,
and verifier identities and intact logs. Ordinary overlong lines are rejected;
any inherited indivisible long identifier requires an exact line hash and reason.

## Attribution and scope

These are formalizations of classical mathematics. Mathematical references and
original author notices remain in the individual modules. The path large-deviation
development follows Renger's density/flux results; the finite Sanov development
uses the method of types. No mathematical priority claim is made.

The package contains generic mathematics. It does not assert empirical validity
for a physical model. [The extraction plan](source-plan.json) records the exact
source revision, original module paths and hashes, public dependencies, and
module ownership. [Apache-2.0](LICENSE); see [NOTICE](NOTICE).
