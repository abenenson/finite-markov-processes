# Finite Markov Processes

Finite-state jump processes and large deviations in Lean 4, built on Mathlib.

The library develops finite-horizon history laws from generators and connects
their explicit densities with normalized generative constructions. Its upper
layers formalize finite-alphabet Sanov bounds, density/flux path large
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

## Large deviations and effective evolution

Focused entry points keep the mathematical layers explicit:

| Import | Results and important premises |
| --- | --- |
| `FiniteMarkovProcesses.Sanov` | Finite-alphabet closed upper/open lower bounds and a good KL rate; the reference density is strictly positive, while empirical targets may lie on the boundary. |
| `FiniteMarkovProcesses.ProbabilityVectorInterop` | Coordinate-preserving equivalence and homeomorphism with the public probability-vector API, including equality of canonical PMFs. |
| `FiniteMarkovProcesses.PathLargeDeviations` | Renger density/flux path bounds for specified initial regimes; the general initial-law theorem assumes an initial LDP and boundary continuity. |
| `FiniteMarkovProcesses.EffectiveEvolution` | Complete-rate zeros are exactly Markov mean evolutions from the supplied initial zero set; all-N strong-L1 particle bounds remain separate probabilistic results. |
| `FiniteMarkovProcesses.QuantitativeBounds` | Dynamic-rate stability with explicit initial-density error, rate-gap coercivity, and eventual LDP concentration. |

General initial mixtures have independent jump dynamics conditional on the
initial configuration. The invariant-IID corollary uses actual IID initialized
histories. The supplied initial cost determines the zero family; uniqueness of
its initial zero is an additional condition.

The all-N Chernoff estimate controls density and cumulative-flow paths in strong
L1 distance from their actual unconditional mean, using a supplied admissible
tilt. The deterministic stability estimates retain the initial-density error;
an arbitrary initial cost does not control that error automatically.

See [the theorem and premise map](docs/theorem-map.md),
[the path large-deviation guide](docs/path-large-deviations.md),
[the Sanov guide](docs/sanov.md), and
[probability-vector interoperability](docs/probability-vector-interop.md).

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
named public top-level declaration's transitive axioms. It admits only `propext`,
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
