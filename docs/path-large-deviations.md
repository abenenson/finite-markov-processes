# Path large deviations and effective evolution

**Status:** Extraction candidate; acceptance awaits fresh build, lint, and axiom checks.

This library extracts generic finite-state mathematics from source commit
`recorded-source-baseline`. Its action and theorem labels retain the
classical attribution to D. R. Michiel Renger, *Flux large deviations of independent and
reacting particle systems, with implications for macroscopic fluctuation theory*,
Journal of Statistical Physics 172 (2018), 1261–1326,
[doi:10.1007/s10955-018-2083-0](https://doi.org/10.1007/s10955-018-2083-0).
The contribution here is extraction and proof assembly, with the source assumptions preserved.

Import `FiniteMarkovProcesses.PathLargeDeviations` for the three path-LDP constructors
and the original-IID exponential confidence estimate. Import
`FiniteMarkovProcesses.EffectiveEvolution` for the complete-rate zero-set classification.
[The theorem map](theorem-map.md) names the declarations and separates assumptions from
proved outputs. [The examples](../FiniteMarkovProcessesExamples/PathLargeDeviations.lean) exercise the public APIs.

## Generator, carrier, and rate

`FiniteStateMarkovGenerator.rate x y : NNReal` is the nonnegative jump-rate kernel with
zero diagonal. It is distinct from the conservative generator matrix, whose diagonal is
minus the escape rate. The row-density forward equation is

```text
rho'_x(t) = sum_y rho_y(t) q_yx - rho_x(t) sum_y q_xy.
```

`RengerDirectionalFlowHybridBVPath State T` carries density and cumulative **ordered
off-diagonal** flow coordinates on the open physical interval `(0,T)`. The carrier binds
strong-L1 equivalence classes to finite signed distributional derivatives, with the induced
strong-L1 plus vague-derivative topology and Borel measurable space. A selected càdlàg
representative recovers initial and terminal-left traces. Equality of paths retains derivative
and boundary data, as well as density and cumulative flow.

For `T > 0`, arbitrary `I0 : FiniteStateProbabilityDensity State → ENNReal`, and a path `p`,
the complete rate is `I0` at the recovered initial density plus

```text
integral_(0,T) sum_(x != y) s(j_xy(t) | rho_x(t) q_xy) dt.
```

The integral is extended nonnegative. Admissibility requires the existing absolutely
continuous derivative and reconstruction conditions, nonnegative normalized density,
nonnegative cumulative flow and flow derivatives, the continuity equation, zero initial
cumulative flow, and the boundary-trace contracts. Inadmissible paths have infinite rate.
Failure to recover a normalized initial density also receives infinite initial cost.

For nonnegative `j,a`, `s(j|a) = j log(j/a) - j + a` when `a > 0`, with the usual zero-flow
convention. At a zero reference intensity, `s(0|0)=0` and `s(j|0)=∞` for `j>0`.
Rates may vanish; no positivity assumption is hidden by the nonnegative coercions on the
admissible domain.

## Three actual microscopic sources

All path-LDP constructors retain finite decidable state, measurable-space and
measurable-singleton instances, a discrete Borel topology, a nonempty state type, and a positive
real duration. Their particle index `n` means `n+1` replicas and speed `n+1`, so the zero-particle
case never enters their laws. None assumes a path LDP as an input.

* **Theorem 4.1:** supplied deterministic labelled configurations have empirical densities
  converging coordinatewise to a density strictly positive in every coordinate. The initial
  rate is zero at that limiting density and infinity elsewhere. The constructor derives its
  initial LDP and preserves the original configurations in the microscopic law.
* **Theorem 4.2:** supplied probability laws on empirical count types push forward exactly to
  the declared initial simplex laws. The caller supplies a good initial rate, its closed upper
  and open lower LDP bounds at particle speed, topology compatibility, and its specified
  lower-boundary continuity property. The count-type mixture produces actual positive-replica
  histories. This theorem extends an **initial** LDP to a **path** LDP; it does not prove an
  arbitrary initial family satisfies that initial contract.
* **Corollary 4.16:** supplied full-support stationary distribution and uniqueness as equality
  of PMFs. The source genuinely initializes labelled replicas IID from that distribution.
  Its initial rate is invariant relative entropy. The finite-IID initial LDP is proved in the
  dependency cone. The corollary retains its stationary uniqueness premise, although the
  scalar initial cost itself does not use it.

Each terminal `...LargeDeviationRepresentation` is a constructed value containing normalized
microscopic laws, a measurable full-carrier observation, positive divergent speed, complete
rate data, Borel compatibility, good-rate compactness, and proved closed upper/open lower
bounds. A bare `DensityFluxLargeDeviationRepresentation` structure declaration is only a
contract; the named terminal constructors provide its mathematical fields from their stated
initial-data contracts. The provenance label and strings provide attribution, not a proof.

## Frozen endpoint conventions

The exact repository history observation counts a jump at or before time `t` and selects the
càdlàg occupied state. The published cumulative flow uses `(0,t)`. For each finite history,
strict-before and at-or-before selectors agree away from its finitely many event times, hence
almost everywhere in physical time. The empirical endpoint bridge passes this equality to L1
classes and any observation respecting componentwise almost-everywhere equality. It does not
claim pointwise equality at jump times or silently change the physical interval.

The distributional derivative uses the Stieltjes convention `d p ((a,b]) = p(b)-p(a)` for
interior endpoints. Traces remain recovered boundary data; vague derivative convergence alone
does not assert ambient continuity of traces. Rate-bounded trace-closure theorems carry their
own finite-level and admissibility hypotheses.

## Zero complete rate and actual mean evolution

For finite decidable measurable states, any constant nonnegative generator, and `T > 0`,

```text
C(Q,T,I0,p) = 0
  iff admissible(p), I0(recovered initial(p)) = 0, and j_xy = rho_x q_xy a.e.
  iff there exists rho, I0(rho) = 0 and p = Mean(Q,rho,T).
```

`Mean` here is the existing actual generated Markov mean hybrid path, built from the history
law and endpoint probabilities. Admissibility and generator flow derive absolute continuity
and the forward equation; classical finite-state forward uniqueness then determines density,
cumulative flow, derivative measures, and traces. The mean map is injective by initial-trace
recovery. The arbitrary supplied initial cost can have no zeros, one zero, or several zeros.
A singleton path zero set requires a separately proved singleton initial zero set. The included
two-state zero-generator theorem exhibits two distinct zero paths for identically zero initial
cost. Irreducibility, stationarity, and strictly positive rates are unnecessary here.

The standalone forward-uniqueness theorem works for real coordinates, with absolute continuity
on each strict subhorizon and an a.e. common forward equation. It needs neither probability
normalization nor positive duration; a nonpositive-duration half-open interval is empty.
The hybrid classification still requires positive duration. It classifies zeros, with no claim
about positive-cost minimizers when the initial zero set is empty.

## Original-IID exponential confidence

`measure_iid_totalHybridBVObservation_deviation_le_exponential` is a separate probability
bound under the original product law, arbitrary initial PMF, and unchanged positive duration.
For `N=n+1`, `a=uniformizationRate*T`, `d` density-plus-ordered-flow coordinates, radius `r`,
and a supplied tilt `0 ≤ theta ≤ 1/(4(a+1))`, it gives

```text
P(norm_L1(empirical total hybrid observation - actual unconditional mean) >= r)
  <= ofReal(2 exp(N (a+1)^2 theta^2 - N theta r/(T d))).
```

The theorem retains unbounded count tails using Poisson domination and exact self-event
deletion. The uniformization rate appears in the bound; the center is the actual generated
mean. This finite-particle estimate concerns the strong-L1 component of the hybrid observation,
not a metric for every vague-derivative test. The deterministic zero-set theorem does not
supply this estimate, and an LDP alone is not this explicit finite-sample bound.

## Validation status

The 193 path/evolution modules were extracted after checking every source SHA256 against
`source-plan.json` and independently against the pinned Git blobs; their imports match the planned rewritten graph with no unresolved planned
local dependency. Proof text differs only by the declared namespace/module rewrites and line
wrapping, including the public `MeasureDiscrimination.ProductDiscrimination` dependency.
Public mathematical comments replace source-specific terminology and construction chronology.
No new theorem premise, axiom, or proof placeholder was introduced. This static provenance check
is not elaboration. Exact-source compilation, full source lint, and transitive axiom audits
remain pending fresh validation; this document makes no completed verification or
release-readiness claim.
