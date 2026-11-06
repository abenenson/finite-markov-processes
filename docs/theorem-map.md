# Theorem and premise map

This map is a review guide to the extracted generic mathematics, not a new theorem.
Names below are in `FiniteMarkovProcesses.InformationTheory` unless a different namespace
is specified. Module links identify the authoritative Lean statements; the table summaries
retain the material mathematical assumptions. The extraction pins source commit
`recorded-source-baseline` in `source-plan.json`.

**Candidate status:** Not accepted. Source hashes and rewritten import closure checked statically;
exact-source elaboration, full source lint, and transitive axiom audits are pending fresh
validation. Historical upstream-source checks are not verification of this extraction.

## What is proved and what is supplied

| Entry | Kind | What it establishes or requires |
| --- | --- | --- |
| `DensityFluxLargeDeviationRepresentation` | Structure contract | Fields request laws, observations, rate, good-rate compactness, and upper/lower bounds. The type's declaration alone supplies none of them. |
| `RengerTheoremFourOneInitialData` | Input contract | Deterministic configurations, exact empirical counts, an interior limiting density, and coordinatewise convergence. |
| `RengerTheoremFourTwoInitialData` | Input contract | Probability count-type and simplex laws, exact pushforward equality, good initial rate, its initial LDP bounds, Borel compatibility, and specified boundary continuity. |
| `RengerCorollaryFourSixteenInitialData` | Input contract | A full-support stationary distribution and uniqueness of its PMF. |
| Three named `...HybridBVLargeDeviationRepresentation` constructors below | Constructed values | Fill every representation field from the corresponding initial-data contract, including proved path bounds on actual microscopic laws. |
| `Renger2018DirectionalFlowProvenance` | Attribution data | Published theorem label and fixed bibliography/conventions; it proves no LDP. |
| `RengerDirectionalFlowRepresentationObligation` | Construction enumeration | An enumeration retained in the boundary API; it is neither an axiom nor a proof that an obligation is discharged. |

The representation contract lives in
[DensityFluxLargeDeviationRepresentation.lean](../FiniteMarkovProcesses/RelativeEntropy/DensityFluxLargeDeviationRepresentation.lean).
The three initial contracts and provenance live in
[FiniteStateJumpDirectionalFlowLDPBoundary.lean](../FiniteMarkovProcesses/RelativeEntropy/FiniteStateJumpDirectionalFlowLDPBoundary.lean).

## Terminal path-LDP constructors

The common instance context is `{State : Type u} [Fintype State] [DecidableEq State]
[MeasurableSpace State] [MeasurableSingletonClass State] [TopologicalSpace State]
[DiscreteTopology State] [BorelSpace State] [Nonempty State]`, a
`FiniteStateMarkovGenerator State`, and `hDuration : 0 < duration` for real `duration`.
The source particle index is successor-indexed: `N = index + 1` with speed `N`.
Each result retains ordered off-diagonal flux and the same hybrid-BV carrier.

| Declaration | Exact additional input | Proved output and source |
| --- | --- | --- |
| [`rengerTheoremFourOneHybridBVLargeDeviationRepresentation`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVTheoremFourOneLargeDeviationRepresentation.lean) | `RengerTheoremFourOneInitialData State` | Representation for the original deterministic labelled initial configurations; indicator initial cost at the positive limiting density plus dynamic action. |
| [`rengerTheoremFourTwoHybridBVLargeDeviationRepresentation`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVTheoremFourTwoLargeDeviationRepresentation.lean) | `RengerTheoremFourTwoInitialData State` | Representation for the exact empirical-count-type mixture of positive-replica histories; supplied initial rate plus dynamic action. |
| [`rengerCorollaryFourSixteenHybridBVLargeDeviationRepresentation`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVCorollaryFourSixteenLargeDeviationRepresentation.lean) | `RengerCorollaryFourSixteenInitialData generator` | Representation for genuinely IID labelled particles from the specified invariant law; invariant relative-entropy initial cost plus dynamic action. |

The constructors fill `microscopicLaw_probability`, `observation_measurable`, `speed_pos`,
`speed_tendsto_atTop`, `topology_generates_measurableSpace`, `rate_good`, `upperBound`, and
`lowerBound`. Thus these values contain proof terms for path LDPs. Theorem 4.2's *initial* LDP
remains a premise in `initialData`; its *path* LDP is the output. No path-LDP premise is hidden
in a bibliographic tag.

| Proof stage | Declarations and modules | Premise boundary |
| --- | --- | --- |
| Deterministic initial LDP and source transport | `rengerTheoremFourOneInitialLaw_hasLargeDeviationUpperBound`, `rengerTheoremFourOneInitialLaw_hasLargeDeviationLowerBound`, `rengerTheoremFourOneAsTheoremFourTwoInitialData`, `rengerTheoremFourOneCountTypeHybridBVObservationLaw_eq_deterministicLaw` in the Theorem 4.1 terminal module | Derive initial bounds from supplied empirical convergence; exact observation law equality retains labelled configurations. |
| General empirical-initial upper bound | [`rengerTheoremFourTwoHybridBVObservationLaw_closedUpperBound`](../FiniteMarkovProcesses/RelativeEntropy/FiniteStateMarkovJumpHybridBVJointClosedUpperBound.lean) | Uses supplied good initial LDP, actual conditional laws, compact containment, and complete rate. |
| Theorem 4.2 microscopic upper transport | `rengerTheoremFourTwoHybridBV_hasLargeDeviationUpperBound` in the Theorem 4.2 terminal module | Measurable total-observation pushforward equality; same particle speed. |
| Theorem 4.1 lower bound | [`rengerTheoremFourOneDeterministicInitialHybridBV_hasLargeDeviationLowerBound`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVTheoremFourOneOpenLowerBound.lean) | Deterministic convergence and interior limiting density retained. |
| Theorem 4.2 lower bound | [`rengerTheoremFourTwoHybridBV_hasLargeDeviationLowerBound`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVTheoremFourTwoOpenLowerBound.lean) | Supplied initial lower bound and lower-boundary continuity retained. |
| Corollary lower bound | [`rengerCorollaryFourSixteenInvariantIIDHybridBV_hasLargeDeviationLowerBound`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVCorollaryFourSixteenOpenLowerBound.lean) | Invariant-IID source and its initial-data contract retained. |
| Complete-rate goodness | [`rengerTheoremFourOneHybridBVCompleteRate_isGoodRateFunction`, `rengerTheoremFourTwoHybridBVCompleteRate_isGoodRateFunction`, `rengerCorollaryFourSixteenHybridBVCompleteRate_isGoodRateFunction`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVCompleteRateCompactness.lean) | The corresponding theorem-specific initial contracts; compact finite sublevels of the actual complete rate. |

## Full-carrier effective evolution

Here the state context reduces to finite decidable measurable states with measurable singletons;
no topology, Borel, or explicit nonempty instance is required in the terminal zero-evolution
module. The duration is positive, the constant generator can have zero rates, and
`initialRate : FiniteStateProbabilityDensity State → ENNReal` is arbitrary.
It need not be good, continuous, finite everywhere, or derived from an initial random law.

| Declaration | Additional hypotheses | Result |
| --- | --- | --- |
| [`rengerExtendedPoissonRateCost_eq_zero_iff`](../FiniteMarkovProcesses/RelativeEntropy/RengerDirectionalFlowZeroRate.lean) | Only `flow expected : NNReal` | Extended scalar cost is zero iff flow equals expectation, including zero-reference boundary. |
| `rengerDirectionalFlowHybridBVDynamicRate_eq_zero_iff` in the same module | Positive duration; arbitrary full-carrier path | Zero iff admissible and generator flow holds a.e. |
| `rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff` in the same module | Arbitrary supplied initial cost | Zero iff admissible, lifted initial cost zero, and generator flow. |
| [`absolutelyContinuousOnInterval_rengerDirectionalFlowHybridBVDensityValue`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVForwardUniqueness.lean) | Admissible representation path and horizon in `[0,T)` | Derives coordinate absolute continuity from reconstruction; it is not a caller-supplied uniqueness field. |
| `ae_hasDerivAt_rengerDirectionalFlowHybridBVDensityValue_of_generatorFlow` in the same module | Admissibility and a.e. generator flow | Derives the common forward equation. |
| `rengerDirectionalFlowHybridBVPath_eq_of_generatorFlow_initialDensity` in the same module | Two admissible generator-flow paths with equal initial density | Literal equality of full hybrid paths. |
| [`finiteStateMarkovMeanHybridBVPath_completeRate_eq_initialRate`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVZeroRateEvolution.lean) | Initial finite probability density | Complete rate on the actual generated mean path equals its supplied initial cost. |
| `rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_exists_initialDensity` in the same module | Arbitrary full-carrier path | Complete zero iff actual mean evolution from some zero-cost initial density. |
| `finiteStateMarkovMeanHybridBVPath_initialDensity_injective` in the same module | Positive duration | Mean map is injective by exact initial-trace recovery. |
| `rengerDirectionalFlowHybridBVCompleteRate_eq_zero_iff_eq_meanPath` in the same module | Separately proved `∀ candidate, initialRate candidate = 0 ↔ candidate = initial` | Unique zero path is the actual mean from that initial density. |
| `exists_distinct_zeroRatePaths_twoState_zeroGenerator` in the same module | Concrete `Fin 2`, duration `1`, zero generator, zero initial cost | Two distinct full-carrier zero paths; controls unconditional uniqueness claims. |

The underlying forward theorem is
[`FiniteMarkovProcesses.Probability.finiteStateMarkov_eqOn_of_forwardEquation`](../FiniteMarkovProcesses/Probability/FiniteStateMarkovForwardUniqueness.lean).
It needs only finite state, the common generator, real coordinate functions absolutely continuous
on every strict subhorizon, their a.e. forward equations, and equal initial vectors. It concludes
equality on `[0,T)`. It does not require positive duration, nonnegative coordinates, normalization,
stationarity, or irreducibility. Its companion `finiteStateMarkov_l1_le_of_forwardEquation`
proves finite-coordinate L1 contraction on a closed interval with ordered endpoints.

These are deterministic zero-set and uniqueness results. A probability estimate requires its
own source law and probability theorem. An empty initial zero set yields no zero path; this map
does not classify positive-cost minimizers in that case.

## Quantitative bounds: deterministic and eventual

Import `FiniteMarkovProcesses.QuantitativeBounds` for these five generic modules and the
existing original-IID all-N strong-L1 estimate. The deterministic state context is only finite
decidable state; measurable-state and stationarity hypotheses are not required. Fix `T > 0`,
`epsilon ≥ 0`, `L ≥ 0`, and a generator with every escape rate at most `L`. The reference `q`
is an admissible representation path with that generator flow. Write `B=T L`,
`delta=sum_x |rho_p(0,x)-rho_q(0,x)|`, and `R=epsilon+sqrt(epsilon^2+4B epsilon)`.

| Declaration and module | Additional premises | Precise conclusion |
| --- | --- | --- |
| [`sum_abs_sub_le_two_mul_sqrt_of_rengerExtendedPoissonRateCost_le`](../FiniteMarkovProcesses/RelativeEntropy/PoissonRateHellinger.lean) | Finite nonnegative vectors, each total mass one; summed extended Poisson cost at most `ofReal(epsilon)`; `epsilon ≥ 0` | Their L1 distance is at most `2 sqrt(epsilon)`. No initial-cost identification is assumed implicitly. |
| `poissonRateBudgetModulus` in the same module | Real arguments | Defines the residual modulus `epsilon+sqrt(epsilon^2+4B epsilon)`; accompanying lemmas retain their nonnegative-budget hypotheses. |
| [`sum_abs_rengerDirectionalFlowHybridBVDensityValue_sub_le_initial_add_residual`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVFlowStability.lean) | Both paths admissible; reference generator flow; `0 ≤ t < T` | Density L1 error is at most actual initial error plus twice the integrated raw flow residual. |
| [`rengerDirectionalFlowHybridBVIntegratedFlowResidual_le_of_dynamicRate_le`](../FiniteMarkovProcesses/RelativeEntropy/RengerHybridBVRateStability.lean) | Arbitrary full-carrier `p` with dynamic rate at most `ofReal(epsilon)`; escape bound and nonnegativity as above | Derives admissibility and residual at most `R`; it does not assume competitor-flow boundedness. |
| `norm_rengerDirectionalFlowHybridBVToL1Path_sub_le_initial_add_rateModulus` in the same module | Same budget and an admissible same-generator-flow reference | Strong-L1 projection error at most `T[(1+B)delta+(3+2B)R]`. Initial error remains explicit. |
| `sum_rengerDirectionalFlowHybridBVDerivativeDifferenceVariation_le_initial_add_rateModulus` in the same module | Same hypotheses | Sum of actual signed derivative-difference variations at most `3[B delta+(1+2B)R]`; a deterministic finite-rate conclusion. |
| `rengerDirectionalFlowHybridBVPath_eq_of_dynamicRate_le_zero_initialDensity` in the same module | Zero dynamic budget and equal initial density | Literal full-hybrid equality, with zero escape allowed. |
| [`poissonRateBudgetModulus_le_mul_sqrt`](../FiniteMarkovProcesses/RelativeEntropy/PoissonRateBudgetCoercivity.lean) | `0 ≤ epsilon ≤ 1`, `B ≥ 0` | `R(epsilon,B) ≤ 2(1+B)sqrt(epsilon)`. |
| `mul_sqrt_poissonRateRadiusBudget_le` in the same module | Positive constant `C` and radius `r` | For `budget=min(1,(r/(2C))^2)`, `C sqrt(budget) ≤ r/2`; positivity and unit bound are proved separately. |
| [`HasLargeDeviationUpperBound.limsup_le_neg_of_isClosed_of_le_rate`](../FiniteMarkovProcesses/RelativeEntropy/LargeDeviationConcentration.lean) | An existing LDP upper bound; a closed event; its pointwise rate at least an extended nonnegative level | Derives the corresponding log-limsup event bound. It assumes the upper bound, rather than proving an LDP for arbitrary laws. |
| `eventually_probability_le_exp_of_limsup_log_div_le` in the same module | Probabilities at most one; strictly positive speeds; log-limsup at most `-e`; real `a<e` | Eventual mass at most `exp(-speed*a)`, with an existential cutoff. Positive `a` and divergent speed give decay. |
| `finitePrefixEventLaw_not_forall_le_exp` in the same module | Positive exponent; normalized Boolean finite-prefix family defined there | Refutes an all-index exponential bound despite log-limsup bottom. |

The rate-stability module also bounds density and cumulative flow on `[0,T)`, integrated
ordered-flow error, and recovered terminal-left density and flow traces. Their exact formulas
appear in the path guide. A complete-rate budget does not give budget-dependent control of
`delta` for an arbitrary supplied initial cost without a separate initial-cost estimate. No deterministic finite-rate hypothesis is imposed samplewise
on microscopic empirical paths by these results.

The existing original-IID theorem remains distinct: it proves an **all-N strong-L1 path-event
Chernoff bound** with a supplied capped tilt, arbitrary initial PMF, and its actual unconditional
mean. None of the five added modules supplies a generic executable confidence budget, optimizes
the tilt into a new radius-only envelope, or proves particle derivative-TV concentration.

## Probability bound and endpoint bridge

| Declaration | Hypotheses | Precise output |
| --- | --- | --- |
| [`FiniteMarkovProcesses.Probability.measure_iid_totalHybridBVObservation_deviation_le_exponential`](../FiniteMarkovProcesses/Probability/FiniteStateMarkovIIDHybridExponential.lean) | Finite decidable nonempty measurable states with measurable singletons; arbitrary initial PMF; generator; positive NNReal duration; successor index; `0 ≤ tilt ≤ 1/(4(uniformizationRate*duration+1))`; arbitrary real radius | Explicit exponential upper bound for the strong-L1 norm event around the actual unconditional mean under the original IID product law. Unbounded count tails retained; no stationarity requirement. |
| [`PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowPath_endpoint_ae`](../FiniteMarkovProcesses/Probability/FiniteJumpHistoryDirectionalFlowEndpointConvention.lean) | A positive finite family of complete histories, with the finite/decidable state instances in its statement | Componentwise a.e. physical-time equality of strict-before and càdlàg empirical observations; not equality at every jump time. |
| [`finiteStateMarkovJumpInvariantIIDMacroscopicObservation_eq_before`](../FiniteMarkovProcesses/RelativeEntropy/FiniteStateJumpDirectionalFlowLDPBoundary.lean) | A quotient observation respecting componentwise a.e. equality | Exact equality after that observation; original interval and endpoint conventions remain explicit. |

The finite-IID simplex exponential estimates and Sanov initial-rate proofs are imported from
the Sanov partition; the original-IID **path** confidence bound above also treats density
randomness, integrated physical time, and unbounded cumulative-count coordinates. Its formula
and interpretation appear in [path-large-deviations.md](path-large-deviations.md).

## Dependency and attribution boundary

`PathLargeDeviations.lean` imports the Theorem 4.1 and Corollary 4.16 terminal modules and the
IID path exponential bound. Theorem 4.2 is reached through their explicit dependency graph.
`EffectiveEvolution.lean` imports the terminal zero-rate evolution module. In the planned graph,
including each root itself, the Theorem 4.1, Theorem 4.2, Corollary 4.16, zero-evolution, and IID
path exponential roots reach respectively 259, 256, 261, 164, and 131 non-Mathlib module nodes.
These counts include public external dependencies where reached and do not count Mathlib's
internal closure. They are static graph facts, not compile certificates.

The only separately packaged public mathematical dependency in the plan is
`MeasureDiscrimination.ProductDiscrimination`; the mathematical closure contains generic
finite-state probability and analysis. The retained action belongs to Renger (2018); entropy equality
and finite-state forward uniqueness are classical (see Norris, *Markov Chains*, Section 2.8).
The scope is finite-state probability, analysis, and the displayed rate/evolution identities.

## Adversarial audit of the terminal interfaces

A generic `DensityFluxLargeDeviationRepresentation` value can contain arbitrary laws and rates
satisfying its fields. Its type, an existential over it, or a provenance label alone does not
identify Renger's microscopic source or functional. The **named constructor** fixes those
projections definitionally. The example checks that the Theorem 4.1 constructor's
`microscopicLaw` is the original deterministic-configuration law, not merely that the generic
interface is inhabited.

The terminal constructors have no input path-LDP field, no input path good-rate theorem, and no
input representation witness. Each takes only the common instances, generator, positive horizon,
and the stated initial-data record. The generator record contains only nonnegative rates and
zero diagonal; finite-state boundedness and escape rates are derived. The corollary's stationary
record contains nonnegative weights, strict coordinate positivity, total mass one, and incoming
flow equal to escape flow. Its uniqueness premise is literally
`∀ other : FiniteStateMarkovStationaryDistribution generator, other.pmf = stationary.pmf`.
Their carried interfaces resolve as follows:

| Interface field | How the named constructors fill it |
| --- | --- |
| `microscopicLaw` | Defined from the exact deterministic configuration, supplied initial count-type mixture, or specified invariant-IID product law. Theorem 4.2 chooses the canonical labelled representative of each count type; it does not assert all labelled initial laws coincide. |
| `microscopicLaw_probability` | Proved normalization of these generated laws. Theorem 4.2 uses the supplied **initial** count-type probability normalization. Where the lower law API accepts a normalization witness, the constructors supply the proved `finiteStateMarkovJumpDensityIsNormalized_of_nonnegative`. |
| `observation`, `observation_measurable` | The fixed total positive-replica hybrid-BV observation and its measurability theorem. No caller chooses a convenient surrogate observation. |
| `speed`, `speed_pos`, `speed_tendsto_atTop` | Defined successor particle speed `N=index+1`, proved positive and divergent. |
| `rateData` | The defined complete Renger rate: recovered initial cost, dynamic action, zero additional boundary cost, infinite cost off the deterministic admissibility predicate. Local-integrand measurability is proved, not assumed as a terminal argument. |
| `topology_generates_measurableSpace` | The hybrid carrier's constructed Borel measurable-space equality. |
| `rate_good` | Derived compact complete-rate sublevels. Theorem 4.2 uses supplied **initial** rate goodness; Theorem 4.1 proves the singleton-indicator initial goodness, and Corollary 4.16 derives initial goodness from finite-IID relative entropy. |
| `upperBound` | Proved closed-set path bound. Theorem 4.2 combines conditional dynamical bounds, the supplied initial upper bound, and compact containment; Theorem 4.1 and Corollary 4.16 transport that bound by exact observation-law identities. |
| `lowerBound` | Proved open-set path bound. Theorem 4.1 proves the deterministic source estimate; Theorem 4.2 combines conditional dynamical lower estimates and selected empirical atoms with the supplied initial lower bound, then extends to lower-boundary initial densities by the supplied boundary continuity; Corollary 4.16 transports the resulting bound to its actual IID law. |
| `provenance` | The fixed theorem label; an attribution field with no mathematical discharge role. |

Theorem 4.2's boundary continuity premise means: for **every** lower-boundary simplex point and
**every** coordinatewise-convergent sequence of strictly positive simplex points, the initial
rates converge in `ENNReal` to the rate at that boundary point. It is stronger than a one-sided
inequality or the existence of a single recovery sequence. Its initial LDP premises apply to
the exact supplied simplex pushforward laws at successor particle speed.

`FiniteIntervalHybridBVPath` carries native L1-plus-derivative data, bounded-variation proof,
and a compatible càdlàg Stieltjes realization. It contains no probability law or LDP bound.
`DensityFluxPathRateData` carries deterministic observations, local action, measurability,
costs, and admissibility; it contains no probabilistic upper/lower bounds. Admissibility is a
**domain predicate**, not a premise that all microscopic paths have zero action. Pointwise lower
lemmas' finite-rate and neighborhood premises are discharged by case analysis when proving the
universal open-set bound; they are not additional terminal hypotheses.

The terminal constructors package **derived** path results, and their bodies themselves are
assembly rather than new independent dynamical proofs. The generic representation and initial
data structures are contracts. `rengerTheoremFourOneAsTheoremFourTwoInitialData` and
`rengerInvariantIIDInitialLargeDeviationData` package their separately proved initial results.
The corollary's `stationary_unique` proof remains required by its input record, although the
assembled bounds use the supplied positive stationary law and do not consume that uniqueness
field separately. This audit concerns statements and proof dependencies; fresh extraction
compilation, lint, and axiom verification remain pending.
