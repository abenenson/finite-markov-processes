# Finite-state continuous-time Markov processes

Import `FiniteMarkovProcesses.CTMC`. Its 65 extracted modules contain no the library definitions.
They cover finite-state jump processes on a finite nonnegative observation horizon, with an
unbounded finite event count. The physical history law records the initial state, all actual
jumps, and the final dwell. Self-events of a uniformized construction are removed measurably.
Probability declarations use the namespace `FiniteMarkovProcesses.Probability`; action, KL, and
Fisher declarations use `FiniteMarkovProcesses.InformationTheory`.

## Main guarantees and hypotheses

| Result | Public declaration | Hypotheses that matter |
| --- | --- | --- |
| Normalized Gillespie law equals the physical jump density | `finiteStateMarkovStoppedHistoryMeasure_eq_jumpDensityMeasure` | A finite measurable state space with measurable singletons, a PMF initial law, nonnegative off-diagonal rates with zero diagonal, and `0 ≤ T`. Absorbing rows are included. |
| Physical density has total mass one | `finiteStateMarkovJumpDensityIsNormalized_of_nonnegative` | The same hypotheses; normalization is proved from the stopped generative construction. |
| Homogeneous uniformization removes exactly the virtual self-events | `map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure` | A finite state space with decidable equality and measurable singletons, and a nonnegative duration. The uniformization rate and transition law are constructed from the generator. |
| Time-dependent deletion gives the physical density | `map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure` | A finite state space with decidable equality and measurable singletons; `FiniteStateTimeDependentMarkovRate`: measurable rates in physical time, zero diagonal, and a supplied global finite bound on every escape row; `0 ≤ duration`. |
| Time-dependent physical law has total mass one | `finiteStateTimeDependentMarkovJumpDensityMeasure_univ` | The same bounded measurable rate-family hypotheses. Continuity and differentiability in physical time are not required. |
| Path likelihood ratio and absolute continuity | `rnDeriv_finiteStateMarkovJumpDensityMeasure_eq_exp_logAction` | Candidate and reference initial PMFs have identical support; generators have identical directed support. The density ratio equals the exponential of the full jump-plus-dwell action almost everywhere. |
| Integral fluctuation identity | `lintegral_exp_neg_finiteStateMarkovJumpLogAction` | Common initial and directed rate support, and both normalization premises. At a nonnegative horizon those premises follow from the normalization theorem above. |
| Expected action equals finite KL | `integral_finiteStateMarkovJumpLogAction_eq_klDiv` | Common support, both normalization premises, and integrability of the complete action. |
| Stationary trajectory KL is duration times the full relative-entropy rate | `finiteStateMarkovTrajectoryKlDiv_toReal_eq_stationaryRelativeEntropyRate` | Candidate stationary distribution, same candidate/reference initial law, common directed support, and nonnegative duration. The reference generator need not preserve the candidate stationary distribution. |
| Trajectory Fisher response | `StationaryTrajectoryAffineChart.hasDerivAt_trajectoryKlDivToRealDerivative_zero` | An explicit affine channel chart identifying generator equality at zero, local common support, channel weights, and the entire stationary relative-entropy rate. The parameter indexes neighboring generators. |

The homogeneous action includes the initial log ratio, every directed jump log ratio, and the
integrated escape-rate difference. The Fisher statement is a local second derivative of complete
trajectory KL at generator equality. Its chart's rate-identification field is an explicit premise.
These results do not assert countable-state or unbounded-rate extensions, nor a global identity
between the Fisher quadratic form and the directed trajectory action. Time-dependent action and
large-deviation results belong to the separately documented package surfaces.

`FiniteMarkovProcessesExamples.CTMC` gives a unit-rate two-state chain, its normalized density and
stopped-law equality, and a fluctuation identity comparing it with a double-rate chain over
duration two. The example proves common support and supplies both normalization premises. It also
applies the general time-dependent normalization theorem. All theorem assumptions are visible in
the Lean declarations.

## Classical attribution and extraction

The continuous-time Markov-chain construction, exponential holding times, uniformization,
likelihood-ratio identities, relative entropy, and Fisher information are classical mathematics.
The implementation is a Lean formalization, not a claim of mathematical priority. Relevant
classical sources include A. Jensen, “Markoff chains as an aid in the study of Markoff processes,”
*Skandinavisk Aktuarietidskrift* **36** (1953), 87–91; D. T. Gillespie, “A general method for
numerically simulating the stochastic time evolution of coupled chemical reactions,” *Journal
of Computational Physics* **22** (1976), 403–434; S. Kullback and R. A. Leibler, “On information
and sufficiency,” *Annals of Mathematical Statistics* **22** (1951), 79–86; and R. A. Fisher,
“Theory of statistical estimation,” *Proceedings of the Cambridge Philosophical Society* **22**
(1925), 700–725. The integral fluctuation statement here is the normalized likelihood-ratio
identity under the stated common-support hypotheses.

The 65 modules are extracted from `the standalone mathematical library` at commit
`recorded-source-baseline`. `source-plan.json` records each exact source path,
source SHA-256, target module, and ownership. Extraction replaces `MathlibExtensions` by
`FiniteMarkovProcesses` in qualified namespaces and imports, and shortens the relative-entropy
module prefix to `FiniteMarkovProcesses.RelativeEntropy`; mathematical statements and proofs
are preserved. The CTMC module closure imports only Mathlib. The unified package also pins the
public `finite-markov-kernels` and `measure-discrimination` dependencies for its other mathematical
surfaces.
