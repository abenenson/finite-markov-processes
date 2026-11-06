/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1DerivativeTopology
import FiniteMarkovProcesses.RelativeEntropy.DensityFluxLargeDeviationRepresentation
import FiniteMarkovProcesses.RelativeEntropy.FiniteStateProbabilityDensity
import FiniteMarkovProcesses.RelativeEntropy.PoissonRateDiscrimination
import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensityLargeDeviation
import FiniteMarkovProcesses.Probability.FiniteIIDPositiveEmpiricalTypeLaw
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryDirectionalFlowEndpointConvention
import FiniteMarkovProcesses.Probability.FiniteStateMarkovGeneratorMatrix
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpDensityIdentification
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpPositiveReplicaHybridBVObservation
import FiniteMarkovProcesses.Probability.FiniteStateMarkovPartialConjugateLaw

/-!
# Finite-state directional-flow LDP boundary for independent jump particles

This module records the exact Renger 2018 provenance and assembles every internally proved finite
source component of the invariant-i.i.d. independent-particle route.  It also freezes the extended
local rate, its zero-rate boundary convention, the open-interval endpoint bridge, and formal data
types for the distinct initial hypotheses of Theorems 4.1 and 4.2.

The hybrid-BV modules construct the paper's `L1` equivalence classes, distributional
derivatives, recovered traces, hybrid topology, measurable full-carrier observation,
admissible domain, dynamic and theorem-specific complete rates, source laws, empirical-
configuration lifts, and the closed-upper/open-lower bounds for each published initial regime.
This boundary module contains the common finite source data and an enumeration of the
representation components. The terminal theorem-specific modules assemble the full
representations.

## Main results

- `rengerExtendedPoissonRateCost`: the extended one-channel rate with explicit zero boundary.
- `rengerDirectionalFlowLocalRate`: ordered off-diagonal density--flow rate integrand.
- `RengerTheoremFourOneInitialData`, `RengerTheoremFourTwoInitialData`, and
  `RengerCorollaryFourSixteenInitialData`: formal, distinct initial-data contracts rather than
  bibliographic tags.
- `finiteStateMarkovJumpInvariantIIDMicroscopicLaw`: exact normalized successor-indexed source.
- `finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw`: exact normalized full-carrier
  hybrid-BV pushforward law.
- `finiteStateMarkovJumpInvariantIIDMacroscopicObservation_eq_before`: exact endpoint bridge for
  every quotient map respecting componentwise almost-everywhere equality.
-/

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u v

/-- The three distinct initial-data results in Renger's independent-particle theorem family. -/
inductive Renger2018DirectionalFlowTheoremLabel
  | theoremFourOne
  | theoremFourTwo
  | corollaryFourSixteen
  deriving DecidableEq, Repr

/-- The initial hypothesis attached to one published theorem label. -/
inductive Renger2018DirectionalFlowInitialHypothesis
  | deterministicEmpiricalLimitPositiveInEveryCoordinate
  | independentInitialRateLeftContinuousAtLowerBoundary
  | independentIdenticallyDistributedFromUniqueInvariantLaw
  deriving DecidableEq, Repr

/-- The theorem-specific initial hypothesis; none of the three regimes is silently broadened. -/
def renger2018DirectionalFlowInitialHypothesis :
    Renger2018DirectionalFlowTheoremLabel → Renger2018DirectionalFlowInitialHypothesis
  | .theoremFourOne => .deterministicEmpiricalLimitPositiveInEveryCoordinate
  | .theoremFourTwo => .independentInitialRateLeftContinuousAtLowerBoundary
  | .corollaryFourSixteen => .independentIdenticallyDistributedFromUniqueInvariantLaw

/-- An ordered transition between distinct states.  Using this subtype prevents diagonal flow
coordinates from entering the published local action unnoticed. -/
abbrev FiniteStateOrderedOffDiagonalTransition
    (State : Type u) [_instDecidableEq : DecidableEq State] :=
  { transition : State × State // transition.1 ≠ transition.2 }

/-- A finite family of open-interval continuous tests, one for every ordered off-diagonal jump
channel. This source-neutral test type is shared by the hybrid dual and its exponential tilt. -/
abbrev RengerDirectionalFlowHybridBVDualTest
    (State : Type u) [_instFintype : Fintype State] [DecidableEq State] (duration : ℝ) :=
  FiniteStateOrderedOffDiagonalTransition State →
    FiniteOpenIntervalVanishingContinuousTest duration

/-- Reindex an ordered off-diagonal transition by its target and a distinct source. -/
def finiteStateIncomingTransitionEquiv
    (State : Type u) [DecidableEq State] :
    (Σ target : State, {source : State // source ≠ target}) ≃
      FiniteStateOrderedOffDiagonalTransition State where
  toFun transition :=
    ⟨(transition.2.1, transition.1), transition.2.2⟩
  invFun transition :=
    ⟨transition.1.2, ⟨transition.1.1, transition.2⟩⟩
  left_inv := by
    rintro ⟨target, source, hSource⟩
    rfl
  right_inv := by
    rintro ⟨⟨source, target⟩, hTransition⟩
    rfl

/-- Reindex an ordered off-diagonal transition by its source and a distinct target. -/
def finiteStateOutgoingTransitionEquiv
    (State : Type u) [DecidableEq State] :
    (Σ source : State, {target : State // target ≠ source}) ≃
      FiniteStateOrderedOffDiagonalTransition State where
  toFun transition :=
    ⟨(transition.1, transition.2.1), transition.2.2.symm⟩
  invFun transition :=
    ⟨transition.1.1, ⟨transition.1.2, transition.2.symm⟩⟩
  left_inv := by
    rintro ⟨source, target, hTarget⟩
    rfl
  right_inv := by
    rintro ⟨⟨source, target⟩, hTransition⟩
    rfl

/-- Summing incoming channels over every target counts every ordered off-diagonal transition
exactly once. -/
theorem sum_incomingTransition_eq_sum_orderedOffDiagonalTransition
    {Value : Type*} [AddCommMonoid Value]
    {State : Type u} [Fintype State] [DecidableEq State]
    (value : FiniteStateOrderedOffDiagonalTransition State → Value) :
    (∑ target, ∑ source : {source : State // source ≠ target},
      value ⟨(source, target), source.property⟩) = ∑ transition, value transition := by
  have hValue :
      (fun transition : (Σ target : State, {source : State // source ≠ target}) =>
        value (finiteStateIncomingTransitionEquiv State transition)) =
      (fun transition =>
        value ⟨(transition.2.1, transition.1), transition.2.2⟩) := by
    funext transition
    rfl
  have hSum := (finiteStateIncomingTransitionEquiv State).sum_comp value
  rw [hValue] at hSum
  simpa only [Fintype.sum_sigma] using hSum

/-- Summing outgoing channels over every source counts every ordered off-diagonal transition
exactly once. -/
theorem sum_outgoingTransition_eq_sum_orderedOffDiagonalTransition
    {Value : Type*} [AddCommMonoid Value]
    {State : Type u} [Fintype State] [DecidableEq State]
    (value : FiniteStateOrderedOffDiagonalTransition State → Value) :
    (∑ source, ∑ target : {target : State // target ≠ source},
      value ⟨(source, target), target.property.symm⟩) = ∑ transition, value transition := by
  have hValue :
      (fun transition : (Σ source : State, {target : State // target ≠ source}) =>
        value (finiteStateOutgoingTransitionEquiv State transition)) =
      (fun transition =>
        value ⟨(transition.1, transition.2.1), transition.2.2.symm⟩) := by
    funext transition
    rfl
  have hSum := (finiteStateOutgoingTransitionEquiv State).sum_comp value
  rw [hValue] at hSum
  simpa only [Fintype.sum_sigma] using hSum

/-- Theorem 4.1's deterministic initial configurations, their empirical densities, and their
coordinate-positive limit.  The successor indexing keeps every particle count positive. -/
structure RengerTheoremFourOneInitialData
    (State : Type u) [Fintype State] [DecidableEq State] where
  /-- Supplied deterministic initial configuration for each positive replica count. -/
  initialState : (successorIndex : ℕ) → Fin (successorIndex + 1) → State
  /-- Supplied sequence of empirical initial densities. -/
  empiricalInitialDensity : ℕ → FiniteStateProbabilityDensity State
  /-- Supplied equality of each empirical weight with its normalized initial-state count. -/
  empiricalInitialDensity_eq : ∀ successorIndex state,
    (empiricalInitialDensity successorIndex).weight state =
      ((Finset.univ.filter
        (fun replica => initialState successorIndex replica = state)).card : NNReal) /
        (successorIndex + 1 : NNReal)
  /-- Supplied limiting density for the initial empirical-density sequence. -/
  limitingDensity : FiniteStateProbabilityDensity State
  /-- Supplied strict positivity of every coordinate of the limiting density. -/
  limitingDensity_interior : limitingDensity.IsInterior
  /-- Supplied coordinatewise convergence of the empirical initial densities to the limit. -/
  empiricalInitialDensity_tendsto :
    FiniteStateProbabilityDensity.TendstoCoordinatewise
      empiricalInitialDensity limitingDensity

/-- Theorem 4.1's deterministic initial cost: zero only at the limiting empirical density and
infinite everywhere else. -/
noncomputable def rengerTheoremFourOneInitialRate
    {State : Type u} [Fintype State] [DecidableEq State]
    (initialData : RengerTheoremFourOneInitialData State)
    (density : FiniteStateProbabilityDensity State) : ENNReal := by
  classical
  exact if density = initialData.limitingDensity then 0 else ⊤

/-- The deterministic initial rate vanishes at the limiting density. -/
@[simp] theorem rengerTheoremFourOneInitialRate_at_limitingDensity
    {State : Type u} [Fintype State] [DecidableEq State]
    (initialData : RengerTheoremFourOneInitialData State) :
    rengerTheoremFourOneInitialRate initialData initialData.limitingDensity = 0 := by
  simp [rengerTheoremFourOneInitialRate]

/-- Every other density has infinite deterministic initial cost. -/
theorem rengerTheoremFourOneInitialRate_of_ne
    {State : Type u} [Fintype State] [DecidableEq State]
    (initialData : RengerTheoremFourOneInitialData State)
    {density : FiniteStateProbabilityDensity State}
    (hDensity : density ≠ initialData.limitingDensity) :
    rengerTheoremFourOneInitialRate initialData density = ⊤ := by
  simp [rengerTheoremFourOneInitialRate, hDensity]

/-- Theorem 4.2's random empirical initial configurations, their induced simplex laws, their own
particle-number-speed LDP, and the additional lower-boundary continuity condition. The explicit
finite empirical count-type law canonically determines a labelled representative configuration and
prevents an
arbitrary off-lattice simplex law from masquerading as an `n + 1`-particle empirical initial
condition. -/
structure RengerTheoremFourTwoInitialData
    (State : Type u) [Fintype State] [DecidableEq State] where
  /-- Supplied sequence of empirical initial-density laws. -/
  initialLaw : ℕ → Measure (FiniteStateProbabilityDensity State)
  /-- Supplied probability normalization of every initial-density law. -/
  initialLaw_probability : ∀ sampleSize, IsProbabilityMeasure (initialLaw sampleSize)
  /-- Supplied law on positive-replica empirical count types at each sample-size index. -/
  initialEmpiricalTypeLaw :
    (sampleSize : ℕ) → Measure (FiniteIIDPositiveEmpiricalType State sampleSize)
  /-- Supplied probability normalization of every empirical count-type law. -/
  initialEmpiricalTypeLaw_probability :
    ∀ sampleSize, IsProbabilityMeasure (initialEmpiricalTypeLaw sampleSize)
  /-- Supplied whole-law equality with the probability-density pushforward of the count-type
  law. -/
  initialLaw_eq_map_probabilityDensity : ∀ sampleSize,
    initialLaw sampleSize = Measure.map
      FiniteIIDPositiveEmpiricalType.probabilityDensity
        (initialEmpiricalTypeLaw sampleSize)
  /-- Supplied initial rate function on the finite probability-density simplex. -/
  initialRate : FiniteStateProbabilityDensity State → ENNReal
  /-- Supplied compatibility of the simplex topology with its measurable space. -/
  topology_generates_measurableSpace :
    TopologyGeneratesMeasurableSpace (FiniteStateProbabilityDensity State)
  /-- Supplied goodness of the initial rate function. -/
  initialRate_good : IsGoodRateFunction initialRate
  /-- Supplied particle-number-speed large-deviation upper bound for the initial laws. -/
  initialUpperBound : HasLargeDeviationUpperBound
    (scaledEventLogProbability initialLaw (fun _ => id)
      FiniteMarkovProcesses.Probability.finiteIIDPositiveSampleSpeed) initialRate
  /-- Supplied particle-number-speed large-deviation lower bound for the initial laws. -/
  initialLowerBound : HasLargeDeviationLowerBound
    (scaledEventLogProbability initialLaw (fun _ => id)
      FiniteMarkovProcesses.Probability.finiteIIDPositiveSampleSpeed) initialRate
  /-- Supplied continuity of the initial rate at the lower boundary from the simplex interior. -/
  initialRate_leftContinuousAtLowerBoundary :
    FiniteStateProbabilityDensity.InitialRateIsLeftContinuousAtLowerBoundary initialRate

/-- Exact theorem-labelled provenance.  Bibliographic metadata and mathematical conventions are
fixed by projections below rather than accepted as caller-supplied strings. -/
structure Renger2018DirectionalFlowProvenance where
  /-- Supplied published theorem label selecting this record's initial-data regime. -/
  theoremLabel : Renger2018DirectionalFlowTheoremLabel
  deriving DecidableEq, Repr

namespace Renger2018DirectionalFlowProvenance

/-- Published author name. -/
def author (_ : Renger2018DirectionalFlowProvenance) : String :=
  "D. R. Michiel Renger"

/-- Published article title. -/
def title (_ : Renger2018DirectionalFlowProvenance) : String :=
  "Flux large deviations of independent and reacting particle systems, " ++
    "with implications for macroscopic fluctuation theory"

/-- Published journal. -/
def journal (_ : Renger2018DirectionalFlowProvenance) : String :=
  "Journal of Statistical Physics 172 (2018)"

/-- Published DOI. -/
def doi (_ : Renger2018DirectionalFlowProvenance) : String :=
  "10.1007/s10955-018-2083-0"

/-- Exact initial-data hypothesis selected by the theorem label. -/
def initialHypothesis (provenance : Renger2018DirectionalFlowProvenance) :
    Renger2018DirectionalFlowInitialHypothesis :=
  renger2018DirectionalFlowInitialHypothesis provenance.theoremLabel

/-- The published flux carrier retains ordered off-diagonal coordinates. -/
def orderedFlowConvention (_ : Renger2018DirectionalFlowProvenance) : String :=
  "ordered off-diagonal source-target pairs"

/-- The paper's cumulative flux uses the open physical interval `(0,t)`. -/
def sourceEndpointConvention (_ : Renger2018DirectionalFlowProvenance) : String :=
  "cumulative jumps in the open interval (0,t)"

/-- The repository's exact complete-history observation uses its càdlàg at-or-before convention. -/
def repositoryEndpointConvention (_ : Renger2018DirectionalFlowProvenance) : String :=
  "cumulative jumps at or before t"

/-- The published macroscopic topology, recorded as provenance rather than asserted as a Lean
instance. -/
def hybridTopology (_ : Renger2018DirectionalFlowProvenance) : String :=
  "strong L1 path convergence plus vague convergence of distributional derivatives"

/-- The published carrier and representative convention. -/
def pathCarrierConvention (_ : Renger2018DirectionalFlowProvenance) : String :=
  "BV((0,T); P(State) x l1_+(State x State)) equivalence classes with " ++
    "cadlag representatives and recovered boundary traces"

/-- The exact local rate formula. -/
def localRateFormula (_ : Renger2018DirectionalFlowProvenance) : String :=
  "integral sum_(x!=y) s(flowDerivative_xy | density_x * Q_xy)"

/-- Corollary 4.16 provenance used by the invariant-i.i.d. source constructor below. -/
def corollaryFourSixteen : Renger2018DirectionalFlowProvenance :=
  ⟨.corollaryFourSixteen⟩

end Renger2018DirectionalFlowProvenance

/-- Extended Poisson relative-entropy cost `s(flow | expected)`.  The zero-rate boundary remains
visible: zero flow against zero expectation costs zero, while positive flow against zero expectation
costs infinity. -/
noncomputable def rengerExtendedPoissonRateCost
    (flow expected : NNReal) : ENNReal :=
  if expected = 0 then
    if flow = 0 then 0 else ⊤
  else ENNReal.ofReal
    (poissonRateDiscrimination (flow : ℝ) (expected : ℝ))

/-- The zero-flow, zero-expected-rate boundary has zero cost. -/
theorem rengerExtendedPoissonRateCost_zero_zero :
    rengerExtendedPoissonRateCost 0 0 = 0 := by
  simp [rengerExtendedPoissonRateCost]

/-- Positive flow through a zero expected-rate channel has infinite cost. -/
theorem rengerExtendedPoissonRateCost_pos_zero
    {flow : NNReal} (hFlow : 0 < flow) :
    rengerExtendedPoissonRateCost flow 0 = ⊤ := by
  simp [rengerExtendedPoissonRateCost, hFlow.ne']

/-- Finite one-channel cost forbids nonzero flow against zero expected intensity. -/
theorem flow_eq_zero_of_expected_eq_zero_of_rengerExtendedPoissonRateCost_ne_top
    {flow expected : NNReal} (hExpected : expected = 0)
    (hCost : rengerExtendedPoissonRateCost flow expected ≠ ⊤) :
    flow = 0 := by
  subst expected
  by_contra hFlow
  have hFlowPositive : 0 < flow := pos_iff_ne_zero.mpr hFlow
  exact hCost (rengerExtendedPoissonRateCost_pos_zero hFlowPositive)

/-- At positive expected rate, the extended cost is the ordinary finite Poisson discrimination. -/
theorem rengerExtendedPoissonRateCost_of_expected_pos
    (flow : NNReal) {expected : NNReal} (hExpected : 0 < expected) :
    rengerExtendedPoissonRateCost flow expected =
      ENNReal.ofReal
        (poissonRateDiscrimination (flow : ℝ) (expected : ℝ)) := by
  simp [rengerExtendedPoissonRateCost, hExpected.ne']

/-- The exponential dual evaluation lies below the extended one-channel cost, including the
zero-expected-rate boundary. -/
theorem ofReal_poissonExponentialDualEvaluation_le_rengerExtendedPoissonRateCost
    (flow expected : NNReal) (exponent : ℝ) :
    ENNReal.ofReal
        ((flow : ℝ) * exponent - (expected : ℝ) * (Real.exp exponent - 1)) ≤
      rengerExtendedPoissonRateCost flow expected := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · simp [rengerExtendedPoissonRateCost, hFlow]
  have hExpectedPositive : 0 < expected := pos_iff_ne_zero.mpr hExpected
  rw [rengerExtendedPoissonRateCost_of_expected_pos flow hExpectedPositive]
  exact ENNReal.ofReal_le_ofReal
    (poissonExponentialDualEvaluation_le_discrimination
      (show 0 ≤ (flow : ℝ) by positivity)
      (show 0 < (expected : ℝ) by exact_mod_cast hExpectedPositive))

/-- The extended one-channel cost controls the observed flow, uniformly through the zero-rate
boundary, up to the explicit reference-rate correction. -/
theorem flow_le_rengerExtendedPoissonRateCost_add_referenceCorrection
    (flow expected : NNReal) :
    (flow : ENNReal) ≤
      rengerExtendedPoissonRateCost flow expected +
        ENNReal.ofReal ((Real.exp 1 - 1) * (expected : ℝ)) := by
  by_cases hExpected : expected = 0
  · subst expected
    by_cases hFlow : flow = 0
    · subst flow
      simp [rengerExtendedPoissonRateCost]
    · simp [rengerExtendedPoissonRateCost, hFlow]
  have hExpectedPos : 0 < expected := pos_iff_ne_zero.mpr hExpected
  have hDiscriminationNonnegative :
      0 ≤ poissonRateDiscrimination (flow : ℝ) (expected : ℝ) :=
    poissonRateDiscrimination_nonneg (by positivity) (by exact_mod_cast hExpectedPos)
  have hExp : 1 ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp 1]
  have hCorrectionNonnegative :
      0 ≤ (Real.exp 1 - 1) * (expected : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hExp) (by positivity)
  rw [rengerExtendedPoissonRateCost_of_expected_pos flow hExpectedPos,
    ← ENNReal.ofReal_add hDiscriminationNonnegative hCorrectionNonnegative]
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal
    (lawIntensity_le_poissonRateDiscrimination_add_referenceCorrection
      (show 0 ≤ (flow : ℝ) by positivity)
      (show 0 < (expected : ℝ) by exact_mod_cast hExpectedPos))

/-- The extended one-channel cost is measurable in its observed and expected intensities,
including both branches at zero expected intensity. -/
theorem measurable_rengerExtendedPoissonRateCost :
    Measurable fun intensities : NNReal × NNReal =>
      rengerExtendedPoissonRateCost intensities.1 intensities.2 := by
  unfold rengerExtendedPoissonRateCost
  apply Measurable.ite
  · exact measurable_snd (α := NNReal) (β := NNReal) (measurableSet_singleton 0)
  · apply Measurable.ite
    · exact measurable_fst (α := NNReal) (β := NNReal) (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  · unfold poissonRateDiscrimination
    fun_prop

/-- Renger's local rate on raw nonnegative density coordinates.  Simplex normalization is an
admissibility condition on the hybrid path, not hidden inside evaluation of the integrand. -/
noncomputable def rengerDirectionalFlowLocalRateRaw
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (density : State → NNReal)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal) :
    ENNReal :=
  ∑ transition,
    rengerExtendedPoissonRateCost
      (directionalFlowDerivative transition)
      (density transition.1.1 * generator.rate transition.1.1 transition.1.2)

/-- Finite local directional-flow action preserves every zero expected-intensity channel. -/
theorem directionalFlow_eq_zero_of_expected_eq_zero_of_rengerDirectionalFlowLocalRateRaw_ne_top
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (density : State → NNReal)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hExpected :
      density transition.1.1 * generator.rate transition.1.1 transition.1.2 = 0)
    (hLocalRate :
      rengerDirectionalFlowLocalRateRaw generator density directionalFlowDerivative ≠ ⊤) :
    directionalFlowDerivative transition = 0 := by
  have hChannelCostLe :
      rengerExtendedPoissonRateCost
          (directionalFlowDerivative transition)
          (density transition.1.1 *
            generator.rate transition.1.1 transition.1.2) ≤
        rengerDirectionalFlowLocalRateRaw generator density directionalFlowDerivative := by
    unfold rengerDirectionalFlowLocalRateRaw
    exact Finset.single_le_sum
      (f := fun channel : FiniteStateOrderedOffDiagonalTransition State ↦
        rengerExtendedPoissonRateCost
          (directionalFlowDerivative channel)
          (density channel.1.1 * generator.rate channel.1.1 channel.1.2))
      (s := Finset.univ)
      (fun _ _ ↦ (bot_le : (0 : ENNReal) ≤ _)) (Finset.mem_univ transition)
  have hChannelCost :
      rengerExtendedPoissonRateCost
          (directionalFlowDerivative transition)
          (density transition.1.1 *
            generator.rate transition.1.1 transition.1.2) ≠ ⊤ :=
    ne_top_of_le_ne_top hLocalRate hChannelCostLe
  exact flow_eq_zero_of_expected_eq_zero_of_rengerExtendedPoissonRateCost_ne_top
    hExpected hChannelCost

/-- The local action controls total instantaneous one-way flow up to the exact finite sum of
reference-rate corrections.  This is the pointwise coercive input to the published bounded-
variation compactness argument. -/
theorem sum_flow_le_rengerDirectionalFlowLocalRateRaw_add_referenceCorrection
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (density : State → NNReal)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal) :
    (∑ transition, (directionalFlowDerivative transition : ENNReal)) ≤
      rengerDirectionalFlowLocalRateRaw generator density directionalFlowDerivative +
        ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ENNReal.ofReal ((Real.exp 1 - 1) *
            (density transition.1.1 *
              generator.rate transition.1.1 transition.1.2 : NNReal)) := by
  calc
    (∑ transition, (directionalFlowDerivative transition : ENNReal)) ≤
        ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          (rengerExtendedPoissonRateCost
              (directionalFlowDerivative transition)
              (density transition.1.1 *
                generator.rate transition.1.1 transition.1.2) +
            ENNReal.ofReal ((Real.exp 1 - 1) *
              (density transition.1.1 *
                generator.rate transition.1.1 transition.1.2 : NNReal))) := by
      apply Finset.sum_le_sum
      intro transition _hTransition
      exact flow_le_rengerExtendedPoissonRateCost_add_referenceCorrection _ _
    _ = rengerDirectionalFlowLocalRateRaw generator density directionalFlowDerivative +
        ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
          ENNReal.ofReal ((Real.exp 1 - 1) *
            (density transition.1.1 *
              generator.rate transition.1.1 transition.1.2 : NNReal)) := by
      rw [Finset.sum_add_distrib]
      rfl

/-- The raw local density--flow rate is jointly measurable in all finite coordinates. -/
theorem measurable_rengerDirectionalFlowLocalRateRaw
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State) :
    Measurable fun input :
        (State → NNReal) ×
          (FiniteStateOrderedOffDiagonalTransition State → NNReal) =>
      rengerDirectionalFlowLocalRateRaw generator input.1 input.2 := by
  unfold rengerDirectionalFlowLocalRateRaw
  apply Finset.measurable_sum
  intro transition _hTransition
  have hInput : Measurable fun input :
      (State → NNReal) ×
        (FiniteStateOrderedOffDiagonalTransition State → NNReal) =>
      (input.2 transition,
        input.1 transition.1.1 * generator.rate transition.1.1 transition.1.2) := by
    fun_prop
  have hFunction :
      ((fun intensities : NNReal × NNReal =>
        rengerExtendedPoissonRateCost intensities.1 intensities.2) ∘
        (fun input : (State → NNReal) ×
            (FiniteStateOrderedOffDiagonalTransition State → NNReal) =>
          (input.2 transition,
            input.1 transition.1.1 * generator.rate transition.1.1 transition.1.2))) =
      (fun input : (State → NNReal) ×
          (FiniteStateOrderedOffDiagonalTransition State → NNReal) =>
        rengerExtendedPoissonRateCost (input.2 transition)
          (input.1 transition.1.1 * generator.rate transition.1.1 transition.1.2)) := by
    funext input
    rfl
  rw [← hFunction]
  exact measurable_rengerExtendedPoissonRateCost.comp hInput

/-- Renger's local independent-particle rate, summed over ordered off-diagonal state pairs. -/
noncomputable def rengerDirectionalFlowLocalRate
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (density : FiniteStateProbabilityDensity State)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal) :
    ENNReal :=
  ∑ transition,
    rengerExtendedPoissonRateCost
      (directionalFlowDerivative transition)
      (density.weight transition.1.1 * generator.rate transition.1.1 transition.1.2)

/-- Forgetting only the simplex proof leaves the local rate unchanged. -/
theorem rengerDirectionalFlowLocalRateRaw_eq
    {State : Type u} [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (density : FiniteStateProbabilityDensity State)
    (directionalFlowDerivative : FiniteStateOrderedOffDiagonalTransition State → NNReal) :
    rengerDirectionalFlowLocalRateRaw generator density.weight directionalFlowDerivative =
      rengerDirectionalFlowLocalRate generator density directionalFlowDerivative :=
  rfl

/-- Initial relative-entropy cost against one positive invariant density. -/
noncomputable def rengerInvariantInitialCost
    {State : Type u} [Fintype State]
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (density : FiniteStateProbabilityDensity State) : ENNReal :=
  ∑ state, rengerExtendedPoissonRateCost (density.weight state) (stationary.weight state)

/-- Uniqueness of the full-support invariant law used by Corollary 4.16. -/
def IsUniqueFiniteStateMarkovStationaryDistribution
    {State : Type u} [Fintype State]
    {generator : FiniteStateMarkovGenerator State}
    (stationary : FiniteStateMarkovStationaryDistribution generator) : Prop :=
  ∀ other : FiniteStateMarkovStationaryDistribution generator,
    other.pmf = stationary.pmf

/-- Corollary 4.16's initial regime: one specified invariant density, together with its
uniqueness.  The microscopic family below then initializes every particle independently from that
same density. -/
structure RengerCorollaryFourSixteenInitialData
    {State : Type u} [Fintype State]
    (generator : FiniteStateMarkovGenerator State) where
  /-- Supplied full-support invariant distribution used to initialize the particles. -/
  stationary : FiniteStateMarkovStationaryDistribution generator
  /-- Supplied uniqueness of the invariant distribution as an equality of probability mass
  laws. -/
  stationary_unique : IsUniqueFiniteStateMarkovStationaryDistribution stationary

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State] [DecidableEq State]

/-- Exact invariant-i.i.d. microscopic source on the common positive-replica sigma carrier. -/
noncomputable def finiteStateMarkovJumpInvariantIIDMicroscopicLaw
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (duration : ℝ) (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    Measure (FiniteStateMarkovJumpPositiveReplicaFamily State) :=
  finiteStateMarkovJumpPositiveReplicaFamilyLaw successorIndex stationary.pmf generator duration
    (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
      stationary.pmf generator duration hDuration)

omit [DecidableEq State] in
/-- Every invariant-i.i.d. microscopic law is exactly normalized. -/
theorem finiteStateMarkovJumpInvariantIIDMicroscopicLaw_isProbabilityMeasure
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (duration : ℝ) (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpInvariantIIDMicroscopicLaw
        generator stationary duration hDuration successorIndex) :=
  finiteStateMarkovJumpPositiveReplicaFamilyLaw_isProbabilityMeasure
    successorIndex stationary.pmf generator duration _

section HybridBVObservation

variable [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]

/-- Corollary 4.16's invariant-i.i.d. source pushed through the total measurable hybrid-BV
observation on the common successor-indexed carrier. The corresponding LDP is assembled in
`RengerHybridBVCorollaryFourSixteenLargeDeviationRepresentation`. -/
noncomputable def finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (duration : ℝ) (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    Measure (FiniteIntervalHybridBVPath
      (EmpiricalDensityDirectionalFlowCoordinate State) duration) :=
  finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw successorIndex
    stationary.pmf generator duration
      (finiteStateMarkovJumpDensityIsNormalized_of_nonnegative
        stationary.pmf generator duration hDuration)

/-- Every invariant-i.i.d. hybrid-BV observation law is exactly normalized. -/
theorem finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw_isProbabilityMeasure
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (duration : ℝ) (hDuration : 0 ≤ duration) (successorIndex : ℕ) :
    IsProbabilityMeasure
      (finiteStateMarkovJumpInvariantIIDHybridBVObservationLaw
        generator stationary duration hDuration successorIndex) :=
  finiteStateMarkovJumpPositiveReplicaFamilyHybridBVObservationLaw_isProbabilityMeasure
    successorIndex stationary.pmf generator duration _

end HybridBVObservation

/-- Exact macroscopic observation obtained by composing the finite density--directional-flow path
with a supplied map into the published hybrid carrier. -/
noncomputable def finiteStateMarkovJumpInvariantIIDMacroscopicObservation
    {MacroscopicPath : Type v}
    (finiteObservationMap : EmpiricalDensityDirectionalFlowPath State → MacroscopicPath)
    (family : FiniteStateMarkovJumpPositiveReplicaFamily State) : MacroscopicPath :=
  finiteObservationMap
    (finiteStateMarkovJumpPositiveReplicaFamilyObservation family)

/-- The source's open-interval observation mapped into the same macroscopic carrier. -/
noncomputable def finiteStateMarkovJumpInvariantIIDMacroscopicBeforeObservation
    {MacroscopicPath : Type v}
    (finiteObservationMap : EmpiricalDensityDirectionalFlowPath State → MacroscopicPath)
    (family : FiniteStateMarkovJumpPositiveReplicaFamily State) : MacroscopicPath :=
  finiteObservationMap
    (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowBeforePath
      family.1 family.2)

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Any macroscopic quotient map respecting componentwise almost-everywhere equality identifies
the repository's càdlàg and the paper's open-interval observations exactly. -/
theorem finiteStateMarkovJumpInvariantIIDMacroscopicObservation_eq_before
    {MacroscopicPath : Type v}
    (finiteObservationMap : EmpiricalDensityDirectionalFlowPath State → MacroscopicPath)
    (hAEEq : ∀ first second,
      PositiveFiniteJumpHistoryReplicas.DensityDirectionalFlowPathsAgreeAlmostEverywhere
          first second →
        finiteObservationMap first = finiteObservationMap second)
    (family : FiniteStateMarkovJumpPositiveReplicaFamily State) :
    finiteStateMarkovJumpInvariantIIDMacroscopicObservation finiteObservationMap family =
      finiteStateMarkovJumpInvariantIIDMacroscopicBeforeObservation
        finiteObservationMap family :=
  hAEEq _ _
    (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowPath_endpoint_ae
      family.1 family.2)

/-- Components of the finite-source density/ordered-flow large-deviation representation.
The theorem-specific hybrid-BV modules supply the corresponding constructions and proofs. -/
inductive RengerDirectionalFlowRepresentationObligation
  | hybridBoundedVariationEquivalenceClassCarrier
  | cadlagRepresentativeAndBoundaryTraceRecovery
  | strongL1AndVagueDerivativeTopology
  | topologyGeneratedBorelMeasurableSpace
  | exactMeasurableSimplexOffDiagonalObservation
  | totalMeasurableFullCarrierObservationAndLaw
  | absolutelyContinuousContinuityEquationRateDomain
  | theoremSpecificCompleteInitialRate
  | invariantIIDInitialEmpiricalLargeDeviationBounds
  | hybridBVCompactContainment
  | dynamicRateDualAdmissibilityAndBoundaryIdentification
  | dynamicRateLowerSemicontinuity
  | compactFiniteRateSublevels
  | deterministicInitialReplicaLawAndConditionalPathBounds
  | randomInitialConfigurationLiftAndDisintegration
  | closedSetUpperBound
  | openSetLowerBound
  deriving DecidableEq, Repr

end FiniteMarkovProcesses.InformationTheory

attribute
  [inherit_doc FiniteMarkovProcesses.InformationTheory.Renger2018DirectionalFlowTheoremLabel]
  FiniteMarkovProcesses.InformationTheory.Renger2018DirectionalFlowTheoremLabel.ofNat_ctorIdx

attribute
  [inherit_doc FiniteMarkovProcesses.InformationTheory.Renger2018DirectionalFlowInitialHypothesis]
  FiniteMarkovProcesses.InformationTheory.Renger2018DirectionalFlowInitialHypothesis.ofNat_ctorIdx

attribute
  [inherit_doc
    FiniteMarkovProcesses.InformationTheory.RengerDirectionalFlowRepresentationObligation]
FiniteMarkovProcesses.InformationTheory.RengerDirectionalFlowRepresentationObligation.ofNat_ctorIdx
