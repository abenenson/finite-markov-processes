/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.FiniteRateChannelFisherResponse
public import
  FiniteMarkovProcesses.RelativeEntropy.FiniteStateMarkovTrajectoryRelativeEntropy

/-!
# Fisher response of finite-state Markov trajectory laws

This module lifts a finite affine rate chart to the actual complete-history probability laws of a
stationary finite-state Markov process. The chart must independently identify its reference
generator, common directed support, channel weights, and full stationary relative-entropy rate.
The complete-trajectory KL then has zero first derivative at generator equality and an exact
duration-scaled Fisher second derivative.

The parameter indexes neighboring generators; it is not physical time or a prescribed protocol.
The Fisher Hessian is a local symmetric germ and is not identified with a global directed action.

## Main Results

- `StationaryTrajectoryAffineChart`: an explicit generator-to-rate-channel chart.
- `StationaryTrajectoryAffineChart.trajectoryKlDivToReal_eq_relativeEntropyRate`: exact local
  measure-level KL identity.
- `StationaryTrajectoryAffineChart.hasDerivAt_trajectoryKlDivToReal_zero`: vanishing first
  reference derivative.
- `StationaryTrajectoryAffineChart.hasDerivAt_trajectoryKlDivToRealDerivative_zero`: exact
  complete-trajectory Fisher Hessian.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open _root_.InformationTheory
open FiniteMarkovProcesses.Probability

universe u v

variable {State : Type u} {Channel : Type v}

/-- A prospectively fixed affine rate chart for complete stationary Markov trajectory laws.
The reference generators share the candidate initial law; they need not preserve it. -/
structure StationaryTrajectoryAffineChart
    [Fintype State] [DecidableEq State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (Channel : Type v) [Fintype Channel] where
  /-- Neighboring normalized Markov generators indexed by the chart parameter. -/
  referenceGenerator : ℝ → FiniteStateMarkovGenerator State
  /-- Positive affine coordinates for the active physical rate channels. -/
  rateFamily : CommonSupportAffineRateFamily Channel
  /-- Fixed candidate stationary occupation weight assigned to each channel. -/
  channelWeight : Channel → ℝ
  /-- Parameter zero is literal generator equality. -/
  referenceGenerator_zero : referenceGenerator 0 = generator
  /-- The complete trajectory measures have common directed support throughout the chart. -/
  sameDirectedSupport : ∀ parameter,
    |parameter| < rateFamily.supportRadius →
      generator.HaveSameDirectedSupport (referenceGenerator parameter)
  /-- The full stationary jump-plus-dwell relative entropy is exactly the named channel rate.
  This field is the explicit carrier chart; it may not discard a physical action sector. -/
  stationaryRelativeEntropyRate_eq : ∀ parameter,
    |parameter| < rateFamily.supportRadius →
      finiteStateMarkovStationaryRelativeEntropyRate
          generator stationary (referenceGenerator parameter) =
        rateFamily.relativeEntropyRate channelWeight parameter

namespace StationaryTrajectoryAffineChart

variable [Fintype State] [DecidableEq State] [Fintype Channel]
  [MeasurableSpace State] [MeasurableSingletonClass State]
  {generator : FiniteStateMarkovGenerator State}
  {stationary : FiniteStateMarkovStationaryDistribution generator}

/-- Finite real KL from the fixed stationary candidate history law to one charted reference
history law over the same observation duration. -/
noncomputable def trajectoryKlDivToReal
    (chart : StationaryTrajectoryAffineChart generator stationary Channel)
    (duration : ℝ≥0) (parameter : ℝ) : ℝ :=
  (klDiv (finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration)
    (finiteStateMarkovJumpDensityMeasure stationary.pmf
      (chart.referenceGenerator parameter) duration)).toReal

/-- Inside the common-support chart, the actual complete-trajectory KL is exactly duration times
the finite affine rate-channel relative entropy. -/
theorem trajectoryKlDivToReal_eq_relativeEntropyRate
    (chart : StationaryTrajectoryAffineChart generator stationary Channel)
    (duration : ℝ≥0) (parameter : ℝ)
    (hParameter : |parameter| < chart.rateFamily.supportRadius) :
    chart.trajectoryKlDivToReal duration parameter =
      (duration : ℝ) *
        chart.rateFamily.relativeEntropyRate chart.channelWeight parameter := by
  unfold trajectoryKlDivToReal
  calc
    _ = (duration : ℝ) *
        finiteStateMarkovStationaryRelativeEntropyRate generator stationary
          (chart.referenceGenerator parameter) :=
      (finiteStateMarkovTrajectoryKlDiv_toReal_eq_stationaryRelativeEntropyRate
        generator stationary (chart.referenceGenerator parameter)
        (chart.sameDirectedSupport parameter hParameter) duration).2
    _ = _ := by rw [chart.stationaryRelativeEntropyRate_eq parameter hParameter]

/-- The complete-trajectory KL has zero first reference derivative at literal generator equality. -/
theorem hasDerivAt_trajectoryKlDivToReal_zero
    (chart : StationaryTrajectoryAffineChart generator stationary Channel)
    (duration : ℝ≥0) :
    HasDerivAt (chart.trajectoryKlDivToReal duration) 0 0 := by
  have hLocalEquality :
      chart.trajectoryKlDivToReal duration =ᶠ[𝓝 0]
        fun parameter ↦ (duration : ℝ) *
          chart.rateFamily.relativeEntropyRate chart.channelWeight parameter := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr chart.rateFamily.supportRadius_pos)
      chart.rateFamily.supportRadius_pos] with parameter hParameter
    exact chart.trajectoryKlDivToReal_eq_relativeEntropyRate duration parameter
      (abs_lt.mpr hParameter)
  simpa using
    ((chart.rateFamily.hasDerivAt_relativeEntropyRate_zero chart.channelWeight).const_mul
      (duration : ℝ)).congr_of_eventuallyEq hLocalEquality

/-- The first reference derivative of complete-trajectory KL vanishes at generator equality. -/
theorem trajectoryKlDivToReal_reference_derivative_zero
    (chart : StationaryTrajectoryAffineChart generator stationary Channel)
    (duration : ℝ≥0) :
    deriv (chart.trajectoryKlDivToReal duration) 0 = 0 :=
  (chart.hasDerivAt_trajectoryKlDivToReal_zero duration).deriv

/-- The derivative of complete-trajectory KL has the exact duration-scaled finite-channel Fisher
response at generator equality. -/
theorem hasDerivAt_trajectoryKlDivToRealDerivative_zero
    (chart : StationaryTrajectoryAffineChart generator stationary Channel)
    (duration : ℝ≥0) :
    HasDerivAt (fun parameter ↦ deriv (chart.trajectoryKlDivToReal duration) parameter)
      ((duration : ℝ) * finiteRateChannelFisherResponse chart.channelWeight
        chart.rateFamily.baseRate chart.rateFamily.tangentRate) 0 := by
  have hDerivativeEquality :
      (fun parameter ↦ deriv (chart.trajectoryKlDivToReal duration) parameter) =ᶠ[𝓝 0]
        fun parameter ↦ (duration : ℝ) *
          deriv (chart.rateFamily.relativeEntropyRate chart.channelWeight) parameter := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr chart.rateFamily.supportRadius_pos)
      chart.rateFamily.supportRadius_pos] with parameter hParameter
    have hLocalEquality :
        chart.trajectoryKlDivToReal duration =ᶠ[𝓝 parameter]
          fun nearby ↦ (duration : ℝ) *
            chart.rateFamily.relativeEntropyRate chart.channelWeight nearby := by
      filter_upwards [Ioo_mem_nhds hParameter.1 hParameter.2] with nearby hNearby
      exact chart.trajectoryKlDivToReal_eq_relativeEntropyRate duration nearby
        (abs_lt.mpr hNearby)
    calc
      deriv (chart.trajectoryKlDivToReal duration) parameter =
          deriv (fun nearby ↦ (duration : ℝ) *
            chart.rateFamily.relativeEntropyRate chart.channelWeight nearby) parameter :=
        hLocalEquality.deriv_eq
      _ = (duration : ℝ) *
          deriv (chart.rateFamily.relativeEntropyRate chart.channelWeight) parameter := by
        rw [deriv_const_mul_field]
  exact ((chart.rateFamily.relativeEntropyRate_reference_secondDerivative_zero
    chart.channelWeight).const_mul (duration : ℝ)).congr_of_eventuallyEq
      hDerivativeEquality

end StationaryTrajectoryAffineChart

end FiniteMarkovProcesses.InformationTheory
