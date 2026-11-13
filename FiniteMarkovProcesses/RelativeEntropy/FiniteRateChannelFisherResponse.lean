/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

/-!
# Fisher response of finite rate channels

This module isolates the local information geometry of a finite family of positive physical rate
channels. A common-support affine reference family is frozen before evaluating its oriented
relative-entropy rate. The first reference derivative vanishes at equality, and the exact second
derivative is the rate-space Fisher response.

The construction retains the global candidate-to-reference orientation and the parameter radius
on which support is common. Its quadratic germ is even in the tangent and therefore does not, by
itself, recover a directed global action or a physical protocol.

## Main Results

- `CommonSupportAffineRateFamily`: positive affine rate variation on a visible parameter radius.
- `finiteRateChannelRelativeEntropyRate`: oriented finite-channel relative-entropy rate.
- `finiteRateChannelRelativeEntropyRate_reference_derivative_zero`: exact vanishing first
  derivative at equality.
- `CommonSupportAffineRateFamily.hasDerivAt_relativeEntropyRate_zero`: the corresponding
  first-order germ with zero derivative.
- `finiteRateChannelRelativeEntropyRate_reference_secondDerivative_zero`: exact Fisher Hessian.
- `finiteRateChannelFisherResponse_scale`: rate-unit covariance of the Fisher response.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open Filter
open scoped BigOperators Topology

universe u

/-- A finite positive rate family varied affinely on an explicit common-support neighborhood.
The channel type should contain only the physical directed channels being compared. -/
structure CommonSupportAffineRateFamily (Channel : Type u) where
  /-- Candidate rate at literal parameter equality. -/
  baseRate : Channel → ℝ
  /-- Rate derivative with respect to the named affine parameter. -/
  tangentRate : Channel → ℝ
  /-- Open parameter radius on which every channel remains positive. -/
  supportRadius : ℝ
  /-- Every candidate channel rate is strictly positive. -/
  baseRate_pos : ∀ channel, 0 < baseRate channel
  /-- The common-support parameter radius is nontrivial. -/
  supportRadius_pos : 0 < supportRadius
  /-- The affine reference retains the identical positive channel support in the frozen radius. -/
  referenceRate_pos : ∀ channel parameter,
    |parameter| < supportRadius → 0 < baseRate channel + parameter * tangentRate channel

namespace CommonSupportAffineRateFamily

variable {Channel : Type u}

/-- Reference-channel rate at one affine parameter. -/
def referenceRate (family : CommonSupportAffineRateFamily Channel)
    (parameter : ℝ) (channel : Channel) : ℝ :=
  family.baseRate channel + parameter * family.tangentRate channel

/-- At zero parameter, the affine reference rate equals its base rate. -/
@[simp]
theorem referenceRate_zero (family : CommonSupportAffineRateFamily Channel)
    (channel : Channel) :
    family.referenceRate 0 channel = family.baseRate channel := by
  simp [referenceRate]

end CommonSupportAffineRateFamily

variable {Channel : Type u} [Fintype Channel]

/-- Oriented stationary relative-entropy rate from fixed candidate rates to reference rates.
`channelWeight` is normally the stationary occupation weight of the channel's source state. -/
noncomputable def finiteRateChannelRelativeEntropyRate
    (channelWeight candidateRate referenceRate : Channel → ℝ) : ℝ :=
  ∑ channel,
    channelWeight channel *
      (candidateRate channel * Real.log (candidateRate channel / referenceRate channel) -
        candidateRate channel + referenceRate channel)

/-- Oriented relative-entropy rate against a common-support affine reference family. -/
noncomputable def CommonSupportAffineRateFamily.relativeEntropyRate
    (family : CommonSupportAffineRateFamily Channel)
    (channelWeight : Channel → ℝ) (parameter : ℝ) : ℝ :=
  finiteRateChannelRelativeEntropyRate channelWeight family.baseRate
    (family.referenceRate parameter)

/-- Exact reference derivative of the finite-channel relative-entropy rate inside the
common-support radius. -/
noncomputable def CommonSupportAffineRateFamily.referenceGradient
    (family : CommonSupportAffineRateFamily Channel)
    (channelWeight : Channel → ℝ) (parameter : ℝ) : ℝ :=
  ∑ channel,
    channelWeight channel *
      (-(family.baseRate channel * family.tangentRate channel) /
          family.referenceRate parameter channel + family.tangentRate channel)

/-- Rate-space Fisher response in a fixed affine tangent direction. -/
noncomputable def finiteRateChannelFisherResponse
    (channelWeight rate tangentRate : Channel → ℝ) : ℝ :=
  ∑ channel, channelWeight channel * (tangentRate channel ^ 2 / rate channel)

/-- The relative-entropy rate vanishes at literal candidate/reference equality. -/
@[simp]
theorem CommonSupportAffineRateFamily.relativeEntropyRate_zero
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ) :
    family.relativeEntropyRate channelWeight 0 = 0 := by
  unfold relativeEntropyRate finiteRateChannelRelativeEntropyRate
  apply Finset.sum_eq_zero
  intro channel _
  rw [family.referenceRate_zero]
  rw [div_self (family.baseRate_pos channel).ne', Real.log_one]
  ring

/-- Exact first derivative of the oriented rate action at any point inside the frozen
common-support neighborhood. -/
theorem CommonSupportAffineRateFamily.hasDerivAt_relativeEntropyRate
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ)
    (parameter : ℝ) (hParameter : |parameter| < family.supportRadius) :
    HasDerivAt (family.relativeEntropyRate channelWeight)
      (family.referenceGradient channelWeight parameter) parameter := by
  unfold relativeEntropyRate finiteRateChannelRelativeEntropyRate referenceGradient
  apply HasDerivAt.fun_sum
  intro channel _
  have hBase : family.baseRate channel ≠ 0 := (family.baseRate_pos channel).ne'
  have hReference : family.referenceRate parameter channel ≠ 0 :=
    (family.referenceRate_pos channel parameter hParameter).ne'
  have hReferenceDerivative :
      HasDerivAt (family.referenceRate · channel) (family.tangentRate channel) parameter := by
    unfold referenceRate
    convert! (hasDerivAt_const parameter (family.baseRate channel)).add
      ((hasDerivAt_id parameter).mul_const (family.tangentRate channel)) using 1
    all_goals ring
  have hRatioDerivative :=
    (hasDerivAt_const parameter (family.baseRate channel)).div
      hReferenceDerivative hReference
  have hLogDerivative := hRatioDerivative.log (div_ne_zero hBase hReference)
  have hChannelDerivative :=
    (((hLogDerivative.const_mul (family.baseRate channel)).sub_const
      (family.baseRate channel)).add hReferenceDerivative).const_mul
        (channelWeight channel)
  convert hChannelDerivative using 1
  simp only [Pi.div_apply]
  field_simp [hBase, hReference]
  ring

/-- The exact first reference derivative vanishes at candidate/reference equality. -/
theorem CommonSupportAffineRateFamily.relativeEntropyRate_reference_derivative_zero
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ) :
    deriv (family.relativeEntropyRate channelWeight) 0 = 0 := by
  rw [(family.hasDerivAt_relativeEntropyRate channelWeight 0 <| by
    simpa using family.supportRadius_pos).deriv]
  unfold referenceGradient
  apply Finset.sum_eq_zero
  intro channel _
  rw [family.referenceRate_zero]
  field_simp [(family.baseRate_pos channel).ne']
  ring

/-- The oriented finite-channel relative-entropy rate has zero first derivative at literal
candidate/reference equality. -/
theorem CommonSupportAffineRateFamily.hasDerivAt_relativeEntropyRate_zero
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ) :
    HasDerivAt (family.relativeEntropyRate channelWeight) 0 0 := by
  have hDerivative := family.hasDerivAt_relativeEntropyRate channelWeight 0 <| by
    simpa using family.supportRadius_pos
  convert hDerivative using 1
  rw [← hDerivative.deriv]
  exact (family.relativeEntropyRate_reference_derivative_zero channelWeight).symm

/-- The explicit reference gradient has the Fisher-response derivative at equality. -/
theorem CommonSupportAffineRateFamily.hasDerivAt_referenceGradient_zero
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ) :
    HasDerivAt (family.referenceGradient channelWeight)
      (finiteRateChannelFisherResponse channelWeight family.baseRate family.tangentRate) 0 := by
  unfold referenceGradient finiteRateChannelFisherResponse
  apply HasDerivAt.fun_sum
  intro channel _
  have hBase : family.baseRate channel ≠ 0 := (family.baseRate_pos channel).ne'
  have hReferenceDerivative :
      HasDerivAt (family.referenceRate · channel) (family.tangentRate channel) 0 := by
    unfold CommonSupportAffineRateFamily.referenceRate
    convert! (hasDerivAt_const 0 (family.baseRate channel)).add
      ((hasDerivAt_id 0).mul_const (family.tangentRate channel)) using 1
    all_goals ring
  have hReferenceZero : family.referenceRate 0 channel ≠ 0 := by
    simpa using hBase
  have hQuotientDerivative :=
    (hasDerivAt_const 0 (-(family.baseRate channel * family.tangentRate channel))).div
      hReferenceDerivative hReferenceZero
  have hChannelDerivative :=
    ((hQuotientDerivative.add_const (family.tangentRate channel)).const_mul
      (channelWeight channel))
  convert hChannelDerivative using 1
  rw [family.referenceRate_zero]
  field_simp [hBase]
  ring

/-- The literal second reference derivative of the oriented rate action is the finite-channel
Fisher response. -/
theorem CommonSupportAffineRateFamily.relativeEntropyRate_reference_secondDerivative_zero
    (family : CommonSupportAffineRateFamily Channel) (channelWeight : Channel → ℝ) :
    HasDerivAt (fun parameter ↦ deriv (family.relativeEntropyRate channelWeight) parameter)
      (finiteRateChannelFisherResponse channelWeight family.baseRate family.tangentRate) 0 := by
  apply (family.hasDerivAt_referenceGradient_zero channelWeight).congr_of_eventuallyEq
  filter_upwards
    [eventually_gt_nhds (show -family.supportRadius < 0 by
      simpa using family.supportRadius_pos),
      eventually_lt_nhds family.supportRadius_pos] with parameter hLower hUpper
  exact (family.hasDerivAt_relativeEntropyRate channelWeight parameter
    (abs_lt.mpr ⟨hLower, hUpper⟩)).deriv

/-- The exact Fisher response is nonnegative for nonnegative channel weights. -/
theorem finiteRateChannelFisherResponse_nonneg
    (channelWeight rate tangentRate : Channel → ℝ)
    (hWeight : ∀ channel, 0 ≤ channelWeight channel)
    (hRate : ∀ channel, 0 < rate channel) :
    0 ≤ finiteRateChannelFisherResponse channelWeight rate tangentRate := by
  unfold finiteRateChannelFisherResponse
  exact Finset.sum_nonneg fun channel _ ↦
    mul_nonneg (hWeight channel) (div_nonneg (sq_nonneg _) (hRate channel).le)

/-- One positively weighted nonzero physical tangent makes the Fisher response strictly
positive. -/
theorem finiteRateChannelFisherResponse_pos_of_exists
    (channelWeight rate tangentRate : Channel → ℝ)
    (hWeight : ∀ channel, 0 ≤ channelWeight channel)
    (hRate : ∀ channel, 0 < rate channel)
    (hActive : ∃ channel, 0 < channelWeight channel ∧ tangentRate channel ≠ 0) :
    0 < finiteRateChannelFisherResponse channelWeight rate tangentRate := by
  unfold finiteRateChannelFisherResponse
  apply Finset.sum_pos'
  · intro channel _
    exact mul_nonneg (hWeight channel) (div_nonneg (sq_nonneg _) (hRate channel).le)
  · obtain ⟨channel, hChannelWeight, hTangent⟩ := hActive
    refine ⟨channel, Finset.mem_univ channel, ?_⟩
    exact mul_pos hChannelWeight (div_pos (sq_pos_of_ne_zero hTangent) (hRate channel))

/-- The local Fisher germ is even in the perturbation tangent. This is why it cannot recover the
time orientation of the global candidate-to-reference action by itself. -/
theorem finiteRateChannelFisherResponse_neg_tangent
    (channelWeight rate tangentRate : Channel → ℝ) :
    finiteRateChannelFisherResponse channelWeight rate (fun channel ↦ -tangentRate channel) =
      finiteRateChannelFisherResponse channelWeight rate tangentRate := by
  unfold finiteRateChannelFisherResponse
  apply Finset.sum_congr rfl
  intro channel _
  ring

/-- Simultaneously scaling physical rates and their parameter tangents scales the Fisher response
by the same positive rate-unit factor. -/
theorem finiteRateChannelFisherResponse_scale
    (channelWeight rate tangentRate : Channel → ℝ) (scale : ℝ) (hScale : 0 < scale) :
    finiteRateChannelFisherResponse channelWeight (fun channel ↦ scale * rate channel)
        (fun channel ↦ scale * tangentRate channel) =
      scale * finiteRateChannelFisherResponse channelWeight rate tangentRate := by
  unfold finiteRateChannelFisherResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro channel _
  field_simp [hScale.ne']

end FiniteMarkovProcesses.InformationTheory
