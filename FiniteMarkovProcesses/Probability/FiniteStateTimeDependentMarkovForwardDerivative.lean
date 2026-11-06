/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovL1Dissipation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDirectionalFlowExpectation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovForwardEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Almost-everywhere derivative of finite-state time-dependent Markov endpoint probabilities

The existing integral forward equation is consolidated into one integrable
incoming-minus-outgoing drift.  Lebesgue differentiation then identifies that drift as the
almost-everywhere derivative of every physical endpoint-probability coordinate.
-/

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Real incoming-minus-outgoing forward drift of one endpoint-probability coordinate. -/
noncomputable def finiteStateTimeDependentMarkovEndpointProbabilityDrift
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (observed : State) : ℝ :=
  (∑ source ∈ Finset.univ.erase observed,
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time source).toReal * (rates.rate time source observed : ℝ)) -
    ∑ target ∈ Finset.univ.erase observed,
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time observed).toReal * (rates.rate time observed target : ℝ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The off-diagonal physical drift is the complete finite-state divergence of the generated
instantaneous probability flow; its diagonal terms vanish individually. -/
theorem finiteStateTimeDependentMarkovEndpointProbabilityDrift_eq_flowDivergence
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (time : ℝ) (observed : State) :
    finiteStateTimeDependentMarkovEndpointProbabilityDrift initial rates time observed =
      finiteStateFlowDivergence
        (fun source target ↦
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time source).toReal * (rates.rate time source target : ℝ))
        observed := by
  unfold finiteStateTimeDependentMarkovEndpointProbabilityDrift finiteStateFlowDivergence
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ observed),
    ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ observed)]
  simp [rates.rate_self]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Occupied-source probability times one off-diagonal physical rate is integrable on every
finite nonnegative horizon. -/
theorem integrableOn_endpointProbability_mul_timeDependentMarkovRate
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target) :
    IntegrableOn (fun time : ℝ ↦
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time source).toReal * (rates.rate time source target : ℝ))
      (Ioo 0 (duration : ℝ)) := by
  simpa only [NNReal.coe_one, one_mul] using
    (integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
      initial rates duration hNe (fun _time ↦ 1) measurable_const
      (weightBound := 1) (by positivity) (fun _time ↦ by simp))

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The endpoint drift is integrable over every finite nonnegative physical horizon. -/
theorem integrableOn_finiteStateTimeDependentMarkovEndpointProbabilityDrift
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    IntegrableOn
      (fun time ↦ finiteStateTimeDependentMarkovEndpointProbabilityDrift
        initial rates time observed)
      (Ioo 0 (duration : ℝ)) := by
  apply Integrable.sub
  · apply integrable_finsetSum (Finset.univ.erase observed)
    intro source hSource
    exact integrableOn_endpointProbability_mul_timeDependentMarkovRate
      initial rates duration (Finset.mem_erase.mp hSource).1
  · apply integrable_finsetSum (Finset.univ.erase observed)
    intro target hTarget
    exact integrableOn_endpointProbability_mul_timeDependentMarkovRate
      initial rates duration (fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm)

/-- The physical endpoint probability is its initial coordinate plus the integral of the complete
forward drift. -/
theorem finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_integral_drift
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    (finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed).toReal =
      (initial observed).toReal +
        ∫ time : ℝ in Ioo 0 (duration : ℝ),
          finiteStateTimeDependentMarkovEndpointProbabilityDrift
            initial rates time observed := by
  rw [finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_incoming_sub_outgoing]
  have hIncoming :
      (∑ source ∈ Finset.univ.erase observed,
        ∫ time : ℝ in Ioo 0 (duration : ℝ),
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time source).toReal *
            (rates.rate time source observed : ℝ)) =
      ∫ time : ℝ in Ioo 0 (duration : ℝ),
        ∑ source ∈ Finset.univ.erase observed,
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time source).toReal *
            (rates.rate time source observed : ℝ) := by
    rw [integral_finsetSum]
    intro source hSource
    exact integrableOn_endpointProbability_mul_timeDependentMarkovRate
      initial rates duration (Finset.mem_erase.mp hSource).1
  have hOutgoing :
      (∑ target ∈ Finset.univ.erase observed,
        ∫ time : ℝ in Ioo 0 (duration : ℝ),
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time observed).toReal *
            (rates.rate time observed target : ℝ)) =
      ∫ time : ℝ in Ioo 0 (duration : ℝ),
        ∑ target ∈ Finset.univ.erase observed,
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates time observed).toReal *
            (rates.rate time observed target : ℝ) := by
    rw [integral_finsetSum]
    intro target hTarget
    exact integrableOn_endpointProbability_mul_timeDependentMarkovRate
      initial rates duration (fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm)
  rw [hIncoming, hOutgoing]
  unfold finiteStateTimeDependentMarkovEndpointProbabilityDrift
  rw [integral_sub]
  · ring
  · exact integrable_finsetSum (Finset.univ.erase observed) fun source hSource ↦
      integrableOn_endpointProbability_mul_timeDependentMarkovRate
        initial rates duration (Finset.mem_erase.mp hSource).1
  · exact integrable_finsetSum (Finset.univ.erase observed) fun target hTarget ↦
      integrableOn_endpointProbability_mul_timeDependentMarkovRate
        initial rates duration (fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm)

/-- On every positive finite horizon, the complete forward drift is almost everywhere the
derivative of the corresponding physical endpoint-probability coordinate. -/
theorem ae_hasDerivAt_finiteStateTimeDependentMarkovEndpointProbability
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    ∀ᵐ time ∂volume.restrict (Ioo 0 (duration : ℝ)),
      HasDerivAt
        (fun horizon ↦
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates horizon observed).toReal)
        (finiteStateTimeDependentMarkovEndpointProbabilityDrift
          initial rates time observed)
        time := by
  have hDriftIntegrable : IntervalIntegrable
      (finiteStateTimeDependentMarkovEndpointProbabilityDrift initial rates · observed)
      volume 0 (duration : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le duration.coe_nonneg]
    exact integrableOn_finiteStateTimeDependentMarkovEndpointProbabilityDrift
      initial rates duration observed
  have hPrimitiveDerivative := hDriftIntegrable.ae_hasDerivAt_integral
  filter_upwards [ae_restrict_of_ae hPrimitiveDerivative,
    ae_restrict_mem measurableSet_Ioo] with time hDerivative hTime
  have hLocalEquality :
      (fun horizon ↦
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates horizon observed).toReal) =ᶠ[nhds time]
      fun horizon ↦
        (initial observed).toReal +
          ∫ markedTime : ℝ in 0..horizon,
            finiteStateTimeDependentMarkovEndpointProbabilityDrift
              initial rates markedTime observed := by
    filter_upwards [Ioo_mem_nhds hTime.1 hTime.2] with horizon hHorizon
    have hEquation :=
      finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_integral_drift
        initial rates ⟨horizon, hHorizon.1.le⟩ observed
    change (finiteStateTimeDependentMarkovEndpointProbability
        initial rates horizon observed).toReal =
      (initial observed).toReal +
        ∫ markedTime : ℝ in Ioo 0 horizon,
          finiteStateTimeDependentMarkovEndpointProbabilityDrift
            initial rates markedTime observed at hEquation
    rw [intervalIntegral.integral_of_le hHorizon.1.le,
      integral_Ioc_eq_integral_Ioo]
    exact hEquation
  apply HasDerivAt.congr_of_eventuallyEq _ hLocalEquality
  have hTimeInterval : time ∈ uIcc 0 (duration : ℝ) := by
    rw [uIcc_of_le duration.coe_nonneg]
    exact ⟨hTime.1.le, hTime.2.le⟩
  have hZeroInterval : (0 : ℝ) ∈ uIcc 0 (duration : ℝ) := by
    rw [uIcc_of_le duration.coe_nonneg]
    exact ⟨le_rfl, duration.coe_nonneg⟩
  exact (hDerivative hTimeInterval 0 hZeroInterval).const_add (initial observed).toReal

end

end FiniteMarkovProcesses.Probability
