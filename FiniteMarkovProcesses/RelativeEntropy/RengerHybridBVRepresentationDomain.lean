/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVCumulativeFlowTranslation

/-!
# Finite-rate representation domain for the Renger hybrid dual

Renger's Proposition 4.4 represents the local directional-flow action on paths already satisfying
the `W¹,¹`, `BVflux`, positivity, and initial-condition kinematics.  It does not turn the same
unpenalized dual into a detector of inadmissible points in a larger observation carrier.

This module freezes that distinction at declaration level.  Microscopic observations retain the
total hybrid-BV carrier, including atomic finite-particle derivatives.  The representation domain
is instead the subtype of paths satisfying the repository's exact finite-rate physical predicate.
The current dual restricts continuously to that subtype and remains bounded by the dynamic rate
there.  A nonzero cumulative-flow translation cannot be lifted into the subtype.

No converse dual identity, total-rate lower semicontinuity, or large-deviation bound is asserted
here.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory Set
open scoped ENNReal

open FiniteMarkovProcesses
open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- The exact finite-rate kinematic domain on which the Renger dual representation is licensed.
The ambient observation carrier is deliberately not replaced by this set. -/
def rengerDirectionalFlowHybridBVRepresentationDomain
    (hDuration : 0 < duration) :
    Set (RengerDirectionalFlowHybridBVPath State duration) :=
  {path | RengerDirectionalFlowHybridBVAdmissible path hDuration}

/-- A path together with its exact finite-rate physical and continuity evidence.  This subtype is
used only for the dual representation theorem; microscopic observations remain total-carrier
valued. -/
abbrev RengerDirectionalFlowHybridBVRepresentationPath
    (State : Type u) [Fintype State] [DecidableEq State]
    (duration : ℝ) (hDuration : 0 < duration) :=
  rengerDirectionalFlowHybridBVRepresentationDomain
    (State := State) hDuration

/-- Membership in the named representation domain is exactly finite-rate admissibility. -/
@[simp]
theorem mem_rengerDirectionalFlowHybridBVRepresentationDomain_iff
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVPath State duration) :
    path ∈ rengerDirectionalFlowHybridBVRepresentationDomain hDuration ↔
      RengerDirectionalFlowHybridBVAdmissible path hDuration :=
  Iff.rfl

/-- Every representation path exposes its finite-rate physical evidence. -/
theorem rengerDirectionalFlowHybridBVRepresentationPath_admissible
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    RengerDirectionalFlowHybridBVAdmissible path.1 hDuration :=
  path.2

/-- On the representation domain, the totalized dynamic rate is exactly the integral of the
ordered-channel local rate. -/
theorem rengerDirectionalFlowHybridBVDynamicRate_eq_integral_on_representationDomain
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 =
      ∫⁻ time,
        rengerDirectionalFlowLocalRateRaw generator
          (rengerDirectionalFlowHybridBVDensityAt path.1 time)
          (rengerDirectionalFlowHybridBVFlowDerivativeAt path.1 time)
        ∂finiteOpenIntervalVolume duration :=
  rengerDirectionalFlowHybridBVDynamicRate_eq_of_admissible
    generator hDuration path.2

/-- Every existing dual test stays below the dynamic rate on the exact representation domain. -/
theorem rengerDirectionalFlowHybridBVExtendedDualEvaluation_le_dynamicRate_on_representationDomain
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    rengerDirectionalFlowHybridBVExtendedDualEvaluation generator test path.1 ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 :=
  rengerDirectionalFlowHybridBVExtendedDualEvaluation_le_dynamicRate
    generator hDuration test path.2

/-- The complete current dual supremum stays below the dynamic rate on the exact representation
domain. -/
theorem rengerDirectionalFlowHybridBVDualRate_le_dynamicRate_on_representationDomain
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration) :
    rengerDirectionalFlowHybridBVDualRate generator path.1 ≤
      rengerDirectionalFlowHybridBVDynamicRate generator hDuration path.1 :=
  rengerDirectionalFlowHybridBVDualRate_le_dynamicRate
    generator hDuration path.2

/-- Each fixed dual evaluation restricts continuously to the exact representation subtype. -/
theorem continuous_rengerDirectionalFlowHybridBVDualEvaluation_on_representationDomain
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    Continuous fun path :
        RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration =>
      rengerDirectionalFlowHybridBVDualEvaluation generator test path.1 :=
  (continuous_rengerDirectionalFlowHybridBVDualEvaluation generator test).comp
    continuous_subtype_val

/-- The current dual supremum restricts lower-semicontinuously to the exact representation
subtype.  This does not imply lower semicontinuity of the totalized dynamic rate on the ambient
carrier. -/
theorem lowerSemicontinuous_rengerDirectionalFlowHybridBVDualRate_on_representationDomain
    (generator : FiniteStateMarkovGenerator State)
    (hDuration : 0 < duration) :
    LowerSemicontinuous fun path :
        RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration =>
      rengerDirectionalFlowHybridBVDualRate generator path.1 :=
  LowerSemicontinuous.comp
    (f := rengerDirectionalFlowHybridBVDualRate (duration := duration) generator)
    (g := (Subtype.val :
      RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration →
        RengerDirectionalFlowHybridBVPath State duration))
    (lowerSemicontinuous_rengerDirectionalFlowHybridBVDualRate
      (duration := duration) generator)
    (continuous_subtype_val :
      Continuous (Subtype.val :
        RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration →
          RengerDirectionalFlowHybridBVPath State duration))

/-- A nonzero constant cumulative-flow translation of a representation path lies outside the
representation domain. -/
theorem rengerDirectionalFlowHybridBVTranslateCumulativeFlow_not_mem_representationDomain
    (hDuration : 0 < duration)
    (path : RengerDirectionalFlowHybridBVRepresentationPath State duration hDuration)
    (offset : FiniteStateOrderedOffDiagonalTransition State → ℝ)
    (transition : FiniteStateOrderedOffDiagonalTransition State)
    (hOffset : offset transition ≠ 0) :
    rengerDirectionalFlowHybridBVTranslateCumulativeFlow path.1 offset ∉
      rengerDirectionalFlowHybridBVRepresentationDomain hDuration := by
  rw [mem_rengerDirectionalFlowHybridBVRepresentationDomain_iff]
  exact not_rengerDirectionalFlowHybridBVAdmissible_translateCumulativeFlow_of_ne_zero
    hDuration path.2 offset transition hOffset

end

end FiniteMarkovProcesses.InformationTheory
