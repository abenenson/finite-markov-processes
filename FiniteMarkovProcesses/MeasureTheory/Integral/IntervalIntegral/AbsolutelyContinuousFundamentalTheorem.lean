/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import FiniteMarkovProcesses.Order.Interval.Finset.Gaps

/-!
# Fundamental theorem of calculus for absolutely continuous functions

This is a compatibility backport of the absolutely-continuous FTC developed upstream in Mathlib
PR #29508, together with the small interval-primitive and finite-gap lemmas that the pinned Mathlib
revision predates. All declarations live under `FiniteMarkovProcesses`, so a future dependency
update cannot collide with the upstream declarations.

The principal result is
`FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.
-/

namespace FiniteMarkovProcesses

variable {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

open Filter Fin.NatCast Function MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace Finset

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (collection : Finset (α × α)) {count : ℕ} (hCount : collection.card = count)
  {lower upper : α} (value : α → β)

/-- Reindex a finite interval collection by its ordered gap boundaries. -/
@[to_additive /-- Reindex a finite interval sum by its existing ordered gap boundaries. -/]
theorem prod_eq_prod_range_intervalGapsWithin (summand : α → α → β) :
    ∏ endpoints ∈ collection, summand endpoints.1 endpoints.2 =
      ∏ index ∈ Finset.range count,
        summand (collection.intervalGapsWithin hCount lower upper index).2
          (collection.intervalGapsWithin hCount lower upper index.succ).1 := by
  let gaps := collection.intervalGapsWithin hCount lower upper
  symm
  apply _root_.Finset.prod_nbij (s := Finset.range count) (t := collection)
    (fun index : ℕ ↦ ((gaps index).2, (gaps index.succ).1))
  · exact fun index _ ↦
      collection.intervalGapsWithin_mapsTo hCount lower upper (x := index) (by grind)
  · intro first hFirst second hSecond hEqual
    exact collection.intervalGapsWithin_injOn hCount lower upper
      (by simpa using hFirst) (by simpa using hSecond) hEqual
  · intro endpoints hEndpoints
    obtain ⟨index, hIndex, hEndpointsEqual⟩ :=
      collection.intervalGapsWithin_surjOn hCount lower upper hEndpoints
    exact ⟨index, by grind, hEndpointsEqual⟩
  · intro index hIndex
    simp [gaps, Nat.succ_eq_add_one]

/-- Multiplicative telescoping across a finite family of interval gaps. -/
@[to_additive /-- Additive telescoping across the same finite family of interval gaps. -/]
theorem prod_intervalGapsWithin_mul_prod_eq_div :
    (∏ index ∈ Finset.range (count + 1),
      value (collection.intervalGapsWithin hCount lower upper index).2 /
        value (collection.intervalGapsWithin hCount lower upper index).1) *
      ∏ endpoints ∈ collection, value endpoints.2 / value endpoints.1 =
        value upper / value lower := by
  rw [FiniteMarkovProcesses.Finset.prod_eq_prod_range_intervalGapsWithin collection hCount
      (lower := lower) (upper := upper)
      (fun first second ↦ value second / value first),
    mul_comm, _root_.Finset.prod_range_succ, ← mul_assoc,
    ← _root_.Finset.prod_mul_distrib,
    _root_.Finset.prod_congr rfl (fun _ _ ↦ div_mul_div_cancel _ _ _),
    _root_.Finset.prod_range_div
      (fun index ↦ value (collection.intervalGapsWithin hCount lower upper index).1)]
  simp

/-- Multiplicative telescoping with the selected intervals moved to the right-hand side. -/
@[to_additive /-- Additive telescoping with the selected intervals on the right-hand side. -/]
theorem prod_intervalGapsWithin_eq_div_div_prod :
    (∏ index ∈ Finset.range (count + 1),
      value (collection.intervalGapsWithin hCount lower upper index).2 /
        value (collection.intervalGapsWithin hCount lower upper index).1) =
      (value upper / value lower) /
        ∏ endpoints ∈ collection, value endpoints.2 / value endpoints.1 :=
  eq_div_iff_mul_eq'.mpr
    (prod_intervalGapsWithin_mul_prod_eq_div collection hCount value)

end Finset

namespace Vitali

/-- Filter form of the measurable Vitali covering theorem. -/
theorem exists_disjoint_covering_ae_filter
    {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (measure : Measure α) [IsLocallyFiniteMeasure measure]
    (source : Set α) (family : Set ι) (constant : ℝ≥0) (radius : ι → ℝ)
    (center : ι → α) (body : ι → Set α)
    (hBody : ∀ member ∈ family,
      body member ⊆ Metric.closedBall (center member) (radius member))
    (hMeasure : ∀ member ∈ family,
      measure (Metric.closedBall (center member) (3 * radius member))
        ≤ constant * measure (body member))
    (hInterior : ∀ member ∈ family, (interior (body member)).Nonempty)
    (hClosed : ∀ member ∈ family, IsClosed (body member))
    (hFine : ∀ point ∈ source, ∃ᶠ epsilon in 𝓝[>] (0 : ℝ),
      ∃ member ∈ family, radius member = epsilon ∧ center member = point) :
    ∃ selected ⊆ family, selected.Countable ∧ selected.PairwiseDisjoint body ∧
      measure (source \ ⋃ member ∈ selected, body member) = 0 := by
  apply _root_.Vitali.exists_disjoint_covering_ae measure source family constant
    radius center body hBody hMeasure hInterior hClosed
  intro point hPoint epsilon hEpsilon
  specialize hFine point hPoint
  rw [frequently_nhdsWithin_iff, frequently_nhds_iff] at hFine
  obtain ⟨_, _, ⟨member, hMember, hRadius, hCenter⟩, _⟩ :=
    hFine (Ioo (-epsilon) epsilon) (by grind) isOpen_Ioo
  exact ⟨member, hMember, by grind, hCenter⟩

end Vitali

/-- A member interval of `disjWithin` lies in the ambient unoriented interval. -/
lemma uIoc_subset_of_mem_disjWithin {a b : ℝ} {count : ℕ} {interval : ℕ → ℝ × ℝ}
    (hIntervals : (count, interval) ∈ AbsolutelyContinuousOnInterval.disjWithin a b)
    {index : ℕ} (hIndex : index < count) :
    uIoc (interval index).1 (interval index).2 ⊆ uIoc a b := by
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range, mem_ofPred_eq,
    uIcc, mem_Icc] at hIntervals
  have hBounds := hIntervals.left index hIndex
  dsimp only [uIoc]
  gcongr 1
  · simp only [le_inf_iff]
    tauto
  · simp only [sup_le_iff]
    tauto

/-- The total volume of the disjoint-interval filter tends to zero. -/
lemma tendsto_volume_totalLengthFilter_nhds_zero :
    Tendsto
      (fun data : ℕ × (ℕ → ℝ × ℝ) ↦
        volume (⋃ index ∈ Finset.range data.1,
          uIoc (data.2 index).1 (data.2 index).2))
      AbsolutelyContinuousOnInterval.totalLengthFilter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun data ↦ ENNReal.ofReal
      (∑ index ∈ Finset.range data.1, dist (data.2 index).1 (data.2 index).2))
  · convert! ENNReal.tendsto_ofReal Filter.tendsto_comap
    simp
  · intro
    simp
  · intro data
    simp only
    grw [measure_biUnion_finset_le]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
    apply Eq.le
    apply Finset.sum_congr rfl
    simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']

/-- Restricting to the ambient interval preserves the vanishing-volume filter limit. -/
lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : ℝ) :
    Tendsto
      (fun data : ℕ × (ℕ → ℝ × ℝ) ↦
        volume.restrict (uIoc a b)
          (⋃ index ∈ Finset.range data.1,
            uIoc (data.2 index).1 (data.2 index).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun data : ℕ × (ℕ → ℝ × ℝ) ↦
      volume (⋃ index ∈ Finset.range data.1,
        uIoc (data.2 index).1 (data.2 index).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro
    simp
  · intro data
    simp only [Finset.mem_range]
    apply Measure.restrict_le_self

/-- An interval integral primitive is absolutely continuous on its integration interval. -/
theorem intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
    {integrand : ℝ → ℝ} {a b c : ℝ}
    (hIntegrable : IntervalIntegrable integrand volume a b) (hCenter : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ value in c..x, integrand value) a b := by
  let unionIntervals := fun data : ℕ × (ℕ → ℝ × ℝ) ↦
    ⋃ index ∈ Finset.range data.1, uIoc (data.2 index).1 (data.2 index).2
  have hVanishing : Tendsto
      (fun data ↦ ∫⁻ x in unionIntervals data, ‖integrand x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    apply tendsto_setLIntegral_zero
    · apply ne_of_lt
      exact (intervalIntegrable_iff.mp hIntegrable).hasFiniteIntegral
    · exact tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero a b
  have hToReal := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hVanishing
  refine squeeze_zero' ?_ ?_ hToReal
  · filter_upwards with data
    exact Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  simp only [comp_apply, unionIntervals]
  have hEventuallyIntervals :
      ∀ᶠ data : ℕ × (ℕ → ℝ × ℝ) in
        AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
        data ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hEventuallyIntervals] with data hData
  rcases data with ⟨count, interval⟩
  obtain ⟨hBounds, hDisjoint⟩ := mem_ofPred_eq ▸ hData
  simp only
  have hStrong : AEStronglyMeasurable integrand (volume.restrict (uIoc a b)) := by
    by_cases hab : a ≤ b
    · rw [uIoc_of_le hab]
      exact hIntegrable.aestronglyMeasurable
    · rw [uIoc_of_ge (le_of_not_ge hab)]
      exact hIntegrable.aestronglyMeasurable'
  rw [← integral_norm_eq_lintegral_enorm hStrong.restrict,
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hDisjoint]
  · refine Finset.sum_le_sum fun index hIndex ↦ ?_
    rw [Real.dist_eq,
      intervalIntegral.integral_interval_sub_left
        (by apply IntervalIntegrable.mono_set' hIntegrable; grind [uIoc, uIcc])
        (by apply IntervalIntegrable.mono_set' hIntegrable; grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hData (Finset.mem_range.mp hIndex)),
      intervalIntegral.integral_symm, abs_neg,
      intervalIntegral.abs_intervalIntegral_eq]
    exact abs_integral_le_integral_abs
  · intro index hIndex
    unfold IntegrableOn
    have hSubset := uIoc_subset_of_mem_disjWithin hData (Finset.mem_range.mp hIndex)
    rw [Measure.restrict_restrict_of_subset hSubset]
    exact IntegrableOn.mono_set hIntegrable.def'.norm hSubset |>.integrable

/-- A.e. derivatives yield a full-measure family of short intervals with controlled slopes. -/
lemma exists_dist_slope_lt_pairwiseDisjoint_hasSum
    {function derivative : ℝ → F} {lower upper tolerance : ℝ}
    (hBounds : lower ≤ upper)
    (hDerivative : ∀ᵐ x, x ∈ Ioo lower upper → HasDerivAt function (derivative x) x)
    (hTolerance : 0 < tolerance) :
    ∃ intervals : Set (ℝ × ℝ),
      (∀ endpoints ∈ intervals,
        (lower < endpoints.1 ∧ endpoints.1 < endpoints.2 ∧ endpoints.2 < upper) ∧
          dist (slope function endpoints.1 endpoints.2) (derivative endpoints.1) < tolerance) ∧
      intervals.PairwiseDisjoint (fun endpoints ↦ Icc endpoints.1 endpoints.2) ∧
      HasSum (fun endpoints : intervals ↦ endpoints.val.2 - endpoints.val.1) (upper - lower) := by
  rcases hBounds.eq_or_lt with rfl | hBounds
  · refine ⟨(∅ : Set (ℝ × ℝ)), by simp, Set.pairwiseDisjoint_empty, ?_⟩
    simp
  let candidate := {endpoints : ℝ × ℝ |
    (lower < endpoints.1 ∧ endpoints.1 < endpoints.2 ∧ endpoints.2 < upper) ∧
      dist (slope function endpoints.1 endpoints.2) (derivative endpoints.1) < tolerance}
  let good := {x ∈ Ioo lower upper | HasDerivAt function (derivative x) x}
  obtain ⟨intervals, hSubset, hCountable, hDisjoint, hCover⟩ :=
    Vitali.exists_disjoint_covering_ae_filter volume good candidate 6
      (Prod.snd - Prod.fst) Prod.fst (fun endpoints ↦ Icc endpoints.1 endpoints.2)
      (by grind [Metric.closedBall, Real.dist_eq, Pi.sub_apply, abs_le'])
      (by
        intro endpoints hEndpoints
        simp only [Pi.sub_apply, Real.volume_closedBall, ENNReal.coe_ofNat, Real.volume_Icc]
        rw [show 6 = ENNReal.ofReal 6 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_le_ofReal_iff (by grind)]
        linarith)
      (by simp +contextual [candidate]) (by simp [isClosed_Icc]) (by
        intro x hX
        apply Eventually.frequently
        obtain ⟨delta, hDeltaPositive, hDelta⟩ :=
          (Metric.tendsto_nhdsWithin_nhds).mp
            (hasDerivAt_iff_tendsto_slope.mp hX.right) tolerance hTolerance
        have hEventuallyBound {alpha : ℝ} (hAlpha : 0 < alpha) :
            ∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon < alpha := by
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          exact ⟨Ioo (-alpha) alpha, by grind, isOpen_Ioo, by grind⟩
        have hEventuallyPositive : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, 0 < epsilon :=
          eventually_mem_of_tendsto_nhdsWithin fun _ h ↦ h
        filter_upwards [hEventuallyPositive, hEventuallyBound hTolerance,
          hEventuallyBound hDeltaPositive,
          hEventuallyBound (show 0 < (upper - x) / 2 by simp [hX.left.right])]
          with epsilon hEpsilonPositive hEpsilonTolerance hEpsilonDelta hEpsilonUpper
        refine ⟨(x, x + epsilon),
          ⟨⟨hX.1.1, by linarith, by linarith⟩, ?_⟩, by simp, rfl⟩
        exact hDelta (by grind)
          (by simp [abs_eq_self.mpr hEpsilonPositive.le, hEpsilonDelta]))
  simp only [candidate, subset_def, mem_ofPred_eq] at hSubset
  refine ⟨intervals, hSubset, hDisjoint, ?_⟩
  have : Countable intervals := hCountable.to_subtype
  have hSubtypeDisjoint : Pairwise
      (Disjoint on fun endpoints : intervals ↦ Icc endpoints.val.1 endpoints.val.2) :=
    fun first second hNe ↦ hDisjoint first.prop second.prop (Subtype.coe_ne_coe.mpr hNe)
  replace hCover : volume (Ioo lower upper \ ⋃ endpoints ∈ intervals,
      Icc endpoints.1 endpoints.2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem] at hCover ⊢
    filter_upwards [hDerivative, hCover] with x hDerivativeAt hNotCovered
    grind
  have hVolume : volume (⋃ endpoints : intervals,
      Icc endpoints.val.1 endpoints.val.2) = ENNReal.ofReal (upper - lower) := by
    convert Real.volume_Ioo ▸
      measure_eq_measure_of_null_sdiff
        (by simp only [iUnion_subset_iff]; grind) hCover using 2
    simp
  rw [measure_iUnion hSubtypeDisjoint (by simp)] at hVolume
  simp_rw [Real.volume_Icc] at hVolume
  apply_fun ENNReal.toReal at hVolume
  rw [ENNReal.tsum_toReal_eq (by simp), ENNReal.toReal_ofReal (by linarith),
    ← Summable.hasSum_iff (by grind [tsum_def])] at hVolume
  convert hVolume with endpoints
  grind [ENNReal.toReal_ofReal]

/-- Absolute continuity fills the gaps left by a disjoint full-length interval family. -/
lemma AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum
    {function : ℝ → X} {lower upper totalDistance : ℝ}
    (hBounds : lower ≤ upper)
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function lower upper)
    {intervals : Set (ℝ × ℝ)}
    (hInterior : ∀ endpoints ∈ intervals,
      lower < endpoints.1 ∧ endpoints.1 < endpoints.2 ∧ endpoints.2 < upper)
    (hDisjoint : intervals.PairwiseDisjoint (fun endpoints ↦ Icc endpoints.1 endpoints.2))
    (hLength : HasSum (fun endpoints : intervals ↦ endpoints.val.2 - endpoints.val.1)
      (upper - lower))
    (hDistance : HasSum
      (fun endpoints : intervals ↦ dist (function endpoints.val.1) (function endpoints.val.2))
      totalDistance) :
    dist (function lower) (function upper) ≤ totalDistance := by
  let intervalCoefficients (selected : Finset intervals) : Finset (ℝ × ℝ) :=
    selected.image Subtype.val
  replace hInterior (selected : Finset intervals) :
      ∀ ⦃endpoints : ℝ × ℝ⦄, endpoints ∈ intervalCoefficients selected →
        lower ≤ endpoints.1 ∧ endpoints.1 ≤ endpoints.2 ∧ endpoints.2 ≤ upper := by
    grind
  replace hDisjoint (selected : Finset intervals) :
      (SetLike.coe (intervalCoefficients selected)).PairwiseDisjoint
        fun endpoints ↦ Icc endpoints.1 endpoints.2 :=
    hDisjoint.subset (by grind)
  let gaps (selected : Finset intervals) :=
    ((intervalCoefficients selected).card + 1,
      fun index : ℕ ↦ (intervalCoefficients selected).intervalGapsWithin rfl lower upper index)
  have hGapLower (selected : Finset intervals) (index : ℕ) :=
    (intervalCoefficients selected).intervalGapsWithin_le_fst rfl index (hInterior selected)
  have hGapOrdered (selected : Finset intervals) (index : ℕ) :=
    (intervalCoefficients selected).intervalGapsWithin_fst_le_snd rfl index hBounds
      (hInterior selected) (hDisjoint selected)
  have hGapUpper (selected : Finset intervals) (index : ℕ) :=
    (intervalCoefficients selected).intervalGapsWithin_snd_le rfl index (hInterior selected)
  have hGapDisjoint (selected : Finset intervals) :=
    (intervalCoefficients selected).intervalGapsWithin_pairwiseDisjoint_Ioc rfl
      (hInterior selected)
  have hGapsMap : univ.MapsTo gaps
      (AbsolutelyContinuousOnInterval.disjWithin lower upper) := by
    intro selected _
    rw [AbsolutelyContinuousOnInterval.disjWithin]
    constructor
    · intro index hIndex
      dsimp only [gaps]
      rw [uIcc_of_le hBounds]
      exact ⟨⟨hGapLower selected index,
          (hGapOrdered selected index).trans (hGapUpper selected index)⟩,
        ⟨(hGapLower selected index).trans (hGapOrdered selected index),
          hGapUpper selected index⟩⟩
    · dsimp only [gaps]
      simpa only [Finset.coe_range, uIoc_of_le (hGapOrdered selected _)] using
        hGapDisjoint selected
  have hCoefficientsSum (selected : Finset intervals) (summand : ℝ → ℝ → ℝ) :
      ∑ endpoints ∈ selected, summand endpoints.val.1 endpoints.val.2 =
        ∑ endpoints ∈ intervalCoefficients selected, summand endpoints.1 endpoints.2 :=
    Finset.sum_nbij Subtype.val (by simp [intervalCoefficients]) (by simp)
      (by simp only [Finset.coe_image, intervalCoefficients]; tauto) (by simp)
  replace hLength : Tendsto gaps atTop
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin lower upper)) := by
    refine tendsto_inf.mpr ⟨?_, hGapsMap.tendsto.mono_left (by simp)⟩
    simp only [AbsolutelyContinuousOnInterval.totalLengthFilter, tendsto_comap_iff]
    convert! hLength.const_sub (upper - lower) with selected
    · simp only [comp_apply]
      rw [Finset.sum_congr rfl
        (g := fun index ↦ ((gaps selected).2 index).2 - ((gaps selected).2 index).1)
        (fun index hIndex ↦ by
          rw [dist_comm, Real.dist_eq, abs_of_nonneg (by grind)])]
      convert! FiniteMarkovProcesses.Finset.sum_intervalGapsWithin_eq_sub_sub_sum
        (intervalCoefficients selected) rfl id
      exact hCoefficientsSum selected fun x y ↦ y - x
    · abel
  rw [HasSum] at hDistance
  simp_rw [hCoefficientsSum _ fun x y ↦ dist (function x) (function y)] at hDistance
  have hLimit := hContinuous.comp hLength |>.add hDistance
  simp only [comp_apply, zero_add] at hLimit
  have hFiniteBound (selected : Finset intervals) :
      dist (function lower) (function upper) ≤
        ∑ index ∈ Finset.range (gaps selected).1,
          dist (function ((gaps selected).2 index).1)
            (function ((gaps selected).2 index).2) +
        ∑ endpoints ∈ intervalCoefficients selected,
          dist (function endpoints.1) (function endpoints.2) := by
    rw [FiniteMarkovProcesses.Finset.sum_eq_sum_range_intervalGapsWithin _ rfl
      (fun x y ↦ dist (function x) (function y)), Finset.sum_range_succ,
      add_right_comm, ← Finset.sum_add_distrib]
    grw [← Finset.sum_le_sum (fun _ _ ↦ dist_triangle _ _ _),
      ← dist_le_range_sum_dist, ← dist_triangle]
    simp [gaps]
  exact le_of_tendsto_of_tendsto' (by simp) hLimit hFiniteBound

/-- An absolutely continuous function with a.e. zero derivative is constant. -/
theorem AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero
    {function : ℝ → F} {a b : ℝ}
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function a b)
    (hDerivative : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt function 0 x) :
    ∃ constant, ∀ x ∈ uIcc a b, function x = constant := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this (a := b) (b := a) hContinuous.symm
      (uIcc_comm a b ▸ hDerivative) (by linarith)
  suffices ∀ x ∈ uIcc a b, function x = function b by
    exact ⟨function b, this⟩
  rw [uIcc_of_le hab] at hDerivative ⊢
  intro lower hLower
  suffices ∀ radius > 0, dist (function lower) (function b) ≤ radius by
    contrapose! this
    exact exists_between (dist_pos.mpr this)
  intro radius hRadius
  rw [mem_Icc] at hLower
  rcases hLower.right.eq_or_lt with rfl | hLowerUpper
  · simp [hRadius.le]
  replace hDerivative : ∀ᵐ x, x ∈ Ioo lower b → HasDerivAt function 0 x := by
    filter_upwards [hDerivative] with x hX _
    exact hX (by grind)
  have hTolerance : 0 < radius / (b - lower) := by
    apply div_pos <;> linarith
  obtain ⟨intervals, hIntervals, hDisjoint, hLength⟩ :=
    exists_dist_slope_lt_pairwiseDisjoint_hasSum hLower.right hDerivative hTolerance
  let distance := fun endpoints : intervals ↦
    dist (function endpoints.val.1) (function endpoints.val.2)
  have hDistanceNonnegative : 0 ≤ distance := by intro; simp [distance]
  have hFiniteDistance (selected : Finset intervals) :
      ∑ endpoints ∈ selected, distance endpoints ≤ radius := by
    have hEach (endpoints : intervals) (_ : endpoints ∈ selected) :
        distance endpoints ≤
          radius / (b - lower) * (endpoints.val.2 - endpoints.val.1) := by
      have hSlope := (hIntervals endpoints (by simp)).right.le
      have hPositive : 0 < endpoints.val.2 - endpoints.val.1 := by
        linarith [hIntervals endpoints (by simp)]
      grw [← hSlope]
      simp only [dist_eq_norm, slope, vsub_eq_sub, sub_zero, distance, mul_comm]
      nth_rw 1 [← Real.norm_of_nonneg hPositive.le]
      simp only [norm_smul, Real.norm_eq_abs, norm_inv]
      field_simp
      rw [norm_sub_rev]
    grw [Finset.sum_le_sum hEach]
    rw [← Finset.mul_sum]
    have hPartial : ∑ endpoints ∈ selected,
        (endpoints.val.2 - endpoints.val.1) ≤ b - lower :=
      hLength.tsum_eq ▸ Summable.sum_le_tsum _ (by grind) hLength.summable
    grw [hPartial]
    field_simp
    grind
  have hDistanceSum := summable_of_sum_le hDistanceNonnegative hFiniteDistance |>.hasSum
  have hTotalDistance := hDistanceSum.summable.tsum_le_of_sum_le hFiniteDistance
  have hRestrictedSubset : uIcc lower b ⊆ uIcc a b := by
    rw [uIcc_of_le hab, uIcc_of_le hLower.right]
    intro point hPoint
    exact ⟨hLower.left.trans hPoint.1, hPoint.2⟩
  have hFill :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.dist_le_of_pairwiseDisjoint_hasSum
      hLower.right (hContinuous.mono hRestrictedSubset)
      (fun endpoints hEndpoints ↦ (hIntervals endpoints hEndpoints).left)
      hDisjoint hLength hDistanceSum
  linarith

/-- Fundamental theorem of calculus for absolutely continuous real functions. -/
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    {function : ℝ → ℝ} {a b : ℝ}
    (hContinuous : _root_.AbsolutelyContinuousOnInterval function a b) :
    ∫ x in a..b, deriv function x = function b - function a := by
  have hPrimitiveContinuous :=
    intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral
      hContinuous.intervalIntegrable_deriv (c := a) (by simp)
  let residual := fun x ↦ function x - ∫ t in a..x, deriv function t
  have hResidualContinuous : _root_.AbsolutelyContinuousOnInterval residual a b :=
    hContinuous.sub hPrimitiveContinuous
  have hResidualDerivative : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt residual 0 x := by
    filter_upwards [hContinuous.ae_differentiableAt,
      hContinuous.intervalIntegrable_deriv.ae_hasDerivAt_integral]
      with x hFunction hPrimitive hX
    convert (hFunction hX).hasDerivAt.sub (hPrimitive hX a (by simp))
    abel
  obtain ⟨constant, hConstant⟩ :=
    FiniteMarkovProcesses.AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero
      hResidualContinuous hResidualDerivative
  have hAtA : function a = residual a := by simp [residual]
  have hConstantA := hConstant a (by simp)
  have hConstantB := hConstant b (by simp)
  grind

end FiniteMarkovProcesses
