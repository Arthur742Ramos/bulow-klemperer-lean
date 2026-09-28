module

public import BulowKlemperer.Probability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory
open Filter
open TopologicalSpace
open scoped ENNReal Topology

namespace BulowKlemperer

/-- A direct mechanism. Interim probabilities and payments integrate out the other bids
under the common i.i.d. product law. The overwritten coordinate is immaterial. -/
public structure DirectMechanism (D : ValueDistribution) (n : ℕ) where
  allocation : Fin n → (Fin n → ℝ) → ℝ
  payment : Fin n → (Fin n → ℝ) → ℝ
  allocation_integrable : ∀ i x, Integrable (fun v => allocation i (Function.update v i x)) (D.jointLaw n)
  payment_integrable : ∀ i x, Integrable (fun v => payment i (Function.update v i x)) (D.jointLaw n)
  allocation_nonneg : ∀ i v, 0 ≤ allocation i v
  allocation_feasible : ∀ v, ∑ i : Fin n, allocation i v ≤ 1

namespace DirectMechanism

@[expose] public noncomputable def interimAllocation {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) : ℝ :=
  ∫ v, M.allocation i (Function.update v i x) ∂D.jointLaw n

@[expose] public noncomputable def interimPayment {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) : ℝ :=
  ∫ v, M.payment i (Function.update v i x) ∂D.jointLaw n

@[expose] public noncomputable def interimUtility {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) : ℝ :=
  x * M.interimAllocation i x - M.interimPayment i x

/-- Truthful reporting maximizes expected utility for every value in the closed support. -/
public def BIC {D : ValueDistribution} {n : ℕ} (M : DirectMechanism D n) : Prop :=
  ∀ i (x y : ℝ), x ∈ Set.Icc 0 D.omega → y ∈ Set.Icc 0 D.omega →
    x * M.interimAllocation i y - M.interimPayment i y ≤ M.interimUtility i x

public theorem allocation_le_one {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (v : Fin n → ℝ) :
    M.allocation i v ≤ 1 := by
  have hsum : M.allocation i v ≤ ∑ j : Fin n, M.allocation j v := by
    exact Finset.single_le_sum (fun j _ => M.allocation_nonneg j v) (Finset.mem_univ i)
  exact hsum.trans (M.allocation_feasible v)

public theorem interimAllocation_nonneg {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) :
    0 ≤ M.interimAllocation i x := by
  exact integral_nonneg fun v => M.allocation_nonneg i _

public theorem interimAllocation_le_one {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) :
    M.interimAllocation i x ≤ 1 := by
  let : IsProbabilityMeasure (D.jointLaw n) := D.jointLaw_probability n
  calc
    M.interimAllocation i x ≤ ∫ _v : Fin n → ℝ, (1 : ℝ) ∂D.jointLaw n := by
      apply integral_mono (M.allocation_integrable i x) (integrable_const (1 : ℝ))
      intro v
      exact M.allocation_le_one i _
    _ = 1 := by simp

public theorem utility_increment_bounds {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 D.omega) (hy : y ∈ Set.Icc 0 D.omega) :
    (y - x) * M.interimAllocation i x ≤ M.interimUtility i y - M.interimUtility i x ∧
    M.interimUtility i y - M.interimUtility i x ≤
      (y - x) * M.interimAllocation i y := by
  have hxy := hBIC i x y hx hy
  have hyx := hBIC i y x hy hx
  dsimp [interimUtility] at *
  constructor <;> nlinarith

public theorem interimAllocation_monotoneOn {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n) :
    MonotoneOn (M.interimAllocation i) (Set.Icc 0 D.omega) := by
  intro x hx y hy hxy
  obtain ⟨h1, h2⟩ := M.utility_increment_bounds hBIC i hx hy
  have h : (y - x) * M.interimAllocation i x ≤
      (y - x) * M.interimAllocation i y := le_trans h1 h2
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact le_of_mul_le_mul_left h (sub_pos.mpr hlt)

public theorem interimUtility_lipschitz {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n) :
    LipschitzOnWith 1 (M.interimUtility i) (Set.Icc 0 D.omega) := by
  apply LipschitzOnWith.of_le_add_mul 1
  intro x hx y hy
  by_cases hxy : y ≤ x
  · have h := (M.utility_increment_bounds hBIC i hy hx).2
    have hq := M.interimAllocation_le_one i x
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)]
    calc
      M.interimUtility i x ≤ M.interimUtility i y + (x - y) * M.interimAllocation i x := by linarith
      _ ≤ M.interimUtility i y + (x - y) * 1 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hxy)) _
      _ = M.interimUtility i y + 1 * (x - y) := by ring
  · have h := (M.utility_increment_bounds hBIC i hx hy).1
    have hq := M.interimAllocation_nonneg i x
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hxy)))]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hxy))) hq]

public theorem interimUtility_absolutelyContinuous {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n) :
    AbsolutelyContinuousOnInterval (M.interimUtility i) 0 D.omega := by
  exact (show LipschitzOnWith 1 (M.interimUtility i) (Set.uIcc 0 D.omega) from
    (Set.uIcc_of_le D.omega_pos.le).symm ▸ M.interimUtility_lipschitz hBIC i).absolutelyContinuousOnInterval

/-- At interior values, the BIC supporting-line inequalities squeeze utility slopes
between nearby interim allocations. -/
public theorem interimUtility_hasDerivAt {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : ContinuousOn (M.interimAllocation i) (Set.Icc 0 D.omega))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 D.omega) :
    HasDerivAt (M.interimUtility i) (M.interimAllocation i x) x := by
  have hQx : ContinuousAt (M.interimAllocation i) x :=
    hQ.continuousAt (Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2)
      Set.Ioo_subset_Icc_self)
  have hIcc : Set.Icc 0 D.omega ∈ nhds x :=
    Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
  have hIcc_left : ∀ᶠ y in 𝓝[<] x, y ∈ Set.Icc 0 D.omega :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hIcc
  have hIcc_right : ∀ᶠ y in 𝓝[>] x, y ∈ Set.Icc 0 D.omega :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hIcc
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hQx.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
    · filter_upwards [hIcc_left, self_mem_nhdsWithin]
        with y hy hyx
      have hb := M.utility_increment_bounds hBIC i hy (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩)
      have hpos : 0 < x - y := sub_pos.mpr hyx
      rw [slope_def_field, show M.interimUtility i y - M.interimUtility i x =
        -(M.interimUtility i x - M.interimUtility i y) by ring,
        show y - x = -(x - y) by ring, neg_div_neg_eq]
      exact (le_div_iff₀ hpos).2 (by nlinarith [hb.1])
    · filter_upwards [hIcc_left, self_mem_nhdsWithin]
        with y hy hyx
      have hb := M.utility_increment_bounds hBIC i hy (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩)
      rw [slope_def_field, show M.interimUtility i y - M.interimUtility i x =
        -(M.interimUtility i x - M.interimUtility i y) by ring,
        show y - x = -(x - y) by ring, neg_div_neg_eq]
      exact (div_le_iff₀ (sub_pos.mpr hyx)).2 (by nlinarith [hb.2])
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (hQx.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [hIcc_right, self_mem_nhdsWithin]
        with y hy hxy
      have hb := M.utility_increment_bounds hBIC i (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩) hy
      rw [slope_def_field]
      exact (le_div_iff₀ (sub_pos.mpr hxy)).2 (by nlinarith [hb.1])
    · filter_upwards [hIcc_right, self_mem_nhdsWithin]
        with y hy hxy
      have hb := M.utility_increment_bounds hBIC i (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩) hy
      rw [slope_def_field]
      exact (div_le_iff₀ (sub_pos.mpr hxy)).2 (by nlinarith [hb.2])

/-- The interim utility envelope. BIC supplies the supporting lines; continuity of
interim allocation identifies their common interior slope. -/
public theorem envelope {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : ContinuousOn (M.interimAllocation i) (Set.Icc 0 D.omega))
    {x : ℝ} (hx : x ∈ Set.Icc 0 D.omega) :
    M.interimUtility i x = M.interimUtility i 0 +
      ∫ t in (0 : ℝ)..x, M.interimAllocation i t := by
  have hsub : Set.Icc 0 x ⊆ Set.Icc 0 D.omega := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hx.2⟩
  have hQint : IntervalIntegrable (M.interimAllocation i) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hx.1] using hQ.mono hsub
  have hUcont : ContinuousOn (M.interimUtility i) (Set.Icc 0 x) :=
    (M.interimUtility_lipschitz hBIC i).continuousOn.mono hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hUcont
    (fun t ht => M.interimUtility_hasDerivAt hBIC i hQ
      ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩) hQint
  linarith

public theorem primitive_nonneg {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ t in (0 : ℝ)..x, M.interimAllocation i t :=
  intervalIntegral.integral_nonneg_of_forall hx (M.interimAllocation_nonneg i)

public theorem primitive_le_value {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ≤ x := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := x)
    (f := M.interimAllocation i) (g := fun _ => (1 : ℝ)) hx
    (hQ.intervalIntegrable 0 x) (intervalIntegrable_const) (fun t _ => M.interimAllocation_le_one i t)
  simpa using h

public theorem primitive_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    Integrable (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  have hcont : Continuous (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) :=
    intervalIntegral.continuous_primitive (fun a b => hQ.intervalIntegrable a b) 0
  apply Integrable.of_bound hcont.measurable.aestronglyMeasurable D.omega
  filter_upwards [D.value_mem] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (M.primitive_nonneg i hx.1)]
  exact (M.primitive_le_value i hQ hx.1).trans hx.2

@[expose] public noncomputable def weightedTail {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) : ℝ :=
  (Set.Ioo 0 D.omega).indicator
    (fun t => (1 - D.cdf t) * M.interimAllocation i t) x

public theorem weightedTail_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    Integrable (M.weightedTail i) volume := by
  have hcont : Continuous (fun x : ℝ => (1 - D.cdf x) * M.interimAllocation i x) :=
    (continuous_const.sub D.cdf_continuous).mul hQ
  have hIcc : IntegrableOn (fun x : ℝ => (1 - D.cdf x) * M.interimAllocation i x)
      (Set.Icc 0 D.omega) volume := hcont.continuousOn.integrableOn_Icc
  exact (hIcc.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

public theorem density_mul_weightedHazard {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) :
    (ENNReal.ofReal (D.density x)).toReal *
      (D.hazardTerm x * M.interimAllocation i x) = M.weightedTail i x := by
  rw [← mul_assoc, D.density_mul_hazard]
  unfold weightedTail ValueDistribution.truncatedTail
  by_cases hx : x ∈ Set.Ioo 0 D.omega
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

public theorem weightedHazard_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    Integrable (fun x => D.hazardTerm x * M.interimAllocation i x) D.law := by
  rw [D.law_eq_withDensity]
  rw [integrable_withDensity_iff_integrable_smul'
    (D.density_measurable.ennreal_ofReal) (by simp)]
  convert M.weightedTail_integrable i hQ using 1
  funext x
  simpa only [smul_eq_mul] using M.density_mul_weightedHazard i x

public theorem weightedHazard_integral {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    (∫ x, D.hazardTerm x * M.interimAllocation i x ∂D.law) =
      ∫ x, M.weightedTail i x := by
  rw [D.law_eq_withDensity]
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.density_measurable.ennreal_ofReal) (by simp)]
  apply integral_congr_ae
  filter_upwards with x
  simpa only [smul_eq_mul] using M.density_mul_weightedHazard i x

public theorem weightedTail_nonneg {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) :
    0 ≤ M.weightedTail i x := by
  unfold weightedTail
  by_cases hx : x ∈ Set.Ioo 0 D.omega
  · rw [Set.indicator_of_mem hx, ← D.tail_probability]
    exact mul_nonneg (measureReal_nonneg) (M.interimAllocation_nonneg i x)
  · simp [Set.indicator_of_notMem hx]

public theorem weightedTail_eq_layercake {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (x : ℝ) :
    ENNReal.ofReal (M.weightedTail i x) =
      (Set.Ioi 0).indicator
        (fun t => D.law (Set.Ioi t) * ENNReal.ofReal (M.interimAllocation i t)) x := by
  by_cases hx0 : 0 < x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ioi 0 from hx0)]
    have hfin : D.law (Set.Ioi x) ≠ ∞ := by
      let : IsProbabilityMeasure D.law := D.probability
      exact measure_ne_top D.law _
    rw [← ENNReal.ofReal_toReal hfin,
      show (D.law (Set.Ioi x)).toReal = 1 - D.cdf x from D.tail_probability x]
    by_cases hxw : x < D.omega
    · have hx : x ∈ Set.Ioo 0 D.omega := ⟨hx0, hxw⟩
      rw [weightedTail, Set.indicator_of_mem hx]
      have htail : 0 ≤ 1 - D.cdf x := by
        rw [← D.tail_probability]
        exact measureReal_nonneg
      rw [ENNReal.ofReal_mul htail]
    · have hw : D.omega ≤ x := le_of_not_gt hxw
      simp [weightedTail, Set.indicator_of_notMem (show x ∉ Set.Ioo 0 D.omega from
        fun h => hxw h.2), D.cdf_above x hw]
  · have hx : x ∉ Set.Ioo 0 D.omega := fun h => hx0 h.1
    simp [weightedTail, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ Set.Ioi 0 from hx0)]

public theorem weighted_tail_eq_primitive_integral {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    (∫ x, (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law) =
      ∫ x, M.weightedTail i x := by
  have hLayer := lintegral_comp_eq_lintegral_meas_lt_mul
    (f := fun x : ℝ => x) (g := M.interimAllocation i) D.law
    D.value_nonneg_ae measurable_id.aemeasurable
    (fun t ht => hQ.intervalIntegrable 0 t)
    (Eventually.of_forall fun t => M.interimAllocation_nonneg i t)
  have hLeft : 0 ≤ᵐ[D.law]
      (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) := by
    filter_upwards [D.value_mem] with x hx
    exact M.primitive_nonneg i hx.1
  rw [integral_eq_lintegral_of_nonneg_ae hLeft
    (M.primitive_integrable i hQ).aestronglyMeasurable, hLayer]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => M.weightedTail_nonneg i x)
    (M.weightedTail_integrable i hQ).aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro x
  exact (M.weightedTail_eq_layercake i x).symm

public theorem value_mul_allocation_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    Integrable (fun x => x * M.interimAllocation i x) D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  apply Integrable.of_bound
    (continuous_id.mul hQ).measurable.aestronglyMeasurable D.omega
  filter_upwards [D.value_mem] with x hx
  have hnonneg : 0 ≤ x * M.interimAllocation i x :=
    mul_nonneg hx.1 (M.interimAllocation_nonneg i x)
  change ‖x * M.interimAllocation i x‖ ≤ D.omega
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    x * M.interimAllocation i x ≤ x * 1 :=
      mul_le_mul_of_nonneg_left (M.interimAllocation_le_one i x) hx.1
    _ = x := mul_one x
    _ ≤ D.omega := hx.2

public theorem payment_eq_envelope_ae {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : ContinuousOn (M.interimAllocation i) (Set.Icc 0 D.omega))
    (hU0 : M.interimUtility i 0 = 0) :
    (M.interimPayment i) =ᵐ[D.law]
      (fun x => x * M.interimAllocation i x -
        ∫ t in (0 : ℝ)..x, M.interimAllocation i t) := by
  filter_upwards [D.value_mem] with x hx
  have henv := M.envelope hBIC i hQ hx
  rw [hU0] at henv
  change x * M.interimAllocation i x - M.interimPayment i x =
    0 + ∫ t in (0 : ℝ)..x, M.interimAllocation i t at henv
  linarith

public theorem interimPayment_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i))
    (hU0 : M.interimUtility i 0 = 0) :
    Integrable (M.interimPayment i) D.law := by
  have hp := M.payment_eq_envelope_ae hBIC i hQ.continuousOn hU0
  exact ((M.value_mul_allocation_integrable i hQ).sub
    (M.primitive_integrable i hQ)).congr hp.symm

public theorem virtualValue_mul_allocation_integrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i)) :
    Integrable (fun x => D.virtualValue x * M.interimAllocation i x) D.law := by
  convert (M.value_mul_allocation_integrable i hQ).sub
    (M.weightedHazard_integrable i hQ) using 1
  funext x
  unfold ValueDistribution.virtualValue ValueDistribution.hazardTerm
  simp only [Pi.sub_apply]
  ring

/-- Myerson's single-bidder payment identity for a direct BIC mechanism.
The normalization is interim utility at zero. No regularity of virtual values is used. -/
public theorem revenue_formula {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i))
    (hU0 : M.interimUtility i 0 = 0) :
    (∫ x, M.interimPayment i x ∂D.law) =
      ∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law := by
  have hPae := M.payment_eq_envelope_ae hBIC i hQ.continuousOn hU0
  calc
    (∫ x, M.interimPayment i x ∂D.law) =
        ∫ x, x * M.interimAllocation i x -
          (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law :=
      integral_congr_ae hPae
    _ = (∫ x, x * M.interimAllocation i x ∂D.law) -
        (∫ x, (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law) :=
      integral_sub (M.value_mul_allocation_integrable i hQ) (M.primitive_integrable i hQ)
    _ = (∫ x, x * M.interimAllocation i x ∂D.law) -
        (∫ x, D.hazardTerm x * M.interimAllocation i x ∂D.law) := by
      rw [M.weighted_tail_eq_primitive_integral i hQ, M.weightedHazard_integral]
    _ = ∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law := by
      rw [← integral_sub (M.value_mul_allocation_integrable i hQ)
        (M.weightedHazard_integrable i hQ)]
      apply integral_congr_ae
      filter_upwards with x
      unfold ValueDistribution.virtualValue ValueDistribution.hazardTerm
      ring

end DirectMechanism
end BulowKlemperer
