module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace BulowKlemperer

/-- A common, compactly supported continuous distribution of private values.  The
law is represented by its Lebesgue density, and its cdf is the actual measure
of a lower half-line. -/
public structure ValueDistribution where
  omega : ℝ
  omega_pos : 0 < omega
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  density : ℝ → ℝ
  density_measurable : Measurable density
  density_nonneg : ∀ x, 0 ≤ density x
  density_pos : ∀ x ∈ Set.Ioo 0 omega, 0 < density x
  density_zero : ∀ x ∉ Set.Ioo 0 omega, density x = 0
  law_eq_withDensity : law = volume.withDensity (fun x => ENNReal.ofReal (density x))
  cdf : ℝ → ℝ
  cdf_eq : ∀ x, cdf x = law.real (Set.Iic x)
  cdf_continuous : Continuous cdf
  cdf_zero : cdf 0 = 0
  cdf_above : ∀ x, omega ≤ x → cdf x = 1
  value_mem : ∀ᵐ x ∂law, x ∈ Set.Icc 0 omega
  value_mem_open : ∀ᵐ x ∂law, x ∈ Set.Ioo 0 omega

namespace ValueDistribution

@[expose] public noncomputable def virtualValue (D : ValueDistribution) (x : ℝ) : ℝ :=
  x - (1 - D.cdf x) / D.density x

@[expose] public noncomputable def hazardTerm (D : ValueDistribution) (x : ℝ) : ℝ :=
  (1 - D.cdf x) / D.density x

@[expose] public noncomputable def truncatedTail (D : ValueDistribution) (x : ℝ) : ℝ :=
  (Set.Ioo 0 D.omega).indicator (fun t => 1 - D.cdf t) x

public theorem value_integrable (D : ValueDistribution) :
    Integrable (fun x : ℝ => x) D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  apply Integrable.of_bound measurable_id.aestronglyMeasurable D.omega
  filter_upwards [D.value_mem] with x hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

public theorem value_nonneg_ae (D : ValueDistribution) :
    0 ≤ᵐ[D.law] (fun x : ℝ => x) := by
  filter_upwards [D.value_mem] with x hx
  exact hx.1

public theorem tail_integrable (D : ValueDistribution) :
    Integrable D.truncatedTail volume := by
  have hcont : Continuous (fun x : ℝ => 1 - D.cdf x) :=
    continuous_const.sub D.cdf_continuous
  have hIcc : IntegrableOn (fun x : ℝ => 1 - D.cdf x)
      (Set.Icc 0 D.omega) volume :=
    hcont.continuousOn.integrableOn_Icc
  have hIoo : IntegrableOn (fun x : ℝ => 1 - D.cdf x)
      (Set.Ioo 0 D.omega) volume :=
    hIcc.mono_set Set.Ioo_subset_Icc_self
  exact hIoo.integrable_indicator measurableSet_Ioo

public theorem density_mul_hazard (D : ValueDistribution) (x : ℝ) :
    (ENNReal.ofReal (D.density x)).toReal * D.hazardTerm x = D.truncatedTail x := by
  by_cases hx : x ∈ Set.Ioo 0 D.omega
  · rw [ENNReal.toReal_ofReal (D.density_nonneg x)]
    have hf := ne_of_gt (D.density_pos x hx)
    simp only [hazardTerm, truncatedTail, Set.indicator_of_mem hx]
    field_simp
  · rw [D.density_zero x hx]
    simp [hazardTerm, truncatedTail, Set.indicator_of_notMem hx]

public theorem hazard_integrable (D : ValueDistribution) :
    Integrable D.hazardTerm D.law := by
  rw [D.law_eq_withDensity]
  rw [integrable_withDensity_iff_integrable_smul'
    (D.density_measurable.ennreal_ofReal) (by simp)]
  convert D.tail_integrable using 1
  funext x
  simpa only [smul_eq_mul] using D.density_mul_hazard x

public theorem hazard_integral_eq_tail_integral (D : ValueDistribution) :
    (∫ x, D.hazardTerm x ∂D.law) = ∫ x, D.truncatedTail x := by
  rw [D.law_eq_withDensity]
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.density_measurable.ennreal_ofReal) (by simp)]
  apply integral_congr_ae
  filter_upwards with x
  simpa only [smul_eq_mul] using D.density_mul_hazard x

public theorem tail_probability (D : ValueDistribution) (x : ℝ) :
    D.law.real (Set.Ioi x) = 1 - D.cdf x := by
  let : IsProbabilityMeasure D.law := D.probability
  rw [← Set.compl_Iic]
  rw [probReal_compl_eq_one_sub measurableSet_Iic]
  rw [D.cdf_eq]

public theorem tail_integral_eq_value_integral (D : ValueDistribution) :
    (∫ x, D.truncatedTail x) = ∫ x, x ∂D.law := by
  have htail : ∀ x : ℝ,
      (Set.Ioi 0).indicator (fun t => 1 - D.cdf t) x = D.truncatedTail x := by
    intro x
    by_cases hx0 : 0 < x
    · by_cases hxw : x < D.omega
      · simp [truncatedTail, Set.indicator_of_mem, hx0, hxw]
      · have hw : D.omega ≤ x := le_of_not_gt hxw
        simp [truncatedTail, Set.indicator_of_mem, Set.indicator_of_notMem,
          hx0, hxw, D.cdf_above x hw]
    · simp [truncatedTail, Set.indicator_of_notMem, hx0]
  calc
    (∫ x, D.truncatedTail x) = ∫ x in Set.Ioi (0 : ℝ), 1 - D.cdf x := by
      rw [← integral_indicator measurableSet_Ioi]
      simp_rw [htail]
    _ = ∫ x in Set.Ioi (0 : ℝ), D.law.real {y : ℝ | x < y} := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact (D.tail_probability x).symm
    _ = ∫ x, x ∂D.law :=
      (D.value_integrable.integral_eq_integral_meas_lt D.value_nonneg_ae).symm

/-- Integration by parts in tail form: the expected virtual value of one draw is zero. -/
public theorem virtualValue_mean_zero (D : ValueDistribution) :
    (∫ x, D.virtualValue x ∂D.law) = 0 := by
  have hratio : (∫ x, D.hazardTerm x ∂D.law) = ∫ x, x ∂D.law :=
    (D.hazard_integral_eq_tail_integral).trans D.tail_integral_eq_value_integral
  change (∫ x, x - D.hazardTerm x ∂D.law) = 0
  rw [integral_sub D.value_integrable D.hazard_integrable, hratio, sub_self]

public theorem virtualValue_integrable (D : ValueDistribution) :
    Integrable D.virtualValue D.law := by
  change Integrable (fun x => x - D.hazardTerm x) D.law
  exact D.value_integrable.sub D.hazard_integrable

public theorem virtualValue_measurable (D : ValueDistribution) :
    Measurable D.virtualValue := by
  unfold virtualValue
  exact measurable_id.sub ((measurable_const.sub D.cdf_continuous.measurable).div
    D.density_measurable)

/-- Regularity of the common value distribution. -/
@[expose] public def Regular (D : ValueDistribution) : Prop :=
  StrictMonoOn D.virtualValue (Set.Ioo 0 D.omega)

/-- The product law of `n` independent draws from the common distribution. -/
@[expose] public noncomputable def jointLaw (D : ValueDistribution) (n : ℕ) :
    Measure (Fin n → ℝ) := Measure.pi (fun _ => D.law)

public theorem jointLaw_probability (D : ValueDistribution) (n : ℕ) :
    IsProbabilityMeasure (D.jointLaw n) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => D.law))
  exact @Measure.pi.instIsProbabilityMeasure (Fin n) (fun _ => ℝ)
    inferInstance (fun _ => inferInstance) (fun _ => D.law) (fun _ => D.probability)

@[expose] public def draw (_D : ValueDistribution) {n : ℕ} (i : Fin n)
    (v : Fin n → ℝ) : ℝ := v i

public theorem draw_law (D : ValueDistribution) {n : ℕ} (i : Fin n) :
    (D.jointLaw n).map (D.draw i) = D.law := by
  have hprob : ∀ _ : Fin n, IsProbabilityMeasure D.law := fun _ => D.probability
  change (Measure.pi (fun _ : Fin n => D.law)).map (Function.eval i) = D.law
  exact (@measurePreserving_eval (Fin n) (fun _ => ℝ) inferInstance
    (fun _ => inferInstance) (fun _ => D.law) hprob i).map_eq

public theorem draws_independent (D : ValueDistribution) (n : ℕ) :
    iIndepFun (fun i v => D.draw i v) (D.jointLaw n) := by
  have hprob : ∀ _ : Fin n, IsProbabilityMeasure D.law := fun _ => D.probability
  change iIndepFun (fun i v => v i) (Measure.pi (fun _ : Fin n => D.law))
  simpa only [id_eq] using
    (@iIndepFun_pi (Fin n) inferInstance (fun _ => ℝ) (fun _ => inferInstance)
      (fun _ => D.law) hprob (fun _ => ℝ) (fun _ => inferInstance)
      (fun _ => id) (fun _ => aemeasurable_id))

public theorem draw_integrable (D : ValueDistribution) {n : ℕ} (i : Fin n) :
    Integrable (D.draw i) (D.jointLaw n) := by
  have h : Integrable (fun x : ℝ => x) ((D.jointLaw n).map (D.draw i)) := by
    rw [D.draw_law i]
    exact D.value_integrable
  change Integrable ((fun x : ℝ => x) ∘ D.draw i) (D.jointLaw n)
  exact h.comp_measurable (measurable_pi_apply i)

public theorem draw_virtual_integrable (D : ValueDistribution) {n : ℕ} (i : Fin n) :
    Integrable (fun v => D.virtualValue (D.draw i v)) (D.jointLaw n) := by
  have h : Integrable D.virtualValue ((D.jointLaw n).map (D.draw i)) := by
    rw [D.draw_law i]
    exact D.virtualValue_integrable
  change Integrable (D.virtualValue ∘ D.draw i) (D.jointLaw n)
  exact h.comp_measurable (measurable_pi_apply i)

public theorem draw_virtual_mean_zero (D : ValueDistribution) {n : ℕ} (i : Fin n) :
    (∫ v, D.virtualValue (D.draw i v) ∂D.jointLaw n) = 0 := by
  have h := integral_map (μ := D.jointLaw n) (φ := D.draw i)
    (measurable_pi_apply i).aemeasurable
    (show AEStronglyMeasurable D.virtualValue ((D.jointLaw n).map (D.draw i)) from
      D.virtualValue_measurable.aestronglyMeasurable)
  rw [D.draw_law i] at h
  exact h.symm.trans D.virtualValue_mean_zero

public theorem draws_mem_open_ae (D : ValueDistribution) (n : ℕ) :
    ∀ᵐ v ∂D.jointLaw n, ∀ i : Fin n, D.draw i v ∈ Set.Ioo 0 D.omega := by
  apply ae_all_iff.2
  intro i
  apply ae_of_ae_map (f := D.draw i) (measurable_pi_apply i).aemeasurable
  rw [D.draw_law i]
  exact D.value_mem_open

public theorem finsetSup_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (s : Finset ι) (hs : s.Nonempty) :
    Integrable (fun x => s.sup' hs (fun i => f i x)) μ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa only [Finset.sup'_singleton] using hf a
  | cons a s ha hs ih =>
    have h := (hf a).sup ih
    convert h using 1
    funext x
    exact Finset.sup'_cons hs (fun i => f i x)

public noncomputable def maxValue (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => D.draw i v)

@[expose] public noncomputable def maxVirtual (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => D.virtualValue (D.draw i v))

public theorem maxValue_integrable (D : ValueDistribution) (n : ℕ) :
    Integrable (D.maxValue n) (D.jointLaw (n + 1)) := by
  change Integrable (fun v => (Finset.univ : Finset (Fin (n + 1))).sup'
    Finset.univ_nonempty (fun i => D.draw i v)) (D.jointLaw (n + 1))
  exact finsetSup_integrable (fun i => D.draw i) (fun i => D.draw_integrable i)
    Finset.univ Finset.univ_nonempty

public theorem maxVirtual_integrable (D : ValueDistribution) (n : ℕ) :
    Integrable (D.maxVirtual n) (D.jointLaw (n + 1)) := by
  change Integrable (fun v => (Finset.univ : Finset (Fin (n + 1))).sup'
    Finset.univ_nonempty (fun i => D.virtualValue (D.draw i v))) (D.jointLaw (n + 1))
  exact finsetSup_integrable (fun i v => D.virtualValue (D.draw i v))
    (fun i => D.draw_virtual_integrable i) Finset.univ Finset.univ_nonempty

/-- An increasing virtual value sends the largest realized value to the
largest realized virtual value. -/
public theorem virtualValue_max (D : ValueDistribution) (hreg : D.Regular)
    (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, D.draw i v ∈ Set.Ioo 0 D.omega) :
    D.virtualValue (D.maxValue n v) = D.maxVirtual n v := by
  let s : Finset (Fin (n + 1)) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  obtain ⟨j, hj, hjmax⟩ := s.exists_mem_eq_sup' hs (fun i => D.draw i v)
  have hmax_mem : D.maxValue n v ∈ Set.Ioo 0 D.omega := by
    change (s.sup' hs (fun i => D.draw i v)) ∈ Set.Ioo 0 D.omega
    rw [hjmax]
    exact hv j
  apply le_antisymm
  · rw [maxValue, hjmax]
    exact Finset.le_sup' (fun i => D.virtualValue (D.draw i v)) hj
  · apply Finset.sup'_le hs
    intro i hi
    apply hreg.monotoneOn (hv i) hmax_mem
    exact Finset.le_sup' (fun i => D.draw i v) hi

public theorem virtualValue_max_ae (D : ValueDistribution) (hreg : D.Regular)
    (n : ℕ) :
    ∀ᵐ v ∂D.jointLaw (n + 1),
      D.virtualValue (D.maxValue n v) = D.maxVirtual n v := by
  filter_upwards [D.draws_mem_open_ae (n + 1)] with v hv
  exact D.virtualValue_max hreg n v hv

end ValueDistribution

end BulowKlemperer
