module

public import BulowKlemperer.Optimal

open MeasureTheory

namespace BulowKlemperer

namespace ValueDistribution

/-- The highest bid other than `i`; it is zero when `i` is the sole bidder. -/
@[expose] public noncomputable def otherMax {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then
    (Finset.univ.erase i).sup' h (fun j => v j)
  else 0

/-- The highest bid wins, with the smallest index winning ties. -/
public def secondPriceWinner {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) : Prop :=
  (∀ j, v j ≤ v i) ∧ (∀ j, v j = v i → i ≤ j)

public theorem secondPriceWinner_measurableSet {n : ℕ} (i : Fin (n + 1)) :
    MeasurableSet {v : Fin (n + 1) → ℝ | secondPriceWinner i v} := by
  have hmax : MeasurableSet {v : Fin (n + 1) → ℝ | ∀ j, v j ≤ v i} := by
    simpa only [Set.iInter_ofPred] using
      (MeasurableSet.iInter (fun j => measurableSet_le
        (measurable_pi_apply j) (measurable_pi_apply i)))
  have htie : MeasurableSet
      {v : Fin (n + 1) → ℝ | ∀ j, v j = v i → i ≤ j} := by
    have h (j : Fin (n + 1)) : MeasurableSet
        {v : Fin (n + 1) → ℝ | v j = v i → i ≤ j} := by
      by_cases hij : i ≤ j
      · simp [hij]
      · simpa [hij, Set.compl_def] using
          (measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply i)).compl
    simpa only [Set.iInter_ofPred] using (MeasurableSet.iInter h)
  exact hmax.inter htie

@[expose] public noncomputable def secondPriceAllocation {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : ℝ :=
  by classical exact if secondPriceWinner i v then 1 else 0

@[expose] public noncomputable def secondPricePayment {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : ℝ :=
  by classical exact if secondPriceWinner i v then otherMax i v else 0

public theorem otherMax_measurable {n : ℕ} (i : Fin (n + 1)) :
    Measurable (otherMax i) := by
  classical
  unfold otherMax
  split_ifs with h
  · convert (Finset.measurable_sup' h (f := fun j (v : Fin (n + 1) → ℝ) => v j)
      (fun j _ => measurable_pi_apply j)) using 1
    funext v
    exact (Finset.sup'_apply h (fun j (v : Fin (n + 1) → ℝ) => v j) v).symm
  · exact measurable_const

public theorem secondPriceAllocation_measurable {n : ℕ} (i : Fin (n + 1)) :
    Measurable (secondPriceAllocation i) := by
  classical
  change Measurable (fun v : Fin (n + 1) → ℝ =>
    if secondPriceWinner i v then (1 : ℝ) else 0)
  exact Measurable.ite (secondPriceWinner_measurableSet i) measurable_const measurable_const

public theorem secondPricePayment_measurable {n : ℕ} (i : Fin (n + 1)) :
    Measurable (secondPricePayment i) := by
  classical
  change Measurable (fun v : Fin (n + 1) → ℝ =>
    if secondPriceWinner i v then otherMax i v else 0)
  exact Measurable.ite (secondPriceWinner_measurableSet i)
    (otherMax_measurable i) measurable_const

public theorem secondPriceWinner_unique {n : ℕ} {i j : Fin (n + 1)}
    {v : Fin (n + 1) → ℝ} (hi : secondPriceWinner i v)
    (hj : secondPriceWinner j v) : i = j := by
  have heq : v j = v i := le_antisymm (hi.1 j) (hj.1 i)
  exact le_antisymm (hi.2 j heq) (hj.2 i heq.symm)

public theorem secondPriceAllocation_feasible {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (∑ i, secondPriceAllocation i v) ≤ 1 := by
  classical
  by_cases h : ∃ i, secondPriceWinner i v
  · obtain ⟨i, hi⟩ := h
    have heq : ∀ j : Fin (n + 1), secondPriceAllocation j v = if j = i then 1 else 0 := by
      intro j
      by_cases hj : secondPriceWinner j v
      · have hji := secondPriceWinner_unique hj hi
        simp [secondPriceAllocation, hji, hi]
      · have hji : j ≠ i := by
          intro hji
          subst j
          exact hj hi
        simp [secondPriceAllocation, hj, hji]
    simp_rw [heq]
    simp
  · have hz : ∀ i : Fin (n + 1), secondPriceAllocation i v = 0 := by
      intro i
      simp [secondPriceAllocation, not_exists.mp h i]
    simp [hz]

public theorem otherMax_nonneg_of_nonneg {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ otherMax i v := by
  classical
  unfold otherMax
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    exact (hv j).trans (Finset.le_sup' (fun j => v j) hj)
  · exact le_refl _

public theorem otherMax_le_of_le {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv : ∀ j, v j ≤ c) : otherMax i v ≤ c := by
  classical
  unfold otherMax
  split_ifs with h
  · apply Finset.sup'_le
    intro j _
    exact hv j
  · exact hc

public theorem otherMax_bounds {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv : ∀ j, j ≠ i → 0 ≤ v j ∧ v j ≤ c) :
    0 ≤ otherMax i v ∧ otherMax i v ≤ c := by
  classical
  unfold otherMax
  split_ifs with h
  · obtain ⟨j, hj⟩ := h
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    constructor
    · exact (hv j hji).1.trans (Finset.le_sup' (fun j => v j) hj)
    · apply Finset.sup'_le
      intro k hk
      exact (hv k (Finset.ne_of_mem_erase hk)).2
  · exact ⟨le_refl _, hc⟩

public theorem secondPriceAllocation_slice_integrable (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) :
    Integrable (fun v => secondPriceAllocation i (Function.update v i x))
      (D.jointLaw (n + 1)) := by
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  apply Integrable.of_bound
    ((secondPriceAllocation_measurable i).comp measurable_update_left).aestronglyMeasurable 1
  filter_upwards with v
  classical
  change ‖(if secondPriceWinner i (Function.update v i x) then (1 : ℝ) else 0)‖ ≤ 1
  split_ifs <;> norm_num

public theorem secondPricePayment_slice_integrable (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) :
    Integrable (fun v => secondPricePayment i (Function.update v i x))
      (D.jointLaw (n + 1)) := by
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  apply Integrable.of_bound
    ((secondPricePayment_measurable i).comp measurable_update_left).aestronglyMeasurable D.omega
  filter_upwards [D.draws_mem_open_ae (n + 1)] with v hv
  have hb := otherMax_bounds i (Function.update v i x) D.omega D.omega_pos.le
    (fun j hji => by simpa [Function.update_of_ne hji] using
      (show 0 ≤ v j ∧ v j ≤ D.omega from ⟨(hv j).1.le, (hv j).2.le⟩))
  classical
  change ‖(if secondPriceWinner i (Function.update v i x) then
    otherMax i (Function.update v i x) else 0)‖ ≤ D.omega
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · simp [D.omega_pos.le]

/-- Replacing one's own bid does not change the highest competing bid. -/
public theorem otherMax_update {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (x : ℝ) :
    otherMax i (Function.update v i x) = otherMax i v := by
  classical
  unfold otherMax
  split_ifs with h
  · apply Finset.sup'_congr h rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · rfl

public theorem otherMax_le_of_winner {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hi : secondPriceWinner i v)
    (hvi : 0 ≤ v i) : otherMax i v ≤ v i := by
  classical
  unfold otherMax
  split_ifs with h
  · apply Finset.sup'_le
    intro j _
    exact hi.1 j
  · exact hvi

public theorem secondPriceWinner_of_gt_otherMax {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hx : otherMax i v < v i) :
    secondPriceWinner i v := by
  classical
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      exact le_refl _
    · have hj : v j ≤ otherMax i v := by
        unfold otherMax
        have hne : (Finset.univ.erase i).Nonempty :=
          ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩⟩
        rw [dite_eq_left hne]
        exact Finset.le_sup' (fun k => v k)
          (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
      exact hj.trans hx.le
  · intro j hji
    by_contra hn
    have hne : j ≠ i := Ne.symm (ne_of_not_le hn)
    have hj : v j ≤ otherMax i v := by
      unfold otherMax
      have hs : (Finset.univ.erase i).Nonempty :=
        ⟨j, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩⟩
      rw [dite_eq_left hs]
      exact Finset.le_sup' (fun k => v k)
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    linarith

public theorem secondPriceWinner_iff_gt_otherMax_of_ne {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ)
    (hvi : 0 ≤ v i) (hne : v i ≠ otherMax i v) :
    secondPriceWinner i v ↔ otherMax i v < v i := by
  constructor
  · intro hi
    exact lt_of_le_of_ne (otherMax_le_of_winner i v hi hvi) hne.symm
  · exact secondPriceWinner_of_gt_otherMax i v

public theorem secondPrice_payoff_le {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ)
    (x y : ℝ) :
    x * secondPriceAllocation i (Function.update v i y) -
      secondPricePayment i (Function.update v i y) ≤
      max 0 (x - otherMax i v) := by
  classical
  by_cases hw : secondPriceWinner i (Function.update v i y)
  · simp only [secondPriceAllocation, secondPricePayment, hw, ite_eq_left, mul_one]
    rw [otherMax_update]
    exact le_max_right _ _
  · simp [secondPriceAllocation, secondPricePayment, hw]

public theorem secondPrice_truthful_payoff {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ)
    (x : ℝ) (hx : 0 ≤ x) :
    x * secondPriceAllocation i (Function.update v i x) -
      secondPricePayment i (Function.update v i x) =
      max 0 (x - otherMax i v) := by
  classical
  let w := Function.update v i x
  have hwi : w i = x := Function.update_self i x v
  have hm : otherMax i w = otherMax i v := otherMax_update i v x
  rcases lt_trichotomy (otherMax i v) x with hlt | heq | hgt
  · have hw : secondPriceWinner i w :=
      secondPriceWinner_of_gt_otherMax i w (by rw [hm, hwi]; exact hlt)
    simp [secondPriceAllocation, secondPricePayment, hw, w, hm,
      max_eq_right (sub_nonneg.mpr hlt.le)]
  · have hdiff : x - otherMax i v = 0 := by rw [heq]; ring
    simp only [hdiff, max_self]
    by_cases hw : secondPriceWinner i w
    · simp [secondPriceAllocation, secondPricePayment, hw, w, hm, heq]
    · change x * (if secondPriceWinner i w then (1 : ℝ) else 0) -
        (if secondPriceWinner i w then otherMax i w else 0) = 0
      simp [hw]
  · have hw : ¬secondPriceWinner i w := by
      intro hw
      have hle := otherMax_le_of_winner i w hw (hwi ▸ hx)
      rw [hm, hwi] at hle
      exact not_lt_of_ge hle hgt
    rw [max_eq_left (sub_nonpos.mpr hgt.le)]
    change x * (if secondPriceWinner i w then (1 : ℝ) else 0) -
      (if secondPriceWinner i w then otherMax i w else 0) = 0
    simp [hw]

public noncomputable def secondPriceAuction (D : ValueDistribution) (n : ℕ) :
    DirectMechanism D (n + 1) where
  allocation := secondPriceAllocation
  payment := secondPricePayment
  allocation_measurable := secondPriceAllocation_measurable
  allocation_integrable := D.secondPriceAllocation_slice_integrable
  payment_integrable := D.secondPricePayment_slice_integrable
  allocation_nonneg := by
    intro i v
    classical
    change 0 ≤ (if secondPriceWinner i v then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  allocation_feasible := secondPriceAllocation_feasible

public theorem secondPrice_payoff_integral (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) (x y : ℝ) :
    x * (D.secondPriceAuction n).interimAllocation i y -
      (D.secondPriceAuction n).interimPayment i y =
      ∫ v, x * secondPriceAllocation i (Function.update v i y) -
        secondPricePayment i (Function.update v i y) ∂D.jointLaw (n + 1) := by
  rw [DirectMechanism.interimAllocation, DirectMechanism.interimPayment]
  change x * (∫ v, secondPriceAllocation i (Function.update v i y) ∂D.jointLaw (n + 1)) -
    (∫ v, secondPricePayment i (Function.update v i y) ∂D.jointLaw (n + 1)) = _
  rw [← integral_const_mul, integral_sub]
  · exact (D.secondPriceAllocation_slice_integrable i y).const_mul x
  · exact D.secondPricePayment_slice_integrable i y

public theorem secondPriceAuction_BIC (D : ValueDistribution) (n : ℕ) :
    (D.secondPriceAuction n).BIC := by
  intro i x y hx _
  rw [DirectMechanism.interimUtility, D.secondPrice_payoff_integral n i x y,
    D.secondPrice_payoff_integral n i x x]
  apply integral_mono
    ((D.secondPriceAuction n).allocation_integrable i y |>.const_mul x |>.sub
      ((D.secondPriceAuction n).payment_integrable i y))
    ((D.secondPriceAuction n).allocation_integrable i x |>.const_mul x |>.sub
      ((D.secondPriceAuction n).payment_integrable i x))
  intro v
  exact (secondPrice_payoff_le i v x y).trans
    (secondPrice_truthful_payoff i v x hx.1).symm.le

public theorem secondPriceAuction_utility_zero (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) :
    (D.secondPriceAuction n).interimUtility i 0 = 0 := by
  rw [DirectMechanism.interimUtility, D.secondPrice_payoff_integral n i 0 0]
  have hzero : ∀ᵐ v ∂D.jointLaw (n + 1),
      (0 : ℝ) * secondPriceAllocation i (Function.update v i 0) -
        secondPricePayment i (Function.update v i 0) = 0 := by
    filter_upwards [D.draws_mem_open_ae (n + 1)] with v hv
    rw [secondPrice_truthful_payoff i v 0 (le_refl _)]
    have hm : 0 ≤ otherMax i v := otherMax_nonneg_of_nonneg i v
      (fun j => (hv j).1.le)
    simpa only [zero_sub] using (max_eq_left (neg_nonpos.mpr hm))
  rw [integral_congr_ae hzero]
  simp

public theorem secondPriceWinner_exists {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ∃ i, secondPriceWinner i v := by
  classical
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i => v i = Finset.univ.sup' Finset.univ_nonempty v)
  obtain ⟨j, _, hj⟩ := (Finset.univ : Finset (Fin (n + 1))).exists_mem_eq_sup'
    Finset.univ_nonempty v
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.symm⟩
  let i := s.min' ⟨j, hjs⟩
  have his : i ∈ s := s.min'_mem ⟨j, hjs⟩
  have hieq : v i = Finset.univ.sup' Finset.univ_nonempty v :=
    (Finset.mem_filter.mp his).2
  refine ⟨i, ?_, ?_⟩
  · intro k
    rw [hieq]
    exact Finset.le_sup' v (Finset.mem_univ k)
  · intro k hk
    apply s.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.trans hieq⟩

public theorem secondPriceAllocation_surplus (D : ValueDistribution)
    (hreg : D.Regular) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, v i ∈ Set.Ioo 0 D.omega) :
    (∑ i, D.virtualValue (v i) * secondPriceAllocation i v) =
      D.maxVirtual n v := by
  classical
  obtain ⟨i, hi⟩ := secondPriceWinner_exists v
  have hmax : D.virtualValue (v i) = D.maxVirtual n v := by
    apply le_antisymm
    · unfold maxVirtual
      exact Finset.le_sup' (fun j => D.virtualValue (D.draw j v)) (Finset.mem_univ i)
    · unfold maxVirtual
      apply Finset.sup'_le
      intro j _
      exact hreg.monotoneOn (hv j) (hv i) (hi.1 j)
  have hsum : (∑ j, D.virtualValue (v j) * secondPriceAllocation j v) =
      D.virtualValue (v i) := by
    calc
      _ = D.virtualValue (v i) * secondPriceAllocation i v := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          have hj : ¬secondPriceWinner j v := by
            intro hj
            exact hji (secondPriceWinner_unique hj hi)
          simp [secondPriceAllocation, hj]
        · simp
      _ = D.virtualValue (v i) := by simp [secondPriceAllocation, hi]
  exact hsum.trans hmax

public theorem secondPriceAuction_expectedRevenue (D : ValueDistribution)
    (hreg : D.Regular) (n : ℕ) :
    (D.secondPriceAuction n).expectedRevenue =
      ∫ v, D.maxVirtual n v ∂D.jointLaw (n + 1) := by
  unfold DirectMechanism.expectedRevenue
  simp_rw [fun i => (D.secondPriceAuction n).revenue_formula_bic (D.secondPriceAuction_BIC n) i
    (D.secondPriceAuction_utility_zero n i)]
  simp_rw [(D.secondPriceAuction n).virtual_interim_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    (D.secondPriceAuction n).virtualAllocation_integrable_mul i)]
  apply integral_congr_ae
  filter_upwards [D.draws_mem_open_ae (n + 1)] with v hv
  exact D.secondPriceAllocation_surplus hreg n v hv

/-- Adding a final draw makes the maximum at least each of the old maximum
and the final draw's virtual value. -/
public theorem maxVirtual_snoc_lower (D : ValueDistribution) (m : ℕ)
    (w : Fin (m + 1) → ℝ) (x : ℝ) :
    max (D.maxVirtual m w) (D.virtualValue x) ≤
      D.maxVirtual (m + 1) (Fin.snoc w x) := by
  apply max_le
  · unfold maxVirtual
    apply Finset.sup'_le
    intro j _
    calc
      D.virtualValue (D.draw j w) =
          D.virtualValue (D.draw (Fin.castSucc j) (Fin.snoc w x)) := by
            simp [draw, Fin.snoc_castSucc]
      _ ≤ (Finset.univ : Finset (Fin (m + 1 + 1))).sup'
          Finset.univ_nonempty (fun k => D.virtualValue (D.draw k (Fin.snoc w x))) :=
            Finset.le_sup' (fun k : Fin (m + 1 + 1) =>
              D.virtualValue (D.draw k (Fin.snoc w x)))
              (Finset.mem_univ (Fin.castSucc j))
  · unfold maxVirtual
    simpa only [draw, Fin.snoc_last] using
      (Finset.le_sup' (fun k : Fin (m + 1 + 1) =>
        D.virtualValue (D.draw k (Fin.snoc w x)))
        (Finset.mem_univ (Fin.last (m + 1))))

public theorem maxVirtual_extra_bidder (D : ValueDistribution) (m : ℕ) :
    (∫ v, max 0 (D.maxVirtual m v) ∂D.jointLaw (m + 1)) ≤
      ∫ v, D.maxVirtual (m + 1) v ∂D.jointLaw (m + 2) := by
  let : IsProbabilityMeasure D.law := D.probability
  let : IsProbabilityMeasure (D.jointLaw (m + 1)) := D.jointLaw_probability (m + 1)
  let e : (Fin (m + 2) → ℝ) ≃ᵐ ℝ × (Fin (m + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last (m + 1))
  have hmp : MeasurePreserving e (D.jointLaw (m + 2))
      (D.law.prod (D.jointLaw (m + 1))) := by
    simpa only [ValueDistribution.jointLaw, Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => D.law)
        (Fin.last (m + 1)))
  let g : (ℝ × (Fin (m + 1) → ℝ)) → ℝ :=
    fun p => max (D.maxVirtual m p.2) (D.virtualValue p.1)
  have hg : Integrable g (D.law.prod (D.jointLaw (m + 1))) := by
    exact ((D.maxVirtual_integrable m).comp_snd D.law).sup
      (D.virtualValue_integrable.comp_fst (D.jointLaw (m + 1)))
  have hleft : (∫ p, g p ∂(D.law.prod (D.jointLaw (m + 1)))) ≤
      (∫ v, D.maxVirtual (m + 1) v ∂D.jointLaw (m + 2)) := by
    have hcomp : Integrable (g ∘ e) (D.jointLaw (m + 2)) :=
      hmp.integrable_comp_of_integrable hg
    rw [← hmp.integral_comp' g]
    apply integral_mono hcomp (D.maxVirtual_integrable (m + 1))
    intro v
    have heq : e.symm (e v) = v := e.symm_apply_apply v
    have hsnoc : e.symm (e v) = Fin.snoc (e v).2 (e v).1 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_last']
    change g (e v) ≤ D.maxVirtual (m + 1) v
    calc
      g (e v) = max (D.maxVirtual m (e v).2) (D.virtualValue (e v).1) := rfl
      _ ≤ D.maxVirtual (m + 1) (Fin.snoc (e v).2 (e v).1) :=
        D.maxVirtual_snoc_lower m (e v).2 (e v).1
      _ = D.maxVirtual (m + 1) v := congrArg _ (hsnoc.symm.trans heq)
  have hinner (w : Fin (m + 1) → ℝ) :
      max 0 (D.maxVirtual m w) ≤
        ∫ x, g (x, w) ∂D.law := by
    have hgi : Integrable (fun x => g (x, w)) D.law :=
      (integrable_const (D.maxVirtual m w)).sup D.virtualValue_integrable
    have h1 : D.maxVirtual m w ≤ ∫ x, g (x, w) ∂D.law := by
      calc
        D.maxVirtual m w = ∫ _x : ℝ, D.maxVirtual m w ∂D.law := by simp
        _ ≤ ∫ x, g (x, w) ∂D.law := by
          apply integral_mono (integrable_const _) hgi
          intro x
          exact le_max_left _ _
    have h2 : 0 ≤ ∫ x, g (x, w) ∂D.law := by
      calc
        (0 : ℝ) = ∫ x, D.virtualValue x ∂D.law := D.virtualValue_mean_zero.symm
        _ ≤ ∫ x, g (x, w) ∂D.law := by
          apply integral_mono D.virtualValue_integrable hgi
          intro x
          exact le_max_right _ _
    exact max_le h2 h1
  have hproduct : (∫ w, max 0 (D.maxVirtual m w) ∂D.jointLaw (m + 1)) ≤
      ∫ p, g p ∂(D.law.prod (D.jointLaw (m + 1))) := by
    rw [integral_prod_symm g hg]
    apply integral_mono ((integrable_const (0 : ℝ)).sup (D.maxVirtual_integrable m))
      hg.integral_prod_right
    exact hinner
  exact hproduct.trans hleft

end ValueDistribution

/-- With one extra i.i.d. bidder, the no-reserve second-price auction earns at
least the optimal normalized BIC auction with one fewer bidder. -/
public theorem bulowKlemperer (D : ValueDistribution) (hreg : D.Regular) (m : ℕ) :
    (D.secondPriceAuction (m + 1)).expectedRevenue ≥
      (D.optimalAuction m).expectedRevenue := by
  rw [D.secondPriceAuction_expectedRevenue hreg (m + 1),
    DirectMechanism.expectedRevenue_optimalAuction D hreg m]
  exact D.maxVirtual_extra_bidder m

end BulowKlemperer
