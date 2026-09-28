module

public import BulowKlemperer.Revenue
public import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open Filter
open TopologicalSpace
open scoped Topology

namespace BulowKlemperer

namespace ValueDistribution

/-- Bidder `i` wins when her virtual value is nonnegative and maximal.  The
smallest index among maximizers wins a tie. -/
public def virtualWinner (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : Prop :=
  0 < v i ∧ 0 ≤ D.virtualValue (v i) ∧
  (∀ j, D.virtualValue (v j) ≤ D.virtualValue (v i)) ∧
  (∀ j, D.virtualValue (v j) = D.virtualValue (v i) → i ≤ j)

public theorem virtualWinner_measurableSet (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) : MeasurableSet {v | D.virtualWinner i v} := by
  have hm (j : Fin (n + 1)) : Measurable (fun v : Fin (n + 1) → ℝ =>
      D.virtualValue (v j)) := D.virtualValue_measurable.comp (measurable_pi_apply j)
  unfold virtualWinner
  have hpos : MeasurableSet {v : Fin (n + 1) → ℝ | 0 < v i} :=
    measurableSet_lt measurable_const (measurable_pi_apply i)
  have htop : MeasurableSet {v : Fin (n + 1) → ℝ |
      0 ≤ D.virtualValue (v i)} := measurableSet_le measurable_const (hm i)
  have hmax : MeasurableSet {v : Fin (n + 1) → ℝ |
      ∀ j, D.virtualValue (v j) ≤ D.virtualValue (v i)} := by
    simpa only [Set.iInter_ofPred] using
      (MeasurableSet.iInter (fun j => measurableSet_le (hm j) (hm i)))
  have htie : MeasurableSet {v : Fin (n + 1) → ℝ |
      ∀ j, D.virtualValue (v j) = D.virtualValue (v i) → i ≤ j} := by
    have h (j : Fin (n + 1)) : MeasurableSet
        {v : Fin (n + 1) → ℝ | D.virtualValue (v j) = D.virtualValue (v i) → i ≤ j} := by
      by_cases hij : i ≤ j
      · simp [hij]
      · have heq : MeasurableSet {v : Fin (n + 1) → ℝ |
            D.virtualValue (v j) = D.virtualValue (v i)} :=
          measurableSet_eq_fun (hm j) (hm i)
        simpa [hij, Set.compl_def] using heq.compl
    simpa only [Set.iInter_ofPred] using (MeasurableSet.iInter h)
  simpa only [Set.ofPred_and] using (hpos.inter (htop.inter (hmax.inter htie)))

/-- The zero-one allocation rule of the optimal virtual-surplus auction. -/
@[expose] public noncomputable def virtualAllocation (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : ℝ :=
  by classical exact if D.virtualWinner i v then 1 else 0

public theorem virtualAllocation_measurable (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) : Measurable (D.virtualAllocation i) := by
  classical
  change Measurable (fun v => if D.virtualWinner i v then (1 : ℝ) else 0)
  exact Measurable.ite (D.virtualWinner_measurableSet i) measurable_const measurable_const

public theorem virtualAllocation_nonneg (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) :
    0 ≤ D.virtualAllocation i v := by
  classical
  change 0 ≤ if D.virtualWinner i v then (1 : ℝ) else 0
  split_ifs <;> norm_num

public theorem virtualWinner_unique (D : ValueDistribution) {n : ℕ}
    {i j : Fin (n + 1)} {v : Fin (n + 1) → ℝ}
    (hi : D.virtualWinner i v) (hj : D.virtualWinner j v) : i = j := by
  have hle : D.virtualValue (v i) ≤ D.virtualValue (v j) := hj.2.2.1 i
  have hge : D.virtualValue (v j) ≤ D.virtualValue (v i) := hi.2.2.1 j
  exact le_antisymm (hi.2.2.2 j (le_antisymm hge hle))
    (hj.2.2.2 i (le_antisymm hle hge))

public theorem virtualAllocation_feasible (D : ValueDistribution) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i, D.virtualAllocation i v) ≤ 1 := by
  classical
  by_cases h : ∃ i, D.virtualWinner i v
  · obtain ⟨i, hi⟩ := h
    have heq : ∀ j : Fin (n + 1), D.virtualAllocation j v = if j = i then 1 else 0 := by
      intro j
      by_cases hj : D.virtualWinner j v
      · have hji := D.virtualWinner_unique hj hi
        simp [virtualAllocation, hi, hji]
      · have hji : j ≠ i := by
          intro hji
          subst j
          exact hj hi
        simp [virtualAllocation, hj, hji]
    simp_rw [heq]
    simp
  · have hz : ∀ i : Fin (n + 1), D.virtualAllocation i v = 0 := by
      intro i
      simp [virtualAllocation, not_exists.mp h i]
    simp [hz]

public theorem virtualValue_of_nonpos (D : ValueDistribution) {x : ℝ} (hx : x ≤ 0) :
    D.virtualValue x = x := by
  have hnot : x ∉ Set.Ioo 0 D.omega := fun h => not_lt_of_ge hx h.1
  simp [virtualValue, D.density_zero x hnot]

public theorem virtualWinner_exists_of_pos (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (hmax : 0 < D.maxVirtual n v) :
    ∃ i, D.virtualWinner i v := by
  classical
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun i => D.virtualValue (v i) = D.maxVirtual n v)
  obtain ⟨j, _, hj⟩ := (Finset.univ : Finset (Fin (n + 1))).exists_mem_eq_sup'
    Finset.univ_nonempty (fun i => D.virtualValue (v i))
  have hjs : j ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa only [maxVirtual, draw] using hj.symm⟩
  have hs : s.Nonempty := ⟨j, hjs⟩
  let i := s.min' hs
  have his : i ∈ s := s.min'_mem hs
  have hieq : D.virtualValue (v i) = D.maxVirtual n v :=
    (Finset.mem_filter.mp his).2
  have hpos : 0 < v i := by
    by_contra h
    have hx : v i ≤ 0 := le_of_not_gt h
    rw [D.virtualValue_of_nonpos hx] at hieq
    linarith
  refine ⟨i, ⟨hpos, hieq.symm ▸ hmax.le, ?_, ?_⟩⟩
  · intro k
    rw [hieq]
    exact Finset.le_sup' (fun j : Fin (n + 1) => D.virtualValue (v j))
      (Finset.mem_univ k)
  · intro k hk
    apply s.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.trans hieq⟩

/-- The virtual-surplus allocation realizes the pointwise positive maximum. -/
public theorem virtualAllocation_surplus (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) :
    (∑ i, D.virtualValue (v i) * D.virtualAllocation i v) =
      max 0 (D.maxVirtual n v) := by
  classical
  by_cases hmax : 0 < D.maxVirtual n v
  · obtain ⟨i, hi⟩ := D.virtualWinner_exists_of_pos n v hmax
    have hzero (j : Fin (n + 1)) (hji : j ≠ i) :
        D.virtualAllocation j v = 0 := by
      have hj : ¬D.virtualWinner j v := by
        intro hj
        exact hji (D.virtualWinner_unique hj hi)
      simp [virtualAllocation, hj]
    have hsum : (∑ j, D.virtualValue (v j) * D.virtualAllocation j v) =
        D.virtualValue (v i) := by
      calc
        (∑ j, D.virtualValue (v j) * D.virtualAllocation j v) =
            D.virtualValue (v i) * D.virtualAllocation i v := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            simp [hzero j hji]
          · simp
        _ = D.virtualValue (v i) := by simp [virtualAllocation, hi]
    rw [hsum, max_eq_right hmax.le]
    apply le_antisymm
    · rw [maxVirtual]
      simpa only [draw] using
        (Finset.le_sup' (fun j : Fin (n + 1) => D.virtualValue (v j))
          (Finset.mem_univ i))
    · rw [maxVirtual]
      apply Finset.sup'_le
      intro j _
      simpa only [draw] using hi.2.2.1 j
  · have hnonpos : D.maxVirtual n v ≤ 0 := le_of_not_gt hmax
    have hz (i : Fin (n + 1)) :
        D.virtualValue (v i) * D.virtualAllocation i v = 0 := by
      by_cases hi : D.virtualWinner i v
      · have hle : D.virtualValue (v i) ≤ D.maxVirtual n v := by
          rw [maxVirtual]
          exact Finset.le_sup' (fun j : Fin (n + 1) => D.virtualValue (v j))
            (Finset.mem_univ i)
        have heq : D.virtualValue (v i) = 0 := by linarith [hi.2.1]
        simp [heq]
      · simp [virtualAllocation, hi]
    simp [hz, max_eq_left hnonpos]

public theorem virtualValue_le_value (D : ValueDistribution) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 D.omega) : D.virtualValue x ≤ x := by
  have htail : 0 ≤ 1 - D.cdf x := by
    rw [← D.tail_probability]
    exact measureReal_nonneg
  have hratio : 0 ≤ (1 - D.cdf x) / D.density x :=
    div_nonneg htail (D.density_pos x hx).le
  unfold virtualValue
  linarith

public theorem virtualValue_strictMonoOn_Ioc (D : ValueDistribution) (hreg : D.Regular) :
    StrictMonoOn D.virtualValue (Set.Ioc 0 D.omega) := by
  intro x hx y hy hxy
  by_cases hyw : y < D.omega
  · unfold Regular at hreg
    exact hreg ⟨hx.1, lt_trans hxy hyw⟩ ⟨hy.1, hyw⟩ hxy
  · have hy' : y = D.omega := le_antisymm hy.2 (le_of_not_gt hyw)
    subst y
    have hxopen : x ∈ Set.Ioo 0 D.omega := ⟨hx.1, hxy⟩
    have homega : D.virtualValue D.omega = D.omega := by
      have hnot : D.omega ∉ Set.Ioo 0 D.omega := fun h => (lt_irrefl _ h.2)
      simp [virtualValue, D.density_zero D.omega hnot]
    rw [homega]
    exact lt_of_le_of_lt (D.virtualValue_le_value hxopen) hxy

/-- A bidder who wins at a positive report keeps winning after increasing it
within the support. Strict regularity eliminates a former tie. -/
public theorem virtualWinner_monotone_update (D : ValueDistribution) (hreg : D.Regular)
    {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 D.omega) (hy : y ∈ Set.Icc 0 D.omega)
    (hxy : x ≤ y) (hw : D.virtualWinner i (Function.update v i x)) :
    D.virtualWinner i (Function.update v i y) := by
  classical
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact hw
  have hxpos : 0 < x := by simpa [virtualWinner] using hw.1
  have hpsi : D.virtualValue x < D.virtualValue y :=
    D.virtualValue_strictMonoOn_Ioc hreg ⟨hxpos, hx.2⟩
      ⟨lt_trans hxpos hlt, hy.2⟩ hlt
  have hmax (j : Fin (n + 1)) (hji : j ≠ i) :
      D.virtualValue (v j) ≤ D.virtualValue x := by
    have h := hw.2.2.1 j
    simpa [Function.update_of_ne hji] using h
  refine ⟨by simpa using lt_trans hxpos hlt, ?_, ?_, ?_⟩
  · have hw0 : 0 ≤ D.virtualValue x := by simpa using hw.2.1
    simpa using (le_of_lt (lt_of_le_of_lt hw0 hpsi))
  · intro j
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hji] using
        (le_of_lt (lt_of_le_of_lt (hmax j hji) hpsi))
  · intro j hj
    by_cases hji : j = i
    · simp [hji]
    · have hltj : D.virtualValue (v j) < D.virtualValue y :=
        lt_of_le_of_lt (hmax j hji) hpsi
      have hcontr : D.virtualValue (v j) = D.virtualValue y := by
        simpa [Function.update_of_ne hji] using hj
      exact False.elim (ne_of_lt hltj hcontr)

public theorem virtualAllocation_slice_integrable (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) :
    Integrable (fun v => D.virtualAllocation i (Function.update v i x))
      (D.jointLaw (n + 1)) := by
  classical
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  have hm : Measurable (fun v : Fin (n + 1) → ℝ =>
      D.virtualAllocation i (Function.update v i x)) :=
    (D.virtualAllocation_measurable i).comp measurable_update_left
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with v
  simp only [Real.norm_eq_abs]
  by_cases h : D.virtualWinner i (Function.update v i x)
  · simp [virtualAllocation, h]
  · simp [virtualAllocation, h]

@[expose] public noncomputable def optimalInterimAllocation (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  ∫ v, D.virtualAllocation i (Function.update v i x) ∂D.jointLaw (n + 1)

public theorem optimalInterimAllocation_monotoneOn (D : ValueDistribution)
    (hreg : D.Regular) {n : ℕ} (i : Fin (n + 1)) :
    MonotoneOn (D.optimalInterimAllocation i) (Set.Icc 0 D.omega) := by
  intro x hx y hy hxy
  unfold optimalInterimAllocation
  apply integral_mono (D.virtualAllocation_slice_integrable i x)
    (D.virtualAllocation_slice_integrable i y)
  intro v
  by_cases hw : D.virtualWinner i (Function.update v i x)
  · have hwy := D.virtualWinner_monotone_update hreg i v hx hy hxy hw
    simp [virtualAllocation, hw, hwy]
  · simp [virtualAllocation, hw]
    split_ifs <;> norm_num

public theorem optimalInterimAllocation_measurable (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) : Measurable (D.optimalInterimAllocation i) := by
  classical
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  have hupdate : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      Function.update p.2 i p.1) :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  have h : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      D.virtualAllocation i (Function.update p.2 i p.1)) :=
    (D.virtualAllocation_measurable i).comp hupdate
  change Measurable (fun x => ∫ v, D.virtualAllocation i
    (Function.update v i x) ∂D.jointLaw (n + 1))
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    h.stronglyMeasurable).measurable

public theorem optimalInterimAllocation_nonneg (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) : 0 ≤ D.optimalInterimAllocation i x := by
  unfold optimalInterimAllocation
  exact integral_nonneg (fun v => D.virtualAllocation_nonneg i _)

public theorem optimalInterimAllocation_le_one (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) : D.optimalInterimAllocation i x ≤ 1 := by
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  unfold optimalInterimAllocation
  calc
    (∫ v, D.virtualAllocation i (Function.update v i x) ∂D.jointLaw (n + 1)) ≤
        ∫ _v : Fin (n + 1) → ℝ, (1 : ℝ) ∂D.jointLaw (n + 1) := by
      apply integral_mono (D.virtualAllocation_slice_integrable i x) (integrable_const 1)
      intro v
      classical
      change (if D.virtualWinner i (Function.update v i x) then (1 : ℝ) else 0) ≤ 1
      split_ifs <;> norm_num
    _ = 1 := by simp

/-- The normalized interim payment prescribed by the envelope identity. -/
@[expose] public noncomputable def optimalInterimPayment (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  x * D.optimalInterimAllocation i x -
    ∫ t in (0 : ℝ)..x, D.optimalInterimAllocation i t

/-- The direct mechanism uses the virtual-surplus allocation and the interim
envelope payment. Its payment depends only on the bidder's own report. -/
public noncomputable def optimalAuction (D : ValueDistribution) (n : ℕ) :
    DirectMechanism D (n + 1) where
  allocation := D.virtualAllocation
  payment := fun i v => D.optimalInterimPayment i (v i)
  allocation_measurable := D.virtualAllocation_measurable
  allocation_integrable := D.virtualAllocation_slice_integrable
  payment_integrable := by
    intro i x
    let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
    have heq : (fun v : Fin (n + 1) → ℝ =>
        D.optimalInterimPayment i ((Function.update v i x) i)) =
        fun _ => D.optimalInterimPayment i x := by
      funext v
      simp
    rw [heq]
    exact integrable_const _
  allocation_nonneg := D.virtualAllocation_nonneg
  allocation_feasible := D.virtualAllocation_feasible

public theorem optimalAuction_interimAllocation (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) (x : ℝ) :
    (D.optimalAuction n).interimAllocation i x = D.optimalInterimAllocation i x := by
  rfl

public theorem optimalAuction_interimPayment (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) (x : ℝ) :
    (D.optimalAuction n).interimPayment i x = D.optimalInterimPayment i x := by
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  simp [DirectMechanism.interimPayment, optimalAuction]

public theorem optimalAuction_interimUtility (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) (x : ℝ) :
    (D.optimalAuction n).interimUtility i x =
      ∫ t in (0 : ℝ)..x, D.optimalInterimAllocation i t := by
  rw [DirectMechanism.interimUtility, D.optimalAuction_interimAllocation,
    D.optimalAuction_interimPayment]
  unfold optimalInterimPayment
  ring

public theorem optimalAuction_utility_zero (D : ValueDistribution) (n : ℕ)
    (i : Fin (n + 1)) :
    (D.optimalAuction n).interimUtility i 0 = 0 := by
  rw [D.optimalAuction_interimUtility]
  simp

public theorem optimalInterimAllocation_intervalIntegrable (D : ValueDistribution)
    (hreg : D.Regular) {n : ℕ} (i : Fin (n + 1))
    {a b : ℝ} (ha : a ∈ Set.Icc 0 D.omega) (hb : b ∈ Set.Icc 0 D.omega) :
    IntervalIntegrable (D.optimalInterimAllocation i) volume a b := by
  have hmono := D.optimalInterimAllocation_monotoneOn hreg i
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 D.omega := by
    intro t ht
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at ht
      exact ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at ht
      exact ⟨hb.1.trans ht.1, ht.2.trans ha.2⟩
  exact (hmono.mono hsub).intervalIntegrable

/-- Monotonic interim allocation and the envelope payment make truthful
reporting optimal for all values in the closed support. -/
public theorem optimalAuction_BIC (D : ValueDistribution) (hreg : D.Regular)
    (n : ℕ) : (D.optimalAuction n).BIC := by
  intro i x y hx hy
  let Q := D.optimalInterimAllocation i
  have hmono : MonotoneOn Q (Set.Icc 0 D.omega) :=
    D.optimalInterimAllocation_monotoneOn hreg i
  have h0x : IntervalIntegrable Q volume 0 x :=
    D.optimalInterimAllocation_intervalIntegrable hreg i
      ⟨le_refl _, D.omega_pos.le⟩ hx
  have h0y : IntervalIntegrable Q volume 0 y :=
    D.optimalInterimAllocation_intervalIntegrable hreg i
      ⟨le_refl _, D.omega_pos.le⟩ hy
  have hxyint : IntervalIntegrable Q volume x y :=
    D.optimalInterimAllocation_intervalIntegrable hreg i hx hy
  have htruth : (D.optimalAuction n).interimUtility i x =
      ∫ t in (0 : ℝ)..x, Q t := D.optimalAuction_interimUtility n i x
  rw [htruth, D.optimalAuction_interimAllocation,
    D.optimalAuction_interimPayment]
  unfold optimalInterimPayment
  by_cases hxy : x ≤ y
  · have hbound : (∫ t in x..y, Q t) ≤ (y - x) * Q y := by
      have h := intervalIntegral.integral_mono_on (μ := volume) (a := x) (b := y)
        (f := Q) (g := fun _ => Q y) hxy hxyint intervalIntegrable_const
        (fun t ht => hmono ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩ hy ht.2)
      simpa using h
    have hsub := intervalIntegral.integral_interval_sub_left h0y h0x
    dsimp [Q] at *
    linarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hyxint : IntervalIntegrable Q volume y x := hxyint.symm
    have hbound : (x - y) * Q y ≤ ∫ t in y..x, Q t := by
      have h := intervalIntegral.integral_mono_on (μ := volume) (a := y) (b := x)
        (f := fun _ => Q y) (g := Q) hyx intervalIntegrable_const hyxint
        (fun t ht => hmono hy ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩ ht.1)
      simpa using h
    have hsub := intervalIntegral.integral_interval_sub_left h0x h0y
    dsimp [Q] at *
    linarith

/-- Replacing one coordinate of an independent profile by a fresh draw
preserves the joint law. -/
public theorem update_jointLaw (D : ValueDistribution) {n : ℕ} (i : Fin (n + 1)) :
    ((D.jointLaw (n + 1)).prod D.law).map
      (fun p : (Fin (n + 1) → ℝ) × ℝ => Function.update p.1 i p.2) =
        D.jointLaw (n + 1) := by
  classical
  let : IsProbabilityMeasure D.law := D.probability
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  have hmap : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      Function.update p.1 i p.2) := measurable_update'
  change ((Measure.pi (fun _ : Fin (n + 1) => D.law)).prod D.law).map _ =
    Measure.pi (fun _ : Fin (n + 1) => D.law)
  apply (Measure.pi_eq (μ := fun _ : Fin (n + 1) => D.law) ?_).symm
  intro s hs
  have hset : (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      Function.update p.1 i p.2) ⁻¹' (Set.pi Set.univ s) =
      (Set.pi Set.univ (Function.update s i Set.univ)) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · intro hp
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simp
        · simpa [Function.update_of_ne hji] using hp j
      · simpa using hp i
    · rintro ⟨hp, hpi⟩ j
      by_cases hji : j = i
      · subst j
        simpa using hpi
      · simpa [Function.update_of_ne hji] using hp j
  rw [Measure.map_apply hmap (MeasurableSet.pi (Set.to_countable _) (fun j _ => hs j)), hset,
    Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin (n + 1)))
    (fun j => D.law (s j)) (Finset.mem_univ i)]
  have hfun : (fun j : Fin (n + 1) => D.law (Function.update s i Set.univ j)) =
      Function.update (fun j => D.law (s j)) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, one_mul]

public theorem integral_update_jointLaw (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f (D.jointLaw (n + 1))) :
    (∫ v, f v ∂D.jointLaw (n + 1)) =
      ∫ x, (∫ v, f (Function.update v i x) ∂D.jointLaw (n + 1)) ∂D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  let u : ((Fin (n + 1) → ℝ) × ℝ) → (Fin (n + 1) → ℝ) :=
    fun p => Function.update p.1 i p.2
  have hu : Measurable u := measurable_update'
  have hfmap : Integrable f (((D.jointLaw (n + 1)).prod D.law).map u) := by
    rw [show ((D.jointLaw (n + 1)).prod D.law).map u =
      D.jointLaw (n + 1) from D.update_jointLaw i]
    exact hf
  have hfprod : Integrable (fun p => f (u p))
      ((D.jointLaw (n + 1)).prod D.law) := hfmap.comp_measurable hu
  have hint := integral_prod_symm (μ := D.jointLaw (n + 1)) (ν := D.law)
    (f := fun p => f (u p)) hfprod
  have hmap := integral_map (μ := (D.jointLaw (n + 1)).prod D.law)
    (φ := u) hu.aemeasurable hfmap.aestronglyMeasurable
  rw [D.update_jointLaw i] at hmap
  exact hmap.trans hint

public theorem virtualAllocation_integrable_mul (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) : Integrable
      (fun v => D.virtualValue (v i) * D.virtualAllocation i v)
      (D.jointLaw (n + 1)) := by
  have hbound : ∀ᵐ v ∂D.jointLaw (n + 1), ‖D.virtualAllocation i v‖ ≤ (1 : ℝ) := by
    filter_upwards with v
    classical
    change ‖if D.virtualWinner i v then (1 : ℝ) else 0‖ ≤ 1
    split_ifs <;> norm_num
  exact (D.draw_virtual_integrable i).mul_bdd
    (D.virtualAllocation_measurable i).aestronglyMeasurable hbound

public theorem virtual_allocation_interim_integral (D : ValueDistribution) {n : ℕ}
    (i : Fin (n + 1)) :
    (∫ x, D.virtualValue x * D.optimalInterimAllocation i x ∂D.law) =
      ∫ v, D.virtualValue (v i) * D.virtualAllocation i v ∂D.jointLaw (n + 1) := by
  have h := D.integral_update_jointLaw i
    (fun v => D.virtualValue (v i) * D.virtualAllocation i v)
    (D.virtualAllocation_integrable_mul i)
  rw [h]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Function.update_self, optimalInterimAllocation]
  rw [← integral_const_mul]

/-- The optimal allocation's expected virtual surplus is the expected positive
maximum, with `n+1` explicitly matching M1's indexing. -/
public theorem optimal_virtual_surplus (D : ValueDistribution) (n : ℕ) :
    (∑ i : Fin (n + 1),
      ∫ x, D.virtualValue x * D.optimalInterimAllocation i x ∂D.law) =
      ∫ v, max 0 (D.maxVirtual n v) ∂D.jointLaw (n + 1) := by
  simp_rw [D.virtual_allocation_interim_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ => D.virtualAllocation_integrable_mul i)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => D.virtualAllocation_surplus n v)

/-- Any feasible nonnegative allocation has virtual surplus no greater than
the positive part of the highest virtual value. -/
public theorem virtual_surplus_le (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hfeas : (∑ i, q i) ≤ 1) :
    (∑ i, D.virtualValue (v i) * q i) ≤ max 0 (D.maxVirtual n v) := by
  have hmax (i : Fin (n + 1)) : D.virtualValue (v i) ≤ D.maxVirtual n v := by
    rw [BulowKlemperer.ValueDistribution.maxVirtual]
    exact Finset.le_sup' (fun j : Fin (n + 1) => D.virtualValue (v j))
      (Finset.mem_univ i)
  have hterm (i : Fin (n + 1)) :
      D.virtualValue (v i) * q i ≤ max 0 (D.maxVirtual n v) * q i :=
    mul_le_mul_of_nonneg_right ((hmax i).trans (le_max_right _ _)) (hq i)
  calc
    (∑ i, D.virtualValue (v i) * q i) ≤
        ∑ i, max 0 (D.maxVirtual n v) * q i := Finset.sum_le_sum (fun i _ => hterm i)
    _ = max 0 (D.maxVirtual n v) * ∑ i, q i := by rw [Finset.mul_sum]
    _ ≤ max 0 (D.maxVirtual n v) * 1 :=
      mul_le_mul_of_nonneg_left hfeas (le_max_left _ _)
    _ = max 0 (D.maxVirtual n v) := mul_one _

end ValueDistribution

namespace DirectMechanism

/-- Interim allocation is measurable as a parameter integral of the measurable allocation. -/
public theorem interimAllocation_measurable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    Measurable (M.interimAllocation i) := by
  let : IsProbabilityMeasure (D.jointLaw n) := D.jointLaw_probability n
  have hupdate : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      Function.update p.2 i p.1) :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  have h : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      M.allocation i (Function.update p.2 i p.1)) :=
    (M.allocation_measurable i).comp hupdate
  change Measurable (fun x => ∫ v, M.allocation i
    (Function.update v i x) ∂D.jointLaw n)
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
    h.stronglyMeasurable).measurable

/-- A bounded measurable interim allocation is interval integrable on any real interval. -/
public theorem interimAllocation_intervalIntegrable {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) (a b : ℝ) :
    IntervalIntegrable (M.interimAllocation i) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (μ := volume)
    (measure_Ioc_lt_top.ne) (M.interimAllocation_measurable i).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (M.interimAllocation_nonneg i x)]
  exact M.interimAllocation_le_one i x

/-- At a continuity point of interim allocation, BIC identifies the derivative
of interim utility with that allocation. -/
public theorem interimUtility_hasDerivAt_of_continuousAt {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 D.omega)
    (hQx : ContinuousAt (M.interimAllocation i) x) :
    HasDerivAt (M.interimUtility i) (M.interimAllocation i x) x := by
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
      have hb := M.utility_increment_bounds hBIC i hy
        (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩)
      have hpos : 0 < x - y := sub_pos.mpr hyx
      rw [slope_def_field, show M.interimUtility i y - M.interimUtility i x =
        -(M.interimUtility i x - M.interimUtility i y) by ring,
        show y - x = -(x - y) by ring, neg_div_neg_eq]
      exact (le_div_iff₀ hpos).2 (by nlinarith [hb.1])
    · filter_upwards [hIcc_left, self_mem_nhdsWithin]
        with y hy hyx
      have hb := M.utility_increment_bounds hBIC i hy
        (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩)
      rw [slope_def_field, show M.interimUtility i y - M.interimUtility i x =
        -(M.interimUtility i x - M.interimUtility i y) by ring,
        show y - x = -(x - y) by ring, neg_div_neg_eq]
      exact (div_le_iff₀ (sub_pos.mpr hyx)).2 (by nlinarith [hb.2])
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (hQx.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [hIcc_right, self_mem_nhdsWithin]
        with y hy hxy
      have hb := M.utility_increment_bounds hBIC i
        (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩) hy
      rw [slope_def_field]
      exact (le_div_iff₀ (sub_pos.mpr hxy)).2 (by nlinarith [hb.1])
    · filter_upwards [hIcc_right, self_mem_nhdsWithin]
        with y hy hxy
      have hb := M.utility_increment_bounds hBIC i
        (show x ∈ Set.Icc 0 D.omega from ⟨hx.1.le, hx.2.le⟩) hy
      rw [slope_def_field]
      exact (div_le_iff₀ (sub_pos.mpr hxy)).2 (by nlinarith [hb.2])

/-- BIC gives the envelope identity without continuity of interim allocation.
The monotone allocation has only countably many discontinuities, while interim
utility is absolutely continuous. -/
public theorem envelope_of_BIC {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    {x : ℝ} (hx : x ∈ Set.Icc 0 D.omega) :
    M.interimUtility i x = M.interimUtility i 0 +
      ∫ t in (0 : ℝ)..x, M.interimAllocation i t := by
  have hmono := M.interimAllocation_monotoneOn hBIC i
  have hbad := hmono.countable_not_continuousWithinAt
  have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioo 0 D.omega →
      HasDerivAt (M.interimUtility i) (M.interimAllocation i t) t := by
    filter_upwards [compl_mem_ae_iff.mpr (hbad.measure_zero volume)] with t ht htopen
    have htclosed : t ∈ Set.Icc 0 D.omega := ⟨htopen.1.le, htopen.2.le⟩
    have hwithin : ContinuousWithinAt (M.interimAllocation i)
        (Set.Icc 0 D.omega) t := by
      by_contra hn
      exact ht ⟨htclosed, hn⟩
    have hnhds : Set.Icc 0 D.omega ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds htopen.1 htopen.2)
        Set.Ioo_subset_Icc_self
    exact M.interimUtility_hasDerivAt_of_continuousAt hBIC i htopen
      (hwithin.continuousAt hnhds)
  have hAC : AbsolutelyContinuousOnInterval (M.interimUtility i) 0 x := by
    have hsub : Set.uIcc 0 x ⊆ Set.Icc 0 D.omega := by
      rw [Set.uIcc_of_le hx.1]
      intro t ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    exact (M.interimUtility_lipschitz hBIC i |>.mono hsub).absolutelyContinuousOnInterval
  have hFTC := hAC.integral_deriv_eq_sub
  have heq : (∫ t in (0 : ℝ)..x, deriv (M.interimUtility i) t) =
      ∫ t in (0 : ℝ)..x, M.interimAllocation i t := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hx.1]
    filter_upwards [hae, Measure.ae_ne volume x] with t ht hne htx
    have htopen : t ∈ Set.Ioo 0 D.omega :=
      ⟨htx.1, (lt_of_le_of_ne htx.2 hne).trans_le hx.2⟩
    exact (ht htopen).deriv
  rw [heq] at hFTC
  linarith

public theorem primitive_le_value_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ≤ x := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := x)
    (f := M.interimAllocation i) (g := fun _ => (1 : ℝ)) hx
    (M.interimAllocation_intervalIntegrable i 0 x) intervalIntegrable_const
    (fun t _ => M.interimAllocation_le_one i t)
  simpa using h

public theorem primitive_integrable_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    Integrable (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  have hcont : Continuous (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) :=
    intervalIntegral.continuous_primitive
      (fun a b => M.interimAllocation_intervalIntegrable i a b) 0
  apply Integrable.of_bound hcont.measurable.aestronglyMeasurable D.omega
  filter_upwards [D.value_mem] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (M.primitive_nonneg i hx.1)]
  exact (M.primitive_le_value_bic i hx.1).trans hx.2

public theorem weightedTail_integrable_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    Integrable (M.weightedTail i) volume := by
  let : IsProbabilityMeasure D.law := D.probability
  have hm : Measurable (fun x : ℝ => (1 - D.cdf x) * M.interimAllocation i x) :=
    (measurable_const.sub D.cdf_continuous.measurable).mul
      (M.interimAllocation_measurable i)
  have hint : IntegrableOn
      (fun x : ℝ => (1 - D.cdf x) * M.interimAllocation i x)
      (Set.Ioo 0 D.omega) volume := by
    apply Measure.integrableOn_of_bounded (μ := volume)
      (measure_Ioo_lt_top.ne) hm.aestronglyMeasurable
    filter_upwards with x
    have htail : 0 ≤ 1 - D.cdf x := by
      rw [← D.tail_probability]
      exact measureReal_nonneg
    have htail1 : 1 - D.cdf x ≤ 1 := by
      rw [← D.tail_probability]
      exact measureReal_le_one
    have hq0 := M.interimAllocation_nonneg i x
    have hq1 := M.interimAllocation_le_one i x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htail hq0)]
    calc
      (1 - D.cdf x) * M.interimAllocation i x ≤
          1 * M.interimAllocation i x := mul_le_mul_of_nonneg_right htail1 hq0
      _ = M.interimAllocation i x := one_mul _
      _ ≤ 1 := hq1
  change Integrable ((Set.Ioo 0 D.omega).indicator
    (fun x => (1 - D.cdf x) * M.interimAllocation i x)) volume
  exact hint.integrable_indicator measurableSet_Ioo

public theorem weightedHazard_integrable_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    Integrable (fun x => D.hazardTerm x * M.interimAllocation i x) D.law := by
  rw [D.law_eq_withDensity]
  rw [integrable_withDensity_iff_integrable_smul'
    (D.density_measurable.ennreal_ofReal) (by simp)]
  convert M.weightedTail_integrable_bic i using 1
  funext x
  simpa only [smul_eq_mul] using M.density_mul_weightedHazard i x

public theorem weighted_tail_eq_primitive_integral_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    (∫ x, (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law) =
      ∫ x, M.weightedTail i x := by
  have hLayer := lintegral_comp_eq_lintegral_meas_lt_mul
    (f := fun x : ℝ => x) (g := M.interimAllocation i) D.law
    D.value_nonneg_ae measurable_id.aemeasurable
    (fun t _ => M.interimAllocation_intervalIntegrable i 0 t)
    (Eventually.of_forall fun t => M.interimAllocation_nonneg i t)
  have hLeft : 0 ≤ᵐ[D.law]
      (fun x => ∫ t in (0 : ℝ)..x, M.interimAllocation i t) := by
    filter_upwards [D.value_mem] with x hx
    exact M.primitive_nonneg i hx.1
  rw [integral_eq_lintegral_of_nonneg_ae hLeft
    (M.primitive_integrable_bic i).aestronglyMeasurable, hLayer]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => M.weightedTail_nonneg i x)
    (M.weightedTail_integrable_bic i).aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro x
  exact (M.weightedTail_eq_layercake i x).symm

public theorem value_mul_allocation_integrable_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (i : Fin n) :
    Integrable (fun x => x * M.interimAllocation i x) D.law := by
  let : IsProbabilityMeasure D.law := D.probability
  apply Integrable.of_bound
    (measurable_id.mul (M.interimAllocation_measurable i)).aestronglyMeasurable D.omega
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

public theorem revenue_formula_bic {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hU0 : M.interimUtility i 0 = 0) :
    (∫ x, M.interimPayment i x ∂D.law) =
      ∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law := by
  have hPae : (M.interimPayment i) =ᵐ[D.law]
      (fun x => x * M.interimAllocation i x -
        ∫ t in (0 : ℝ)..x, M.interimAllocation i t) := by
    filter_upwards [D.value_mem] with x hx
    have henv := M.envelope_of_BIC hBIC i hx
    rw [hU0] at henv
    change x * M.interimAllocation i x - M.interimPayment i x =
      0 + ∫ t in (0 : ℝ)..x, M.interimAllocation i t at henv
    linarith
  calc
    (∫ x, M.interimPayment i x ∂D.law) =
        ∫ x, x * M.interimAllocation i x -
          (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law :=
      integral_congr_ae hPae
    _ = (∫ x, x * M.interimAllocation i x ∂D.law) -
        (∫ x, (∫ t in (0 : ℝ)..x, M.interimAllocation i t) ∂D.law) :=
      integral_sub (M.value_mul_allocation_integrable_bic i)
        (M.primitive_integrable_bic i)
    _ = (∫ x, x * M.interimAllocation i x ∂D.law) -
        (∫ x, D.hazardTerm x * M.interimAllocation i x ∂D.law) := by
      rw [M.weighted_tail_eq_primitive_integral_bic i, M.weightedHazard_integral]
    _ = ∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law := by
      rw [← integral_sub (M.value_mul_allocation_integrable_bic i)
        (M.weightedHazard_integrable_bic i)]
      apply integral_congr_ae
      filter_upwards with x
      unfold ValueDistribution.virtualValue ValueDistribution.hazardTerm
      ring

/-- Total expected revenue, computed from the marginal interim payments. -/
@[expose] public noncomputable def expectedRevenue {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) : ℝ :=
  ∑ i : Fin n, ∫ x, M.interimPayment i x ∂D.law

public theorem virtualAllocation_integrable_mul {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D (n + 1)) (i : Fin (n + 1)) : Integrable
      (fun v => D.virtualValue (v i) * M.allocation i v)
      (D.jointLaw (n + 1)) := by
  have hbound : ∀ᵐ v ∂D.jointLaw (n + 1), ‖M.allocation i v‖ ≤ (1 : ℝ) := by
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (M.allocation_nonneg i v)]
    exact M.allocation_le_one i v
  exact (D.draw_virtual_integrable i).mul_bdd
    (M.allocation_measurable i).aestronglyMeasurable hbound

public theorem virtual_interim_integral {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D (n + 1)) (i : Fin (n + 1)) :
    (∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law) =
      ∫ v, D.virtualValue (v i) * M.allocation i v ∂D.jointLaw (n + 1) := by
  have h := D.integral_update_jointLaw i
    (fun v => D.virtualValue (v i) * M.allocation i v)
    (M.virtualAllocation_integrable_mul i)
  rw [h]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Function.update_self, interimAllocation]
  rw [← integral_const_mul]

/-- The normalized revenue of every BIC mechanism is bounded by the expected
positive maximum virtual value for the same `n+1` bidders. -/
public theorem expectedRevenue_le_maxVirtual {D : ValueDistribution} (n : ℕ)
    (M : DirectMechanism D (n + 1)) (hBIC : M.BIC)
    (hU0 : ∀ i, M.interimUtility i 0 = 0) :
    M.expectedRevenue ≤
      ∫ v, max 0 (D.maxVirtual n v) ∂D.jointLaw (n + 1) := by
  let : IsProbabilityMeasure (D.jointLaw (n + 1)) := D.jointLaw_probability (n + 1)
  unfold expectedRevenue
  simp_rw [fun i => M.revenue_formula_bic hBIC i (hU0 i)]
  simp_rw [M.virtual_interim_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ => M.virtualAllocation_integrable_mul i)]
  have hmax : Integrable (fun v => max 0 (D.maxVirtual n v))
      (D.jointLaw (n + 1)) := (integrable_const (0 : ℝ)).sup (D.maxVirtual_integrable n)
  apply integral_mono
    (integrable_finsetSum Finset.univ (fun i _ => M.virtualAllocation_integrable_mul i)) hmax
  intro v
  exact D.virtual_surplus_le n v (fun i => M.allocation i v)
    (fun i => M.allocation_nonneg i v) (M.allocation_feasible v)

/-- The optimal auction attains the upper bound, with `n+1` bidders. -/
public theorem expectedRevenue_optimalAuction (D : ValueDistribution)
    (hreg : D.Regular) (n : ℕ) :
    (D.optimalAuction n).expectedRevenue =
      ∫ v, max 0 (D.maxVirtual n v) ∂D.jointLaw (n + 1) := by
  unfold expectedRevenue
  simp_rw [fun i => (D.optimalAuction n).revenue_formula_bic
    (D.optimalAuction_BIC hreg n) i (D.optimalAuction_utility_zero n i)]
  simp_rw [D.optimalAuction_interimAllocation n]
  exact D.optimal_virtual_surplus n

end DirectMechanism

end BulowKlemperer
