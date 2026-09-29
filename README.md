# Bulow–Klemperer in Lean 4

This project formalizes the independent private-value revenue comparison associated with [Bulow and Klemperer, *Auctions Versus Negotiations* (1996)](https://ideas.repec.org/a/aea/aecrev/v86y1996i1p180-94.html). The proved statement is [`BulowKlemperer.bulowKlemperer`](BulowKlemperer/SecondPrice.lean):

```lean
(D : ValueDistribution) (hreg : D.Regular) (m : ℕ) :
  (D.secondPriceAuction (m + 1)).expectedRevenue ≥
    (D.optimalAuction m).expectedRevenue
```

The bidder counts follow the constructor binders in [`ValueDistribution.secondPriceAuction`](BulowKlemperer/SecondPrice.lean) and [`ValueDistribution.optimalAuction`](BulowKlemperer/Optimal.lean): each `(D : ValueDistribution) (n : ℕ)` returns `DirectMechanism D (n + 1)`. Thus the left side has `m + 2` bidders and the right side has `m + 1`.

## Model and hypotheses

The [`ValueDistribution`](BulowKlemperer/Probability.lean) structure has fields `omega : ℝ`, `omega_pos : 0 < omega`, `law : Measure ℝ`, `probability : IsProbabilityMeasure law`, `density : ℝ → ℝ`, `density_measurable : Measurable density`, `density_nonneg : ∀ x, 0 ≤ density x`, `density_pos : ∀ x ∈ Set.Ioo 0 omega, 0 < density x`, `density_zero : ∀ x ∉ Set.Ioo 0 omega, density x = 0`, `cdf : ℝ → ℝ`, `cdf_eq : ∀ x, cdf x = law.real (Set.Iic x)`, `cdf_continuous : Continuous cdf`, `cdf_zero : cdf 0 = 0`, `cdf_above : ∀ x, omega ≤ x → cdf x = 1`, and almost-sure support facts `value_mem : ∀ᵐ x ∂law, x ∈ Set.Icc 0 omega` and `value_mem_open : ∀ᵐ x ∂law, x ∈ Set.Ioo 0 omega`. These are the continuous, bounded, common private-value distribution assumptions used by the proof.

Independent draws use [`ValueDistribution.jointLaw`](BulowKlemperer/Probability.lean), with binder `(D : ValueDistribution) (n : ℕ) : Measure (Fin n → ℝ)` and body `Measure.pi (fun _ => D.law)`. [`ValueDistribution.draw_law`](BulowKlemperer/Probability.lean) states `(D : ValueDistribution) {n : ℕ} (i : Fin n) : (D.jointLaw n).map (D.draw i) = D.law`; [`ValueDistribution.draws_independent`](BulowKlemperer/Probability.lean) states `(D : ValueDistribution) (n : ℕ) : iIndepFun (fun i v => D.draw i v) (D.jointLaw n)`. Together these are the precise i.i.d. claims.

Regularity is [`ValueDistribution.Regular`](BulowKlemperer/Probability.lean):

```lean
(D : ValueDistribution) : Prop :=
  StrictMonoOn D.virtualValue (Set.Ioo 0 D.omega)
```

It requires strictly increasing virtual values on the **open** interval `(0, omega)`. The virtual value is [`ValueDistribution.virtualValue`](BulowKlemperer/Probability.lean), `(D : ValueDistribution) (x : ℝ) : ℝ := x - (1 - D.cdf x) / D.density x`.

Bidder utility is risk neutral in [`DirectMechanism.interimUtility`](BulowKlemperer/Revenue.lean): `{D : ValueDistribution} {n : ℕ} (M : DirectMechanism D n) (i : Fin n) (x : ℝ) : ℝ := x * M.interimAllocation i x - M.interimPayment i x`. Revenue is [`DirectMechanism.expectedRevenue`](BulowKlemperer/Optimal.lean):

```lean
{D : ValueDistribution} {n : ℕ} (M : DirectMechanism D n) : ℝ :=
  ∑ i : Fin n, ∫ x, M.interimPayment i x ∂D.law
```

Thus revenue is the sum of expected interim payments under the common law.

## Auctions and revenue identities

The optimal mechanism uses [`ValueDistribution.virtualWinner`](BulowKlemperer/Optimal.lean), with binders `(D : ValueDistribution) {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : Prop`; its body requires `0 ≤ D.virtualValue (v i)` and maximal virtual value. Its [`optimal_virtual_surplus`](BulowKlemperer/Optimal.lean), with binders `(D : ValueDistribution) (n : ℕ)`, equals `∫ v, max 0 (D.maxVirtual n v) ∂D.jointLaw (n + 1)`. Consequently the allocation can withhold the item when every virtual value is negative. The revenue identity is [`DirectMechanism.expectedRevenue_optimalAuction`](BulowKlemperer/Optimal.lean):

```lean
(D : ValueDistribution) (hreg : D.Regular) (n : ℕ) :
  (D.optimalAuction n).expectedRevenue =
    ∫ v, max 0 (D.maxVirtual n v) ∂D.jointLaw (n + 1)
```

The no-reserve second-price auction uses [`ValueDistribution.secondPriceWinner`](BulowKlemperer/SecondPrice.lean), with binders `{n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) : Prop` and body `(∀ j, v j ≤ v i) ∧ (∀ j, v j = v i → i ≤ j)`. This selects the highest **value** bidder and breaks ties by index; there is no reserve condition. [`ValueDistribution.secondPricePayment`](BulowKlemperer/SecondPrice.lean), with the same binders and result `ℝ`, charges the winner `otherMax i v` and charges others zero. Its revenue identity is [`ValueDistribution.secondPriceAuction_expectedRevenue`](BulowKlemperer/SecondPrice.lean):

```lean
(D : ValueDistribution) (hreg : D.Regular) (n : ℕ) :
  (D.secondPriceAuction n).expectedRevenue =
    ∫ v, D.maxVirtual n v ∂D.jointLaw (n + 1)
```

This expectation has no positive part. The comparison is completed by [`ValueDistribution.maxVirtual_extra_bidder`](BulowKlemperer/SecondPrice.lean), with binders `(D : ValueDistribution) (m : ℕ)` and conclusion

```lean
(∫ v, max 0 (D.maxVirtual m v) ∂D.jointLaw (m + 1)) ≤
  ∫ v, D.maxVirtual (m + 1) v ∂D.jointLaw (m + 2)
```

The model uses the BIC condition in [`DirectMechanism.BIC`](BulowKlemperer/Revenue.lean), with binders `{D : ValueDistribution} {n : ℕ} (M : DirectMechanism D n) : Prop` and body `∀ i (x y : ℝ), x ∈ Set.Icc 0 D.omega → y ∈ Set.Icc 0 D.omega → x * M.interimAllocation i y - M.interimPayment i y ≤ M.interimUtility i x`. [`optimalAuction_BIC`](BulowKlemperer/Optimal.lean) has binders `(D : ValueDistribution) (hreg : D.Regular) (n : ℕ) : (D.optimalAuction n).BIC`; [`secondPriceAuction_BIC`](BulowKlemperer/SecondPrice.lean) has binders `(D : ValueDistribution) (n : ℕ) : (D.secondPriceAuction n).BIC`. Their utility normalization is stated by [`optimalAuction_utility_zero`](BulowKlemperer/Optimal.lean) and [`secondPriceAuction_utility_zero`](BulowKlemperer/SecondPrice.lean), each with binders `(D : ValueDistribution) (n : ℕ) (i : Fin (n + 1))` and conclusion `(D.<auction> n).interimUtility i 0 = 0`. The formal theorem addresses this BIC direct-mechanism setting; it does not state the paper's affiliated-signal or general negotiation results.

## Palomar package

[`Challenge.lean`](Challenge.lean) states three comparison theorems with deliberate placeholders. [`Solution.lean`](Solution.lean) proves the same statements from the library. The two modules compile separately; neither imports the other. [`comparator.json`](comparator.json) names those theorems and six genuine definitions. Run `scripts/verify-palomar.sh` to check compilation, declarations, axiom use, and the comparator. `lake build` includes both modules.
