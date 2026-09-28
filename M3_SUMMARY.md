# M3: optimal auction and revenue

## Model and indexing

`D.maxVirtual n` is defined on profiles `Fin (n + 1) → ℝ`; all optimal-auction and revenue-bound theorems use `DirectMechanism D (n + 1)` and `D.jointLaw (n + 1)`. The `n` in these statements is one less than the number of bidders.

`D.Regular` means that `D.virtualValue` is strictly increasing on the open value support `(0, D.omega)`. The value law has a density, positive on that interval, as specified in M1.

## Main declarations

| Declaration | Statement |
| --- | --- |
| `ValueDistribution.virtualWinner` | Bidder `i` wins if her value is positive, her virtual value is nonnegative and maximal, and her index is the smallest among equal virtual values. |
| `ValueDistribution.virtualWinner_measurableSet`, `virtualAllocation_measurable` | The winner event and its zero-one allocation are measurable. |
| `ValueDistribution.virtualAllocation_feasible` | At most one bidder receives the item. If the maximum virtual value is negative, the allocation is zero. At a zero maximum, the tie rule may allocate the item; this has zero virtual surplus. |
| `ValueDistribution.virtualAllocation_surplus` | The pointwise sum of virtual value times allocation equals `max 0 (D.maxVirtual n v)`. |
| `ValueDistribution.optimalInterimAllocation_monotoneOn` | Under `D.Regular`, each bidder's interim allocation is monotone on `[0, D.omega]`. |
| `ValueDistribution.optimalInterimPayment`, `optimalAuction_interimUtility`, `optimalAuction_utility_zero` | Payment is `x * Qᵢ(x) - ∫ t in 0..x, Qᵢ(t)`, so interim utility is that integral and utility at zero is zero. The actual direct-mechanism payment depends only on the bidder's own report. |
| `ValueDistribution.optimalAuction_BIC` | Under `D.Regular`, truthful reporting maximizes interim utility for every value and report in the closed support. |
| `DirectMechanism.envelope_of_BIC`, `revenue_formula_bic` | Every BIC mechanism with measurable allocation satisfies the envelope identity on the support and the marginal expected-payment/virtual-surplus identity when utility at zero is zero. Continuity of interim allocation is not required. |
| `DirectMechanism.expectedRevenue_le_maxVirtual` | For **any** normalized BIC mechanism with `n + 1` bidders, total expected revenue is at most the `D.jointLaw (n + 1)` expectation of `max 0 (D.maxVirtual n)`. No regularity or interim-allocation continuity hypothesis is imposed. |
| `DirectMechanism.expectedRevenue_optimalAuction` | Under `D.Regular`, `D.optimalAuction n` attains that same expected positive maximum virtual value. |

`DirectMechanism.expectedRevenue` is the sum of expected interim payments over all bidders. The support and independence assumptions come from `ValueDistribution`; the results make no assertion about arbitrary correlated value laws.

The auxiliary theorems prove uniqueness and existence of the deterministic winner when the virtual maximum is positive, monotonicity of the winner under a higher own report, integrability and measurability of the interim quantities, preservation of the product law when a coordinate is replaced by an independent draw, equality between profile and interim virtual-surplus integrals, and the pointwise feasibility upper bound.

## Changes to M1 and M2

The statements of existing M1/M2 theorems were not changed. `@[expose]` was added to `Regular`, `maxVirtual`, and `BIC` for M3 elaboration. `DirectMechanism` gained `allocation_measurable`, which the optimal-auction constructor supplies. `BulowKlemperer.lean` imports the new module.

The M2 payment theorem assumed continuous interim allocation. Reserve-price allocations can jump, so M3 proves a more general BIC envelope and revenue formula using monotonicity, countability of discontinuities, and absolute continuity of interim utility. This is the substantive deviation from the initial draft and allows the upper bound to cover every normalized BIC mechanism in the defined class.

## Verification

- `lake build`: successful, 3455 jobs, with no warnings.
- `rg -n '\b(sorry|admit|axiom|unsafe)\b' BulowKlemperer BulowKlemperer.lean`: no matches.
- `#print axioms` was run on all 49 new public definitions and theorems in `Optimal.lean` and on the new `DirectMechanism.allocation_measurable` projection. Every result listed only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`: clean.
