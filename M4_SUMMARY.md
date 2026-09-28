# M4: Bulow–Klemperer comparison

## Public results

- `ValueDistribution.secondPriceAuction n`: the no-reserve second-price direct mechanism for `n+1` bidders. The highest bid wins, with the smallest index breaking ties; the winner pays the highest competing bid. With one bidder, the payment is zero.
- `ValueDistribution.secondPriceAuction_BIC`: truthful reporting maximizes interim utility for every value and report in the closed support.
- `ValueDistribution.secondPriceAuction_utility_zero`: every bidder's interim utility at value zero is zero.
- `ValueDistribution.secondPriceAuction_expectedRevenue`: under regularity, expected second-price revenue with `n+1` bidders is the expectation of `maxVirtual n`, without a positive part.
- `ValueDistribution.maxVirtual_extra_bidder`: the expectation of `maxVirtual (m+1)` with `m+2` bidders is at least the expectation of the positive part of `maxVirtual m` with `m+1` bidders.
- `BulowKlemperer.bulowKlemperer`: under regularity, second-price revenue with `m+2` bidders is at least optimal-auction revenue with `m+1` bidders.

The remaining public declarations in `SecondPrice.lean` establish measurability, feasibility, integrability, pointwise payoff identities, virtual-surplus equality, and the product-measure comparison used by these results.

## Verification

- `lake build` passed: **3456 jobs**, with no warnings.
- A repository Lean-source search found no `sorry`, `admit`, `axiom`, or `unsafe` declarations.
- `#print axioms` was run on **all 31 new public declarations**. Each reports exactly `[propext, Classical.choice, Quot.sound]`.
- The M1–M3 files and their theorem statements were not changed.

## Proof detail and deviations

The comparison uses Fubini and two applications of integral monotonicity: the conditional expectation of `max (M, ψ(X))` is at least both `M` and `E[ψ(X)] = 0`. This proves the needed Jensen bound directly. Ties need no null-set argument for virtual-surplus equality: every highest-value winner has maximal virtual value under regularity, including tied profiles in the open support. The finite measure comparison uses a lower bound for the enlarged maximum, which is sufficient for the theorem.
