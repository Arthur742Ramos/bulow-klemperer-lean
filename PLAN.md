# Bulow-Klemperer Theorem — Formalization Plan

**Theorem** (Bulow-Klemperer 1996, "Auctions versus Negotiations", AER):
In a symmetric independent-private-values setting with values drawn i.i.d.
from a regular distribution, the expected revenue of a standard (no-reserve)
second-price auction with `n+1` bidders is at least the expected revenue of
the revenue-optimal auction with `n` bidders.

**Proof skeleton** (the formalization follows this chain):

1. Virtual values: `ψ(x) = x - (1 - F x) / f x`, strictly increasing
   (regularity). Key fact: `E[ψ(X)] = 0` for a single draw, by integration
   by parts (`E[(1-F(X))/f(X)] = ∫(1-F) = E[X]`).
2. Revenue formula (envelope theorem): in any BIC mechanism with
   `U_i(0) = 0`, bidder `i`'s expected payment equals
   `E[ψ(X_i) * Q_i(X_i)]` where `Q_i` is the interim allocation probability.
3. Optimal auction (regular case): allocate to the bidder with the highest
   virtual value when it is non-negative. Expected revenue equals
   `E[(max_i ψ(X_i))^+]`.
4. No-reserve second-price auction with `n+1` bidders: allocates to the
   highest value (hence highest virtual value, by regularity); expected
   revenue equals `E[max_{i ≤ n+1} ψ(X_i)]` (no positive part: the object
   always sells).
5. Comparison: condition on the first `n` draws, write `M = max_{i≤n} ψ(X_i)`.
   Then `E[max(M, ψ(X_{n+1}))] ≥ E[max(M, 0)]` because `max(M, ·)` is convex
   and `E[ψ(X_{n+1})] = 0` (Jensen). Hence
   `E[max_{n+1} ψ] ≥ E[(max_n ψ)^+]`, i.e. no-reserve SPA with `n+1`
   bidders beats the optimal auction with `n` bidders.

## Milestones

- **M1 — Probability foundations.** I.i.d. continuous value model
  (`F`, `f > 0` on `(0, ω)`), virtual value `ψ` and regularity,
  `E[ψ(X)] = 0`, basic order-statistic / max facts. Survey the
  Myerson-Satterthwaite repo for reusable virtual-value and
  continuous-type machinery before building from scratch.
- **M2 — Revenue formula.** Envelope theorem: expected payment
  `= E[ψ(X_i) * Q_i(X_i)]` for BIC mechanisms with `U_i(0) = 0`.
- **M3 — Optimal auction revenue.** The max-virtual-value allocation is
  revenue-optimal; its revenue is `E[(max_i ψ(X_i))^+]`.
- **M4 — Bulow-Klemperer comparison.** The Jensen step and the final
  inequality: `Revenue(SPA_{n+1}) ≥ Revenue(OPT_n)`.
- **M5 — Palomar packaging.** Challenge/Solution split, `comparator.json`,
  `formalization.yaml`, README prose. Prose-to-hypothesis audit required:
  every factual claim in prose must point at the exact Lean declaration
  backing it (regularity, i.i.d., no-reserve, which auction, revenue
  notion). Module-system headers on all Lean sources from the start
  (see revelation-principle-lean for the pattern).
- **M6 — Intake.** Local Palomar verifier replica PASS, submit, monitor
  mechanical verification and automated review.

## Quality bar

- Zero `sorry`/`admit`/`axiom` in library code; axioms limited to
  `propext`, `Classical.choice`, `Quot.sound`.
- Every milestone independently compiled and axiom-audited before the
  next begins.
- `scripts/verify-palomar.sh` equivalent gates from M5 onward.
