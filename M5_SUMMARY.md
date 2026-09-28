# M5: Palomar packaging

## Comparator design

`Challenge.lean` and `Solution.lean` separately declare three theorems under
`BulowKlemperer.Palomar`: the optimal-auction positive-part revenue identity,
the no-reserve second-price revenue identity without a positive part, and the
main Bulow–Klemperer inequality. `Challenge.lean` has three intentional theorem
placeholders. `Solution.lean` applies the corresponding proved M3–M4 library
theorems. Neither module imports the other. Five existing library definitions
are listed in `definition_names`; `ValueDistribution`, a structure, is omitted.

## Declaration-kind checks

The verifier generates Lean files importing `Challenge` and `Solution`
separately. Each file runs `#check @<full.name>` for every comparator name,
then checks `ConstantInfo.defnInfo` for each definition and
`ConstantInfo.thmInfo` for each theorem. Both environments passed for:

| Comparator definition | Kind in Challenge | Kind in Solution |
| --- | --- | --- |
| `ValueDistribution.secondPriceAuction` | `defnInfo` | `defnInfo` |
| `ValueDistribution.optimalAuction` | `defnInfo` | `defnInfo` |
| `DirectMechanism.expectedRevenue` | `defnInfo` | `defnInfo` |
| `ValueDistribution.Regular` | `defnInfo` | `defnInfo` |
| `ValueDistribution.maxVirtual` | `defnInfo` | `defnInfo` |

All names above have the `BulowKlemperer.` prefix in `comparator.json`.

## Prose-to-hypothesis audit

The README and `formalization.yaml` were written from the final declarations:

- `ValueDistribution.Regular (D : ValueDistribution) : Prop` is exactly
  `StrictMonoOn D.virtualValue (Set.Ioo 0 D.omega)`, so regularity is only
  asserted on the open support.
- `ValueDistribution.jointLaw (D : ValueDistribution) (n : ℕ)` is
  `Measure.pi (fun _ => D.law)`; `draw_law` and `draws_independent` justify
  the identical and independent draw claims.
- `DirectMechanism.expectedRevenue {D} {n} (M : DirectMechanism D n)` is
  `∑ i : Fin n, ∫ x, M.interimPayment i x ∂D.law`.
- `DirectMechanism.expectedRevenue_optimalAuction (D) (hreg) (n)` uses
  `max 0 (D.maxVirtual n v)`, matching the allocation's nonnegative virtual
  value condition and possible withholding.
- `ValueDistribution.secondPriceAuction_expectedRevenue (D) (hreg) (n)`
  uses `D.maxVirtual n v` without a positive part. `secondPriceWinner` selects
  a highest value, with no reserve condition.
- Both auction constructors return `DirectMechanism D (n + 1)`. Thus the
  main binder `(D : ValueDistribution) (hreg : D.Regular) (m : ℕ)` compares
  `secondPriceAuction (m + 1)` with `m + 2` bidders against
  `optimalAuction m` with `m + 1`.
- `DirectMechanism.interimUtility` is `x * interimAllocation - interimPayment`,
  supporting the risk-neutral private-value description. The metadata limits
  the result to the normalized BIC direct-mechanism setting.

The 2026-09-28 Palomar/web search found no checkable earlier entry for this
Bulow–Klemperer statement. The metadata phrases this as the author's current
knowledge, not as an absolute prior-art claim. The source citation was checked
against the published bibliographic record.

## Verification

`lake build` completed all 3460 jobs. The three `Challenge.lean` warnings are
the deliberate placeholders. `scripts/verify-palomar.sh` checked the source
tokens, module headers, Challenge import surface, comparator names and kinds,
all library and Solution axioms, the comparator, and whitespace. Its Lean
environment scan found 213 `BulowKlemperer` declarations, all using only
`propext`, `Classical.choice`, and `Quot.sound`. No M1–M4 proof or theorem
statement was changed. No Palomar intake was performed.
