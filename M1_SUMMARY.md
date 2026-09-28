# M1 probability foundations

## Definitions

`BulowKlemperer.ValueDistribution` packages a common probability law on real values, a strictly positive Lebesgue density on `(0, omega)` that vanishes outside that interval, its continuous cdf `F` with `F 0 = 0`, and compact-support facts. `jointLaw n` is the Mathlib product measure on `Fin n → ℝ`; `draw i` is coordinate evaluation. `virtualValue x = x - (1 - cdf x) / density x`, and `Regular` is `StrictMonoOn virtualValue (Set.Ioo 0 omega)`. `maxValue n` and `maxVirtual n` are finite suprema over `Fin (n + 1)`.

## Main lemmas (exact statements)

```lean
ValueDistribution.hazard_integral_eq_tail_integral (D : ValueDistribution) :
  (∫ x, D.hazardTerm x ∂D.law) = ∫ x, D.truncatedTail x

ValueDistribution.tail_integral_eq_value_integral (D : ValueDistribution) :
  (∫ x, D.truncatedTail x) = ∫ x, x ∂D.law

ValueDistribution.virtualValue_mean_zero (D : ValueDistribution) :
  (∫ x, D.virtualValue x ∂D.law) = 0

ValueDistribution.draw_law (D : ValueDistribution) {n : ℕ} (i : Fin n) :
  (D.jointLaw n).map (D.draw i) = D.law

ValueDistribution.draws_independent (D : ValueDistribution) (n : ℕ) :
  iIndepFun (fun i v => D.draw i v) (D.jointLaw n)

ValueDistribution.draw_virtual_mean_zero (D : ValueDistribution) {n : ℕ} (i : Fin n) :
  (∫ v, D.virtualValue (D.draw i v) ∂D.jointLaw n) = 0

ValueDistribution.virtualValue_max_ae (D : ValueDistribution) (hreg : D.Regular)
    (n : ℕ) :
  ∀ᵐ v ∂D.jointLaw (n + 1),
    D.virtualValue (D.maxValue n v) = D.maxVirtual n v

ValueDistribution.maxValue_integrable (D : ValueDistribution) (n : ℕ) :
  Integrable (D.maxValue n) (D.jointLaw (n + 1))

ValueDistribution.maxVirtual_integrable (D : ValueDistribution) (n : ℕ) :
  Integrable (D.maxVirtual n) (D.jointLaw (n + 1))
```

The expectation proof cancels the density with `integral_withDensity_eq_integral_toReal_smul`, then applies Mathlib's `Integrable.integral_eq_integral_meas_lt` tail formula, the measure-theoretic integration-by-parts identity. Separate lemmas establish integrability of the hazard term and virtual value, probability of the joint law, and almost-sure interior support for all draws.

## Reuse and checks

I surveyed `~/workspace/myerson-satterthwaite-lean`. Its `MSData` pattern of bundling probability measures and support hypotheses, and its `MS/Main.lean` pattern of proving integrability from compact support with `Integrable.of_bound`, informed this model. The MS code has no continuous virtual-value machinery to import, and its source files predate the module headers used here.

`lake exe cache get` found 8,915 already decompressed Mathlib artifacts; `lake build` exited 0 against Mathlib v4.35.0-rc2. `lake update` was attempted first but could not reach GitHub through the container's proxy, so the matching local Mathlib checkout and manifest were used. The new library contains no `sorry`, `admit`, or `axiom`. `#print axioms` on all 23 new public theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.

The workspace's original `.git` is read-only. The M1 commit is retained in `.m1-git` against this worktree; publishing it to `origin/main` remains pending because shell Git has no network access and the GitHub connector rejected its write action under the session's no-approval policy.
