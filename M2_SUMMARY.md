# M2 revenue formula via the envelope theorem

## Mechanism model

`BulowKlemperer.DirectMechanism D n` has profile allocation and payment rules for `Fin n` bidders. Allocations are nonnegative and feasible (`∑ i, allocation i v ≤ 1`); allocation and payment slices obtained by replacing bidder `i`'s coordinate are integrable under `D.jointLaw n`. This product law is M1's i.i.d. law. The definitions `interimAllocation i x` and `interimPayment i x` integrate those slices against the product law; `interimUtility i x = x * interimAllocation i x - interimPayment i x`. `BIC` says that, for each bidder and all true values and reports in `[0, D.omega]`, truthful interim utility is at least the interim utility from that report. Since the overwritten coordinate is ignored by the slice, its integration is harmless.

## Exact main statements

```lean
DirectMechanism.interimUtility_absolutelyContinuous {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n) :
    AbsolutelyContinuousOnInterval (M.interimUtility i) 0 D.omega

DirectMechanism.envelope {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : ContinuousOn (M.interimAllocation i) (Set.Icc 0 D.omega))
    {x : ℝ} (hx : x ∈ Set.Icc 0 D.omega) :
    M.interimUtility i x = M.interimUtility i 0 +
      ∫ t in (0 : ℝ)..x, M.interimAllocation i t

DirectMechanism.revenue_formula {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) (hBIC : M.BIC) (i : Fin n)
    (hQ : Continuous (M.interimAllocation i))
    (hU0 : M.interimUtility i 0 = 0) :
    (∫ x, M.interimPayment i x ∂D.law) =
      ∫ x, D.virtualValue x * M.interimAllocation i x ∂D.law
```

The revenue statement defines bidder `i`'s expected payment by integrating its interim payment over the marginal value law. It assumes global continuity of the interim allocation for the weighted layer-cake proof; the envelope statement needs continuity only on the closed support. It does **not** assume `D.Regular` or differentiability of the allocation rule. The mechanism's slice integrability is explicit, and the proof establishes integrability of the interim payment, primitive, weighted hazard, and virtual-value product under the stated hypotheses.

## Proof

BIC at `x` and `y` gives supporting-line inequalities `(y-x) Q_i(x) ≤ U_i(y)-U_i(x) ≤ (y-x) Q_i(y)`. They imply monotonicity of `Q_i`; with `0 ≤ Q_i ≤ 1`, they make `U_i` 1-Lipschitz and absolutely continuous on `[0, omega]`. Continuity of `Q_i` squeezes left and right slopes of `U_i` to `Q_i(x)` at every interior value. The fundamental theorem of calculus, with the Lipschitz boundary continuity, proves the envelope formula. This route proves pointwise interior differentiability, so an a.e. differentiability or differentiation-under-the-integral argument is unnecessary.

For revenue, the envelope and `U_i(0)=0` give `P_i(x)=x Q_i(x)-∫_0^x Q_i(t) dt` almost everywhere under `D.law`. Mathlib's weighted layer-cake identity turns the expectation of the primitive into `∫_0^omega (1-F(t))Q_i(t) dt`. M1's density cancellation, generalized to `Q_i`, identifies this with `E[((1-F(X))/f(X)) Q_i(X)]`. Subtraction gives `E[virtualValue(X) Q_i(X)]`.

## Verification

`LD_PRELOAD=/tmp/m2_trace.so lake build` exited 0 and built the root library against Lean 4.35.0-rc2 and Mathlib v4.35.0-rc2. The preload shim is a temporary sandbox workaround: the sandbox reports a PID absent from `/proc`, which otherwise prevents Lean's executable-path lookup. It changes no repository source. The new library has zero `sorry`, `admit`, and `axiom` declarations. `#print axioms` on all 24 new public theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.
