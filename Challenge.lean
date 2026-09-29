module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

open MeasureTheory
open ProbabilityTheory
open Filter
open TopologicalSpace
open scoped ENNReal Topology

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

/-- The product law of `n` independent draws from the common distribution. -/
@[expose] public noncomputable def jointLaw (D : ValueDistribution) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  sorry

end ValueDistribution

/-- A direct mechanism. Interim probabilities and payments integrate out the other bids
under the common i.i.d. product law. The overwritten coordinate is immaterial. -/
public structure DirectMechanism (D : ValueDistribution) (n : ℕ) where
  allocation : Fin n → (Fin n → ℝ) → ℝ
  payment : Fin n → (Fin n → ℝ) → ℝ
  allocation_measurable : ∀ i, Measurable (allocation i)
  allocation_integrable : ∀ i x, Integrable (fun v => allocation i (Function.update v i x)) (D.jointLaw n)
  payment_integrable : ∀ i x, Integrable (fun v => payment i (Function.update v i x)) (D.jointLaw n)
  allocation_nonneg : ∀ i v, 0 ≤ allocation i v
  allocation_feasible : ∀ v, ∑ i : Fin n, allocation i v ≤ 1

namespace DirectMechanism

/-- Total expected revenue, computed from the marginal interim payments. -/
@[expose] public noncomputable def expectedRevenue {D : ValueDistribution} {n : ℕ}
    (M : DirectMechanism D n) : ℝ :=
  sorry

end DirectMechanism

namespace ValueDistribution

/-- Regularity of the common value distribution. -/
@[expose] public def Regular (D : ValueDistribution) : Prop :=
  sorry

/-- The maximum virtual value over `n + 1` bidders. -/
@[expose] public noncomputable def maxVirtual (D : ValueDistribution) (n : ℕ)
    (v : Fin (n + 1) → ℝ) : ℝ :=
  sorry

/-- The no-reserve second-price auction with `n + 1` bidders. -/
public noncomputable def secondPriceAuction (D : ValueDistribution) (n : ℕ) :
    DirectMechanism D (n + 1) :=
  sorry

/-- The optimal (revenue-maximizing) auction with `n + 1` bidders. -/
public noncomputable def optimalAuction (D : ValueDistribution) (n : ℕ) :
    DirectMechanism D (n + 1) :=
  sorry

end ValueDistribution

namespace Palomar

/-- The optimal auction earns the positive part of the maximum virtual value. -/
public theorem optimalAuction_expectedRevenue (D : ValueDistribution)
    (hreg : D.Regular) (m : ℕ) :
    (D.optimalAuction m).expectedRevenue =
      ∫ v, max 0 (D.maxVirtual m v) ∂D.jointLaw (m + 1) := by
  sorry

/-- The no-reserve second-price auction earns the maximum virtual value. -/
public theorem secondPriceAuction_expectedRevenue (D : ValueDistribution)
    (hreg : D.Regular) (m : ℕ) :
    (D.secondPriceAuction m).expectedRevenue =
      ∫ v, D.maxVirtual m v ∂D.jointLaw (m + 1) := by
  sorry

/-- One extra bidder in a no-reserve second-price auction beats the optimal auction. -/
public theorem bulowKlemperer (D : ValueDistribution) (hreg : D.Regular) (m : ℕ) :
    (D.secondPriceAuction (m + 1)).expectedRevenue ≥
      (D.optimalAuction m).expectedRevenue := by
  sorry

end Palomar

end BulowKlemperer
