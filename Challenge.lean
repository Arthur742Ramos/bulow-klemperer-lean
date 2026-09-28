module

public import BulowKlemperer

open MeasureTheory

namespace BulowKlemperer.Palomar

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

end BulowKlemperer.Palomar
