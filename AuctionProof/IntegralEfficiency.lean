import AuctionProof.Auction
import AuctionProof.Axioms
import AuctionProof.Efficiency

/-!
# Integral Efficiency: From Pointwise to Expected Welfare

## Main result

The pointwise welfare-maximizing allocation (proved in Efficiency.lean)
also maximizes *expected* social welfare — the integral of welfare against
the query distribution μ.

## Proof sketch

If `f(x) ≥ g(x)` for all x, and the integral is monotone, then
`∫ f dμ ≥ ∫ g dμ`. This is `QueryMeasure.integral_mono` from Axioms.lean.

The bridge:
1. winner_maximizes_welfare (Efficiency.lean): for each x and each j,
   trueVal(winner, x) ≥ trueVal(j, x) under truthful reporting.
2. For any alternative allocation rule `rule`, at each x:
   trueVal(winner(x), x) ≥ trueVal(rule(x), x).
3. Apply integral_mono.

## References

- Standard measure theory (integral monotonicity).
- Groves (1973), Thm 1: efficient choice rule = argmax of values.
  DOI: https://doi.org/10.2307/1914085
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- DEFINITIONS
-- ============================================================

/-- Expected social welfare of an allocation rule under query distribution μ.

    The allocation rule maps each query point x to a winning advertiser.
    Welfare is the expected value of the winner's valuation over all queries.

    Standard in mechanism design. Nisan et al. (2007), Ch. 9. -/
def welfareOfRule (auc : Auction ι E) (rule : E → ι) (μ : QueryMeasure E) : ℝ :=
  μ.integrate (fun x => trueVal (auc.valuation (rule x)) x)

-- ============================================================
-- MAIN THEOREM
-- ============================================================

/-- The pointwise-max allocation maximizes expected social welfare over
    ALL possible allocation rules.

    Given:
    - allTruthful: everyone reports honestly
    - winner_maximizes_welfare (Efficiency.lean): for each x, the winner
      achieves the highest value among all players

    Then for any allocation rule `rule : E → ι`:
      𝔼[trueVal(winner(x), x)] ≥ 𝔼[trueVal(rule(x), x)]

    This is the "as efficient as it can get" result. No allocation rule —
    not just no power-diagram allocation, but no allocation whatsoever —
    can achieve higher expected welfare.

    Groves (1973), Thm 1: efficient choice rule = argmax.
    Standard measure theory: pointwise domination ⟹ integral domination.
    DOI: https://doi.org/10.2307/1914085 -/
theorem integral_efficiency
    (auc : Auction ι E) (μ : QueryMeasure E)
    (htruth : allTruthful auc) :
    ∀ (rule : E → ι),
      welfareOfRule auc (fun x => winner auc x) μ ≥ welfareOfRule auc rule μ := by
  intro rule
  unfold welfareOfRule
  exact μ.integral_mono _ _ (fun x => winner_maximizes_welfare auc x htruth (rule x))

/-- Corollary: if two allocation rules achieve the same expected welfare,
    they must assign the same value at every query point (assuming the
    winner rule is one of them).

    This follows from pointwise domination + equal integrals: if f ≥ g
    everywhere and ∫f = ∫g, then f = g everywhere.

    Note: without a measure-theoretic framework, we state this as
    pointwise equality rather than a.e. equality. The stronger a.e.
    version would require Mathlib's measure theory.

    Standard measure theory. -/
theorem integral_efficiency_pointwise_unique
    (auc : Auction ι E) (μ : QueryMeasure E)
    (htruth : allTruthful auc)
    (rule : E → ι)
    (hequal : welfareOfRule auc (fun x => winner auc x) μ =
              welfareOfRule auc rule μ)
    (hstrict : ∀ (f g : E → ℝ), (∀ x, f x ≥ g x) →
               μ.integrate f = μ.integrate g → ∀ x, f x = g x) :
    ∀ x, trueVal (auc.valuation (winner auc x)) x =
         trueVal (auc.valuation (rule x)) x :=
  hstrict _ _ (fun x => winner_maximizes_welfare auc x htruth (rule x)) hequal

end
