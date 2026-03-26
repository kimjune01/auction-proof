import AuctionProof.Auction
import AuctionProof.Axioms
import AuctionProof.Efficiency
import AuctionProof.IntegralEfficiency

/-!
# Gaussian Surplus Optimality

## Main result

Under Gaussian valuations in continuous embedding space, the VCG
power-diagram allocation is as efficient as any allocation can be.
No mechanism — not just no VCG mechanism, but no mechanism whatsoever —
can achieve higher expected social welfare.

## Proof chain

1. `trueVal_positive` (this file): each Gaussian value function is
   strictly positive (from b_i > 0 and exp > 0).
2. `winner_maximizes_welfare` (Efficiency.lean): the winner at each
   point x achieves the highest value among all advertisers.
3. `integral_efficiency` (IntegralEfficiency.lean): pointwise domination
   ⟹ integral domination.
4. `gaussian_optimality` (this file): the composition.

## Why this matters for economists

The Gaussian decay model v_i(x) = b_i * exp(-||x-c_i||²/σ_i²) is the
natural model when:
- Relevance decreases with distance in embedding space
- The rate of decrease is advertiser-specific (sigma)
- Willingness to pay scales the whole curve (bid)

Under these assumptions, VCG on the induced power diagram is not just
"pretty good" — it is *provably optimal*. No clever mechanism design can
beat it. The only room for improvement is in the choice of embedding space
itself (which is outside the auction's scope).

## References

- Groves (1973), Thm 1: efficient choice rule = argmax of values.
  DOI: https://doi.org/10.2307/1914085
- Green & Laffont (1977), Thm 1: VCG is the *only* efficient DSIC mechanism.
- Aurenhammer (1987), §2: power diagram geometry.
  DOI: https://doi.org/10.1137/0216006
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- GAUSSIAN-SPECIFIC PROPERTIES
-- ============================================================

/-- The Gaussian value function is strictly positive everywhere.

    Follows from b_i > 0 and exp(·) > 0.

    Not a published theorem — this is a consequence of the model definition. -/
theorem trueVal_positive (v : Valuation E) (x : E) :
    0 < trueVal v x := by
  unfold trueVal
  exact mul_pos v.value_pos (Real.exp_pos _)

-- ============================================================
-- MAIN THEOREM: Gaussian Optimality
-- ============================================================

/-- Under Gaussian valuations and truthful reporting, the VCG
    power-diagram allocation maximizes expected social welfare over
    ALL possible allocation rules.

    This is the headline result for economists:
    **No allocation can do better than VCG on the power diagram.**

    The proof composes:
    1. winner_maximizes_welfare: at each query x, the winner has the
       highest value (Efficiency.lean, proved).
    2. Specializing to any alternative rule: trueVal(winner) ≥ trueVal(alt).
    3. integral_mono: pointwise ≥ ⟹ integral ≥ (QueryMeasure axiom).

    Groves (1973), Thm 1.
    DOI: https://doi.org/10.2307/1914085 -/
theorem gaussian_optimality
    (auc : Auction ι E) (μ : QueryMeasure E)
    (htruth : allTruthful auc) :
    ∀ (rule : E → ι),
      welfareOfRule auc (fun x => winner auc x) μ ≥
        welfareOfRule auc rule μ :=
  integral_efficiency auc μ htruth

end
