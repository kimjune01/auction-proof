import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

/-!
# VCG Efficiency on Power Diagram Auctions

Lean 4 formalization proving that VCG on Gaussian embedding auctions is
welfare-optimal, incentive-compatible, and equilibrium-efficient.

## File map

- **Auction.lean** — definitions: Report, Valuation, score, trueVal, winner,
  Clarke pivot payment, playerUtility.
- **Axioms.lean** — the sole non-definitional assumption: QueryMeasure
  (monotone integration operator).
- **Efficiency.lean** — the contribution: `score_eq_log_trueVal` (score =
  log(value) under truthful reports), `score_eq_log_reportedVal` (same
  but unconditional — the key to DSIC), `winner_maximizes_welfare`
  (pointwise welfare optimality), `winner_maximizes_reportedVal`
  (unconditional reported-value optimality).
- **Strategyproof.lean** — utility case analysis, payment invariance,
  `vcg_dsic` (dominant strategy incentive compatibility — only player i
  needs to be truthful), Nash equilibrium as corollary.
- **IntegralEfficiency.lean** — pointwise optimality ⟹ integral optimality.
- **GaussianOptimality.lean** — headline result: no allocation beats VCG.
  Capstone: `gaussian_vcg_weakly_dominates` (welfare-optimal ∧ incentive-
  compatible ∧ equilibrium-efficient).
- **OpenGame.lean** — Hedges' compositional game theory: open games,
  sequential and parallel composition, decomposition theorems.
- **VectorSpace.lean** — blog claim catalog with proofs, stubs, and roadmap.

## Blog series

https://june.kim/vector-space
-/

#check Real.log
#check InnerProductSpace
