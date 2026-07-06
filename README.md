# auction-proof

[![DOI](https://zenodo.org/badge/1189850319.svg)](https://doi.org/10.5281/zenodo.21214697)

Lean 4 formalization proving that VCG on Gaussian embedding auctions is maximally efficient and strategyproof. Zero sorry in the proof chain.

## The claim

For any real inner product space (the embedding), if advertiser relevance decays as a Gaussian in distance, then the scoring function `log(b) - ||x-c||²/σ²` is a monotone transform of value. Therefore:

1. The power diagram allocation (argmax of score) maximizes social welfare at every query point.
2. VCG payments make truthful reporting each advertiser's best response.
3. No allocation rule — not just no power diagram, but no allocation whatsoever — achieves higher expected welfare.

The contribution is `score_eq_log_trueVal`: showing that under truthful reporting, `score_i(x) = log(trueVal_i(x))`. This is the bridge between the embedding geometry and the VCG machinery. Everything else is standard (Vickrey 1961, Clarke 1971, Groves 1973).

Two geometric bookends (PowerDiagram.lean, SecondPrice.lean) pin down the "power diagram" name and the "keywords are a special case" claim: with equal sigmas the allocation is a power diagram in the embedding space itself; with heterogeneous sigmas it is exactly a power diagram one dimension up, restricted to the paraboloid `(x, ‖x‖²)` (Aurenhammer 1987, §4). And at a query point where all centers coincide — a keyword — the mechanism collapses to Vickrey's sealed-bid second-price auction, payment included.

## What's proved

| Theorem | File | What it says |
|---------|------|-------------|
| `score_eq_log_trueVal` | Efficiency.lean | score = log(value) under truthful reports |
| `score_eq_log_reportedVal` | Efficiency.lean | score = log(reportedVal) unconditionally — key to DSIC |
| `winner_maximizes_welfare` | Efficiency.lean | the winner has the highest true value (under allTruthful) |
| `winner_maximizes_reportedVal` | Efficiency.lean | the winner has the highest reported value (unconditional) |
| `vcg_dsic` | Strategyproof.lean | **truthful bidding is a dominant strategy (DSIC)** — only player i needs to be truthful |
| `vcg_strategyproof` | Strategyproof.lean | Nash equilibrium (corollary of DSIC under allTruthful) |
| `integral_efficiency` | IntegralEfficiency.lean | expected welfare is maximized over all allocation rules |
| `gaussian_optimality` | GaussianOptimality.lean | no allocation beats VCG on Gaussian embeddings |
| `gaussian_vcg_weakly_dominates` | GaussianOptimality.lean | capstone: welfare-optimal ∧ DSIC ∧ equilibrium-efficient |
| `composed_equilibria_decompose` | OpenGame.lean | Hedges' Thm 4.3: composite Nash = component Nash |
| `score_le_iff_powerDist_le` | PowerDiagram.lean | equal-sigma case: the allocation is a power diagram in E (weights σ²·log b) |
| `score_sub_affine` | PowerDiagram.lean | equal-sigma bisectors are hyperplanes |
| `liftedPowerDist_paraboloid` | PowerDiagram.lean | **variable sigma**: the allocation is a power diagram in E × ℝ via the Aurenhammer lift (x, ‖x‖²) |
| `winner_minimizes_liftedPowerDist` | PowerDiagram.lean | the winner rule is the lifted power-diagram cell assignment, for arbitrary sigmas |
| `winner_maximizes_bid_of_common_center` | SecondPrice.lean | at a keyword point (common centers), the auction ranks by bid alone |
| `vcgPayment_common_center_second_price` | SecondPrice.lean | at a keyword point, Clarke pivot = highest competing bid — exact Vickrey recovery |

## What's assumed

1. **Definitions** (Auction.lean): Gaussian scoring function, single-winner allocation, Clarke pivot payment, quasilinear utility. These define the model, not assumptions about it.
2. **`QueryMeasure.integral_mono`** (Axioms.lean): integrals respect pointwise ≥. The sole non-definitional axiom.
3. **`isTruthful`**: theorem hypothesis on DSIC — "player i reports honestly." Others can report anything.
4. **`allTruthful`**: theorem hypothesis on efficiency — "everyone reports honestly." Needed for welfare optimality, not for incentive compatibility.

That's it. No assumptions about the query distribution, embedding dimension, number of advertisers, or reserve prices. IPV, quasilinearity, and free disposal are baked into the type signatures.

## Context

- Blog series: [june.kim/vector-space](https://june.kim/vector-space), especially [Power Diagrams for Ad Auctions](https://june.kim/power-diagrams-for-ad-auctions)
- Simulation: [github.com/kimjune01/openauction](https://github.com/kimjune01/openauction)
- Compositional game theory: Ghani, Hedges, Winschel & Zahn (2018), [arXiv:1603.04641](https://arxiv.org/abs/1603.04641)

## Build

```
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

Requires Lean 4 (v4.29.0-rc6) and Mathlib.

## License

AGPL-3.0
