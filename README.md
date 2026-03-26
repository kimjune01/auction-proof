# auction-proof

Lean 4 formalization proving that VCG on Gaussian embedding auctions is maximally efficient and strategyproof. Zero sorry in the proof chain.

## The claim

For any finite-dimensional real inner product space (the embedding), if advertiser relevance decays as a Gaussian in distance, then the scoring function `log(b) - ||x-c||²/σ²` is a monotone transform of value. Therefore:

1. The power diagram allocation (argmax of score) maximizes social welfare at every query point.
2. VCG payments make truthful reporting each advertiser's best response.
3. No allocation rule — not just no power diagram, but no allocation whatsoever — achieves higher expected welfare.

The contribution is `score_eq_log_trueVal`: showing that under truthful reporting, `score_i(x) = log(trueVal_i(x))`. This is the bridge between the embedding geometry and the VCG machinery. Everything else is standard (Vickrey 1961, Clarke 1971, Groves 1973).

## What's proved

| Theorem | File | What it says |
|---------|------|-------------|
| `score_eq_log_trueVal` | Efficiency.lean | score = log(value) under truthful reports |
| `winner_maximizes_welfare` | Efficiency.lean | the winner has the highest value at every query point |
| `playerUtility_decomp` | Strategyproof.lean | utility = total welfare minus a constant |
| `welfareOthersWithout_invariant` | Strategyproof.lean | the constant doesn't depend on your report |
| `vcg_strategyproof` | Strategyproof.lean | truthful bidding is weakly dominant |
| `integral_efficiency` | IntegralEfficiency.lean | expected welfare is maximized over all allocation rules |
| `gaussian_optimality` | GaussianOptimality.lean | no allocation beats VCG on Gaussian embeddings |
| `composed_equilibria_decompose` | OpenGame.lean | Hedges' Thm 4.3: composite Nash = component Nash |
| `vcg_is_nash_equilibrium` | Strategyproof.lean | VCG satisfies Nash in Hedges' open game framework |

## What's assumed

1. **Definitions** (Auction.lean): Gaussian scoring function, single-winner allocation, Clarke pivot payment, quasilinear utility. These define the model, not assumptions about it.
2. **`QueryMeasure.integral_mono`** (Axioms.lean): integrals respect pointwise ≥. The sole non-definitional axiom.
3. **`allTruthful`**: theorem hypothesis — "if everyone reports honestly." Not a global axiom.

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
