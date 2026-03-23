# auction-proof

Lean 4 formalization of VCG efficiency on power diagram auctions in continuous embedding space.

## Ground rule

**No new math.** Every `theorem` must cite the specific paper and result it formalizes **inline in a doc comment** on the theorem itself. The `.lean` file is the artifact — a reader should never need to leave it to know where the math comes from. See GOALS.md for the full citation map.

Example format:
```lean
/-- VCG is strategyproof: truthful bidding is a dominant strategy.
    Vickrey (1961), Thm 1; Clarke (1971), §3; Groves (1973), Thm 2.
    DOI: https://doi.org/10.2307/2977633 -/
theorem vcg_strategyproof ...
```

## Goal

Prove: for fixed scoring function `score_i(x) = log(b_i) - ||x - c_i||^2 / sigma_i^2`, the VCG mechanism on the resulting power diagram allocation is strategyproof and efficient.

## Theorem structure

1. **Power diagram allocation**: the scoring function partitions embedding space into advertiser territories. Each point is allocated to the highest-scoring advertiser.
2. **VCG payments**: each winner pays the externality they impose — the difference in social welfare with and without them.
3. **Strategyproofness**: truthful bidding (bid = true value) is a dominant strategy under VCG.
4. **Efficiency**: the allocation maximizes total social welfare (sum of winners' values).

## Assumptions

- Grades are natural numbers with + (the semiring from Kura 2026)
- Advertiser valuations decay as Gaussian in distance from their center
- Publisher tau is fixed (exogenous relevance threshold)
- User retention curve R(f) is concave with R(0) = R(1) = 0 (existence of optimal frequency assumed, not formalized)

## Context

- Blog series: june.kim/vector-space (especially /power-diagrams-ad-auctions, /three-levers, /one-shot-bidding, /the-price-of-relevance)
- Simulation: github.com/kimjune01/openauction
- Category theory connection: Hedges 2018 (compositional game theory), Kura 2026 (indexed graded monads)

## Build

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

## Mathlib

Project initialized with Mathlib dependency. Use `lake exe cache get` to fetch prebuilt oleans.
