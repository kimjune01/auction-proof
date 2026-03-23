# Proof Goals: VCG Efficiency on Power Diagram Auctions

*Merged from independent proposals by GPT-5.4 (Codex) and Claude (subagent), with editorial notes from conversation context.*

## Ground rule

**No new math.** Every `theorem` in Lean must cite the specific paper and result it formalizes. This project is a machine-checked transcription of existing proofs, not a novel contribution. The value is in the verification, not the invention. If a claim cannot be linked to a published result, it does not belong in the proof.

## Scoring function under proof

```
score_i(x) = log(b_i) - ||x - c_i||^2 / sigma_i^2
```

---

## PRIMARY: VCG Efficiency on Power Diagram Allocation

### Theorems

**P1 (Partition).** The scoring function partitions E into convex cells (the power diagram). When all sigma_i are equal, pairwise boundaries are affine hyperplanes. In the general case, boundaries are quadratic surfaces. The scoring function is an affine transformation of the power distance `||x - c_i||^2 - w_i` with `w_i = sigma_i^2 * log(b_i)`, so the resulting partition is exactly a power diagram.

**P2 (Efficiency).** The allocation maximizes total social welfare `sum_i integral_{R_i} v_i(x) dmu(x)` over all partitions, where `v_i(x) = b_i * exp(-||x - c_i||^2 / sigma_i^2)`.

**P3 (Strategyproofness).** Under VCG payments (externality pricing), truthful bidding is a weakly dominant strategy.

### Why it matters

If Lean certifies "winner = welfare maximizer" and "VCG payment = strategyproof," the project formalizes the actual auction, not geometric intuition. This would also be the first Lean 4 formalization of VCG on a continuous allocation domain. The only prior formal verification is Caminati, Kerber, Lange & Rowat (AFP, 2015) in Isabelle/HOL for combinatorial VCG (finite goods, discrete allocation).

*Conversation note: The Lean proof is the credential substitute. "Don't trust me, trust the math that type-checked." A proof that compiles cannot be dismissed with "who are you to claim this."*

### Axioms

1. E is a finite-dimensional real inner product space.
2. Advertisers are finite and nonempty.
3. b_i > 0, sigma_i > 0.
4. Values are quasilinear: utility = value of allocation minus payment.
5. Ties broken by fixed total order (or: ties have measure zero under mu).
6. For aggregate welfare: mu is a finite Borel measure over E (query distribution), welfare function is integrable.
7. Independent private values (each v_i depends only on i's own type).

### Prior art

| Paper | What it provides | Specific result |
|-------|-----------------|-----------------|
| **Vickrey (1961)**, "Counterspeculation, Auctions, and Competitive Sealed Tenders," J. Finance 16(1):8-37 | Second-price truthfulness for single item | Dominant strategy in sealed-bid auctions |
| **Clarke (1971)**, "Multipart Pricing of Public Goods," Public Choice 11(1):17-33 | Externality payment (Clarke pivot) | Payment = welfare without i minus welfare of others with i |
| **Groves (1973)**, "Incentives in Teams," Econometrica 41(4):617-631 | Groves class characterization | Any payment = f(others' reports) + sum of others' values is DSIC |
| **Green & Laffont (1977)**, "Characterization of Satisfactory Mechanisms," Econometrica 45(2):427-438 | **Uniqueness**: Groves mechanisms are the *only* efficient dominant-strategy mechanisms | Justifies VCG as the unique target for formalization |
| **Myerson (1981)**, "Optimal Auction Design," Math. Oper. Res. 6(1):58-73 | Revelation principle, payment identities | Any outcome achievable by any mechanism is achievable by a truthful direct mechanism |
| **Aurenhammer (1987)**, "Power Diagrams: Properties, Algorithms and Applications," SIAM J. Comput. 16(1):78-96 | Power diagram geometry | Theorem 1: each cell is a convex polyhedron. Lifting correspondence to R^(d+1) |
| **Ausubel & Milgrom (2006)**, "The Lovely but Lonely Vickrey Auction," MIT Press | VCG benchmark for multi-item allocation | Substitutes condition (Def 2) guarantees VCG revenue is in the core |
| **Caminati et al. (2015)**, "VCG - Combinatorial Vickrey-Clarke-Groves Auctions," Archive of Formal Proofs | Only prior formal VCG verification (Isabelle/HOL) | Discrete allocation only. We extend to continuous domains in Lean 4 |

### Mathlib dependencies

**Available:**
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product, norm, dist. The ||x - c_i||^2 term.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real.log, monotonicity, concavity.
- `Mathlib.Data.Finset.Basic` — finite advertiser sets, Finset.sum, Finset.sup.
- `Data/List/MinMax` — finite argmax (argmax_mem, le_of_mem_argmax, etc.).
- `Mathlib.Analysis.Convex.*` — convexity of sets, convex hull.
- `Mathlib.LinearAlgebra.AffineSpace.*` — affine subspaces, hyperplanes.
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Lebesgue measure.
- `Mathlib.MeasureTheory.Integral.Bochner` — Bochner integral for value functions.

**Needs building:**
- `PowerDiagram.lean` — power distance, cells as `{x : E | forall j, score_i(x) >= score_j(x)}`, convexity of cells, partition proof.
- `VCGPayment.lean` — payment as `W_{-i}(a*_{-i}) - W_{-i}(a*)`, non-negativity.
- `Strategyproof.lean` — utility = total welfare minus constant, so maximizing utility = maximizing welfare.
- `Efficiency.lean` — pointwise argmax of score = pointwise argmax of value (affine relationship), so power diagram allocation maximizes integral welfare.
- Tie-broken finite argmax on Finset (wrapper around List.argmax).

### Opens the door to

Reusable types: `Advertiser`, `AllocationRule`, `Welfare`, `VCGPayment`, `QueryMeasure`. These become the SECONDARY's inputs.

*Conversation note: "Stage N's guarantee becomes stage N+1's assumption." The PRIMARY's output types (allocation, payment, strategyproofness proof term) are exactly the SECONDARY's input types. This is Definition 7 from Kura — the handshake.*

---

## SECONDARY: Composed Parameter Games

### Theorems

**S1 (Sigma Best Response).** For fixed centers, bids, publisher threshold tau, and query distribution mu, define advertiser utility U_i(sigma_i) as the integral of VCG utility over queries. There exists an optimal sigma_i* on a compact feasible interval. sigma_i* is monotonically related to impression density near c_i.

**S2 (Tau Preserves Strategyproofness).** The truncated auction (only advertisers with ||x - c_i||^2 / sigma_i^2 <= tau^2 compete) is still strategyproof under VCG. Welfare is weakly decreasing in tau (loss from exclusion, not distortion).

**S3 (Log Compression Neutrality).** For any monotone increasing f : R+ -> R, replacing log(b_i) with f(b_i) in the scoring function yields the same allocation and strategyproofness guarantee, provided f is applied uniformly.

*Conversation note: S3 formalizes the blog's finding that log(b) is a fake lever. Sigma adapts to neutralize any compression. "Two levers and a market." This is an important practical insight: the exchange that controls the compression function extracts temporary rent, but sigma adaptation erases the effect at equilibrium. The lever's value is in turning it, not where it points.*

*Conversation note: tau is zoning, not strategy. The publisher sets a percentage ("10% of conversations include a recommendation"), their server adjusts tau to hit that target. The Lean proof doesn't model HOW they optimize — it assumes they do. R(f) is concave with R(0) = R(1) = 0, so an optimum exists. Three axioms, not a model.*

### Why it matters

Upgrades the project from "the auction is correct" to "the surrounding game is analyzable." Each player's optimization is separable, which is what makes the mechanism practical. Formalizes the blog's claims that "tau has zero auction cost" and that log compression is neutral.

### Axioms

All from PRIMARY, plus:
1. Compact feasible sets for sigma_i.
2. Measurability and integrability of utility/revenue under mu.
3. Continuity of expected utility in sigma_i.
4. For tau: a no-allocation outcome with zero value/payment.
5. Advertiser's true value function: v_i(x) = b_i * exp(-||x - c_i||^2 / sigma_true_i^2). Declared sigma may differ from true sigma (strategic misreport of reach).

### Prior art

| Paper | What it provides | Specific result |
|-------|-----------------|-----------------|
| **Che (1993)**, "Design Competition through Multidimensional Auctions," RAND J. Econ. 24(4):668-680 | Scoring auctions with price-quality tradeoff | Proposition 1: revenue-maximizing platform under-rewards quality vs user-optimal |
| **Asker & Cantillon (2008)**, "Properties of Scoring Auctions," RAND J. Econ. 39(1):69-85 | Scoring auctions dominate price-only + quality threshold | Theorem 1: scoring > price + min quality. Proposition 2: pseudotype reduction makes sigma optimization tractable |
| **Lahaie & Pennock (2007)**, "Revenue Analysis of Ranking Rules for Keyword Auctions," ACM EC pp. 50-56 | Squashing parameter s in bid * quality^s | Tuning s matters more than reserve prices. s = ln(b) maps to our scoring function |
| **Hartline, Hoy & Taggart (2023)**, arXiv:2310.03702 | Reserve pricing and competitive efficiency | Competitive efficiency is closed under reserve pricing — tau has zero auction cost |
| **Hotelling (1929)** / **D'Aspremont, Gabszewicz & Thisse (1979)** | Spatial competition | Quadratic transport costs (our cost structure) prevent minimum differentiation. Sigma best response pushes toward specialization. |

### Mathlib dependencies

**Available:** compactness/topology, continuity, convexity, calculus on convex domains, Bochner/Lebesgue integration, `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.

**Needs building:**
- `SigmaOptimization.lean` — U_i(sigma_i) as function of sigma, continuity, existence of maximizer via compactness.
- `TauTruncation.lean` — truncated auction is still Groves mechanism, welfare monotonicity.
- `CompressionInvariance.lean` — monotone transform preserves ranking, hence allocation.

### Opens the door to

The SECONDARY delivers `SigmaBestResponse`, `TauTruncation.Strategyproof`, and `CompressionInvariance`. These become the STRETCH's inputs: once each player's lever is formalized, the STRETCH asks about the information game between them.

*Conversation note: The clean lemma for multi-exchange competition lives here too. "The max over efficient auctions is efficient." If each exchange runs the same VCG mechanism on the same market-position.json, the publisher taking the best result across exchanges can only improve welfare. This probably falls out for free from VCG's properties.*

---

## STRETCH: Information Games and Transparency Dominance

### Theorems

**T1 (Transparency Weakly Dominates).** Under the linkage principle (affiliated values from shared impression density mu), expected payment for advertiser i is weakly lower when all (c_i, sigma_i) are public than when any are private. Public sigma is a de-escalation signal — it reduces defensive overbidding.

**T2 (Defection Dominance).** In a repeated game where a platform chooses between transparent auctions (public parameters, attested VCG) and opaque auctions (hidden parameters, unverifiable mechanism), if switching costs are below a threshold epsilon, the transparent platform attracts all advertisers in finite time. Opacity is not a Nash equilibrium when platform competition exists.

**T3 (Compositional Auction).** The power diagram auction with VCG is an open game in the sense of Ghani, Hedges, Winschel & Zahn (2018). The sigma game and tau game compose via categorical composition (sequential) and monoidal product (simultaneous). Theorem 4.3 from Hedges: Nash equilibria of composite games decompose into equilibria of components.

*Conversation note: T2 formalizes the key insight from our discussion — defection being always losing is what makes it a protocol, not a platform. TCP/IP works because sending malformed packets hurts the sender. In this system: an advertiser who lies about their center wastes their own budget. An exchange that rigs the auction loses attestation. A publisher who fakes conversions gets crushed on fill rate. Every defection is visible and costs the defector more than the victim. That's not just incentive compatibility (VCG says truthful play is optimal) — it's stronger: untruthful play is actively punished by the network. Dominant strategy, not just Nash.*

*Conversation note: Transparency is a one-way ratchet because openness is the greedy strategy, not the altruistic one. 7.6x better IPO valuations for open-core companies. The exchange that publishes first gets the trust premium (like Visa). Any exchange that hides sigma is running the closed playbook, and a transparent competitor can poach every advertiser by importing their market-position.json on day one. The opaque exchange can't do the reverse.*

### Why it matters

This is where the project moves from mechanism design to market-structure claims. It formally bridges "VCG on embeddings works" to "public declarations and open competition are strategically stable." The compositional game theorem connects to Hedges and Kura, linking the auction proof to the broader categorical program.

### Axioms

All from PRIMARY and SECONDARY, plus:
1. Values are affiliated (Milgrom & Weber's affiliation condition).
2. Platform competition follows Bertrand model (fee-setting, advertisers choose lowest fee above quality threshold).
3. Switching costs parameterized by epsilon >= 0.
4. Common knowledge of mechanism rules and attestation.
5. For compositional theorem: auction modeled as morphism in symmetric monoidal category of open games.

### Prior art

| Paper | What it provides | Specific result |
|-------|-----------------|-----------------|
| **Milgrom & Weber (1982)**, "A Theory of Auctions and Competitive Bidding," Econometrica 50(5):1089-1122 | Linkage principle | Theorem 15: seller's expected revenue weakly higher when more information is public. Public sigma reduces winner's curse. |
| **Ghani, Hedges, Winschel & Zahn (2018)**, "Compositional Game Theory," Proc. LiCS | Open games as morphisms in symmetric monoidal category | Theorem 4.3: Nash equilibria of composite games decompose into component equilibria |
| **Kura et al. (2026)**, arXiv:2601.14846 | Indexed graded monads | Categorical scaffolding for staged mechanism composition. The grade tracks welfare through composition. The restricted pointwise order (Def 7) parallels the handshake condition. |
| **Ausubel & Milgrom (2006)** | Substitutes condition | For isotropic power diagrams, territories are substitutes (expanding one shrinks others), so VCG revenue is in the core |

*Conversation note: The connection to Kura is deeper than scaffolding. The semiring structure (costs accumulate, can't subtract) maps directly to auction accounting: bids accumulate through the pipeline, welfare is tracked as a grade, and the restricted pointwise order is the triangle inequality on compositions. Intelligence (consolidation, forgetting) requires the missing inverse — a ring, not a semiring. Legacy systems can't forget, so they can't learn. The auction protocol is a semiring by design: no refunds.*

### Mathlib dependencies

**Available:**
- `Mathlib.CategoryTheory.Monoidal.Basic` — symmetric monoidal categories.
- `Mathlib.CategoryTheory.Category.Basic` — categories, functors, natural transformations.
- `Mathlib.Order.CompleteLattice` — lattice structure for affiliation.
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — discrete probability for simplified information games.

**Needs building (substantial):**
- `OpenGame.lean` — open games (lens-like structure with play/coplay), composition, monoidal product. No Lean 4 formalization of Hedges exists. This would be a research contribution in its own right.
- `Affiliation.lean` — affiliation on R^n, linkage principle for VCG. Requires measure-theoretic lattice theory.
- `PlatformCompetition.lean` — Bertrand competition between platforms, transparency as binary strategy.

### Opens the door to

A formally verified chain: geometric allocation (PRIMARY) -> lever optimization (SECONDARY) -> information-theoretic dominance of transparency (STRETCH). Future work plugs in new auction formats as morphisms, new cost structures as grades, and new competition models as composed games.

---

## Citation Map

Every theorem links to a published result. No exceptions.

| Checkpoint | Theorem | Source | Specific result |
|-----------|---------|--------|-----------------|
| 1 | (definitions only) | Aurenhammer (1987) | Power distance definition, §2 |
| 2 | Pointwise allocation maximizes welfare | Groves (1973), Thm 1 | Efficient choice rule = argmax of values |
| 2 | Score argmax = value argmax | Aurenhammer (1987), §2 | Affine transform preserves argmax |
| 3 | VCG is strategyproof | Vickrey (1961), Thm 1; Clarke (1971), §3; Groves (1973), Thm 2 | Dominant strategy under externality payment |
| 3 | VCG is the *only* efficient DSIC mechanism | Green & Laffont (1977), Thm 1 | Uniqueness on unrestricted domains |
| 4 | Integral efficiency from pointwise | Standard measure theory | Pointwise a.e. maximization implies integral maximization |
| 5 | Monotone compression preserves allocation | Lahaie & Pennock (2007), §3 | Ranking invariance under monotone transform of bid |
| 6 | Truncation preserves strategyproofness | Hartline, Hoy & Taggart (2023), main structural result | Competitive efficiency closed under reserve pricing |
| 6 | Welfare monotone in tau | Asker & Cantillon (2008), Thm 1 | Scoring auctions dominate price + threshold |
| 7 | Optimal sigma exists | Standard topology | Continuous function on compact set attains maximum |
| 7 | Sigma best response monotone in density | Che (1993), Prop 1 | Quality weight determines specialization incentive |
| S1 | Public sigma reduces overbidding | Milgrom & Weber (1982), Thm 15 | Linkage principle: public info reduces winner's curse |
| S2 | Transparent platform dominates | Milgrom & Weber (1982) + Bertrand model | Revenue weakly higher under information revelation + fee competition |
| S3 | Compositional equilibrium decomposes | Ghani, Hedges et al. (2018), Thm 4.3 | Nash equilibria of composite games = component equilibria |

Any theorem not in this table does not belong in the codebase.

## Dependency Chain

```
PRIMARY                    SECONDARY                  STRETCH
PowerDiagram ──────────>   SigmaOptimization ──────>  OpenGame composition
VCGPayment ──────────>     TauTruncation ──────────>  Transparency dominance
Strategyproofness ────>    CompressionInvariance ──>  Defection dominance
```

Each arrow is a handshake: the output type of the left becomes the input type of the right. Stage N's guarantee becomes stage N+1's assumption.

## Effort Estimates

| Goal | New Lean files | Lines (est.) | Hardest lemma |
|------|---------------|-------------|---------------|
| PRIMARY | 4-5 | 800-1200 | Efficiency: pointwise argmax => integral welfare max |
| SECONDARY | 3 | 500-800 | SigmaBestResponse: existence via compactness of continuous utility |
| STRETCH | 3 | 600-1000 | Linkage principle: affiliation => lower expected payment under public info |

The PRIMARY is a realistic near-term target. The SECONDARY is achievable given the PRIMARY. The STRETCH requires foundational open-game infrastructure that doesn't exist in Lean 4 — completing it would itself be a research contribution.

---

## Sources

- [Vickrey (1961)](https://doi.org/10.2307/2977633)
- [Clarke (1971)](https://doi.org/10.1007/BF01726210)
- [Groves (1973)](https://www.econometricsociety.org/publications/econometrica/1973/07/01/incentives-teams)
- [Green & Laffont (1977)](https://scholar.harvard.edu/files/green/files/characterization_of_satisfactory_mechanisms_for_the_revelation_of_preferences_for_public_goods.pdf)
- [Myerson (1981)](https://doi.org/10.1287/moor.6.1.58)
- [Milgrom & Weber (1982)](https://doi.org/10.2307/1911865)
- [Aurenhammer (1987)](https://doi.org/10.1137/0216006)
- [Che (1993)](https://blogs.cuit.columbia.edu/yc2271/files/2017/05/Scoring-auctions.pdf)
- [Ausubel & Milgrom (2006)](https://doi.org/10.1017/CBO9780511492274.006)
- [Lahaie & Pennock (2007)](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/RankingPaper.pdf)
- [Asker & Cantillon (2008)](https://doi.org/10.1111/j.1756-2171.2008.00004.x)
- [Caminati et al. (2015) - AFP](https://www.isa-afp.org/entries/Vickrey_Clarke_Groves.html)
- [Ghani, Hedges et al. (2018)](https://arxiv.org/abs/1603.04641) — [Milewski on compositional game theory](https://www.youtube.com/watch?v=5Qny8YmLUzk)
- [Hartline, Hoy & Taggart (2023)](https://arxiv.org/abs/2310.03702)
- [Kura et al. (2026)](https://arxiv.org/abs/2601.14846)
