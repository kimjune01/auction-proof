import AuctionProof.Auction
import AuctionProof.Efficiency

/-!
# Compositional Game Theory Scaffold

## Overview

This file defines open games in the sense of Ghani, Hedges, Winschel & Zahn
(2018) and shows the VCG power-diagram auction fits this interface. The key
payoff is Hedges' Theorem 4.3: Nash equilibria of composite games decompose
into equilibria of the components.

This means:
- The VCG auction is one composable module, not a monolith.
- The sigma optimization game (SECONDARY) composes sequentially.
- Multiple advertisers compose in parallel (monoidal product).
- Equilibrium analysis of the full system reduces to per-component analysis.

## Structure

An open game is a lens-like object with four type parameters:
- X: observations (input context)
- Y: actions/moves (output)
- R: results/rewards (backward input)
- S: coresults (backward output)

Plus a strategy type and three operations:
- play: given a strategy and observation, produce an action
- coplay: given a strategy, observation, and result, produce a coresult
- bestResponse: given context, which strategy profiles are equilibria?

## References

- Ghani, Hedges, Winschel & Zahn (2018), "Compositional Game Theory,"
  Proc. LiCS. arXiv: 1603.04641.
  Theorem 4.3: Nash equilibria of composite games decompose into
  component equilibria.
- Hedges (2017), "Morphisms of open games," arXiv: 1711.07059.
- Kura et al. (2026), arXiv: 2601.14846. The indexed graded monad
  tracks welfare through composition. The grade's semiring structure
  ensures costs accumulate (no refunds).
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- TIER 2: OPEN GAME DEFINITIONS
-- Direct transcription of Ghani, Hedges et al. (2018).
-- ============================================================

/-- An open game in the sense of Ghani, Hedges, Winschel & Zahn (2018).

    The five type parameters are:
    - `St` (Strategy): the type of strategy profiles
    - `X` : observations / input context
    - `Y` : actions / moves / output
    - `R` : results / rewards (backward channel)
    - `S` : coresults (backward channel output)

    Ghani, Hedges, Winschel & Zahn (2018), Definition 2.1.
    arXiv: 1603.04641 -/
structure OpenGame (St X Y R S : Type*) where
  /-- Forward pass: given a strategy and observation, produce an action. -/
  play : St → X → Y
  /-- Backward pass: given a strategy, observation, and result, produce a coresult. -/
  coplay : St → X → R → S
  /-- Best response relation: which strategy deviations are rational? -/
  bestResponse : X → (Y → R) → St → Prop

/-- Nash equilibrium of an open game: a strategy profile where no player
    wants to deviate, given a context and continuation.

    Ghani, Hedges, Winschel & Zahn (2018), Definition 2.3.
    arXiv: 1603.04641 -/
def OpenGame.isNashEquilibrium
    {St X Y R S : Type*}
    (G : OpenGame St X Y R S)
    (x : X) (k : Y → R) (s : St) : Prop :=
  G.bestResponse x k s

-- ============================================================
-- COMPOSITION: Sequential and Parallel
-- ============================================================

/-- Sequential composition of open games.

    Game G plays first, then game H plays using G's output.
    The backward channel threads results back through both games.

    Ghani, Hedges, Winschel & Zahn (2018), §3.1.
    arXiv: 1603.04641 -/
def OpenGame.seq
    {St₁ St₂ X Y Z R S T : Type*}
    (G : OpenGame St₁ X Y S T)
    (H : OpenGame St₂ Y Z R S) :
    OpenGame (St₁ × St₂) X Z R T where
  play := fun ⟨s₁, s₂⟩ x =>
    H.play s₂ (G.play s₁ x)
  coplay := fun ⟨s₁, s₂⟩ x r =>
    G.coplay s₁ x (H.coplay s₂ (G.play s₁ x) r)
  bestResponse := fun x k ⟨s₁, s₂⟩ =>
    let y := G.play s₁ x
    G.bestResponse x (fun y' => H.coplay s₂ y' (k (H.play s₂ y'))) s₁ ∧
    H.bestResponse y k s₂

/-- Parallel (monoidal) composition of open games.

    Games G and H play simultaneously on independent inputs.

    Ghani, Hedges, Winschel & Zahn (2018), §3.2.
    arXiv: 1603.04641 -/
def OpenGame.par
    {St₁ St₂ X₁ X₂ Y₁ Y₂ R₁ R₂ S₁ S₂ : Type*}
    (G : OpenGame St₁ X₁ Y₁ R₁ S₁)
    (H : OpenGame St₂ X₂ Y₂ R₂ S₂) :
    OpenGame (St₁ × St₂) (X₁ × X₂) (Y₁ × Y₂) (R₁ × R₂) (S₁ × S₂) where
  play := fun ⟨s₁, s₂⟩ ⟨x₁, x₂⟩ =>
    (G.play s₁ x₁, H.play s₂ x₂)
  coplay := fun ⟨s₁, s₂⟩ ⟨x₁, x₂⟩ ⟨r₁, r₂⟩ =>
    (G.coplay s₁ x₁ r₁, H.coplay s₂ x₂ r₂)
  bestResponse := fun ⟨x₁, x₂⟩ k ⟨s₁, s₂⟩ =>
    G.bestResponse x₁ (fun y₁ => (k (y₁, H.play s₂ x₂)).1) s₁ ∧
    H.bestResponse x₂ (fun y₂ => (k (G.play s₁ x₁, y₂)).2) s₂

-- ============================================================
-- TIER 3: VCG AUCTION AS AN OPEN GAME
-- ============================================================

/-- The VCG power-diagram auction as an open game.

    - Strategy: the full auction state (report + valuation profiles)
    - Observation: a query point x ∈ E
    - Action: the winning advertiser
    - Result: the welfare value (used by downstream games)
    - Coresult: the welfare value (passed back upstream)

    Our composition. The bestResponse condition says: under VCG, no player
    can improve their utility by deviating. This is exactly strategyproofness.

    Connects to: Ghani, Hedges et al. (2018) for the framework;
    Vickrey-Clarke-Groves for the equilibrium content. -/
def vcgOpenGame : OpenGame (Auction ι E) E ι ℝ ℝ where
  play := fun auc x => winner auc x
  coplay := fun _auc _x r => r  -- pass welfare back unchanged
  bestResponse := fun x _k auc =>
    ∀ (i : ι) (r' : Report E),
      playerUtility auc i x ≥
        playerUtility (auc.withReport i r') i x

-- ============================================================
-- HEDGES' DECOMPOSITION THEOREM
-- ============================================================

/-- Nash equilibria of composite games decompose into component equilibria.

    If G and H are open games composed sequentially (or in parallel),
    a strategy profile is a Nash equilibrium of the composite if and only if
    the component strategies are Nash equilibria of the component games
    (with appropriately threaded continuations).

    Ghani, Hedges, Winschel & Zahn (2018), Theorem 4.3.
    arXiv: 1603.04641

    This is the key structural result that makes the proof modular:

    **On DSIC composition**: DSIC does NOT compose through open games
    in general. Counterexample: two DSIC mechanisms where lying in
    stage 1 gives a payoff through stage 2's output (the upstream
    report influences downstream utility through the interface).

    However, DSIC DOES compose when the continuation is *i-insensitive*:
    downstream games don't let player i's upstream report affect i's
    downstream payoff. In our auction pipeline, this holds because the
    publisher filter is exogenous (publisher decides, not the advertiser)
    and the sigma game's payoff to advertiser i doesn't depend on i's
    report to the auction beyond what VCG already handles.

    No published result in the open-games literature addresses DSIC
    composition (as of 2026). Hedges' framework decomposes Nash,
    Bayesian-Nash, and subgame-perfect equilibria, but not dominant
    strategies. A formal "DSIC composition under i-insensitive
    continuations" theorem would be a new result.

    Literature:
    - Ghani, Hedges et al. (2018), Thm 4.3: Nash composition.
    - Bolt, Hedges, Zahn (2023): Bayesian open games. arXiv: 1910.03656
    - Hedges (2018), "Morphisms of open games": subgame-perfect.
      DOI: https://doi.org/10.1016/j.entcs.2018.11.008
    proving equilibrium of the full auction-sigma-tau system reduces to
    proving equilibrium of each component separately. -/
theorem composed_equilibria_decompose
    {St₁ St₂ X Y Z R S T : Type*}
    (G : OpenGame St₁ X Y S T)
    (H : OpenGame St₂ Y Z R S)
    (x : X) (k : Z → R) (s₁ : St₁) (s₂ : St₂) :
    (G.seq H).isNashEquilibrium x k (s₁, s₂) ↔
    (G.bestResponse x (fun y => H.coplay s₂ y (k (H.play s₂ y))) s₁ ∧
     H.bestResponse (G.play s₁ x) k s₂) := by
  unfold OpenGame.seq OpenGame.isNashEquilibrium
  simp only

/-- Parallel decomposition: equilibria of the monoidal product decompose
    into component equilibria.

    Ghani, Hedges, Winschel & Zahn (2018), Theorem 4.3 (parallel case).
    arXiv: 1603.04641 -/
theorem parallel_equilibria_decompose
    {St₁ St₂ X₁ X₂ Y₁ Y₂ R₁ R₂ S₁ S₂ : Type*}
    (G : OpenGame St₁ X₁ Y₁ R₁ S₁)
    (H : OpenGame St₂ X₂ Y₂ R₂ S₂)
    (x : X₁ × X₂) (k : Y₁ × Y₂ → R₁ × R₂) (s₁ : St₁) (s₂ : St₂) :
    (G.par H).isNashEquilibrium x k (s₁, s₂) ↔
    (G.bestResponse x.1 (fun y₁ => (k (y₁, H.play s₂ x.2)).1) s₁ ∧
     H.bestResponse x.2 (fun y₂ => (k (G.play s₁ x.1, y₂)).2) s₂) := by
  unfold OpenGame.par OpenGame.isNashEquilibrium
  simp only

-- ============================================================
-- APPLICATION: Full auction system as composed game
-- ============================================================

/-- The sigma optimization game: each advertiser chooses their reach
    parameter to maximize expected utility given the auction outcome.

    This composes sequentially with the VCG auction: the auction takes
    the declared positions as input, the sigma game produces them.

    Che (1993), Proposition 1.
    DOI: https://doi.org/10.2307/2555752

    Note: bestResponse is a placeholder (True). Formalizing Che's sigma
    best-response condition is SECONDARY goal S1 in GOALS.md. -/
def sigmaGame : OpenGame (ι → ℝ) (Auction ι E) (Auction ι E) ℝ ℝ where
  play := fun _sigmas auc => auc
  coplay := fun _sigmas _auc r => r
  bestResponse := fun _auc _k _sigmas => True

/-- The tau truncation game: the publisher chooses a relevance threshold.

    This composes sequentially after the auction: it filters the allocation
    by excluding advertisers below the relevance threshold.

    Hartline, Hoy & Taggart (2023), main structural result.
    arXiv: 2310.03702

    Note: bestResponse is a placeholder (True). The publisher's tau/filter
    optimization is outside the auction's scope — see Axes of Exclusion
    (https://june.kim/axes-of-exclusion) for the compound filter model. -/
def tauGame : OpenGame ℝ (Auction ι E) (Auction ι E) ℝ ℝ where
  play := fun _tau auc => auc
  coplay := fun _tau _auc r => r
  bestResponse := fun _auc _k _tau => True

end
