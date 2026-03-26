import AuctionProof.Auction

/-!
# Assumptions

Everything the proof chain actually rests on, and nothing more.

## What's baked into the definitions (Auction.lean)

These are not axioms — they're consequences of the type signatures:

- **Quasilinear utility**: `utility` is defined as `value - payment`. There is
  no class for this because it's not an assumption, it's the definition.
- **Positive bids and sigmas**: `Report` and `Valuation` carry `bid_pos` and
  `sigma_pos` fields. The Gaussian value function `trueVal` is automatically
  positive (product of positive bid and positive exp).
- **Independent private values**: `Auction.withReport` only changes `report`,
  not `valuation`. This is structural, not an axiom.
- **Free disposal**: `welfareOthersWithout` returns 0 when the restricted
  player set is empty. No axiom needed.
- **Finite nonempty advertisers**: the `[Fintype ι] [Nonempty ι]` type class
  constraints on `ι`.

## What's axiomatized (this file)

Only the integration interface, because we dropped Mathlib's measure theory:

- `QueryMeasure`: an integration operator with monotonicity.

This is the sole non-definitional assumption in the proof chain.

## What's a hypothesis on theorems

- `isTruthful`: player i reports honestly. This appears as a precondition
  on the DSIC theorem (`vcg_dsic`) — only player i needs to be truthful.
- `allTruthful`: all players report honestly. Used for the efficiency
  theorems and the Nash equilibrium corollary.
  The proof says: truthful reporting is a dominant strategy (DSIC), which
  implies Nash equilibrium and also maximizes surplus (efficiency).
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- INTEGRATION INTERFACE
-- Replaces Mathlib's Bochner integral.
-- ============================================================

/-- A query distribution over the embedding space, equipped with an
    integration operator.

    This axiomatizes exactly what we need from measure theory:
    1. An integral operator that maps (E → ℝ) to ℝ.
    2. Monotonicity: if f(x) ≥ g(x) everywhere, then ∫f ≥ ∫g.

    An economist can read this as: "there is a probability distribution
    over queries, and expected values respect pointwise ordering."

    No assumptions about the distribution's shape, density, support, or
    dimension. Just "integrals exist and respect ≥."

    Standard measure theory. -/
structure QueryMeasure (E : Type*) where
  /-- The integral operator: maps a real-valued function on E to its
      expected value under the query distribution. -/
  integrate : (E → ℝ) → ℝ
  /-- Monotonicity: pointwise ≥ implies integral ≥.

      This is the only property of integration we use. It holds for
      any finite positive measure (Lebesgue, Bochner, Riemann).
      Standard measure theory. -/
  integral_mono : ∀ (f g : E → ℝ), (∀ x, f x ≥ g x) → integrate f ≥ integrate g

end
