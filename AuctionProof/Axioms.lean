import AuctionProof.Auction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

This is the sole non-definitional assumption in the proof chain. It is carried
as a structure hypothesis, not a Lean `axiom`, so `#print axioms` on every
downstream theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
The interface is not vacuous: `QueryMeasure.dirac` and
`QueryMeasure.ofWeightedFinset` below construct concrete instances — a point
evaluation and a finite weighted expectation — that discharge `integral_mono`
by proof.

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
    dimension. Just "expectations exist and respect ≥." See the note on
    `integral_mono` for the exact scope of that quantifier. -/
structure QueryMeasure (E : Type*) where
  /-- The integral operator: maps a real-valued function on E to its
      expected value under the query distribution. -/
  integrate : (E → ℝ) → ℝ
  /-- Monotonicity: pointwise ≥ implies integral ≥.

      This is the only property of integration we use. Note the scope:
      the field quantifies over ALL functions f g, not only measurable
      or integrable ones, so `QueryMeasure` is a total monotone
      expectation operator (e.g. a finite weighted sum over a query log,
      or any finitely additive expectation), not a literal Lebesgue
      integral, which is partial. A measure-theoretic integral satisfies
      this interface on the functions it can evaluate; downstream
      theorems that quantify over arbitrary allocation rules inherit
      exactly this interface's strength. -/
  integral_mono : ∀ (f g : E → ℝ), (∀ x, f x ≥ g x) → integrate f ≥ integrate g

-- ============================================================
-- CONCRETE INSTANCES
-- The integration interface is satisfiable, not vacuous: these
-- build QueryMeasures and discharge `integral_mono` by proof, so
-- the downstream theorems are not quantifying over an empty class.
-- ============================================================

/-- The Dirac query measure at a single point: `integrate f = f x₀`.
    The minimal witness that the interface is inhabited. -/
def QueryMeasure.dirac {E : Type*} (x₀ : E) : QueryMeasure E where
  integrate f := f x₀
  integral_mono _ _ hfg := hfg x₀

/-- A finite weighted expectation over a query log `s` with nonnegative
    weights `w`: `integrate f = ∑ x ∈ s, w x * f x`. This is the "finite
    weighted sum over a query log" the `QueryMeasure` docstring describes; it
    satisfies `integral_mono` because a nonnegative-weighted sum preserves
    pointwise ≥. -/
def QueryMeasure.ofWeightedFinset {E : Type*} (s : Finset E) (w : E → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) : QueryMeasure E where
  integrate f := ∑ x ∈ s, w x * f x
  integral_mono _ _ hfg :=
    Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hfg x) (hw x hx)

end
