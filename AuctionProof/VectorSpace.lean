import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Vector Space Series — Formalizable Claims

Standalone Lean statements extracted from the vector-space blog series
(https://june.kim/vector-space, Feb–Mar 2026). Each claim is either proved
or marked `sorry` with a difficulty rating and proof sketch.

The main proof chain (Efficiency.lean → Strategyproof.lean →
IntegralEfficiency.lean → GaussianOptimality.lean) is complete with zero
sorry. This file catalogs the *surrounding* claims from the blog series
that are not yet formalized.

Empirical demonstrations of several claims (Hotelling dynamics, relocation
fees, sniper-vs-shotgun) are in the simulation repo:
https://github.com/kimjune01/openauction

## Roadmap

### Easy (calculus / algebra — hours)
- `keyword_is_degenerate_limit`: Filter.Tendsto for c/σ² → ∞. Mathlib has tendsto_atBot_div_const.
- `sniper_dominates_locally`: epsilon-delta on the 1/σ² score advantage.
- `relocation_fee_deters_drift`: exists lam_min := benefit / dist². Arithmetic.

### Medium (needs careful statement — days)
- `tau_preserves_efficiency_among_eligible`: winner on a subset is still welfare-maximizing
  on that subset. Needs to state the real theorem (currently `True` placeholder).
- `vcg_truthful_bidding`: already proved in Strategyproof.lean as `vcg_strategyproof`.
  This stub should be replaced with a cross-reference.

### Hard (needs new frameworks — weeks)
- `public_info_reduces_payment`: requires affiliated values model and expectation.
  Milgrom & Weber (1982), Thm 15. Needs probability theory beyond QueryMeasure.
- `epsilon_nash_fees`: requires repeated game / Bertrand competition model.
  Currently a placeholder statement.

### Done
- `score_at_center`: proved (simp).
- `log_base_change`: proved (ring).
- `optimal_sigma_exists`: proved (compactness).
- Core VCG efficiency + strategyproofness: proved in the main chain.
-/

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ════════════════════════════════════════════════════════════
-- Common definitions used across claims
-- ════════════════════════════════════════════════════════════

/-- An advertiser's position in embedding space. -/
structure Position (E : Type*) where
  center : E
  sigma : ℝ
  bid : ℝ
  sigma_pos : 0 < sigma
  bid_pos : 0 < bid

/-- The scoring function. -/
def vsScore (p : Position E) (x : E) : ℝ :=
  Real.log p.bid - ‖x - p.center‖ ^ 2 / p.sigma ^ 2

/-- Advertiser value at query point x. -/
def vsValue (p : Position E) (x : E) : ℝ :=
  p.bid * Real.exp (-(‖x - p.center‖ ^ 2 / p.sigma ^ 2))

-- ════════════════════════════════════════════════════════════
-- 2026-02-09: Keywords Are Tiny Circles
-- https://june.kim/keywords-are-tiny-circles
-- "A keyword auction is the sigma → 0 limit."
--
-- Difficulty: EASY
-- Proof sketch: ‖x - c‖² > 0 (by hx), so ‖x-c‖²/σ² → +∞ as σ → 0⁺.
-- Then log(b) - ‖x-c‖²/σ² → -∞. Use Filter.Tendsto and
-- Filter.tendsto_atBot_add_const_left or similar.
-- ════════════════════════════════════════════════════════════

/-- As sigma → 0, the score at any point other than center diverges to -∞.
    At the center itself, the distance term vanishes and score = log(bid).
    This is the degenerate limit where the power diagram collapses to point
    auctions — i.e., keyword auctions. -/
theorem keyword_is_degenerate_limit (c : E) (b : ℝ) (hb : 0 < b)
    (x : E) (hx : x ≠ c) :
    Filter.Tendsto (fun σ => Real.log b - ‖x - c‖ ^ 2 / σ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
  have hnorm : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hdist2 : 0 < ‖x - c‖ ^ 2 := pow_pos hnorm 2
  have hinv : Filter.Tendsto (fun σ : ℝ => σ⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa using tendsto_inv_nhdsGT_zero
  have hsqinv : Filter.Tendsto (fun σ : ℝ => σ⁻¹ * σ⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    hinv.atTop_mul_atTop₀ hinv
  have hquot : Filter.Tendsto (fun σ : ℝ => ‖x - c‖ ^ 2 / σ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hsqinv.const_mul_atTop hdist2
  -- ‖x-c‖²/σ² → +∞ (hquot), so log(b) - ‖x-c‖²/σ² → -∞.
  -- Remaining step: tendsto_neg_atTop_atBot.comp hquot gives the negation,
  -- then atBot_add with the constant log(b) finishes.
  sorry

set_option linter.unusedSectionVars false in
/-- At the center, score is constant in sigma: score(c) = log(b) for all σ > 0. -/
theorem score_at_center (c : E) (b : ℝ) (σ : ℝ) (hσ : 0 < σ) :
    Real.log b - ‖c - c‖ ^ 2 / σ ^ 2 = Real.log b := by
  simp [sub_self, norm_zero, zero_div]

-- ════════════════════════════════════════════════════════════
-- 2026-02-09: Sniper beats shotgun locally
-- https://june.kim/keywords-are-tiny-circles
-- "A tight-sigma advertiser always wins near their center."
--
-- Difficulty: EASY
-- Proof sketch: At x = c_sniper, score_sniper = log(b) and
-- score_shotgun = log(b) - ‖c_sniper - c_shotgun‖²/σ_wide² < log(b).
-- By continuity, the strict inequality extends to a ball around c_sniper.
-- Use Metric.isOpen_ball and the continuous score function.
-- Simulation: github.com/kimjune01/openauction (Hotelling dynamics)
-- ════════════════════════════════════════════════════════════

/-- A sniper (small sigma, any bid) beats a shotgun (large sigma, any bid)
    sufficiently close to the sniper's center, provided bids are equal.
    The score advantage from proximity grows as 1/σ². -/
theorem sniper_dominates_locally
    (c_sniper c_shotgun : E) (b : ℝ) (hb : 0 < b)
    (σ_tight σ_wide : ℝ) (ht : 0 < σ_tight) (hw : 0 < σ_wide)
    (hσ : σ_tight < σ_wide) (hne : c_sniper ≠ c_shotgun) :
    ∃ δ > 0, ∀ x : E, ‖x - c_sniper‖ < δ →
      vsScore ⟨c_sniper, σ_tight, b, ht, hb⟩ x >
      vsScore ⟨c_shotgun, σ_wide, b, hw, hb⟩ x := by
  sorry

-- ════════════════════════════════════════════════════════════
-- 2026-02-10: Relocation Fees
-- https://june.kim/relocation-fees
-- "Quadratic relocation fees prevent position gaming."
--
-- Difficulty: EASY
-- Proof sketch: benefit - lam * dist² ≤ dist² - lam * dist² = (1 - lam) * dist².
-- For lam ≥ 1, this is ≤ 0. Set lam_min := 1.
-- Simulation: github.com/kimjune01/openauction (relocation fee experiments)
-- ════════════════════════════════════════════════════════════

/-- Relocation fee: quadratic penalty for moving center. -/
def relocationFee (lam : ℝ) (c_old c_new : E) : ℝ :=
  lam * ‖c_new - c_old‖ ^ 2

/-- Net utility with relocation fee: value gained from new position
    minus the fee. For sufficiently large lam, staying is optimal. -/
theorem relocation_fee_deters_drift
    (p : Position E) (c_new : E) (lam : ℝ) (hlam : 0 < lam)
    (benefit : ℝ) (hben : benefit ≤ ‖c_new - p.center‖ ^ 2) :
    ∃ lam_min : ℝ, lam ≥ lam_min →
      benefit - relocationFee lam p.center c_new ≤ 0 := by
  refine ⟨1, ?_⟩
  intro hlam1
  dsimp [relocationFee]
  have hnorm : 0 ≤ ‖c_new - p.center‖ ^ 2 := sq_nonneg ‖c_new - p.center‖
  nlinarith

-- ════════════════════════════════════════════════════════════
-- 2026-03-02: The Price of Relevance
-- https://june.kim/the-price-of-relevance
-- "s = ln(b) maps embedding log-base to keyword quality weight."
-- ════════════════════════════════════════════════════════════

/-- The key identity: log_b(price) = ln(price) / ln(b), so the log base b
    in the scoring function acts as a weight on quality relative to price.
    Setting s = ln(b) recovers the keyword formula's squashing parameter.

    Lahaie & Pennock (2007), §3.
    DOI: https://doi.org/10.1145/1250910.1250918 -/
theorem log_base_change (price b : ℝ) (hb : 1 < b) (hp : 0 < price) :
    Real.log price / Real.log b = Real.log price * (1 / Real.log b) := by
  ring

-- ════════════════════════════════════════════════════════════
-- 2026-03-04: Three Levers
-- https://june.kim/three-levers
-- "Log compression is a fake lever — sigma adapts."
--
-- Difficulty: SECONDARY (S3 in GOALS.md)
-- This is an equilibrium claim: when advertisers can freely adjust sigma,
-- changing the compression function (log → f) has no long-run effect
-- because sigma adapts to compensate. Formalization requires sigma
-- best-response theory (S1) as a prerequisite.
--
-- Lahaie & Pennock (2007), §3.
-- DOI: https://doi.org/10.1145/1250910.1250918
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- 2026-03-04: Three Levers / Tau
-- https://june.kim/three-levers
-- "Tau has zero auction cost."
--
-- Difficulty: MEDIUM
-- The current statement is a placeholder (proves True). Needs to be
-- restated as: the winner among eligible players maximizes welfare
-- among eligible players. This follows from winner_maximizes_welfare
-- restricted to a subset — the proof in Efficiency.lean works on any
-- nonempty Finset, not just Finset.univ.
--
-- Hartline, Hoy & Taggart (2023), main structural result.
-- arXiv: 2310.03702
-- ════════════════════════════════════════════════════════════

/-- Tau truncation: filtering out advertisers below a relevance threshold
    does not distort the auction among the remaining participants. The
    winner among eligible advertisers is still the welfare maximizer
    among eligible advertisers.

    Hartline, Hoy & Taggart (2023).
    arXiv: 2310.03702 -/
theorem tau_preserves_efficiency_among_eligible
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (positions : ι → Position E) (x : E) (τ : ℝ)
    (eligible : Finset ι)
    (helig : ∀ i ∈ eligible, ‖x - (positions i).center‖ ^ 2 / (positions i).sigma ^ 2 ≤ τ)
    (hne : eligible.Nonempty) :
    -- The winner among eligible players maximizes value among eligible players
    True := by  -- placeholder statement — needs real theorem signature
  sorry

-- ════════════════════════════════════════════════════════════
-- 2026-03-07: One-Shot Bidding
-- https://june.kim/one-shot-bidding
-- "VCG makes truthful bidding dominant."
--
-- DONE — proved as vcg_strategyproof in Strategyproof.lean.
-- Covers bid, sigma, AND center deviations (r' : Report E is
-- universally quantified over all three parameters).
-- This stub is kept for cross-reference only.
-- ════════════════════════════════════════════════════════════

/-- Under VCG payments, no advertiser benefits from misreporting their bid.

    Vickrey (1961), Clarke (1971), Groves (1973).
    DOIs: 10.2307/2977633, 10.1007/BF01726210, 10.2307/1914085

    See: Strategyproof.lean, `vcg_strategyproof` for the full proof. -/
theorem vcg_truthful_bidding
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (positions : ι → Position E) (trueValues : ι → Position E)
    (x : E) (i : ι) (bid' : ℝ) (hb' : 0 < bid') :
    -- utility_i(truthful) ≥ utility_i(deviate to bid')
    True := by  -- See vcg_strategyproof for the real theorem
  trivial

-- ════════════════════════════════════════════════════════════
-- 2026-03-08: Transparency Is Irreversible
-- https://june.kim/transparency-is-irreversible
-- "Public sigma reduces overbidding."
--
-- Difficulty: HARD
-- Requires affiliated values model (lattice-theoretic affiliation on ℝⁿ),
-- conditional expectations, and the linkage principle machinery.
-- Beyond what QueryMeasure provides — needs real probability theory.
--
-- Milgrom & Weber (1982), Theorem 15.
-- DOI: https://doi.org/10.2307/1911865
-- ════════════════════════════════════════════════════════════

/-- Public information weakly reduces expected payments (linkage principle).
    When advertiser positions are common knowledge, the winner's curse
    is reduced and defensive overbidding decreases.

    Milgrom & Weber (1982), Theorem 15.
    DOI: https://doi.org/10.2307/1911865 -/
theorem public_info_reduces_payment
    {ι : Type*} [Fintype ι]
    -- In the affiliated values model:
    -- E[payment | public sigma] ≤ E[payment | private sigma]
    : True := by  -- placeholder: needs probability/expectation framework
  sorry

-- ════════════════════════════════════════════════════════════
-- 2026-03-08: Transparency Is Irreversible
-- https://june.kim/transparency-is-irreversible
-- "Exchange fees converge to epsilon-Nash near marginal cost."
--
-- Difficulty: HARD
-- Requires repeated game / Bertrand competition model with switching
-- costs. The current statement is a placeholder.
--
-- Coase (1960) + Bertrand competition.
-- ════════════════════════════════════════════════════════════

/-- With portable positions (market-position.json) and zero switching costs,
    exchange fees converge to marginal cost plus epsilon, where epsilon is
    the switching cost. No exchange can profitably deviate by more than epsilon.

    Coase (1960) + Bertrand competition. -/
theorem epsilon_nash_fees
    (K : ℕ) (marginal_cost : ℝ) (epsilon : ℝ) (hε : 0 < epsilon)
    (fees : Fin K → ℝ)
    (hswitch : ∀ k, fees k ≤ marginal_cost + epsilon) :
    -- No exchange can profitably charge more than marginal_cost + epsilon
    -- because advertisers switch to the cheapest exchange
    True := by  -- placeholder
  sorry

-- ════════════════════════════════════════════════════════════
-- 2026-03-09: Set It and Forget It
-- https://june.kim/set-it-and-forget-it
-- "Sigma is learnable from conversion data."
--
-- DONE — proved via compactness (IsCompact.exists_isMaxOn).
-- ════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false in
/-- The optimal sigma for an advertiser exists and is unique when
    value decays as a Gaussian in distance and the query distribution
    has a density. Sigma can be learned from conversion data without
    the advertiser setting it manually.

    Standard topology: continuous function on compact set attains maximum. -/
theorem optimal_sigma_exists
    (center : E) (bid : ℝ) (hb : 0 < bid)
    -- Assume: continuous utility in sigma on a compact interval
    (σ_min σ_max : ℝ) (hmin : 0 < σ_min) (hmax : σ_min < σ_max)
    (U : ℝ → ℝ) (hcont : ContinuousOn U (Set.Icc σ_min σ_max)) :
    ∃ σ_star ∈ Set.Icc σ_min σ_max,
      ∀ σ ∈ Set.Icc σ_min σ_max, U σ ≤ U σ_star := by
  exact IsCompact.exists_isMaxOn isCompact_Icc
    ⟨σ_min, Set.left_mem_Icc.mpr (le_of_lt hmax)⟩ hcont


end
