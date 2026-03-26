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
  -- ‖x-c‖²/σ² → +∞ (hquot), so -(‖x-c‖²/σ²) → -∞, so log(b) + (-(‖x-c‖²/σ²)) → -∞.
  have hneg : Filter.Tendsto (fun σ => -(‖x - c‖ ^ 2 / σ ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Filter.Tendsto.comp (Filter.tendsto_neg_atTop_atBot) hquot
  simpa [sub_eq_add_neg] using
    (tendsto_const_nhds (x := Real.log b)).add_atBot hneg

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
  -- The score gap at c_sniper is positive (sniper scores log(b), shotgun scores
  -- log(b) - ‖c_sniper - c_shotgun‖²/σ_wide² < log(b)). Both score functions
  -- are continuous, so the gap is continuous and positive in a neighborhood.
  let sniper : Position E := ⟨c_sniper, σ_tight, b, ht, hb⟩
  let shotgun : Position E := ⟨c_shotgun, σ_wide, b, hw, hb⟩
  let gap : E → ℝ := fun x => vsScore sniper x - vsScore shotgun x
  have hgap_cont : Continuous gap := by
    dsimp [gap, sniper, shotgun, vsScore]
    refine (continuous_const.sub ?_).sub (continuous_const.sub ?_)
    · exact ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).div_const _
    · exact ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).div_const _
  have hgap_pos : 0 < gap c_sniper := by
    have hdist : 0 < ‖c_sniper - c_shotgun‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hsq : 0 < ‖c_sniper - c_shotgun‖ ^ 2 := pow_pos hdist 2
    have hdiv : 0 < ‖c_sniper - c_shotgun‖ ^ 2 / σ_wide ^ 2 :=
      div_pos hsq (pow_pos hw 2)
    simpa [gap, sniper, shotgun, vsScore, sub_self, norm_zero, zero_div] using hdiv
  have hEvent : ∀ᶠ x in nhds c_sniper, gap x ∈ Set.Ioi 0 :=
    hgap_cont.continuousAt.eventually_mem (Ioi_mem_nhds hgap_pos)
  rcases Metric.mem_nhds_iff.mp hEvent with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx
  have hxBall : x ∈ Metric.ball c_sniper δ := by
    simpa [Metric.ball, dist_eq_norm] using hx
  exact sub_pos.mp (hδ hxBall)

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
-- 2026-03-04: Three Levers / Tau → superseded by Axes of Exclusion
-- https://june.kim/three-levers (original)
-- https://june.kim/axes-of-exclusion (supersedes scalar tau)
--
-- Three Levers defined τ as a scalar relevance floor: isotropic sphere.
-- Axes of Exclusion replaces it with a compound filter:
--   1. Axis-aligned exclusion (per-axis category trees with bitfield lookups)
--   2. Learned Mahalanobis gate (diagonal M, directional τ)
--   3. The auction runs unchanged inside the gate
--
-- The formalization target shifts: instead of "scalar τ preserves
-- efficiency among eligible," the claim is "any pre-auction filter
-- that passes a nonempty subset preserves VCG efficiency on that
-- subset." This is a direct corollary of winner_maximizes_welfare
-- restricted to a Finset — the existing proof works on any nonempty
-- Finset, not just Finset.univ.
--
-- Difficulty: MEDIUM (needs real theorem statement)
-- Hartline, Hoy & Taggart (2023). arXiv: 2310.03702
-- ════════════════════════════════════════════════════════════

/-- Pre-auction filtering preserves VCG efficiency on the surviving set.

    Any filter (scalar τ, axis-aligned exclusion, Mahalanobis gate, or
    their composition) that passes a nonempty subset of advertisers
    preserves the welfare-maximizing property: the winner among eligible
    advertisers is still the highest-value advertiser among eligible
    advertisers. The auction doesn't care how you got the subset.

    This generalizes "tau has zero auction cost" from Three Levers and
    subsumes the compound filter pipeline from Axes of Exclusion.

    The compound filter (axes + Mahalanobis gate) strictly generalizes
    scalar τ: τ is the special case M = I with no axis exclusions.
    Since each filter is optional — the publisher can always recover
    the τ-only case by setting M = I and excluding nothing — publisher
    welfare is weakly increasing. A rational publisher only adds filters
    that improve their outcome.

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

    Proved as `vcg_strategyproof` in Strategyproof.lean. Covers deviations
    in bid, sigma, AND center (r' : Report E is universally quantified).
    This stub is kept as a cross-reference only. -/
theorem vcg_truthful_bidding
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (positions : ι → Position E) (trueValues : ι → Position E)
    (x : E) (i : ι) (bid' : ℝ) (hb' : 0 < bid') :
    True := by
  trivial

-- ════════════════════════════════════════════════════════════
-- 2026-03-08: Transparency Is Irreversible
-- https://june.kim/transparency-is-irreversible
--
-- Two independent claims:
--
-- 1. TRANSPARENT MARKETS (Akerlof 1970)
--    Opaque auction → advertisers can't verify fairness → defensive
--    bidding → high-value advertisers leave → adverse selection →
--    lemon pricing. Transparency (attested VCG, public positions)
--    resolves the information asymmetry → full participation →
--    higher welfare. This is about a single exchange's information
--    structure. Independent of whether competitors exist.
--
--    Note: under our IPV model, the linkage principle (Milgrom &
--    Weber 1982) is trivially satisfied — there's no winner's curse
--    with independent private values. The real transparency benefit
--    is resolving adverse selection about the *mechanism*, not about
--    other bidders' values.
--
--    Akerlof (1970), "The Market for 'Lemons'," QJE 84(3):488-500.
--    DOI: https://doi.org/10.2307/1879431
--
-- 2. COMPETITIVE EXCHANGES (Bertrand)
--    Multiple exchanges, portable positions (market-position.json),
--    switching cost ε. Fees converge to marginal cost + ε. This is
--    about market structure across exchanges. Independent of whether
--    any single exchange is transparent (opaque exchanges still
--    undercut each other, just at lower equilibrium welfare).
--
--    Bertrand (1883); Tirole, Theory of Industrial Organization, Ch. 5.
--
-- The two compound: transparency resolves adverse selection (1),
-- portability enables switching that drives Bertrand competition (2).
-- But they're independent claims with independent formalizations.
-- ════════════════════════════════════════════════════════════

/-- Transparent markets resolve adverse selection.

    An opaque exchange is a lemons market (Akerlof 1970): advertisers
    can't verify the auction mechanism is fair, so they discount bids.
    The participation set under opacity (where expected utility
    `belief_i * value_i - bid_i ≥ 0`) is a subset of the participation
    set under transparency (where `value_i - bid_i ≥ 0`), because
    `belief_i ≤ 1` implies `belief_i * value_i ≤ value_i`.

    More participants → more competition → higher welfare.

    Akerlof (1970), "The Market for 'Lemons'," QJE 84(3):488-500.
    DOI: https://doi.org/10.2307/1879431 -/
theorem transparent_market_resolves_adverse_selection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (value bid belief : ι → ℝ)
    (hvalue : ∀ i, 0 ≤ value i)
    (hbelief1 : ∀ i, belief i ≤ 1) :
    (Finset.univ.filter (fun i => 0 ≤ belief i * value i - bid i)) ⊆
      (Finset.univ.filter (fun i => 0 ≤ value i - bid i)) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hmul_le : belief i * value i ≤ value i := by
    nlinarith [hbelief1 i, hvalue i]
  nlinarith

/-- Competitive exchanges drive fees to marginal cost.

    With portable positions (market-position.json) and switching cost ε,
    no exchange can profitably charge more than marginal cost + ε because
    advertisers switch to the cheapest exchange. In any equilibrium where
    all fees satisfy the switching-cost bound, no fee exceeds the bound.

    Bertrand (1883); Tirole, Theory of Industrial Organization, Ch. 5. -/
theorem competitive_exchanges_bertrand_fees
    (K : ℕ) (marginal_cost : ℝ) (epsilon : ℝ) (hε : 0 < epsilon)
    (fees : Fin K → ℝ)
    (hswitch : ∀ k, fees k ≤ marginal_cost + epsilon) :
    ¬ ∃ k, marginal_cost + epsilon < fees k := by
  intro h
  rcases h with ⟨k, hk⟩
  exact not_lt_of_ge (hswitch k) hk

-- ════════════════════════════════════════════════════════════
-- 2026-03-09: Set It and Forget It
-- https://june.kim/set-it-and-forget-it
-- "Sigma is learnable from conversion data."
--
-- DONE — proved via compactness (IsCompact.exists_isMaxOn).
-- ════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false in
/-- An optimal sigma exists for each advertiser when utility is continuous
    on a compact interval. Sigma can be learned from conversion data
    without the advertiser setting it manually.

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
