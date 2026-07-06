import AuctionProof.Auction
import AuctionProof.Efficiency

/-!
# The allocation is a power diagram — including variable sigma

The blog post (https://june.kim/power-diagrams-ad-auctions) claims the
scoring rule `log(b) - ‖x-c‖²/σ²` partitions embedding space into a power
diagram. The docstring on `score` was more careful: the in-space power-diagram
identification only holds when all sigmas are equal. This file proves both
halves and closes the gap for variable sigma:

1. **Equal sigma** (`score_le_iff_powerDist_le`): score comparison is
   power-distance comparison in `E` with sites `c_i` and weights
   `σ² · log(b_i)`. Bisectors are affine (`score_sub_affine`), i.e.
   hyperplanes — the classical power diagram.

2. **Variable sigma** (`liftedPowerDist_paraboloid`,
   `score_le_iff_liftedPowerDist_ge`): in general the in-space cells are
   bounded by spheres, not hyperplanes. But the diagram is exactly a power
   diagram **one dimension up**: lift each query to the paraboloid
   `(x, ‖x‖²) ∈ E × ℝ`, place site `i` at `(σᵢ⁻² • cᵢ, -σᵢ⁻²/2)` with a
   matching weight, and score comparison in `E` becomes power-distance
   comparison in `E × ℝ`. The identity is exact:

   `liftedPowerDist i (x, ‖x‖²) = ‖x‖² + ‖x‖⁴ - score_i(x)`

   with the `‖x‖² + ‖x‖⁴` term independent of `i`, so the argmax of score is
   the argmin of lifted power distance (`winner_minimizes_liftedPowerDist`).

   The lifted product space is handled coordinatewise (the `E`-component and
   the `ℝ`-component appear as separate arguments), which is the L2 product
   structure without needing a product-space instance.

Reference:
- Aurenhammer (1987), "Power diagrams: properties, algorithms and
  applications," SIAM J. Comput. 16(1):78-96, §4: diagrams of quadratic
  distance functions are power diagrams in one dimension higher.
  DOI: https://doi.org/10.1137/0216006
-/

noncomputable section

open Real RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- Power distance
-- ============================================================

/-- Power distance (Laguerre distance) from `x` to a site with center `p`
    and weight `w`: `pow(x) = ‖x - p‖² - w`.

    Reference: Aurenhammer (1987), §1. -/
def powerDist (p : E) (w : ℝ) (x : E) : ℝ :=
  ‖x - p‖ ^ 2 - w

-- ============================================================
-- Part 1: equal sigma — power diagram in E itself
-- ============================================================

/-- With weight `σ² · log(b)`, the power distance to an advertiser's site is
    `-σ²` times their score. Monotone-decreasing transform: argmax score =
    argmin power distance. -/
theorem powerDist_eq_neg_sigma_sq_mul_score (r : Report E) (x : E) :
    powerDist r.center (r.sigma ^ 2 * Real.log r.bid) x
      = -(r.sigma ^ 2 * score r x) := by
  have hσ : r.sigma ≠ 0 := ne_of_gt r.sigma_pos
  unfold powerDist score
  field_simp
  ring

/-- **Equal-sigma power diagram.** When two advertisers share the same sigma,
    the score comparison at any query point is exactly a power-distance
    comparison with sites at the centers and weights `σ² · log(bid)`.

    This is the in-space power-diagram identification promised in the `score`
    docstring, now a theorem. -/
theorem score_le_iff_powerDist_le (r s : Report E) (x : E)
    (h : r.sigma = s.sigma) :
    score r x ≤ score s x ↔
      powerDist s.center (s.sigma ^ 2 * Real.log s.bid) x ≤
        powerDist r.center (r.sigma ^ 2 * Real.log r.bid) x := by
  have hσ : 0 < s.sigma ^ 2 := pow_pos s.sigma_pos 2
  rw [powerDist_eq_neg_sigma_sq_mul_score, powerDist_eq_neg_sigma_sq_mul_score, h]
  constructor
  · intro hh
    have := mul_le_mul_of_nonneg_left hh (le_of_lt hσ)
    linarith
  · intro hh
    by_contra hlt
    push_neg at hlt
    have := mul_lt_mul_of_pos_left hlt hσ
    linarith

/-- **Equal-sigma bisectors are hyperplanes.** The score difference between
    two equal-sigma advertisers is an affine function of the query point:
    linear part `(2/σ²)⟪x, c_r - c_s⟫`, constant part determined by the
    centers' norms and the bids. The bisector `{x | score r x = score s x}`
    is therefore a hyperplane (when the centers differ). -/
theorem score_sub_affine (r s : Report E) (x : E) (h : r.sigma = s.sigma) :
    score r x - score s x =
      (2 / s.sigma ^ 2) * inner ℝ x (r.center - s.center) +
        ((‖s.center‖ ^ 2 - ‖r.center‖ ^ 2) / s.sigma ^ 2 +
          (Real.log r.bid - Real.log s.bid)) := by
  have hσ : s.sigma ≠ 0 := ne_of_gt s.sigma_pos
  unfold score
  rw [h, norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
  field_simp
  ring

-- ============================================================
-- Part 2: variable sigma — power diagram in E × ℝ
-- (Aurenhammer lift to the paraboloid)
-- ============================================================

/-- Inverse variance `σ⁻²`: the site's "steepness" in the lift. -/
def invVar (r : Report E) : ℝ := (r.sigma ^ 2)⁻¹

theorem invVar_pos (r : Report E) : 0 < invVar r :=
  inv_pos.mpr (pow_pos r.sigma_pos 2)

/-- `E`-component of the lifted site: `σ⁻² • c`. -/
def liftSiteCenter (r : Report E) : E := invVar r • r.center

/-- `ℝ`-component of the lifted site: `-σ⁻²/2`. -/
def liftSiteHeight (r : Report E) : ℝ := -invVar r / 2

/-- Weight of the lifted site, chosen so the power distance on the
    paraboloid reproduces the score exactly (up to the common
    `‖x‖² + ‖x‖⁴` term). -/
def liftSiteWeight (r : Report E) : ℝ :=
  invVar r ^ 2 * ‖r.center‖ ^ 2 + invVar r ^ 2 / 4
    - invVar r * ‖r.center‖ ^ 2 + Real.log r.bid

/-- Power distance in the lifted space `E × ℝ`, written coordinatewise:
    `‖x - u‖² + (y - s)² - w` for a lifted point `(x, y)` and lifted site
    `(u, s)` with weight `w`. This is the L2 product structure. -/
def liftedPowerDist (r : Report E) (x : E) (y : ℝ) : ℝ :=
  ‖x - liftSiteCenter r‖ ^ 2 + (y - liftSiteHeight r) ^ 2 - liftSiteWeight r

/-- **The Aurenhammer lift identity.** On the paraboloid `y = ‖x‖²`, the
    lifted power distance to advertiser `r`'s site equals
    `‖x‖² + ‖x‖⁴ - score r x`. The first two terms don't depend on `r`, so
    comparing scores in `E` is comparing power distances in `E × ℝ` — for
    arbitrary, heterogeneous sigmas.

    Aurenhammer (1987), §4. -/
theorem liftedPowerDist_paraboloid (r : Report E) (x : E) :
    liftedPowerDist r x (‖x‖ ^ 2)
      = ‖x‖ ^ 2 + (‖x‖ ^ 2) ^ 2 - score r x := by
  have hm : 0 < invVar r := invVar_pos r
  have hexp : ‖x - liftSiteCenter r‖ ^ 2
      = ‖x‖ ^ 2 - 2 * (invVar r * inner ℝ x r.center)
        + invVar r ^ 2 * ‖r.center‖ ^ 2 := by
    unfold liftSiteCenter
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hm, mul_pow]
  have hscore : score r x
      = Real.log r.bid
        - (‖x‖ ^ 2 - 2 * inner ℝ x r.center + ‖r.center‖ ^ 2) * invVar r := by
    unfold score invVar
    rw [norm_sub_sq_real, div_eq_mul_inv]
  unfold liftedPowerDist liftSiteHeight liftSiteWeight
  rw [hexp, hscore]
  ring

/-- **Variable-sigma power diagram.** Score comparison in `E` is power-
    distance comparison in `E × ℝ` at the paraboloid lift — no equal-sigma
    hypothesis. Higher score means smaller lifted power distance. -/
theorem score_le_iff_liftedPowerDist_ge (r s : Report E) (x : E) :
    score r x ≤ score s x ↔
      liftedPowerDist s x (‖x‖ ^ 2) ≤ liftedPowerDist r x (‖x‖ ^ 2) := by
  rw [liftedPowerDist_paraboloid, liftedPowerDist_paraboloid]
  constructor <;> intro h <;> linarith

/-- The auction winner minimizes lifted power distance: the allocation rule
    **is** the power-diagram cell assignment in `E × ℝ`, for arbitrary
    sigmas. -/
theorem winner_minimizes_liftedPowerDist (auc : Auction ι E) (x : E) (j : ι) :
    liftedPowerDist (auc.report (winner auc x)) x (‖x‖ ^ 2) ≤
      liftedPowerDist (auc.report j) x (‖x‖ ^ 2) := by
  have hval := winner_maximizes_reportedVal auc x j
  have hpos : ∀ k : ι, 0 < reportedVal (auc.report k) x := by
    intro k
    unfold reportedVal
    exact mul_pos (auc.report k).bid_pos (Real.exp_pos _)
  have hscore : score (auc.report j) x ≤ score (auc.report (winner auc x)) x := by
    rw [score_eq_log_reportedVal, score_eq_log_reportedVal]
    exact (Real.log_le_log_iff (hpos j) (hpos (winner auc x))).mpr hval
  exact (score_le_iff_liftedPowerDist_ge (auc.report j) (auc.report (winner auc x)) x).mp
    hscore

end
