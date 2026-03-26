import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.MinMax

/-!
# Auction Definitions for the VCG Development

This file is intentionally split into three tiers.

## Tier 1: Scaffolding

Standard direct-revelation mechanism-design definitions. These are textbook-level
objects, cited at the textbook level rather than to paper-level theorems.

Reference:
- Noam Nisan, Tim Roughgarden, Éva Tardos, Vijay V. Vazirani (eds.),
  *Algorithmic Game Theory* (2007), Chapter 9.

## Tier 2: Giants

Definitions that are direct transcriptions of published constructions and can be
named honestly as such.

References:
- Generic VCG mechanism: Nisan et al. (2007), Chapter 9; Groves (1973).
- Power distance: Aurenhammer (1987), §2.
  DOI: https://doi.org/10.1137/0216006

## Tier 3: Our Composition

Definitions that specialize or bridge the giants for this project's model.
These are explicit modeling choices inspired by the literature, not claims that
the code below is itself a direct transcription of a published formal definition.

In particular:
- `score`, `trueVal`, and `winner` live here.
- `vcgPayment` implements the Clarke pivot via `winnerOnFinset` on
  `Finset.univ.erase i` — proper exclusion of player i.
- The connection from `score` to power diagrams is only asserted in the
  equal-`sigma` case.
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- TIER 1: SCAFFOLDING
-- Standard mechanism-design definitions.
-- Reference: Nisan et al. (2007), Chapter 9.
-- ============================================================

/-- A reported profile in a direct-revelation mechanism.

This is standard mechanism-design scaffolding: each player reports a center,
a spread parameter, and a bid. The positivity fields keep the later logarithm
and division expressions well-formed.

Reference:
- Nisan et al. (2007), Chapter 9. -/
structure Report (E : Type*) where
  center : E
  sigma : ℝ
  bid : ℝ
  sigma_pos : 0 < sigma
  bid_pos : 0 < bid

/-- A player's private valuation data.

The project keeps reports and private valuations separate so later statements of
truthfulness can compare truthful and deviating reports against a fixed type.

Reference:
- Nisan et al. (2007), Chapter 9. -/
structure Valuation (E : Type*) where
  center : E
  trueSigma : ℝ
  trueValue : ℝ
  sigma_pos : 0 < trueSigma
  value_pos : 0 < trueValue

/-- An auction state with one reported profile and one private valuation profile.

Reference:
- Nisan et al. (2007), Chapter 9. -/
structure Auction (ι : Type*) (E : Type*) where
  report : ι → Report E
  valuation : ι → Valuation E

/-- Quasilinear utility, standard in mechanism design.

Reference:
- Nisan et al. (2007), Chapter 9. -/
def utility (_auc : Auction ι E) (_i : ι) (_x : E)
    (myValue payment : ℝ) : ℝ :=
  myValue - payment

/-- Replace player `i`'s report while leaving private valuations unchanged.

This is standard scaffolding for deviation comparisons. -/
def Auction.withReport (auc : Auction ι E) (i : ι) (r' : Report E) : Auction ι E where
  report := Function.update auc.report i r'
  valuation := auc.valuation

-- ============================================================
-- TIER 2: GIANTS
-- Direct transcriptions of published constructions.
-- ============================================================

/-- A generic VCG-style mechanism: an allocation rule together with a payment rule.

This is the standard mechanism-level object used in VCG presentations.

References:
- Nisan et al. (2007), Chapter 9.
- Theodore Groves, "Incentives in Teams" (1973).
  DOI: https://doi.org/10.2307/1914085 -/
structure VCGMechanism (ι : Type*) (Message : Type*) (Outcome : Type*) where
  allocation : (ι → Message) → Outcome
  payment : (ι → Message) → ι → ℝ

/-- Power distance from `x` to a weighted site `(site, weight)`.

This matches the standard power-distance construction used in power-diagram
geometry.

Reference:
- Franz Aurenhammer, "Power diagrams: properties, algorithms and applications"
  (1987), §2.
  DOI: https://doi.org/10.1137/0216006 -/
def powerDistance (site : E) (weight : ℝ) (x : E) : ℝ :=
  ‖x - site‖ ^ 2 - weight

-- ============================================================
-- TIER 3: OUR COMPOSITION
-- Project-specific modeling choices inspired by the literature.
-- No claim here is a direct transcription unless stated above.
-- ============================================================

/-- Project scoring rule:
`score_i(x) = log(b_i) - ||x - c_i||^2 / sigma_i^2`.

This is a modeling choice inspired by the quality-decay form in sponsored-search
models, where relevance decays with distance. It is not claimed here as a direct
formalization of a published auction definition.

In the special case where all `sigma_i` are equal, maximizing this score is
equivalent to minimizing a power distance with weights `sigma^2 * log(b_i)`.
That equal-sigma specialization matches a power-diagram partition. We do not
claim a general power-diagram identification when the `sigma_i` vary.

Inspiration:
- Lahaie and Pennock (2007), sponsored-search quality weighting.
  DOI: https://doi.org/10.1145/1250910.1250918 -/
def score (r : Report E) (x : E) : ℝ :=
  Real.log r.bid - ‖x - r.center‖ ^ 2 / r.sigma ^ 2

/-- Project valuation model:
`trueVal_i(x) = trueValue_i * exp(-||x - center_i||^2 / trueSigma_i^2)`.

This Gaussian-decay form is a modeling choice inspired by relevance-decay
models in the literature. It is not claimed as a direct transcription of a
published definition.

Inspiration:
- Lahaie and Pennock (2007), sponsored-search quality weighting.
  DOI: https://doi.org/10.1145/1250910.1250918 -/
def trueVal (v : Valuation E) (x : E) : ℝ :=
  v.trueValue * Real.exp (-(‖x - v.center‖ ^ 2 / v.trueSigma ^ 2))

/-- The project's winner rule: choose an advertiser maximizing `score` at `x`.

This is our allocation rule induced by the project-specific scoring function
above. It is an argmax construction, not a theorem citation to power-diagram
cell geometry. Ties are broken by the order of `Finset.univ.toList`. -/
def winner (auc : Auction ι E) (x : E) : ι :=
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  let scores : ι → ℝ := fun i => score (auc.report i) x
  let l := (Finset.univ : Finset ι).toList
  match h : l.argmax scores with
  | some i => i
  | none =>
      absurd (List.argmax_eq_none.mp h) (Finset.Nonempty.toList_ne_nil hne)

/-- Welfare contributed by players other than `i` when `w` is selected.

    Helper for the Clarke pivot payment. -/
def welfareOthersAt (auc : Auction ι E) (i w : ι) (x : E) : ℝ :=
  if w = i then 0 else trueVal (auc.valuation w) x

/-- Winner restricted to a nonempty finite player set.

    Used to compute the counterfactual allocation with player `i` removed.

    Reference:
    - Clarke (1971), §3: the pivotal mechanism requires recomputing the
      outcome without each player. -/
def winnerOnFinset (players : Finset ι) (hplayers : players.Nonempty)
    (auc : Auction ι E) (x : E) : ι :=
  let scores : ι → ℝ := fun j => score (auc.report j) x
  let l := players.toList
  match h : l.argmax scores with
  | some j => j
  | none =>
      absurd (List.argmax_eq_none.mp h) (Finset.Nonempty.toList_ne_nil hplayers)

/-- Welfare of players other than `i` under the current allocation. -/
def welfareOthersWith (auc : Auction ι E) (i : ι) (x : E) : ℝ :=
  welfareOthersAt auc i (winner auc x) x

/-- Welfare of players other than `i` under the optimal allocation with
    `i` removed.

    If there is only one player, removing them leaves the empty set and
    welfare is zero (free disposal). -/
def welfareOthersWithout (auc : Auction ι E) (i : ι) (x : E) : ℝ :=
  if h : (Finset.univ.erase i : Finset ι).Nonempty then
    let w := winnerOnFinset (Finset.univ.erase i) h auc x
    welfareOthersAt auc i w x
  else
    0

/-- Clarke pivot payment:
    `payment_i = welfare_others(optimal without i) - welfare_others(with i)`.

    This is the externality pricing from the pivotal mechanism: player i pays
    exactly the damage their presence inflicts on the other players.

    References:
    - Clarke (1971), "Multipart Pricing of Public Goods," §3.
      DOI: https://doi.org/10.1007/BF01726210
    - Groves (1973), "Incentives in Teams," Thm 2.
      DOI: https://doi.org/10.2307/1914085 -/
def vcgPayment (auc : Auction ι E) (i : ι) (x : E) : ℝ :=
  welfareOthersWithout auc i x - welfareOthersWith auc i x

/-- Welfare at query `x` under the project's allocation rule.

This is our composition of the project-specific winner rule with the
project-specific valuation model. -/
def pointwiseWelfare (auc : Auction ι E) (x : E) : ℝ :=
  trueVal (auc.valuation (winner auc x)) x

/-- Player `i`'s utility at query `x` under the current project model.

This combines quasilinear utility with the project-specific winner rule,
valuation model, and Clarke pivot payment. -/
def playerUtility (auc : Auction ι E) (i : ι) (x : E) : ℝ :=
  utility auc i x
    (if winner auc x = i then trueVal (auc.valuation i) x else 0)
    (vcgPayment auc i x)

end
