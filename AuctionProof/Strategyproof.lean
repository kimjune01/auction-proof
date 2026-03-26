import AuctionProof.Auction
import AuctionProof.Axioms
import AuctionProof.Efficiency
import AuctionProof.OpenGame

/-!
# Strategyproofness of VCG on Power Diagram Allocation

## Main result

Under VCG payments (Clarke pivot), truthful reporting is a weakly dominant
strategy: no player can improve their utility by misreporting their bid,
center, or sigma.

## Proof structure

Three lemmas compose into the main theorem:

1. **Decomposition** (`playerUtility_decomp`): Player i's utility equals
   total welfare minus a "constant" term:
     `utility_i(x) = pointwiseWelfare(x) - welfareOthersWithout(i, x)`
   Proved by case analysis on whether i wins.

2. **Invariance** (`welfareOthersWithout_invariant`): The "constant" term
   does not depend on i's report. It is computed by re-optimizing over
   ι \ {i}, so i's report is irrelevant.

3. **Optimality** (`winner_maximizes_welfare`, from Efficiency.lean):
   Under truthful reporting, the winner at each x has the highest value.

Combining: maximizing utility = maximizing pointwiseWelfare (by 1 + 2),
and truthful reporting maximizes pointwiseWelfare (by 3). QED.

## Hedges connection

The strategyproofness theorem is exactly the `bestResponse` condition of
`vcgOpenGame` from OpenGame.lean. We prove this connection as
`vcg_is_nash_equilibrium`, which shows the VCG auction satisfies Nash
equilibrium in the compositional game theory framework.

## References

- Vickrey (1961), "Counterspeculation, Auctions, and Competitive Sealed
  Tenders," J. Finance 16(1):8-37. Thm 1.
  DOI: https://doi.org/10.2307/2977633
- Clarke (1971), "Multipart Pricing of Public Goods," Public Choice
  11(1):17-33. §3.
  DOI: https://doi.org/10.1007/BF01726210
- Groves (1973), "Incentives in Teams," Econometrica 41(4):617-631. Thm 2.
  DOI: https://doi.org/10.2307/1914085
- Ghani, Hedges, Winschel & Zahn (2018), "Compositional Game Theory,"
  Proc. LiCS. Thm 4.3.
  arXiv: 1603.04641
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- TIER 3: Truthful report construction
-- ============================================================

/-- Construct the truthful report from a player's private valuation. -/
def truthfulReport (v : Valuation E) : Report E where
  center := v.center
  sigma := v.trueSigma
  bid := v.trueValue
  sigma_pos := v.sigma_pos
  bid_pos := v.value_pos

/-- A truthful report satisfies `isTruthful`. -/
theorem truthfulReport_isTruthful (v : Valuation E) :
    isTruthful (truthfulReport v) v := ⟨rfl, rfl, rfl⟩

-- ============================================================
-- LEMMA 1: Utility decomposition
-- ============================================================

/-- Player i's utility decomposes as total welfare minus a constant:

      utility_i(x) = pointwiseWelfare(x) - welfareOthersWithout(i, x)

    This holds regardless of whether i wins or loses. The proof is a
    case split on `winner auc x = i`:

    - If i wins: utility = trueVal_i - (W_without - 0) = trueVal_i - W_without
      = pointwiseWelfare - W_without. ✓
    - If i loses: utility = 0 - (W_without - trueVal_winner) = trueVal_winner - W_without
      = pointwiseWelfare - W_without. ✓

    Our composition. Not a published theorem — this is the standard VCG
    utility decomposition applied to our specific definitions. -/
theorem playerUtility_decomp (auc : Auction ι E) (i : ι) (x : E) :
    playerUtility auc i x =
      pointwiseWelfare auc x - welfareOthersWithout auc i x := by
  unfold playerUtility utility vcgPayment welfareOthersWith welfareOthersAt pointwiseWelfare
  split_ifs with h
  · -- Case: winner auc x = i
    rw [h]; ring
  · -- Case: winner auc x ≠ i
    ring

-- ============================================================
-- LEMMA 2: Payment invariance under own-report change
-- ============================================================

/-- If two scoring functions agree on all elements of a list, argmax gives
    the same result.

    Uses `List.argmax_eq_some_iff` from Mathlib (Data.List.MinMax), which
    characterizes argmax as the element that dominates all others and has
    the smallest index among ties.

    Standard list theory — no economic content. -/
private theorem List.argmax_congr' {α : Type*} {β : Type*}
    [DecidableEq α] [LinearOrder β]
    {f g : α → β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    l.argmax f = l.argmax g := by
  cases hl : l.argmax f with
  | none =>
    rw [List.argmax_eq_none] at hl; subst hl; rfl
  | some m =>
    symm; rw [List.argmax_eq_some_iff]
    rw [List.argmax_eq_some_iff] at hl
    obtain ⟨hml, hmax, hidx⟩ := hl
    exact ⟨hml, fun a ha => by rw [← h a ha, ← h m hml]; exact hmax a ha,
           fun a ha hle => hidx a ha (by rw [← h m hml, ← h a ha] at hle; exact hle)⟩

/-- `winnerOnFinset` depends only on the scores of players in the player set.
    If two auctions agree on scores for all players in the set, the restricted
    winner is the same.

    Our composition — not a published result. Connects `Function.update_of_ne`
    (Lean core) with `List.argmax_congr'` (above). -/
private theorem winnerOnFinset_congr (players : Finset ι) (hplayers : players.Nonempty)
    (auc auc' : Auction ι E) (x : E)
    (hscore : ∀ j ∈ players, score (auc'.report j) x = score (auc.report j) x) :
    winnerOnFinset players hplayers auc' x = winnerOnFinset players hplayers auc x := by
  unfold winnerOnFinset
  dsimp only
  have harg : players.toList.argmax (fun j => score (auc'.report j) x) =
              players.toList.argmax (fun j => score (auc.report j) x) :=
    List.argmax_congr' (fun a ha => hscore a (Finset.mem_toList.mp ha))
  split
  · next w hw =>
    split
    · next w' hw' =>
      exact Option.some.inj (hw.symm.trans (harg.trans hw'))
    · next hw' =>
      exact absurd (List.argmax_eq_none.mp hw') (Finset.Nonempty.toList_ne_nil hplayers)
  · next hw =>
    exact absurd (List.argmax_eq_none.mp hw) (Finset.Nonempty.toList_ne_nil hplayers)

/-- Changing player i's report does not affect the counterfactual welfare
    computed without i.

    `welfareOthersWithout` re-optimizes over `Finset.univ.erase i`, which
    excludes i. The computation uses `score (auc.report j) x` for j ≠ i,
    and `trueVal (auc.valuation w) x` for the restricted winner w ≠ i.
    Since `Auction.withReport` only changes i's report (via `Function.update`)
    and leaves valuations unchanged, neither the restricted winner nor its
    welfare value changes.

    Vickrey (1961), Clarke (1971), Groves (1973): the VCG payment for i
    depends only on others' reports, not on i's own report. -/
theorem welfareOthersWithout_invariant
    (auc : Auction ι E) (i : ι) (r' : Report E) (x : E) :
    welfareOthersWithout (auc.withReport i r') i x =
      welfareOthersWithout auc i x := by
  unfold welfareOthersWithout
  split
  · next h =>
    -- The restricted winner is the same because scores agree on univ.erase i
    have hw : winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x =
              winnerOnFinset (Finset.univ.erase i) h auc x := by
      apply winnerOnFinset_congr
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      -- (auc.withReport i r').report j = Function.update auc.report i r' j = auc.report j
      show score ((Function.update auc.report i r') j) x = score (auc.report j) x
      rw [Function.update_of_ne hji]
    -- After rewriting the winner, welfareOthersAt is the same because
    -- (auc.withReport i r').valuation = auc.valuation (definitional)
    rw [hw]
    rfl
  · rfl

-- ============================================================
-- MAIN THEOREM: Strategyproofness
-- ============================================================

/-- **VCG is strategyproof**: truthful bidding is a weakly dominant strategy.

    For any deviation r' that player i might submit, their utility under
    truthful reporting (when all players are truthful) is at least as high
    as under the deviation.

    **Proof**: By decomposition (Lemma 1), utility = pointwiseWelfare - C.
    By invariance (Lemma 2), C is the same under both profiles. So it
    suffices to show pointwiseWelfare is higher under truthful reporting.
    By `winner_maximizes_welfare` (Efficiency.lean), the truthful winner
    achieves the maximum trueVal at every point. Any deviation can only
    pick a winner with equal or lower trueVal.

    Vickrey (1961), Thm 1; Clarke (1971), §3; Groves (1973), Thm 2.
    DOI: https://doi.org/10.2307/2977633 -/
theorem vcg_strategyproof
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (htruth : allTruthful auc) :
    playerUtility auc i x ≥
      playerUtility (auc.withReport i r') i x := by
  rw [playerUtility_decomp, playerUtility_decomp]
  rw [welfareOthersWithout_invariant auc i r' x]
  -- Goal: pointwiseWelfare auc x - C ≥ pointwiseWelfare (auc.withReport i r') x - C
  -- Reduces to: pointwiseWelfare auc x ≥ pointwiseWelfare (auc.withReport i r') x
  suffices h : pointwiseWelfare auc x ≥
              pointwiseWelfare (auc.withReport i r') x by linarith
  -- pointwiseWelfare auc x = trueVal(winner under truthful) = max of all trueVals
  -- pointwiseWelfare auc' x = trueVal(winner under deviation) ≤ max of all trueVals
  -- Note: (auc.withReport i r').valuation = auc.valuation (definitional)
  unfold pointwiseWelfare
  exact winner_maximizes_welfare auc x htruth _

-- ============================================================
-- HEDGES CONNECTION: VCG satisfies Nash equilibrium
-- ============================================================

/-- The VCG auction satisfies the Nash equilibrium condition of the
    compositional game theory framework (OpenGame.lean).

    Under truthful reporting, `vcgOpenGame.bestResponse` holds: no player
    can improve their utility by deviating. This is exactly
    `vcg_strategyproof`.

    The result holds for any continuation `k : ι → ℝ` because the VCG
    auction's best-response condition is self-contained — it does not
    depend on downstream games. This is what makes VCG composable:
    strategyproofness is a local property that survives composition.

    Connects: Vickrey-Clarke-Groves (equilibrium content) with
    Ghani, Hedges et al. (2018) (compositional framework). -/
theorem vcg_is_nash_equilibrium
    (auc : Auction ι E) (x : E) (k : ι → ℝ)
    (htruth : allTruthful auc) :
    vcgOpenGame.isNashEquilibrium x k auc := by
  -- vcgOpenGame.bestResponse x k auc unfolds to:
  -- ∀ i r', playerUtility auc i x ≥ playerUtility (auc.withReport i r') i x
  show ∀ (i : ι) (r' : Report E),
    playerUtility auc i x ≥ playerUtility (auc.withReport i r') i x
  exact fun i r' => vcg_strategyproof auc i x r' htruth

/-- Green & Laffont (1977): VCG is the *only* efficient dominant-strategy
    incentive-compatible mechanism on unrestricted domains.

    Stated as a placeholder to document the uniqueness result in the proof
    chain. Full formalization requires domain-restriction machinery.

    Green & Laffont (1977), Thm 1. -/
theorem vcg_is_unique_efficient_dsic : True := trivial

end
