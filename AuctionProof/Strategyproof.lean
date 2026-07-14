import AuctionProof.Auction
import AuctionProof.Axioms
import AuctionProof.Efficiency
import AuctionProof.OpenGame

/-!
# VCG is DSIC (Dominant Strategy Incentive Compatible)

## Main result

Under VCG payments (Clarke pivot with reported values), truthful reporting
is a **dominant strategy**: no player can improve their utility by
misreporting their bid, center, or sigma, **regardless of what others report**.

The hypothesis is `isTruthful (auc.report i) (auc.valuation i)` — only
player i needs to be truthful. Others can report anything.

## Proof structure

1. **Winner utility** (`playerUtility_of_winner`): when i wins,
   utility = trueVal_i - C where C = welfareOthersWithout.
2. **Loser utility** (`playerUtility_eq_zero_of_loser`): when i loses,
   utility = 0. (Because the restricted winner matches the full winner's
   reportedVal when the full winner ≠ i.)
3. **Win bound** (`welfareOthersWithout_le_trueVal_of_win`): when truthful
   i wins, C ≤ trueVal_i, so utility ≥ 0.
4. **Loss bound** (`trueVal_le_welfareOthersWithout_of_loss`): when truthful
   i loses, trueVal_i ≤ C.
5. **DSIC** (`vcg_dsic`): four-case analysis. In all cases, truthful utility
   ≥ deviated utility.

## References

- Vickrey (1961), Thm 1. DOI: https://doi.org/10.2307/2977633
- Clarke (1971), §3. DOI: https://doi.org/10.1007/BF01726210
- Groves (1973). DOI: https://doi.org/10.2307/1914085
- Ghani, Hedges, Winschel & Zahn (2018), Thm 4.3. arXiv: 1603.04641
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- ============================================================
-- Truthful report construction
-- ============================================================

def truthfulReport (v : Valuation E) : Report E where
  center := v.center
  sigma := v.trueSigma
  bid := v.trueValue
  sigma_pos := v.sigma_pos
  bid_pos := v.value_pos

theorem truthfulReport_isTruthful (v : Valuation E) :
    isTruthful (truthfulReport v) v := ⟨rfl, rfl, rfl⟩

-- ============================================================
-- Utility case analysis
-- ============================================================

theorem playerUtility_of_winner (auc : Auction ι E) (i : ι) (x : E)
    (hwin : winner auc x = i) :
    playerUtility auc i x =
      trueVal (auc.valuation i) x - welfareOthersWithout auc i x := by
  unfold playerUtility utility vcgPayment welfareOthersWith welfareOthersAt
  simp [hwin]

theorem playerUtility_of_loser (auc : Auction ι E) (i : ι) (x : E)
    (hlose : winner auc x ≠ i) :
    playerUtility auc i x =
      reportedVal (auc.report (winner auc x)) x - welfareOthersWithout auc i x := by
  unfold playerUtility utility vcgPayment welfareOthersWith welfareOthersAt
  simp [hlose]

-- ============================================================
-- Argmax helpers
-- ============================================================

theorem winnerOnFinset_mem (players : Finset ι) (hplayers : players.Nonempty)
    (auc : Auction ι E) (x : E) :
    winnerOnFinset players hplayers auc x ∈ players := by
  unfold winnerOnFinset; dsimp only
  split
  · next w hw =>
    have := List.argmax_eq_some_iff.mp hw
    exact Finset.mem_toList.mp this.1
  · next hw => exact absurd (List.argmax_eq_none.mp hw) (Finset.Nonempty.toList_ne_nil hplayers)

theorem winnerOnFinset_maximizes_reportedVal
    (players : Finset ι) (hplayers : players.Nonempty)
    (auc : Auction ι E) (x : E) (j : ι) (hj : j ∈ players) :
    reportedVal (auc.report (winnerOnFinset players hplayers auc x)) x ≥
      reportedVal (auc.report j) x := by
  unfold winnerOnFinset; dsimp only
  have hj_mem : j ∈ players.toList := Finset.mem_toList.mpr hj
  split
  · next w hw =>
    have hw_arg : w ∈ List.argmax (fun k => score (auc.report k) x) players.toList := by
      simp [hw]
    have hscore : score (auc.report j) x ≤ score (auc.report w) x :=
      List.le_of_mem_argmax hj_mem hw_arg
    have hlog : Real.log (reportedVal (auc.report j) x) ≤
        Real.log (reportedVal (auc.report w) x) := by
      simpa [score_eq_log_reportedVal] using hscore
    have hposj : 0 < reportedVal (auc.report j) x := by
      unfold reportedVal; exact mul_pos (auc.report j).bid_pos (Real.exp_pos _)
    have hposw : 0 < reportedVal (auc.report w) x := by
      unfold reportedVal; exact mul_pos (auc.report w).bid_pos (Real.exp_pos _)
    exact (Real.log_le_log_iff hposj hposw).mp hlog
  · next hw => exact absurd (List.argmax_eq_none.mp hw) (Finset.Nonempty.toList_ne_nil hplayers)

-- ============================================================
-- Payment invariance (DSIC version)
-- ============================================================

/-- Changing player i's report does not affect welfareOthersWithout.

    Vickrey (1961), Clarke (1971), Groves (1973): the VCG payment for i
    depends only on others' reports, not on i's own report. -/
theorem welfareOthersWithout_invariant
    (auc : Auction ι E) (i : ι) (r' : Report E) (x : E) :
    welfareOthersWithout (auc.withReport i r') i x =
      welfareOthersWithout auc i x := by
  unfold welfareOthersWithout
  split
  · next h =>
    have hwMem := winnerOnFinset_mem (Finset.univ.erase i) h auc x
    have hwDevMem := winnerOnFinset_mem (Finset.univ.erase i) h (auc.withReport i r') x
    have hwi : winnerOnFinset (Finset.univ.erase i) h auc x ≠ i :=
      Finset.ne_of_mem_erase hwMem
    have hwiDev : winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x ≠ i :=
      Finset.ne_of_mem_erase hwDevMem
    unfold welfareOthersAt
    rw [if_neg hwiDev, if_neg hwi]
    apply le_antisymm
    · have hmax := winnerOnFinset_maximizes_reportedVal (Finset.univ.erase i) h auc x
        (winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x) hwDevMem
      have hleft : reportedVal ((auc.withReport i r').report
          (winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x)) x =
          reportedVal (auc.report
          (winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x)) x := by
        change reportedVal ((Function.update auc.report i r')
          (winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x)) x =
          reportedVal (auc.report
          (winnerOnFinset (Finset.univ.erase i) h (auc.withReport i r') x)) x
        rw [Function.update_of_ne hwiDev]
      rw [hleft]; exact hmax
    · have hmax := winnerOnFinset_maximizes_reportedVal (Finset.univ.erase i) h
        (auc.withReport i r') x
        (winnerOnFinset (Finset.univ.erase i) h auc x) hwMem
      have hright : reportedVal ((auc.withReport i r').report
          (winnerOnFinset (Finset.univ.erase i) h auc x)) x =
          reportedVal (auc.report
          (winnerOnFinset (Finset.univ.erase i) h auc x)) x := by
        change reportedVal ((Function.update auc.report i r')
          (winnerOnFinset (Finset.univ.erase i) h auc x)) x =
          reportedVal (auc.report
          (winnerOnFinset (Finset.univ.erase i) h auc x)) x
        rw [Function.update_of_ne hwi]
      rw [hright] at hmax; exact hmax
  · rfl

-- ============================================================
-- DSIC helpers
-- ============================================================

private theorem welfareOthersWithout_eq_winner_reportedVal_of_loser
    (auc : Auction ι E) (i : ι) (x : E)
    (hlose : winner auc x ≠ i) :
    welfareOthersWithout auc i x =
      reportedVal (auc.report (winner auc x)) x := by
  unfold welfareOthersWithout
  have hne : (Finset.univ.erase i : Finset ι).Nonempty :=
    ⟨winner auc x, Finset.mem_erase.mpr ⟨hlose, Finset.mem_univ _⟩⟩
  rw [dif_pos hne]
  have hw_mem := winnerOnFinset_mem (Finset.univ.erase i) hne auc x
  have hwi : winnerOnFinset (Finset.univ.erase i) hne auc x ≠ i :=
    Finset.ne_of_mem_erase hw_mem
  unfold welfareOthersAt; rw [if_neg hwi]
  apply le_antisymm
  · exact winner_maximizes_reportedVal auc x _
  · exact winnerOnFinset_maximizes_reportedVal (Finset.univ.erase i) hne auc x
      (winner auc x) (Finset.mem_erase.mpr ⟨hlose, Finset.mem_univ _⟩)

private theorem playerUtility_eq_zero_of_loser
    (auc : Auction ι E) (i : ι) (x : E)
    (hlose : winner auc x ≠ i) :
    playerUtility auc i x = 0 := by
  rw [playerUtility_of_loser (auc := auc) (i := i) (x := x) hlose]
  rw [welfareOthersWithout_eq_winner_reportedVal_of_loser (auc := auc) (i := i) (x := x) hlose]
  ring

private theorem welfareOthersWithout_le_trueVal_of_win
    (auc : Auction ι E) (i : ι) (x : E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hwin : winner auc x = i) :
    welfareOthersWithout auc i x ≤ trueVal (auc.valuation i) x := by
  unfold welfareOthersWithout
  split
  · next h =>
    have hw_mem := winnerOnFinset_mem (Finset.univ.erase i) h auc x
    have hwi : winnerOnFinset (Finset.univ.erase i) h auc x ≠ i :=
      Finset.ne_of_mem_erase hw_mem
    unfold welfareOthersAt; rw [if_neg hwi]
    calc reportedVal (auc.report (winnerOnFinset (Finset.univ.erase i) h auc x)) x
        ≤ reportedVal (auc.report (winner auc x)) x :=
          winner_maximizes_reportedVal auc x _
      _ = reportedVal (auc.report i) x := by rw [hwin]
      _ = trueVal (auc.valuation i) x :=
          reportedVal_eq_trueVal_of_truthful _ _ x hi
  · exact le_of_lt (by unfold trueVal; exact mul_pos (auc.valuation i).value_pos (Real.exp_pos _))

private theorem trueVal_le_welfareOthersWithout_of_loss
    (auc : Auction ι E) (i : ι) (x : E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hlose : winner auc x ≠ i) :
    trueVal (auc.valuation i) x ≤ welfareOthersWithout auc i x := by
  rw [welfareOthersWithout_eq_winner_reportedVal_of_loser (auc := auc) (i := i) (x := x) hlose]
  calc
    trueVal (auc.valuation i) x = reportedVal (auc.report i) x := by
      symm; exact reportedVal_eq_trueVal_of_truthful _ _ x hi
    _ ≤ reportedVal (auc.report (winner auc x)) x :=
      winner_maximizes_reportedVal auc x i

/-- **Losers pay zero.** A player who does not win pays nothing: removing a
    loser leaves the allocation among the others unchanged, so their Clarke
    externality is zero. Paired with `vcgPayment_common_center_second_price`
    (the winner pays the highest competing bid) this completes the Vickrey
    picture at a keyword point — losers pay 0, the winner pays the second
    price — making the whole payment rule explicit, not just the winner's. -/
theorem vcgPayment_eq_zero_of_loser (auc : Auction ι E) (i : ι) (x : E)
    (hlose : winner auc x ≠ i) :
    vcgPayment auc i x = 0 := by
  unfold vcgPayment welfareOthersWith welfareOthersAt
  rw [if_neg hlose,
    welfareOthersWithout_eq_winner_reportedVal_of_loser
      (auc := auc) (i := i) (x := x) hlose]
  ring

-- ============================================================
-- MAIN THEOREM: DSIC
-- ============================================================

/-- **VCG is DSIC**: truthful bidding is a dominant strategy.

    For any deviation r' that player i might submit, their utility under
    truthful reporting is at least as high — **regardless of what others
    report**. Only player i needs to be truthful.

    Vickrey (1961); Clarke (1971), §3; Groves (1973).
    DOI: https://doi.org/10.2307/2977633 -/
theorem vcg_dsic
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (hi : isTruthful (auc.report i) (auc.valuation i)) :
    playerUtility auc i x ≥
      playerUtility (auc.withReport i r') i x := by
  by_cases hTruth : winner auc x = i <;> by_cases hDev : winner (auc.withReport i r') x = i
  · -- Both win → same utility
    rw [playerUtility_of_winner (auc := auc) (i := i) (x := x) hTruth]
    rw [playerUtility_of_winner (auc := auc.withReport i r') (i := i) (x := x) hDev]
    rw [welfareOthersWithout_invariant]; rfl
  · -- Truth wins, dev loses → trueVal_i - C ≥ 0
    rw [playerUtility_of_winner (auc := auc) (i := i) (x := x) hTruth]
    rw [playerUtility_eq_zero_of_loser (auc := auc.withReport i r') (i := i) (x := x) hDev]
    exact sub_nonneg.mpr (welfareOthersWithout_le_trueVal_of_win auc i x hi hTruth)
  · -- Truth loses, dev wins → 0 ≥ trueVal_i - C
    rw [playerUtility_eq_zero_of_loser (auc := auc) (i := i) (x := x) hTruth]
    rw [playerUtility_of_winner (auc := auc.withReport i r') (i := i) (x := x) hDev]
    rw [welfareOthersWithout_invariant]
    change trueVal (auc.valuation i) x - welfareOthersWithout auc i x ≤ 0
    exact sub_nonpos.mpr (trueVal_le_welfareOthersWithout_of_loss auc i x hi hTruth)
  · -- Both lose → 0 = 0
    rw [playerUtility_eq_zero_of_loser (auc := auc) (i := i) (x := x) hTruth]
    rw [playerUtility_eq_zero_of_loser (auc := auc.withReport i r') (i := i) (x := x) hDev]

-- ============================================================
-- STRICT DSIC UNDER COMPETITION
-- ============================================================

/-- If truthful reporting wins a query, a deviation loses it, and the
    truthful value strictly clears the best rival welfare, the deviation
    strictly lowers utility at that query. -/
theorem vcg_strict_at_contested_point
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (hTruth : winner auc x = i)
    (hDev : winner (auc.withReport i r') x ≠ i)
    (hmargin : welfareOthersWithout auc i x < trueVal (auc.valuation i) x) :
    playerUtility (auc.withReport i r') i x < playerUtility auc i x := by
  rw [playerUtility_of_winner (auc := auc) (i := i) (x := x) hTruth]
  rw [playerUtility_eq_zero_of_loser
    (auc := auc.withReport i r') (i := i) (x := x) hDev]
  exact sub_pos.mpr hmargin

/-- At a non-tie query, any deviation that changes whether player `i` wins is
    strictly worse than a truthful report. -/
theorem vcg_strict_of_allocation_change
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hchange : ¬ (winner (auc.withReport i r') x = i ↔ winner auc x = i))
    (hmargin : trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x) :
    playerUtility (auc.withReport i r') i x < playerUtility auc i x := by
  by_cases hTruth : winner auc x = i
  · have hDev : winner (auc.withReport i r') x ≠ i := by
      intro hDev
      exact hchange ⟨fun _ => hTruth, fun _ => hDev⟩
    apply vcg_strict_at_contested_point auc i x r' hTruth hDev
    have hle := welfareOthersWithout_le_trueVal_of_win auc i x hi hTruth
    exact lt_of_le_of_ne hle (Ne.symm hmargin)
  · have hDev : winner (auc.withReport i r') x = i := by
      by_contra hDev
      exact hchange ⟨fun h => (hDev h).elim, fun h => (hTruth h).elim⟩
    rw [playerUtility_eq_zero_of_loser (auc := auc) (i := i) (x := x) hTruth]
    rw [playerUtility_of_winner
      (auc := auc.withReport i r') (i := i) (x := x) hDev]
    rw [welfareOthersWithout_invariant]
    apply sub_neg.mpr
    have hle := trueVal_le_welfareOthersWithout_of_loss auc i x hi hTruth
    exact lt_of_le_of_ne hle hmargin

/-- Expected utility under a query measure. -/
def expectedPlayerUtility (auc : Auction ι E) (i : ι) (μ : QueryMeasure E) : ℝ :=
  μ.integrate (playerUtility auc i)

/-- A strict utility loss at a positive-weight contested query lifts to a
    strict expected-utility loss. -/
theorem vcg_strict_expected_at_contested_point
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E) (μ : QueryMeasure E)
    [QueryMeasure.PositiveAt μ x]
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hTruth : winner auc x = i)
    (hDev : winner (auc.withReport i r') x ≠ i)
    (hmargin : welfareOthersWithout auc i x < trueVal (auc.valuation i) x) :
    expectedPlayerUtility (auc.withReport i r') i μ < expectedPlayerUtility auc i μ := by
  exact QueryMeasure.PositiveAt.integral_lt_of_pointwise_lt_at
    (self := inferInstance)
    (playerUtility (auc.withReport i r') i) (playerUtility auc i)
    (fun y => vcg_dsic auc i y r' hi)
    (vcg_strict_at_contested_point auc i x r' hTruth hDev hmargin)

/-- If a deviation forfeits truthful wins with a strict competitive margin
    throughout a positive-weight query region, truthful expected utility is
    strictly larger.  This is the nonatomic counterpart of the point theorem. -/
theorem vcg_strict_expected_on_contested_set
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E) (s : Set E)
    [QueryMeasure.PositiveOn μ s]
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hTruth : ∀ x ∈ s, winner auc x = i)
    (hDev : ∀ x ∈ s, winner (auc.withReport i r') x ≠ i)
    (hmargin : ∀ x ∈ s,
      welfareOthersWithout auc i x < trueVal (auc.valuation i) x) :
    expectedPlayerUtility (auc.withReport i r') i μ < expectedPlayerUtility auc i μ := by
  exact QueryMeasure.PositiveOn.integral_lt_of_pointwise_lt_on
    (self := inferInstance)
    (playerUtility (auc.withReport i r') i) (playerUtility auc i)
    (fun x => vcg_dsic auc i x r' hi)
    (fun x hx => vcg_strict_at_contested_point auc i x r'
      (hTruth x hx) (hDev x hx) (hmargin x hx))

/-- If allocation changes throughout a positive-weight region away from
    competitive ties, the deviation has strictly lower expected utility. -/
theorem vcg_strict_expected_on_allocation_change_set
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E) (s : Set E)
    [QueryMeasure.PositiveOn μ s]
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hchange : ∀ x ∈ s,
      ¬ (winner (auc.withReport i r') x = i ↔ winner auc x = i))
    (hmargin : ∀ x ∈ s,
      trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x) :
    expectedPlayerUtility (auc.withReport i r') i μ < expectedPlayerUtility auc i μ := by
  exact QueryMeasure.PositiveOn.integral_lt_of_pointwise_lt_on
    (self := inferInstance)
    (playerUtility (auc.withReport i r') i) (playerUtility auc i)
    (fun x => vcg_dsic auc i x r' hi)
    (fun x hx => vcg_strict_of_allocation_change
      auc i x r' hi (hchange x hx) (hmargin x hx))

/-- Therefore an expected-utility tie cannot disagree with truthful allocation
    throughout any positive-weight region having nonzero competitive margins. -/
theorem expected_utility_tie_forbids_allocation_change_set
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E) (s : Set E)
    [QueryMeasure.PositiveOn μ s]
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hmargin : ∀ x ∈ s,
      trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x)
    (heq : expectedPlayerUtility (auc.withReport i r') i μ =
      expectedPlayerUtility auc i μ) :
    ¬ ∀ x ∈ s, ¬ (winner (auc.withReport i r') x = i ↔ winner auc x = i) := by
  intro hchange
  have hstrict := vcg_strict_expected_on_allocation_change_set
    auc i r' μ s hi hchange hmargin
  exact (ne_of_lt hstrict) heq

/-- Queries where the deviation changes player `i`'s allocation away from a
    competitive tie. -/
def strictlyContestedAllocationDisagreement
    (auc : Auction ι E) (i : ι) (r' : Report E) : Set E :=
  {x | ¬ (winner (auc.withReport i r') x = i ↔ winner auc x = i) ∧
    trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x}

/-- An expected-utility tie implies that the strictly contested allocation-
    disagreement set cannot have positive query weight.  This is the abstract
    interface's analogue of allocation equivalence almost everywhere. -/
theorem expected_utility_tie_disagreement_not_positive
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (heq : expectedPlayerUtility (auc.withReport i r') i μ =
      expectedPlayerUtility auc i μ) :
    ¬ QueryMeasure.PositiveOn μ (strictlyContestedAllocationDisagreement auc i r') := by
  intro hpositive
  letI := hpositive
  apply expected_utility_tie_forbids_allocation_change_set
    auc i r' μ (strictlyContestedAllocationDisagreement auc i r') hi
    (fun x hx => hx.2) heq
  intro x hx
  exact hx.1

/-- Dirac specialization: a contested point by itself witnesses strict
    expected dominance. -/
theorem vcg_strict_expected_dirac
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hTruth : winner auc x = i)
    (hDev : winner (auc.withReport i r') x ≠ i)
    (hmargin : welfareOthersWithout auc i x < trueVal (auc.valuation i) x) :
    expectedPlayerUtility (auc.withReport i r') i (QueryMeasure.dirac x) <
      expectedPlayerUtility auc i (QueryMeasure.dirac x) := by
  exact vcg_strict_expected_at_contested_point auc i x r' (QueryMeasure.dirac x)
    hi hTruth hDev hmargin

/-- At a query whose strict inequalities are detected by `μ`, an
    expected-utility tie forces the deviation to preserve whether player `i`
    wins.  This local form avoids requiring every point of a continuous query
    space to carry positive atomic weight. -/
theorem expected_utility_tie_implies_allocation_tie_at
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E)
    (x : E) [QueryMeasure.PositiveAt μ x]
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hmargin : trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x)
    (heq : expectedPlayerUtility (auc.withReport i r') i μ =
      expectedPlayerUtility auc i μ) :
    winner (auc.withReport i r') x = i ↔ winner auc x = i := by
  constructor
  · intro hDev
    by_contra hTruth
    have hle := trueVal_le_welfareOthersWithout_of_loss auc i x hi hTruth
    have hlt : trueVal (auc.valuation i) x < welfareOthersWithout auc i x :=
      lt_of_le_of_ne hle hmargin
    have hpoint : playerUtility (auc.withReport i r') i x < playerUtility auc i x := by
      rw [playerUtility_eq_zero_of_loser (auc := auc) (i := i) (x := x) hTruth]
      rw [playerUtility_of_winner
        (auc := auc.withReport i r') (i := i) (x := x) hDev]
      rw [welfareOthersWithout_invariant]
      exact sub_neg.mpr hlt
    have hstrict : expectedPlayerUtility (auc.withReport i r') i μ <
        expectedPlayerUtility auc i μ :=
      QueryMeasure.PositiveAt.integral_lt_of_pointwise_lt_at
        (self := inferInstance)
        (playerUtility (auc.withReport i r') i) (playerUtility auc i)
        (fun y => vcg_dsic auc i y r' hi) hpoint
    exact (ne_of_lt hstrict) heq
  · intro hTruth
    by_contra hDev
    have hle := welfareOthersWithout_le_trueVal_of_win auc i x hi hTruth
    have hmargin : welfareOthersWithout auc i x < trueVal (auc.valuation i) x :=
      lt_of_le_of_ne hle (Ne.symm hmargin)
    have hstrict := vcg_strict_expected_at_contested_point
      auc i x r' μ hi hTruth hDev hmargin
    exact (ne_of_lt hstrict) heq

/-- Strong discrete/full-detection specialization of
    `expected_utility_tie_implies_allocation_tie_at`.  For nonatomic query
    distributions, use the local theorem (or a future almost-everywhere
    interface) instead of assuming `PositiveAt` at every point. -/
theorem truthful_unique_maximizer_up_to_allocation
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E)
    (hi : isTruthful (auc.report i) (auc.valuation i))
    (hpositive : ∀ x, QueryMeasure.PositiveAt μ x)
    (hcoverage : ∀ x,
      trueVal (auc.valuation i) x ≠ welfareOthersWithout auc i x)
    (heq : expectedPlayerUtility (auc.withReport i r') i μ =
      expectedPlayerUtility auc i μ) :
    ∀ x, winner (auc.withReport i r') x = i ↔ winner auc x = i := by
  intro x
  letI := hpositive x
  exact expected_utility_tie_implies_allocation_tie_at
    auc i r' μ x hi (hcoverage x) heq

/-- In a one-player market every report gives the player the same pointwise
    utility.  This witnesses why competition is necessary for strictness. -/
theorem playerUtility_invariant_of_subsingleton [Subsingleton ι]
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E) :
    playerUtility (auc.withReport i r') i x = playerUtility auc i x := by
  have hTruth : winner auc x = i := Subsingleton.elim _ _
  have hDev : winner (auc.withReport i r') x = i := Subsingleton.elim _ _
  rw [playerUtility_of_winner (auc := auc) (i := i) (x := x) hTruth]
  rw [playerUtility_of_winner
    (auc := auc.withReport i r') (i := i) (x := x) hDev]
  rw [welfareOthersWithout_invariant]
  change trueVal (auc.valuation i) x - welfareOthersWithout auc i x =
    trueVal (auc.valuation i) x - welfareOthersWithout auc i x
  rfl

/-- Consequently every report also ties in expected utility in a one-player
    market, for every `QueryMeasure`. -/
theorem expectedPlayerUtility_invariant_of_subsingleton [Subsingleton ι]
    (auc : Auction ι E) (i : ι) (r' : Report E) (μ : QueryMeasure E) :
    expectedPlayerUtility (auc.withReport i r') i μ = expectedPlayerUtility auc i μ := by
  apply congrArg μ.integrate
  funext x
  exact playerUtility_invariant_of_subsingleton auc i x r'

-- ============================================================
-- Nash as corollary of DSIC
-- ============================================================

theorem vcg_strategyproof
    (auc : Auction ι E) (i : ι) (x : E) (r' : Report E)
    (htruth : allTruthful auc) :
    playerUtility auc i x ≥
      playerUtility (auc.withReport i r') i x :=
  vcg_dsic auc i x r' (htruth i)

-- ============================================================
-- HEDGES CONNECTION
-- ============================================================

theorem vcg_is_nash_equilibrium
    (auc : Auction ι E) (x : E) (k : ι → ℝ)
    (htruth : allTruthful auc) :
    vcgOpenGame.isNashEquilibrium x k auc := by
  change ∀ (i : ι) (r' : Report E),
    playerUtility auc i x ≥ playerUtility (auc.withReport i r') i x
  exact fun i r' => vcg_dsic auc i x r' (htruth i)

-- ============================================================
-- SECONDARY corollaries (now from DSIC)
-- ============================================================

theorem truthful_sigma_is_best_response
    (auc : Auction ι E) (i : ι) (x : E) (σ' : ℝ) (hσ' : 0 < σ')
    (hi : isTruthful (auc.report i) (auc.valuation i)) :
    let r' : Report E := {
      center := (auc.report i).center
      sigma := σ'
      bid := (auc.report i).bid
      sigma_pos := hσ'
      bid_pos := (auc.report i).bid_pos }
    playerUtility auc i x ≥ playerUtility (auc.withReport i r') i x := by
  intro r'; exact vcg_dsic auc i x r' hi

end
