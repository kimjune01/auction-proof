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
- Groves (1973), Thm 2. DOI: https://doi.org/10.2307/1914085
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

private theorem List.argmax_congr' {α : Type*} {β : Type*}
    [DecidableEq α] [LinearOrder β]
    {f g : α → β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    l.argmax f = l.argmax g := by
  cases hl : l.argmax f with
  | none => rw [List.argmax_eq_none] at hl; subst hl; rfl
  | some m =>
    symm; rw [List.argmax_eq_some_iff]
    rw [List.argmax_eq_some_iff] at hl
    obtain ⟨hml, hmax, hidx⟩ := hl
    exact ⟨hml, fun a ha => by rw [← h a ha, ← h m hml]; exact hmax a ha,
           fun a ha hle => hidx a ha (by rw [← h m hml, ← h a ha] at hle; exact hle)⟩

private theorem winnerOnFinset_mem (players : Finset ι) (hplayers : players.Nonempty)
    (auc : Auction ι E) (x : E) :
    winnerOnFinset players hplayers auc x ∈ players := by
  unfold winnerOnFinset; dsimp only
  split
  · next w hw =>
    have := List.argmax_eq_some_iff.mp hw
    exact Finset.mem_toList.mp this.1
  · next hw => exact absurd (List.argmax_eq_none.mp hw) (Finset.Nonempty.toList_ne_nil hplayers)

private theorem winnerOnFinset_maximizes_reportedVal
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
        show reportedVal ((Function.update auc.report i r')
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
        show reportedVal ((Function.update auc.report i r')
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

-- ============================================================
-- MAIN THEOREM: DSIC
-- ============================================================

/-- **VCG is DSIC**: truthful bidding is a dominant strategy.

    For any deviation r' that player i might submit, their utility under
    truthful reporting is at least as high — **regardless of what others
    report**. Only player i needs to be truthful.

    Vickrey (1961), Thm 1; Clarke (1971), §3; Groves (1973), Thm 2.
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
  show ∀ (i : ι) (r' : Report E),
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
