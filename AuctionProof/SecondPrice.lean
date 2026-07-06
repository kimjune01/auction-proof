import AuctionProof.Auction
import AuctionProof.Efficiency
import AuctionProof.Strategyproof

/-!
# Keywords are the degenerate case: exact Vickrey recovery

The blog post (https://june.kim/keywords-are-tiny-circles) claims keyword
auctions are the σ → 0 special case of the embedding auction. The limit
half is proved in VectorSpace.lean (`keyword_is_degenerate_limit`,
`score_at_center`). This file proves the mechanism half on the real auction
machinery: at a query point where all advertisers' centers coincide (the
keyword's embedding), the Gaussian embedding auction with Clarke pivot
payments **is** the sealed-bid second-price auction:

- `reportedVal_common_center`: every report's value at the shared center is
  its bid — the geometry drops out entirely.
- `winner_maximizes_bid_of_common_center`: the winner is a highest bidder.
- `vcgPayment_common_center_second_price`: the winner pays the highest
  competing bid.

Reference:
- Vickrey (1961), "Counterspeculation, Auctions, and Competitive Sealed
  Tenders," Journal of Finance 16(1):8-37, Thm 1.
  DOI: https://doi.org/10.2307/2977633
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- At its own center, a report's implied value is exactly its bid:
    the Gaussian factor is `exp(0) = 1`. -/
theorem reportedVal_center (r : Report E) : reportedVal r r.center = r.bid := by
  unfold reportedVal
  simp

/-- All advertisers centered at the query point: the keyword scenario.
    Each has embedded the same keyword; the query lands on it. -/
def commonCenter (auc : Auction ι E) (x : E) : Prop :=
  ∀ i, (auc.report i).center = x

/-- Under a common center, reported value at the query is the bid. -/
theorem reportedVal_common_center (auc : Auction ι E) (x : E)
    (hc : commonCenter auc x) (i : ι) :
    reportedVal (auc.report i) x = (auc.report i).bid := by
  rw [← hc i]
  exact reportedVal_center (auc.report i)

/-- Under a common center, the winner is a highest bidder: the auction
    ranks by bid alone, as in a keyword auction. -/
theorem winner_maximizes_bid_of_common_center (auc : Auction ι E) (x : E)
    (hc : commonCenter auc x) (j : ι) :
    (auc.report j).bid ≤ (auc.report (winner auc x)).bid := by
  have h := winner_maximizes_reportedVal auc x j
  rwa [reportedVal_common_center auc x hc, reportedVal_common_center auc x hc] at h

/-- **Exact Vickrey recovery.** Under a common center with at least one
    competitor, the Clarke pivot payment of the winner is the highest
    competing bid: pay the second price.

    Together with `winner_maximizes_bid_of_common_center` this shows the
    embedding auction restricted to a keyword point is literally the
    sealed-bid second-price auction of Vickrey (1961). -/
theorem vcgPayment_common_center_second_price (auc : Auction ι E) (x : E)
    (hc : commonCenter auc x)
    (hne : (Finset.univ.erase (winner auc x)).Nonempty) :
    vcgPayment auc (winner auc x) x =
      (Finset.univ.erase (winner auc x)).sup' hne
        (fun j => (auc.report j).bid) := by
  set w := winner auc x with hw
  -- The `with i` branch: welfareOthersWith is zero because w won.
  have hwith : welfareOthersWith auc w x = 0 := by
    unfold welfareOthersWith welfareOthersAt
    rw [← hw, if_pos rfl]
  -- The `without i` branch: the runner-up's reported value, i.e. its bid.
  set w' := winnerOnFinset (Finset.univ.erase w) hne auc x with hw'
  have hw'_mem : w' ∈ Finset.univ.erase w :=
    winnerOnFinset_mem (Finset.univ.erase w) hne auc x
  have hw'_ne : w' ≠ w := Finset.ne_of_mem_erase hw'_mem
  have hwithout : welfareOthersWithout auc w x = (auc.report w').bid := by
    unfold welfareOthersWithout
    rw [dif_pos hne]
    unfold welfareOthersAt
    rw [← hw', if_neg hw'_ne]
    exact reportedVal_common_center auc x hc w'
  -- The runner-up's bid is the maximum competing bid.
  have hsup : (auc.report w').bid =
      (Finset.univ.erase w).sup' hne (fun j => (auc.report j).bid) := by
    apply le_antisymm
    · exact Finset.le_sup' (fun j => (auc.report j).bid) hw'_mem
    · apply Finset.sup'_le
      intro j hj
      have h := winnerOnFinset_maximizes_reportedVal
        (Finset.univ.erase w) hne auc x j hj
      rw [← hw'] at h
      rwa [reportedVal_common_center auc x hc,
        reportedVal_common_center auc x hc] at h
  unfold vcgPayment
  rw [hwith, hwithout, hsup]
  ring

end
