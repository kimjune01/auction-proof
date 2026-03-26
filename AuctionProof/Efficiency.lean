import AuctionProof.Auction

/-!
# Checkpoint 2: Pointwise allocation maximizes welfare

The key lemma: when reports are truthful (bid = trueValue, sigma = trueSigma,
center = center), the scoring function is a monotone transformation of the
value function. Therefore argmax of score = argmax of value, and the winner
rule maximizes welfare.

This is our composition connecting:
- The argmax allocation rule (Tier 3, from Auction.lean)
- Monotonicity of log (Mathlib)
- The observation that score = log ∘ value under truthful reports

No new math. The only bridge is showing score_i(x) = log(v_i(x)) when
reports match true valuations.
-/

noncomputable section

open Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A report is truthful when it matches the player's private valuation:
    same center, same sigma, bid = true value. -/
def isTruthful (r : Report E) (v : Valuation E) : Prop :=
  r.center = v.center ∧ r.sigma = v.trueSigma ∧ r.bid = v.trueValue

/-- All players report truthfully. -/
def allTruthful (auc : Auction ι E) : Prop :=
  ∀ i, isTruthful (auc.report i) (auc.valuation i)

set_option linter.unusedSectionVars false in
/-- Helper: if argmax returns w, then winner = w. -/
lemma winner_eq_of_argmax (auc : Auction ι E) (x : E) (w : ι)
    (harg : (Finset.univ : Finset ι).toList.argmax (fun i => score (auc.report i) x) = some w) :
    winner auc x = w := by
  unfold winner
  dsimp only
  split
  · next heq => exact Option.some.inj (harg.symm.trans heq).symm
  · next heq => exact absurd (harg.symm.trans heq) (by simp)

/-- Under truthful reporting, score_i(x) = log(trueVal_i(x)).

This is the bridge: the scoring function is log of the value function
when reports are honest. Since log is monotone, argmax score = argmax value.

Our composition, not a published theorem. Connects:
- score definition (Tier 3)
- trueVal definition (Tier 3)
- Real.log and Real.exp are inverses (Mathlib) -/
theorem score_eq_log_trueVal (r : Report E) (v : Valuation E) (x : E)
    (h : isTruthful r v) :
    score r x = Real.log (trueVal v x) := by
  unfold score trueVal isTruthful at *
  obtain ⟨hc, hs, hb⟩ := h
  rw [hc, hs, hb]
  rw [Real.log_mul (ne_of_gt v.value_pos) (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_exp]
  ring

/-- score = log(reportedVal) unconditionally — no truthfulness needed.

    This is the key to DSIC: the mechanism always maximizes reported
    welfare. Only the truthful player aligns reported with true welfare. -/
theorem score_eq_log_reportedVal (r : Report E) (x : E) :
    score r x = Real.log (reportedVal r x) := by
  unfold score reportedVal
  rw [Real.log_mul (ne_of_gt r.bid_pos) (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_exp]
  ring

/-- reportedVal equals trueVal when the report is truthful. -/
theorem reportedVal_eq_trueVal_of_truthful (r : Report E) (v : Valuation E) (x : E)
    (h : isTruthful r v) :
    reportedVal r x = trueVal v x := by
  unfold reportedVal trueVal isTruthful at *
  obtain ⟨hc, hs, hb⟩ := h
  rw [hc, hs, hb]

/-- The winner maximizes reported value — no truthfulness needed.

    For any player j, reportedVal(winner) ≥ reportedVal(j). This follows
    from score = log(reportedVal) and winner = argmax of score. -/
theorem winner_maximizes_reportedVal (auc : Auction ι E) (x : E) (j : ι) :
    reportedVal (auc.report (winner auc x)) x ≥ reportedVal (auc.report j) x := by
  let scores : ι → ℝ := fun i => score (auc.report i) x
  let l : List ι := (Finset.univ : Finset ι).toList
  have hj_mem : j ∈ l := by simp [l, Finset.mem_toList]
  rcases harg : l.argmax scores with _ | w
  · have hnil : l = [] := List.argmax_eq_none.mp harg
    exact absurd hnil (Finset.Nonempty.toList_ne_nil Finset.univ_nonempty)
  · have hw_arg : w ∈ l.argmax scores := by simp [harg]
    have hscore : scores j ≤ scores w := List.le_of_mem_argmax hj_mem hw_arg
    have hwinner : winner auc x = w := winner_eq_of_argmax auc x w harg
    have hscore' : score (auc.report j) x ≤ score (auc.report (winner auc x)) x := by
      rw [hwinner]; exact hscore
    have hj_log : score (auc.report j) x = Real.log (reportedVal (auc.report j) x) :=
      score_eq_log_reportedVal (auc.report j) x
    have hw_log : score (auc.report (winner auc x)) x =
        Real.log (reportedVal (auc.report (winner auc x)) x) :=
      score_eq_log_reportedVal (auc.report (winner auc x)) x
    have hlog : Real.log (reportedVal (auc.report j) x) ≤
        Real.log (reportedVal (auc.report (winner auc x)) x) := by
      simpa [hj_log, hw_log] using hscore'
    have hpos : ∀ k : ι, 0 < reportedVal (auc.report k) x := by
      intro k; unfold reportedVal; exact mul_pos (auc.report k).bid_pos (Real.exp_pos _)
    exact (Real.log_le_log_iff (hpos j) (hpos (winner auc x))).mp hlog

/-- The winner under truthful reporting maximizes true value.

For any other player j, trueVal(winner) ≥ trueVal(j) at query x.

Our composition. The proof strategy:
1. score(winner) ≥ score(j) — by definition of argmax
2. score = log(trueVal) — by score_eq_log_trueVal
3. log is monotone — by Mathlib
4. Therefore trueVal(winner) ≥ trueVal(j) -/
theorem winner_maximizes_welfare (auc : Auction ι E) (x : E)
    (htruth : allTruthful auc) (j : ι) :
    trueVal (auc.valuation (winner auc x)) x ≥ trueVal (auc.valuation j) x := by
  let scores : ι → ℝ := fun i => score (auc.report i) x
  let l : List ι := (Finset.univ : Finset ι).toList
  have hj_mem : j ∈ l := by
    simp [l, Finset.mem_toList]
  rcases harg : l.argmax scores with _ | w
  · have hnil : l = [] := List.argmax_eq_none.mp harg
    have hcontra : False := by
      have hne : ((Finset.univ : Finset ι).toList) ≠ [] :=
        Finset.Nonempty.toList_ne_nil (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
      exact hne (by simpa [l] using hnil)
    exact hcontra.elim
  · have hw_arg : w ∈ l.argmax scores := by
      simp [harg]
    have hscore : scores j ≤ scores w :=
      List.le_of_mem_argmax hj_mem hw_arg
    have hwinner : winner auc x = w :=
      winner_eq_of_argmax auc x w harg
    have hscore' : score (auc.report j) x ≤ score (auc.report (winner auc x)) x := by
      rw [hwinner]; exact hscore
    have hj_log :
        score (auc.report j) x = Real.log (trueVal (auc.valuation j) x) :=
      score_eq_log_trueVal (auc.report j) (auc.valuation j) x (htruth j)
    have hw_log :
        score (auc.report (winner auc x)) x =
          Real.log (trueVal (auc.valuation (winner auc x)) x) :=
      score_eq_log_trueVal (auc.report (winner auc x)) (auc.valuation (winner auc x)) x
        (htruth (winner auc x))
    have hlog :
        Real.log (trueVal (auc.valuation j) x) ≤
          Real.log (trueVal (auc.valuation (winner auc x)) x) := by
      simpa [hj_log, hw_log] using hscore'
    have hpos : ∀ i : ι, 0 < trueVal (auc.valuation i) x := by
      intro i
      unfold trueVal
      exact mul_pos (auc.valuation i).value_pos (Real.exp_pos _)
    exact (Real.log_le_log_iff (hpos j) (hpos (winner auc x))).mp hlog

end
