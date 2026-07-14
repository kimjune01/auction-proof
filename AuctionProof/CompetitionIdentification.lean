import AuctionProof.Strategyproof
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Competition identifies reported centers

This file isolates the geometric identification step from the VCG incentive
step.  DSIC already makes the true center optimal; the issue is multiplicity,
not a learning dynamic.  Each informative competitor contributes a persistent
constraint on centers that remain allocation-equivalent to the truthful center.
The feasible classes are
nested by construction.  If a separate competitive-coverage theorem eventually
puts the class inside every ball around the true center, every selection from
those classes converges to the true center.  Connecting actual auction entry to
these persistent constraints is intentionally left as an explicit obligation.
-/

noncomputable section

open Filter Set

variable {E : Type*} [PseudoMetricSpace E]

/-- Centers observationally indistinguishable after the first `n` competitive
    constraints. -/
def competitiveIndifferenceClass (constraint : ℕ → E → Prop) (n : ℕ) : Set E :=
  {c | ∀ k < n, constraint k c}

/-- Adding one competitor can only shrink the indifference class. -/
theorem competitiveIndifferenceClass_succ_subset
    (constraint : ℕ → E → Prop) (n : ℕ) :
    competitiveIndifferenceClass constraint (n + 1) ⊆
      competitiveIndifferenceClass constraint n := by
  intro c hc k hk
  exact hc k (Nat.lt_succ_of_lt hk)

/-- The competitive indifference classes form an antitone sequence. -/
theorem competitiveIndifferenceClass_antitone
    (constraint : ℕ → E → Prop) :
    Antitone (competitiveIndifferenceClass constraint) := by
  intro m n hmn c hc k hk
  exact hc k (lt_of_lt_of_le hk hmn)

/-- **Hotelling identification.** If every sufficiently thick market pins the
    surviving indifference class inside any prescribed neighborhood of the
    true center, then every choice of a center from that class converges to the
    true center. -/
theorem centers_converge_of_competitive_coverage
    (C : ℕ → Set E) (cStar : E) (chosen : ℕ → E)
    (hchosen : ∀ n, chosen n ∈ C n)
    (hcoverage : ∀ ε > 0, ∃ N, ∀ n ≥ N, C n ⊆ Metric.ball cStar ε) :
    Tendsto chosen atTop (nhds cStar) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hcoverage ε hε
  exact ⟨N, fun n hn => by
    have hball := hN n hn (hchosen n)
    simpa [Metric.mem_ball, dist_comm] using hball⟩

/-- Inductive form of identification: successive persistent competitor
    constraints generate the classes from which centers are selected. -/
theorem selected_centers_converge_as_competitors_pile_on
    (constraint : ℕ → E → Prop) (cStar : E) (chosen : ℕ → E)
    (hchosen : ∀ n, chosen n ∈ competitiveIndifferenceClass constraint n)
    (hcoverage : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      competitiveIndifferenceClass constraint n ⊆ Metric.ball cStar ε) :
    Tendsto chosen atTop (nhds cStar) :=
  centers_converge_of_competitive_coverage
    (competitiveIndifferenceClass constraint) cStar chosen hchosen hcoverage

/-- A quantitative hook for geometric results: if `C n` lies in a closed ball
    of radius `radius n` about `cStar`, and those radii tend to zero, every
    selection from `C n` converges to `cStar`. -/
theorem centers_converge_of_shrinking_radius
    (C : ℕ → Set E) (cStar : E) (chosen : ℕ → E) (radius : ℕ → ℝ)
    (hchosen : ∀ n, chosen n ∈ C n)
    (hradius_nonneg : ∀ n, 0 ≤ radius n)
    (hcontained : ∀ n, C n ⊆ Metric.closedBall cStar (radius n))
    (hradius : Tendsto radius atTop (nhds 0)) :
    Tendsto chosen atTop (nhds cStar) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hradius) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hrlt : radius n < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (hradius_nonneg n)] using hN n hn
  have hdist : dist (chosen n) cStar ≤ radius n := by
    have := hcontained n (hchosen n)
    simpa [Metric.mem_closedBall, dist_comm] using this
  exact lt_of_le_of_lt hdist hrlt

/-- Backwards-compatible name; the hypotheses select centers from the classes
    but do not themselves assert utility maximization. -/
theorem maximizing_centers_converge_as_competitors_pile_on
    (constraint : ℕ → E → Prop) (cStar : E) (chosen : ℕ → E)
    (hchosen : ∀ n, chosen n ∈ competitiveIndifferenceClass constraint n)
    (hcoverage : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      competitiveIndifferenceClass constraint n ⊆ Metric.ball cStar ε) :
    Tendsto chosen atTop (nhds cStar) :=
  selected_centers_converge_as_competitors_pile_on
    constraint cStar chosen hchosen hcoverage

end
