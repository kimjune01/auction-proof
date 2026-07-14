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

/-!
## Discharging the coverage hypothesis

The section above is deliberately abstract: it proves convergence *given* that
competition shrinks the indifference classes.  Here that coverage claim is
discharged, not assumed.  The reported center enters `score` only through
`‖x - center‖²`, so holding bid and spread fixed, two centers give player `i`
the same score at query `y` exactly when they are equidistant from `y`.  A
competitor sits on that win/lose boundary, so each competitor contributes one
score-indifference constraint.  Enough competitors probing independent
directions force the reported center to equal the true one exactly.
-/

section Identification

open Filter
open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {κ : Type*}

/-- Player `i`'s score at query `y` is unchanged by reporting center `c` instead
    of `cStar` (bid and spread fixed) exactly when `c` and `cStar` are
    equidistant from `y`.  A competitor located at `y` pins down this constraint:
    it is where the win/lose boundary sits, so preserving `i`'s score at `y`
    preserves the allocation there. -/
def scoreIndifferent (cStar c y : F) : Prop := ‖y - c‖ = ‖y - cStar‖

/-- Two score-indifference constraints, at base query `y₀` and probe query `y`,
    force the center displacement `cStar - c` orthogonal to the probe
    displacement `y - y₀`. -/
theorem inner_probe_eq_zero {cStar c y₀ y : F}
    (h0 : scoreIndifferent cStar c y₀) (hy : scoreIndifferent cStar c y) :
    ⟪y - y₀, cStar - c⟫ = 0 := by
  have e0 : ‖y₀ - c‖ ^ 2 = ‖y₀ - cStar‖ ^ 2 := by rw [h0]
  have ey : ‖y - c‖ ^ 2 = ‖y - cStar‖ ^ 2 := by rw [hy]
  rw [norm_sub_sq_real, norm_sub_sq_real] at e0 ey
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith [e0, ey]

/-- **Competition identifies the reported center.**  If player `i` stays
    score-indifferent to the truthful center `cStar` at a base query `y₀` and at
    a family of probe queries whose displacements `probe k - y₀` span the whole
    embedding space, then the only center consistent with every constraint is
    `cStar` itself.  Enough competitors probing enough independent directions
    pin the reported center exactly — the coverage hypothesis of the abstract
    section is now a theorem, not an assumption. -/
theorem center_identified_of_spanning_probes
    (cStar c y₀ : F) (probe : κ → F)
    (h0 : scoreIndifferent cStar c y₀)
    (hprobe : ∀ k, scoreIndifferent cStar c (probe k))
    (hspan : Submodule.span ℝ (Set.range (fun k => probe k - y₀)) = ⊤) :
    c = cStar := by
  set w := cStar - c with hw
  have hortho : ∀ v ∈ Submodule.span ℝ (Set.range (fun k => probe k - y₀)),
      ⟪v, w⟫ = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact inner_probe_eq_zero h0 (hprobe k)
    | zero => simp
    | add x y _ _ ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
    | smul a x _ ih => rw [real_inner_smul_left, ih, mul_zero]
  have hself : ⟪w, w⟫ = 0 := by
    apply hortho
    rw [hspan]; exact Submodule.mem_top
  have hzero : w = 0 := inner_self_eq_zero.mp hself
  rw [hw, sub_eq_zero] at hzero
  exact hzero.symm

/-- The exact identification collapses the concrete indifference class to a
    singleton: the centers score-indifferent to `cStar` at `y₀` and along a
    spanning probe family are exactly `{cStar}`. -/
theorem indifferent_centers_eq_singleton
    (cStar y₀ : F) (probe : κ → F)
    (hspan : Submodule.span ℝ (Set.range (fun k => probe k - y₀)) = ⊤) :
    {c | scoreIndifferent cStar c y₀ ∧ ∀ k, scoreIndifferent cStar c (probe k)}
      = {cStar} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, hp⟩
    exact center_identified_of_spanning_probes cStar c y₀ probe h0 hp hspan
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩

/-- Convergence with the coverage hypothesis discharged: if every selected
    center satisfies the score-indifference constraints along a spanning probe
    family, the selection is constantly `cStar`, hence converges to it. -/
theorem centers_converge_of_spanning_identification
    (cStar y₀ : F) (probe : κ → F) (chosen : ℕ → F)
    (hspan : Submodule.span ℝ (Set.range (fun k => probe k - y₀)) = ⊤)
    (hchosen : ∀ n, scoreIndifferent cStar (chosen n) y₀ ∧
      ∀ k, scoreIndifferent cStar (chosen n) (probe k)) :
    Tendsto chosen atTop (nhds cStar) := by
  have hconst : chosen = fun _ => cStar :=
    funext fun n => center_identified_of_spanning_probes cStar (chosen n) y₀ probe
      (hchosen n).1 (hchosen n).2 hspan
  rw [hconst]
  exact tendsto_const_nhds

end Identification
