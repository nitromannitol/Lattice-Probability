import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BWiring
import LatticeProb.LQG.Theorem15DiscreteBoundary

/-!
# Theorem 1.5 with discrete boundary data on the good event of (3.35)

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Theorem 1.5 and the
proof of Theorem 3.9. This is `theorem15_of_lemma311Holds` with the continuous boundary data (a `χ`-Hölder function
`f` on `∂D` and the discrete harmonic extension of its (1.6) values) replaced by discrete boundary data: a function
`g : V → ℝ`, discrete harmonic on `V(D) \ V(∂D)`, with `|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and `|g(a)| ≤ M`
on the boundary vertices `V(D) ∩ V(∂D)`. The inputs are the same:
* (3.35) at an ambient radius `ρ' > ρ`: `T15A.Lemma311Holds H ε ρ' β p`, read as the disconnection hypothesis
  through `disc_of_lemma311Holds`;
* (3.31′): produced on the same event by `t15c_boundaryEstimate_of_lemma311Holds` and read as `BoundaryEstimate`
  through `boundaryEstimate_of_t15c`;
* the cells meeting `B_ρ(0)` have diameter `≤ ε^q` ([18] Lemma 2.7);
and the deterministic step is `theorem15_deterministic_discreteBoundary`.

Main results:
* `theorem15_of_lemma311Holds_discreteBoundary`: `|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'` for `x, y ∈ V(D)`, with
  `K = theorem15DiscreteConst p' C₁ ξ₁ β q χ C' M` and `ξ' = theorem15DiscreteExponent p' ξ₁ β q χ`
  (`p' = probParam p`, `ξ₁ = boundaryExponent p`, `C₁ = boundaryConst p ρ ρ'`).
* `theorem15_of_lemma311Holds_discreteBoundary_max`: the same estimate with the constant `max C₀ (A₀ M)`,
  `C₀ = theorem15DiscreteBdryConst χ C'` and `A₀ = theorem15DiscreteMassConst p' C₁ ξ₁`; `A₀` depends only on
  `p`, `ρ` and `ρ'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- **[18] Theorem 1.5 with discrete boundary data, on one good environment**. Let `H` be a cellular embedding of a
connected graph with (LC), marked points `pt v ∈ H_v`, `0 < ε ≤ 1`, `0 < ρ < ρ'`, `0 < β ≤ q ≤ 1`, `p > 0`, and
assume (3.35) at ambient radius `ρ'` (`T15A.Lemma311Holds H ε ρ' β p`) and that the cells meeting `B_ρ(0)` have
diameter `≤ ε^q`. Then for every open `D ⊆ B_ρ(0)` with `ℂ \ D` preconnected and every `g : V → ℝ` discrete harmonic
on `V(D) \ V(∂D)` with `|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and `|g(a)| ≤ M` on the boundary vertices
`V(D) ∩ V(∂D)`: `|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'` on `V(D)`, with
`K = theorem15DiscreteConst p' C₁ ξ₁ β q χ C' M` and `ξ' = theorem15DiscreteExponent p' ξ₁ β q χ`
(`p' = probParam p`, `ξ₁ = boundaryExponent p`, `C₁ = boundaryConst p ρ ρ'`). -/
theorem theorem15_of_lemma311Holds_discreteBoundary {H : CellularEmbedding G o} (hconn : G.adj.Connected)
    (hLC : H.PointConnected) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v)
    {ε ρ ρ' β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hβ : 0 < β)
    (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p) (h311 : T15A.Lemma311Holds H ε ρ' β p)
    (hcells : ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell x) ≤ ε ^ q)
    {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ)
    {g : V → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤
        theorem15DiscreteConst (probParam p) (boundaryConst p ρ ρ') (boundaryExponent p) β q χ C' M *
          max ε (dist (pt x) (pt y)) ^
            theorem15DiscreteExponent (probParam p) (boundaryExponent p) β q χ := by
  have hp' := probParam_pos hp
  have h311' : T15A.Lemma311Holds H ε ρ' β (probParam p) :=
    T15A.Lemma311Holds.mono h311 hε0 hε1 le_rfl le_rfl (min_le_left _ _)
  have hDρ' : D ⊆ ball (0 : ℂ) ρ' := hDρ.trans (ball_subset_ball hρρ'.le)
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDρ
  have h331 : BoundaryEstimate G H.cell pt D (ε ^ β) (boundaryConst p ρ ρ') (boundaryExponent p) :=
    boundaryEstimate_of_t15c hε0
      (t15c_boundaryEstimate_of_lemma311Holds hconn hLC hε0 hρ hρρ' hp' (probParam_lt_one p) h311')
      hDo hDρ hDc pt hpt
  refine theorem15_deterministic_discreteBoundary H hconn pt hpt hDo hDb hε0 hε1 hβ hβq hq1 hp'
    (boundaryConst_nonneg hρ hρρ') (boundaryExponent_pos hp) ?_ (disc_of_lemma311Holds hε0 h311' hDρ')
    h331 hC' hχ hM hharm hbdry hbdM
  rintro v ⟨c, hc, hcD⟩
  exact hcells v ⟨c, hc, hDρ hcD⟩

/-- **[18] Theorem 1.5 with discrete boundary data, on one good environment, with the constant `max C₀ (A₀ M)`**:
under the hypotheses of `theorem15_of_lemma311Holds_discreteBoundary`, for all `x, y ∈ V(D)`,
`|g(x) − g(y)| ≤ max C₀ (A₀ M) (ε ∨ |pt x − pt y|)^ξ'` with `C₀ = theorem15DiscreteBdryConst χ C'` (free of `M`) and
`A₀ = theorem15DiscreteMassConst p' C₁ ξ₁` (depending only on `p`, `ρ`, `ρ'`). -/
theorem theorem15_of_lemma311Holds_discreteBoundary_max {H : CellularEmbedding G o}
    (hconn : G.adj.Connected) (hLC : H.PointConnected) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v)
    {ε ρ ρ' β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρρ' : ρ < ρ') (hβ : 0 < β)
    (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p) (h311 : T15A.Lemma311Holds H ε ρ' β p)
    (hcells : ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell x) ≤ ε ^ q)
    {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ)
    {g : V → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) → GMS3.lap G g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
        |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤
        max (theorem15DiscreteBdryConst χ C')
            (theorem15DiscreteMassConst (probParam p) (boundaryConst p ρ ρ') (boundaryExponent p) * M) *
          max ε (dist (pt x) (pt y)) ^
            theorem15DiscreteExponent (probParam p) (boundaryExponent p) β q χ := by
  intro x hx y hy
  refine (theorem15_of_lemma311Holds_discreteBoundary hconn hLC pt hpt hε0 hε1 hρ hρρ' hβ hβq hq1 hp h311
    hcells hDo hDρ hDc hC' hχ hM hharm hbdry hbdM x hx y hy).trans ?_
  exact mul_le_mul_of_nonneg_right (theorem15DiscreteConst_le hβ (boundaryConst_nonneg hρ hρρ') hM)
    (Real.rpow_nonneg (le_max_of_le_left hε0.le) _)

end MatedCRTHarmonic.GMSMain.T15B
