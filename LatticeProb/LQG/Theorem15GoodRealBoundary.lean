import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.MainResultsDraft
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.LQG.Theorem15DiscreteBoundaryGood

/-!
# Theorem 1.5 with discrete boundary data on the real-mesh good event of (3.35)

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* (arXiv:1807.07511), Theorem 1.5 and the
proof of Theorem 3.9. On the event `EpsB.Lemma311GoodReal bm η ε ρ' β p` of (3.35) at the real mesh `ε` and the
ambient radius `ρ' = (1 + ρ)/2`, the ε-mated-CRT map `G^ε = MatedCRT.graph ε (bm ω) h` carries a cellular embedding
whose cells are `H^ε_x = η([ε(x − 1), εx])` (`MainResults.cell ε (η ω) x`) and which satisfies
`T15A.Lemma311Holds`. The graph hypotheses of `theorem15_of_lemma311Holds_discreteBoundary` are discharged by:
* connectivity of `G^ε`: `matedCRT_graph_connected_impl` ([18] (1.1));
* (LC), the cells through a point induce a connected subgraph: `pointConnected_of_peanosphere_holds`, from the
  Peanosphere structure of `(bm ω, η ω)` (`RouteM.Peanosphere`, an inline hypothesis).
The statements are deterministic and pointwise in `ω`; no probability enters.

Main results:
* `theorem15_discreteBoundary_of_lemma311GoodReal`: for `ω` in the good event, a point `pt x ∈ H^ε_x` per vertex,
  and `g : ℤ → ℝ` discrete harmonic on `V(D) \ V(∂D)` with `|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and
  `|g(a)| ≤ M` on `V(D) ∩ V(∂D)`: `|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'` on `V(D)`, with the constant and
  exponent of `theorem15_of_lemma311Holds_discreteBoundary` at `ρ' = (1 + ρ)/2`.
* `theorem15_discreteBoundary_max_of_lemma311GoodReal`: the same with the constant `max C₀ (A₀ M)`.
* `Theorem15DiscreteBoundaryEvent`, `lemma311GoodReal_inter_subset_theorem15DiscreteBoundaryEvent`: the event
  of the `max` form with the marked points `η(εx)` contains the good event intersected with the Peanosphere event
  and the cell-diameter event (`diam H^ε_x ≤ ε^q` for the cells meeting `B_ρ(0)`, [18] Lemma 2.7).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.T15B

/-- The marked point `η(εx)` of the vertex `x` lies in its cell `η([ε(x − 1), εx])` when `ε ≥ 0`. -/
theorem mem_mainResultsCell_self {ε : ℝ} (hε : 0 ≤ ε) (η : C(ℝ, ℂ)) (x : ℤ) :
    η (ε * x) ∈ MainResults.cell ε η x :=
  ⟨ε * x, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- **[18] Theorem 1.5 with discrete boundary data on the real-mesh good event of (3.35)**. Let `0 < ε ≤ 1`,
`0 < ρ < 1`, `0 < β ≤ q ≤ 1`, `p > 0`, and let `ω` lie in `EpsB.Lemma311GoodReal bm η ε ((1 + ρ)/2) β p`, with
`(bm ω, η ω)` a Peanosphere and the cells `H^ε_x = η([ε(x − 1), εx])` meeting `B_ρ(0)` of diameter `≤ ε^q`.
Then for every locally finite ε-mated-CRT map `G^ε` of `bm ω`, every choice of points `pt x ∈ H^ε_x`, every open
`D ⊆ B_ρ(0)` with `ℂ \ D` preconnected and every `g : ℤ → ℝ` discrete harmonic on `V(D) \ V(∂D)` with
`|g(a) − g(b)| ≤ C' (ε ∨ |pt a − pt b|)^χ` and `|g(a)| ≤ M` on the boundary vertices `V(D) ∩ V(∂D)`:
`|g(x) − g(y)| ≤ K (ε ∨ |pt x − pt y|)^ξ'` on `V(D)`, with
`K = theorem15DiscreteConst p' C₁ ξ₁ β q χ C' M`, `ξ' = theorem15DiscreteExponent p' ξ₁ β q χ`
(`p' = probParam p`, `ξ₁ = boundaryExponent p`, `C₁ = boundaryConst p ρ ((1 + ρ)/2)`). -/
theorem theorem15_discreteBoundary_of_lemma311GoodReal {Ω : Type*} {bm : Ω → MatedCRT.Path2}
    {η : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p)
    (hω : ω ∈ EpsB.Lemma311GoodReal bm η ε ((1 + ρ) / 2) β p)
    (hpeano : RouteM.Peanosphere (bm ω) (η ω))
    (hcells : ∀ x : ℤ, (MainResults.cell ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (MainResults.cell ε (η ω) x) ≤ ε ^ q)
    (h : MatedCRT.IsLocallyFinite ε (bm ω)) (pt : ℤ → ℂ) (hpt : ∀ x, pt x ∈ MainResults.cell ε (η ω) x)
    {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ)
    {g : ℤ → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      v ∉ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
        GMS3.lap (MatedCRT.graph ε (bm ω) h) g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
      ∀ b ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
        b ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
          |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting (MainResults.cell ε (η ω)) D, ∀ y ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      |g x - g y| ≤
        theorem15DiscreteConst (probParam p) (boundaryConst p ρ ((1 + ρ) / 2)) (boundaryExponent p) β q χ
            C' M *
          max ε (dist (pt x) (pt y)) ^
            theorem15DiscreteExponent (probParam p) (boundaryExponent p) β q χ := by
  obtain ⟨h₀, H, hcell, h311⟩ := hω
  have hJ : H.cell = MainResults.cell ε (η ω) := funext hcell
  have hconn : (MatedCRT.graph ε (bm ω) h₀).adj.Connected :=
    MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl ε (bm ω) h₀
  have hLC : H.PointConnected := RouteM.pointConnected_of_peanosphere_holds hpeano H (funext hcell)
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  have hpt' : ∀ v, pt v ∈ H.cell v := by rw [hJ]; exact hpt
  have hcells' : ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → diam (H.cell x) ≤ ε ^ q := by
    rw [hJ]; exact hcells
  have key := theorem15_of_lemma311Holds_discreteBoundary hconn hLC pt hpt' hε0 hε1 hρ hρρ' hβ hβq hq1 hp
    h311 hcells' hDo hDρ hDc hC' hχ hM (by rw [hJ]; exact hharm) (by rw [hJ]; exact hbdry)
    (by rw [hJ]; exact hbdM)
  rw [hJ] at key
  exact key

/-- **[18] Theorem 1.5 with discrete boundary data on the real-mesh good event of (3.35), with the constant
`max C₀ (A₀ M)`**: under the hypotheses of `theorem15_discreteBoundary_of_lemma311GoodReal`, for all
`x, y ∈ V(D)`, `|g(x) − g(y)| ≤ max C₀ (A₀ M) (ε ∨ |pt x − pt y|)^ξ'` with
`C₀ = theorem15DiscreteBdryConst χ C'` (free of `M`) and `A₀ = theorem15DiscreteMassConst p' C₁ ξ₁` (depending only
on `p` and `ρ`). -/
theorem theorem15_discreteBoundary_max_of_lemma311GoodReal {Ω : Type*} {bm : Ω → MatedCRT.Path2}
    {η : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p)
    (hω : ω ∈ EpsB.Lemma311GoodReal bm η ε ((1 + ρ) / 2) β p)
    (hpeano : RouteM.Peanosphere (bm ω) (η ω))
    (hcells : ∀ x : ℤ, (MainResults.cell ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty →
      diam (MainResults.cell ε (η ω) x) ≤ ε ^ q)
    (h : MatedCRT.IsLocallyFinite ε (bm ω)) (pt : ℤ → ℂ) (hpt : ∀ x, pt x ∈ MainResults.cell ε (η ω) x)
    {D : Set ℂ} (hDo : IsOpen D) (hDρ : D ⊆ ball (0 : ℂ) ρ) (hDc : IsPreconnected Dᶜ)
    {g : ℤ → ℝ} {C' χ M : ℝ} (hC' : 0 ≤ C') (hχ : 0 < χ) (hM : 0 ≤ M)
    (hharm : ∀ v ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      v ∉ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
        GMS3.lap (MatedCRT.graph ε (bm ω) h) g v = 0)
    (hbdry : ∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
      ∀ b ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
        b ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
          |g a - g b| ≤ C' * max ε (dist (pt a) (pt b)) ^ χ)
    (hbdM : ∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) → |g a| ≤ M) :
    ∀ x ∈ verticesMeeting (MainResults.cell ε (η ω)) D, ∀ y ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      |g x - g y| ≤
        max (theorem15DiscreteBdryConst χ C')
            (theorem15DiscreteMassConst (probParam p) (boundaryConst p ρ ((1 + ρ) / 2)) (boundaryExponent p) *
              M) *
          max ε (dist (pt x) (pt y)) ^
            theorem15DiscreteExponent (probParam p) (boundaryExponent p) β q χ := by
  intro x hx y hy
  refine (theorem15_discreteBoundary_of_lemma311GoodReal hε0 hε1 hρ hρ1 hβ hβq hq1 hp hω hpeano hcells h pt
    hpt hDo hDρ hDc hC' hχ hM hharm hbdry hbdM x hx y hy).trans ?_
  have hρρ' : ρ < (1 + ρ) / 2 := by linarith
  exact mul_le_mul_of_nonneg_right (theorem15DiscreteConst_le hβ (boundaryConst_nonneg hρ hρρ') hM)
    (Real.rpow_nonneg (le_max_of_le_left hε0.le) _)

/-- **The event of [18] Theorem 1.5 with discrete boundary data at mesh `ε` in `B_ρ(0)`**, with the marked points
`η(εx)`: for every locally finite ε-mated-CRT map `G^ε` of `bm ω`, every open `D ⊆ B_ρ(0)` with `ℂ \ D`
preconnected and every `g : ℤ → ℝ` discrete harmonic on `V(D) \ V(∂D)` with
`|g(a) − g(b)| ≤ C' (ε ∨ |η(εa) − η(εb)|)^χ` and `|g(a)| ≤ M` on `V(D) ∩ V(∂D)` (`C' ≥ 0`, `χ > 0`, `M ≥ 0`):
`|g(x) − g(y)| ≤ max C₀ (A₀ M) (ε ∨ |η(εx) − η(εy)|)^ξ'` on `V(D)`, with the constants of
`theorem15_discreteBoundary_max_of_lemma311GoodReal`. -/
def Theorem15DiscreteBoundaryEvent {Ω : Type*} (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    (ε ρ β q p : ℝ) : Set Ω :=
  {ω | ∀ h : MatedCRT.IsLocallyFinite ε (bm ω), ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ →
    IsPreconnected Dᶜ → ∀ (g : ℤ → ℝ) (C' χ M : ℝ), 0 ≤ C' → 0 < χ → 0 ≤ M →
    (∀ v ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      v ∉ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
        GMS3.lap (MatedCRT.graph ε (bm ω) h) g v = 0) →
    (∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
      ∀ b ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
        b ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) →
          |g a - g b| ≤ C' * max ε (dist (η ω (ε * a)) (η ω (ε * b))) ^ χ) →
    (∀ a ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      a ∈ verticesMeeting (MainResults.cell ε (η ω)) (frontier D) → |g a| ≤ M) →
    ∀ x ∈ verticesMeeting (MainResults.cell ε (η ω)) D, ∀ y ∈ verticesMeeting (MainResults.cell ε (η ω)) D,
      |g x - g y| ≤
        max (theorem15DiscreteBdryConst χ C')
            (theorem15DiscreteMassConst (probParam p) (boundaryConst p ρ ((1 + ρ) / 2)) (boundaryExponent p) *
              M) *
          max ε (dist (η ω (ε * x)) (η ω (ε * y))) ^
            theorem15DiscreteExponent (probParam p) (boundaryExponent p) β q χ}

/-- **The good event of (3.35) at `ρ' = (1 + ρ)/2`, on the Peanosphere event and the cell-diameter event, is
contained in the event of Theorem 1.5 with discrete boundary data** (deterministic inclusion of sets of `Ω`). -/
theorem lemma311GoodReal_inter_subset_theorem15DiscreteBoundaryEvent {Ω : Type*}
    {bm : Ω → MatedCRT.Path2} {η : Ω → C(ℝ, ℂ)} {ε ρ β q p : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1) (hp : 0 < p) :
    EpsB.Lemma311GoodReal bm η ε ((1 + ρ) / 2) β p ∩ {ω | RouteM.Peanosphere (bm ω) (η ω)} ∩
        {ω | ∀ x : ℤ, (MainResults.cell ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty →
          diam (MainResults.cell ε (η ω) x) ≤ ε ^ q} ⊆
      Theorem15DiscreteBoundaryEvent bm η ε ρ β q p := by
  rintro ω ⟨⟨hω, hpeano⟩, hcells⟩
  intro h D hDo hDρ hDc g C' χ M hC' hχ hM hharm hbdry hbdM
  exact theorem15_discreteBoundary_max_of_lemma311GoodReal hε0 hε1 hρ hρ1 hβ hβq hq1 hp hω hpeano hcells h
    (fun x => η ω (ε * x)) (mem_mainResultsCell_self hε0.le (η ω)) hDo hDρ hDc hC' hχ hM hharm hbdry hbdM

end LatticeProb
