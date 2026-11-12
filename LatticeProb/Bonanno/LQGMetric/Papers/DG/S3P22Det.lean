/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22, deterministic core (DG:1739–1771)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.22
(`prop-lfpp-upper0`). On the event (eqn-lfpp-lower-event) — the square-crossing lower bound
(3.?) `eqn-square-dist` of Lemma 3.21 for every square `S`, and `min μ(B_{δ_ε/2}(z)) ≥ ε` — DG fix
`z, w ∈ 𝕊`, a path `P` covered by `D^ε(z,w;𝕊(1/2))` admissible balls, cut it at the successive
exit times `t_j` of the expanded squares `S_j(1)`, join the points `P(t_j)` by segments
(each inside `S_j(1)`, so of length `≲ δ_ε` and with `ĥ_{ε^β} ≤ max_{S_j(1)} ĥ_{ε^β}` on it) and
bound `Σ_j exp(ξ max_{S_j(1)} ĥ_{ε^β}) ≤ 3 ε^{…} D^ε(z,w;𝕊(1/2))` via (eqn-lfpp-upper-inc),
(eqn-lfpp-upper-sum).

Here the same argument is run on the polygon of `exists_chain_of_dgLGD_le` (vertices in a chain
of admissible balls) in place of `P`, with abstract cells: `S i ⊆ interior (T i)` (DG: `S` and
`S(1)`), `T i` closed convex of diameter `≤ A` (DG: `A = 3√2 δ_ε`), points of `S i` at distance
`≥ a` from `∂T i` (DG: `a = δ_ε`). The crossing hypothesis `hcross` is (eqn-square-dist) read
pointwise (`exp(ξ φ v) ≤ D/L` for all `v ∈ S(1)` is `exp(ξ max_{S(1)} φ) ≤ D/L`), and `hmass` is
the second condition of (eqn-lfpp-lower-event). The last segment (inside `S_𝒥(1)`, not followed by a
crossing; DG's sum (eqn-lfpp-upper-sum) includes `j = 𝒥` without comment) is bounded with the
global maximum `Mx` of `φ` (in DG: `max_{𝕊(1)} ĥ_{ε^β} ≤ (2β + ζ) log ε⁻¹`, eqn-field-control').
Output: `D^{LFPP}(z,w; Ū) ≤ A (2N/L + e^{ξ Mx})` (DG: `≲ δ_ε · 3 ε^{…} D`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open LQGDimension.PolygonRiemannAux

/-- Polygon bound in a convex set: if all vertices lie in the convex set `C` and
`exp(ξ φ) ≤ K i` on the `i`-th edge, then `D^{LFPP}(V 0, V n; C) ≤ Σ_i |V(i+1) − V i| K i`. -/
theorem dgLFPP_le_poly_convex (V : ℕ → ℂ) (n : ℕ) (hn : 0 < n) {φ : ℂ → ℝ} (hφ : Continuous φ)
    (ξ : ℝ) {C : Set ℂ} (hC : Convex ℝ C) (hV : ∀ i ≤ n, V i ∈ C) (K : ℕ → ℝ)
    (hK : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1, Real.exp (ξ * φ (segAff V i s)) ≤ K i) :
    dgLFPP ξ φ C (V 0) (V n) ≤ ∑ i ∈ Finset.range n, ‖V (i + 1) - V i‖ * K i := by
  have hP := DFGPS.L36.isDGPath_polyPath V n hn
  have hPC : IsDGPath C (V 0) (V n) (polyPath V n) := by
    refine ⟨hP.source, hP.target, fun t ht => ?_, hP.continuousOn, hP.piecewise_contDiff⟩
    have hi := idx_lt n hn t
    exact polyPath_mem_of_convex V n hC hn _ hi (hV _ hi.le) (hV _ hi) t
      (mem_Icc_idx n hn t ht.1 ht.2)
  refine (ciInf_le (bddBelow_dg ξ φ C (V 0) (V n)) ⟨_, hPC⟩).trans ?_
  show LQGDimension.lfppLength ξ φ (polyPath V n) ≤ _
  rw [lfppLength_eq_sum V n φ hφ ξ hn]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hcont : Continuous fun s : ℝ => Real.exp (ξ * φ (segAff V i s)) := by
    unfold segAff; fun_prop
  calc (∫ s in (0:ℝ)..1, Real.exp (ξ * φ (segAff V i s))) ≤ ∫ _s in (0:ℝ)..1, K i :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
          intervalIntegrable_const (hK i hi')
    _ = K i := by simp

/-- A segment from a point of `interior T` to a point outside `interior T` meets `frontier T`. -/
lemma exists_segment_frontier {T : Set ℂ} (hT : IsClosed T) {p r : ℂ} (hp : p ∈ interior T)
    (hr : r ∉ interior T) : ∃ y ∈ segment ℝ p r, y ∈ frontier T := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hsub : segment ℝ p r ⊆ interior T ∪ Tᶜ := by
    intro y hy
    by_cases hyT : y ∈ T
    · left
      by_contra hyi
      exact hno y hy ⟨by rw [hT.closure_eq]; exact hyT, hyi⟩
    · exact Or.inr hyT
  have hdis : Disjoint (interior T) Tᶜ :=
    Set.disjoint_left.2 fun y hy hyc => hyc (interior_subset hy)
  have := (convex_segment p r).isPreconnected.subset_left_of_subset_union isOpen_interior
    hT.isOpen_compl hdis hsub ⟨p, left_mem_segment ℝ p r, hp⟩
  exact hr (this (right_mem_segment ℝ p r))

lemma segAff_mem_segment (V : ℕ → ℂ) (i : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    segAff V i s ∈ segment ℝ (V i) (V (i + 1)) := by
  refine ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, ?_⟩
  unfold segAff
  simp only [smul_sub]
  module

lemma norm_sub_lt_of_mem_ball {c x y : ℂ} {ρ : ℝ} (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) :
    ‖x - y‖ < 2 * ρ := by
  rw [← dist_eq_norm]
  have := dist_triangle_right x y c
  rw [mem_ball] at hx hy
  linarith

end DG
end LQGMetric
