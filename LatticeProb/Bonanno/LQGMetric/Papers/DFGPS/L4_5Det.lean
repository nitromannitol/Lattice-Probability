/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L4_5Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Grid
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 4.5: deterministic part and Prop 3.1 in the whole plane (task P2-DFA10)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 4.5
(`lem-geo-bdy-ratio`, T:2645–2667): "If `z, w ∈ B_{ε^{-M}𝕣}(0)` with `|z − w| ≥ ε𝕣`, then any
path from `z` to `w` must cross between the inner and outer boundaries of an annulus
`B_{ε𝕣/2}(x) ∖ B_{ε𝕣/4}(x)` for some grid point `x`" (T:2660–2661), with
Proposition 3.1 at the grid points (T:2647–2650, `eqn-geo-bdy-across`).

Grid (own elementary choice, as in `L3_22.lean`): the mesh `m` with `8m ≤ ρ = ε𝕣`; the grid
point `x` below `z` has `|z − x| ≤ 2m ≤ ρ/4`, so `|w − x| ≥ ρ/2`, and in the length metric
`D_h` (Axiom I) `D_h(z, w) ≥ inf_{u ∈ ∂B_{ρ/4}(x), v ∈ ∂B_{ρ/2}(x)} D_h(u, v)`
(`GM.Tight.le_of_forall_crossing`). Prop 3.1 is applied with `U = ℂ`, `K₁ = B̄_{1/4}(0)`,
`K₂ = ∂B_{1/2}(0)`, so that `D_h(·,·; ℂ) = D_h`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L45

open Blueprint LQGDimension.LFPPRecords

lemma scaleSet_univ {r : ℝ} (hr : 0 < r) (z : ℂ) : scaleSet r z univ = univ := by
  refine eq_univ_of_forall fun w => ⟨(w - z) / r, mem_univ _, ?_⟩
  have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  field_simp; ring

/-- `D(·,·) ≥ s` across `A`, `B` from `D(A, B; ℂ) ≥ s` for a length metric -/
lemma le_of_setDistIn_univ (Dg : ContMetric) (hlen : Dg.IsLength) {A B : Set ℂ} {s : ℝ}
    (h : ENNReal.ofReal s ≤ setDistIn Dg A B univ) {u v : ℂ} (hu : u ∈ A) (hv : v ∈ B) :
    s ≤ Dg.1 (u, v) := by
  have h1 : setDistIn Dg A B univ ≤ Dg.internal univ u v :=
    (biInf_le _ hu).trans (biInf_le _ hv)
  rw [Dg.internal_univ_of_isLength hlen] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (ContMetric.nonneg Dg _ _)).1 (h.trans h1)

/-- `ofReal D(u, v) ≤ D(u, v; V)` -/
lemma ofReal_le_internal (Dg : ContMetric) (V : Set ℂ) (u v : ℂ) :
    ENNReal.ofReal (Dg.1 (u, v)) ≤ Dg.internal V u v := by
  rw [← ContMetric.edist_pt]
  exact MetricGeometry.edist_le_internalEDist _ _ _

/-- `sup_{u,v∈A} D(u,v) ≤ sup_{u,v∈A'} D(u,v; V)` for `A ⊆ A'` -/
lemma supDist_le_internalDiam (Dg : ContMetric) {A A' V : Set ℂ} (hA : A ⊆ A') :
    supDist Dg A ≤ internalDiam Dg A' V :=
  iSup₂_le fun u hu => iSup₂_le fun v hv =>
    (ofReal_le_internal Dg V u v).trans (le_iSup₂_of_le u (hA hu) (le_iSup₂_of_le v (hA hv) le_rfl))

/-- **Deterministic part of Lemma 4.5** (T:2660–2662) -/
theorem det_lower (Dg : ContMetric) (hlen : Dg.IsLength) {ρ R m L : ℝ} (hm : 0 < m)
    (hmρ : 8 * m ≤ ρ) (hmR : 2 * m ≤ R)
    (hcross : ∀ a : ℤ × ℤ, ‖gridPt m a‖ < 2 * R → ∀ u ∈ sphere (gridPt m a) (ρ / 4),
      ∀ v ∈ sphere (gridPt m a) (ρ / 2), L ≤ Dg.1 (u, v))
    {z w : ℂ} (hz : ‖z‖ < R) (hzw : ρ ≤ ‖z - w‖) : L ≤ Dg.1 (z, w) := by
  set x := gridPt m (gridIdx m z)
  have hzx : ‖z - x‖ ≤ 2 * m := norm_sub_gridPt_le hm z
  have hx : ‖x‖ < 2 * R := by
    have : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
      calc ‖x‖ = ‖z - (z - x)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le _ _
    linarith
  have hwx : ρ / 2 ≤ ‖w - x‖ := by
    have : ‖z - w‖ ≤ ‖z - x‖ + ‖w - x‖ := by
      calc ‖z - w‖ = ‖(z - x) - (w - x)‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖w - x‖ := norm_sub_le _ _
    linarith
  exact GM.Tight.le_of_forall_crossing hlen (by linarith) (by linarith) hwx
    (hcross _ hx)

/-- **Prop 3.1 at every centre** for `B̄_{1/4}(0) → ∂B_{1/2}(0)` in `ℂ` (`eqn-geo-bdy-across`) -/
theorem prop3_1_centre_plane (h31 : Prop3_1) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ) :
    ∀ p : ℝ, 0 < p → ∃ C A₀ : ℝ, ∀ A, A₀ < A → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : ℂ,
      μ {g | ENNReal.ofReal (A⁻¹ * scaleFac (xiGamma γ) c g 𝕣 z) ≤
            setDistIn (D g) (closedBall z (1 / 4 * 𝕣)) (sphere z (1 / 2 * 𝕣)) univ}ᶜ ≤
        ENNReal.ofReal (C * A ^ (-p)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hdis : Disjoint (closedBall (0 : ℂ) (1 / 4)) (sphere 0 (1 / 2)) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    rw [mem_closedBall] at hw1
    rw [mem_sphere] at hw2
    linarith
  have hn₁ : ¬ (closedBall (0 : ℂ) (1 / 4)).Subsingleton := by
    intro hs
    have := hs (x := (1 / 4 : ℂ)) (by norm_num) (y := (-1 / 4 : ℂ)) (by norm_num)
    norm_num at this
  have hn₂ : ¬ (sphere (0 : ℂ) (1 / 2)).Subsingleton := by
    intro hs
    have := hs (x := (1 / 2 : ℂ)) (by norm_num) (y := (-1 / 2 : ℂ)) (by norm_num)
    norm_num at this
  intro p hp
  obtain ⟨C, A₀, h⟩ := prop3_1_centre h31 hγ0 hγ2 hD isOpen_univ isConnected_univ
    (isCompact_closedBall 0 (1 / 4)) (isCompact_sphere 0 (1 / 2))
    (isConnected_closedBall (by norm_num)) (isConnected_sphere hrank 0 (by norm_num))
    (subset_univ _) (subset_univ _) hdis hn₁ hn₂ hμ p hp
  refine ⟨C, A₀, fun A hA r hr z => le_trans (measure_mono ?_) (h A hA r hr z)⟩
  intro g hg hE
  apply hg
  rw [scaleSet_closedBall hr, scaleSet_sphere hr, scaleSet_univ hr] at hE
  exact hE.1

end L45
end LQGMetric.DFGPS
