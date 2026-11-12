/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiB1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12

/-!
# The D97 sandwich with the wall `K` kept in the lower half (D129, P-129B)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Prop 5.1, l. 2340–2350
((eq-geodesic-range)): on the event that balls meeting `∂𝕍_{u,λ}` and leaving `𝕍_{u,2λ}` are
heavy, `min_{x ∈ ∂𝕍_{u,λ}} D(u,x) = min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}(u,x)`. Decision D129
(`decisions/DEC-129.md` §2 (S5), §4 P-129B).

* `dzzWall_dzzWall_of_subset`: `dzzWall K (dzzWall 𝕍 ν) = dzzWall K ν` for `K ⊆ 𝕍`;
* `lgd_sandwich_dzzWall_lower_K`: the lower half of `lgd_sandwich_dzzWall` (S3P32X) keeping the
  wall `K` (same proof, without the last step `dzzWall_anti`, which drops `K` to `𝕍`);
* `ae_lgd_sandwich_wick_K`: `ae_lgd_sandwich_wick` (S3P32W13) with this lower half.

**DEVIATIONS DV-D129-3**: (eq-geodesic-range) is used one-sidedly (`≤`), with the wall kept.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- `dzzWall K (dzzWall 𝕍 ν) = dzzWall K ν` for `K ⊆ 𝕍`: the outer wall is absorbed. -/
lemma dzzWall_dzzWall_of_subset {K : Set ℂ} (hK : K ⊆ dzzV) (ν : Measure ℂ) :
    dzzWall K (dzzWall dzzV ν) = dzzWall K ν := by
  ext s hs
  simp only [dzzWall, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hs]
  rw [add_assoc]
  congr 1
  have hle : volume (s ∩ dzzVᶜ) ≤ volume (s ∩ Kᶜ) :=
    measure_mono (inter_subset_inter_right _ (compl_subset_compl.2 hK))
  rcases eq_or_ne (volume (s ∩ Kᶜ)) 0 with h0 | h0
  · have h1 : volume (s ∩ dzzVᶜ) = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hle)
    rw [h0, h1]; simp
  · rw [ENNReal.top_mul h0, add_top]

/-- **The lower half of the sandwich, wall kept** (DZZ l. 2340–2350; copy of the first half of
`lgd_sandwich_dzzWall`, S3P32X): if `ν(B) ≤ e^b μ(B)` for the balls inside the closed `K` and the
balls of `μ`-mass `≤ δ²` meeting `closure U` lie in `K`, then for `u ∈ U`, `v ∉ U`,
`min_{x ∈ ∂U} D^K_{δe^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v)`. -/
theorem lgd_sandwich_dzzWall_lower_K {μ ν : Measure ℂ} {b δ : ℝ} {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsClosed K)
    (hlow : ∀ (x : ℚ × ℚ) (r : ℝ), Metric.ball (ratPt x) r ⊆ K →
      ν (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp b) * μ (Metric.ball (ratPt x) r))
    {u v : ℂ} (hu : u ∈ U) (hv : v ∉ U)
    (hheavy : ∀ (c : ℚ × ℚ) (ρ : ℝ), (Metric.ball (ratPt c) ρ ∩ closure U).Nonempty →
      μ (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) → Metric.ball (ratPt c) ρ ⊆ K) :
    lgdMinSet (dzzWall K ν) (δ * Real.exp (b / 2)) {u} (frontier U) ≤ lgdDZZ μ δ u v := by
  have hexp : ENNReal.ofReal (Real.exp b) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos b)).ne'
  refine le_trans ?_ (lgdMinSet_dzzWall_le_of_exit μ δ hU hu hv hheavy)
  refine iInf₂_mono fun x _ => iInf₂_mono fun y _ => ?_
  have h2 := lgdDZZ_le_of_ball_le (dzzWall_ball_le hK hexp hlow) (δ * Real.exp (b / 2)) x y
  rwa [neg_div, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h2

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

/-- **`ae_lgd_sandwich_wick` with the `K`-walled lower half** (D129 §4 P-129B): under the
hypotheses of `ae_lgd_sandwich_wick` (S3P32W13), a.s. for all small `δ`, all `u ∈ U`, `v ∉ U`,
`min_{x ∈ ∂U} D^K_{M^W}(δ e^{b/2})(u, x) ≤ D_δ(u, v) ≤ D^𝕍_{M^W}(δ e^{−a/2})(u, v)`. -/
theorem ae_lgd_sandwich_wick_K (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {U K : Set ℂ} (hU : IsOpen U) (hC : IsCompact (closure U)) (hK : IsCompact K)
    (hKV : K ⊆ openSquare) {r : ℝ} (hr : 0 < r)
    (hCK : ∀ p ∈ closure U, ∀ z ∉ K, 4 * r ≤ dist p z)
    (hCV : thickening (4 * r) (closure U) ⊆ openSquare) :
    ∃ a b : ℝ, ∀ᵐ ω ∂P', ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ u ∈ U, ∀ v ∉ U,
      lgdMinSet (dzzWall K (dzzMuIn γ W ω)) (δ * Real.exp (b / 2)) {u} (frontier U) ≤
          lgdDZZ (qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare) δ u v ∧
        lgdDZZ (qAreaMeasureOn γ (GMCIdent3.wnField W ω) openSquare) δ u v ≤
          lgdDZZ (dzzMuIn γ W ω) (δ * Real.exp (-a / 2)) u v := by
  obtain ⟨b, hb⟩ := wickArea_le_of_compact γ hK hKV
  refine ⟨γ ^ 2 / 2 * Real.log 3, b, ?_⟩
  filter_upwards [ae_exists_heavy_wn hW hγ hγ2 hC hr hCK hCV] with ω ⟨δ₀, hδ₀, hheavy⟩
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ u hu v hv => ⟨?_, ?_⟩⟩
  · rw [show dzzMuIn γ W ω = dzzWall dzzV (wickQArea γ W ω) from rfl,
      dzzWall_dzzWall_of_subset (hKV.trans openSquare_subset_dzzV)]
    exact lgd_sandwich_dzzWall_lower_K hU hK.isClosed
      (fun x ρ hsub => hb _ _ measurableSet_ball hsub) hu hv (hheavy δ hδ hδδ₀)
  · exact (lgd_sandwich_dzzWall hU hK.isClosed (hKV.trans openSquare_subset_dzzV)
      (fun x ρ _ => le_wickQArea γ W ω measurableSet_ball)
      (fun x ρ hsub => hb _ _ measurableSet_ball hsub) hu hv (hheavy δ hδ hδδ₀)).2

end DZZ
end LQGMetric
