/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Grid
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.20, first display (`eqn-holder-upper`) from Lemma 3.19 (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.20 (T:2317–2322) and its
proof (T:2327–2329): "The bound (eqn-holder-upper) follows from (eqn-ep-diam), applied with
`s = χ` and with `2^{-k}ε` for `k ∈ ℕ₀` in place of `ε`, together with a union bound over all
`z ∈ B_{ε𝕣}(K) ∩ (2^{-k-2}ε𝕣ℤ²)` and then over all `k ∈ ℕ₀`."

The paper leaves the choice of `k` and `z` for given `u, v` implicit. With the paper's literal
choices (radius `2^{-k}ε𝕣`, mesh `2^{-k-2}ε𝕣`) the two requirements `u, v ∈ B_{t𝕣}(z)` and
`B_{2t𝕣}(z) ⊆ B_{2|u−v|}(u)` (needed to pass from `D_h(·,·;B_{2t𝕣}(z))` to
`D_h(u,v;B_{2|u−v|}(u))`) force `t𝕣 ∈ (|u−v|/2, 3|u−v|/4)` up to the mesh, a window narrower than
the ratio 2. We use scales `t_k = ε(3/4)^k`, mesh `t_k𝕣/40` and `z` the grid point nearest the
midpoint of `u, v` (own elementary choice, proposed DEVIATIONS entry DFA7-1); the union bound is
the paper's (`grid_union_bound`). Points `z` are taken in `B̄_{R𝕣}(0)` with `K ⊆ B̄_{R−1}(0)`
and Lemma 3.19 is applied with the compact set `B̄_R(0)` in place of `K` (the paper's
`B_{ε𝕣}(K)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open Blueprint LQGDimension.LFPPRecords

/-- the scale selection: for `0 < d ≤ ε𝕣` and `λ, ρ ∈ (0,1)` some `t_k = ερ^k` has
`ρλd < t_k𝕣 ≤ λd` -/
theorem exists_scale {ε 𝕣 d ρ l : ℝ} (hε : 0 < ε) (h𝕣 : 0 < 𝕣) (hd : 0 < d) (hdε : d ≤ ε * 𝕣)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hl0 : 0 < l) (hl1 : l < 1) :
    ∃ k : ℕ, ε * ρ ^ k * 𝕣 ≤ l * d ∧ ρ * (l * d) < ε * ρ ^ k * 𝕣 := by
  classical
  have hex : ∃ k : ℕ, ε * ρ ^ k * 𝕣 ≤ l * d := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < l * d / (ε * 𝕣) by positivity) hρ1
    refine ⟨k, ?_⟩
    rw [lt_div_iff₀ (by positivity)] at hk
    nlinarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, mul_one] at this
    nlinarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
  push Not at hmin
  rw [hj, pow_succ]
  nlinarith

/-- deterministic part of the first display: the good events at all scales and grid points give
the bound for all `u ≠ v` with `|u − v| ≤ ε𝕣` -/
theorem ball_det (Dg : ContMetric) {F 𝕣 ε χ R : ℝ} (hF : 0 < F) (h𝕣 : 0 < 𝕣) (hε0 : 0 < ε)
    (hχ : 0 < χ) {u v : ℂ} (huv : u ≠ v) (hd : ‖u - v‖ ≤ ε * 𝕣) (hu : ‖u‖ + ε * 𝕣 ≤ R * 𝕣)
    (hgood : ∀ (k : ℕ) (a : ℤ × ℤ), a ∈ gridSel ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) (R * 𝕣) →
      internalDiam Dg (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a)
          ((ε * (3 / 4) ^ k) * 𝕣))
        (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a) (2 * (ε * (3 / 4) ^ k) * 𝕣)) ≤
        ENNReal.ofReal ((ε * (3 / 4) ^ k) ^ χ * F)) :
    ENNReal.ofReal F⁻¹ * Dg.internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
      ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ) := by
  set d := ‖u - v‖ with hd_def
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 huv)
  obtain ⟨k, hk1, hk2⟩ := exists_scale hε0 h𝕣 hd0 hd (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num) (by norm_num : (0 : ℝ) < 30 / 41) (by norm_num)
  set t := ε * (3 / 4 : ℝ) ^ k with ht
  have ht0 : 0 < t := by positivity
  set m := (1 / 40) * t * 𝕣 with hm
  have hm0 : 0 < m := by positivity
  set w : ℂ := u + (1 / 2 : ℂ) * (v - u) with hw
  set a := gridIdx m w with ha
  set z := gridPt m a with hz
  have hzw : ‖z - w‖ ≤ 2 * m := by
    rw [norm_sub_rev]; exact norm_sub_gridPt_le hm0 w
  have huw : ‖u - w‖ = d / 2 := by
    rw [hw, show u - (u + (1 / 2 : ℂ) * (v - u)) = (1 / 2 : ℂ) * (u - v) by ring, norm_mul]
    norm_num [hd_def]; ring
  have hvw : ‖v - w‖ = d / 2 := by
    rw [hw, show v - (u + (1 / 2 : ℂ) * (v - u)) = (1 / 2 : ℂ) * (v - u) by ring, norm_mul,
      norm_sub_rev v u]
    norm_num [hd_def]; ring
  have huz : ‖u - z‖ ≤ d / 2 + 2 * m := by
    calc ‖u - z‖ ≤ ‖u - w‖ + ‖w - z‖ := norm_sub_le_norm_sub_add_norm_sub u w z
      _ ≤ d / 2 + 2 * m := by rw [huw, norm_sub_rev]; linarith
  have hvz : ‖v - z‖ ≤ d / 2 + 2 * m := by
    calc ‖v - z‖ ≤ ‖v - w‖ + ‖w - z‖ := norm_sub_le_norm_sub_add_norm_sub v w z
      _ ≤ d / 2 + 2 * m := by rw [hvw, norm_sub_rev]; linarith
  have hu_in : u ∈ Metric.ball z (t * 𝕣) := by
    rw [Metric.mem_ball, dist_eq_norm]; rw [hm] at huz; nlinarith
  have hv_in : v ∈ Metric.ball z (t * 𝕣) := by
    rw [Metric.mem_ball, dist_eq_norm]; rw [hm] at hvz; nlinarith
  have hsub : Metric.ball z (2 * t * 𝕣) ⊆ Metric.ball u (2 * d) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    calc ‖y - u‖ ≤ ‖y - z‖ + ‖u - z‖ := by
          rw [norm_sub_rev u z]; exact norm_sub_le_norm_sub_add_norm_sub y z u
      _ < 2 * d := by rw [hm] at huz; nlinarith
  have hzR : a ∈ gridSel m (R * 𝕣) := by
    show ‖gridPt m a‖ ≤ R * 𝕣
    have hwn : ‖w‖ ≤ ‖u‖ + d / 2 := by
      calc ‖w‖ ≤ ‖u‖ + ‖w - u‖ := by
            calc ‖w‖ = ‖u + (w - u)‖ := by ring_nf
              _ ≤ ‖u‖ + ‖w - u‖ := norm_add_le _ _
        _ = ‖u‖ + d / 2 := by rw [norm_sub_rev, huw]
    calc ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          calc ‖z‖ = ‖w + (z - w)‖ := by ring_nf
            _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
      _ ≤ R * 𝕣 := by rw [hm] at hzw; nlinarith
  have hg := hgood k a hzR
  have hint : Dg.internal (Metric.ball u (2 * d)) u v ≤ ENNReal.ofReal (t ^ χ * F) :=
    (internal_anti Dg hsub u v).trans ((internal_le_internalDiam Dg hu_in hv_in).trans hg)
  have htd : t ≤ ‖(u - v) / 𝕣‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣, le_div_iff₀ h𝕣]
    nlinarith
  calc ENNReal.ofReal F⁻¹ * Dg.internal (Metric.ball u (2 * d)) u v
      ≤ ENNReal.ofReal F⁻¹ * ENNReal.ofReal (t ^ χ * F) := by gcongr
    _ = ENNReal.ofReal (t ^ χ) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hF.le)]
        congr 1; field_simp
    _ ≤ ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht0.le htd hχ.le)

end L320
end LQGMetric.DFGPS
