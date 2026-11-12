/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.TightAround at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightWind
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLoop
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# GM S2.4d, deterministic part: a short loop around an annulus (task P2-TIGHT)

Decision D-A3 (`decisions/DEC-A.md` (c), S2.4d): "Take `m` equally spaced points on the middle
circle. Join consecutive points by near-geodesics; by S2.4b and the inverse modulus they stay in
small Euclidean balls inside the annulus. The loop then has winding number 1 about 0, so it
disconnects the two boundaries … Its length is `≤ m·(small)`."

`aroundDist_le_of_events`: let `D` be a length metric, `α ∈ (0, 1)`, `ρ = (1 + α)/2`,
`g = (1 − α)/2`, `u_k = ρ e^{2πik/m}`, and suppose (in coordinates `u ↦ ru + z`) that
(E1) `D(ru + z, rv + z) > σ` whenever `u, v ∈ B̄₁(0)`, `|u − v| ≥ g/4`, and
(E2) `D(ru + z, rv + z) < τ` whenever `u, v ∈ B̄₁(0)`, `|u − v| ≤ b`, with `2τ ≤ σ`,
`|u_k − u_{k+1}| ≤ b` and `2πρ/m ≤ g/4`. Then the `D`-distance around `𝔸_{αr, r}(z)`
(DFGPS Def. 3.7, `ContMetric.aroundDist`) is at most `mσ`. Own argument (D-A3; DEVIATIONS DA5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric
namespace GM
namespace Tight

open MetricGeometry QuantumZipper.CA.Topo

/-- the `k`-th of `m` equally spaced points on `∂B_ρ(0)` -/
def ringPt (ρ : ℝ) (m k : ℕ) : ℂ := circleMap 0 ρ (2 * π * k / m)

lemma norm_ringPt {ρ : ℝ} (hρ : 0 ≤ ρ) (m k : ℕ) : ‖ringPt ρ m k‖ = ρ := by
  simp [ringPt, norm_circleMap_zero, abs_of_nonneg hρ]

lemma norm_circleMap_sub_circleMap_le {R : ℝ} (hR : 0 ≤ R) (θ θ' : ℝ) :
    ‖circleMap 0 R θ - circleMap 0 R θ'‖ ≤ R * |θ - θ'| := by
  have := (lipschitzWith_circleMap 0 R).dist_le_mul θ θ'
  rw [dist_eq_norm, Real.dist_eq] at this
  simpa [Real.coe_nnabs, abs_of_nonneg hR] using this

lemma mul_circleMap (r R θ : ℝ) : (r : ℂ) * circleMap 0 R θ = circleMap 0 (r * R) θ := by
  simp only [circleMap, zero_add]; push_cast; ring

/-- **Deterministic core of GM S2.4d.** -/
theorem aroundDist_le_of_events {D : ContMetric} (hlen : D.IsLength) {r : ℝ} (hr : 0 < r)
    (z : ℂ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {σ τ b : ℝ} (hτ : 0 < τ) (hτσ : 2 * τ ≤ σ)
    {m : ℕ} (hm : 0 < m)
    (hstep : ∀ k, ‖ringPt ((1 + α) / 2) m k - ringPt ((1 + α) / 2) m (k + 1)‖ ≤ b)
    (hmg : (1 + α) / 2 * (2 * π / m) ≤ (1 - α) / 2 / 4)
    (hE1 : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, (1 - α) / 2 / 4 ≤ ‖u - v‖ →
      σ < D.1 ((r : ℂ) * u + z, (r : ℂ) * v + z))
    (hE2 : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1, ‖u - v‖ ≤ b →
      D.1 ((r : ℂ) * u + z, (r : ℂ) * v + z) < τ) :
    D.aroundDist {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} (sphere z (α * r)) (sphere z r) ≤
      ENNReal.ofReal (m * σ) := by
  set ρ : ℝ := (1 + α) / 2 with hρ
  set g : ℝ := (1 - α) / 2 with hg
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  have hg0 : 0 < g := by rw [hg]; linarith
  have hρ1 : ρ + g / 4 < 1 := by rw [hρ, hg]; linarith
  have hu : ∀ k, ringPt ρ m k ∈ closedBall (0 : ℂ) 1 := fun k => by
    rw [mem_closedBall, dist_zero_right, norm_ringPt hρ0]; linarith
  let x : ℕ → ℂ := fun k => (r : ℂ) * ringPt ρ m k + z
  let w : ℕ → D.Space := fun k => D.pt (x k)
  -- near-geodesics between consecutive points
  have hpath : ∀ k, ∃ p : Path (w k) (w (k + 1)), pathLength p < ENNReal.ofReal σ := fun k => by
    obtain ⟨p, hp⟩ := hlen (w k) (w (k + 1)) τ hτ
    refine ⟨p, hp.trans_lt (lt_of_lt_of_le (b := ENNReal.ofReal τ + ENNReal.ofReal τ) ?_ ?_)⟩
    · refine ENNReal.add_lt_add_right ENNReal.ofReal_ne_top ?_
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hτ).2 (hE2 _ (hu k) _ (hu (k + 1)) (hstep k))
    · rw [← ENNReal.ofReal_add hτ.le hτ.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  choose γ hγ using hpath
  -- the paths stay in small Euclidean balls
  have hball : ∀ k t, ‖D.unpt ((γ k).extend t) - x k‖ < g / 4 * r := by
    intro k t
    by_contra hcon
    push Not at hcon
    have hf : Continuous fun t' => ‖D.unpt ((γ k).extend t') - x k‖ :=
      ((D.continuous_unpt.comp (γ k).continuous_extend).sub continuous_const).norm
    have hf0 : ‖D.unpt ((γ k).extend 0) - x k‖ = 0 := by
      rw [Path.extend_zero]; simp [w]
    have ht0 : 0 ≤ t := by
      by_contra ht
      rw [(γ k).extend_of_le_zero (by linarith)] at hcon
      simp only [w, ContMetric.unpt_pt, sub_self, norm_zero] at hcon
      nlinarith
    obtain ⟨t', -, ht'⟩ := intermediate_value_Icc ht0 hf.continuousOn
      ⟨by rw [hf0]; positivity, hcon⟩
    set y : ℂ := D.unpt ((γ k).extend t') with hy
    set u' : ℂ := (y - z) / r with hu'
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have hyu : y = (r : ℂ) * u' + z := by rw [hu']; field_simp; ring
    have hdist : ‖u' - ringPt ρ m k‖ = g / 4 := by
      have e : u' - ringPt ρ m k = (y - x k) / r := by
        rw [hu']; simp only [x]; field_simp; ring
      rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simp only at ht'
      rw [← hy] at ht'
      rw [ht']; field_simp
    have hu'1 : u' ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖u'‖ ≤ ‖u' - ringPt ρ m k‖ + ‖ringPt ρ m k‖ := norm_le_norm_sub_add _ _
        _ = g / 4 + ρ := by rw [hdist, norm_ringPt hρ0]
        _ ≤ 1 := by linarith
    have h1 := hE1 _ (hu k) _ hu'1 (by rw [norm_sub_rev, hdist])
    have h2 : edist (w k) ((γ k).extend t') ≤ pathLength (γ k) :=
      edist_extend_le_pathLength _ _
    have h3 : edist (w k) ((γ k).extend t') = ENNReal.ofReal (D.1 (x k, y)) := by
      rw [edist_dist]; rfl
    rw [h3, hyu] at h2
    have := (h2.trans_lt (hγ k))
    have hnn : 0 ≤ D.1 (x k, (r : ℂ) * u' + z) := (dist_nonneg : 0 ≤ dist (D.pt (x k)) (D.pt _))
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn] at this
    exact absurd h1 (not_lt.2 this.le)
  -- the loop
  let Q : ℝ → D.Space := concatCurve w γ m
  let P : ℝ → ℂ := fun t => D.unpt (Q t)
  have hPc : Continuous P := D.continuous_unpt.comp (continuous_concatCurve w γ m)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hgr0 : 0 < g * r := mul_pos hg0 hr
  have hgr : g * r = ρ * r - α * r := by rw [hρ, hg]; ring
  have hgr' : g * r = r - ρ * r := by rw [hρ, hg]; ring
  have hnear : ∀ t ∈ Icc (0 : ℝ) m, ∃ j < m, t ∈ Icc (j : ℝ) (j + 1) ∧
      ‖P t - x j‖ < g / 4 * r := by
    intro t ht
    obtain ⟨j, hj, hjt, he⟩ := concatCurve_mem w γ m hm ht
    refine ⟨j, hj, hjt, ?_⟩
    show ‖D.unpt (concatCurve w γ m t) - x j‖ < g / 4 * r
    rw [he]
    exact hball j _
  have hxz : ∀ j, ‖x j - z‖ = ρ * r := fun j => by
    simp only [x, add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, norm_ringPt hρ0]
    ring
  -- the loop lies in the annulus
  have hA : P '' Icc 0 m ⊆ {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨j, -, -, hj⟩ := hnear t ht
    have h1 : ‖P t - z‖ ≤ ‖P t - x j‖ + ‖x j - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖x j - z‖ ≤ ‖x j - P t‖ + ‖P t - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (x j) (P t)] at h2
    rw [hxz] at h1 h2
    constructor <;> linarith
  -- the loop as a map on `[0, 1]`
  have hQ0 : Q 0 = w 0 := by
    have := concatCurve_eqOn w γ m 0 hm (show (0 : ℝ) ∈ Icc ((0 : ℕ) : ℝ) ((0 : ℕ) + 1) by simp)
    simp only [Nat.cast_zero, sub_zero, Path.extend_zero] at this
    exact this
  have hwm : w m = w 0 := by
    simp only [w, x, ringPt]
    congr 3
    rw [mul_div_assoc, div_self hm'.ne', mul_one, Nat.cast_zero, mul_zero, zero_div]
    exact (periodic_circleMap 0 ρ).eq
  let Γ : C(unitInterval, ℂ) :=
    ⟨fun t => P (m * t), hPc.comp (continuous_const.mul continuous_subtype_val)⟩
  have hΓc : Γ 0 = Γ 1 := by
    show P (m * ((0 : unitInterval) : ℝ)) = P (m * ((1 : unitInterval) : ℝ))
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
    show D.unpt (Q 0) = D.unpt (concatCurve w γ m m)
    rw [hQ0, concatCurve_of_ge w γ m m le_rfl, hwm]
  have htm : ∀ t : unitInterval, (m : ℝ) * t ∈ Icc (0 : ℝ) m := fun t =>
    ⟨mul_nonneg hm'.le t.2.1, by nlinarith [t.2.2]⟩
  have hclose : ∀ t : unitInterval,
      ‖Γ t - (z + circleLoop (ρ * r) t)‖ < min (ρ * r - α * r) (r - ρ * r) := by
    intro t
    obtain ⟨j, -, hjt, hj⟩ := hnear _ (htm t)
    have hc : ‖x j - (z + circleLoop (ρ * r) t)‖ ≤ g / 4 * r := by
      have e : x j - (z + circleLoop (ρ * r) t) =
          circleMap 0 (r * ρ) (2 * π * j / m) - circleMap 0 (r * ρ) (2 * π * t) := by
        simp only [x, ringPt, circleLoop, ContinuousMap.coe_mk, mul_circleMap, mul_comm ρ r]
        ring
      rw [e]
      refine (norm_circleMap_sub_circleMap_le (by positivity) _ _).trans ?_
      have habs : |2 * π * j / m - 2 * π * t| ≤ 2 * π / m := by
        have e2 : 2 * π * j / m - 2 * π * t = 2 * π / m * (j - m * t) := by
          field_simp
        rw [e2, abs_mul, abs_of_pos (by positivity)]
        have : |(j : ℝ) - m * t| ≤ 1 := abs_le.2 ⟨by linarith [hjt.2], by linarith [hjt.1]⟩
        nlinarith [show (0 : ℝ) < 2 * π / m by positivity]
      calc r * ρ * |2 * π * j / m - 2 * π * t| ≤ r * ρ * (2 * π / m) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = r * (ρ * (2 * π / m)) := by ring
        _ ≤ r * (g / 4) := mul_le_mul_of_nonneg_left hmg hr.le
        _ = g / 4 * r := by ring
    have h1 : ‖Γ t - (z + circleLoop (ρ * r) t)‖ ≤
        ‖Γ t - x j‖ + ‖x j - (z + circleLoop (ρ * r) t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖Γ t - x j‖ < g / 4 * r := hj
    rw [min_eq_left (by linarith)]
    linarith
  have hdisc : Disconnects (P '' Icc 0 m) (sphere z (α * r)) (sphere z r) := by
    refine (disconnects_of_near_circle hΓc (by positivity) (by linarith) (by linarith)
      hclose).mono ?_ subset_rfl subset_rfl
    rintro _ ⟨t, rfl⟩
    exact ⟨m * t, htm t, rfl⟩
  have hσ : 0 ≤ σ := by linarith
  have hlenP : D.len P 0 m ≤ ENNReal.ofReal (m * σ) := by
    have e : D.len P 0 m = curveLength Q 0 m := rfl
    rw [e, curveLength_concatCurve]
    calc ∑ j ∈ Finset.range m, pathLength (γ j) ≤ ∑ _j ∈ Finset.range m, ENNReal.ofReal σ :=
          Finset.sum_le_sum fun j _ => (hγ j).le
      _ = ENNReal.ofReal (m * σ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  refine le_trans ?_ hlenP
  unfold ContMetric.aroundDist
  exact iInf_le_of_le 0 (iInf_le_of_le m (iInf_le_of_le P (iInf_le_of_le hm'.le
    (iInf_le_of_le hPc.continuousOn (iInf_le_of_le hA (iInf_le_of_le hdisc le_rfl))))))

end Tight
end GM
end LQGMetric
