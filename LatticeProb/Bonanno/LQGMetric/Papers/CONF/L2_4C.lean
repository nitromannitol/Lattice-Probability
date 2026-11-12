/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L2_4C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4B
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-!
# CONF Lemma 2.4: approximation by geodesics to rational points

Source: CONF = Gwynne–Miller arXiv:1905.00381, `confluence-final.tex`, proof of Lemma 2.4
(l. 552–556): "Since `D_h` induces the Euclidean topology, for each `n` we can find
`q_n^- ∈ ℚ² ∖ 𝓑^•_s` such that `D_h(q_n^-, y_n^-)` is smaller than half of the distance from
`q_n^-` to any point of `∂𝓑^•_s` in the clockwise arc … Then the points `P_{q_n^-}(s)` converge
to `y` from the left … Arzelà–Ascoli … converge uniformly to … `P_y^-`."

* `jordan_local_inv`: points of `∂𝓑^•_s` close to `φ(t)` are `φ(r)` with `r` close to `t`
  (a positively oriented Jordan parametrization is a local homeomorphism; own elementary
  compactness argument, CONF uses "from the left" without comment);
* `exists_rat_near`: CONF's choice of `q_n`: `q ∈ ℚ² ∖ 𝓑^•_s` with `P_q(s) = φ(r)`, `r` close to
  `t` (we use `D(P_q(s), y_n) ≤ 2 D(q, y_n)`, which follows from the geodesic property, in place
  of CONF's half-distance condition);
* `side_approx`: given **uniqueness** of the one-sided limit, every `IsSideGeod` is a uniform
  limit on `[0, s]` of geodesics to rational points outside `𝓑^•_s` (the approximation clause
  of `CONFLem2_4`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.CONF

/-- a `2π`-periodic continuous map injective on `[0, 2π)` is locally invertible near each `t`
(up to `2π`-shifts) -/
theorem jordan_local_inv {φ : ℝ → ℂ} (hc : Continuous φ)
    (hper : ∀ t, φ (t + 2 * Real.pi) = φ t) (hinj : InjOn φ (Ico 0 (2 * Real.pi))) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ r, ‖φ r - φ t‖ < ρ → ∃ r', φ r' = φ r ∧ |r' - t| < ε := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hP : Function.Periodic φ (2 * Real.pi) := hper
  have hmod : ∀ a b : ℝ, φ (toIcoMod hp a b) = φ b := fun a b => by
    show φ (b - toIcoDiv hp a b • (2 * Real.pi)) = φ b
    exact hP.sub_zsmul_eq _
  set ε₁ := min ε Real.pi with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε Real.pi_pos
  set F : Set ℝ := Icc (t - Real.pi) (t + Real.pi) ∩ {r | ε₁ ≤ |r - t|} with hF
  have hFc : IsCompact F :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hC : IsCompact (φ '' F) := hFc.image hc
  have hnot : φ t ∉ φ '' F := by
    rintro ⟨r, hrF, hrt⟩
    have h1 := hinj (toIcoMod_mem_Ico' hp r) (toIcoMod_mem_Ico' hp t)
      (by rw [hmod, hmod, hrt])
    obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod hp).1 h1
    rw [zsmul_eq_mul] at hn
    have hab : |r - t| ≤ Real.pi := abs_sub_le_iff.2 ⟨by linarith [hrF.1.2], by linarith [hrF.1.1]⟩
    have hge : ε₁ ≤ |r - t| := hrF.2
    have hrt' : |r - t| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [show r - t = -((n : ℝ) * (2 * Real.pi)) by linarith, abs_neg, abs_mul,
        abs_of_pos hp]
    rcases eq_or_ne n 0 with h0 | h0
    · rw [h0, Int.cast_zero, abs_zero, zero_mul] at hrt'
      rw [hrt'] at hge
      linarith
    · have : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
      nlinarith [Real.pi_pos]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hC.isClosed.isOpen_compl (φ t) hnot
  refine ⟨ρ, hρ, fun r hr => ⟨toIcoMod hp (t - Real.pi) r, hmod _ _, ?_⟩⟩
  have hm := toIcoMod_mem_Ico hp (t - Real.pi) r
  by_contra hcon
  have hrF : toIcoMod hp (t - Real.pi) r ∈ F :=
    ⟨⟨hm.1, by linarith [hm.2]⟩, le_trans (min_le_left _ _) (not_lt.1 hcon)⟩
  exact hball (show φ (toIcoMod hp (t - Real.pi) r) ∈ Metric.ball (φ t) ρ by
    rw [hmod, Metric.mem_ball, dist_eq_norm]; exact hr) ⟨_, hrF, rfl⟩

section Det
variable {D : ContMetric} {z : ℂ} {s : ℝ}

/-- **CONF's choice of `q_n`** (l. 552–555) -/
theorem exists_rat_near
    (hbc : ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) → IsCompact A)
    (hgeo : ∀ a b : ℂ, ∃ η, IsGeod01 D a b η) (hs : 0 < s) {φ : ℝ → ℂ}
    (hφ : IsPosJordanParam (frontier (filledBall D z s)) z φ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℚ × ℚ) (G : ℝ → ℂ) (r : ℝ), ratPt q ∉ filledBall D z s ∧
      IsGeodesicL D G (D.1 (z, ratPt q)) z (ratPt q) ∧ s < D.1 (z, ratPt q) ∧
      φ r = G s ∧ |r - t| < ε := by
  have hbd := isBounded_ballM_of_bc hbc z s
  have hKc : IsClosed (filledBall D z s) := GM.jb_isClosed_filledBall hbd
  obtain ⟨ρ, hρ, hinv⟩ := jordan_local_inv hφ.1 hφ.2.1 hφ.2.2.1 t hε
  obtain ⟨δ, hδ, hδρ⟩ := D.2.euclidean_of_small (φ t) ρ hρ
  have hft : φ t ∈ frontier (filledBall D z s) := hφ.2.2.2.1 ▸ mem_range_self t
  have hU : IsOpen {w | D.1 (φ t, w) < δ / 2} :=
    isOpen_lt ((map_continuous D.1).comp (Continuous.prodMk_right (φ t))) continuous_const
  have hcl : φ t ∈ closure (filledBall D z s)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hft; exact hft.2
  obtain ⟨w, hwU, hwK⟩ := mem_closure_iff.1 hcl _ hU
    (show D.1 (φ t, φ t) < δ / 2 by rw [D.2.self_eq_zero]; positivity)
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 (hU.inter hKc.isOpen_compl) w ⟨hwU, hwK⟩
  obtain ⟨q, hq⟩ := exists_ratPt_dist_lt w hε'
  obtain ⟨hqU, hqK⟩ := hball hq
  have hqU' : D.1 (φ t, ratPt q) < δ / 2 := hqU
  have hzq : z ≠ ratPt q := fun h0 => hqK (h0 ▸ GM.jo_mem_filledBall_self hs)
  obtain ⟨η, hη⟩ := hgeo z (ratPt q)
  have hG := GM.gm_geodL_isGeodesicL hη hzq
  set L := D.1 (z, ratPt q) with hLdef
  have hsL : s < L := by
    by_contra hcon
    rcases (not_lt.1 hcon).lt_or_eq with h1 | h1
    · exact hqK (Or.inl (subset_closure (show D.1 (z, ratPt q) < s from h1)))
    · have := DD.cl_geod_mem_closure hG hs h1.symm.le
      rw [← h1, hG.2.2.1] at this
      exact hqK (Or.inl (h1 ▸ this))
  have hfr := DD.cl_geod_mem_frontier hG hs hsL hqK
  have hdt : D.1 (z, φ t) = s := GM.jp_frontier_subset_sphere hbd hft
  have hGs : D.1 (GM.geodL D z (ratPt q) η s, ratPt q) = L - s := by
    have := hG.2.2.2 s ⟨hs.le, hsL.le⟩ L ⟨hG.1, le_rfl⟩
    rw [hG.2.2.1, abs_of_nonneg (by linarith)] at this; exact this
  have htri1 := D.2.triangle z (φ t) (ratPt q)
  have htri2 := D.2.triangle (φ t) (ratPt q) (GM.geodL D z (ratPt q) η s)
  have hsym := D.2.symm (GM.geodL D z (ratPt q) η s) (ratPt q)
  have hclose : D.1 (φ t, GM.geodL D z (ratPt q) η s) < δ := by linarith
  have hn := hδρ _ hclose
  obtain ⟨r0, hr0⟩ : GM.geodL D z (ratPt q) η s ∈ range φ := hφ.2.2.2.1 ▸ hfr
  obtain ⟨r', hr'φ, hr't⟩ := hinv r0 (by rw [hr0, norm_sub_rev]; exact hn)
  exact ⟨q, _, r', hqK, hG, hsL, hr'φ.trans hr0, hr't⟩

end Det

end LQGMetric.CONF
