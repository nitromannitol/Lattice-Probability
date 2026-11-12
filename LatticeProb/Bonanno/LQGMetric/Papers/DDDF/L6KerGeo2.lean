/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerGeo2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerGeom

/-!
# DDDF Lemma 6, Step 3: geometry of `F` on `K` without convexity

DDDF (arXiv:1904.08021, `tightness.tex` l. 539–545) assume `U`, `V`, `K` convex and use
`|F(x) − F(y)|/|F'(y)| ≥ |x − y|/C` (l. 643, via `‖(F⁻¹)'‖`). The maps of DDDF Lemma 12′ are not
known to have convex domains, so we prove the needed facts on `K` directly:

* `exists_far_lower`: `|F x − F y| ≥ ρ > 0` for `x ∈ K`, `y ∈ U`, `|x − y| ≥ ε` (injectivity and
  the open mapping theorem, QuantumZipper `CA.isOpen_image_of_injOn'`, plus compactness of `K`);
* `exists_geom`: `B(x, ε) ⊆ U` for `x ∈ K`, and `κ|x − y| ≤ |F x − F y|` for `x ∈ K`, `y ∈ U`
  (Taylor near the diagonal, `exists_far_lower` and boundedness of `U` away from it).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

/-! ### Geometry without convexity of `U`, `V`, `K` -/

lemma confHyp_mono (h : ConfHyp F U) {S : Set ℂ} (hS : IsOpen S) (hSU : S ⊆ U) : ConfHyp F S :=
  ⟨hS, h.diff.mono hSU, h.inj.mono hSU, fun y hy => h.deriv_ne y (hSU hy)⟩

/-- Injectivity and the open mapping theorem, uniformly on `K` (DDDF l. 619–625, case (b):
`|F x − F y|` bounded below for `|x − y| ≥ ε`). -/
lemma exists_far_lower (h : ConfHyp F U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ U, ε ≤ ‖x - y‖ → ρ ≤ ‖F x - F y‖ := by
  have hloc : ∀ x₀ ∈ K, ∀ᶠ z : ℝ × ℂ in nhds ((0 : ℝ), x₀),
      ∀ y ∈ U, ε ≤ ‖z.2 - y‖ → z.1 ≤ ‖F z.2 - F y‖ := by
    intro x₀ hx₀
    have hO : IsOpen (F '' (U ∩ ball x₀ (ε / 2))) :=
      QuantumZipper.CA.isOpen_image_of_injOn' (h.isOpen.inter isOpen_ball)
        (h.diff.mono inter_subset_left) (h.inj.mono inter_subset_left)
    obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.1 hO (F x₀)
      (mem_image_of_mem F ⟨hKU hx₀, mem_ball_self (by positivity)⟩)
    have hc : ContinuousAt F x₀ := h.diff.continuousOn.continuousAt (h.isOpen.mem_nhds (hKU hx₀))
    have h1 : ∀ᶠ x in nhds x₀, dist (F x) (F x₀) < r₀ / 2 :=
      hc.eventually (ball_mem_nhds _ (by positivity))
    have h2 : ∀ᶠ x in nhds x₀, dist x x₀ < ε / 2 := ball_mem_nhds _ (by positivity)
    have h3 : ∀ᶠ ρ in nhds (0 : ℝ), ρ < r₀ / 2 := eventually_lt_nhds (by positivity)
    rw [nhds_prod_eq]
    filter_upwards [h3.prod_mk (h1.and h2)] with z hz y hy hxy
    obtain ⟨hρ, hF, hd⟩ := hz
    refine le_of_not_gt fun hlt => ?_
    have hmem : F y ∈ F '' (U ∩ ball x₀ (ε / 2)) := hsub (by
      rw [mem_ball, dist_eq_norm]
      calc ‖F y - F x₀‖ ≤ ‖F z.2 - F y‖ + ‖F z.2 - F x₀‖ := by
            rw [norm_sub_rev (F z.2) (F y)]
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < r₀ / 2 + r₀ / 2 := by
            have := hF; rw [dist_eq_norm] at this; linarith
        _ = r₀ := by ring)
    obtain ⟨y', hy', he⟩ := hmem
    have hyy : y' = y := h.inj hy'.1 hy he
    have hy2 := hy'.2
    rw [hyy, mem_ball, dist_eq_norm] at hy2
    have : ‖z.2 - y‖ < ε := by
      calc ‖z.2 - y‖ ≤ ‖z.2 - x₀‖ + ‖y - x₀‖ := by
            rw [norm_sub_rev y x₀]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε / 2 + ε / 2 := by
            have := hd; rw [dist_eq_norm] at this; linarith
        _ = ε := by ring
    linarith
  have hev := hK.eventually_forall_of_forall_eventually
    (P := fun ρ x => ∀ y ∈ U, ε ≤ ‖x - y‖ → ρ ≤ ‖F x - F y‖) hloc
  obtain ⟨ρ, hρ, hρ0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ nhdsWithin 0 (Ioi 0))).exists
  exact ⟨ρ, hρ0, fun x hx y hy hxy => hρ x hx y hy hxy⟩

/-- **Geometric package** (no convexity): `ε`-balls around `K` lie in `U`, `ε M₂ ≤ 1/2`, and the
bi-Lipschitz lower bound `κ |x − y| ≤ |F x − F y|` for `x ∈ K`, `y ∈ U` (DDDF l. 643, which uses
`‖(F⁻¹)'‖` and convexity; here near the diagonal by Taylor, away from it by
`exists_far_lower` and boundedness of `U`). -/
lemma exists_geom (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M₂ : ℝ} (hM20 : 0 ≤ M₂)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε κ, 0 < ε ∧ 0 < κ ∧ κ ≤ 1 ∧ ε * M₂ ≤ 1 / 2 ∧ (∀ x ∈ K, ball x ε ⊆ U) ∧
      ∀ x ∈ K, ∀ y ∈ U, κ * ‖x - y‖ ≤ ‖F x - F y‖ := by
  obtain ⟨d, hd, hdK⟩ := exists_dist_compl h.isOpen hK hKU
  set ε := min d (1 / (2 * (M₂ + 1))) with hεdef
  have hε : 0 < ε := lt_min hd (by positivity)
  have hεM : ε * M₂ ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (M₂ + 1)) := min_le_right _ _
    have h2 : ε * (2 * (M₂ + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hball : ∀ x ∈ K, ball x ε ⊆ U := fun x hx y hy => by
    by_contra hyU
    have := hdK x hx y hyU
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
    linarith [min_le_left d (1 / (2 * (M₂ + 1)))]
  obtain ⟨ρ, hρ, hfar⟩ := exists_far_lower h hK hKU hε
  set D := max (diam U) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  refine ⟨ε, min (1 / 2) (ρ / D), hε, lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans (by norm_num), hεM, hball, fun x hx y hy => ?_⟩
  by_cases hxy : ε ≤ ‖x - y‖
  · have hr : ‖x - y‖ ≤ D := by
      rw [← dist_eq_norm]; exact (dist_le_diam_of_mem hUb (hKU hx) hy).trans (le_max_left _ _)
    calc min (1 / 2) (ρ / D) * ‖x - y‖ ≤ ρ / D * D :=
          mul_le_mul (min_le_right _ _) hr (norm_nonneg _) (by positivity)
      _ = ρ := by field_simp
      _ ≤ _ := hfar x hx y hy hxy
  · push Not at hxy
    have hyb : y ∈ ball x ε := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hxy
    have hB := hball x hx
    have hT := norm_taylor_le (confHyp_mono h isOpen_ball hB) (convex_ball x ε)
      (fun z hz => hM2 z (hB hz)) (mem_ball_self hε) hyb
    have hr := norm_nonneg (x - y)
    have h1 : ‖deriv F y * (x - y)‖ ≤ ‖F x - F y‖ + M₂ * ‖x - y‖ ^ 2 := by
      calc ‖deriv F y * (x - y)‖ = ‖(F x - F y) - (F x - F y - deriv F y * (x - y))‖ := by
            congr 1; ring
        _ ≤ ‖F x - F y‖ + ‖F x - F y - deriv F y * (x - y)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hT]
    rw [norm_mul] at h1
    have h2 : ‖x - y‖ ≤ ‖deriv F y‖ * ‖x - y‖ := le_mul_of_one_le_left hr (hF1 y hy)
    have h3 : M₂ * ‖x - y‖ ^ 2 ≤ ‖x - y‖ / 2 := by
      have : M₂ * ‖x - y‖ ≤ 1 / 2 := by nlinarith
      nlinarith
    calc min (1 / 2) (ρ / D) * ‖x - y‖ ≤ 1 / 2 * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr
      _ ≤ _ := by linarith

end DDDF
end LQGMetric
