/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K5b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_12

/-!
# CONF Theorem 3.9, packet J6d (D130 §4): scale invariance of the arcs `I^{(t)}`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1559–1561 with `h` "viewed modulo additive constant" (C:1154): adding a constant `c` to `h`
multiplies `D_h` by `e^{ξc}` (Weyl scaling, GM (1.6)), and the arcs `I^{(t)}` (C:1543) are
unchanged at the scaled radius. Deterministic content, own elementary proof (reparametrization
`u ↦ u/C` of geodesics and angle lifts):

* `t39k5_ballM_smul`, `t39k5_filledBall_smul`: `𝓑_{Ct}(z; C·D) = 𝓑_t(z; D)` and the filled balls;
* `t39k5_geodL_smul`: `P` is a `D`-geodesic of length `L` iff `P(·/C)` is a `C·D`-geodesic of
  length `CL`;
* `t39k5_weaklyRightOf_smul`, `t39k5_leftmost_smul`: the order of D-D1 and leftmost geodesics;
* **`t39k5_gArc_smul`**: `t39gArc (C·D) z₀ (Ct) I = t39gArc D z₀ t I`;
* **`t39k5_gArc_sat`**: the saturation property of the arcs modulo constants (C:1559–1561): if
  `C·d₁` and `d₂` (length metrics) have the same internal metric on an open `U ⊇ 𝓑^•_s(d₁)`, then
  `𝓑^•_{Cs}(d₂) = 𝓑^•_s(d₁)` and `t39gArc d₂ z₀ (Cs) I = t39gArc d₁ z₀ s I` (with
  `GM.gm_ballM_eq_of_internal_eq`, `t39k5_gArc_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace CONF

open Blueprint

variable {C : ℝ} (hC : 0 < C)
include hC

theorem t39k5_ballM_smul (D : ContMetric) (z : ℂ) (t : ℝ) :
    ballM (D.smul C hC) z (C * t) = ballM D z t := by
  ext w
  show C * D.1 (z, w) < C * t ↔ D.1 (z, w) < t
  exact mul_lt_mul_iff_of_pos_left hC

theorem t39k5_filledBall_smul (D : ContMetric) (z : ℂ) (t : ℝ) :
    filledBall (D.smul C hC) z (C * t) = filledBall D z t := by
  unfold filledBall; rw [t39k5_ballM_smul hC]

theorem t39k5_smul_smul_inv (D : ContMetric) :
    (D.smul C hC).smul C⁻¹ (inv_pos.2 hC) = D := by
  refine Subtype.ext (ContinuousMap.ext fun p => ?_)
  show C⁻¹ * (C * D.1 p) = D.1 p
  rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

/-- geodesics: `P` for `D` of length `L` gives `P(·/C)` for `C·D` of length `CL` -/
theorem t39k5_geodL_smul {D : ContMetric} {P : ℝ → ℂ} {L : ℝ} {z y : ℂ}
    (hP : IsGeodesicL D P L z y) :
    IsGeodesicL (D.smul C hC) (fun u => P (u / C)) (C * L) z y := by
  obtain ⟨hL, h0, hL', hd⟩ := hP
  refine ⟨mul_nonneg hC.le hL, by simpa using h0, by
    simp only; rw [mul_div_cancel_left₀ _ hC.ne']; exact hL', fun s hs t ht => ?_⟩
  have hmem : ∀ u ∈ Icc 0 (C * L), u / C ∈ Icc 0 L := fun u hu =>
    ⟨div_nonneg hu.1 hC.le, (div_le_iff₀ hC).2 (by linarith [hu.2])⟩
  show C * D.1 (P (s / C), P (t / C)) = |t - s|
  rw [hd _ (hmem s hs) _ (hmem t ht), div_sub_div_same, abs_div, abs_of_pos hC]
  field_simp

/-- angle lifts on `[a, b]` reparametrize to angle lifts on `[a/C, b/C]` -/
theorem t39k5_angleLift_comp {z : ℂ} {P : ℝ → ℂ} {a b : ℝ} {α : ℝ → ℝ}
    (hα : DD.IsAngleLift z P a b α) :
    DD.IsAngleLift z (fun u => P (C * u)) (a / C) (b / C) (fun u => α (C * u)) := by
  have hmaps : MapsTo (fun u => C * u) (Icc (a / C) (b / C)) (Icc a b) := fun u hu =>
    ⟨by have := mul_le_mul_of_nonneg_left hu.1 hC.le; rwa [mul_div_cancel₀ _ hC.ne'] at this,
      by have := mul_le_mul_of_nonneg_left hu.2 hC.le; rwa [mul_div_cancel₀ _ hC.ne'] at this⟩
  exact ⟨hα.1.comp (continuousOn_const.mul continuousOn_id) hmaps,
    fun u hu => hα.2 _ (hmaps hu)⟩

/-- the order `WeaklyRightOf` of D-D1 is scale invariant -/
theorem t39k5_weaklyRightOf_smul {D : ContMetric} {z : ℂ} {s : ℝ} {Q P : ℝ → ℂ}
    (h : DD.WeaklyRightOf D z s Q P) :
    DD.WeaklyRightOf (D.smul C hC) z (C * s) (fun u => Q (u / C)) (fun u => P (u / C)) := by
  intro t ht φ θ hφ α β hα hβ hαβ u v hu hθu hv hθv
  have ht' : t / C ∈ Ioo 0 s :=
    ⟨div_pos ht.1 hC, (div_lt_iff₀ hC).2 (by linarith [ht.2])⟩
  have hfb : filledBall (D.smul C hC) z t = filledBall D z (t / C) := by
    rw [← t39k5_filledBall_smul hC D z (t / C), mul_div_cancel₀ _ hC.ne']
  rw [hfb] at hφ
  have hα' := t39k5_angleLift_comp hC hα
  have hβ' := t39k5_angleLift_comp hC hβ
  have eP : (fun u => P (C * u / C)) = P := by funext u; rw [mul_div_cancel_left₀ _ hC.ne']
  have eQ : (fun u => Q (C * u / C)) = Q := by funext u; rw [mul_div_cancel_left₀ _ hC.ne']
  rw [eP, mul_div_cancel_left₀ _ hC.ne'] at hα'
  rw [eQ, mul_div_cancel_left₀ _ hC.ne'] at hβ'
  have e : C * (t / C) = t := mul_div_cancel₀ _ hC.ne'
  refine h (t / C) ht' φ θ hφ _ _ hα' hβ' ?_ u v hu ?_ hv ?_
  · exact hαβ
  · simp only [e]; exact hθu
  · simp only [e]; exact hθv

/-- leftmost geodesics (D-D1) are scale invariant -/
theorem t39k5_leftmost_smul {D : ContMetric} {z : ℂ} {s : ℝ} {y : ℂ} {P : ℝ → ℂ}
    (hP : DD.IsLeftmostGeod D z s y P) :
    DD.IsLeftmostGeod (D.smul C hC) z (C * s) y (fun u => P (u / C)) := by
  obtain ⟨hy, hg, hQ⟩ := hP
  refine ⟨by rw [t39k5_filledBall_smul hC]; exact hy, t39k5_geodL_smul hC hg, fun Q' hQ' => ?_⟩
  have hinv := inv_pos.2 hC
  have hQg := t39k5_geodL_smul hinv hQ'
  rw [t39k5_smul_smul_inv hC, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at hQg
  have hW : DD.WeaklyRightOf D z s (fun u => Q' (u / C⁻¹)) P := by simpa using hQ _ hQg
  have := t39k5_weaklyRightOf_smul hC hW
  have e : (fun u => (fun v => Q' (v / C⁻¹)) (u / C)) = Q' := by
    funext u; simp only [div_inv_eq_mul]; rw [div_mul_cancel₀ _ hC.ne']
  rw [e] at this
  show DD.WeaklyRightOf (D.smul C hC) z (C * s) Q' (fun u => P (u / C))
  exact this

theorem t39k5_gArc_smul_subset (D : ContMetric) (z₀ : ℂ) (t : ℝ) (I : Set ℂ) :
    t39gArc D z₀ t I ⊆ t39gArc (D.smul C hC) z₀ (C * t) I := by
  rintro x ⟨hx, P, hP, u, hu, hPu⟩
  refine ⟨by rw [t39k5_filledBall_smul hC]; exact hx, _, t39k5_leftmost_smul hC hP, C * u,
    ⟨mul_nonneg hC.le hu.1, mul_le_mul_of_nonneg_left hu.2 hC.le⟩, ?_⟩
  show P (C * u / C) ∈ I
  rw [mul_div_cancel_left₀ _ hC.ne']; exact hPu

/-- **the arcs `I^{(t)}` are scale invariant**: `t39gArc (C·D) z₀ (Ct) I = t39gArc D z₀ t I`
(C:1559–1561 modulo additive constants) -/
theorem t39k5_gArc_smul (D : ContMetric) (z₀ : ℂ) (t : ℝ) (I : Set ℂ) :
    t39gArc (D.smul C hC) z₀ (C * t) I = t39gArc D z₀ t I := by
  refine Subset.antisymm ?_ (t39k5_gArc_smul_subset hC D z₀ t I)
  have := t39k5_gArc_smul_subset (inv_pos.2 hC) (D.smul C hC) z₀ (C * t) I
  rwa [t39k5_smul_smul_inv hC, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at this

omit hC in
/-- equal internal metrics on an open `U ⊇ 𝓑^•_σ(d₁)` give `GMAgree d₁ d₂ U z₀ σ` -/
theorem t39k5_agree_of_internal {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {z₀ : ℂ} {σ : ℝ} (hσ : 0 < σ) {U : Set ℂ} (hU : IsOpen U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (hKU : filledBall d₁ z₀ σ ⊆ U) : GM.GMAgree d₁ d₂ U z₀ σ := by
  have hball : ∀ u ≤ σ, ballM d₁ z₀ u = ballM d₂ z₀ u := by
    intro u hu
    rcases le_or_gt u 0 with hu0 | hu0
    · rw [GM.gm_ballM_nonpos _ z₀ hu0, GM.gm_ballM_nonpos _ z₀ hu0]
    · exact (GM.gm_ballM_eq_of_internal_eq h₁ h₂ hU heq hu0
        (subset_closure.trans (subset_union_left.trans
          ((GM.gm_filledBall_mono _ z₀ hu).trans hKU)))).symm
  exact ⟨heq, hball, hKU, hσ⟩

end CONF
end LQGMetric
