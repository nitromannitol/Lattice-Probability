/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.PathOps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece

/-!
# Piecewise C¹ paths: segments, sub-paths, reversal, concatenation (with their LFPP lengths)

Task P2-LFPP. The path operations implicit in GM (1.4) (`uniqueness-final.tex` l. 216–220) and
DFGPS §2 (`lqg-metric-estimates-final.tex`, LFPP as a length metric): straight segments,
restriction to `[s,t]`, time reversal and concatenation of piecewise C¹ paths, with the
corresponding identities for `lfppLen`. Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ}

theorem lenDens_congr_nhds {P Q : ℝ → ℂ} {u : ℝ} (h : P =ᶠ[𝓝 u] Q) :
    lenDens ξ φ P u = lenDens ξ φ Q u := by
  unfold lenDens
  rw [h.eq_of_nhds, h.deriv_eq]

/-! ### Segments -/

/-- the straight segment `u ↦ z + u (w - z)` -/
def segPath (z w : ℂ) (u : ℝ) : ℂ := z + u • (w - z)

theorem hasDerivAt_segPath (z w : ℂ) (u : ℝ) : HasDerivAt (segPath z w) (w - z) u := by
  exact (((hasDerivAt_id u).smul_const (w - z)).const_add z).congr_deriv (one_smul _ _)

theorem isPiecewiseC1Path_segPath (z w : ℂ) : IsPiecewiseC1Path (segPath z w) z w := by
  have hc : ContDiff ℝ 1 (segPath z w) := by unfold segPath; fun_prop
  refine IsPiecewiseC1Path.of_pcwC1 (F := ∅) (by simp [segPath]) (by simp [segPath])
    hc.continuous.continuousOn fun a b _ _ _ _ => hc.contDiffOn

theorem lenDens_segPath (z w : ℂ) (u : ℝ) :
    lenDens ξ φ (segPath z w) u = ENNReal.ofReal (Real.exp (ξ * φ (segPath z w u)) * ‖w - z‖) := by
  unfold lenDens
  rw [(hasDerivAt_segPath z w u).deriv]

theorem segPath_mem_closedBall (z w : ℂ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    segPath z w u ∈ Metric.closedBall z ‖w - z‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm, segPath, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hu.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hu.2

/-- **Segment bound**: `lfppLen` of the segment is at most `B |w - z|` if `e^{ξ φ} ≤ B` on the
closed ball `B(z, |w-z|)`. -/
theorem lfppLen_segPath_le (z w : ℂ) {B : ℝ}
    (hB : ∀ x ∈ Metric.closedBall z ‖w - z‖, Real.exp (ξ * φ x) ≤ B) :
    lfppLen ξ φ (segPath z w) ≤ ENNReal.ofReal (B * ‖w - z‖) := by
  rw [lfppLen_eq]
  calc ∫⁻ t in Icc (0 : ℝ) 1, lenDens ξ φ (segPath z w) t
      ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (B * ‖w - z‖) := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        rw [lenDens_segPath]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hB _ (segPath_mem_closedBall z w hu)) (norm_nonneg _))
    _ = ENNReal.ofReal (B * ‖w - z‖) := by simp

/-! ### Sub-paths -/

/-- the restriction of `P` to `[s, t]`, reparametrized by `[0, 1]` -/
def subPath (P : ℝ → ℂ) (s t : ℝ) (u : ℝ) : ℂ := P ((t - s) * u + s)

theorem image_subPath_Icc {s t : ℝ} (hst : s < t) :
    (fun u : ℝ => (t - s) * u + s) '' Icc 0 1 = Icc s t := by
  rw [image_affine_Icc' (sub_pos.2 hst)]
  congr 1 <;> ring

theorem isPiecewiseC1Path_subPath {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    IsPiecewiseC1Path (subPath P s t) (P s) (P t) := by
  classical
  obtain ⟨F, hF⟩ := hP.exists_pcwC1
  have hc : 0 < t - s := sub_pos.2 hst
  have hmaps : ∀ a b : ℝ, MapsTo (fun u : ℝ => (t - s) * u + s) (Icc a b)
      (Icc ((t - s) * a + s) ((t - s) * b + s)) := fun a b u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  refine IsPiecewiseC1Path.of_pcwC1 (F := F.image fun x => (x - s) / (t - s))
    (by simp [subPath]) (by simp [subPath]) ?_ ?_
  · refine hP.continuousOn.comp (by fun_prop) fun u hu => ?_
    have := hmaps 0 1 hu
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at this
    exact ⟨hs.trans this.1, this.2.trans ht⟩
  · intro a b ha hab hb hFa
    refine contDiffOn_comp_affine (hF _ _ (by nlinarith) (by nlinarith) (by nlinarith)
      fun x hx hxI => hFa _ (Finset.mem_image_of_mem _ hx) ⟨?_, ?_⟩) (hmaps a b)
    · rw [lt_div_iff₀ hc]; linarith [hxI.1]
    · rw [div_lt_iff₀ hc]; linarith [hxI.2]

theorem lfppLen_subPath (P : ℝ → ℂ) {s t : ℝ} (hst : s < t) :
    lfppLen ξ φ (subPath P s t) = ∫⁻ x in Icc s t, lenDens ξ φ P x := by
  rw [← image_subPath_Icc hst]
  exact lfppLen_comp_affine ξ φ P (sub_pos.2 hst).ne' s

/-! ### Reversal -/

/-- the time reversal `u ↦ P(1 - u)` -/
def revPath (P : ℝ → ℂ) (u : ℝ) : ℂ := P ((-1) * u + 1)

theorem isPiecewiseC1Path_revPath {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) :
    IsPiecewiseC1Path (revPath P) w z := by
  classical
  obtain ⟨F, hF⟩ := hP.exists_pcwC1
  have hmaps : ∀ a b : ℝ, MapsTo (fun u : ℝ => (-1) * u + 1) (Icc a b) (Icc (1 - b) (1 - a)) :=
    fun a b u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
  refine IsPiecewiseC1Path.of_pcwC1 (F := F.image fun x => 1 - x)
    (by simp [revPath, hP.target]) (by simp [revPath, hP.source]) ?_ ?_
  · refine hP.continuousOn.comp (by fun_prop) fun u hu => ?_
    have := hmaps 0 1 hu
    simpa using this
  · intro a b ha hab hb hFa
    exact contDiffOn_comp_affine (hF _ _ (by linarith) (by linarith) (by linarith)
      fun x hx hxI => hFa _ (Finset.mem_image_of_mem _ hx)
        ⟨by linarith [hxI.2], by linarith [hxI.1]⟩) (hmaps a b)

theorem lfppLen_revPath (P : ℝ → ℂ) : lfppLen ξ φ (revPath P) = lfppLen ξ φ P := by
  rw [show revPath P = fun u => P ((-1) * u + 1) from rfl, lfppLen_comp_affine ξ φ P (by norm_num : (-1 : ℝ) ≠ 0), lfppLen_eq]
  congr 2
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  · intro hx
    exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by ring⟩

end LFPP
end LQGMetric
