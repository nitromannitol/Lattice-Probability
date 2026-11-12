/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.PathOps at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece

/-!
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

theorem isPiecewiseC1Path_segPath (z w : ℂ) : IsPiecewiseC1Path (segPath z w) z w := by
  have hc : ContDiff ℝ 1 (segPath z w) := by unfold segPath; fun_prop
  refine IsPiecewiseC1Path.of_pcwC1 (F := ∅) (by simp [segPath]) (by simp [segPath])
    hc.continuous.continuousOn fun a b _ _ _ _ => hc.contDiffOn

/-! ### Sub-paths -/

/-- the restriction of `P` to `[s, t]`, reparametrized by `[0, 1]` -/
def subPath (P : ℝ → ℂ) (s t : ℝ) (u : ℝ) : ℂ := P ((t - s) * u + s)

theorem image_subPath_Icc {s t : ℝ} (hst : s < t) :
    (fun u : ℝ => (t - s) * u + s) '' Icc 0 1 = Icc s t := by
  rw [image_affine_Icc' (sub_pos.2 hst)]
  congr 1 <;> ring

theorem lfppLen_subPath (P : ℝ → ℂ) {s t : ℝ} (hst : s < t) :
    lfppLen ξ φ (subPath P s t) = ∫⁻ x in Icc s t, lenDens ξ φ P x := by
  rw [← image_subPath_Icc hst]
  exact lfppLen_comp_affine ξ φ P (sub_pos.2 hst).ne' s

/-! ### Reversal -/

/-- the time reversal `u ↦ P(1 - u)` -/
def revPath (P : ℝ → ℂ) (u : ℝ) : ℂ := P ((-1) * u + 1)

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
