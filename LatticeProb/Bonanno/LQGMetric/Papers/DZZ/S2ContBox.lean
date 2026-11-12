/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2ContBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Cont

/-!
# DZZ Lemma 2.6, first inequality, for fields on a box (task P2-DZZPRE, WP-112)

`dzz_lemma26_box`: the form of `dzz_lemma26_core` for fields given only on a box
`𝕍 = ferniqueBox x₀ s` (DZZ's `η_δ` lives on the unit square `𝕍`, `LBM_LGDarXiv.tex`
l. 546–569): hypotheses and conclusion are restricted to `𝕍`. Reduction (own elementary step):
compose with the 1-Lipschitz coordinatewise projection `boxClamp` of `ℂ` onto the box, which
preserves both increment bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open SupTail

universe u

/-- Coordinatewise projection of `ℂ` onto `ferniqueBox x₀ s`. -/
def boxClamp (x₀ : ℂ) (s : ℝ) (v : ℂ) : ℂ :=
  ((max x₀.re (min v.re (x₀.re + s)) : ℝ) : ℂ) +
    ((max x₀.im (min v.im (x₀.im + s)) : ℝ) : ℂ) * Complex.I

@[simp] lemma boxClamp_re (x₀ : ℂ) (s : ℝ) (v : ℂ) :
    (boxClamp x₀ s v).re = max x₀.re (min v.re (x₀.re + s)) := by simp [boxClamp]

@[simp] lemma boxClamp_im (x₀ : ℂ) (s : ℝ) (v : ℂ) :
    (boxClamp x₀ s v).im = max x₀.im (min v.im (x₀.im + s)) := by simp [boxClamp]

lemma continuous_boxClamp (x₀ : ℂ) (s : ℝ) : Continuous (boxClamp x₀ s) := by
  unfold boxClamp; fun_prop

lemma boxClamp_mem {x₀ : ℂ} {s : ℝ} (hs : 0 ≤ s) (v : ℂ) :
    boxClamp x₀ s v ∈ ferniqueBox x₀ s := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [boxClamp_re, boxClamp_im]
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma boxClamp_of_mem {x₀ v : ℂ} {s : ℝ} (hv : v ∈ ferniqueBox x₀ s) : boxClamp x₀ s v = v := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv
  apply Complex.ext <;> simp only [boxClamp_re, boxClamp_im]
  · rw [min_eq_left h2, max_eq_right h1]
  · rw [min_eq_left h4, max_eq_right h3]

lemma abs_clamp_sub_le (a b x y : ℝ) :
    |max a (min x b) - max a (min y b)| ≤ |x - y| := by
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ a).trans ((abs_min_sub_min_le_max x b y b).trans ?_)
  simp

lemma norm_boxClamp_sub_le (x₀ : ℂ) (s : ℝ) (v w : ℂ) :
    ‖boxClamp x₀ s v - boxClamp x₀ s w‖ ≤ ‖v - w‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, boxClamp_re, boxClamp_im]
  have h1 := sq_le_sq.2 (abs_clamp_sub_le x₀.re (x₀.re + s) v.re w.re)
  have h2 := sq_le_sq.2 (abs_clamp_sub_le x₀.im (x₀.im + s) v.im w.im)
  nlinarith only [h1, h2]

end DZZ
end LQGMetric
