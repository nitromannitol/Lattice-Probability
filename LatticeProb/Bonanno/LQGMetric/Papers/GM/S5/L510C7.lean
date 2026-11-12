/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C6
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43Frk

/-!
# GM Lemma 5.10, condition (10): bump templates and scaling (task P2-M2M6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`,
l. 3189–3192 ("we can choose `f_r^{x,y}` … in such a way that … the Dirichlet energy is bounded
above by a constant which does not depend on `r`", by scaling) and l. 3331–3333. Here:

* `l510_exists_bump`: a smooth `[0,1]`-valued test function `≡ 1` on a bounded set `W` and
  vanishing off `B_d(W)` (mathlib's smooth Urysohn lemma
  `exists_contDiff_zero_iff_one_iff_of_isClosed`);
* `dilT r φ = φ(·/r)` (`testAffinePull r 0`): `gradEnergy_dilT` (scale invariance of the Dirichlet
  energy in dimension 2) and `isBumpFor_dilT` (bumps rescale);
* `sqTubes_smul`: rescaling by `r⁻¹` maps the square tubes of side `sr` near `cl B_{Rr}(0)` to
  the square tubes of side `s` near `cl B_R(0)`, a finite family independent of `r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace LQGMetric.GM
open Blueprint

/-- a smooth bump `≡ 1` on `W`, supported in `B_{d/2}(W)` -/
lemma l510_exists_bump {W : Set ℂ} (hW : Bornology.IsBounded W) {d : ℝ} (hd : 0 < d) :
    ∃ F : TestC, IsBumpFor F W d := by
  have hs : IsClosed (thickening (d / 2) W)ᶜ := isOpen_thickening.isClosed_compl
  have hdisj : Disjoint (thickening (d / 2) W)ᶜ (closure W) :=
    Set.disjoint_left.2 fun x hx hx' => hx (closure_subset_thickening (by linarith) W hx')
  obtain ⟨f, hf, hrange, h0, h1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) hs isClosed_closure hdisj
  have hsupp : Function.support f ⊆ thickening (d / 2) W := fun x hx => by
    by_contra h; exact hx ((h0 x).1 h)
  have hcs : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (hW.thickening.isCompact_closure) isClosed_closure
      (closure_mono hsupp)
  refine ⟨⟨f, hf, hcs, subset_univ _⟩, fun z => hrange ⟨z, rfl⟩, fun z hz => (h1 z).1
    (subset_closure hz), fun z hz => (h0 z).1 fun h => hz (thickening_mono (by linarith) W h)⟩

/-- `φ(·/r)` -/
abbrev dilT (r : ℝ) (φ : TestC) : TestC := testAffinePull r 0 φ

lemma dilT_apply {r : ℝ} (hr : 0 < r) (φ : TestC) (x : ℂ) : dilT r φ x = φ ((r⁻¹ : ℝ) • x) := by
  rw [testAffinePull_apply r 0 hr.ne', sub_zero]
  congr 1
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

/-- **Scale invariance of the Dirichlet energy** in dimension 2 -/
lemma gradEnergy_dilT {r : ℝ} (hr : 0 < r) (φ : TestC) : gradEnergy (dilT r φ) = gradEnergy φ := by
  have e : (⇑(dilT r φ) : ℂ → ℝ) = fun y => φ ((r⁻¹ : ℝ) • y) := funext fun y => dilT_apply hr φ y
  have hd : Differentiable ℝ (⇑φ) := (contDiff_two_testC φ).differentiable (by norm_num)
  have hfd : ∀ x : ℂ, ‖fderiv ℝ (fun y => φ ((r⁻¹ : ℝ) • y)) x‖ ^ 2 =
      (r⁻¹) ^ 2 * ‖fderiv ℝ (⇑φ) ((r⁻¹ : ℝ) • x)‖ ^ 2 := by
    intro x
    have h1 : HasFDerivAt (fun y : ℂ => (r⁻¹ : ℝ) • y)
        ((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).const_smul (r⁻¹ : ℝ)
    have h2 := ((hd _).hasFDerivAt).comp x h1
    rw [show (fun y : ℂ => φ ((r⁻¹ : ℝ) • y)) = ⇑φ ∘ fun y : ℂ => (r⁻¹ : ℝ) • y from rfl,
      h2.fderiv, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), mul_pow]
  unfold gradEnergy
  rw [e]
  simp_rw [hfd]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x => ‖fderiv ℝ (⇑φ) x‖ ^ 2) hr.le, Complex.finrank_real_complex, smul_eq_mul,
    inv_pow]
  have : (r ^ 2)⁻¹ * r ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  calc _ = (2 * Real.pi)⁻¹ * ((r ^ 2)⁻¹ * r ^ 2) * ∫ x : ℂ, ‖fderiv ℝ (⇑φ) x‖ ^ 2 := by ring
    _ = _ := by rw [this, mul_one]

lemma inv_smul_mem_smul {r : ℝ} (_hr : 0 < r) {V : Set ℂ} {z : ℂ} (hz : z ∈ V) :
    (r⁻¹ : ℝ) • z ∈ (r⁻¹ : ℝ) • V := smul_mem_smul_set hz

/-- bumps rescale: a bump for `r⁻¹ V` with margin `d` gives a bump for `V` with margin `dr` -/
lemma isBumpFor_dilT {r : ℝ} (hr : 0 < r) {T : TestC} {V : Set ℂ} {d : ℝ}
    (hT : IsBumpFor T ((r⁻¹ : ℝ) • V) d) : IsBumpFor (dilT r T) V (d * r) := by
  refine ⟨fun z => by rw [dilT_apply hr]; exact hT.1 _, fun z hz => by
    rw [dilT_apply hr]; exact hT.2.1 _ (inv_smul_mem_smul hr hz), fun z hz => ?_⟩
  rw [dilT_apply hr]
  refine hT.2.2 _ fun hmem => hz ?_
  obtain ⟨w, ⟨v, hv, rfl⟩, hd⟩ := mem_thickening_iff.1 hmem
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)] at hd
  refine mem_thickening_iff.2 ⟨v, hv, ?_⟩
  have := (inv_mul_lt_iff₀ hr).1 hd
  linarith

/-! ## Rescaling square tubes -/

lemma smul_gridSquare {s r : ℝ} (hr : 0 < r) (m : ℤ × ℤ) :
    (r⁻¹ : ℝ) • gridSquare (s * r) m = gridSquare s m := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'), inv_inv]
  simp only [gridSquare, mem_ofPred_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_of_mul_le_mul_right (by linarith : (m.1 : ℝ) * s * r ≤ x.re * r) hr
    · exact le_of_mul_le_mul_right (by linarith : x.re * r ≤ ((m.1 : ℝ) + 1) * s * r) hr
    · exact le_of_mul_le_mul_right (by linarith : (m.2 : ℝ) * s * r ≤ x.im * r) hr
    · exact le_of_mul_le_mul_right (by linarith : x.im * r ≤ ((m.2 : ℝ) + 1) * s * r) hr
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- rescaling the square tubes -/
lemma sqTubes_smul {s R r : ℝ} (hr : 0 < r) {V : Set ℂ}
    (hV : V ∈ sqTubes (s * r) (squareSet (s * r) (closedBall 0 (R * r)))) :
    (r⁻¹ : ℝ) • V ∈ sqTubes s (squareSet s (closedBall 0 R)) := by
  obtain ⟨B, hB, rfl⟩ := hV
  refine ⟨B, fun m hm => ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hB hm
    refine ⟨(r⁻¹ : ℝ) • x, ?_, ?_⟩
    · rw [← smul_gridSquare (s := s) hr m]; exact smul_mem_smul_set hx1
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
      rw [mem_closedBall, dist_zero_right] at hx2; linarith
  · show interior (⋃ m ∈ B, gridSquare s m) = (r⁻¹ : ℝ) • interior (⋃ m ∈ B, gridSquare (s * r) m)
    rw [← interior_smul₀ (inv_ne_zero hr.ne'), smul_set_iUnion₂]
    simp_rw [smul_gridSquare hr]

/-- the tubes near `cl B_R(0)` are bounded -/
lemma sqTubes_subset_ball {s R : ℝ} (hs : 0 < s) {V : Set ℂ}
    (hV : V ∈ sqTubes s (squareSet s (closedBall 0 R))) : V ⊆ closedBall 0 (R + 3 * s) := by
  obtain ⟨B, hB, rfl⟩ := hV
  intro z hz
  obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.1 (interior_subset hz)
  obtain ⟨x, hx1, hx2⟩ := hB hm
  have h1 := gridSquare_subset_ball hs hx1 hzm
  rw [mem_ball, dist_eq_norm] at h1
  rw [mem_closedBall, dist_zero_right] at hx2 ⊢
  have := norm_le_norm_add_norm_sub' z x
  linarith

end LQGMetric.GM
