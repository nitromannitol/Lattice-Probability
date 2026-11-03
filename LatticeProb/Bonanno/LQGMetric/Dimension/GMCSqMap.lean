/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqMap at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCCircle
import LatticeProb.Bonanno.LQGMetric.Field.GreenFnSquare
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A conformal map of the unit square onto `ℍ`; pushed circles are admissible (P2-GMC, WP-24)

`sqMap : 𝕍 → ℍ` is a fixed conformal map of the open unit square onto the upper half-plane
(Riemann mapping, `exists_isConformalOnto_H_of_convex`). For it:

* `sqQuot x y = ∫₀¹ φ'(y + t(x − y)) dt` is jointly continuous on `𝕍 × 𝕍`, equals the
  difference quotient `(φ x − φ y)/(x − y)` (`sqQuot_mul`) and never vanishes (injectivity,
  `φ' ≠ 0`);
* `exists_lowerLip` : on a compact convex `K ⊆ 𝕍`, `c ‖x − y‖ ≤ ‖φ x − φ y‖`;
* `isAdmissibleH_map_circle` : `φ_* (circle in 𝕍)` is admissible on `ℍ` (QZ
  `isAdmissibleH_map`), so QZ's kernel form of the covariance `K3.dualCov_conformal_eq_kernel`
  applies to circle averages of the zero-boundary GFF on `𝕍`.

This is the input for the Green-function computations of circle averages on `𝕍`
(Duplantier–Sheffield arXiv:0808.1560 §3.1: `G_𝕍(x,y) = −log|x−y| + harmonic`). The
difference-quotient argument is an own elementary proof (fundamental theorem of calculus on
segments, mathlib `integral_unitInterval_deriv_eq_sub`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal

namespace LQGMetric

lemma openSquare_ne_univ : openSquare ≠ univ := fun h => by
  have := h ▸ mem_univ (0 : ℂ); simp [openSquare] at this

lemma openSquare_nonempty : openSquare.Nonempty :=
  ⟨⟨1 / 2, 1 / 2⟩, by simp only [openSquare, mem_ofPred_eq]; norm_num⟩

/-- a fixed conformal map of `𝕍` onto `ℍ` -/
def sqMap : ℂ → ℂ :=
  (exists_isConformalOnto_H_of_convex isOpen_openSquare convex_openSquare openSquare_nonempty
    openSquare_ne_univ).choose

lemma isConformalOnto_sqMap : K3.IsConformalOnto sqMap openSquare H :=
  (exists_isConformalOnto_H_of_convex isOpen_openSquare convex_openSquare openSquare_nonempty
    openSquare_ne_univ).choose_spec

lemma analyticOnNhd_sqMap : AnalyticOnNhd ℂ sqMap openSquare :=
  isConformalOnto_sqMap.diffOn.analyticOnNhd isOpen_openSquare

lemma continuousOn_deriv_sqMap : ContinuousOn (deriv sqMap) openSquare :=
  analyticOnNhd_sqMap.deriv.continuousOn

lemma sqMap_mem_H {x : ℂ} (hx : x ∈ openSquare) : sqMap x ∈ H := by
  rw [← isConformalOnto_sqMap.image_eq]; exact mem_image_of_mem _ hx

lemma segment_mem {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : y + t • (x - y) ∈ openSquare := by
  have := convex_openSquare hy hx (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
  convert this using 1
  simp only [Complex.real_smul]; push_cast; ring

/-- the integrated difference quotient of `sqMap` -/
def sqQuot (x y : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, deriv sqMap (y + t • (x - y))

lemma sqQuot_mul {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) :
    (x - y) * sqQuot x y = sqMap x - sqMap y := by
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub (𝕜 := ℂ) (E := ℂ)
    (f := sqMap) (f' := deriv sqMap) (z₀ := y) (z₁ := x - y)
    (continuousOn_deriv_sqMap.comp (by fun_prop) fun t ht => segment_mem hx hy ht)
    (fun t ht => (analyticOnNhd_sqMap _ (segment_mem hx hy ht)).differentiableAt.hasDerivAt)
  rw [smul_eq_mul, add_sub_cancel] at h
  exact h

lemma sqQuot_self {x : ℂ} (hx : x ∈ openSquare) : sqQuot x x = deriv sqMap x := by
  simp [sqQuot]

lemma sqQuot_ne_zero {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) : sqQuot x y ≠ 0 := by
  by_cases hxy : x = y
  · subst hxy; rw [sqQuot_self hx]; exact isConformalOnto_sqMap.deriv_ne x hx
  · intro h0
    have := sqQuot_mul hx hy
    rw [h0, mul_zero, eq_comm, sub_eq_zero] at this
    exact hxy (isConformalOnto_sqMap.injOn hx hy this)

/-- joint continuity of the difference quotient on a compact convex subset -/
lemma continuousOn_sqQuot {K : Set ℂ} (hKU : K ⊆ openSquare) (hKc : Convex ℝ K)
    (hKk : IsCompact K) : ContinuousOn (fun p : ℂ × ℂ => sqQuot p.1 p.2) (K ×ˢ K) := by
  -- the integrand is continuous on the compact set `K × K × [0,1]`, extend by a clamp
  set g : (ℂ × ℂ) × ℝ → ℂ := fun q => deriv sqMap (q.1.2 + (max 0 (min 1 q.2)) • (q.1.1 - q.1.2))
  have hseg : ∀ q : (ℂ × ℂ) × ℝ, q.1 ∈ K ×ˢ K →
      q.1.2 + (max 0 (min 1 q.2)) • (q.1.1 - q.1.2) ∈ K := by
    intro q hq
    have ht0 : 0 ≤ max 0 (min 1 q.2) := le_max_left _ _
    have ht1 : max 0 (min 1 q.2) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have := hKc hq.2 hq.1 (by linarith : (0 : ℝ) ≤ 1 - max 0 (min 1 q.2)) ht0 (by ring)
    convert this using 1
    simp only [Complex.real_smul]; push_cast; ring
  have hgc : ContinuousOn g ((K ×ˢ K) ×ˢ univ) :=
    (continuousOn_deriv_sqMap.mono hKU).comp (by fun_prop) fun q hq => hseg q hq.1
  -- reduce to continuity on the subtype
  rw [continuousOn_iff_continuous_domRestrict]
  have hint : ∀ p : K ×ˢ K, sqQuot p.1.1 p.1.2 = ∫ t in (0 : ℝ)..1, g (p.1, t) := by
    intro p
    unfold sqQuot
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [g, min_eq_right ht.2, max_eq_right ht.1]
  have : (K ×ˢ K).domRestrict (fun p : ℂ × ℂ => sqQuot p.1 p.2) =
      fun p : K ×ˢ K => ∫ t in (0 : ℝ)..1, g (p.1, t) := funext hint
  rw [this]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
  have := hgc.comp_continuous (continuous_subtype_val.prodMap continuous_id)
    (fun q => ⟨q.1.2, mem_univ _⟩)
  exact this

/-- **lower Lipschitz bound** for `sqMap` on a compact convex subset of `𝕍` -/
theorem exists_lowerLip {K : Set ℂ} (hKU : K ⊆ openSquare) (hKc : Convex ℝ K)
    (hKk : IsCompact K) : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ y ∈ K, c * ‖x - y‖ ≤ ‖sqMap x - sqMap y‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun x hx => hx.elim⟩
  have hc := (continuousOn_sqQuot hKU hKc hKk).norm
  obtain ⟨p₀, hp₀, hmin⟩ := (hKk.prod hKk).exists_isMinOn (hne.prod hne) hc
  refine ⟨‖sqQuot p₀.1 p₀.2‖, norm_pos_iff.mpr (sqQuot_ne_zero (hKU hp₀.1) (hKU hp₀.2)),
    fun x hx y hy => ?_⟩
  have h := hmin (show (x, y) ∈ K ×ˢ K from ⟨hx, hy⟩)
  simp only [mem_ofPred_eq] at h
  rw [← sqQuot_mul (hKU hx) (hKU hy), norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- **pushed circles are admissible on `ℍ`** -/
theorem isAdmissibleH_map_circle {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ openSquare) :
    IsAdmissibleH (((circleUnif z r).restrict openSquare).map sqMap) := by
  rw [K3.map_restrict_confMod isConformalOnto_sqMap]
  have hzi : r ≤ z.im := by
    have := hB (show z + r * Complex.I ∈ closedBall z r by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        Complex.norm_of_nonneg hr.le, mul_one])
    have h2 := this.2.2.1
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, mul_one] at h2
    -- `z.im + r` is in `(0,1)` only gives positivity; use the lowest point instead
    have := hB (show z - r * Complex.I ∈ closedBall z r by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
        Complex.norm_of_nonneg hr.le, mul_one])
    have h3 := this.2.2.1
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, mul_one] at h3
    linarith
  have hadm : IsAdmissibleH (circleUnif z r) := by
    rw [← foldedCircle_eq_circleUnif hr.le hzi]
    exact isAdmissibleH_foldedCircle (show z ∈ Hbar from (hr.trans_le hzi).le) hr
  obtain ⟨c, hc, hlip⟩ := exists_lowerLip hB (convex_closedBall z r) (isCompact_closedBall z r)
  refine isAdmissibleH_map (isAdmissibleH_restrict hadm _) (isCompact_closedBall z r) ?_
    (K3.measurable_confMod isConformalOnto_sqMap) ?_ ?_ hc ?_
  · rw [Measure.restrict_apply' isOpen_openSquare.measurableSet]
    exact measure_mono_null inter_subset_left (circleUnif_compl_closedBall hr z)
  · exact (isConformalOnto_sqMap.diffOn.continuousOn.mono hB).congr
      fun x hx => K3.confMod_eqOn (hB hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [K3.confMod_eqOn (hB hx)]; exact H_subset_Hbar (sqMap_mem_H (hB hx))
  · intro x hx y hy
    rw [K3.confMod_eqOn (hB hx), K3.confMod_eqOn (hB hy)]; exact hlip x hx y hy

end LQGMetric
