/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GenHeat at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.6 on squares, with translation (for Lemma 2.8 on general squares)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), proof of Lemma 2.8, T:893–894:
"By Lemma 2.6 and the scale and translation invariance of the law of `h`, modulo additive
constant, it suffices to prove the lemma for `S = [0,1]²`." This file proves the identity behind
that sentence, for internal metrics: for a whole-plane GFF `h`, a.s. for all `z, w`,
`D^{ε/s}_{h(s·+a)}(z, w; [0,1]²) = s⁻¹ D^ε_h(a + s z, a + s w; a + [0,s]²)` (`lem2_6_sq`).

The proof is that of Lemma 2.6 (T:847–855): the heat-kernel change of variables
`(h(s·+a))*_{ε/s}(z) = h*_ε(a + s z)` and the change of variables `P ↦ a + s P` of paths. The
scaling part of the heat-kernel identity is `ae_heatMollify_affineComp` (L2_6.lean); the
translation part (`ae_heatMollify_translate`) is proved here in the same way (the two
truncations `χ_n(· − a)` and `χ_n` differ only where the heat kernel is `O(e^{-n})`; own argument
for "standard change of variables", as in L2_6.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the difference of the two truncations under translation: `p_s(z + a, ·)(χ_n(· − a) − χ_n)` -/
def transTruncDiff (s : ℝ) (a z : ℂ) (n : ℕ) : TestC :=
  testAffinePull 1 a (heatTrunc s z n) - heatTrunc s (z + a) n

lemma transTruncDiff_apply (s : ℝ) (a z : ℂ) (n : ℕ) (x : ℂ) :
    transTruncDiff s a z n x = heatKernel s (z + a) x *
      ((cutoff n : ℂ → ℝ) (x - a) - (cutoff n : ℂ → ℝ) x) := by
  show testAffinePull 1 a (heatTrunc s z n) x - heatTrunc s (z + a) n x = _
  rw [testAffinePull_apply _ _ one_ne_zero, heatTrunc_apply, heatTrunc_apply]
  have e1 : (x - a) / ((1 : ℝ) : ℂ) = x - a := by simp
  have e2 : heatKernel s z (x - a) = heatKernel s (z + a) x := by
    unfold heatKernel
    rw [show z - (x - a) = z + a - x by ring]
  rw [e1, e2]
  ring

lemma abs_transTruncDiff_le {s : ℝ} (hs : 0 < s) (a z : ℂ) (n : ℕ) (x : ℂ) :
    |transTruncDiff s a z n x| ≤ (2 * Real.pi * s)⁻¹ *
      Real.exp (s / 2 + ‖a‖ + ‖z + a‖) * Real.exp (-(n : ℝ)) := by
  rw [transTruncDiff_apply]
  by_cases hx : ‖x‖ + ‖a‖ ≤ (n : ℝ) + 1
  · have h1 : ‖x - a‖ ≤ (n : ℝ) + 1 := (norm_sub_le x a).trans hx
    have h2 : ‖x‖ ≤ (n : ℝ) + 1 := by linarith [norm_nonneg a]
    rw [cutoff_eq_one h1, cutoff_eq_one h2, sub_self, mul_zero, abs_zero]
    positivity
  push Not at hx
  have hp := heatKernel_nonneg s hs.le (z + a) x
  have hc : |(cutoff n : ℂ → ℝ) (x - a) - (cutoff n : ℂ → ℝ) x| ≤ 1 := by
    have := (cutoff n).nonneg (x := x - a); have := (cutoff n).le_one (x := x - a)
    have := (cutoff n).nonneg (x := x); have := (cutoff n).le_one (x := x)
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hp]
  refine (mul_le_of_le_one_right hp hc).trans ?_
  unfold heatKernel
  rw [mul_assoc _ (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (2 * Real.pi * s)⁻¹)
  refine (exp_neg_sq_div_le' s _ 1 hs one_pos).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have ht : ‖x‖ - ‖z + a‖ ≤ ‖z + a - x‖ := by
    have := norm_sub_norm_le x (z + a)
    rw [norm_sub_rev] at this
    linarith
  simp only [one_pow, mul_one, div_one]
  linarith

lemma transTruncDiff_eq_zero (s : ℝ) (a z : ℂ) (n : ℕ) (x : ℂ)
    (hx : (1 + ‖a‖) * ((n : ℝ) + 3) ≤ ‖x‖) : transTruncDiff s a z n x = 0 := by
  have ha := norm_nonneg a
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx1 : (n : ℝ) + 2 ≤ ‖x‖ := by nlinarith
  have hx2 : (n : ℝ) + 2 ≤ ‖x - a‖ := by
    have := norm_sub_norm_le x a
    nlinarith
  rw [transTruncDiff_apply, cutoff_eq_zero hx1, cutoff_eq_zero hx2, sub_self, mul_zero]

/-- **The heat-kernel translation identity**, a.s. at a fixed point:
`(h(· + a))*_ε(z) = h*_ε(z + a)`. -/
theorem ae_heatMollify_translate_at (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : ε ≠ 0) (a z : ℂ) :
    ∀ᵐ ω ∂P, heatMollify ε (affineComp 1 a (h ω)) z = heatMollify ε (h ω) (z + a) := by
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  have h1 := hh.ae_tendsto_heatMollify ε hε (z + a)
  have h2 := (hh.affineComp one_pos a).ae_tendsto_heatMollify ε hε z
  have h3 := ae_summable_abs_of_decay_scaled hh (fun n => transTruncDiff s a z n)
    (by positivity) (by positivity : (0 : ℝ) < 1 + ‖a‖)
    (fun n w => abs_transTruncDiff_le hs a z n w)
    (fun n w hw => transTruncDiff_eq_zero s a z n w hw)
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  have hD : Tendsto (fun n => h ω (transTruncDiff s a z n)) atTop (𝓝 0) :=
    hω3.of_abs.tendsto_atTop_zero
  have e : ∀ n, affineComp 1 a (h ω) (heatTrunc s z n) =
      h ω (heatTrunc s (z + a) n) + h ω (transTruncDiff s a z n) := fun n => by
    rw [GFFInv.affineComp_apply, transTruncDiff, map_sub]
    ring
  have hω2' : Tendsto (fun n => affineComp 1 a (h ω) (heatTrunc s z n)) atTop
      (𝓝 (heatMollify ε (affineComp 1 a (h ω)) z)) := hω2
  simp_rw [e] at hω2'
  have := hω1.add hD
  rw [add_zero] at this
  exact tendsto_nhds_unique hω2' this

/-- the heat-kernel translation identity a.s. at all points simultaneously -/
theorem ae_heatMollify_translate (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : ε ≠ 0) (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ z, heatMollify ε (affineComp 1 a (h ω)) z = heatMollify ε (h ω) (z + a) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hall := (ae_ball_iff hSc).2 fun z _ => ae_heatMollify_translate_at hh hε a z
  have hc1 := (hh.affineComp one_pos a).ae_tendstoLocallyUniformly_heatMollify ε hε
  have hc2 := hh.ae_tendstoLocallyUniformly_heatMollify ε hε
  filter_upwards [hall, hc1, hc2] with ω hω h1 h2
  have := Continuous.ext_on hSd h1.2 (h2.2.comp (continuous_id.add continuous_const))
    fun z hz => hω z hz
  exact fun z => congrFun this z

/-- `h(r · + a) = (h(· + a))(r ·)` -/
lemma affineComp_eq_affineComp_translate {r : ℝ} (hr : r ≠ 0) (a : ℂ) (g : DistC) :
    affineComp r a g = affineComp r 0 (affineComp 1 a g) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply]
  have : testAffinePull 1 a (testAffinePull r 0 φ) = testAffinePull r a φ :=
    TestFunction.ext fun x => by
      rw [testAffinePull_apply _ _ one_ne_zero, testAffinePull_apply _ _ hr,
        testAffinePull_apply _ _ hr]
      congr 1
      simp
  rw [this]
  simp

/-- **The heat-kernel change of variables with translation** (DFGPS T:848):
a.s. `(h(r· + a))*_{ε/r}(z) = h*_ε(a + r z)` for all `z`. -/
theorem ae_heatMollify_affineComp_trans (hh : IsWholePlaneGFF h P) {ε r : ℝ} (hε : ε ≠ 0)
    (hr : 0 < r) (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ z, heatMollify (ε / r) (affineComp r a (h ω)) z =
      heatMollify ε (h ω) (a + (r : ℂ) * z) := by
  filter_upwards [ae_heatMollify_affineComp (hh.affineComp one_pos a) hε hr,
    ae_heatMollify_translate hh hε a] with ω h1 h2 z
  rw [affineComp_eq_affineComp_translate hr.ne', h1 z, h2, add_comm]

/-! ## The change of variables `P ↦ b + c P` in internal LFPP distances -/

theorem isPiecewiseC1Path_affine {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    (b c : ℂ) : IsPiecewiseC1Path (fun t => b + c * P t) (b + c * z) (b + c * w) := by
  obtain ⟨k, t, ht, h0, h1, hC⟩ := hP.piecewise
  refine ⟨by simp [hP.source], by simp [hP.target],
    continuousOn_const.add (continuousOn_const.mul hP.continuousOn), k, t, ht, h0, h1,
    fun i => ?_⟩
  exact contDiffOn_const.add (contDiffOn_const.mul (hC i))

theorem lfppLen_affine (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) (b c : ℂ) :
    lfppLen ξ φ (fun t => b + c * P t) =
      ENNReal.ofReal ‖c‖ * lfppLen ξ (fun x => φ (b + c * x)) P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  simp only
  rw [deriv_const_add, deriv_const_mul_field, norm_mul, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  ring

/-- the change of variables `P ↦ b + c P` in `lfppDOn` (`c ≠ 0`, `S' = b + c S`) -/
theorem lfppDOn_affine (ξ : ℝ) (φ : ℂ → ℝ) {S S' : Set ℂ} {b c : ℂ} (hc : c ≠ 0)
    (hS : ∀ x, x ∈ S ↔ b + c * x ∈ S') (z w : ℂ) :
    lfppDOn ξ φ S' (b + c * z) (b + c * w) =
      ENNReal.ofReal ‖c‖ * lfppDOn ξ (fun x => φ (b + c * x)) S z w := by
  unfold lfppDOn
  rw [ENNReal.mul_iInf_of_ne (by simpa using hc) ENNReal.ofReal_ne_top]
  have hinv : ∀ y, b + c * (-(c⁻¹ * b) + c⁻¹ * y) = y := fun y => by
    field_simp; ring
  refine le_antisymm (le_iInf fun P => ?_) (le_iInf fun Q => ?_)
  · rw [← lfppLen_affine]
    exact iInf_le_of_le ⟨_, isPiecewiseC1Path_affine P.2.1 b c,
      fun t ht => (hS _).1 (P.2.2 t ht)⟩ le_rfl
  · have hQ := isPiecewiseC1Path_affine Q.2.1 (-(c⁻¹ * b)) c⁻¹
    have e1 : -(c⁻¹ * b) + c⁻¹ * (b + c * z) = z := by field_simp; ring
    have e2 : -(c⁻¹ * b) + c⁻¹ * (b + c * w) = w := by field_simp; ring
    rw [e1, e2] at hQ
    refine iInf_le_of_le ⟨_, hQ, fun t ht => (hS _).2 (by rw [hinv]; exact Q.2.2 t ht)⟩
      (le_of_eq ?_)
    rw [lfppLen_affine]
    simp only [hinv]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _), ← norm_mul, mul_inv_cancel₀ hc,
      norm_one, ENNReal.ofReal_one, one_mul]

lemma mem_closedSq01_iff {a : ℂ} {s : ℝ} (hs : 0 < s) (x : ℂ) :
    x ∈ closedSq 0 1 ↔ a + (s : ℂ) * x ∈ closedSq a s := by
  simp only [closedSq, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, zero_add,
    Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hc; push Not at hc; nlinarith
    · by_contra hc; push Not at hc; nlinarith
    · by_contra hc; push Not at hc; nlinarith
    · by_contra hc; push Not at hc; nlinarith

/-- **DFGPS Lemma 2.6 for internal metrics on squares** (T:837–856 with T:893–894): for a
whole-plane GFF `h`, a.s. for all `z, w`,
`D^{ε/s}_{h(s·+a)}(z, w; [0,1]²) = s⁻¹ D^ε_h(a + s z, a + s w; a + [0,s]²)`. -/
theorem lem2_6_sq (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      lfppDOn ξ (heatMollify (ε / s) (affineComp s a (h ω))) closedUnitSquare z w =
        ENNReal.ofReal s⁻¹ *
          lfppDOn ξ (heatMollify ε (h ω)) (closedSq a s) (a + (s : ℂ) * z) (a + (s : ℂ) * w) := by
  filter_upwards [ae_heatMollify_affineComp_trans hh hε.ne' hs a] with ω hω z w
  have hc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [lfppDOn_affine ξ _ hc (mem_closedSq01_iff hs) z w, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul, closedUnitSquare_eq]
  congr 1
  funext x
  exact hω x

end LQGMetric.DFGPS
