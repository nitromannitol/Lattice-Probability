/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Topology.PolarTemplate at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: remove unused simp arguments.
   v4.35 port: remove unused tactics.
   v4.35 port: replace unnecessary simpa. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Topology.PlanarCore
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

/-!
# The polar crossing template and free curve distance

The free distance is the infimum of the uniform costs over increasing order isomorphisms of the
unit interval. Each such order isomorphism is a homeomorphism, so this is the `d_F` distance
after linear normalization of its time interval.
-/

namespace MatedCRTHarmonic.Topology

open Set Real
open QuantumZipper.CA.Topo

/-- A normalized continuous curve in the plane. -/
abbrev PlaneCurve := C(unitInterval, ℂ)

/-- The increasing changes of time used in `dF`. -/
abbrev IncreasingParametrization := unitInterval ≃o unitInterval

/-- Uniform error for a fixed increasing reparametrization. -/
noncomputable def frechetCost (γ δ : PlaneCurve) (φ : IncreasingParametrization) : ℝ :=
  ‖γ - δ.comp φ.toHomeomorph‖

/-- Fréchet distance modulo increasing homeomorphisms of `[0,1]`. -/
noncomputable def dF (γ δ : PlaneCurve) : ℝ :=
  sInf (Set.range fun φ : IncreasingParametrization => frechetCost γ δ φ)

/-- Pointwise error is bounded by the uniform cost of a fixed time change. -/
theorem norm_curve_sub_reparam_le_frechetCost (γ δ : PlaneCurve)
    (φ : IncreasingParametrization) (t : unitInterval) :
    ‖γ t - δ (φ t)‖ ≤ frechetCost γ δ φ := by
  let err : PlaneCurve := γ - δ.comp φ.toHomeomorph
  calc
    ‖γ t - δ (φ t)‖ = ‖err t‖ := by simp [err]
    _ ≤ ‖err‖ := err.norm_coe_le_norm t
    _ = frechetCost γ δ φ := rfl

/-- A strict `dF` bound supplies one increasing homeomorphism with the same pointwise bound. -/
theorem exists_reparam_of_dF_lt {γ δ : PlaneCurve} {ε : ℝ} (hε : dF γ δ < ε) :
    ∃ φ : IncreasingParametrization, ∀ t, ‖γ t - δ (φ t)‖ < ε := by
  have hcost : ∃ φ : IncreasingParametrization, frechetCost γ δ φ < ε := by
    change sInf (Set.range fun φ : IncreasingParametrization => frechetCost γ δ φ) < ε at hε
    have hnonempty : (Set.range fun φ : IncreasingParametrization => frechetCost γ δ φ).Nonempty :=
      ⟨frechetCost γ δ (OrderIso.refl unitInterval), ⟨OrderIso.refl unitInterval, rfl⟩⟩
    obtain ⟨c, hc, hclt⟩ := exists_lt_of_csInf_lt hnonempty hε
    obtain ⟨φ, rfl⟩ := hc
    exact ⟨φ, hclt⟩
  obtain ⟨φ, hφ⟩ := hcost
  exact ⟨φ, fun t => (norm_curve_sub_reparam_le_frechetCost γ δ φ t).trans_lt hφ⟩

/-- Radius coordinate of the polar template, in its unnormalized time `u ∈ [0,4]`. -/
noncomputable def polarRadius (u : ℝ) : ℝ :=
  1 - u / 10 + (3 / 10) * max (u - 1) 0 - (3 / 10) * max (u - 2) 0 +
    (1 / 10) * max (u - 3) 0

/-- Argument coordinate of the polar template, in its unnormalized time `u ∈ [0,4]`. -/
noncomputable def polarAngle (u : ℝ) : ℝ :=
  (2 * π - 1 / 10) * max (u - 2) 0 +
    (1 / 5 - (2 * π - 1 / 10)) * max (u - 3) 0

/-- Polar template `T(u) = r(u) exp(i θ(u))`, normalized from `[0,4]` to `[0,1]`. -/
noncomputable def polarTemplate : PlaneCurve :=
  ⟨fun t =>
      ((polarRadius (4 * (t : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((polarAngle (4 * (t : ℝ)) : ℝ) : ℂ) * Complex.I),
    by
      have hr : Continuous fun t : unitInterval => polarRadius (4 * (t : ℝ)) := by
        unfold polarRadius
        fun_prop
      have hθ : Continuous fun t : unitInterval => polarAngle (4 * (t : ℝ)) := by
        unfold polarAngle
        fun_prop
      fun_prop⟩

/-- The radius on the whole template stays in `[9/10, 11/10]`. -/
theorem polarRadius_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu4 : u ≤ 4) :
    9 / 10 ≤ polarRadius u ∧ polarRadius u ≤ 11 / 10 := by
  by_cases h1 : u ≤ 1
  · have h2 : u - 2 ≤ 0 := by linarith
    have h3 : u - 3 ≤ 0 := by linarith
    simp [polarRadius, max_eq_right (sub_nonpos.mpr h1),
      max_eq_right h2, max_eq_right h3]
    constructor <;> linarith
  · by_cases h2 : u ≤ 2
    · have hU : 1 ≤ u := le_of_not_ge h1
      have h3 : u - 3 ≤ 0 := by linarith
      simp [polarRadius, max_eq_left (sub_nonneg.mpr hU),
        max_eq_right (sub_nonpos.mpr h2), max_eq_right h3]
      constructor <;> linarith
    · by_cases h3 : u ≤ 3
      · have hU2 : 2 ≤ u := le_of_not_ge h2
        have hU1 : 1 ≤ u := by linarith
        have hL3 : u - 3 ≤ 0 := by linarith
        simp [polarRadius, max_eq_left (sub_nonneg.mpr hU1),
          max_eq_left (sub_nonneg.mpr hU2), max_eq_right hL3]
        constructor <;> linarith
      · have hU3 : 3 ≤ u := le_of_not_ge h3
        have hU2 : 2 ≤ u := by linarith
        have hU1 : 1 ≤ u := by linarith
        simp [polarRadius, max_eq_left (sub_nonneg.mpr hU1),
          max_eq_left (sub_nonneg.mpr hU2), max_eq_left (sub_nonneg.mpr hU3)]
        constructor <;> linarith

/-- On the radial segment `[1,2]` the polar angle is zero. -/
theorem polarAngle_eq_zero_on_radial {u : ℝ} (hu2 : u ≤ 2) :
    polarAngle u = 0 := by
  have h1 : u - 2 ≤ 0 := by linarith
  have h2 : u - 3 ≤ 0 := by linarith
  simp [polarAngle, max_eq_right h1, max_eq_right h2]

/-- On the final angular segment the polar angle runs from `2π-1/10` to `2π+1/10`. -/
theorem polarAngle_bounds_on_final {u : ℝ} (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    2 * π - 1 / 10 ≤ polarAngle u ∧ polarAngle u ≤ 2 * π + 1 / 10 := by
  have heq : polarAngle u = 2 * π - 1 / 10 + (1 / 5) * (u - 3) := by
    simp [polarAngle, max_eq_left (sub_nonneg.mpr (show 2 ≤ u by linarith)),
      max_eq_left (sub_nonneg.mpr hu3)]
    ring
  rw [heq]
  constructor <;> nlinarith [hu3, hu4]

/-- The norm of the polar template is its radius coordinate. -/
theorem polarTemplate_norm (t : unitInterval) :
    ‖polarTemplate t‖ = polarRadius (4 * (t : ℝ)) := by
  rw [polarTemplate, ContinuousMap.coe_mk]
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]
  have hr : 0 ≤ polarRadius (4 * (t : ℝ)) := by
    have ht0 : 0 ≤ 4 * (t : ℝ) := mul_nonneg (by norm_num) t.2.1
    have ht4 : 4 * (t : ℝ) ≤ 4 := by nlinarith [t.2.2]
    exact (le_trans (by norm_num : (0 : ℝ) ≤ 9 / 10) (polarRadius_bounds ht0 ht4).1)
  rw [abs_of_nonneg hr, mul_one]

/-- Template values on the radial crossing block have zero imaginary part. -/
theorem polarTemplate_im_eq_zero_on_radial {t : unitInterval}
    (ht0 : (1 / 4 : ℝ) ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ (1 / 2 : ℝ)) :
    (polarTemplate t).im = 0 := by
  have ht0' : 0 ≤ 4 * (t : ℝ) := by positivity
  have ht2' : 4 * (t : ℝ) ≤ 2 := by nlinarith [ht1]
  rw [polarTemplate, ContinuousMap.coe_mk]
  have hθ := polarAngle_eq_zero_on_radial ht2'
  rw [Complex.exp_ofReal_mul_I]
  simp [hθ]

/-- On the final angular block, the real coordinate stays close to one. -/
theorem polarTemplate_re_bounds_on_final {t : unitInterval}
    (ht0 : (3 / 4 : ℝ) ≤ t) (_ht1 : t ≤ 1) :
    199 / 200 ≤ (polarTemplate t).re ∧ (polarTemplate t).re ≤ 1 := by
  have hu3 : 3 ≤ 4 * (t : ℝ) := by nlinarith [ht0]
  have hu4 : 4 * (t : ℝ) ≤ 4 := by nlinarith [_ht1, t.2.2]
  have hθ := polarAngle_bounds_on_final hu3 hu4
  rw [polarTemplate, ContinuousMap.coe_mk]
  have hr : polarRadius (4 * (t : ℝ)) = 1 := by
    unfold polarRadius
    simp [max_eq_left (sub_nonneg.mpr (show 1 ≤ 4 * (t : ℝ) by linarith)),
      max_eq_left (sub_nonneg.mpr (show 2 ≤ 4 * (t : ℝ) by linarith)),
      max_eq_left (sub_nonneg.mpr hu3)]
    nlinarith
  rw [hr]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  have hperiod :
      Real.cos (polarAngle (4 * (t : ℝ))) =
        Real.cos (polarAngle (4 * (t : ℝ)) - 2 * π) := by
    rw [← Real.cos_add_two_pi (polarAngle (4 * (t : ℝ)) - 2 * π)]
    ring_nf
  rw [hperiod]
  constructor
  · have hsmall : |polarAngle (4 * (t : ℝ)) - 2 * π| ≤ 1 / 10 := by
      rw [abs_le]
      constructor <;> linarith [hθ.1, hθ.2]
    have := Real.one_sub_sq_div_two_le_cos
      (x := polarAngle (4 * (t : ℝ)) - 2 * π)
    nlinarith [sq_abs (polarAngle (4 * (t : ℝ)) - 2 * π), hsmall]
  · nlinarith [Real.cos_le_one (polarAngle (4 * (t : ℝ)) - 2 * π)]

/-- The two ends of the final arc cross the horizontal axis by a definite amount. -/
theorem polarTemplate_im_endpoints_final :
    (polarTemplate ⟨3 / 4, by norm_num, by norm_num⟩).im = -Real.sin (1 / 10) ∧
      (polarTemplate (1 : unitInterval)).im = Real.sin (1 / 10) := by
  constructor
  · simp only [polarTemplate, ContinuousMap.coe_mk]
    change ((((polarRadius (4 * (3 / 4 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((polarAngle (4 * (3 / 4 : ℝ)) : ℝ) : ℂ) * Complex.I))).im = _
    rw [show 4 * (3 / 4 : ℝ) = 3 by norm_num]
    have hr : polarRadius 3 = 1 := by norm_num [polarRadius]
    have hθ : polarAngle 3 = 2 * π - 1 / 10 := by
      simp only [polarAngle, show max (3 - 2 : ℝ) 0 = 1 by norm_num,
        show max (3 - 3 : ℝ) 0 = 0 by norm_num]
      ring
    rw [hr, hθ, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, zero_add]
    rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
    ring_nf
  · simp only [polarTemplate, ContinuousMap.coe_mk]
    change ((((polarRadius (4 * (1 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((polarAngle (4 * (1 : ℝ)) : ℝ) : ℂ) * Complex.I))).im = _
    rw [show 4 * (1 : ℝ) = 4 by norm_num]
    have hr : polarRadius 4 = 1 := by norm_num [polarRadius]
    have hθ : polarAngle 4 = 2 * π + 1 / 10 := by
      simp only [polarAngle, show max (4 - 2 : ℝ) 0 = 2 by norm_num,
        show max (4 - 3 : ℝ) 0 = 1 by norm_num]
      ring
    rw [hr, hθ, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, zero_add]
    rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
    ring_nf

/-- The ends of the radial crossing block have radii `9/10` and `11/10`. -/
theorem polarTemplate_radial_endpoints :
    polarTemplate ⟨1 / 4, by norm_num, by norm_num⟩ = (9 / 10 : ℂ) ∧
      polarTemplate ⟨1 / 2, by norm_num, by norm_num⟩ = (11 / 10 : ℂ) := by
  constructor <;> norm_num [polarTemplate, polarRadius, polarAngle]

/-- A curve within the stated tolerance of the polar template has a self-intersection, with the
first visit on the radial crossing block and the second on the final angular block. -/
theorem exists_polarTemplate_self_intersection {γ : PlaneCurve}
    (φ : IncreasingParametrization)
    (hnear : ∀ u, ‖γ u - polarTemplate (φ u)‖ < 1 / 50) :
    ∃ s t : ℝ, s < t ∧ ∃ hs : s ∈ unitInterval, ∃ ht : t ∈ unitInterval,
      γ ⟨s, hs⟩ = γ ⟨t, ht⟩ ∧
        ((1 / 4 : ℝ) ≤ (φ ⟨s, hs⟩ : ℝ) ∧ (φ ⟨s, hs⟩ : ℝ) ≤ 1 / 2) ∧
        ((3 / 4 : ℝ) ≤ (φ ⟨t, ht⟩ : ℝ) ∧ (φ ⟨t, ht⟩ : ℝ) ≤ 1) := by
  let p : Path (γ 0) (γ 1) := ⟨γ, rfl, rfl⟩
  let f := p.extend
  let q₁ : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩
  let q₂ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let q₃ : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩
  let q₄ : unitInterval := 1
  let a₂ := φ.symm q₁
  let b₂ := φ.symm q₂
  let a₄ := φ.symm q₃
  let b₄ := φ.symm q₄
  have ha₂ : φ a₂ = q₁ := by simp [a₂]
  have hb₂ : φ b₂ = q₂ := by simp [b₂]
  have ha₄ : φ a₄ = q₃ := by simp [a₄]
  have hb₄ : φ b₄ = q₄ := by simp [b₄]
  have ha₂b₂ : a₂ < b₂ := by
    apply φ.symm.strictMono
    norm_num [q₁, q₂]
  have ha₄b₄ : a₄ < b₄ := by
    apply φ.symm.strictMono
    change (3 / 4 : ℝ) < (1 : ℝ)
    norm_num
  have hb₂a₄ : b₂ < a₄ := by
    apply φ.symm.strictMono
    norm_num [q₂, q₃]
  have hnear_ext (x : ℝ) (hx : x ∈ unitInterval) :
      ‖f x - polarTemplate (φ ⟨x, hx⟩)‖ < 1 / 50 := by
    have hx' : (⟨x, hx⟩ : unitInterval) = ⟨x, hx⟩ := rfl
    rw [p.extend_extends' ⟨x, hx⟩]
    exact hnear ⟨x, hx⟩
  have hq₁ : polarTemplate q₁ = (9 / 10 : ℂ) := by
    convert polarTemplate_radial_endpoints.1 using 1
  have hq₂ : polarTemplate q₂ = (11 / 10 : ℂ) := by
    convert polarTemplate_radial_endpoints.2 using 1
  have hradial_re_a : |(γ a₂).re - 9 / 10| < 1 / 50 := by
    have h := Complex.abs_re_le_norm (γ a₂ - polarTemplate q₁)
    have h' : |(γ a₂).re - (polarTemplate q₁).re| ≤
        ‖γ a₂ - polarTemplate q₁‖ := by simpa [q₁] using h
    have hnear' := hnear a₂
    rw [ha₂] at hnear'
    have hcombine := h'.trans_lt hnear'
    have hre : (polarTemplate q₁).re = 9 / 10 := by rw [hq₁]; norm_num
    rw [hre] at hcombine
    exact hcombine
  have hradial_re_b : |(γ b₂).re - 11 / 10| < 1 / 50 := by
    have h := Complex.abs_re_le_norm (γ b₂ - polarTemplate q₂)
    have h' : |(γ b₂).re - (polarTemplate q₂).re| ≤
        ‖γ b₂ - polarTemplate q₂‖ := by simpa [q₂] using h
    have hnear' := hnear b₂
    rw [hb₂] at hnear'
    have hcombine := h'.trans_lt hnear'
    have hre : (polarTemplate q₂).re = 11 / 10 := by rw [hq₂]; norm_num
    rw [hre] at hcombine
    exact hcombine
  have hfinal_im_a : (γ a₄).im < -1 / 20 := by
    have hsin : 7 / 100 < Real.sin (1 / 10) := by
      have := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1 / 10)
      norm_num at this ⊢
      linarith
    have h := Complex.abs_im_le_norm (γ a₄ - polarTemplate q₃)
    have hT : (polarTemplate q₃).im = -Real.sin (1 / 10) := by
      simpa [q₃] using polarTemplate_im_endpoints_final.1
    have hnear' := hnear a₄
    rw [ha₄] at hnear'
    have habs : |(γ a₄).im + Real.sin (1 / 10)| < 1 / 50 := by
      simpa [hT, Complex.sub_im] using h.trans_lt hnear'
    rw [abs_lt] at habs
    linarith
  have hfinal_im_b : 1 / 20 < (γ b₄).im := by
    have hsin : 7 / 100 < Real.sin (1 / 10) := by
      have := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1 / 10)
      norm_num at this ⊢
      linarith
    have h := Complex.abs_im_le_norm (γ b₄ - polarTemplate q₄)
    have hT : (polarTemplate q₄).im = Real.sin (1 / 10) := by
      simpa [q₄] using polarTemplate_im_endpoints_final.2
    have hnear' := hnear b₄
    rw [hb₄] at hnear'
    have habs : |(γ b₄).im - Real.sin (1 / 10)| < 1 / 50 := by
      simpa [hT, Complex.sub_im] using h.trans_lt hnear'
    rw [abs_lt] at habs
    linarith
  have hradial_start : (f a₂).re < 19 / 20 := by
    have h := hradial_re_a
    rw [abs_lt] at h
    have hf : f (a₂ : ℝ) = γ a₂ := by
      simp [f, p]
    rw [hf]
    norm_num at h ⊢
    linarith
  have hradial_end : 21 / 20 < (f b₂).re := by
    have h := hradial_re_b
    rw [abs_lt] at h
    have hf : f (b₂ : ℝ) = γ b₂ := by
      simp [f, p]
    rw [hf]
    norm_num at h ⊢
    linarith
  have hradial_cont : ContinuousOn (fun x : ℝ => (f x).re) (Icc (a₂ : ℝ) b₂) :=
    (Complex.continuous_re.comp f.continuous).continuousOn
  obtain ⟨s₁, t₁, hs₁, hs₁t₁, ht₁, hfs₁, hft₁, hcross₁⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (α := (a₂ : ℝ)) (β := (b₂ : ℝ))
      (z := 19 / 20) (w := 21 / 20) (by exact_mod_cast ha₂b₂.le)
      hradial_cont (by norm_num) (by simpa using hradial_start.le)
      (by simpa using hradial_end.le)
  have hfinal_cont : ContinuousOn (fun x : ℝ => (f x).im) (Icc (a₄ : ℝ) b₄) :=
    (Complex.continuous_im.comp f.continuous).continuousOn
  obtain ⟨s₂, t₂, hs₂, hs₂t₂, ht₂, hfs₂, hft₂, hcross₂⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun x => (f x).im)
      (α := (a₄ : ℝ)) (β := (b₄ : ℝ)) (z := (-1 / 20 : ℝ)) (w := 1 / 20)
      (by exact_mod_cast ha₄b₄.le)
      hfinal_cont (by norm_num)
      (by
        have hf : f (a₄ : ℝ) = γ a₄ := by simp [f, p]
        rw [hf]
        exact le_of_lt hfinal_im_a)
      (by
        have hf : f (b₄ : ℝ) = γ b₄ := by simp [f, p]
        rw [hf]
        exact le_of_lt hfinal_im_b)
  have hfirst_re : ∀ x ∈ Icc s₁ t₁, (f x).re ∈ Icc (19 / 20) (21 / 20) := hcross₁
  have hsecond_im : ∀ x ∈ Icc s₂ t₂, (f x).im ∈ Icc (-1 / 20) (1 / 20) := hcross₂
  have hfirst_im : ∀ x ∈ Icc s₁ t₁, (f x).im ∈ Icc (-1 / 20) (1 / 20) := by
    intro x hx
    have hxlo : (a₂ : ℝ) ≤ x := hs₁.trans hx.1
    have hxhi : x ≤ b₂ := hx.2.trans ht₁
    let u : unitInterval := ⟨x, ⟨(show (0 : ℝ) ≤ (a₂ : ℝ) from a₂.2.1).trans hxlo,
      hxhi.trans b₂.2.2⟩⟩
    have hle : a₂ ≤ u := by exact_mod_cast hxlo
    have hge : u ≤ b₂ := by exact_mod_cast hxhi
    have hu₁ : q₁ ≤ φ u := by rw [← ha₂]; exact φ.monotone hle
    have hu₂ : φ u ≤ q₂ := by rw [← hb₂]; exact φ.monotone hge
    have hT : (polarTemplate (φ u)).im = 0 :=
      polarTemplate_im_eq_zero_on_radial (by exact_mod_cast hu₁) (by exact_mod_cast hu₂)
    have hcloseu : ‖f x - polarTemplate (φ u)‖ < 1 / 50 := by
      simpa using hnear_ext x u.2
    have him := Complex.abs_im_le_norm (f x - polarTemplate (φ u))
    have habs : |(f x).im| < 1 / 50 := by
      simpa [hT, Complex.sub_im] using him.trans_lt hcloseu
    rw [abs_lt] at habs
    exact ⟨by linarith, by linarith⟩
  have hfinal_re : ∀ x ∈ Icc s₂ t₂, (f x).re ∈ Icc (19 / 20) (21 / 20) := by
    intro x hx
    have hxlo : (a₄ : ℝ) ≤ x := hs₂.trans hx.1
    have hxhi : x ≤ b₄ := hx.2.trans ht₂
    let u : unitInterval := ⟨x, ⟨(show (0 : ℝ) ≤ (a₄ : ℝ) from a₄.2.1).trans hxlo,
      hxhi.trans b₄.2.2⟩⟩
    have hle : a₄ ≤ u := by exact_mod_cast hxlo
    have hge : u ≤ b₄ := by exact_mod_cast hxhi
    have hu₃ : q₃ ≤ φ u := by rw [← ha₄]; exact φ.monotone hle
    have hu₄ : φ u ≤ q₄ := by rw [← hb₄]; exact φ.monotone hge
    have ht₃ : (3 / 4 : ℝ) ≤ (φ u : ℝ) := by exact_mod_cast hu₃
    have hT := polarTemplate_re_bounds_on_final (t := φ u) ht₃ (by simpa [q₄] using hu₄)
    have hcloseu : ‖f x - polarTemplate (φ u)‖ < 1 / 50 := by
      simpa using hnear_ext x u.2
    have habs := Complex.abs_re_le_norm (f x - polarTemplate (φ u))
    have habs' : |(f x).re - (polarTemplate (φ u)).re| < 1 / 50 := by
      simpa [Complex.sub_re] using habs.trans_lt hcloseu
    rw [abs_lt] at habs'
    constructor <;> nlinarith [hT.1, hT.2]
  let crossLR : ℝ → ℂ := fun u => f (s₁ + (t₁ - s₁) * u)
  let crossBT : ℝ → ℂ := fun u => f (s₂ + (t₂ - s₂) * (1 - u))
  have hparamLR (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      s₁ + (t₁ - s₁) * u ∈ Icc s₁ t₁ := by constructor <;> nlinarith [hu.1, hu.2, hs₁t₁]
  have hparamBT (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      s₂ + (t₂ - s₂) * (1 - u) ∈ Icc s₂ t₂ := by constructor <;> nlinarith [hu.1, hu.2, hs₂t₂]
  have hcrossLRc : ContinuousOn crossLR (Icc (0 : ℝ) 1) := by
    dsimp [crossLR]
    fun_prop
  have hcrossBTc : ContinuousOn crossBT (Icc (0 : ℝ) 1) := by
    dsimp [crossBT]
    fun_prop
  have hcrossLRmap : MapsTo crossLR (Icc (0 : ℝ) 1)
      (LQGMetric.RectCross.rect (19 / 20) (21 / 20) (-1 / 20) (1 / 20)) := by
    intro u hu
    have hx := hparamLR u hu
    exact ⟨hfirst_re _ hx, hfirst_im _ hx⟩
  have hcrossBTmap : MapsTo crossBT (Icc (0 : ℝ) 1)
      (LQGMetric.RectCross.rect (19 / 20) (21 / 20) (-1 / 20) (1 / 20)) := by
    intro u hu
    have hx := hparamBT u hu
    exact ⟨hfinal_re _ hx, hsecond_im _ hx⟩
  have hcrossLR0 : (crossLR 0).re = 19 / 20 := by
    simp [crossLR, hfs₁]
  have hcrossLR1 : (crossLR 1).re = 21 / 20 := by
    simp [crossLR, hft₁]
  have hcrossBT0 : (crossBT 0).im = 1 / 20 := by
    simp [crossBT, hft₂]
  have hcrossBT1 : (crossBT 1).im = -1 / 20 := by
    simp [crossBT, hfs₂]
  obtain ⟨u, hu, v, hv, heq⟩ := LQGMetric.RectMeet.rect_crossings_meet
    (19 / 20) (21 / 20) (-1 / 20) (1 / 20) crossLR crossBT
    hcrossLRc hcrossBTc hcrossLRmap hcrossBTmap hcrossLR0 hcrossLR1 hcrossBT0 hcrossBT1
  let s := s₁ + (t₁ - s₁) * u
  let t := s₂ + (t₂ - s₂) * (1 - v)
  have hsrange : s ∈ Icc s₁ t₁ := by simpa [s] using hparamLR u hu
  have htrange : t ∈ Icc s₂ t₂ := by simpa [t] using hparamBT v hv
  have hst : s < t := by
    have ht1s2 : t₁ < s₂ :=
      lt_of_le_of_lt ht₁ (lt_of_lt_of_le (by exact_mod_cast hb₂a₄) hs₂)
    linarith [hsrange.2, htrange.1]
  have hfeq : f s = f t := by simpa [s, t, crossLR, crossBT] using heq
  have hsMem : s ∈ unitInterval := ⟨(a₂.2.1).trans (le_trans hs₁ hsrange.1),
    (le_trans hsrange.2 (le_trans ht₁ b₂.2.2))⟩
  have htMem : t ∈ unitInterval := ⟨(a₄.2.1).trans (le_trans hs₂ htrange.1),
    le_trans htrange.2 (le_trans ht₂ b₄.2.2)⟩
  have hf_s : f s = γ ⟨s, hsMem⟩ := by
    simpa [f, p] using p.extend_extends' ⟨s, hsMem⟩
  have hf_t : f t = γ ⟨t, htMem⟩ := by
    simpa [f, p] using p.extend_extends' ⟨t, htMem⟩
  have hsI : a₂ ≤ (⟨s, hsMem⟩ : unitInterval) := by exact_mod_cast (le_trans hs₁ hsrange.1)
  have hsI' : (⟨s, hsMem⟩ : unitInterval) ≤ b₂ := by exact_mod_cast (le_trans hsrange.2 ht₁)
  have htI : a₄ ≤ (⟨t, htMem⟩ : unitInterval) := by exact_mod_cast (le_trans hs₂ htrange.1)
  have htI' : (⟨t, htMem⟩ : unitInterval) ≤ b₄ := by exact_mod_cast (le_trans htrange.2 ht₂)
  have hφs₁ : q₁ ≤ φ ⟨s, hsMem⟩ := by rw [← ha₂]; exact φ.monotone hsI
  have hφs₂ : φ ⟨s, hsMem⟩ ≤ q₂ := by rw [← hb₂]; exact φ.monotone hsI'
  have hφt₁ : q₃ ≤ φ ⟨t, htMem⟩ := by rw [← ha₄]; exact φ.monotone htI
  have hφt₂ : φ ⟨t, htMem⟩ ≤ q₄ := by rw [← hb₄]; exact φ.monotone htI'
  refine ⟨s, t, hst, hsMem, htMem, ?_, ?_⟩
  · rw [← hf_s, ← hf_t]
    exact hfeq
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact_mod_cast hφs₁
    · exact_mod_cast hφs₂
    · exact_mod_cast hφt₁
    · exact_mod_cast hφt₂

end MatedCRTHarmonic.Topology
