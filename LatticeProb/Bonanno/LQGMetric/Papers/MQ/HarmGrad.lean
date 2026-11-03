/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.HarmGrad at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Liouville

/-!
# Gradient estimate for harmonic functions (task P2-MQ)

MQ (Miller–Qian, arXiv:1812.03913, `lqg_geodesics.tex`) use the standard estimate (4.1),
`|∇𝔥(w)| ≲ sup|𝔥 − a| / dist(w, ∂B)` for a harmonic `𝔥` (l. 566–580, bounding the Dirichlet
energy of the cut-off harmonic part). Here:

* `norm_fderiv_le_of_harmonic` : if `g : ℂ → ℝ` is harmonic on `B(w, s)` and `|g − a| ≤ M` there,
  then `‖Dg(w)‖ ≤ 8M/s`.

Proof (standard, cf. Axler–Bourdon–Ramey, *Harmonic Function Theory*, Thm 2.10, here through
complex analysis): `g = Re F` with `F` holomorphic on the ball (mathlib
`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`); `H(ζ) = F(w + ζ) − F(w)` has `Re H ≤ 2M` and
`H(0) = 0`, so Borel–Carathéodory (mathlib `Complex.borelCaratheodory_zero`) gives `|H| ≤ 4M` on
`|ζ| = s/2`, and the Cauchy estimate (mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`)
gives `|F'(w)| ≤ 8M/s`; finally `Dg(w) v = Re(F'(w) v)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set Filter Topology

namespace LQGMetric.MQ

/-- **Gradient estimate** for harmonic functions: `‖Dg(w)‖ ≤ 8M/s`. -/
theorem norm_fderiv_le_of_harmonic {g : ℂ → ℝ} {w : ℂ} {s M a : ℝ} (hs : 0 < s) (hM : 0 < M)
    (hg : InnerProductSpace.HarmonicOnNhd g (ball w s)) (hb : ∀ y ∈ ball w s, |g y - a| ≤ M) :
    ‖fderiv ℝ g w‖ ≤ 8 * M / s := by
  obtain ⟨F, hFa, hFre⟩ := hg.exists_analyticOnNhd_ball_re_eq
  have hw : w ∈ ball w s := mem_ball_self hs
  have hFd : DifferentiableOn ℂ F (ball w s) := hFa.differentiableOn
  set d := deriv F w
  have hFw : HasDerivAt F d w := (hFa w hw).differentiableAt.hasDerivAt
  set H : ℂ → ℂ := fun ζ => F (w + ζ) - F w with hHdef
  have hHd : DifferentiableOn ℂ H (ball 0 s) := by
    intro ζ hζ
    have hwζ : w + ζ ∈ ball w s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hζ
    exact (((hFa _ hwζ).differentiableAt.comp ζ ((differentiableAt_const w).add
      differentiableAt_id)).sub_const _).differentiableWithinAt
  have hHre : MapsTo H (ball 0 s) {ζ | ζ.re ≤ 2 * M} := by
    intro ζ hζ
    have hwζ : w + ζ ∈ ball w s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; simpa using hζ
    simp only [mem_setOf_eq, hHdef, Complex.sub_re]
    have e1 : (F (w + ζ)).re = g (w + ζ) := hFre hwζ
    have e2 : (F w).re = g w := hFre hw
    rw [e1, e2]
    have h1 := hb _ hwζ
    have h2 := hb _ hw
    rw [abs_le] at h1 h2
    linarith
  have hH0 : H 0 = 0 := by simp [hHdef]
  have hs2 : 0 < s / 2 := half_pos hs
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) (s / 2), ‖H ζ‖ ≤ 4 * M := by
    intro ζ hζ
    have hn : ‖ζ‖ = s / 2 := by simpa using hζ
    have hζb : ζ ∈ ball (0 : ℂ) s := by
      rw [mem_ball, dist_zero_right, hn]; linarith
    have := Complex.borelCaratheodory_zero (by positivity : 0 < 2 * M) hHd hHre hs hζb hH0
    rw [hn] at this
    calc ‖H ζ‖ ≤ 2 * (2 * M) * (s / 2) / (s - s / 2) := this
      _ = 4 * M := by field_simp; ring
  have hcl : DiffContOnCl ℂ H (ball (0 : ℂ) (s / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hs2.ne']
    exact hHd.mono (closedBall_subset_ball (by linarith))
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs2 hcl hsph
  have hH' : HasDerivAt H d 0 := by
    have : HasDerivAt (fun ζ => F (w + ζ)) d 0 := by
      have h0 : HasDerivAt F d (w + 0) := by simpa using hFw
      exact h0.comp_const_add w 0
    exact this.sub_const _
  rw [hH'.deriv] at hder
  have hdle : ‖d‖ ≤ 8 * M / s := by
    calc ‖d‖ ≤ 4 * M / (s / 2) := hder
      _ = 8 * M / s := by field_simp; ring
  -- the real derivative of `g = Re F`
  set L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) with hLdef
  have hgL : HasFDerivAt g L w := by
    have h1 : HasFDerivAt F ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ)
        w := hFw.hasFDerivAt.restrictScalars ℝ
    have h2 : HasFDerivAt (fun y => (F y).re) L w := Complex.reCLM.hasFDerivAt.comp w h1
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy
    exact (hFre hy).symm
  rw [hgL.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  simp only [hLdef, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.reCLM_apply, Real.norm_eq_abs]
  calc |(v • d).re| ≤ ‖v • d‖ := Complex.abs_re_le_norm _
    _ = ‖v‖ * ‖d‖ := norm_smul _ _
    _ ≤ 8 * M / s * ‖v‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hdle (norm_nonneg _)

end LQGMetric.MQ
