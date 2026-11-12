/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Complex.CircleArcBall at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arcs of the unit circle and the balls `B_I` of CONF Lemma 2.14

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), proof of Lemma 2.14 (`lem-disconnect-set`, confluence-final.tex 853–877).
For an arc `φ⁻¹(I)` of `∂𝔻` of length `r_I ≤ π/4` with centre `u_I`, CONF puts
`w_I := (1 − r_I) u_I` and `B_I := B_{r_I/100}(w_I)` and observes (C:876) that `B_I` lies in the
sector of `𝔻` over the arc, so that the balls `B_I` are disjoint when the arcs meet only at
their endpoints.

Here an arc is `circArc θ ℓ = {e^{it} : t ∈ [θ, θ + ℓ]}` (length `ℓ`), its relative interior is
`circArcOpen θ ℓ` (`t ∈ (θ, θ+ℓ)`), its centre `arcCenter θ ℓ = e^{i(θ+ℓ/2)}` and
`arcPt θ ℓ = (1 − ℓ) e^{i(θ+ℓ/2)}` is CONF's `w_I`.

* `div_norm_mem_circArcOpen_of_mem_ball`: for `0 < ℓ ≤ π/4` and `z ∈ B_{ℓ/100}(w)`, the radial
  projection `z/|z|` lies in the open arc (the sector statement of C:876);
* `disjoint_ball_arcPt`: disjoint open arcs give disjoint balls `B_I`.

The sector claim is stated without proof in CONF; the argument here (argument of `z ū` controlled
by `|sin ψ| ≥ (2/π)|ψ|`, Jordan's inequality, mathlib `Real.mul_le_sin`) is an own elementary
proof.
-/

namespace LQGMetric

open Set Metric Complex Real

/-- The closed arc `{e^{it} : θ ≤ t ≤ θ + ℓ}` of the unit circle. -/
noncomputable def circArc (θ ℓ : ℝ) : Set ℂ := (fun t : ℝ => exp (t * I)) '' Icc θ (θ + ℓ)

/-- The relative interior `{e^{it} : θ < t < θ + ℓ}` of `circArc θ ℓ`. -/
noncomputable def circArcOpen (θ ℓ : ℝ) : Set ℂ := (fun t : ℝ => exp (t * I)) '' Ioo θ (θ + ℓ)

/-- The centre `u_I = e^{i(θ+ℓ/2)}` of the arc `circArc θ ℓ` (CONF C:858). -/
noncomputable def arcCenter (θ ℓ : ℝ) : ℂ := exp (((θ + ℓ / 2 : ℝ) : ℂ) * I)

/-- CONF's point `w_I := (1 − r_I) u_I` (C:862) for the arc `circArc θ ℓ`, `r_I = ℓ`. -/
noncomputable def arcPt (θ ℓ : ℝ) : ℂ := ((1 - ℓ : ℝ) : ℂ) * arcCenter θ ℓ

theorem norm_arcCenter (θ ℓ : ℝ) : ‖arcCenter θ ℓ‖ = 1 := norm_exp_ofReal_mul_I _

theorem norm_arcPt {θ ℓ : ℝ} (hℓ : ℓ ≤ 1) : ‖arcPt θ ℓ‖ = 1 - ℓ := by
  rw [arcPt, norm_mul, norm_arcCenter, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- **Sector property of `B_I`** (CONF C:876): if `0 < ℓ ≤ π/4` and `|z − w_I| < ℓ/100` then
`z ≠ 0` and `z/|z|` lies in the open arc. -/
theorem div_norm_mem_circArcOpen_of_mem_ball {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ' : ℓ ≤ π / 4) {z : ℂ}
    (hz : z ∈ ball (arcPt θ ℓ) (ℓ / 100)) :
    z ≠ 0 ∧ z / (‖z‖ : ℂ) ∈ circArcOpen θ ℓ := by
  have hpi := Real.pi_lt_d2
  set u := arcCenter θ ℓ with hu
  have hu1 : ‖u‖ = 1 := norm_arcCenter θ ℓ
  have huu : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]; simp
  set q := z * (starRingEnd ℂ) u with hq
  have hzq : z = q * u := by rw [hq, mul_assoc, huu, mul_one]
  have hqe : q - ((1 - ℓ : ℝ) : ℂ) = (z - arcPt θ ℓ) * (starRingEnd ℂ) u := by
    rw [hq, arcPt, ← hu, sub_mul, mul_assoc, mul_comm u, huu, mul_one]
  have hqn : ‖q - ((1 - ℓ : ℝ) : ℂ)‖ < ℓ / 100 := by
    rw [hqe, norm_mul, Complex.norm_conj, hu1, mul_one, ← dist_eq_norm]; exact mem_ball.1 hz
  have hre : |q.re - (1 - ℓ)| < ℓ / 100 := by
    have := (abs_re_le_norm (q - ((1 - ℓ : ℝ) : ℂ))).trans_lt hqn
    simpa using this
  have him : |q.im| < ℓ / 100 := by
    have := (abs_im_le_norm (q - ((1 - ℓ : ℝ) : ℂ))).trans_lt hqn
    simpa using this
  have hre0 : 1 / 5 < q.re := by
    have := (abs_lt.1 hre).1; nlinarith
  have hqnorm : q.re ≤ ‖q‖ := re_le_norm q
  have hq0 : q ≠ 0 := by intro h; rw [h] at hre0; simp at hre0; linarith
  have hnzq : ‖z‖ = ‖q‖ := by rw [hzq, norm_mul, hu1, mul_one]
  set ψ := arg q with hψ
  have hψ2 : |ψ| < π / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith))
  have hsin : |Real.sin ψ| < ℓ / 20 := by
    rw [hψ, sin_arg, abs_div, abs_of_nonneg (norm_nonneg q)]
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  -- Jordan's inequality: `(2/π)|ψ| ≤ |sin ψ|`
  have hjor : 2 / π * |ψ| ≤ |Real.sin ψ| := by
    rcases le_total 0 ψ with h0 | h0
    · rw [abs_of_nonneg h0]
      have := Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hψ2; linarith)
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h0]
      have := Real.mul_le_sin (x := -ψ) (by linarith)
        (by rw [abs_of_nonpos h0] at hψ2; linarith)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hψl : |ψ| < ℓ / 2 := by
    have h1 : 2 / π * |ψ| < ℓ / 20 := hjor.trans_lt hsin
    have hpi0 : 0 < π := Real.pi_pos
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi0] at h1
    nlinarith [abs_nonneg ψ]
  have hz0 : z ≠ 0 := by
    intro h; apply hq0; rw [hq, h, zero_mul]
  refine ⟨hz0, θ + ℓ / 2 + ψ, ⟨?_, ?_⟩, ?_⟩
  · linarith [(abs_lt.1 hψl).1]
  · linarith [(abs_lt.1 hψl).2]
  · have hzn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hz0).ne'
    have hq' : q = (‖q‖ : ℂ) * exp (ψ * I) := (norm_mul_exp_arg_mul_I q).symm
    have key : z = (‖z‖ : ℂ) * exp (((θ + ℓ / 2 + ψ : ℝ) : ℂ) * I) := by
      calc z = q * u := hzq
        _ = (‖q‖ : ℂ) * exp (ψ * I) * exp (((θ + ℓ / 2 : ℝ) : ℂ) * I) := by
          rw [← hq', hu, arcCenter]
        _ = _ := by
          rw [hnzq, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    show exp (((θ + ℓ / 2 + ψ : ℝ) : ℂ) * I) = z / (‖z‖ : ℂ)
    rw [eq_div_iff hzn, mul_comm]; exact key.symm

/-- **Disjointness of the balls `B_I`** (CONF C:876): disjoint open arcs of length `≤ π/4` give
disjoint balls `B_{ℓ/100}(w_I)`. -/
theorem disjoint_ball_arcPt {θ ℓ θ' ℓ' : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ π / 4) (hℓ' : 0 < ℓ')
    (hℓ1' : ℓ' ≤ π / 4) (hd : Disjoint (circArcOpen θ ℓ) (circArcOpen θ' ℓ')) :
    Disjoint (ball (arcPt θ ℓ) (ℓ / 100)) (ball (arcPt θ' ℓ') (ℓ' / 100)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.1 hd (div_norm_mem_circArcOpen_of_mem_ball hℓ hℓ1 hz).2
    (div_norm_mem_circArcOpen_of_mem_ball hℓ' hℓ1' hz').2

end LQGMetric
