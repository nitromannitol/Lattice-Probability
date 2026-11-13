/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Rescale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window

/-!
# The deterministic rescaling step of [18] Lemma 4.9

Source: [18] ("Using the γ-LQG coordinate change formula (2.6), we
find that `u^ε_*(z)` (resp. `ε^{-(q−4ζ)}(B^ε_z − z)`) is determined by `(ĥ, ĥ^IG)` in the same manner that
`u^{ε̂}_*(0)` (resp. `B^{ε̂}_0`) is determined by `(h, h^IG)` … Since `B^ε_z ⊂ B_{ε^{q−4ζ}}(z)` on `F^ε(z)`, we infer
that a.s. `X_{a₁,a₂} ≤ X̂_{a₁,a₂}`").

For a curve `c` (the area-time SLE), a point `z` with first hitting time `τ_z`, a spatial scale `r > 0` and a time
scale `λ > 0`, the rescaled curve is `ĉ(t) = r⁻¹ (c(τ_z + λ t) − z)`, rooted at time `0` at the point `0`.
The localized quantities of [18] §4.2 use **Lebesgue** area in `DA^ε` and only `ε`-*time* segments otherwise, so
The deterministic covariance `GMS4b.locUStar_affine` gives `u^ε_*(z)` for `c` = `u^{ε/λ}_*` of `ĉ` at root time `0`,
and the ball `B^ε_z` maps to `r⁻¹ (B^ε_z − z)`. When `diam c([τ_z − ε, τ_z + ε]) ≤ ε^q` and `4 ε^q ≤ θ r`, that ball
lies in `closedBall 0 θ`, so the source quantity equals the **masked** quantity of `ĉ` at mesh `ε/λ`:

* `L43O.maskedLocDA`, `L43O.maskedLocUStar`: `1{B^s_0 ⊆ B̄_θ(0)} DA^s(0)` and `1{B^s_0 ⊆ B̄_θ(0)} u^s_*(0)`
  at root time `0` ([18] `X̂`);
* `L43O.areaRatio_eq_maskedLocDA_rescaled`, `L43O.uStar_eq_maskedLocUStar_rescaled`: the identities above;
* `L43O.maskedLocDA_le`, `L43O.maskedLocUStar_le`: the masked quantities are at most the unmasked ones.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.L43O

open GMS4b

/-- The rescaled curve `t ↦ r⁻¹ (c(τ_z + λ t) − z)` of the proof of [18] Lemma 4.9. -/
def rescaledCurve (c : ℝ → ℂ) (z : ℂ) (r l : ℝ) : ℝ → ℂ :=
  affineCurve ((r : ℂ)⁻¹) (-((r : ℂ)⁻¹ * z)) c (hitTime c z) l

theorem rescaledCurve_apply (c : ℝ → ℂ) (z : ℂ) (r l t : ℝ) :
    rescaledCurve c z r l t = (r : ℂ)⁻¹ * (c (hitTime c z + l * t) - z) := by
  simp only [rescaledCurve, affineCurve]
  ring

/-- `1{B^s_0 ⊆ B̄_θ(0)} DA^s(0)` at root time `0` (the source's `X̂`, [18]). -/
def maskedLocDA (θ s : ℝ) (c : ℝ → ℂ) : ℝ≥0∞ := by
  classical
  exact if locBall s c 0 ⊆ closedBall (0 : ℂ) θ then locDA s c 0 else 0

/-- `1{B^s_0 ⊆ B̄_θ(0)} u^s_*(0)` at root time `0`. -/
def maskedLocUStar (θ s : ℝ) (c : ℝ → ℂ) : ℝ≥0∞ := by
  classical
  exact if locBall s c 0 ⊆ closedBall (0 : ℂ) θ then locUStar s c 0 else 0

theorem maskedLocDA_le (θ s : ℝ) (c : ℝ → ℂ) : maskedLocDA θ s c ≤ locDA s c 0 := by
  unfold maskedLocDA
  split_ifs <;> simp

theorem maskedLocUStar_le (θ s : ℝ) (c : ℝ → ℂ) : maskedLocUStar θ s c ≤ locUStar s c 0 := by
  unfold maskedLocUStar
  split_ifs <;> simp

/-- The ball `B^{ε/λ}_0` of the rescaled curve is `r⁻¹ (B^ε_z − z)`, i.e. the closed ball of radius
`r⁻¹ · 4 diam c([τ_z − ε, τ_z + ε])` about `0`. -/
theorem locBall_rescaledCurve {c : ℝ → ℂ} {z : ℂ} (hcz : c (hitTime c z) = z) {r l : ℝ} (hr : 0 < r)
    (hl : 0 < l) (ε : ℝ) :
    locBall (ε / l) (rescaledCurve c z r l) 0 =
      closedBall (0 : ℂ) (r⁻¹ * (4 * windowDiam ε c z)) := by
  have hA : ((r : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
  rw [rescaledCurve, locBall_affine _ _ hA c hl, mul_zero, add_zero, locBall,
    simC_image_closedBall, simC_apply, hcz, windowDiam]
  congr 1
  · ring
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- On the event `diam c([τ_z − ε, τ_z + ε]) ≤ ε^q`, with `4 ε^q ≤ θ r`, the ball of the rescaled curve lies in
`closedBall 0 θ`. -/
theorem locBall_rescaledCurve_subset {c : ℝ → ℂ} {z : ℂ} (hcz : c (hitTime c z) = z) {r l : ℝ}
    (hr : 0 < r) (hl : 0 < l) {ε q θ : ℝ} (hdiam : windowDiam ε c z ≤ ε ^ q)
    (hθ : 4 * ε ^ q ≤ θ * r) :
    locBall (ε / l) (rescaledCurve c z r l) 0 ⊆ closedBall (0 : ℂ) θ := by
  rw [locBall_rescaledCurve hcz hr hl]
  refine closedBall_subset_closedBall ?_
  rw [inv_mul_le_iff₀ hr]
  linarith

/-- **The rescaling identity for `DA`.** On `diam c([τ_z − ε, τ_z + ε]) ≤ ε^q`, with `4 ε^q ≤ θ r`,
`DA^ε(z)` of `c` equals the masked `DA^{ε/λ}(0)` of the rescaled curve. -/
theorem areaRatio_eq_maskedLocDA_rescaled {c : ℝ → ℂ} {z : ℂ} (hcz : c (hitTime c z) = z) {r l : ℝ}
    (hr : 0 < r) (hl : 0 < l) {ε q θ : ℝ} (hdiam : windowDiam ε c z ≤ ε ^ q)
    (hθ : 4 * ε ^ q ≤ θ * r) :
    areaRatio ε c z = maskedLocDA θ (ε / l) (rescaledCurve c z r l) := by
  have hA : ((r : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
  rw [maskedLocDA, ite_eq_left_of_eq_true _ _ (eq_true (locBall_rescaledCurve_subset hcz hr hl hdiam hθ)), rescaledCurve,
    locDA_affine _ _ hA c hl, mul_zero, add_zero, areaRatio]

/-- **The rescaling identity for `u_*`.** On `diam c([τ_z − ε, τ_z + ε]) ≤ ε^q`, with `4 ε^q ≤ θ r`,
`u^ε_*(z)` of `c` equals the masked `u^{ε/λ}_*(0)` of the rescaled curve. -/
theorem uStar_eq_maskedLocUStar_rescaled {c : ℝ → ℂ} {z : ℂ} (hcz : c (hitTime c z) = z) {r l : ℝ}
    (hr : 0 < r) (hl : 0 < l) {ε q θ : ℝ} (hdiam : windowDiam ε c z ≤ ε ^ q)
    (hθ : 4 * ε ^ q ≤ θ * r) :
    uStar ε c z = maskedLocUStar θ (ε / l) (rescaledCurve c z r l) := by
  have hA : ((r : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
  rw [maskedLocUStar, ite_eq_left_of_eq_true _ _ (eq_true (locBall_rescaledCurve_subset hcz hr hl hdiam hθ)), rescaledCurve,
    locUStar_affine _ _ hA c hl, mul_zero, add_zero, uStar]

end MatedCRTHarmonic.L43O
