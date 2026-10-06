/-
# Reducing `GradOneExp` to the Ornstein–Uhlenbeck heat-flow contraction

`GaussianLogSobolevGradOneExp` (`GaussianLogSobolevGradOneForm.lean`) is the one-dimensional
Γ-form Gaussian log-Sobolev inequality in exponential form.  This module reduces it to a single
named **Ornstein–Uhlenbeck heat-flow** input `GaussianOUFlowContraction`, stated along the Mehler
semigroup `gaussianOUSemigroup`:

* the entropy along the flow becomes arbitrarily small: for every `ε > 0` there is `t ≥ 0` with
  `Ent(P_t h) ≤ ε`;
* the initial entropy is at most the entropy at time `t` plus the sharp Fisher term
  `(1 - e^{-2t})/2 · ∫ ‖∇ log h‖² h`.

The second clause is the integrated Fisher decay `I(P_s h) ≤ e^{-2s} I(h)` (i.e. the Γ₂ criterion
for the Gaussian) and the first is the convergence to equilibrium; both are the genuine
heat-flow content.  The log-Sobolev inequality follows by letting `t` grow: with `t` chosen so that
`Ent(P_t h) ≤ ε` one gets `Ent(h) ≤ ε + I(h)/2` for every `ε > 0`.

* `gaussianOUSemigroup` — the Mehler (Ornstein–Uhlenbeck) semigroup on `Fin 1 → ℝ`;
* `GaussianOUFlowContraction` — the named heat-flow input;
* `gaussianLogSobolevGrad_of_ouFlow` — the input implies `GaussianLogSobolevGrad 1`;
* `gaussianLogSobolevGradOneExp_of_ouFlow` — and hence `GaussianLogSobolevGradOneExp`.
-/
import LatticeProb.Prob.GaussianLogSobolevGradOneForm

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The one-dimensional Mehler (Ornstein–Uhlenbeck) semigroup** on the standard Gaussian
`γ₁ = Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)`:
`P_t h x = ∫ z, h (e^{-t} x + √(1 - e^{-2t}) z) ∂γ₁(z)`. -/
def gaussianOUSemigroup (t : ℝ) (h : (Fin 1 → ℝ) → ℝ) : (Fin 1 → ℝ) → ℝ :=
  fun x => ∫ z, h (fun i => Real.exp (-t) * x i
      + Real.sqrt (1 - Real.exp (-2 * t)) * z i)
    ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)

/-- **The Ornstein–Uhlenbeck heat-flow input.**  Along the Mehler semigroup `gaussianOUSemigroup`
the entropy tends to the equilibrium value `0` (in the `ε`-sense), and the initial entropy is at
most the entropy at time `t` plus the sharp Fisher term `(1 - e^{-2t})/2 · I(h)`.  The latter is the
integrated Fisher decay `I(P_s h) ≤ e^{-2s} I(h)` produced by the `Γ₂` criterion. -/
def GaussianOUFlowContraction : Prop :=
  ∀ h : (Fin 1 → ℝ) → ℝ, (∀ x, 0 < h x) → ContDiff ℝ 1 h →
    Integrable h (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1) = 1) →
    (∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 ≤ t ∧
      (∫ x, gaussianOUSemigroup t h x * Real.log (gaussianOUSemigroup t h x)
        ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) ≤ ε) ∧
    (∀ t : ℝ, 0 ≤ t →
      (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        ≤ (∫ x, gaussianOUSemigroup t h x * Real.log (gaussianOUSemigroup t h x)
            ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
          + (1 - Real.exp (-2 * t)) / 2
            * ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
                ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))

/-- **The heat-flow input implies the one-dimensional Γ-form log-Sobolev inequality.**  Choose
`t` with `Ent(P_t h) ≤ ε`; the contraction clause gives `Ent(h) ≤ ε + (1 - e^{-2t})/2 · I(h)
≤ ε + I(h)/2`, and `ε > 0` is arbitrary. -/
theorem gaussianLogSobolevGrad_of_ouFlow (hou : GaussianOUFlowContraction) :
    GaussianLogSobolevGrad 1 := by
  intro h hpos hcont hint hintlog hgradint hnorm
  obtain ⟨hsmall, hineq⟩ := hou h hpos hcont hint hintlog hgradint hnorm
  have hI0 : 0 ≤ (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
      ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (le_of_lt (hpos x))
  have hkey : ∀ ε : ℝ, 0 < ε →
      (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        ≤ (1 / 2) * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
              ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) + ε := by
    intro ε hε
    obtain ⟨t, ht0, ht⟩ := hsmall ε hε
    have hcoef : (1 - Real.exp (-2 * t)) / 2 ≤ 1 / 2 := by
      have := Real.exp_pos (-2 * t); linarith
    have hIle : (1 - Real.exp (-2 * t)) / 2
        * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
            ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        ≤ 1 / 2 * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
            ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) :=
      mul_le_mul_of_nonneg_right hcoef hI0
    calc (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        ≤ (∫ x, gaussianOUSemigroup t h x * Real.log (gaussianOUSemigroup t h x)
              ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
            + (1 - Real.exp (-2 * t)) / 2
              * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
                  ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) := hineq t ht0
      _ ≤ ε + 1 / 2 * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
              ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) :=
          add_le_add ht hIle
      _ = (1 / 2) * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
              ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) + ε := by ring
  exact le_of_forall_pos_le_add hkey

/-- **The heat-flow input implies the exponential form** `GaussianLogSobolevGradOneExp`, through
the Γ-form and the log/exp equivalence of `GaussianLogSobolevGradOneForm.lean`. -/
theorem gaussianLogSobolevGradOneExp_of_ouFlow (hou : GaussianOUFlowContraction) :
    GaussianLogSobolevGradOneExp :=
  gaussianLogSobolevGradOneExp_of_grad (gaussianLogSobolevGrad_of_ouFlow hou)

/-- **The dissipation half of `GaussianOUFlowContraction`.**  Along the Mehler semigroup the
entropy drops by at least the sharp Fisher term.  This is the integrated Fisher decay
`I(P_s h) ≤ e^{-2s} I(h)` produced by the `Γ₂` criterion for the Gaussian. -/
def GaussianOUDissipation : Prop :=
  ∀ h : (Fin 1 → ℝ) → ℝ, (∀ x, 0 < h x) → ContDiff ℝ 1 h →
    Integrable h (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1) = 1) →
    ∀ t : ℝ, 0 ≤ t →
      (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        - (∫ x, gaussianOUSemigroup t h x * Real.log (gaussianOUSemigroup t h x)
            ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
        ≤ (1 - Real.exp (-2 * t)) / 2
            * (∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
                ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))

/-- **The convergence half of `GaussianOUFlowContraction`.**  The entropy along the Mehler
semigroup becomes arbitrarily small: the ergodicity of the Ornstein–Uhlenbeck flow drives `P_t h`
to the equilibrium `1`. -/
def GaussianOUEntropyConvergence : Prop :=
  ∀ h : (Fin 1 → ℝ) → ℝ, (∀ x, 0 < h x) → ContDiff ℝ 1 h →
    Integrable h (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1) = 1) →
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 ≤ t ∧
      (∫ x, gaussianOUSemigroup t h x * Real.log (gaussianOUSemigroup t h x)
        ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) ≤ ε

/-- **`GaussianOUFlowContraction` from its two halves.**  The two clauses are independent — the
dissipation bound alone only gives a lower bound on `Ent(P_t h)`, never that it vanishes — so the
input splits into the dissipation and the entropy-convergence factors. -/
theorem gaussianOUFlowContraction_of_dissipation_convergence
    (hd : GaussianOUDissipation) (hc : GaussianOUEntropyConvergence) :
    GaussianOUFlowContraction := by
  intro h hpos hcont hint hintlog hgradint hnorm
  refine ⟨hc h hpos hcont hint hintlog hgradint hnorm, fun t ht => ?_⟩
  have h := hd h hpos hcont hint hintlog hgradint hnorm t ht
  linarith

/-- **The exponential form from the two halves**, through `GaussianOUFlowContraction`. -/
theorem gaussianLogSobolevGradOneExp_of_dissipation_convergence
    (hd : GaussianOUDissipation) (hc : GaussianOUEntropyConvergence) :
    GaussianLogSobolevGradOneExp :=
  gaussianLogSobolevGradOneExp_of_ouFlow
    (gaussianOUFlowContraction_of_dissipation_convergence hd hc)

end LatticeProb
