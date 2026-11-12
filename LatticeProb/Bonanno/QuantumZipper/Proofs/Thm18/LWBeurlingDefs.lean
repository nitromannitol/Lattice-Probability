/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWBeurlingDefs at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LWF-4: statement plan for the Beurling estimate (Carleman route)

Task BEURLING-PLAN (plan: `handoff/LW-BEURLING.md`). Target: `LWFar.BeurlingHarmStmt`
(`LWFarDefs.lean`), the analytic Beurling estimate with the sharp exponent `1/2`
(G. Lawler, B. Werness, arXiv:1011.3551, Prop 2.1, p. 5; Lawler, *Conformally Invariant
Processes in the Plane*, Thm 3.69, p. 67 printed / PDF p. 77).

**Route: Carleman's method in logarithmic coordinates** (J. Garnett, D. Marshall, *Harmonic
Measure*, Cambridge 2005, Appendix G, Theorem G.1, Lemma G.2 and (G.2)–(G.6), pp. 480–482
printed = PDF pp. 498–500; Carleman 1933). Put `v = φ_ε ∘ ĥ`, where `ĥ` is `h` on the component
`V` of `D ∩ B(w, ρ)` containing `w` and `0` elsewhere, and `φ_ε` is a `C²` convex cut-off vanishing
on `(-∞, ε]`. Then `v` is `C²` and subharmonic on `B(w, ρ)` (no boundary regularity needed), and
`V(ζ) = v(w + e^ζ)` is `C²`, `2πi`-periodic and satisfies `V_tt + V_θθ ≥ 0` on `{Re ζ < log ρ}`.
For `I(t) = ∫_{-π}^{π} V(t + iθ)² dθ`: `I'' = 2∫(V_t² + V V_tt) ≥ 2∫V_t² + 2∫V_θ²` (periodic
integration by parts), and on circles meeting `K` (where `V = 0`) the sharp Wirtinger inequality
`∫V² ≤ 4∫V_θ²` (GM (G.2) with interval length `2π`) with Cauchy–Schwarz gives
`I'² + I² ≤ 2 I I''` (GM Lemma G.2 with `ℓ = 2π`). Hence `J = √I` has `J'' ≥ J/4`, so
`I(log d) ≤ 4 (d/ρ') I(log ρ')`; and `I` is convex and bounded, hence nondecreasing, so
`2π φ_ε(h w)² ≤ I(log d)`. This gives `h(w) ≤ 2ε + 2 (d/ρ')^{1/2}`.

Departures from GM App. G (own adaptation, recorded in DEVIATIONS): GM work with the harmonic
measure of a domain with analytic boundary and its Dirichlet integral; we use the `C²`
subharmonic function `φ_ε ∘ ĥ` on the whole disk (so no smoothing of the domain and no Green
formula), log-polar cross sections (circles with one zero instead of vertical segments with zero
end values), and a first-order comparison for `J = √I` instead of GM's (G.6) (which needs
`ϕ(0) = 0`).

This file contains definitions only (no proofs, no hypotheses assumed anywhere).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-! ## Log-polar partial derivatives and the circle energy -/

/-- `∂_t V` for `ζ = t + iθ`. -/
def lpDt (V : ℂ → ℝ) (ζ : ℂ) : ℝ := fderiv ℝ V ζ 1

/-- `∂_θ V` for `ζ = t + iθ`. -/
def lpDθ (V : ℂ → ℝ) (ζ : ℂ) : ℝ := fderiv ℝ V ζ Complex.I

/-- `∂_t² V`. -/
def lpDtt (V : ℂ → ℝ) (ζ : ℂ) : ℝ := fderiv ℝ (lpDt V) ζ 1

/-- `∂_θ² V`. -/
def lpDθθ (V : ℂ → ℝ) (ζ : ℂ) : ℝ := fderiv ℝ (lpDθ V) ζ Complex.I

/-- Carleman's circle energy `I(t) = ∫_{-π}^{π} V(t + iθ)² dθ` (GM App. G, `ϕ(x)`). -/
def lpI (V : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (-π)..π, V ((t : ℂ) + (θ : ℂ) * Complex.I) ^ 2

/-- The formula for `I'(t) = 2 ∫ V V_t dθ`. -/
def lpI1 (V : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (-π)..π, 2 * (V ((t : ℂ) + (θ : ℂ) * Complex.I) *
    lpDt V ((t : ℂ) + (θ : ℂ) * Complex.I))

/-- The formula for `I''(t) = 2 ∫ (V_t² + V V_tt) dθ`. -/
def lpI2 (V : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (-π)..π, 2 * (lpDt V ((t : ℂ) + (θ : ℂ) * Complex.I) ^ 2 +
    V ((t : ℂ) + (θ : ℂ) * Complex.I) * lpDtt V ((t : ℂ) + (θ : ℂ) * Complex.I))

/-! ## B1. Sharp Wirtinger inequality -/

/-- **B1a. Sharp Wirtinger inequality, Dirichlet form, interval of length `2π`** (GM (G.2),
p. 480, with `b − a = 2π`, so `(π/(b−a))² = 1/4`). Suggested proof: Picone's identity with the
ground state `sin((x−a)/2)` on `[a+δ, a+2π−δ]`, then `δ → 0`. -/
def WirtingerDirStmt : Prop :=
  ∀ (g g' : ℝ → ℝ) (a : ℝ), (∀ x ∈ Icc a (a + 2 * π), HasDerivAt g (g' x) x) →
    ContinuousOn g' (Icc a (a + 2 * π)) → g a = 0 → g (a + 2 * π) = 0 →
    ∫ x in a..a + 2 * π, g x ^ 2 ≤ 4 * ∫ x in a..a + 2 * π, g' x ^ 2

/-- **B1b. Sharp Wirtinger inequality on a circle with one zero** (from B1a by periodicity). -/
def WirtingerCircleStmt : Prop :=
  ∀ (g g' : ℝ → ℝ), (∀ x, HasDerivAt g (g' x) x) → Continuous g' →
    Function.Periodic g (2 * π) → (∃ θ₀ : ℝ, g θ₀ = 0) →
    ∫ x in (-π)..π, g x ^ 2 ≤ 4 * ∫ x in (-π)..π, g' x ^ 2

/-! ## B2. Carleman's differential inequality -/

/-- **B2a. Differentiation of the circle energy** (differentiation under the integral sign). -/
def CircleEnergyDerivStmt : Prop :=
  ∀ (V : ℂ → ℝ) (T : ℝ), ContDiffOn ℝ 2 V {ζ : ℂ | ζ.re < T} → ∀ t : ℝ, t < T →
    HasDerivAt (lpI V) (lpI1 V t) t ∧ HasDerivAt (lpI1 V) (lpI2 V t) t

/-- **B2b. Carleman's differential inequality** (GM Lemma G.2, p. 481, log-polar form with
`ℓ = 2π`): for a nonnegative `C²` periodic `V` with `V_tt + V_θθ ≥ 0`, `I'' ≥ 0`, and on every
circle where `V` has a zero, `I'² + I² ≤ 2 I I''`. -/
def CarlemanIneqStmt : Prop :=
  ∀ (V : ℂ → ℝ) (T : ℝ), ContDiffOn ℝ 2 V {ζ : ℂ | ζ.re < T} →
    (∀ ζ : ℂ, V (ζ + 2 * π * Complex.I) = V ζ) →
    (∀ ζ : ℂ, ζ.re < T → 0 ≤ V ζ) →
    (∀ ζ : ℂ, ζ.re < T → 0 ≤ lpDtt V ζ + lpDθθ V ζ) →
    ∀ t : ℝ, t < T → 0 ≤ lpI2 V t ∧
      ((∃ θ : ℝ, V ((t : ℂ) + (θ : ℂ) * Complex.I) = 0) →
        lpI1 V t ^ 2 + lpI V t ^ 2 ≤ 2 * lpI V t * lpI2 V t)

/-! ## B3. The ODE comparison -/

/-- **B3. Integration of Carleman's inequality** (own first-order comparison replacing GM (G.6)):
a bounded nonnegative convex `I` on `(-∞, T)` is nondecreasing, and `I'² + I² ≤ 2 I I''` on
`[a, T)` gives `I(a) ≤ 4 e^{a−b} I(b)` (i.e. `√I` grows like `e^{t/2}`). -/
def CarlemanODEStmt : Prop :=
  ∀ (I I1 I2 : ℝ → ℝ) (T M a : ℝ), (∀ t, t < T → HasDerivAt I (I1 t) t) →
    (∀ t, t < T → HasDerivAt I1 (I2 t) t) → (∀ t, t < T → 0 ≤ I t ∧ I t ≤ M) →
    (∀ t, t < T → 0 ≤ I2 t) → (∀ t, a ≤ t → t < T → I1 t ^ 2 + I t ^ 2 ≤ 2 * I t * I2 t) →
    MonotoneOn I (Iio T) ∧ ∀ b : ℝ, a ≤ b → b < T → I a ≤ 4 * Real.exp (a - b) * I b

/-! ## B4. The subharmonic cut-off and its log-polar form -/

/-- **B4a. A `C²` convex cut-off** (from `Real.smoothTransition`, own elementary construction). -/
def SmoothCutStmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ (∀ s, s ≤ ε → φ s = 0) ∧
    (∀ s, 0 ≤ deriv φ s ∧ deriv φ s ≤ 1) ∧ (∀ s, 0 ≤ deriv (deriv φ) s) ∧
    (∀ s, s - 2 * ε ≤ φ s)

/-- Local normal form of a `C²` subharmonic function of the type `φ ∘ (harmonic)`: near each point
of `U`, `v` is either identically `0` or `φ ∘ Re ∘ f` with `φ` convex `C²` and `f` holomorphic. -/
def LocConvHarmForm (v : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ x ∈ U, (v =ᶠ[𝓝 x] fun _ => (0 : ℝ)) ∨
    ∃ (φ : ℝ → ℝ) (f : ℂ → ℂ), ContDiff ℝ 2 φ ∧ (∀ s, 0 ≤ deriv (deriv φ) s) ∧
      AnalyticAt ℂ f x ∧ v =ᶠ[𝓝 x] fun y => φ (f y).re

/-- **B4b. The cut-off of the extension by zero has the local normal form** on `B(w, ρ)`
(harmonic ⇒ locally `Re` of a holomorphic function, mathlib
`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`; near `∂V ∩ B(w, ρ) ⊆ ∂D` the extension is
`< ε`, so the cut-off vanishes). The harmonicity is stated through the real part of local
holomorphic functions, to keep this file free of the harmonic API; see the plan. -/
def ExtLocalFormStmt : Prop :=
  ∀ (D : Set ℂ) (w : ℂ) (ρ ε : ℝ) (h : ℂ → ℝ) (φ : ℝ → ℝ), IsOpen D → 0 < ε →
    ContDiff ℝ 2 φ → (∀ s, s ≤ ε → φ s = 0) → (∀ s, 0 ≤ deriv (deriv φ) s) →
    (∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧
      h =ᶠ[𝓝 x] fun y => (f y).re) →
    (∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, dist x x₀ < δ → h x ≤ ε') →
    LocConvHarmForm (fun x => φ ((connectedComponentIn (D ∩ ball w ρ) w).indicator h x))
      (ball w ρ)

/-- **B4c. Log-polar subharmonicity**: if `v` has the local normal form on `B(w, ρ)`, then
`V(ζ) = v(w + e^ζ)` is `C²` on `{Re ζ < log ρ}` with `V_tt + V_θθ ≥ 0` there (for
`V = φ ∘ Re G`, `V_tt + V_θθ = φ''(Re G) |G'|²`). -/
def LogPolarSubharmStmt : Prop :=
  ∀ (v : ℂ → ℝ) (w : ℂ) (ρ : ℝ), 0 < ρ → LocConvHarmForm v (ball w ρ) →
    ContDiffOn ℝ 2 (fun ζ => v (w + Complex.exp ζ)) {ζ : ℂ | ζ.re < Real.log ρ} ∧
    ∀ ζ : ℂ, ζ.re < Real.log ρ →
      0 ≤ lpDtt (fun ζ => v (w + Complex.exp ζ)) ζ + lpDθθ (fun ζ => v (w + Complex.exp ζ)) ζ

end LWFar
end Thm18Asm
end QuantumZipper
