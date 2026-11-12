/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43Frk at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43CM

/-!
# GM §5.2: the event `𝔈_r` and the Radon–Nikodym bound (5.5) (task P2-M2N, WP-M2n)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.

* `frkE` : the event `𝔈_r^{𝕫,𝕨}(z)` of GM l. 2759–2771 ((5.4) and (5.5)), as a set of fields,
  centred at `z` directly (GM: the event at `0` for the translated field `h(· + z) − h_1(z)`,
  l. 2846), for the geodesic `P = sel 𝕫 𝕨 g` parametrized on `[0,1]` (`0 < s < t < 1` is GM's
  `0 < s < t < D_h(𝕫,𝕨)`), and a set `G` of test functions (GM: `𝓖_r`, translated to `z`).
* `frkE_zero_iff` : at `z = 0` the main condition (5.4) is `ShortcutConcl` (the conclusion (5.3)
  of Prop 5.2 (C)), so `frkE` at `h − φ` is exactly what Prop 5.2 (B), (C) produce (GM (5.7)).
* `cmDensity_neg_le_of_frkE` : on `𝔈_r`, the Cameron–Martin density of `h − φ` w.r.t. `h`,
  `M_h = exp(−(h,φ)_∇ − ½(φ,φ)_∇)`, is `≤ Λ` for `φ ∈ G` (GM l. 2813: "By (5.5), on `𝔈_r`, we
  have `M_h ≤ Λ`"), the hypothesis `hΛ` of `condExp_le_cm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Laplacian
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the main condition (5.4) of `𝔈_r` at centre `z` for a path `Q` on `[0,1]` -/
def frkDist (D D' : DistC → ContMetric) (cs Cs c₂ b₀ r : ℝ) (z : ℂ) (g : DistC)
    (Q : C(unitInterval, ℂ)) : Prop :=
  ∃ s t : unitInterval, 0 < s ∧ s < t ∧ t < 1 ∧
    Q s ∈ Metric.ball z (3 / 2 * r) ∧ Q t ∈ Metric.ball z (3 / 2 * r) ∧
    b₀ * r ≤ ‖Q s - Q t‖ ∧ (D' g).1 (Q s, Q t) ≤ c₂ * (D g).1 (Q s, Q t) ∧
    ENNReal.ofReal ((D' g).1 (Q s, Q t)) ≤
      ENNReal.ofReal (cs / Cs) * setDist (D' g) {Q s} (Metric.sphere z (3 * r))

/-- **GM's event `𝔈_r^{𝕫,𝕨}(z)`** (l. 2759–2771): (5.4) for the geodesic `sel 𝕫 𝕨 g` and
(5.5) `exp(−(g,φ)_∇ + ½(φ,φ)_∇) ≤ Λ` for all `φ ∈ G`. -/
def frkE (D D' : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (cs Cs c₂ b₀ Λ r : ℝ) (G : Set TestC) (z a b : ℂ) : Set DistC :=
  {g | frkDist D D' cs Cs c₂ b₀ r z g (sel a b g) ∧
    ∀ φ ∈ G, Real.exp (-dirInner g φ + gradEnergy φ / 2) ≤ Λ}

lemma cmTest_neg_cm (φ : TestC) : cmTest (-φ) = -cmTest φ := by
  ext x
  show -(2 * Real.pi)⁻¹ * Δ (⇑(-φ)) x = -(-(2 * Real.pi)⁻¹ * Δ (⇑φ) x)
  have e : (⇑(-φ) : ℂ → ℝ) = -⇑φ := rfl
  rw [e, InnerProductSpace.laplacian_neg]
  simp only [Pi.neg_apply]
  ring

lemma gradEnergy_neg_cm (φ : TestC) : gradEnergy (⇑(-φ)) = gradEnergy ⇑φ := by
  have e : (⇑(-φ) : ℂ → ℝ) = -⇑φ := rfl
  simp only [gradEnergy, e, fderiv_neg, norm_neg]

lemma gradEnergy_nonneg_cm (φ : ℂ → ℝ) : 0 ≤ gradEnergy φ := by
  unfold gradEnergy
  exact mul_nonneg (inv_nonneg.2 (by positivity)) (MeasureTheory.integral_nonneg fun _ => by positivity)

/-- the Cameron–Martin density of `h − φ` at a field `g`: `exp(−(g,φ)_∇ − ½(φ,φ)_∇)` -/
lemma cmDensity_neg_pair0 (φ : TestC) (g : DistC) :
    cmDensity (-φ) (pair0 g) = Real.exp (-dirInner g φ - gradEnergy φ / 2) := by
  unfold cmDensity
  have e1 : pair0 g (cmTest0 (-φ)) = -dirInner g φ := by
    show g (cmTest (-φ)) = -g (cmTest φ)
    rw [cmTest_neg_cm, map_neg]
  rw [e1, gradEnergy_neg_cm]

/-- GM l. 2813: by (5.5), on `𝔈_r` the Radon–Nikodym derivative `M_h` is `≤ Λ` -/
lemma cmDensity_neg_le_of_frkE {D D' : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {cs Cs c₂ b₀ Λ r : ℝ} {G : Set TestC}
    {z a b : ℂ} {g : DistC} (hg : g ∈ frkE D D' sel cs Cs c₂ b₀ Λ r G z a b) {φ : TestC}
    (hφ : φ ∈ G) : cmDensity (-φ) (pair0 g) ≤ Λ := by
  rw [cmDensity_neg_pair0]
  refine le_trans (Real.exp_le_exp.2 ?_) (hg.2 φ hφ)
  linarith [gradEnergy_nonneg_cm ⇑φ]

end LQGMetric.GM
