/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylLQG at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric

/-!
# Weyl scaling by constants and bounded functions for LQG metrics (GM.S1.6, DFGPS.S5)

GM (arXiv:1905.00383v3, `uniqueness-final.tex` l. 300–302, Axiom III) together with Axiom I
(length space) gives, for a constant `c`, `D_{h+c} = e^{ξ c} D_h` (GM.S1.6, used e.g. at
l. 458, 516, 1069), and for a continuous `f` with `a ≤ ξ f ≤ b`,
`e^a D_h ≤ D_{h+f} ≤ e^b D_h` (DFGPS (arXiv:1904.00384) and GM, used with
`a = −ξ‖f‖∞`, `b = ξ‖f‖∞`). The deterministic step is `LQGMetric.weylScale_of_eq_const` and
`LQGMetric.weylScale_mem_Icc_of_isLength`; here they are combined with Axioms I and III.

Internal metrics (blueprint GM.S5.W, GM l. 3403–3550): a.s., for all continuous `f`, open `U`,
`D_{h+f}(·,·;U)` is the Weyl infimum over `D_h`-length-parametrized paths in `U`
(`ae_internal_addFun`); in particular if `ξ f ≡ c` on `U` then
`D_{h+f}(·,·;U) = e^c D_h(·,·;U)` (`ae_internal_addFun_of_eq_const`). Deterministic input:
`LQGMetric.weylScaleOn_eq_internal`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric

section Deterministic

variable {ξ : ℝ} {Dm : DistC → ContMetric} {h : DistC}

/-- Axiom I + III (pathwise) ⇒ `D_{h+c} = e^{ξ c} D_h`. -/
theorem dist_addConst_of_weyl (hlen : (Dm h).IsLength)
    (hweyl : ∀ (f : C(ℂ, ℝ)) (z w : ℂ),
      weylScale ξ f (Dm h) z w = ENNReal.ofReal ((Dm (addFun h f)).1 (z, w)))
    (c : ℝ) (z w : ℂ) :
    (Dm (addConst h c)).1 (z, w) = Real.exp (ξ * c) * (Dm h).1 (z, w) := by
  have h1 := hweyl (ContinuousMap.const ℂ c) z w
  rw [weylScale_const_of_isLength hlen] at h1
  have hd : 0 ≤ (Dm h).1 (z, w) := dist_nonneg (x := (Dm h).pt z) (y := (Dm h).pt w)
  have hd' : 0 ≤ (Dm (addConst h c)).1 (z, w) :=
    dist_nonneg (x := (Dm (addConst h c)).pt z) (y := (Dm (addConst h c)).pt w)
  exact ((ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (Real.exp_pos _).le hd) hd').1 h1).symm

/-- Axiom I + III (pathwise) ⇒ `a ≤ ξ f ≤ b` gives `e^a D_h ≤ D_{h+f} ≤ e^b D_h`. -/
theorem dist_addFun_mem_Icc_of_weyl (hlen : (Dm h).IsLength)
    (hweyl : ∀ (f : C(ℂ, ℝ)) (z w : ℂ),
      weylScale ξ f (Dm h) z w = ENNReal.ofReal ((Dm (addFun h f)).1 (z, w)))
    {f : C(ℂ, ℝ)} {a b : ℝ} (ha : ∀ x, a ≤ ξ * f x) (hb : ∀ x, ξ * f x ≤ b) (z w : ℂ) :
    Real.exp a * (Dm h).1 (z, w) ≤ (Dm (addFun h f)).1 (z, w) ∧
      (Dm (addFun h f)).1 (z, w) ≤ Real.exp b * (Dm h).1 (z, w) := by
  obtain ⟨h1, h2⟩ := weylScale_mem_Icc_of_isLength (z := z) (w := w) hlen ha hb
  rw [hweyl f z w] at h1 h2
  have hd : 0 ≤ (Dm h).1 (z, w) := dist_nonneg (x := (Dm h).pt z) (y := (Dm h).pt w)
  have hd' : 0 ≤ (Dm (addFun h f)).1 (z, w) :=
    dist_nonneg (x := (Dm (addFun h f)).pt z) (y := (Dm (addFun h f)).pt w)
  exact ⟨(ENNReal.ofReal_le_ofReal_iff hd').1 h1,
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le hd)).1 h2⟩

end Deterministic

variable {γ : ℝ} {Dm : DistC → ContMetric}
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **GM.S1.6** for a strong LQG metric: a.s., for every constant `c`,
`D_{h+c} = e^{ξ c} D_h`. -/
theorem IsStrongLQGMetric.ae_dist_addConst (hD : IsStrongLQGMetric γ Dm)
    (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (z w : ℂ),
      (Dm (addConst (h ω) c)).1 (z, w) = Real.exp (xiGamma γ * c) * (Dm (h ω)).1 (z, w) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact dist_addConst_of_weyl hl hw

/-- **GM.S1.6** for a weak LQG metric (Axioms I and III only). -/
theorem IsWeakLQGMetric.ae_dist_addConst {c₀ : ℝ → ℝ} (hD : IsWeakLQGMetric γ Dm c₀)
    (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (z w : ℂ),
      (Dm (addConst (h ω) c)).1 (z, w) = Real.exp (xiGamma γ * c) * (Dm (h ω)).1 (z, w) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact dist_addConst_of_weyl hl hw

/-- **GM.S5.W** (strong metric): a.s., if `ξ f ≡ c` on an open `U`, then
`D_{h+f}(·,·;U) = e^c D_h(·,·;U)`. -/
theorem IsStrongLQGMetric.ae_internal_addFun_of_eq_const (hD : IsStrongLQGMetric γ Dm)
    (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (U : Set ℂ) (c : ℝ), IsOpen U → (∀ x ∈ U, xiGamma γ * f x = c) →
      ∀ z w : ℂ, (Dm (addFun (h ω) f)).internal U z w =
        ENNReal.ofReal (Real.exp c) * (Dm (h ω)).internal U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  intro f U c hU hf z w
  exact internal_eq_of_eq_const _ (fun x y => (hw f x y).symm) hU hf z w

/-- **GM.S5.W** (weak metric). -/
theorem IsWeakLQGMetric.ae_internal_addFun_of_eq_const {c₀ : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ Dm c₀) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (U : Set ℂ) (c : ℝ), IsOpen U → (∀ x ∈ U, xiGamma γ * f x = c) →
      ∀ z w : ℂ, (Dm (addFun (h ω) f)).internal U z w =
        ENNReal.ofReal (Real.exp c) * (Dm (h ω)).internal U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  intro f U c hU hf z w
  exact internal_eq_of_eq_const _ (fun x y => (hw f x y).symm) hU hf z w

end LQGMetric
