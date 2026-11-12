/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bTrans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bHit
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Rad

/-!
# Translating the events of Prop 5.2 to centre `z` (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 4.3, l. 2846–2848: `E_r(z)`, `𝔈_r^{𝕫,𝕨}(z)` are the events of Prop 5.2 for the field
`h(· + z) − h_1(z)`. Deterministic identities for the translated field `g(· + z) = affineComp 1 z g`
and the translated bump `φ(· − z) = transTest z φ`:
* `dirInner_affineComp` : `(g(· + z), ψ)_∇ = (g, ψ(· − z))_∇`; `gradEnergy_transTest`;
* `affineComp_subTest` : `(g − φ(· − z))(· + z) = g(· + z) − φ`;
* `tsupport_transTest_subset` : supports move with the translation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Laplacian
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `φ(· − z)` -/
abbrev transTest (z : ℂ) (φ : TestC) : TestC := testAffinePull 1 z φ

lemma transTest_apply (z : ℂ) (φ : TestC) (x : ℂ) : transTest z φ x = φ (x - z) := by
  rw [testAffinePull_apply 1 z one_ne_zero, Complex.ofReal_one, div_one]

lemma cmTest_transTest (z : ℂ) (φ : TestC) : cmTest (transTest z φ) = transTest z (cmTest φ) := by
  ext x
  rw [cmTest_apply, transTest_apply, cmTest_apply]
  have e : (⇑(transTest z φ) : ℂ → ℝ) = fun y => φ (y - z) := funext fun y => transTest_apply z φ y
  rw [e, MarkovWeyl2.laplacian_comp_sub]

lemma affineComp_one_apply (z : ℂ) (g : DistC) (ψ : TestC) :
    affineComp 1 z g ψ = g (transTest z ψ) := by
  rw [GFFInv.affineComp_apply]; simp

lemma dirInner_affineComp (z : ℂ) (g : DistC) (ψ : TestC) :
    dirInner (affineComp 1 z g) ψ = dirInner g (transTest z ψ) := by
  show affineComp 1 z g (cmTest ψ) = g (cmTest (transTest z ψ))
  rw [affineComp_one_apply, cmTest_transTest]

lemma gradEnergy_transTest (z : ℂ) (ψ : TestC) :
    gradEnergy (transTest z ψ) = gradEnergy ψ := by
  have e : (⇑(transTest z ψ) : ℂ → ℝ) = fun y => ψ (y + -z) :=
    funext fun y => by rw [transTest_apply, sub_eq_add_neg]
  unfold gradEnergy
  rw [e]
  congr 1
  simp_rw [fderiv_comp_add_right]
  exact integral_add_right_eq_self (fun x => ‖fderiv ℝ (⇑ψ) x‖ ^ 2) (-z)

lemma tsupport_transTest_subset {z : ℂ} {φ : TestC} {ρ : ℝ}
    (hφ : tsupport (φ : ℂ → ℝ) ⊆ Metric.ball 0 ρ) :
    tsupport (transTest z φ : ℂ → ℝ) ⊆ Metric.ball z ρ := by
  have e : (⇑(transTest z φ) : ℂ → ℝ) = (⇑φ) ∘ (Homeomorph.addRight (-z)) :=
    funext fun y => by rw [transTest_apply, Function.comp_apply, Homeomorph.coe_addRight,
      sub_eq_add_neg]
  rw [e, tsupport_comp_eq_preimage]
  intro x hx
  have := hφ hx
  simp only [Homeomorph.coe_addRight, Metric.mem_ball, dist_zero_right] at this
  rw [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg]
  exact this

lemma affineComp_subTest (z : ℂ) (g : DistC) (φ : TestC) :
    affineComp 1 z (subTest g (transTest z φ)) = subTest (affineComp 1 z g) φ := by
  rw [subTest, subTest, affineComp_addFun one_pos]
  congr 1
  ext x
  simp only [ContinuousMap.comp_apply, affinePt_apply, Complex.ofReal_one, one_mul]
  show -(transTest z φ) (x + z) = -φ x
  rw [transTest_apply, add_sub_cancel_right]

end LQGMetric.GM
