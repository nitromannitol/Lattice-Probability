/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistDist at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistField
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# The random distribution `⟨h, φ⟩ = ∫ F ∂_re ∂_im φ` (task P2-EXIST)

For a continuous field `F`, `antiDist F := ofCont F ∘ ∂_re ∂_im` is a distribution (mathlib's
`TestFunction.lineDerivCLM` makes `φ ↦ ∂_re ∂_im φ` a continuous linear map of `𝓓(ℂ)`, so no
seminorm estimate is needed). For a field `Y : ℂ → Ω → ℝ` continuous in `x` and measurable in
`ω`, `ω ↦ antiDist (Y · ω)` is measurable for the cylinder σ-algebra (`measurable_gffOf`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set

namespace LQGMetric
namespace GFFExist

/-- `φ ↦ ∂_re ∂_im φ` on `𝓓(ℂ)` -/
def d12 : TestC →L[ℝ] TestC :=
  (TestFunction.lineDerivCLM ℝ (1 : ℂ) : TestC →L[ℝ] TestC).comp
    (TestFunction.lineDerivCLM ℝ Complex.I : TestC →L[ℝ] TestC)

/-- `⟨antiDist F, φ⟩ = ∫ F ∂_re ∂_im φ` -/
def antiDist (f : C(ℂ, ℝ)) : DistC := (ofCont f).comp d12

lemma antiDist_apply (f : C(ℂ, ℝ)) (φ : TestC) : antiDist f φ = ∫ x, d12 φ x * f x :=
  ofCont_apply_heat f (d12 φ)

variable {Ω : Type*}

/-- the random distribution built from a continuous field `Y` -/
def gffOf (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) : DistC :=
  antiDist ⟨fun x => Y x ω, hYc ω⟩

lemma gffOf_apply (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) (φ : TestC) :
    gffOf Y hYc ω φ = ∫ x, d12 φ x * Y x ω :=
  antiDist_apply _ φ

lemma measurable_gffOf [MeasurableSpace Ω] (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) : Measurable (gffOf Y hYc) := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [gffOf_apply]
  have hj : Measurable (Function.uncurry Y) :=
    measurable_uncurry_of_continuous_of_measurable (u := Y) (fun ω => hYc ω) hYm
  have hd : Continuous (d12 φ : ℂ → ℝ) := (d12 φ).continuous
  have hF : Measurable fun p : ℂ × Ω => d12 φ p.1 * Y p.1 p.2 :=
    (hd.measurable.comp measurable_fst).mul hj
  exact (hF.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

end GFFExist
end LQGMetric
