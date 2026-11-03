/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryField at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Affine invariance of the `𝒟'(U)`-valued zero-boundary GFF (task P2-ZB, WP-14)

`testPullOn r z hr U : 𝓓(U) →L[ℝ] 𝓓(rU + z)`, `φ ↦ φ((·-z)/r)` (built with mathlib's
`TestFunction.mkCLM`, continuity on each `𝓓_K` from `continuous_pullK` of `Statement/Field`, as
for `testAffinePull`), and `distAffine r z hr : 𝒟'(rU + z) → 𝒟'(U)`,
`g ↦ g(r·+z) = r⁻² g ∘ testPullOn` (the restriction-compatible version of `affineComp`).

* `IsZeroBoundaryGFF.affine` : if `g` is a zero-boundary GFF on `rU + z`, then `g(r·+z)` is a
  zero-boundary GFF on `U` (`h̊^{rU+z}(r·+z) ~ h̊^U`; Sheffield math/0312099 §2.2), from the
  process version `IsZBGFFProcess.affine`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric

variable {r : ℝ} {z : ℂ}

lemma affK_subset_affOpens (hr : r ≠ 0) {U : Opens ℂ} {K : Compacts ℂ} (hK : (K : Set ℂ) ⊆ U) :
    (affK r z K : Set ℂ) ⊆ affOpens r z U := by
  rintro x ⟨y, hy, rfl⟩
  show affMap r z (r • y + z) ∈ (U : Set ℂ)
  have : affMap r z (r • y + z) = y := affMap_affFwd hr y
  rw [this]; exact hK hy

/-- `φ ↦ φ((·-z)/r)` as a continuous linear map `𝓓(U) → 𝓓(rU + z)` -/
def testPullOn (r : ℝ) (z : ℂ) (hr : r ≠ 0) (U : Opens ℂ) :
    TestOn U →L[ℝ] TestOn (affOpens r z U) :=
  TestFunction.mkCLM ℝ (zbPull r z hr) (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
    have : (zbPull r z hr ∘ TestFunction.ofSupportedIn hK) =
        TestFunction.ofSupportedInCLM ℝ (affK_subset_affOpens hr hK) ∘ pullK r z hr K := by
      funext φ; ext x; rfl
    rw [this]
    exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp (continuous_pullK r z hr K))

@[simp] lemma testPullOn_apply (hr : r ≠ 0) {U : Opens ℂ} (φ : TestOn U) :
    testPullOn r z hr U φ = zbPull r z hr φ := rfl

/-- `g ↦ g(r · + z)` from `𝒟'(rU + z)` to `𝒟'(U)`:
`⟨g(r·+z), φ⟩ = r⁻² ⟨g, φ((·-z)/r)⟩` -/
def distAffine (r : ℝ) (z : ℂ) (hr : r ≠ 0) {U : Opens ℂ} (g : DistOn (affOpens r z U)) :
    DistOn U :=
  (r ^ 2)⁻¹ • g.comp (testPullOn r z hr U)

lemma distAffine_apply (hr : r ≠ 0) {U : Opens ℂ} (g : DistOn (affOpens r z U)) (φ : TestOn U) :
    distAffine r z hr g φ = (r ^ 2)⁻¹ * g (zbPull r z hr φ) := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Affine invariance** of the zero-boundary GFF: `h̊^{rU+z}(r·+z) ~ h̊^U`. -/
theorem IsZeroBoundaryGFF.affine (hr : r ≠ 0) {U : Opens ℂ} {g : Ω → DistOn (affOpens r z U)}
    (hg : IsZeroBoundaryGFF (affOpens r z U) g P) :
    IsZeroBoundaryGFF U (fun ω => distAffine r z hr (g ω)) P :=
  ⟨measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply (zbPull r z hr φ)).comp hg.measurable).const_mul _,
    hg.process.affine hr⟩

end LQGMetric
