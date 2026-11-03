/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundary at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-boundary GFF on an open set `U ⊆ ℂ` (task P2-ZB, WP-14, decision D-ZB1)

A zero-boundary GFF `h̊^U` on an open set `U` is described, like `IsWholePlaneGFF`, by the law of
its pairings with test functions `φ ∈ 𝓓(U)`: they form a centred Gaussian process whose covariance
is the dual Dirichlet form
`⟨φ, ψ⟩_{H⁻¹(U)} = QuantumZipper.zeroGFFTestCov U φ ψ`
(QZ's `dualCov U (zeroSpace U)` of `sup_{f ∈ C_c^∞(U)} (∫ f ρ)² / (f,f)_∇`, expanded bilinearly on
`φ = φ⁺ − φ⁻`; normalization `(f,g)_∇ = (2π)⁻¹ ∫ ∇f·∇g`, so the kernel is the Green function
`G_U(x,y) = −log|x−y| + harmonic`). This is Sheffield's definition (*Gaussian free fields for
mathematicians*, math/0312099, §2: the GFF on `U` is the standard Gaussian of `H₀¹(U)`, so
`Var⟨h, ρ⟩ = ‖ρ‖²_{H⁻¹(U)}`), equivalent to Berestycki–Powell arXiv:2404.16642, Ch. 1 (Green
covariance). Deviation ZB-1 (`decisions/DEC-ZB.md`).

* `IsZBGFFProcess U X P` : the process-level law predicate (`X : TestOn U → Ω → ℝ`);
* `IsZeroBoundaryGFF U g P` : a `𝒟'(U)`-valued field whose pairings satisfy it;
* `isZBGFFProcess_of_isZeroBoundaryGFFOn` : **bridge** — for a QZ zero-boundary GFF
  `X : Ω → Measure ℂ → ℝ` (`QuantumZipper.IsZeroBoundaryGFFOn U X P`), the pairings
  `φ ↦ X(φ⁺dz) − X(φ⁻dz)` form a zero-boundary GFF process in our sense (pure algebra: same
  covariance object, mathlib `IsGaussianProcess.of_isGaussianProcess`);
* `zbAdmissible_of_subset_H` : for `U ⊆ ℍ` every `φ^± dz` is admissible for QZ (finite dual norm,
  via QZ `K3.isAdmissibleH_testMeasPos_of`, `K3.isAdmissibleDual_H_of_isAdmissibleH`,
  `K3.dualNormSq_zeroSpace_mono`);
* `exists_isZBGFFProcess` : existence (QZ's Gaussian-series construction `K3.exists_zeroGFFOn`,
  transported through the bridge); `exists_isZBGFFProcess_openSquare` for the square of §8.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric

open QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The zero-boundary GFF on the open set `U`, as a law statement on a process indexed by
`𝓓(U)`: measurable, centred Gaussian, with covariance the dual Dirichlet form
`zeroGFFTestCov U φ ψ = ⟨φ, ψ⟩_{H⁻¹(U)}` (D-ZB1). -/
structure IsZBGFFProcess (U : Opens ℂ) (X : TestOn U → Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : ∀ φ, Measurable (X φ)
  gaussian : IsGaussianProcess X P
  centered : ∀ φ, ∫ ω, X φ ω ∂P = 0
  covariance_eq : ∀ φ ψ, cov[X φ, X ψ; P] = zeroGFFTestCov U φ ψ

/-- `g : Ω → 𝒟'(U)` is a zero-boundary GFF on `U`: measurable, and its pairings with `𝓓(U)`
satisfy `IsZBGFFProcess`. -/
structure IsZeroBoundaryGFF (U : Opens ℂ) (g : Ω → DistOn U) (P : Measure Ω) : Prop where
  measurable : Measurable g
  process : IsZBGFFProcess U (fun φ ω => g ω φ) P

/-- Every `φ ∈ 𝓓(U)` has `φ⁺dz` and `φ⁻dz` in QZ's admissible class for `U` (finite
`H⁻¹(U)`-norm). True whenever `ℂ ∖ U` is non-polar; proved here for `U ⊆ ℍ`. -/
def ZBAdmissible (U : Opens ℂ) : Prop :=
  ∀ φ : TestOn U, IsAdmissibleDual U (zeroSpace U) (testMeasPos φ) ∧
    IsAdmissibleDual U (zeroSpace U) (testMeasNeg φ)

section Bridge

variable {P : Measure Ω}

end Bridge

section Admissible

lemma testMeasPos_compl_tsupport (φ : ℂ → ℝ) : testMeasPos φ (tsupport φ)ᶜ = 0 :=
  K3.withDensity_compl_null (isClosed_tsupport φ).measurableSet
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])

lemma testMeasNeg_compl_tsupport (φ : ℂ → ℝ) : testMeasNeg φ (tsupport φ)ᶜ = 0 :=
  K3.withDensity_compl_null (isClosed_tsupport φ).measurableSet
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])

/-- For `U ⊆ ℍ`, every `φ^± dz`, `φ ∈ 𝓓(U)`, is admissible for the dual norm on `U`. -/
theorem zbAdmissible_of_subset_H {U : Opens ℂ} (hU : (U : Set ℂ) ⊆ H) : ZBAdmissible U := by
  intro φ
  have hsH : tsupport φ ⊆ Hbar := φ.tsupport_subset.trans (hU.trans K3.H_subset_Hbar_K3)
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  have hKU : tsupport φ ⊆ closure (U : Set ℂ) := φ.tsupport_subset.trans subset_closure
  have hp := K3.isAdmissibleH_testMeasPos_of φ.continuous φ.hasCompactSupport hsH
  have hn := K3.isAdmissibleH_testMeasNeg_of φ.continuous φ.hasCompactSupport hsH
  exact ⟨⟨hp.1, ⟨_, hK, hKU, testMeasPos_compl_tsupport φ⟩,
      (K3.dualNormSq_zeroSpace_mono U.isOpen hU).trans_lt
        (K3.isAdmissibleDual_H_of_isAdmissibleH hp).2.2⟩,
    ⟨hn.1, ⟨_, hK, hKU, testMeasNeg_compl_tsupport φ⟩,
      (K3.dualNormSq_zeroSpace_mono U.isOpen hU).trans_lt
        (K3.isAdmissibleDual_H_of_isAdmissibleH hn).2.2⟩⟩

lemma isOpen_openSquare : IsOpen openSquare := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {z : ℂ | z.im < 1} := isOpen_lt Complex.continuous_im continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- the open unit square `(0,1)²` of §8 as an element of `Opens ℂ` -/
def openSquareOpens : Opens ℂ := ⟨openSquare, isOpen_openSquare⟩

lemma openSquare_subset_H : openSquare ⊆ H := fun _ hz => hz.2.2.1

end Admissible

end LQGMetric
