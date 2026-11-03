/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.GFF.Defs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Gaussian free fields

The paper's Dirichlet normalization is `(f,g)_∇ = (2π)⁻¹∫∇f·∇g`, so `Cov = G` with `−ΔG =
2πδ` (`notes/section3_4.md` §A.1-A.4). Fields are `Measure ℂ → ℝ` (this is `FieldSample`,
defined in `QuantumZipper.Field.Sample`, not imported here): `X ω μ` is meant to be `⟨h(ω),
μ⟩` for the sample `h(ω)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The zero-boundary GFF on `ℍ`, as a law hypothesis on raw coordinates: every coordinate
is measurable, the process indexed by admissible measures is a centered Gaussian process, and
its covariance is given by the zero-boundary kernel `greenH` (Sheffield §3.1.3, §3.2). -/
structure IsZeroBoundaryGFFH (X : Ω → Measure ℂ → ℝ) (P : Measure Ω) : Prop where
  measurable_coord : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ
  gaussian : IsGaussianProcess (fun (μ : {μ // IsAdmissibleH μ}) (ω : Ω) => X ω μ.1) P
  centered : ∀ μ : Measure ℂ, IsAdmissibleH μ → ∫ ω, X ω μ ∂P = 0
  covariance_eq : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH ν →
      cov[fun ω => X ω μ, fun ω => X ω ν; P] = kernelCov greenH μ ν

/-- The free-boundary GFF on `ℍ`, modulo additive constants: the process of *differences*
`X · μ − X · ν` over balanced admissible pairs (`μ Set.univ = ν Set.univ`) is a centered
Gaussian process with covariance given by the free-boundary kernel `neumannH`, bilinearly
expanded on the signed measures `μ − ν`; and `X` is (a.s.) **linear** on admissible measures.

Any additive-constant convention (even a random one, `X = h + C · mass`) satisfies this
definition. Linearity is part of being a random distribution; without it the balanced-pair
conditions would also admit non-linear "gauges" `X μ = h μ + F μ` with `F` depending only on
the mass, for which regularized pairings with single (unbalanced) measures need not
converge. -/
structure IsFreeGFFModConstH (X : Ω → Measure ℂ → ℝ) (P : Measure Ω) : Prop where
  measurable_coord : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ
  gaussian : IsGaussianProcess
      (fun (p : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ})
        (ω : Ω) => X ω p.1.1 - X ω p.1.2) P
  centered : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH ν → μ Set.univ = ν Set.univ →
      ∫ ω, (X ω μ - X ω ν) ∂P = 0
  covariance_eq : ∀ p q : Measure ℂ × Measure ℂ,
      IsAdmissibleH p.1 → IsAdmissibleH p.2 → p.1 Set.univ = p.2 Set.univ →
      IsAdmissibleH q.1 → IsAdmissibleH q.2 → q.1 Set.univ = q.2 Set.univ →
      cov[fun ω => X ω p.1 - X ω p.2, fun ω => X ω q.1 - X ω q.2; P] = kernelCov2 neumannH p q
  linear : ∀ μ ν : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH ν → ∀ a b : NNReal,
      (fun ω => X ω (a • μ + b • ν)) =ᵐ[P] fun ω => (a : ℝ) * X ω μ + (b : ℝ) * X ω ν

/-! ## Dual Dirichlet norm -/

/-- Dirichlet energy of `f` on `D`, in the paper's `(f,f)_∇` normalization. -/
def dirichletEnergyOn (D : Set ℂ) (f : ℂ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2

/-- Squared dual Dirichlet norm of the functional `f ↦ ∫ f dμ` on the test space `V`: this is
`Var⟨h,μ⟩` for `h = Σ αᵢ fᵢ` an orthonormal (in `(·,·)_∇`) expansion over `V`, the paper's
`Σ αᵢ fᵢ` definition of the GFF (Sheffield §1.2, §3). -/
def dualNormSq (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨆ f ∈ {f ∈ V | 0 < dirichletEnergyOn D f},
    ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn D f)

/-- Covariance associated to the dual Dirichlet norm, by polarization. -/
def dualCov (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ ν : Measure ℂ) : ℝ :=
  ((dualNormSq D V (μ + ν)).toReal - (dualNormSq D V μ).toReal - (dualNormSq D V ν).toReal) / 2

/-- Smooth, compactly supported test functions with support in the open set `U`: the test
space for the zero-boundary GFF on `U`. -/
def zeroSpace (U : Set ℂ) : Set (ℂ → ℝ) :=
  {f : ℂ → ℝ | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ U}

/-- Smooth, finite-(Dirichlet-)energy functions on `D` that vanish near `∂D \ S`: the test
space for the mixed (zero on `∂D \ S`, free on `S`) GFF. -/
def mixedSpace (D S : Set ℂ) : Set (ℂ → ℝ) :=
  {f : ℂ → ℝ | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D ∧
    ∃ N : Set ℂ, IsOpen N ∧ frontier D \ S ⊆ N ∧ ∀ z ∈ N, f z = 0}

/-- Admissibility class indexing `IsZeroBoundaryGFFOn`/`IsMixedGFF`: finite measures with
compact support in `closure D` and finite dual `V`-norm. -/
def IsAdmissibleDual (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ (∃ K, IsCompact K ∧ K ⊆ closure D ∧ μ Kᶜ = 0) ∧ dualNormSq D V μ < ⊤

/-- The zero-boundary GFF on a general open set `U` (Theorem 1.1's addendum): same shape as
`IsZeroBoundaryGFFH`, but the covariance is the dual Dirichlet norm on `zeroSpace U`, i.e.
`Var⟨h,μ⟩ = sup_{f ∈ C_c^∞(U)} (∫f dμ)²/(f,f)_∇`, polarized. -/
structure IsZeroBoundaryGFFOn (U : Set ℂ) (X : Ω → Measure ℂ → ℝ) (P : Measure Ω) : Prop where
  measurable_coord : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ
  gaussian : IsGaussianProcess
      (fun (μ : {μ // IsAdmissibleDual U (zeroSpace U) μ}) (ω : Ω) => X ω μ.1) P
  centered : ∀ μ : Measure ℂ, IsAdmissibleDual U (zeroSpace U) μ → ∫ ω, X ω μ ∂P = 0
  covariance_eq : ∀ μ ν : Measure ℂ, IsAdmissibleDual U (zeroSpace U) μ →
      IsAdmissibleDual U (zeroSpace U) ν →
      cov[fun ω => X ω μ, fun ω => X ω ν; P] = dualCov U (zeroSpace U) μ ν

/-- The mixed GFF on `D`, zero on `∂D \ S` and free on `S` (Proposition 1.6): same shape as
`IsZeroBoundaryGFFH`, but the covariance is the dual Dirichlet norm on `mixedSpace D S`, i.e.
`Var⟨h,μ⟩ = sup_{f ∈ mixedSpace D S} (∫f dμ)²/(f,f)_∇`, polarized. -/
structure IsMixedGFF (D S : Set ℂ) (X : Ω → Measure ℂ → ℝ) (P : Measure Ω) : Prop where
  measurable_coord : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ
  gaussian : IsGaussianProcess
      (fun (μ : {μ // IsAdmissibleDual D (mixedSpace D S) μ}) (ω : Ω) => X ω μ.1) P
  centered : ∀ μ : Measure ℂ, IsAdmissibleDual D (mixedSpace D S) μ → ∫ ω, X ω μ ∂P = 0
  covariance_eq : ∀ μ ν : Measure ℂ, IsAdmissibleDual D (mixedSpace D S) μ →
      IsAdmissibleDual D (mixedSpace D S) ν →
      cov[fun ω => X ω μ, fun ω => X ω ν; P] = dualCov D (mixedSpace D S) μ ν

end QuantumZipper
