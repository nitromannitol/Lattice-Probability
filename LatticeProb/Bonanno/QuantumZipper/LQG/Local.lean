/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.LQG.Local at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Surfaces

/-!
# Local LQG measures for fields constrained only on a subdomain

`STATEMENT_SPEC.md` A17, `blueprint/M4_BLUEPRINT.md` §D3. For fields constrained only on a
subdomain (Proposition 1.6's mixed GFF on a bounded domain `D`), the raw values of the sample on
measures far from `D` are arbitrary, so the global vague limits defining `qBoundaryMeasure` /
`qAreaMeasure` may fail to exist and those measures may be junk. The local variants here take
the vague limit of the same approximating measures `bdryApprox` / `areaApprox`, but test only
against continuous functions with compact support inside a given open set (`I ⊆ ℝ`,
resp. `U ⊆ ℂ`), so they only read the sample near that set.

These are *additions*: the global definitions of `LQG/Measures.lean` and `LQG/Surfaces.lean`
are unchanged. For globally good samples the local measures are the restrictions of the global
ones (blueprint M4-R5(d)).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace QuantumZipper

/-- Vague convergence on the open set `I ⊆ ℝ`, for fields constrained only on a subdomain
(A17): the limit `ν` is concentrated on `I`, finite on compact subsets of `I`, and the integrals
of every continuous test function with compact support inside `I` converge. This is the
real-line analogue of `IsVagueLimitOn`. -/
def IsVagueLimitOnR (I : Set ℝ) (νs : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  ν Iᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ I → ν K < ⊤) ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ I →
      Tendsto (fun k => ∫ t, f t ∂(νs k)) atTop (𝓝 (∫ t, f t ∂ν))

open Classical in
/-- The quantum boundary length measure of `x` on the open set `I ⊆ ℝ`, for fields constrained
only on a subdomain (A17): a chosen vague limit of `bdryApprox γ x` on `I` (tested only against
continuous functions with compact support in `I`), or the junk measure `0` if none exists. -/
def qBoundaryMeasureOn (γ : ℝ) (x : FieldSample) (I : Set ℝ) : Measure ℝ :=
  if h : ∃ ν, IsVagueLimitOnR I (bdryApprox γ x) ν then h.choose else 0

open Classical in
/-- The quantum area measure of `x` on the open set `U ⊆ ℂ`, for fields constrained only on a
subdomain (A17): a chosen vague limit of `areaApprox γ x` on `U` (tested only against continuous
functions with compact support in `U`), or the junk measure `0` if none exists. -/
def qAreaMeasureOn (γ : ℝ) (x : FieldSample) (U : Set ℂ) : Measure ℂ :=
  if h : ∃ μ, IsVagueLimitOn U (areaApprox γ x) μ then h.choose else 0

/-- Local analogue of `scaleParam`, for fields constrained only on a subdomain (A17): the
smallest radius `a` at which the local quantum area measure on `U` gives `B_a(0) ∩ ℍ` mass at
least `1`. -/
def scaleParamOn (γ : ℝ) (x : FieldSample) (U : Set ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ x U (Metric.ball 0 a ∩ H)}

/-- Local analogue of `canonical`, for fields constrained only on a subdomain (A17): rescale by
(1.8) with `scaleParamOn γ x U`, so that `B₁(0)` carries unit local quantum area. The rescaled
field lives on `canonicalDomainOn γ x U`. -/
def canonicalOn (γ : ℝ) (x : FieldSample) (U : Set ℂ) : FieldSample :=
  rescale x (Qc γ) (scaleParamOn γ x U)

/-- The domain of `canonicalOn γ x U`: `rescale x Q a` is `x(a ·) + Q log a`, so a field living
on `U` becomes a field living on `a⁻¹ U = {z | a z ∈ U}`. -/
def canonicalDomainOn (γ : ℝ) (x : FieldSample) (U : Set ℂ) : Set ℂ :=
  (fun z => (scaleParamOn γ x U : ℂ) * z) ⁻¹' U

/-- Local analogue of `AreaConvergesInLaw`, for fields constrained only on a subdomain (A17):
the area measure of `Y c ω` is the local measure `qAreaMeasureOn γ (Y c ω) (U c ω)` on the
(possibly random, `c`-dependent) open set `U c ω` where `Y c ω` lives, while the limit object
`Y'` (a field on all of `ℍ`) uses the global `qAreaMeasure`. Convergence is in the sense of
finite-dimensional distributions against continuous compactly supported test functions
(Kallenberg), exactly as in `AreaConvergesInLaw`. -/
def AreaConvergesInLawOn (γ : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Y : ℝ → Ω → FieldSample) (U : ℝ → Ω → Set ℂ) (P' : Measure Ω')
    (Y' : Ω' → FieldSample) : Prop :=
  ∀ (m : ℕ) (f : Fin m → ℂ → ℝ), (∀ j, Continuous (f j)) → (∀ j, HasCompactSupport (f j)) →
    ∀ F : (Fin m → ℝ) → ℝ, Continuous F → (∃ C, ∀ v, |F v| ≤ C) →
      Tendsto (fun c : ℝ => ∫ ω, F (fun j => ∫ z, f j z ∂(qAreaMeasureOn γ (Y c ω) (U c ω))) ∂P)
        atTop (𝓝 (∫ ω, F (fun j => ∫ z, f j z ∂(qAreaMeasure γ (Y' ω))) ∂P'))

end QuantumZipper
