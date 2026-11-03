/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.LQG.Measures at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Liouville quantum gravity measures

`FOUNDATIONS.md` §5. The boundary length measure and area measure of a `γ`-LQG surface are
vague limits of explicit approximating measures built from the regularized field `avgReg`
(Sheffield §1, formulas (1.1)/(1.2)). Since vague convergence is not otherwise present in
mathlib, `IsVagueLimitR`/`IsVagueLimitOn` spell it out directly as convergence of integrals
against continuous, compactly supported test functions, and `qBoundaryMeasure`/`qAreaMeasure`
pick out a limit by `Classical.choice` when one exists (junk `0` otherwise, Principle 4 of
`FOUNDATIONS.md` §0).
-/

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported Topology

namespace QuantumZipper

/-- Paper (1.2): the approximating boundary measure at scale `ε = 2^{-k}`,
`ε^{γ²/4} e^{γ h_ε(x)/2} dx` on `ℝ`, where `h_ε(x) = avgReg x k x` is the regularized
semicircle average. -/
def bdryApprox (γ : ℝ) (x : FieldSample) (k : ℕ) : Measure ℝ :=
  volume.withDensity fun t : ℝ =>
    ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k (t : ℂ)))

/-- Paper (1.1): the approximating area measure at scale `ε = 2^{-k}`,
`ε^{γ²/2} e^{γ h_ε(z)} dz` restricted to the open upper half-plane `ℍ`. -/
def areaApprox (γ : ℝ) (x : FieldSample) (k : ℕ) : Measure ℂ :=
  (volume.restrict H).withDensity fun z : ℂ =>
    ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k z))

/-- Vague convergence of a sequence of measures on `ℝ` to a locally finite limit: convergence of
integrals against every continuous, compactly supported test function. -/
def IsVagueLimitR (νs : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  IsLocallyFiniteMeasure ν ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ t, f t ∂(νs k)) atTop (𝓝 (∫ t, f t ∂ν))

/-- Vague convergence of a sequence of measures on `ℂ` to a limit concentrated on the open set
`U`, finite on compact subsets of `U`: convergence of integrals against every continuous,
compactly supported test function whose support lies in `U`. -/
def IsVagueLimitOn (U : Set ℂ) (μs : ℕ → Measure ℂ) (μ : Measure ℂ) : Prop :=
  μ Uᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 (∫ z, f z ∂μ))

open Classical in
/-- The quantum boundary length measure of `x` (Duplantier–Sheffield): a chosen vague limit of
`bdryApprox γ x`, or the junk measure `0` if none exists. -/
def qBoundaryMeasure (γ : ℝ) (x : FieldSample) : Measure ℝ :=
  if h : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν then h.choose else 0

open Classical in
/-- The quantum area measure of `x` on `ℍ`: a chosen vague limit of `areaApprox γ x`, or the
junk measure `0` if none exists. -/
def qAreaMeasure (γ : ℝ) (x : FieldSample) : Measure ℂ :=
  if h : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ then h.choose else 0

/-! ## Measurability -/

theorem measurable_bdryApprox (γ : ℝ) (k : ℕ) :
    Measurable (fun x : FieldSample => bdryApprox γ x k) := by
  unfold bdryApprox
  apply MeasureTheory.measurable_withDensity
  have h1 : Measurable (fun p : FieldSample × ℝ => avgReg p.1 k ((p.2 : ℝ) : ℂ)) :=
    (measurable_avgReg k).comp
      (measurable_fst.prodMk (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have h2 : Measurable (fun p : FieldSample × ℝ =>
      radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg p.1 k ((p.2 : ℝ) : ℂ))) :=
    (Real.measurable_exp.comp (h1.const_mul (γ / 2))).const_mul (radius k ^ (γ ^ 2 / 4))
  exact ENNReal.measurable_ofReal.comp h2

theorem measurable_areaApprox (γ : ℝ) (k : ℕ) :
    Measurable (fun x : FieldSample => areaApprox γ x k) := by
  unfold areaApprox
  apply MeasureTheory.measurable_withDensity
  have h2 : Measurable (fun p : FieldSample × ℂ =>
      radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg p.1 k p.2)) :=
    (Real.measurable_exp.comp ((measurable_avgReg k).const_mul γ)).const_mul (radius k ^ (γ ^ 2 / 2))
  exact ENNReal.measurable_ofReal.comp h2

/-! ## Uniqueness of vague limits on `ℝ` -/

/-- Two vague limits of the same sequence of measures on `ℝ` agree: a locally finite measure on
`ℝ` is determined by its integrals against continuous, compactly supported test functions
(`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`, since every locally finite
Borel measure on the `σ`-compact metrizable space `ℝ` is automatically regular). -/
theorem isVagueLimitR_unique {νs : ℕ → Measure ℝ} {ν ν' : Measure ℝ}
    (h : IsVagueLimitR νs ν) (h' : IsVagueLimitR νs ν') : ν = ν' := by
  obtain ⟨hloc, htend⟩ := h
  obtain ⟨hloc', htend'⟩ := h'
  have := hloc
  have := hloc'
  refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  exact tendsto_nhds_unique (htend f (map_continuous f) f.hasCompactSupport)
    (htend' f (map_continuous f) f.hasCompactSupport)

/-- `qBoundaryMeasure` is any vague limit of `bdryApprox`, when one exists: it is defined by
choice among vague limits, and they are all equal by `isVagueLimitR_unique`. -/
theorem qBoundaryMeasure_eq {γ : ℝ} {x : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ x) ν) : qBoundaryMeasure γ x = ν := by
  have hex : ∃ ν', IsVagueLimitR (bdryApprox γ x) ν' := ⟨ν, hν⟩
  unfold qBoundaryMeasure
  rw [dif_pos hex]
  exact isVagueLimitR_unique hex.choose_spec hν

end QuantumZipper
