/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepTight at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Integration

/-!
# GM Lemma 2.7: a configuration-free second-moment bound for the harmonic part

GM (`literature/src/1905.00383/uniqueness-final.tex`) l. 985–988 need `P[𝔐_z ≤ A] ≥ 1 − (1−q)/4`
for every `z ∈ 𝒵` with `A = A(s,q)` independent of the configuration `𝒵`; GM obtain it from
"the law of `𝔐_z` does not depend on `z`" (translation invariance). That route needs the a.s.
uniqueness of the harmonic part on a component and a transfer of the decomposition between
probability spaces, which we lack. **Own argument** (cost rule; proposed DEVIATIONS entry): the
harmonic part is an `L²`-contraction of the field. If `h = G + h̊` a.s. with `G` measurable
w.r.t. `𝓕` and `σ(h̊) ⟂ 𝓕`, then for every mean-zero test function `φ` supported in the Markov
domain `V`,
`E[G(φ)²] ≤ E[h(φ)²] = ∫∫ φ(x)(−log|x−y|)φ(y) dx dy`,
a bound that depends only on `φ` (and is translation invariant), not on the configuration.

* `integral_sq_harmonicPart_le` — the bound above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace

namespace LQGMetric.GM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`E[G(φ)²] ≤ logCov(φ,φ)`** for the part `G` of a decomposition `h = G + h̊` of a
whole-plane GFF with `σ(h̊) ⟂ σ(G)` (e.g. `G` measurable w.r.t. `𝓕 ⟂ σ(h̊)`) and `h̊|_V` a zero-boundary GFF, `φ` mean-zero
and supported in `V` (own argument replacing GM l. 985–986, see the module docstring). -/
theorem integral_sq_harmonicPart_le [IsProbabilityMeasure P] {h hz G : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hzb : IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P)
    (hind : Indep (MeasurableSpace.comap hz inferInstance) (MeasurableSpace.comap G inferInstance) P)
    (hdec : ∀ᵐ ω ∂P, h ω = G ω + hz ω)
    (φ : TestC0) (φV : TestOn V)
    (hφ : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φV) = φ.1) :
    ∫ ω, (G ω φ.1) ^ 2 ∂P ≤ logCov φ.1 φ.1 := by
  set X : Ω → ℝ := fun ω => h ω φ.1
  set Z : Ω → ℝ := fun ω => hz ω φ.1
  set Y : Ω → ℝ := fun ω => G ω φ.1
  have hZeq : Z = fun ω => restrictTo V (hz ω) φV := by
    funext ω; simp only [Z, ← hφ]; rfl
  have hXL : MemLp X 2 P := (hh.gaussian.hasGaussianLaw_eval φ).memLp_two
  have hZL : MemLp Z 2 P := by
    rw [hZeq]; exact (hzb.process.gaussian.hasGaussianLaw_eval φV).memLp_two
  have hZ0 : ∫ ω, Z ω ∂P = 0 := by rw [hZeq]; exact hzb.process.centered φV
  have hYeq : Y =ᵐ[P] X - Z := by
    filter_upwards [hdec] with ω hω
    simp only [X, Y, Z, Pi.sub_apply, hω]
    show G ω φ.1 = (G ω + hz ω) φ.1 - hz ω φ.1
    rw [add_apply]; ring
  have hYL : MemLp Y 2 P := (hXL.sub hZL).ae_eq hYeq.symm
  have hindYZ : IndepFun Y Z P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm ?_) ?_
    · show MeasurableSpace.comap ((fun T : DistC => T φ.1) ∘ G) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_distOn_apply φ.1).comap_le
    · show MeasurableSpace.comap ((fun T : DistC => T φ.1) ∘ hz) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_distOn_apply φ.1).comap_le
  have hYZ : ∫ ω, Y ω * Z ω ∂P = 0 := by
    have := hindYZ.integral_mul_eq_mul_integral hYL.aestronglyMeasurable
      hZL.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hZ0, mul_zero]
  have hXsq : ∫ ω, X ω ^ 2 ∂P = logCov φ.1 φ.1 := by
    rw [← hh.covariance_eq φ φ, covariance_self hXL.aemeasurable,
      variance_of_integral_eq_zero hXL.aemeasurable (hh.centered φ)]
  have hXae : (fun ω => X ω ^ 2) =ᵐ[P] fun ω => Y ω ^ 2 + 2 * (Y ω * Z ω) + Z ω ^ 2 := by
    filter_upwards [hYeq] with ω hω
    simp only [Pi.sub_apply] at hω
    rw [hω]; ring
  have i1 : Integrable (fun ω => Y ω ^ 2) P := hYL.integrable_sq
  have i2 : Integrable (fun ω => 2 * (Y ω * Z ω)) P := (hYL.integrable_mul hZL).const_mul 2
  have i3 : Integrable (fun ω => Z ω ^ 2) P := hZL.integrable_sq
  have hexp : ∫ ω, X ω ^ 2 ∂P = ∫ ω, Y ω ^ 2 ∂P + ∫ ω, Z ω ^ 2 ∂P := by
    rw [integral_congr_ae hXae]
    have e1 : ∫ ω, (Y ω ^ 2 + 2 * (Y ω * Z ω) + Z ω ^ 2) ∂P =
        ∫ ω, (Y ω ^ 2 + 2 * (Y ω * Z ω)) ∂P + ∫ ω, Z ω ^ 2 ∂P := integral_add (i1.add i2) i3
    have e2 : ∫ ω, (Y ω ^ 2 + 2 * (Y ω * Z ω)) ∂P =
        ∫ ω, Y ω ^ 2 ∂P + ∫ ω, 2 * (Y ω * Z ω) ∂P := integral_add i1 i2
    rw [e1, e2, integral_const_mul, hYZ, mul_zero, add_zero]
  have hZsq : 0 ≤ ∫ ω, Z ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  linarith

end LQGMetric.GM
