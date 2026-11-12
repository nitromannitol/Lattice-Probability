/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Measure
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
Deterministic core of DG Lemma 3.3 (3.6) (`lem-measure-scale`, DG:1014–1036) in the D105 form
(decisions/DEC-105.md §1 item 3–4, §3 N6): DG's proof is "the coordinate change formula
[DS Prop 2.1] … (this is also easy to see directly from the circle average … approximations of
the measures)" (DG:1033–1034) together with `dμ_{h+f} = e^{γf} dμ_h`. We follow the second
route: the approximations `D_j(z) dz` of `μ` and `D'_k(y) dy` of `μ'` satisfy
`D'_k(y) = a · D_{k+m}(Ty) · e^{−γ ψ_k(Ty)}` with `ψ_k → φ` locally uniformly, so
`T_*(w · D'_k dy) = e^{γ(φ − ψ_k)} D_{k+m} dz` on `T(U')`, and uniqueness of vague limits
(QuantumZipper `isVagueLimitOn_unique`) gives `μ|_{T(U')} = T_*(δ²/a · e^{γ φ∘T} μ')`.

* `tendsto_integral_mul_of_unif` — vague convergence survives a density factor `e_k → 1`
  uniformly on the support (no finiteness hypothesis on the approximations);
* `map_affineC_volume`, `setIntegral_comp_affineC` — Lebesgue change of variables;
* **`restrict_eq_map_withDensity_of_vague`** — the deterministic identity.

Own elementary glue (the paper says "easy to see directly", DG:1034).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open QuantumZipper

/-- **vague convergence with a density factor `e_k → 1` uniformly on the support** -/
lemma tendsto_integral_mul_of_unif {U : Set ℂ} {A : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hA : IsVagueLimitOn U A μ) {e : ℕ → ℂ → ℝ} (hem : ∀ k, Measurable (e k)) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hunif : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ tsupport f, |e k z - 1| < η) :
    Tendsto (fun k => ∫ z, f z * e k z ∂(A k)) atTop (𝓝 (∫ z, f z ∂μ)) := by
  have hf0 : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hB : Tendsto (fun k => ∫ z, f z ∂(A k)) atTop (𝓝 (∫ z, f z ∂μ)) := hA.2.2 f hf hfc hfU
  have hC : Tendsto (fun k => ∫ z, |f z| ∂(A k)) atTop (𝓝 (∫ z, |f z| ∂μ)) :=
    hA.2.2 _ hf.abs (hfc.comp_left abs_zero) ((tsupport_comp_subset abs_zero f).trans hfU)
  -- the key estimate `|a_k − b_k| ≤ η c_k`
  have key : ∀ η, 0 < η → η ≤ 1 / 2 → ∀ k, (∀ z ∈ tsupport f, |e k z - 1| < η) →
      |∫ z, f z * e k z ∂(A k) - ∫ z, f z ∂(A k)| ≤ η * ∫ z, |f z| ∂(A k) := by
    intro η hη hη2 k hk
    have hpt : ∀ z, |f z * e k z - f z| ≤ η * |f z| := fun z => by
      by_cases hz : z ∈ tsupport f
      · rw [show f z * e k z - f z = f z * (e k z - 1) by ring, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hk z hz).le (abs_nonneg _)
      · simp [hf0 z hz]
    have hmeas : AEStronglyMeasurable (fun z => f z * e k z) (A k) :=
      (hf.measurable.mul (hem k)).aestronglyMeasurable
    by_cases hi : Integrable (fun z => |f z|) (A k)
    · have hfi : Integrable f (A k) :=
        hi.mono' hf.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs])
      have hfe : Integrable (fun z => f z * e k z) (A k) :=
        (hi.const_mul 2).mono' hmeas (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          have := hpt z
          have h1 := abs_sub_abs_le_abs_sub (f z * e k z) (f z)
          have h2 : η * |f z| ≤ |f z| := by nlinarith [abs_nonneg (f z)]
          linarith)
      rw [← integral_sub hfe hfi, ← integral_const_mul]
      exact (norm_integral_le_of_norm_le (hi.const_mul η)
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hpt z))
    · have h1 : ¬ Integrable f (A k) := fun h => hi h.abs
      have h2 : ¬ Integrable (fun z => f z * e k z) (A k) := fun h => by
        refine hi ((h.norm.const_mul 2).mono' hf.abs.aestronglyMeasurable
          (Eventually.of_forall fun z => ?_))
        rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
        have := hpt z
        have h3 := abs_sub_abs_le_abs_sub (f z) (f z * e k z)
        rw [abs_sub_comm] at h3
        nlinarith [abs_nonneg (f z), abs_nonneg (f z * e k z)]
      rw [integral_undef h1, integral_undef h2, integral_undef hi]
      simp
  have hD : Tendsto (fun k => ∫ z, f z * e k z ∂(A k) - ∫ z, f z ∂(A k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set L := ∫ z, |f z| ∂μ + 1 with hL
    have hL1 : 0 < L := by
      have : 0 ≤ ∫ z, |f z| ∂μ := integral_nonneg fun z => abs_nonneg _
      linarith
    set η := min (1 / 2) (ε / (2 * L)) with hηd
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    filter_upwards [hunif η hη, hC.eventually (gt_mem_nhds (show ∫ z, |f z| ∂μ < L by linarith))]
      with k hk hc
    rw [Real.dist_eq, sub_zero]
    have hc0 : 0 ≤ ∫ z, |f z| ∂(A k) := integral_nonneg fun z => abs_nonneg _
    calc _ ≤ η * ∫ z, |f z| ∂(A k) := key η hη (min_le_left _ _) k hk
      _ ≤ (ε / (2 * L)) * L := mul_le_mul (min_le_right _ _) hc.le hc0 (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := hD.add hB
  rw [zero_add] at this
  exact this.congr fun k => by ring

/-- Lebesgue measure under `y ↦ δy + c`: `T_* Leb = δ⁻² Leb` -/
lemma map_affineC_volume {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    Measure.map (affineC δ c) volume = ENNReal.ofReal (δ ^ 2)⁻¹ • (volume : Measure ℂ) := by
  have e : affineC δ c = (fun y : ℂ => y + c) ∘ fun y : ℂ => δ • y := by
    funext y; simp only [affineC, Function.comp, Complex.real_smul]
  rw [e, ← Measure.map_map (measurable_add_const c) (measurable_const_smul δ),
    Measure.map_addHaar_smul volume hδ.ne', Measure.map_smul,
    map_add_right_eq_self, Complex.finrank_real_complex,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (δ ^ 2)⁻¹)]
  exact (measurable_add_const c).aemeasurable

/-- integrals against a real density -/
lemma integral_withDensity_ofReal (ν : Measure ℂ) {D : ℂ → ℝ} (hD : Measurable D)
    (hD0 : ∀ y, 0 ≤ D y) (g : ℂ → ℝ) :
    ∫ y, g y ∂(ν.withDensity fun y => ENNReal.ofReal (D y)) = ∫ y, D y * g y ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hD.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (hD0 y), smul_eq_mul]

end DG
end LQGMetric
