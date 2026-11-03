/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovZB at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGauss
import LatticeProb.Bonanno.LQGMetric.Field.Green
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The zero-boundary part of a whole-plane GFF on an open set `U` (task P2-MARKOV, part 2)

Let `h` be a whole-plane GFF (`IsWholePlaneGFF`; only mean-zero pairings are used) and `U ⊆ ℂ`
open. For `f ∈ C_c^∞(U)` the Dirichlet pairing `(h, f)_∇ = ⟨h, −Δf/(2π)⟩` (`cmTest f`) satisfies
`E[(h, f)_∇²] = (f, f)_∇` (`logCov_cmTest_cmTest`), so `∇f ↦ (h, f)_∇` extends to a linear
isometry

  `cmIso hh U : H₀¹(U) = gradClosure U (zeroSpace U) →ₗᵢ L²(P)`

(mathlib `LinearMap.extendOfIsometry`). Composing with the Riesz vector `zbRiesz U φ` of
`f ↦ ∫ f φ` gives, for `φ ∈ 𝓓(U)`, the projection of `h` onto `H₀¹(U)`:

* `zbVec hh U φ := cmIso hh U (zbRiesz U φ)`, with `E[zbVec φ · zbVec ψ] = zeroGFFTestCov U φ ψ`;
* `isZBGFFProcess_zbProc` : a measurable version `zbProc` is a zero-boundary GFF process on `U`
  (`IsZBGFFProcess`), jointly Gaussian with the mean-zero pairings of `h`;
* `inner_cmIso_pair_eq_zero` : `cmIso` is orthogonal to `⟨h, ψ⟩` for every mean-zero `ψ`
  vanishing on `U`; `inner_cmIso_gradLin` : `E[(h, f)_∇ ⟨h, ψ⟩] = ∫ f ψ`.

This is the first half of the orthogonal decomposition `H = H₀(U) ⊕ Harm(U)` of the
Cameron–Martin space in Miller–Sheffield IG4 (arXiv:1302.4738, Prop. 2.8, tex l. 1111–1127,
"`h = h₁ + h₂` with `h₁` the projection onto `H(W)`"), Sheffield math/0312099 Thm 2.17 (§2.6), and
Berestycki–Powell arXiv:2404.16642 Thm 1.52 (proof: the projection onto `H₀¹(U)` is a Dirichlet
GFF on `U`). The Dirichlet normalization `(f, g)_∇ = (2π)⁻¹ ∫ ∇f·∇g` is GM's (l. 296).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Laplacian TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovZB

open QuantumZipper QuantumZipper.K3 MarkovGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `f ∈ C_c^∞(U)` as a test function on `ℂ` -/
def zsTest {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) : TestC where
  toFun := f
  contDiff' := hf.1
  hasCompactSupport' := hf.2.1
  tsupport_subset' := subset_univ _

@[simp] lemma zsTest_apply {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) (z : ℂ) :
    zsTest hf z = f z := rfl

/-- `C_c^∞(U)` as a submodule of `ℂ → ℝ` -/
def zsSub (U : Set ℂ) : Submodule ℝ (ℂ → ℝ) where
  carrier := zeroSpace U
  add_mem' {f g} hf hg := (isDNSpace_zeroSpace U).add_mem f hf g hg
  zero_mem' := (isDNSpace_zeroSpace U).zero_mem
  smul_mem' a f hf := (isDNSpace_zeroSpace U).smul_mem a f hf

lemma memLp_pair (hh : IsWholePlaneGFF h P) (ψ : TestC0) : MemLp (pairProc h ψ) 2 P :=
  ((gaussian_pairProc hh).hasGaussianLaw_eval ψ).memLp_two

lemma inner_toLp_eq_cov {F G : Ω → ℝ} (hF : MemLp F 2 P) (hG : MemLp G 2 P) (hF0 : P[F] = 0) :
    ⟪hF.toLp F, hG.toLp G⟫ = cov[F, G; P] := by
  rw [covariance_eq_sub hF hG, hF0, zero_mul, sub_zero, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with ω h1 h2
  rw [h1, h2, Pi.mul_apply, real_inner_eq_re_inner, RCLike.re_to_real]
  simp [mul_comm]

lemma cmTest_add {U : Set ℂ} {f g : ℂ → ℝ} (hf : f ∈ zeroSpace U) (hg : g ∈ zeroSpace U)
    (hfg : f + g ∈ zeroSpace U) :
    cmTest (zsTest hfg) = cmTest (zsTest hf) + cmTest (zsTest hg) := by
  ext z
  have h1 : ContDiffAt ℝ 2 f z := (hf.1.of_le (by simp)).contDiffAt
  have h2 : ContDiffAt ℝ 2 g z := (hg.1.of_le (by simp)).contDiffAt
  change -(2 * Real.pi)⁻¹ * Δ (f + g) z =
    -(2 * Real.pi)⁻¹ * Δ f z + -(2 * Real.pi)⁻¹ * Δ g z
  rw [h1.laplacian_add h2]
  ring

lemma cmTest_smul {U : Set ℂ} (a : ℝ) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U)
    (haf : a • f ∈ zeroSpace U) : cmTest (zsTest haf) = a • cmTest (zsTest hf) := by
  ext z
  have h1 : ContDiffAt ℝ 2 f z := (hf.1.of_le (by simp)).contDiffAt
  change -(2 * Real.pi)⁻¹ * Δ (a • f) z = a * (-(2 * Real.pi)⁻¹ * Δ f z)
  rw [InnerProductSpace.laplacian_smul a h1, smul_eq_mul]
  ring

variable (hh : IsWholePlaneGFF h P) (U : Opens ℂ)

/-- the Dirichlet pairing `f ↦ [(h, f)_∇] ∈ L²(P)`, linear on `C_c^∞(U)` -/
def cmLin : zsSub U →ₗ[ℝ] Lp ℝ 2 P where
  toFun f := (memLp_pair hh (cmTest0 (zsTest f.2))).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
    simp only [pairProc, cmTest0, Pi.add_apply]
    rw [show cmTest (zsTest (f + g).2) = cmTest (zsTest f.2) + cmTest (zsTest g.2) from
      cmTest_add f.2 g.2 (f + g).2, map_add]
  map_smul' a f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
    simp only [pairProc, cmTest0, Pi.smul_apply, smul_eq_mul]
    rw [show cmTest (zsTest (a • f).2) = a • cmTest (zsTest f.2) from
      cmTest_smul a f.2 (a • f).2, map_smul, smul_eq_mul]

/-- `f ↦ ∇f ∈ H₀¹(U)` -/
def gradLin : zsSub U →ₗ[ℝ] gradClosure U (zeroSpace U) where
  toFun f := ⟨gradFeat U f, gradFeat_mem_gradClosure f.2⟩
  map_add' f g := Subtype.ext (gradFeat_add (isDNSpace_zeroSpace _) f.2 g.2)
  map_smul' a f := Subtype.ext (gradFeat_smul (isDNSpace_zeroSpace _) a f.2)

lemma gradEnergy_eq_dirichletEnergyOn {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    gradEnergy f = dirichletEnergyOn U f := by
  unfold gradEnergy dirichletEnergyOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ fun h' => hx (hf.2.2 h'), norm_zero,
      zero_pow two_ne_zero]]

lemma norm_cmLin (f : zsSub U) : ‖cmLin hh U f‖ = ‖gradLin U f‖ := by
  have hnn : 0 ≤ ‖cmLin hh U f‖ := norm_nonneg _
  have hnn' : 0 ≤ ‖gradLin U f‖ := norm_nonneg _
  refine (sq_eq_sq₀ hnn hnn').1 ?_
  have h2 : ‖gradLin U f‖ ^ 2 = dirichletEnergyOn U f :=
    norm_gradFeat_sq ((isDNSpace_zeroSpace _).smooth f f.2)
      ((isDNSpace_zeroSpace _).energy f f.2)
  rw [h2, ← gradEnergy_eq_dirichletEnergyOn U f.2, ← real_inner_self_eq_norm_sq]
  simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
  exact (hh.covariance_eq _ _).trans (logCov_cmTest_cmTest _)

lemma denseRange_gradLin : DenseRange (gradLin U) := by
  intro v
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, mem_preimage]
  have hsub : gradFeat U '' zeroSpace U ⊆ Subtype.val '' range (gradLin U) := by
    rintro _ ⟨f, hf, rfl⟩; exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
  have hv := v.2
  unfold gradClosure at hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  exact closure_mono (fun w hw => hsub (mem_image_of_mem_span (isDNSpace_zeroSpace _) hw)) hv

/-- **The Cameron–Martin isometry** `H₀¹(U) → L²(P)`, `∇f ↦ (h, f)_∇`. -/
def cmIso : gradClosure U (zeroSpace U) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  (cmLin hh U).extendOfIsometry (denseRange_gradLin U) (norm_cmLin hh U)

@[simp] lemma cmIso_gradLin (f : zsSub U) : cmIso hh U (gradLin U f) = cmLin hh U f :=
  LinearMap.extendOfIsometry_eq _ _ _ f

/-- `cmIso` lands in the Gaussian space of the mean-zero pairings -/
theorem cmIso_mem_gaussSpace (v : gradClosure U (zeroSpace U)) :
    cmIso hh U v ∈ gaussSpace (pairProc h) (memLp_pair hh) := by
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (cmIso hh U).continuous
  · rw [cmIso_gradLin]
    exact toLp_mem_gaussSpace (memLp_pair hh) _

/-- `E[(h, f)_∇ ⟨h, ψ⟩] = ∫ f ψ` -/
theorem inner_cmIso_gradLin (f : zsSub U) (ψ : TestC0) :
    ⟪cmIso hh U (gradLin U f), (memLp_pair hh ψ).toLp _⟫ = ∫ x, ψ.1 x * f.1 x := by
  rw [cmIso_gradLin]
  simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_toLp_eq_cov _ _ (centered_pairProc hh _), covariance_comm]
  exact (hh.covariance_eq _ _).trans (logCov_cmTest_right _ _)

variable {U}

/-- the projection of `h` onto `H₀¹(U)`, tested against `φ ∈ 𝓓(U)` -/
def zbVec (φ : TestOn U) : Lp ℝ 2 P := cmIso hh U ⟨zbRiesz U φ, zbRiesz_mem φ⟩

theorem inner_zbVec (hadm : ZBAdmissible U) (φ ψ : TestOn U) :
    ⟪zbVec hh φ, zbVec hh ψ⟫ = zeroGFFTestCov U φ ψ := by
  rw [zbVec, zbVec, LinearIsometry.inner_map_map, Submodule.coe_inner,
    zeroGFFTestCov_eq_inner hadm]

/-- a measurable version of `zbVec` -/
def zbProc (φ : TestOn U) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (zbVec hh φ)).aemeasurable.mk _

lemma zbProc_ae (φ : TestOn U) : zbProc hh φ =ᵐ[P] zbVec hh φ :=
  ((Lp.aestronglyMeasurable (zbVec hh φ)).aemeasurable.ae_eq_mk).symm

/-- **The projection onto `H₀¹(U)` is a zero-boundary GFF on `U`** (BP Thm 1.52, IG4 P2.8). -/
theorem isZBGFFProcess_zbProc (hadm : ZBAdmissible U) :
    IsZBGFFProcess U (fun φ => zbProc hh φ) P := by
  have hG := isGaussianProcess_of_mem_gaussSpace (gaussian_pairProc hh)
    (centered_pairProc hh) (memLp_pair hh) (fun φ : TestOn U => zbVec hh φ)
    fun φ => cmIso_mem_gaussSpace hh U _
  have hc : ∀ φ : TestOn U, P[(zbVec hh φ : Ω → ℝ)] = 0 := fun φ =>
    (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh)
      (centered_pairProc hh) (memLp_pair hh) (cmIso_mem_gaussSpace hh U _)).2
  refine ⟨fun φ => (Lp.aestronglyMeasurable _).aemeasurable.measurable_mk,
    hG.congr fun φ => (zbProc_ae hh φ).symm, fun φ => ?_, fun φ ψ => ?_⟩
  · rw [integral_congr_ae (zbProc_ae hh φ), hc]
  · have hm : MemLp (zbProc hh ψ) 2 P := (Lp.memLp (zbVec hh ψ)).ae_eq (zbProc_ae hh ψ).symm
    have hcov : cov[zbProc hh φ, zbProc hh ψ; P] =
        cov[(zbVec hh φ : Ω → ℝ), zbProc hh ψ; P] := by
      unfold covariance
      refine integral_congr_ae ?_
      filter_upwards [zbProc_ae hh φ] with ω h1
      rw [h1, integral_congr_ae (zbProc_ae hh φ)]
    rw [hcov, covariance_eq_inner _ hm (hc φ), ← inner_zbVec hh hadm]
    congr 1
    rw [MemLp.toLp_congr hm (Lp.memLp _) (zbProc_ae hh ψ), Lp.toLp_coeFn]

end MarkovZB
end LQGMetric
