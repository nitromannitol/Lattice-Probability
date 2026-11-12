/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.ZBBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovHarm
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Zero-boundary bridge: a zero-boundary GFF paired with bounded densities (DF-B4, part ii)

DFGPS (arXiv:1905.00380, T:879–880) convolves the zero-boundary GFF `h̊` on `(-1,2)²` with the heat
kernel, `h̊ * p_{ε²/2}`, i.e. pairs it with `p_{ε²/2}(x − ·) 1_U` (zero extension, DDDF DD:160;
`Blueprint.heatBdd`). DDDF's statements (`Blueprint.DDDFThm1_2`, `DDDFProp29`) are about the
process `Xh : BddOn U → Ω → ℝ` (`IsZBGFFProcessExt`), while the Markov property (`LMLem2_1`,
`DFGPS.markov_normAt`) produces a random distribution `g : Ω → 𝒟'(U)` with
`IsZeroBoundaryGFF U g P`. This file builds, on the same probability space, the extension of `g`
to all of `BddOn U` (bounded `U`): the `L²` isometry of the Gaussian Hilbert space of `g` (the
"GFF as a stochastic process" indexed by `H⁻¹(U)`, Berestycki–Powell arXiv:2404.16642 §1.2,
`definitionGFF.tex` l. 648–890: extension by `L²` isometry from a dense set).

Construction (as `MarkovZB.cmIso`): `∇f ↦ [⟨g, −Δf/2π⟩]` for `f ∈ C_c^∞(U)` is an isometry
(`MarkovHarm.zbRiesz_cmTestOn`: the Riesz vector of `−Δf/2π` is `∇f`), extended to `H₀¹(U)` by
density (`MarkovZB.denseRange_gradLin`); `Xh ρ` is a measurable version of the image of the Riesz
vector of `ρ` (`MarkovExt.rieszFun`). It agrees a.s. with `g` on `𝓓(U)` (`zbBdd_toBddOn_ae`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric.DFGPS

open MarkovGauss MarkovZB MarkovHarm MarkovExt QuantumZipper QuantumZipper.K3

/-- the Riesz vector of `ρ_f = −Δf/(2π)` is `∇f` (a deterministic fact; `MarkovHarm` states it
with a whole-plane GFF in context, supplied here by `GFFExist.exists_wholePlaneGFF`) -/
lemma zbRiesz_cmTestOn' {U : Opens ℂ} (hadm : ZBAdmissible U) (f : zsSub U) :
    zbRiesz U (cmTestOn f) = gradFeat U f := by
  obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  exact zbRiesz_cmTestOn hh₀ hadm f

lemma cmTestOn_add {U : Opens ℂ} (f g : zsSub U) : cmTestOn (f + g) = cmTestOn f + cmTestOn g :=
  TestFunction.ext fun x => by
    have := congrArg (fun φ : TestC => φ x) (cmTest_add f.2 g.2 (f + g).2)
    simpa using this

lemma cmTestOn_smul {U : Opens ℂ} (a : ℝ) (f : zsSub U) : cmTestOn (a • f) = a • cmTestOn f :=
  TestFunction.ext fun x => by
    have := congrArg (fun φ : TestC => φ x) (cmTest_smul a f.2 (a • f).2)
    simpa using this

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Opens ℂ} {g : Ω → DistOn U}

/-- the pairing process `φ ↦ ⟨g, φ⟩` -/
def zbPair (g : Ω → DistOn U) (φ : TestOn U) : Ω → ℝ := fun ω => g ω φ

lemma memLp_zbPair (hg : IsZeroBoundaryGFF U g P) (φ : TestOn U) : MemLp (zbPair g φ) 2 P :=
  (hg.process.gaussian.hasGaussianLaw_eval φ).memLp_two

lemma centered_zbPair (hg : IsZeroBoundaryGFF U g P) (φ : TestOn U) : P[zbPair g φ] = 0 :=
  hg.process.centered φ

variable (hg : IsZeroBoundaryGFF U g P)

/-- `f ↦ [⟨g, −Δf/2π⟩] ∈ L²(P)` on `C_c^∞(U)` -/
def zbLin : zsSub U →ₗ[ℝ] Lp ℝ 2 P where
  toFun f := (memLp_zbPair hg (cmTestOn f)).toLp _
  map_add' f f' := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
    simp only [zbPair, Pi.add_apply, cmTestOn_add, map_add]
  map_smul' a f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => ?_)
    simp only [zbPair, Pi.smul_apply, smul_eq_mul, cmTestOn_smul, map_smul]

lemma inner_zbLin_toLp (hadm : ZBAdmissible U) (f : zsSub U) (φ : TestOn U) :
    ⟪zbLin hg f, (memLp_zbPair hg φ).toLp _⟫ = ⟪(gradLin U f : GradSpace U), zbRiesz U φ⟫ := by
  simp only [zbLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_toLp_eq_cov _ _ (centered_zbPair hg _)]
  refine (hg.process.covariance_eq _ _).trans ?_
  rw [zeroGFFTestCov_eq_inner hadm, zbRiesz_cmTestOn' hadm]
  rfl

lemma norm_zbLin (hadm : ZBAdmissible U) (f : zsSub U) : ‖zbLin hg f‖ = ‖gradLin U f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have h1 := inner_zbLin_toLp hg hadm f (cmTestOn f)
  rw [zbRiesz_cmTestOn' hadm] at h1
  exact h1

/-- the isometry `H₀¹(U) → L²(P)`, `∇f ↦ [⟨g, −Δf/2π⟩]` -/
def zbIso (hadm : ZBAdmissible U) : gradClosure U (zeroSpace U) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  (zbLin hg).extendOfIsometry (denseRange_gradLin U) (norm_zbLin hg hadm)

lemma zbIso_gradLin (hadm : ZBAdmissible U) (f : zsSub U) :
    zbIso hg hadm (gradLin U f) = zbLin hg f :=
  LinearMap.extendOfIsometry_eq _ _ _ f

lemma zbIso_mem_gaussSpace (hadm : ZBAdmissible U) (v : gradClosure U (zeroSpace U)) :
    zbIso hg hadm v ∈ gaussSpace (zbPair g) (memLp_zbPair hg) := by
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (zbIso hg hadm).continuous
  · rw [zbIso_gradLin]
    exact toLp_mem_gaussSpace (memLp_zbPair hg) _

lemma inner_zbIso_toLp (hadm : ZBAdmissible U) (v : gradClosure U (zeroSpace U))
    (φ : TestOn U) :
    ⟪zbIso hg hadm v, (memLp_zbPair hg φ).toLp _⟫ = ⟪(v : GradSpace U), zbRiesz U φ⟫ := by
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact isClosed_eq ((continuous_id.inner continuous_const).comp (zbIso hg hadm).continuous)
      ((continuous_subtype_val.inner continuous_const))
  · rw [zbIso_gradLin, inner_zbLin_toLp hg hadm]

/-- the isometry on test functions is the pairing: `[⟨g, φ⟩] = zbIso (Riesz φ)` -/
theorem zbIso_zbRiesz (hadm : ZBAdmissible U) (φ : TestOn U) :
    zbIso hg hadm ⟨zbRiesz U φ, zbRiesz_mem φ⟩ = (memLp_zbPair hg φ).toLp _ := by
  set v : gradClosure U (zeroSpace U) := ⟨zbRiesz U φ, zbRiesz_mem φ⟩
  set a := zbIso hg hadm v
  set b := (memLp_zbPair hg φ).toLp (zbPair g φ)
  have hab : ⟪a, b⟫ = ‖(v : GradSpace U)‖ ^ 2 := by
    rw [inner_zbIso_toLp hg hadm, real_inner_self_eq_norm_sq]
  have haa : ‖a‖ ^ 2 = ‖(v : GradSpace U)‖ ^ 2 := by
    rw [LinearIsometry.norm_map]; rfl
  have hbb : ‖b‖ ^ 2 = ‖(v : GradSpace U)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_cov _ _ (centered_zbPair hg _)]
    refine (hg.process.covariance_eq _ _).trans ?_
    rw [zeroGFFTestCov_eq_inner hadm, real_inner_self_eq_norm_sq]
  have : ‖a - b‖ ^ 2 = 0 := by
    rw [@norm_sub_sq_real, hab, haa, hbb]; ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

/-- `[⟨h̊, ρ⟩] ∈ L²(P)` for `ρ ∈ BddOn U` -/
def zbBddVec (hadm : ZBAdmissible U) (ρ : BddOn U) : Lp ℝ 2 P :=
  zbIso hg hadm ⟨rieszFun U ρ.1, rieszFun_mem U ρ.1⟩

/-- a measurable version: **the zero-boundary GFF `g` paired with `ρ ∈ BddOn U`** -/
def zbBdd (hadm : ZBAdmissible U) (ρ : BddOn U) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (zbBddVec hg hadm ρ)).aemeasurable.mk _

lemma zbBdd_ae (hadm : ZBAdmissible U) (ρ : BddOn U) :
    zbBdd hg hadm ρ =ᵐ[P] zbBddVec hg hadm ρ :=
  ((Lp.aestronglyMeasurable (zbBddVec hg hadm ρ)).aemeasurable.ae_eq_mk).symm

lemma memLp_zbBdd (hadm : ZBAdmissible U) (ρ : BddOn U) : MemLp (zbBdd hg hadm ρ) 2 P :=
  (Lp.memLp (zbBddVec hg hadm ρ)).ae_eq (zbBdd_ae hg hadm ρ).symm

lemma toLp_zbBdd (hadm : ZBAdmissible U) (ρ : BddOn U) :
    (memLp_zbBdd hg hadm ρ).toLp _ = zbBddVec hg hadm ρ := by
  rw [← Lp.toLp_coeFn (zbBddVec hg hadm ρ) (Lp.memLp _)]
  exact MemLp.toLp_congr _ _ (zbBdd_ae hg hadm ρ)

/-- **Agreement on test functions**: `⟨h̊, φ⟩` (extension) `= ⟨g, φ⟩` a.s. -/
theorem zbBdd_toBddOn_ae (hadm : ZBAdmissible U) (φ : TestOn U) :
    zbBdd hg hadm φ.toBddOn =ᵐ[P] zbPair g φ := by
  refine (zbBdd_ae hg hadm _).trans ?_
  have : zbBddVec hg hadm φ.toBddOn = (memLp_zbPair hg φ).toLp _ := by
    rw [← zbIso_zbRiesz hg hadm φ]; rfl
  rw [this]
  exact (memLp_zbPair hg φ).coeFn_toLp

/-- **The bridge** (bounded `U`): the extension is a zero-boundary GFF process on `BddOn U`. -/
theorem isZBGFFProcessExt_zbBdd (hU : Bornology.IsBounded (U : Set ℂ)) :
    IsZBGFFProcessExt U (zbBdd hg (zbAdmissible_of_isBounded hU)) P := by
  set hadm := zbAdmissible_of_isBounded hU
  have hmem : ∀ ρ, zbBddVec hg hadm ρ ∈ gaussSpace (zbPair g) (memLp_zbPair hg) :=
    fun ρ => zbIso_mem_gaussSpace hg hadm _
  have hc0 : ∀ φ, P[zbPair g φ] = 0 := centered_zbPair hg
  have hG := isGaussianProcess_of_mem_gaussSpace hg.process.gaussian hc0 (memLp_zbPair hg)
    (zbBddVec hg hadm) hmem
  have hCG : ∀ ρ, IsCGauss P (zbBddVec hg hadm ρ) := fun ρ =>
    isCGauss_of_mem_gaussSpace hg.process.gaussian hc0 (memLp_zbPair hg) (hmem ρ)
  refine ⟨fun ρ => (Lp.aestronglyMeasurable _).aemeasurable.measurable_mk, ?_, fun ρ => ?_,
    fun ρ σ => ?_⟩
  · exact hG.congr fun ρ => (zbBdd_ae hg hadm ρ).symm
  · rw [integral_congr_ae (zbBdd_ae hg hadm ρ)]; exact (hCG ρ).2
  · have h0 : P[zbBdd hg hadm ρ] = 0 := by
      rw [integral_congr_ae (zbBdd_ae hg hadm ρ)]; exact (hCG ρ).2
    rw [← inner_toLp_eq_cov (memLp_zbBdd hg hadm ρ) (memLp_zbBdd hg hadm σ) h0,
      toLp_zbBdd, toLp_zbBdd, zbBddVec, zbBddVec, LinearIsometry.inner_map_map,
      Submodule.coe_inner]
    exact inner_rieszFun (admissible_bddOn hU ρ) (admissible_bddOn hU σ)

end LQGMetric.DFGPS
