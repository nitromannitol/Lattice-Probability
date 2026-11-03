/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovHarm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV

/-!
# The harmonic part is weakly harmonic, at the level of pairings (task P2-MARKOV, part 7)

For `f ∈ C_c^∞(U)` the test function `ρ_f = −Δf/(2π)` lies in `𝓓(U)` (`cmTestOn f`) and its Riesz
vector in `H₀¹(U)` is `∇f` itself (`zbRiesz_cmTestOn`: `⟨∇f, ∇g⟩_∇ = ∫ g ρ_f`, Green's identity,
here read off the Cameron–Martin isometry). Hence the zero-boundary part of `h` tested against
`ρ_f` is `⟨h, ρ_f⟩` itself (`zbProc_cmTestOn_ae`): the harmonic part `𝔥 = h − h̊` satisfies
`⟨𝔥, Δf⟩ = 0` almost surely for each `f ∈ C_c^∞(U)` — `𝔥` is weakly harmonic on `U`, the
pairing-level form of "𝔥 is harmonic on V" in LM Lemma 2.1 (IG4 Prop. 2.8: `h₂ ∈ H^⊥(W)`, the
functions harmonic in `W`; Sheffield math/0312099 Thm 2.17; BP Thm 1.52).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Laplacian
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovHarm

open MarkovGauss MarkovZB QuantumZipper QuantumZipper.K3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

lemma tsupport_cmTest_subset {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    tsupport (cmTest (zsTest hf) : ℂ → ℝ) ⊆ tsupport f :=
  closure_minimal (fun x hx => by_contra fun h' => hx (by
    rw [cmTest_apply, show (⇑(zsTest hf) : ℂ → ℝ) = f from rfl,
      laplacian_eq_zero_of_notMem_tsupport h', mul_zero])) (isClosed_tsupport _)

/-- `ρ_f = −Δf/(2π)` as a test function on `U` -/
def cmTestOn {U : Opens ℂ} (f : zsSub U) : TestOn U where
  toFun := cmTest (zsTest f.2)
  contDiff' := (cmTest (zsTest f.2)).contDiff
  hasCompactSupport' := (cmTest (zsTest f.2)).hasCompactSupport
  tsupport_subset' := (tsupport_cmTest_subset f.2).trans f.2.2.2

@[simp] lemma cmTestOn_apply {U : Opens ℂ} (f : zsSub U) (x : ℂ) :
    cmTestOn f x = cmTest (zsTest f.2) x := rfl

/-- Green's identity `⟨∇f, ∇g⟩_∇ = ∫ ρ_f g`, read off the Cameron–Martin isometry -/
lemma inner_gradLin (hh : IsWholePlaneGFF h P) {U : Opens ℂ} (f g : zsSub U) :
    ⟪gradLin U f, gradLin U g⟫ = ∫ x, cmTest (zsTest f.2) x * g.1 x := by
  rw [← (cmIso hh U).inner_map_map, cmIso_gradLin, cmIso_gradLin]
  simp only [cmLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_toLp_eq_cov _ _ (centered_pairProc hh _)]
  exact (hh.covariance_eq _ _).trans (logCov_cmTest_right _ _)

/-- the Riesz vector of `ρ_f` is `∇f` -/
theorem zbRiesz_cmTestOn (hh : IsWholePlaneGFF h P) {U : Opens ℂ} (hadm : ZBAdmissible U)
    (f : zsSub U) : zbRiesz U (cmTestOn f) = gradFeat U f := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · refine eq_of_mem_gradClosure (zbRiesz_mem _) (gradFeat_mem_gradClosure f.2) fun g hg => ?_
    rw [inner_zbRiesz_gradFeat hadm hpos _ hg]
    have h1 := inner_gradLin hh f ⟨g, hg⟩
    rw [Submodule.coe_inner] at h1
    change ∫ x, g x * cmTest (zsTest f.2) x = ⟪gradFeat U f, gradFeat U g⟫
    rw [show ⟪gradFeat U f, gradFeat U g⟫ = ⟪((gradLin U f : gradClosure (U : Set ℂ) _) :
      GradSpace U), (gradLin U ⟨g, hg⟩ : gradClosure (U : Set ℂ) _)⟫ from rfl, h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  · rw [zbRiesz_eq_zero_of_nopos hpos]
    refine (gradFeat_eq_zero_of_energy hV f.2 ?_).symm
    exact le_antisymm (not_lt.1 fun hlt => hpos ⟨f, f.2, hlt⟩) (energy_nonneg _ _)

theorem zbVec_cmTestOn (hh : IsWholePlaneGFF h P) {U : Opens ℂ} (hadm : ZBAdmissible U)
    (f : zsSub U) : zbVec hh (cmTestOn f) = cmLin hh U f := by
  rw [zbVec, ← cmIso_gradLin]
  congr 1
  exact Subtype.ext (zbRiesz_cmTestOn hh hadm f)

/-- **Weak harmonicity of the harmonic part**: `⟨h̊, ρ_f⟩ = ⟨h, ρ_f⟩` a.s. for `f ∈ C_c^∞(U)`,
i.e. `⟨h − h̊, Δf⟩ = 0`. -/
theorem zbProc_cmTestOn_ae (hh : IsWholePlaneGFF h P) {U : Opens ℂ} (hadm : ZBAdmissible U)
    (f : zsSub U) : zbProc hh (cmTestOn f) =ᵐ[P] fun ω => h ω (cmTest (zsTest f.2)) := by
  refine (zbProc_ae hh _).trans ?_
  rw [zbVec_cmTestOn hh hadm f]
  exact (memLp_pair hh _).coeFn_toLp

end MarkovHarm
end LQGMetric
