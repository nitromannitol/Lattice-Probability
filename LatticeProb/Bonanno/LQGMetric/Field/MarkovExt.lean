/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovExt at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZBIndep
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt

/-!
# The zero-boundary part extended by zero, at the level of pairings (task P2-MARKOV, part 6)

LM Lemma 2.1 (`Blueprint.LMLem2_1`) asks for `h̊` as a distribution on all of `ℂ`, vanishing off
`cl V`, whose restriction to `V` is a zero-boundary GFF. At the level of pairings this is
`φ ↦ ⟨h̊, φ 1_V⟩`: the image under the Cameron–Martin isometry `cmIso` of the Riesz vector of
`f ↦ ∫_V f φ` on `C_c^∞(V)` (`rieszFun V (1_V φ)`). This file proves, for every `φ ∈ 𝓓(ℂ)`:

* `zbExt_ae_eq_zbProc` : on `𝓓(V)` it is the zero-boundary part `zbProc`;
* `zbExt_ae_eq_zero` : it vanishes for `φ` vanishing on `V` (in particular off `cl V`);
* `isGaussianProcess_zbExt`, `integral_zbExt`, `covariance_zbExt` (bounded `V`): a centred
  Gaussian process with covariance `zeroGFFTestCov V (1_V φ) (1_V ψ)`, the law of the
  zero-boundary GFF extended by zero (`IsZBGFFProcessExt.extZero`);
* `indep_zbExt_fieldSigmaClosed` : it is independent of the germ `σ(h|_{ℂ∖V})` when
  `V ∩ ∂𝔻 = ∅`.

Sources as in `MarkovZB` (IG4 Prop. 2.8; BP Thm 1.52; Sheffield math/0312099 §2.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovExt

open MarkovGauss MarkovZB MarkovGerm MarkovZBIndep Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the Riesz vector of `f ↦ ∫ f ρ` on `C_c^∞(U)` -/
def rieszFun (U : Opens ℂ) (ρ : ℂ → ℝ) : GradSpace U :=
  rieszVec U (zeroSpace U) (testMeasPos ρ) - rieszVec U (zeroSpace U) (testMeasNeg ρ)

lemma rieszFun_mem (U : Opens ℂ) (ρ : ℂ → ℝ) : rieszFun U ρ ∈ gradClosure U (zeroSpace U) :=
  sub_mem rieszVec_mem rieszVec_mem

lemma rieszVec_zero_measure (U : Opens ℂ) : rieszVec U (zeroSpace U) (0 : Measure ℂ) = 0 := by
  unfold rieszVec
  split_ifs with hex
  · exact eq_of_mem_gradClosure hex.choose_spec.1 (zero_mem _) fun f hf => by
      rw [hex.choose_spec.2 f hf, inner_zero_left, integral_zero_measure]
  · rfl

lemma rieszFun_zero (U : Opens ℂ) : rieszFun U 0 = 0 := by
  have h1 : testMeasPos (0 : ℂ → ℝ) = 0 := by simp [testMeasPos]
  have h2 : testMeasNeg (0 : ℂ → ℝ) = 0 := by simp [testMeasNeg]
  rw [rieszFun, h1, h2, rieszVec_zero_measure, sub_zero]

theorem inner_rieszFun {U : Opens ℂ} {ρ σ : ℂ → ℝ}
    (hρ : IsAdmissibleDual U (zeroSpace U) (testMeasPos ρ) ∧
      IsAdmissibleDual U (zeroSpace U) (testMeasNeg ρ))
    (hσ : IsAdmissibleDual U (zeroSpace U) (testMeasPos σ) ∧
      IsAdmissibleDual U (zeroSpace U) (testMeasNeg σ)) :
    ⟪rieszFun U ρ, rieszFun U σ⟫ = zeroGFFTestCov U ρ σ := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  unfold zeroGFFTestCov rieszFun
  rw [dualCov_eq_inner_rieszVec hV hρ.1 hσ.1, dualCov_eq_inner_rieszVec hV hρ.1 hσ.2,
    dualCov_eq_inner_rieszVec hV hρ.2 hσ.1, dualCov_eq_inner_rieszVec hV hρ.2 hσ.2]
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- `φ ↦ [⟨h̊, ρ⟩] ∈ L²(P)` -/
def extVec (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (ρ : ℂ → ℝ) : Lp ℝ 2 P :=
  cmIso hh U ⟨rieszFun U ρ, rieszFun_mem U ρ⟩

/-- the zero-boundary part extended by zero, `φ ↦ ⟨h̊, φ 1_U⟩` (measurable version) -/
def zbExt (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (φ : TestC) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (extVec hh U ((U : Set ℂ).indicator φ))).aemeasurable.mk _

lemma measurable_zbExt (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (φ : TestC) :
    Measurable (zbExt hh U φ) :=
  (Lp.aestronglyMeasurable _).aemeasurable.measurable_mk

lemma zbExt_ae (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (φ : TestC) :
    zbExt hh U φ =ᵐ[P] extVec hh U ((U : Set ℂ).indicator φ) :=
  ((Lp.aestronglyMeasurable _).aemeasurable.ae_eq_mk).symm

lemma indicator_extC {U : Opens ℂ} (φ : TestOn U) :
    (U : Set ℂ).indicator (extC U φ : ℂ → ℝ) = φ := by
  rw [coe_extC]
  funext x
  by_cases hx : x ∈ (U : Set ℂ)
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, φ.zero_on_compl hx]; rfl

/-- on `𝓓(U)` the extension is the zero-boundary part `zbProc` -/
theorem zbExt_ae_eq_zbProc (hh : IsWholePlaneGFF h P) {U : Opens ℂ} (φ : TestOn U) :
    zbExt hh U (extC U φ) =ᵐ[P] zbProc hh φ := by
  have : extVec hh U ((U : Set ℂ).indicator (extC U φ)) = zbVec hh φ := by
    rw [extVec, indicator_extC]; rfl
  exact (zbExt_ae hh U _).trans (this ▸ (zbProc_ae hh φ).symm)

/-- the extension vanishes for test functions vanishing on `U` -/
theorem zbExt_ae_eq_zero (hh : IsWholePlaneGFF h P) {U : Opens ℂ} {φ : TestC}
    (hφ : ∀ x ∈ (U : Set ℂ), φ x = 0) : zbExt hh U φ =ᵐ[P] 0 := by
  have h0 : (U : Set ℂ).indicator (φ : ℂ → ℝ) = 0 := by
    funext x
    by_cases hx : x ∈ (U : Set ℂ)
    · rw [indicator_of_mem hx, hφ x hx, Pi.zero_apply]
    · rw [indicator_of_notMem hx, Pi.zero_apply]
  have : extVec hh U ((U : Set ℂ).indicator φ) = 0 := by
    rw [extVec, h0]
    have : (⟨rieszFun U 0, rieszFun_mem U 0⟩ : gradClosure (U : Set ℂ) (zeroSpace U)) = 0 :=
      Subtype.ext (rieszFun_zero U)
    rw [this, map_zero]
  refine (zbExt_ae hh U φ).trans ?_
  rw [this]
  exact Lp.coeFn_zero _ _ _

lemma extVec_mem_gaussSpace (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (ρ : ℂ → ℝ) :
    extVec hh U ρ ∈ gaussSpace (pairProc h) (memLp_pair hh) :=
  cmIso_mem_gaussSpace hh U _

/-- the extension is a Gaussian process, jointly with the mean-zero pairings of `h` -/
theorem isGaussianProcess_zbExt_sumElim (hh : IsWholePlaneGFF h P) (U : Opens ℂ) :
    IsGaussianProcess (Sum.elim (fun φ : TestC => zbExt hh U φ) (pairProc h)) P := by
  have := isGaussianProcess_sumElim (gaussian_pairProc hh) (centered_pairProc hh)
    (memLp_pair hh) (fun φ : TestC => extVec hh U ((U : Set ℂ).indicator φ))
    (fun φ => extVec_mem_gaussSpace hh U _) (id : TestC0 → TestC0)
  refine this.congr fun x => ?_
  cases x with
  | inl φ => exact (zbExt_ae hh U φ).symm
  | inr ψ => exact Filter.EventuallyEq.rfl

theorem integral_zbExt (hh : IsWholePlaneGFF h P) (U : Opens ℂ) (φ : TestC) :
    P[zbExt hh U φ] = 0 := by
  rw [integral_congr_ae (zbExt_ae hh U φ)]
  exact (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh) (centered_pairProc hh)
    (memLp_pair hh) (extVec_mem_gaussSpace hh U _)).2

/-- covariance of the extension (bounded `U`): `zeroGFFTestCov U (1_U φ) (1_U ψ)` -/
theorem covariance_zbExt (hh : IsWholePlaneGFF h P) {U : Opens ℂ}
    (hU : Bornology.IsBounded (U : Set ℂ)) (φ ψ : TestC) :
    cov[zbExt hh U φ, zbExt hh U ψ; P] =
      zeroGFFTestCov U ((U : Set ℂ).indicator φ) ((U : Set ℂ).indicator ψ) := by
  have hm : MemLp (zbExt hh U ψ) 2 P := (Lp.memLp _).ae_eq (zbExt_ae hh U ψ).symm
  have hcov : cov[zbExt hh U φ, zbExt hh U ψ; P] =
      cov[(extVec hh U ((U : Set ℂ).indicator φ) : Ω → ℝ), zbExt hh U ψ; P] := by
    unfold covariance
    refine integral_congr_ae ?_
    filter_upwards [zbExt_ae hh U φ] with ω h1
    rw [h1, integral_congr_ae (zbExt_ae hh U φ)]
  have h0 : P[(extVec hh U ((U : Set ℂ).indicator φ) : Ω → ℝ)] = 0 := by
    rw [← integral_congr_ae (zbExt_ae hh U φ), integral_zbExt]
  rw [hcov, covariance_eq_inner _ hm h0, MemLp.toLp_congr hm (Lp.memLp _) (zbExt_ae hh U ψ),
    Lp.toLp_coeFn, extVec, extVec, LinearIsometry.inner_map_map, Submodule.coe_inner]
  exact inner_rieszFun (admissible_bddOn hU (extZeroTest U φ))
    (admissible_bddOn hU (extZeroTest U ψ))

/-- **Independence from the germ** (`U ∩ ∂𝔻 = ∅`). -/
theorem indep_zbExt_fieldSigmaClosed (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) :
    Indep (MeasurableSpace.comap (fun ω (φ : TestC) => zbExt hh.1 U φ ω) MeasurableSpace.pi)
      (fieldSigmaClosed h (U : Set ℂ)ᶜ) P :=
  indep_cmIso_fieldSigmaClosed hh hU
    (fun φ : TestC => ⟨rieszFun U ((U : Set ℂ).indicator φ), rieszFun_mem U _⟩)
    (fun φ => zbExt hh.1 U φ) (fun φ => measurable_zbExt hh.1 U φ) fun φ => zbExt_ae hh.1 U φ

end MarkovExt
end LQGMetric
