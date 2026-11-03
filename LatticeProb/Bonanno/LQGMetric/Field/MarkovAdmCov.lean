/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovAdmCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAdm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pairing-level Markov statements on unbounded `V` (task P2-MKA, leaf (A) of P2-MARKOV)

`covariance_zbExt`, `inner_pairVec_cmIso`, `indepFun_harm_zbExt` (`MarkovExt`, `MarkovNorm`)
assume `U` bounded only to get admissibility of `(φ 1_U)^± dz`; with
`MarkovAdm.admissible_extZero_of_disjoint_sphere` the same proofs work for every open `U` with
`U ∩ ∂𝔻 = ∅` (the `_of_disjoint` versions below; the proofs are verbatim copies).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovAdm

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm CircleAvg Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- `[⟨h, φ⟩]` pairs with `H₀¹(U)` like the Riesz vector of `φ 1_U` (`U ∩ ∂𝔻 = ∅`) -/
theorem inner_pairVec_cmIso_of_disjoint (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1))
    (φ : TestC) (v : gradClosure (U : Set ℂ) (zeroSpace U)) :
    ⟪pairVec hh φ, cmIso hh.1 U v⟫ = ⟪rieszFun U ((U : Set ℂ).indicator φ), (v : GradSpace U)⟫ := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  refine (denseRange_gradLin U).induction_on v ?_ fun f => ?_
  · exact isClosed_eq ((continuous_const.inner continuous_id).comp (cmIso hh.1 U).continuous)
      (continuous_const.inner continuous_subtype_val)
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · rw [cmIso_gradLin, inner_pairVec_cmLin hh hU φ f]
    change _ = ⟪rieszFun U ((U : Set ℂ).indicator φ), gradFeat U f.1⟫
    have hadm : IsAdmissibleDual U (zeroSpace U) (testMeasPos (extZeroTest U φ).1) ∧
        IsAdmissibleDual U (zeroSpace U) (testMeasNeg (extZeroTest U φ).1) :=
      admissible_extZero_of_disjoint_sphere hU φ
    obtain ⟨hm, ⟨C, hC⟩, -⟩ := (extZeroTest U φ).2
    rw [rieszFun, inner_sub_left]
    change ∫ x, φ x * f.1 x =
      ⟪rieszVec U (zeroSpace U) (testMeasPos (extZeroTest U φ).1), gradFeat U f.1⟫ -
      ⟪rieszVec U (zeroSpace U) (testMeasNeg (extZeroTest U φ).1), gradFeat U f.1⟫
    rw [pair_rieszVec hV hadm.1 hpos f.1 f.2,
      pair_rieszVec hV hadm.2 hpos f.1 f.2]
    change _ = ∫ x, f.1 x ∂testMeasPos (extZeroTest U φ).1 -
      ∫ x, f.1 x ∂testMeasNeg (extZeroTest U φ).1
    rw [integral_testMeas_sub hm hC f.2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change φ x * f.1 x = (U : Set ℂ).indicator φ x * f.1 x
    by_cases hx : x ∈ (U : Set ℂ)
    · rw [indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport fun h' => hx (f.2.2.2 h'), mul_zero, mul_zero]
  · have h0 : gradLin U f = 0 := Subtype.ext (gradFeat_eq_zero_of_energy hV f.2
      (le_antisymm (not_lt.1 fun hlt => hpos ⟨f.1, f.2, hlt⟩) (energy_nonneg _ _)))
    rw [h0, map_zero, inner_zero_right, ZeroMemClass.coe_zero, inner_zero_right]

/-- **The harmonic part is independent of the zero-boundary part** (pairing level, `U ∩ ∂𝔻 = ∅`). -/
theorem indepFun_harm_zbExt_of_disjoint (hh : IsNormalizedWPGFF h P) {U : Opens ℂ}
    (hU : Disjoint (U : Set ℂ) (sphere 0 1)) :
    IndepFun (fun ω (φ : TestC) => h ω φ - zbExt hh.1 U φ ω)
      (fun ω (ψ : TestC) => zbExt hh.1 U ψ ω) P := by
  set W₁ : TestC → Lp ℝ 2 P := fun φ => pairVec hh φ - extVec hh.1 U ((U : Set ℂ).indicator φ)
  set W₂ : TestC → Lp ℝ 2 P := fun ψ => extVec hh.1 U ((U : Set ℂ).indicator ψ)
  have hmem : ∀ x, Sum.elim W₁ W₂ x ∈ gaussSpace (pairProc h) (memLp_pair hh.1) := fun x => by
    cases x with
    | inl φ => exact sub_mem (pairVec_mem_gaussSpace hh φ) (extVec_mem_gaussSpace hh.1 U _)
    | inr ψ => exact extVec_mem_gaussSpace hh.1 U _
  have hc : ∀ x, ∫ ω, (Sum.elim W₁ W₂ x : Lp ℝ 2 P) ω ∂P = 0 := fun x =>
    (isCGauss_of_mem_gaussSpace (gaussian_pairProc hh.1) (centered_pairProc hh.1)
      (memLp_pair hh.1) (hmem x)).2
  have hae₁ : ∀ φ, (fun ω => h ω φ - zbExt hh.1 U φ ω) =ᵐ[P] (W₁ φ : Ω → ℝ) := fun φ => by
    filter_upwards [Lp.coeFn_sub (pairVec hh φ) (extVec hh.1 U ((U : Set ℂ).indicator φ)),
      pairVec_ae hh φ, zbExt_ae hh.1 U φ] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hG := (isGaussianProcess_of_mem_gaussSpace (gaussian_pairProc hh.1)
    (centered_pairProc hh.1) (memLp_pair hh.1) (Sum.elim W₁ W₂) hmem).congr
    (Y := Sum.elim (fun φ ω => h ω φ - zbExt hh.1 U φ ω) fun ψ => zbExt hh.1 U ψ) fun x => by
      cases x with
      | inl φ => exact (hae₁ φ).symm
      | inr ψ => exact (zbExt_ae hh.1 U ψ).symm
  refine hG.indepFun_of_covariance_eq_zero
    (fun φ => ((measurable_eval hh.1 φ).sub (measurable_zbExt hh.1 U φ)).aemeasurable)
    (fun ψ => (measurable_zbExt hh.1 U ψ).aemeasurable) fun φ ψ => ?_
  rw [cov_congr_ae (hae₁ φ) (zbExt_ae hh.1 U ψ),
    covariance_eq_inner (W₁ φ) (Lp.memLp (W₂ ψ)) (hc (Sum.inl φ)), Lp.toLp_coeFn]
  change ⟪pairVec hh φ - cmIso hh.1 U ⟨rieszFun U _, rieszFun_mem U _⟩,
    cmIso hh.1 U ⟨rieszFun U _, rieszFun_mem U _⟩⟫ = 0
  rw [inner_sub_left, inner_pairVec_cmIso_of_disjoint hh hU, LinearIsometry.inner_map_map,
    Submodule.coe_inner, sub_self]

end MarkovAdm
end LQGMetric
