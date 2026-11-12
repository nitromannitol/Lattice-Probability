/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.ZBDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.ZBSFub
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsmB
import LatticeProb.Bonanno.LQGMetric.Field.ExistDist
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG

/-!
# The white-noise zero-boundary GFF on a square as a random distribution (task P2-DGZB)

`exists_zbDist`: for a white noise `W` and `D = (a, a+L)²` there is a measurable
`hz : Ω → 𝒟'(ℂ)` with

* `⟨hz, φ⟩ = h^D(φ 1_D) = √π W(zbKer(φ 1_D))` a.s. for every `φ ∈ 𝓓(ℂ)`;
* `hz` vanishing off `cl D` for **every** `ω`;

hence `IsZBGFFExtDist (sqOpens a L) hz P` (`isZBGFFExtDist_zbDist`).

Construction (as `GFFExist.exists_wholePlaneGFF`, D109): `hz₀ = antiDist Y` for the continuous
version `Y` of the antiderivative field (`exists_continuous_zbRectField`), whose pairings are
identified by stochastic Fubini (`ae_integral_d12_mul_zb`); then the null-set modification of
`MarkovVer.exists_vanishing_version_zbExt` (copied, with `zbExt` replaced by `zbXSq`: a test
function vanishing on `D` pairs to `W(0) = 0` a.s.).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DGo
namespace ZB

open WhiteNoise HeatSq DDDF.P29WN GFFExist HeatDir MarkovGerm MarkovVer Blueprint

variable {a L : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma wn_zero_ae (hW : IsWhiteNoise P W) : W 0 =ᵐ[P] 0 := by
  have := hW.isProbabilityMeasure
  have h := wn_integral_mul hW 0 0
  rw [inner_zero_left] at h
  have hi : Integrable (fun ω => W 0 ω ^ 2) P := (wn_memLp hW 0).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (W 0 ω)) hi).mp
    (by simpa [sq] using h)
  filter_upwards [h0] with ω hω
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hω

lemma zbKerL2_eq_zero (hL : 0 < L) (ρ : BddOn (sqOpen a L)) (h : ∀ z, ρ.1 z = 0) :
    zbKerL2 a L hL ρ = 0 := by
  have hb := sq_norm_zbKerL2_le hL ρ (C := 0) (fun z => by rw [h z, abs_zero])
  simp only [h, abs_zero, integral_zero, mul_zero] at hb
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (le_antisymm hb (sq_nonneg _)))

/-- a test function vanishing on `D` pairs to `0` a.s. -/
lemma zbXSq_extZero_ae_zero (hL : 0 < L) (hW : IsWhiteNoise P W) {ψ : TestC}
    (hψ : ∀ x ∈ sqOpen a L, ψ x = 0) :
    zbXSq a L hL W (extZeroTest (sqOpens a L) ψ) =ᵐ[P] 0 := by
  have h0 : zbKerL2 a L hL (extZeroTest (sqOpens a L) ψ) = 0 :=
    zbKerL2_eq_zero hL _ fun z => by
      show (sqOpen a L).indicator ψ z = 0
      by_cases hz : z ∈ sqOpen a L
      · rw [indicator_of_mem hz, hψ z hz]
      · rw [indicator_of_notMem hz]
  simp only [zbXSq, h0, smul_zero]
  exact wn_zero_ae hW

/-- **The white-noise zero-boundary GFF as a random distribution**, vanishing off `cl D`. -/
theorem exists_zbDist (hL : 0 < L) (hW : IsWhiteNoise P W) :
    ∃ hz : Ω → DistC, Measurable hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbXSq a L hL W (extZeroTest (sqOpens a L) φ)) ∧
      ∀ ω, restrictTo (toOpens (closure (sqOpen a L))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0 := by
  have := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_zbRectField (a := a) hL hW
  set hz := gffOf Y hYc
  have hm : Measurable hz := measurable_gffOf Y hYc hYm
  have hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbXSq a L hL W (extZeroTest (sqOpens a L) φ) :=
    fun φ => by simpa only [hz, gffOf_apply] using ae_integral_d12_mul_zb hL hW hYc hYm hYW φ
  -- the null-set modification (copied from `MarkovVer.exists_vanishing_version_zbExt`)
  set V : Opens ℂ := sqOpens a L
  set O := outV V
  set S : Set Ω := {ω | ∀ c : CoordJ, hz ω (extC O (comb O c)) = 0}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun c =>
      measurableSet_eq_fun ((measurable_distOn_apply _).comp hm) measurable_const
  have hvan : ∀ c : CoordJ, ∀ x ∈ sqOpen a L, (extC O (comb O c)) x = 0 := by
    intro c x hx
    rw [coe_extC]
    refine (comb O c).zero_on_compl fun hxW => ?_
    have : x ∉ closure (V : Set ℂ) := hxW
    exact this (subset_closure hx)
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    have : ∀ᵐ ω ∂P, ∀ c : CoordJ, hz ω (extC O (comb O c)) = 0 := by
      rw [ae_all_iff]
      intro c
      filter_upwards [hv (extC O (comb O c)), zbXSq_extZero_ae_zero hL hW (hvan c)]
        with ω h1 h2
      rw [h1, h2]; rfl
    exact this
  have hrS : ∀ ω ∈ S, restrictTo O (hz ω) = 0 := fun ω hω =>
    injective_pairJ O (funext fun c => by
      show restrictTo O (hz ω) (comb O c) = (0 : DistOn O) (comb O c)
      rw [ContinuousLinearMap.zero_apply]
      exact hω c)
  classical
  refine ⟨fun ω => if ω ∈ S then hz ω else 0, Measurable.ite hS hm measurable_const,
    fun φ => ?_, fun ω => ?_⟩
  · filter_upwards [hSae, hv φ] with ω h1 h2
    simp only [if_pos h1]
    exact h2
  · by_cases hω : ω ∈ S
    · simp only [if_pos hω]
      exact hrS ω hω
    · simp only [if_neg hω]
      exact ContinuousLinearMap.zero_comp _

lemma extZeroTest_monoCLM (φ : TestOn (sqOpens a L)) :
    extZeroTest (sqOpens a L) (TestFunction.monoCLM ℝ φ) = φ.toBddOn := by
  refine Subtype.ext (funext fun x => ?_)
  show (sqOpen a L).indicator (TestFunction.monoCLM ℝ φ : TestC) x = φ x
  by_cases hx : x ∈ sqOpen a L
  · rw [indicator_of_mem hx]; simp [TestFunction.monoCLM_apply]
  · rw [indicator_of_notMem hx]; exact (φ.zero_on_compl hx).symm

/-- the zero-boundary GFF property of such an `hz` -/
theorem isZBGFFExtDist_of_zb (hL : 0 < L) (hW : IsWhiteNoise P W) {hz : Ω → DistC}
    (hm : Measurable hz)
    (hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbXSq a L hL W (extZeroTest (sqOpens a L) φ))
    (h0 : ∀ ω, restrictTo (toOpens (closure (sqOpen a L))ᶜ isClosed_closure.isOpen_compl)
      (hz ω) = 0) :
    Blueprint.IsZBGFFExtDist (sqOpens a L) hz P := by
  have := hW.isProbabilityMeasure
  refine ⟨⟨(measurable_restrictTo _).comp hm, ?_⟩, h0⟩
  refine MarkovAsm.isZBGFFProcess_congr (isZBGFFProcessExt_zbXSq hL hW).restrict
    (fun φ => (measurable_distOn_apply φ).comp ((measurable_restrictTo _).comp hm))
    fun φ => ?_
  have h := hv (TestFunction.monoCLM ℝ φ)
  rw [extZeroTest_monoCLM] at h
  exact h.symm

end ZB
end DGo
end LQGMetric
