/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1C3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C2

/-!
# DG Lemma 3.1, unconditional (task P2-DG105e, decision D109)

DG (`metric-comparison-final.tex`, Lemma 3.1 `lem-gff-compare`, DG:966–976) only asserts the
existence of a coupling of `h`, `h^U`, `ĥ`, `ĥ^tr`. We take the whole-plane GFF built from the
same white noise `W` that defines `h^U`, `ĥ`, `ĥ^tr` (`Field/ExistGFF`: `h₀(φ) = W(kerFun φ)`),
normalized by `h = h₀ − h₀_1(0)`. Then (DEVIATIONS, D109: this replaces DG's Markov
decomposition `h = h^U + 𝔥` and DG Lemma 2.2 for the pair `(h, h^U)`):

* `dgCircMod_h0_hat`: `(h₀ − ĥ)|_K = √π W(largeKerL2 ·)` has a continuous modification with
  Gaussian tail (`exists_box_modification_tail`, Hölder bound `norm_largeKerL2_sub_sq_le_box`),
  identified on circles by stochastic Fubini (`ae_integral_eq_wn`) and `ae_circleAvg_eq_wn`;
* `dgCircMod_const`: the random constant `h₀_1(0)` (a Gaussian `W(g₀)`);
* **`dgLem31HCoupling_proved`**: `DGLem31HCoupling y b`, via `(h, h^U) = (h, ĥ) − (h^U, ĥ)`
  (`DGCircMod.sub`, `dg_lemma31_hU_hat_circ'`);
* **`dg_lemma31_proved`**: DG Lemma 3.1 (all six pairs), unconditional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DG

open WhiteNoise GFFExist DZZ QuantumZipper SupTail CircleAvg KilledHeat GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the white noise together with the whole-plane GFF built from it (`Field/ExistGFF`) -/
theorem exists_wn_wholePlaneGFF :
    ∃ (W : WNSpace → (ℕ → ℝ) → ℝ) (h₀ : (ℕ → ℝ) → DistC),
      IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧
      IsWholePlaneGFF h₀ LQGDimension.ExistAsm.stdP ∧
      ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[LQGDimension.ExistAsm.stdP] W (testL2 φ) := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hP := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_rectField hW
  have hae : ∀ φ : TestC, (fun ω => gffOf Y hYc ω φ) =ᵐ[LQGDimension.ExistAsm.stdP]
      W (testL2 φ) := fun φ => by
    simpa only [gffOf_apply] using ae_integral_d12_mul_eq hW hYc hYm hYW φ
  refine ⟨W, gffOf Y hYc, hW, ?_, hae⟩
  have hmean : ∀ φ : TestC, ∫ ω, gffOf Y hYc ω φ ∂LQGDimension.ExistAsm.stdP = 0 := fun φ => by
    rw [integral_congr_ae (hae φ),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  refine ⟨measurable_gffOf Y hYc hYm, ?_, fun φ => hmean φ.1, ?_⟩
  · exact (hW.isGaussianProcess_comp (fun φ : TestC0 => testL2 φ.1)).congr
      (fun φ => (hae φ.1).symm)
  · intro φ ψ
    have hm1 := (wn_memLp hW (testL2 φ.1)).ae_eq (hae φ.1).symm
    have hm2 := (wn_memLp hW (testL2 ψ.1)).ae_eq (hae ψ.1).symm
    rw [covariance_eq_sub hm1 hm2, hmean φ.1, zero_mul, sub_zero,
      integral_congr_ae ((hae φ.1).mul (hae ψ.1))]
    have := wn_integral_mul hW (testL2 φ.1) (testL2 ψ.1)
    simp only [Pi.mul_apply]
    rw [this, inner_testL2_testL2 φ.1 ψ.1 φ.2 ψ.2]

section Pairs

variable {h₀ : Ω → DistC} (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
  (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {y : ℂ} {b : ℝ} (hb : 0 < b)

include hW in
/-- stochastic Fubini for a `√π W(k ·)` modification on the box, circle by circle -/
lemma ae_integral_box_modification {k : ℂ → WNSpace} (hk : Continuous k) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun z => Y z ω) (hYm : ∀ z, Measurable (Y z))
    (hYW : ∀ z ∈ ferniqueBox y b, Y z =ᵐ[P] fun ω => Real.sqrt Real.pi * W (k z) ω)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hB : Metric.closedBall z r ⊆ ferniqueBox y b) :
    (fun ω => ∫ x, Y x ω ∂circleUnif z r) =ᵐ[P]
      fun ω => Real.sqrt Real.pi * W (∫ x, k x ∂circleUnif z r) ω := by
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  set S := ferniqueBox y b
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hσS : circleUnif z r Sᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 hB) (circleUnif_compl_closedBall hr z)
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hk.continuousOn
  set Y' : ℂ → Ω → ℝ := fun x ω => Y x ω / Real.sqrt Real.pi
  have hYW' : ∀ x ∈ S, Y' x =ᵐ[P] W (k x) := fun x hx => by
    filter_upwards [hYW x hx] with ω h
    simp only [Y', h]; field_simp
  have hF := ae_integral_eq_wn hW hSc hσS hM (fun ω => (hYc ω).div_const _)
    (fun x => (hYm x).div_const _) hYW' (integrable_circleUnif_of_continuous' hk hr)
  filter_upwards [hF] with ω h1
  have e : ∫ x, Y x ω ∂circleUnif z r = Real.sqrt Real.pi * ∫ x, Y' x ω ∂circleUnif z r := by
    rw [← integral_const_mul]; congr 1; funext x; simp only [Y']; field_simp
  rw [e, h1]

include hW hh hae hb in
/-- **The pair `(h₀, ĥ)`** for the white-noise GFF `h₀` -/
theorem dgCircMod_h0_hat :
    DGCircMod P (ferniqueBox y b) fun z r ω => circleAvg (h₀ ω) r z - dgHat W z r ω := by
  obtain ⟨Y, hYc, hYm, hYW, hT⟩ := exists_box_modification_tail hW largeKerL2 hb
    (L := 2 * b / (2 * Real.pi)) (by positivity) fun x hx c hc => norm_largeKerL2_sub_sq_le_box hx hc
  refine ⟨Y, hYc, hYm, hT, fun z r hr hB => ?_⟩
  filter_upwards [ae_integral_box_modification hW continuous_largeKerL2 hYc hYm hYW hr hB,
    ae_circleAvg_eq_wn hW hh hae z hr] with ω h1 h2
  rw [h1, h2, dgHat]; ring

include hW hh hae hb in
/-- the random constant `h₀_1(0)` -/
theorem dgCircMod_const :
    DGCircMod P (ferniqueBox y b) fun _ _ ω => circleAvg (h₀ ω) 1 0 := by
  have := hW.isProbabilityMeasure
  set σ₀ := circleUnif 0 1
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : WNSpace,
      g₀ = Real.sqrt Real.pi • hatMeasKerL2 σ₀ + Real.sqrt Real.pi • ∫ u, largeKerL2 u ∂σ₀ :=
    ⟨_, rfl⟩
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hc : (fun ω => circleAvg (h₀ ω) 1 0) =ᵐ[P] W g₀ := by
    filter_upwards [ae_circleAvg_eq_wn hW hh hae 0 one_pos,
      hW.add_ae (Real.sqrt Real.pi • hatMeasKerL2 σ₀) (Real.sqrt Real.pi • ∫ u, largeKerL2 u ∂σ₀),
      hW.smul_ae (Real.sqrt Real.pi) (hatMeasKerL2 σ₀),
      hW.smul_ae (Real.sqrt Real.pi) (∫ u, largeKerL2 u ∂σ₀)] with ω h1 h2 h3 h4
    rw [h1, hg₀, h2, h3, h4]
  obtain ⟨Y, hYc, hYm, hYW, hT⟩ := exists_box_modification_tail hW
    (fun _ => (Real.sqrt Real.pi)⁻¹ • g₀) hb (L := 0) le_rfl fun x _ c _ => by simp
  refine ⟨Y, hYc, hYm, hT, fun z r hr hB => ?_⟩
  filter_upwards [ae_integral_box_modification hW continuous_const hYc hYm hYW hr hB,
    hW.smul_ae (Real.sqrt Real.pi)⁻¹ g₀, hc] with ω h1 h2 h3
  rw [h1, h3, integral_const, probReal_univ, one_smul, h2]
  field_simp

end Pairs

end DG
end LQGMetric
