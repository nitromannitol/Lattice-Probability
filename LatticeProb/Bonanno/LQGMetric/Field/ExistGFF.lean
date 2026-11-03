/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistGFF at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2
import LatticeProb.Bonanno.LQGMetric.Field.ExistCov
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Existence of the whole-plane GFF in `𝒟'(ℂ)` (task P2-EXIST; non-vacuity obligation N1)

`exists_wholePlaneGFF`: on `(ℕ → ℝ, stdP)` there is a whole-plane GFF `h : Ω → 𝒟'(ℂ)`
(`IsWholePlaneGFF`), and `exists_normalizedWPGFF` (= `GM.ExistsNormalizedGFF`, blueprint M1 §5):
a normalized one (`h_1(0) = 0` a.s.).

Construction: the space-time white noise `W` of `Field/WhiteNoise` (isonormal process on
`L²(ℝ × ℂ)`, QZ `gs_process_hilbert`); the antiderivative field `F(x) = W(kerFun 1_{[0,x]})` with
`kerFun g (t, y) = √π 1_{t>0} ∫ g(u)(p_{t/2}(u, y) − 1_{t>1} p_{t/2}(0, y)) du` — the
heat-kernel/white-noise representation of the GFF (Ding–Dubédat–Dunlap–Falconet,
arXiv:1904.08021, `tightness.tex` l. 143–145, (2.2)) integrated over rectangles; a continuous
version `Y` of `F` (Kolmogorov–Čentsov); and `⟨h, φ⟩ := ∫ Y ∂_re ∂_im φ`, a continuous linear
functional of `φ` for every `ω` (`gffOf`). Then `⟨h, φ⟩ = W(kerFun φ)` a.s. (stochastic Fubini),
so the pairings are jointly Gaussian and centred, with covariance
`⟪kerFun φ, kerFun ψ⟫ = π ∫_0^∞ ∫∫ φ(u)ψ(v) p_t(u,v) = logCov φ ψ` for mean-zero `φ, ψ`
(Frullani: LQGDimension `heatRep_of_integrable_log`). Normalization: subtract `h_1(0)` as a
random constant (`IsWholePlaneGFF.addConst`, P2-FCIRC `ae_circleAvg_addConst_one_zero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace LQGMetric
namespace GFFExist

open WhiteNoise

lemma BddSupp.mono {g : ℂ → ℝ} {M R R' : ℝ} (h : BddSupp g M R) (hR : R ≤ R') :
    BddSupp g M R' :=
  ⟨h.meas, h.bdd, fun u hu => h.supp u (hR.trans_lt hu)⟩

lemma inner_testL2_testL2 (φ ψ : TestC) (hφ0 : ∫ u, φ u = 0) (hψ0 : ∫ u, ψ u = 0) :
    ⟪testL2 φ, testL2 ψ⟫ = logCov φ ψ := by
  rw [inner_testL2_eq]
  have e : ∫ q, kerFun φ q * (testL2 ψ : ℝ × ℂ → ℝ) q = ∫ q, kerFun φ q * kerFun ψ q := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_kerFun_test ψ).coeFn_toLp] with q h
    rw [testL2, h]
  rw [e]
  obtain ⟨M, R, hR, hφ⟩ := testC_bddSupp φ
  obtain ⟨N, R', hR', hψ⟩ := testC_bddSupp ψ
  exact integral_kerFun_mul_eq_logCov (le_max_of_le_left hR) (hφ.mono (le_max_left R R'))
    (hψ.mono (le_max_right R R')) hφ0 hψ0

/-- **Existence of the whole-plane GFF** as a random distribution. -/
theorem exists_wholePlaneGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → DistC),
      IsProbabilityMeasure P ∧ IsWholePlaneGFF h P := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hP := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_rectField hW
  refine ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, gffOf Y hYc, hP, ?_⟩
  have hae : ∀ φ : TestC, (fun ω => gffOf Y hYc ω φ) =ᵐ[LQGDimension.ExistAsm.stdP]
      W (testL2 φ) := fun φ => by
    simpa only [gffOf_apply] using ae_integral_d12_mul_eq hW hYc hYm hYW φ
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

/-- **Existence of a normalized whole-plane GFF** (`GM.ExistsNormalizedGFF`, N1). -/
theorem exists_normalizedWPGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistC), IsNormalizedWPGFF h P := by
  obtain ⟨Ω, _, P, h, hP, hh⟩ := exists_wholePlaneGFF
  have hc : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  refine ⟨Ω, inferInstance, P, hP, fun ω => addConst (h ω) (-circleAvg (h ω) 1 0),
    hh.addConst hc, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
  rw [hω, add_neg_cancel]

end GFFExist
end LQGMetric
