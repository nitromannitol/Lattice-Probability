/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L37V1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18D
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldGrad
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Lemma 3.7 at `𝕍`-scale, part 1: the white noise rescaled by `T(z) = (z + 1 + i)/3`

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), D105 item 1 (DEC-105 §1): DG's
squares are carried to `𝕍` by `T(z) = (z + 1 + i)/3`, `T⁻¹ y = 3y − (1 + i)` (`p18Tinv`). With the
white-noise scaling isometry `U_{3,−(1+i)}` (`wnScale`, S3D105Sc1, D105 item 3) and
`W' := W ∘ U_{3,−(1+i)}`:

* `wnScale_phiKernelL2`: `U_{δ,b} k_{a,c,x} = k_{δa,δc,δx+b}` (Brownian scaling of the heat
  kernel, `heatKernel_affineC`), hence pathwise `φ_{δ,1}[W'](y) = φ_{3δ,3}[W](T⁻¹ y)`;
* `ae_phiVer_wnScaleT`: a.s. for all `y`,
  `phiVer W' P δ 1 y = phiVer W P (3δ) 1 (T⁻¹ y) + phiVer W P 1 3 (T⁻¹ y)` (`3δ ≤ 1`): the
  continuous versions agree since they are modifications of each other (`phi_add_ae`,
  `ae_eq_of_continuous_modification`).

This is the standard scale covariance of the white noise (DG:1010 "basic properties of `ĥ`");
own elementary glue (DV-D105-2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DG

open WhiteNoise

/-- `δ⁻² k_{a,c,x}(δ⁻² s, δ⁻¹(w − b)) = k_{δa,δc,δx+b}(s, w)` -/
lemma scFun_phiKernel {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (a c : ℝ) (x : ℂ) :
    scFun δ b (phiKernel a c x) = phiKernel (δ * a) (δ * c) (affineC δ b x) := by
  funext p
  obtain ⟨s, w⟩ := p
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hmem : ((δ ^ 2)⁻¹ * s ∈ Icc (a ^ 2) (c ^ 2)) ↔ s ∈ Icc ((δ * a) ^ 2) ((δ * c) ^ 2) := by
    simp only [mem_Icc, mul_pow]
    rw [le_inv_mul_iff₀ hδ2, inv_mul_le_iff₀ hδ2]
  have hw : affineC δ b ((δ⁻¹ : ℝ) • (w - b)) = w := by
    have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
    simp only [affineC, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ hδc, one_mul, sub_add_cancel]
  simp only [scFun, scMap, phiKernel, indicator, mem_prod, mem_univ, and_true]
  by_cases hs : s ∈ Icc ((δ * a) ^ 2) ((δ * c) ^ 2)
  · rw [if_pos (hmem.2 hs), if_pos hs]
    have h := heatKernel_affineC hδ b ((δ ^ 2)⁻¹ * s / 2) x ((δ⁻¹ : ℝ) • (w - b))
    rw [hw, show δ ^ 2 * ((δ ^ 2)⁻¹ * s / 2) = s / 2 by field_simp] at h
    rw [h]
  · rw [if_neg (fun h => hs (hmem.1 h)), if_neg hs, mul_zero]

/-- **Scaling of DDDF's kernel**: `U_{δ,b} k_{a,c,x} = k_{δa,δc,δx+b}` in `L²` -/
theorem wnScale_phiKernelL2 {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {a : ℝ} (ha : 0 < a) (c : ℝ) (x : ℂ) :
    wnScale hδ b (phiKernelL2 a c x) = phiKernelL2 (δ * a) (δ * c) (affineC δ b x) := by
  rw [phiKernelL2, dite_eq_left_of_eq_true (eq_true ha), wnScale_toLp, phiKernelL2,
    dite_eq_left_of_eq_true (eq_true (mul_pos hδ ha))]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => by rw [scFun_phiKernel hδ b])

/-- `b₀ = −(1 + i)`, so that `affineC 3 b₀ = T⁻¹` -/
def l37b0 : ℂ := -(1 + Complex.I)

lemma affineC_three_l37b0 (y : ℂ) : affineC 3 l37b0 y = p18Tinv y := rfl

lemma continuous_p18Tinv : Continuous p18Tinv := continuous_affineC 3 l37b0

/-- the white noise at `𝕍`-scale: `W' = W ∘ U_{3,−(1+i)}` -/
def l37W {Ω : Type*} (W : WNSpace → Ω → ℝ) : WNSpace → Ω → ℝ :=
  fun f ω => W (wnScale (by norm_num : (0 : ℝ) < 3) l37b0 f) ω

theorem isWhiteNoise_l37W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) : IsWhiteNoise P (l37W W) :=
  isWhiteNoise_comp hW _

/-- pathwise: `φ_{a,c}[W'](y) = φ_{3a,3c}[W](T⁻¹ y)` -/
lemma phi_l37W {Ω : Type*} (W : WNSpace → Ω → ℝ) {a : ℝ} (ha : 0 < a) (c : ℝ) (y : ℂ) (ω : Ω) :
    phi (l37W W) a c y ω = phi W (3 * a) (3 * c) (p18Tinv y) ω := by
  simp only [phi, l37W, wnScale_phiKernelL2 _ l37b0 ha, affineC_three_l37b0]

/-- **`φ_δ` of the rescaled white noise** (`0 < δ ≤ 1/3`): a.s., for all `y`,
`φ_δ[W'](y) = φ_{3δ}[W](T⁻¹ y) + φ_{1,3}[W](T⁻¹ y)` (continuous versions). -/
theorem ae_phiVer_l37W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ3 : 3 * δ ≤ 1) :
    ∀ᵐ ω ∂P, ∀ y, DDDF.phiVer (l37W W) P δ 1 y ω =
      DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω + DDDF.phiVer W P 1 3 (p18Tinv y) ω := by
  have h3 : (0 : ℝ) < 3 * δ := by positivity
  have hY := DDDF.isPhiVersion_phiVer (b := 1) (isWhiteNoise_l37W hW) hδ (by linarith)
  have hA := DDDF.isPhiVersion_phiVer hW h3 hδ3
  have hB := DDDF.isPhiVersion_phiVer (P := P) hW one_pos (by norm_num : (1 : ℝ) ≤ 3)
  refine DDDF.ae_eq_of_continuous_modification hY.cont
    (Y₂ := fun y ω => DDDF.phiVer W P (3 * δ) 1 (p18Tinv y) ω +
      DDDF.phiVer W P 1 3 (p18Tinv y) ω)
    (fun ω => ((hA.cont ω).comp continuous_p18Tinv).add ((hB.cont ω).comp continuous_p18Tinv))
    fun y => ?_
  filter_upwards [hY.ae_eq y, hA.ae_eq (p18Tinv y), hB.ae_eq (p18Tinv y),
    phi_add_ae hW h3 hδ3 (by norm_num : (1 : ℝ) ≤ 3) (p18Tinv y)] with ω h1 h2 h3' h4
  rw [h1, phi_l37W W hδ 1 y ω, mul_one, h4, h2, h3']

end DG
end LQGMetric
