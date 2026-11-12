/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldGrad at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseC1Var
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
# Gaussian tail of the gradient of `φ_{a,b}` on one small square (task P2-DDDFFIELD)

Ingredients of DDDF Prop. 3 (arXiv:1904.08021, `tightness.tex` l. 329–345), whose (2.16) is
proved in DF (arXiv:1809.02607, l. 1828–1840): "By Fernique's theorem, we have a tail estimate
for the gradient [...] by scaling [...] by union bound". Here:

* `tail_sup_abs_square`: Fernique (DZZ Lemma 2.3, `SupTail.dzz_lemma23_continuous`) plus
  Borell–TIS (`SupTail.tail_iSup_abs_le_gaussian`) on one square of side `b`;
* `integral_sq_of_hasLaw`, `integral_dphi`: second moments and centring of `D_e = √π W(q)`;
* `ae_fderiv_eq_of_modification`: any two `C¹` modifications of `φ_{a,b}` have a.s. the same
  gradient everywhere (continuous modifications are indistinguishable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Fernique + Borell–TIS on a square**: a centred continuous Gaussian field on the square
`Q = ferniqueBox x₀ b` with `E (G_v − G_u)² ≤ |u − v|/b` on `Q` and `Var G ≤ σ²` satisfies
`P(sup_Q |G| ≥ y) ≤ 2 e^{C_F²/(2σ²)} e^{−y²/(4σ²)}`. -/
theorem tail_sup_abs_square {G : ℂ → Ω → ℝ} (hG : IsGaussianProcess G P)
    (h0 : ∀ z, ∫ ω, G z ω ∂P = 0) (hc : ∀ ω, Continuous fun z => G z ω) {b : ℝ} (hb : 0 < b)
    (x₀ : ℂ) (hinc : ∀ u ∈ ferniqueBox x₀ b, ∀ v ∈ ferniqueBox x₀ b,
      ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ ‖u - v‖ / b) {σ : ℝ} (hvar : ∀ z, Var[G z; P] ≤ σ ^ 2)
    {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ ⨆ z : ferniqueBox x₀ b, |G z ω|} ≤
      2 * Real.exp (ferniqueCF ^ 2 / (2 * σ ^ 2)) * Real.exp (-y ^ 2 / (2 * (2 * σ ^ 2))) := by
  set Q := ferniqueBox x₀ b
  have : CompactSpace Q := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox x₀ b)
  have : Nonempty Q := ⟨⟨x₀, mem_ferniqueBox_self hb.le⟩⟩
  have hGQ : IsGaussianProcess (fun v : Q => G v) P := hG.comp_right Subtype.val
  have hGQ' : IsGaussianProcess (fun v : Q => fun ω => -G v ω) P :=
    (isGaussianProcess_neg hG).comp_right Subtype.val
  have h1 := dzz_lemma23_continuous hb hGQ (G := G) (fun v _ => h0 v) hinc
    (fun ω => (hc ω).continuousOn)
  have h2 := dzz_lemma23_continuous hb (G := fun z ω => -G z ω) hGQ'
    (fun v _ => by simp [integral_neg, h0]) (fun u hu v hv => by
      have := hinc u hu v hv
      refine le_trans (le_of_eq ?_) this
      congr 1; funext ω; ring) (fun ω => (hc ω).neg.continuousOn)
  exact tail_iSup_abs_le_gaussian (T := Q) (X := fun v : Q => G v) hGQ (fun v => h0 v)
    (fun ω => (hc ω).comp continuous_subtype_val) h1.1 h2.1 h1.2 h2.2 (fun v => hvar v) hy

/-- `E U² = v` for `U ~ N(0, v)`. -/
lemma integral_sq_of_hasLaw {U : Ω → ℝ} {v : NNReal} (h : HasLaw U (gaussianReal 0 v) P) :
    ∫ ω, U ω ^ 2 ∂P = v := by
  have hv := h.variance_eq
  rw [variance_id_gaussianReal, variance_of_integral_eq_zero h.aemeasurable
    (by rw [h.integral_eq, integral_id_gaussianReal])] at hv
  exact hv

variable {W : WNSpace → Ω → ℝ}

lemma hasLaw_dphi (hW : IsWhiteNoise P W) (a b : ℝ) (e x : ℂ) (h : ℝ) :
    HasLaw (dphi W a b e x h)
      (gaussianReal 0 (Real.pi * ‖dqKernelL2 a b e x h‖ ^ 2).toNNReal) P := by
  have hl := hW.hasLaw ![dqKernelL2 a b e x h] ![Real.sqrt Real.pi]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_zero,
    Finset.sum_singleton] at hl
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt Real.pi_pos.le] at hl
  exact hl.congr (Eventually.of_forall fun ω => rfl)

lemma integral_dphi (hW : IsWhiteNoise P W) (a b : ℝ) (e x : ℂ) (h : ℝ) :
    ∫ ω, dphi W a b e x h ω ∂P = 0 := by
  rw [(hasLaw_dphi hW a b e x h).integral_eq, integral_id_gaussianReal]

lemma variance_dphi (hW : IsWhiteNoise P W) (a b : ℝ) (e x : ℂ) (h : ℝ) :
    Var[dphi W a b e x h; P] = Real.pi * ‖dqKernelL2 a b e x h‖ ^ 2 := by
  rw [(hasLaw_dphi hW a b e x h).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity)]

lemma integral_sq_dphi_sub (hW : IsWhiteNoise P W) (a b : ℝ) (e x x' : ℂ) (h h' : ℝ) :
    ∫ ω, (dphi W a b e x h ω - dphi W a b e x' h' ω) ^ 2 ∂P =
      Real.pi * ‖dqKernelL2 a b e x h - dqKernelL2 a b e x' h'‖ ^ 2 := by
  rw [integral_sq_of_hasLaw (hasLaw_dphi_sub hW a b e x x' h h'),
    Real.coe_toNNReal _ (by positivity)]

/-- Two continuous modifications are indistinguishable. -/
lemma ae_eq_of_continuous_modification {Y₁ Y₂ : ℂ → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous fun x => Y₁ x ω) (hc₂ : ∀ ω, Continuous fun x => Y₂ x ω)
    (h : ∀ x, Y₁ x =ᵐ[P] Y₂ x) : ∀ᵐ ω ∂P, ∀ x, Y₁ x ω = Y₂ x ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ x : D, Y₁ x ω = Y₂ x ω := ae_all_iff.mpr fun x => h x
  filter_upwards [hD] with ω hω
  intro x
  exact congrFun (Continuous.ext_on hDd (hc₁ ω) (hc₂ ω) fun y hy => hω ⟨y, hy⟩) x

/-- **Gradients of `C¹` modifications agree a.s. everywhere.** -/
lemma ae_fderiv_eq_of_modification {Y₁ Y₂ : ℂ → Ω → ℝ}
    (hc₁ : ∀ ω, Continuous fun x => Y₁ x ω) (hc₂ : ∀ ω, Continuous fun x => Y₂ x ω)
    (h : ∀ x, Y₁ x =ᵐ[P] Y₂ x) :
    ∀ᵐ ω ∂P, ∀ x, fderiv ℝ (fun x => Y₁ x ω) x = fderiv ℝ (fun x => Y₂ x ω) x := by
  filter_upwards [ae_eq_of_continuous_modification hc₁ hc₂ h] with ω hω
  intro x
  have : (fun x => Y₁ x ω) = fun x => Y₂ x ω := funext hω
  rw [this]

end DDDF
end LQGMetric
