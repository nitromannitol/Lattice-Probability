/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta1

/-!
# DZZ's η-chaos `M̃_{γ,δ,η}`: mean, Markov bound, finite-range independence (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`):

* **`lintegral_etaApprox`**: `E ∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var} dz = Leb(B)` (Fubini, Gaussian
  mgf), and **`lintegral_etaChaos_le`**: `E M̃_{γ,δ,η}(B) ≤ Leb(B)` (Fatou). DZZ l. 1122 state
  `E M̃_{γ,ε²s,η}(B̃) = (ts)²` "by Fubini"; only `≤` is used there (Markov, (Eq.LQG-tildeM)).
* **`measure_etaChaos_ge_le`**: the Markov bound (Eq.LQG-tildeM), l. 1123–1125.
* **`iIndepFun_etaChaos`**: `M̃_{γ,δ,η}(B_i)` are mutually independent when the `(R+ρ)`-thickenings
  of the `B_i` are pairwise disjoint (`r ≤ R` on `(0, δ²)`): DZZ l. 1197–1198 ("Since
  `ε² s' log(1/(ε² s')) < ε s'`, … mutually independent"), finite range of `η` (l. 449).
* `etaRad_le_bandHalf`: `r(u) ≤ (δ log δ⁻¹ + δ)/2` on `(0, δ²)`, `δ ≤ 1` (the range bound behind
  DZZ's `ε² s' log(1/(ε² s'))`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `E e^{γ η^δ_{2^{-n}}(z) − γ²/2 Var η^δ_{2^{-n}}(z)} = 1` -/
lemma lintegral_etaDens (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) (z : ℂ) :
    ∫⁻ ω, etaDens W γ δ n z ω ∂P = 1 := by
  have hP := hW.isProbabilityMeasure
  set V := etaBVar δ n z
  set K := etaKernelL2 (etaBand δ n) z
  have hint := (integrable_exp_wn hW (γ * Real.sqrt Real.pi) K).mul_const
    (Real.exp (-(γ ^ 2 / 2 * V)))
  have hae : (fun ω => Real.exp (γ * etaVer W δ n z ω - γ ^ 2 / 2 * V)) =ᵐ[P]
      fun ω => Real.exp (γ * Real.sqrt Real.pi * W K ω) * Real.exp (-(γ ^ 2 / 2 * V)) := by
    filter_upwards [etaVer_ae_eq hW δ n z] with ω h
    rw [h, ← Real.exp_add, sub_eq_add_neg, etaField, mul_assoc]
  simp only [etaDens]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_congr hae).2 hint)
    (Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_congr_ae hae,
    integral_mul_const, integral_exp_wn hW, ← Real.exp_add]
  have : (γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖K‖ ^ 2 + -(γ ^ 2 / 2 * V) = 0 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; simp only [V, etaBVar, K]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one]

/-- **`E ∫_B e^{γ η^δ_{2^{-n}} − γ²/2 Var} dz = Leb(B)`** -/
theorem lintegral_etaApprox (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) {B : Set ℂ}
    (hB : MeasurableSet B) : ∫⁻ ω, etaApprox W γ δ n B ω ∂P = volume B := by
  have hP := hW.isProbabilityMeasure
  simp only [etaApprox]
  have hm : AEMeasurable (Function.uncurry fun ω z => etaDens W γ δ n z ω)
      (P.prod (volume.restrict B)) :=
    ((measurable_etaDens hW γ δ n).comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hm, ← setLIntegral_one]
  refine setLIntegral_congr_fun hB fun z _ => lintegral_etaDens hW γ δ n z

/-- **`E M̃_{γ,δ,η}(B) ≤ Leb(B)`** (Fatou) -/
theorem lintegral_etaChaos_le (hW : IsWhiteNoise P W) (γ δ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) : ∫⁻ ω, etaChaos W γ δ B ω ∂P ≤ volume B := by
  refine (lintegral_liminf_le fun n => measurable_etaApprox hW γ δ n B).trans ?_
  simp only [lintegral_etaApprox hW γ δ _ hB, liminf_const, le_refl]

/-- **DZZ (Eq.LQG-tildeM)**: `P(M̃_{γ,δ,η}(B) ≥ t) ≤ Leb(B)/t` -/
theorem measure_etaChaos_ge_le (hW : IsWhiteNoise P W) (γ δ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) {t : ℝ≥0∞} (ht0 : t ≠ 0) (htt : t ≠ ∞) :
    P {ω | t ≤ etaChaos W γ δ B ω} ≤ volume B / t :=
  (meas_ge_le_lintegral_div (measurable_etaChaos hW γ δ B).aemeasurable ht0 htt).trans
    (ENNReal.div_le_div_right (lintegral_etaChaos_le hW γ δ hB) t)

/-- **finite-range independence of `M̃_{γ,δ,η}`** (DZZ l. 1197–1198) -/
theorem iIndepFun_etaChaos (hW : IsWhiteNoise P W) {δ R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) {ι : Type}
    {B : ι → Set ℂ} (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (thickening (R + ρ) (B i)) (thickening (R + ρ) (B j))) :
    iIndepFun (fun i => etaChaos W γ δ (B i)) P := by
  have h := hW.iIndepFun_of_pairwise_disjoint (A := fun i => etaReg R ρ (B i))
    fun i j hij => Set.disjoint_prod.2 (Or.inr (hdisj hij))
  rw [iIndepFun_iff_iIndep] at h ⊢
  exact iIndep_of_iIndep_of_le h fun i => (measurable_etaChaos_loc hW hR hρ γ (hB i)).comap_le

/-- the range of the band `(0, δ²)`: `r(u) ≤ (δ log δ⁻¹ + δ)/2` -/
lemma etaRad_le_bandHalf {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ (δ * Real.log δ⁻¹ + δ) / 2 := by
  intro u hu
  have h := etaRad_le_of_le hu.1 hu.2.le (pow_le_one₀ hδ.le hδ1)
  rw [Real.sqrt_sq hδ.le, ← inv_pow, Real.log_pow] at h
  refine h.trans (le_of_eq ?_)
  push_cast; ring

end DZZ
end LQGMetric
