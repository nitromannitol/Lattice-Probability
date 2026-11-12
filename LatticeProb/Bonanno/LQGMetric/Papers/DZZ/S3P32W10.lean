/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W9

/-!
# D97, packet P-1: the approximations of `M^W` form a martingale

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 680–682 and (eq-def-M-eta)): the approximations
"form a sequence of martingales (c.f. [RV14])". For the white-noise filtration
`𝓖_m = wnFil hW m` (noise on the scales `> 4^{-m}`), `m ≤ n` and a Borel set `E`:

* `wnDens_ae_eq_mul`: `wnDens_n(z) = wnDens_m(z) · fineDens_{m,n}(z)` a.s. (the band field
  `h̃^{2^{-m}}_{2^{-n}}` is independent of `𝓖_m`, `GMCIdent5`);
* **`setLIntegral_wickMeas_eq`**: `E[1_A wickMeas_n(E)] = E[1_A wickMeas_m(E)]` for `A ∈ 𝓖_m`
  (Tonelli, independence, `E fineDens = 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 GMCIdent5

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma wnDens_ae_eq_mul (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    (fun ω => wnDens W γ n z ω) =ᵐ[P'] fun ω => wnDens W γ m z ω * fineDens W γ m n z ω := by
  filter_upwards [bandDens_eq_fineDens_ae hW γ hmn z, tildeVer_ae_eq hW m z,
    (coarseVer_spec hW m).2.2 z] with ω h1 h2 h3
  have hc : cDens hW γ m z ω = wnDens W γ m z ω := by rw [cDens, wnDens, h2, h3]
  have hne : wnDens W γ m z ω ≠ 0 := by rw [← hc]; exact (cDens_pos hW γ m z ω).ne'
  rw [← h1, hc]; field_simp

lemma measurable_wnDens_fil (hW : IsWhiteNoise P' W) (γ : ℝ) (m : ℕ) (z : ℂ) :
    Measurable[wnFil hW m] fun ω => wnDens W γ m z ω := by
  have hm := measurable_tildeVer hW m
  let _ : MeasurableSpace Ω' := wnFil hW m
  exact measurable_const.mul (Real.measurable_exp.comp
    ((hm.comp measurable_prodMk_left).const_mul γ))

lemma measurable_fineDens_z_compl (hW : IsWhiteNoise P' W) (γ : ℝ) (m n : ℕ) (z : ℂ) :
    Measurable[wnSigma W (coarseSet m)ᶜ] fun ω => fineDens W γ m n z ω := by
  exact (measurable_fineDens hW γ m n).of_uncurry_left (x := z)

lemma measurable_wnDens_uncurry (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) :
    Measurable fun p : Ω' × ℂ => ENNReal.ofReal (wickR γ p.2 * wnDens W γ n p.2 p.1) :=
  ENNReal.measurable_ofReal.comp (((measurable_wickR γ).comp measurable_snd).mul
    (((measurable_wnWeight hW γ n).comp measurable_snd).mul (Real.measurable_exp.comp
      (((measurable_tildeVer' hW n).comp measurable_swap).const_mul γ))))

/-- **Martingale identity** for the approximations of `M^W`. -/
theorem setLIntegral_wickMeas_eq (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n)
    {A : Set Ω'} (hA : MeasurableSet[wnFil hW m] A) {E : Set ℂ} (hE : MeasurableSet E) :
    ∫⁻ ω in A, wickMeas W γ n ω E ∂P' = ∫⁻ ω in A, wickMeas W γ m ω E ∂P' := by
  have hP := hW.isProbabilityMeasure
  have hA' : MeasurableSet A := wnSigma_le hW _ A hA
  simp_rw [wickMeas, withDensity_apply _ hE]
  rw [lintegral_lintegral_swap (measurable_wnDens_uncurry hW γ n).aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap (measurable_wnDens_uncurry hW γ m).aemeasurable]
  refine setLIntegral_congr_fun hE fun z _ => ?_
  simp_rw [ENNReal.ofReal_mul (wickR_pos γ z).le]
  rw [lintegral_const_mul (f := fun ω => ENNReal.ofReal (wnDens W γ n z ω)) _
      (ENNReal.measurable_ofReal.comp
        ((measurable_wnDens_fil hW γ n z).mono (wnSigma_le hW _) le_rfl)),
    lintegral_const_mul (f := fun ω => ENNReal.ofReal (wnDens W γ m z ω)) _
      (ENNReal.measurable_ofReal.comp
        ((measurable_wnDens_fil hW γ m z).mono (wnSigma_le hW _) le_rfl))]
  congr 1
  rw [← lintegral_indicator hA', ← lintegral_indicator hA']
  have hf : Measurable[wnSigma W (coarseSet m)]
      (A.indicator fun ω => ENNReal.ofReal (wnDens W γ m z ω)) :=
    (ENNReal.measurable_ofReal.comp (measurable_wnDens_fil hW γ m z)).indicator hA
  have hg : Measurable[wnSigma W (coarseSet m)ᶜ]
      fun ω => ENNReal.ofReal (fineDens W γ m n z ω) :=
    ENNReal.measurable_ofReal.comp (measurable_fineDens_z_compl hW γ m n z)
  have hae : (A.indicator fun ω => ENNReal.ofReal (wnDens W γ n z ω)) =ᵐ[P']
      fun ω => A.indicator (fun ω => ENNReal.ofReal (wnDens W γ m z ω)) ω *
        ENNReal.ofReal (fineDens W γ m n z ω) := by
    filter_upwards [wnDens_ae_eq_mul hW γ hmn z] with ω h
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω]
      rw [h, ENNReal.ofReal_mul (wnDens_nonneg γ m z ω)]
    · simp only [indicator_of_notMem hω, zero_mul]
  rw [lintegral_congr_ae hae, lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (wnSigma_le hW _) (wnSigma_le hW _) (indep_wnSigma_compl hW (coarseSet m)).symm hf hg,
    lintegral_fineDens hW γ hmn z, mul_one]

end DZZ
end LQGMetric
