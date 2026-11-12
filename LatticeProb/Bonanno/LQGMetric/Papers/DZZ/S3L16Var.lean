/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L16Var at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Main

/-!
# DZZ Lemma 3.16 (eq-B-good): band variance and Chernoff tail (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.16, (eq-for-B'-good), l. 1408–1412:
a Gaussian union bound for the band field `η^{εs/log s⁻¹}_{ε* s}` at the centres of `𝓑(B, ε*)`.

* `etaBandVar_le`: `Var η^{e₂}_{e₁}(w) ≤ log(e₂/e₁)` (as `etaVar_le`: killed heat kernel `≤ (2πs)⁻¹`);
* `measureReal_bandNorm_ge_le`: Chernoff for the normalized band exponent: for `λ ≥ 1` and
  `Var ≤ V`, `P(γη − γ²/2 Var ≥ a) ≤ exp(λ(λ−1) γ² V / 2 − λ a)` (exponential Markov with the Gaussian
  mgf; DZZ only say "by a union bound"; this is the standard Gaussian tail, written so that the unknown
  exact variance enters only through its upper bound `V`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat

/-- `Var η^{e₂}_{e₁}(w) ≤ log(e₂/e₁)` for `0 < e₁ ≤ e₂`. -/
theorem etaBandVar_le {e₁ e₂ : ℝ} (he₁ : 0 < e₁) (he : e₁ ≤ e₂) (v : ℂ) :
    etaBandVar e₁ e₂ v ≤ Real.log (e₂ / e₁) := by
  have h1 : 0 < e₁ ^ 2 := by positivity
  have h12 : e₁ ^ 2 ≤ e₂ ^ 2 := by gcongr
  set f : ℝ → ℝ := fun s => killedHeat (openSquare ∩ Metric.ball v (etaRad s)) s.toNNReal v v
    with hf
  have hI0 : Ioo (e₁ ^ 2) (e₂ ^ 2) ⊆ Ioi (e₁ ^ 2) := Ioo_subset_Ioi_self
  have nv : ∫ p, etaKernel (Ioo (e₁ ^ 2) (e₂ ^ 2)) v p * etaKernel (Ioo (e₁ ^ 2) (e₂ ^ 2)) v p =
      ∫ s in Ioo (e₁ ^ 2) (e₂ ^ 2), f s := by
    simpa [sq] using integral_sq_eq_of_lintegral (measurable_etaKernel measurableSet_Ioo v)
      (etaKernel_nonneg _ _) (measurable_killedHeat_eta_time v)
      (fun s => killedHeat_nonneg _ _ _ _)
      (lintegral_etaKernel_sq measurableSet_Ioo (hI0.trans (Ioi_subset_Ioi h1.le)) v)
  have hfi : IntegrableOn f (Ioo (e₁ ^ 2) (e₂ ^ 2)) := integrableOn_killedHeat_eta h1 hI0 v
  have hinv : IntegrableOn (fun s : ℝ => (2 * Real.pi)⁻¹ * s⁻¹) (Ioc (e₁ ^ 2) (e₂ ^ 2)) :=
    (((continuousOn_inv₀.mono fun x hx => mem_compl_singleton_iff.mpr
      (ne_of_gt (h1.trans_le hx.1))).integrableOn_Icc).mono_set Ioc_subset_Icc_self).const_mul _
  have hb : ∫ s in Ioo (e₁ ^ 2) (e₂ ^ 2), f s ≤ Real.log (e₂ / e₁) / Real.pi := by
    rw [integral_Ioc_eq_integral_Ioo.symm]
    calc ∫ s in Ioc (e₁ ^ 2) (e₂ ^ 2), f s ≤ ∫ s in Ioc (e₁ ^ 2) (e₂ ^ 2), (2 * Real.pi)⁻¹ * s⁻¹ := by
          refine setIntegral_mono_on (hfi.congr_set_ae Ioo_ae_eq_Ioc.symm) hinv measurableSet_Ioc
            fun s hs => ?_
          have hs0 : 0 < s := h1.trans hs.1
          refine (killedHeat_le_heatKernel _ _ _ _).trans ?_
          refine (heatKernel_le_inv _ (NNReal.coe_nonneg _) v v).trans (le_of_eq ?_)
          rw [Real.coe_toNNReal _ hs0.le, mul_inv]
      _ = Real.log (e₂ / e₁) / Real.pi := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le h12,
            integral_inv_of_pos h1 (h1.trans_le h12), ← div_pow, Real.log_pow]
          have := Real.pi_pos
          field_simp
          push_cast
          ring
  have hpi := Real.pi_pos
  rw [etaBandVar, ← real_inner_self_eq_norm_sq,
    inner_etaKernelL2 measurableSet_Ioo h1 hI0 v v, nv]
  calc Real.pi * ∫ s in Ioo (e₁ ^ 2) (e₂ ^ 2), f s ≤ Real.pi * (Real.log (e₂ / e₁) / Real.pi) :=
        mul_le_mul_of_nonneg_left hb hpi.le
    _ = Real.log (e₂ / e₁) := by field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- Chernoff bound for the normalized band exponent. -/
theorem measureReal_bandNorm_ge_le (hW : IsWhiteNoise P W) (γ : ℝ) (bt : DyBox) (N : ℕ)
    {V lam a : ℝ} (hV : etaBandVar bt.side ((2 : ℝ)⁻¹ ^ N) bt.center ≤ V) (hlam : 1 ≤ lam) :
    P.real {ω | a ≤ bandNorm γ W bt N ω} ≤
      Real.exp (lam * (lam - 1) * γ ^ 2 * V / 2 - lam * a) := by
  have := hW.isProbabilityMeasure
  set v := etaBandVar bt.side ((2 : ℝ)⁻¹ ^ N) bt.center
  have hv0 : 0 ≤ v := etaBandVar_nonneg _ _ _
  set X := eta W bt.side ((2 : ℝ)⁻¹ ^ N) bt.center
  have hX := hasLaw_eta hW bt.side ((2 : ℝ)⁻¹ ^ N) bt.center
  have hint : Integrable (fun ω => Real.exp (lam * (γ * X ω))) P :=
    (hX.integrable_comp (f := fun x => Real.exp (lam * γ * x))
      (integrable_exp_mul_gaussianReal _)).congr (ae_of_all _ fun ω => by
        show Real.exp (lam * γ * X ω) = Real.exp (lam * (γ * X ω)); rw [mul_assoc])
  have hmgf : mgf (fun ω => γ * X ω) P lam = Real.exp ((lam * γ) ^ 2 * v / 2) := by
    rw [mgf_const_mul, mgf_gaussianReal hX, Real.coe_toNNReal _ hv0]; ring_nf
  have hset : {ω | a ≤ bandNorm γ W bt N ω} = {ω | a + γ ^ 2 / 2 * v ≤ γ * X ω} := by
    ext ω
    change a ≤ γ * X ω - γ ^ 2 / 2 * v ↔ a + γ ^ 2 / 2 * v ≤ γ * X ω
    constructor <;> intro h <;> linarith
  rw [hset]
  refine (measure_ge_le_exp_mul_mgf (a + γ ^ 2 / 2 * v) (by linarith) hint).trans ?_
  rw [hmgf, ← Real.exp_add, Real.exp_le_exp]
  have : 0 ≤ lam * (lam - 1) * γ ^ 2 := by
    have : 0 ≤ lam - 1 := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hV this]

end DZZ
end LQGMetric
