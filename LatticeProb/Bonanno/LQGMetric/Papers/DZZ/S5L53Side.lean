/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Side at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53CrudeP

/-!
# Side hypotheses of `dzzLem53Exp_of_subadd` at `μ = dzzMuIn γ W` (P2-DZZ53)

For a white noise `W`, `0 < γ < 2` and `ν = dzzWall 𝕍̃_{u,v} μIn` (the tilde distance of DZZ
l. 2265–2270):

* `ae_lgd_tilde_lt_top` (`hfin`): a.s. `D̃_δ(u,v) < ∞` (from `ae_wickQArea_reg`,
  `lgdDZZ_lt_top_of_convex` on `B((u+v)/2, |u−v|)`, as in `dzzL53Whp_dzzMuIn_of_upper`);
* `chiDy_tilde_le` (`hM`, DZZ (eq-very-crude), l. 856, 2411): `χ_{2^{-k}} ≤ M` uniformly;
* `integrable_log_tilde` (`hint`): from the crude bound once `ω ↦ M^W(B(c,r))` is
  a.e.-measurable (hypothesis `hmeas`; DZZ treat measurability implicitly);
* `dzzLem53Exp_dzzMuIn_of_subadd`: DZZ Lemma 5.3 at `μIn` from part 1 (`hsub`), part 3
  (`hindep`) and `hmeas` only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`hfin`**: a.s. `D̃_δ(u,v) < ∞` -/
theorem ae_lgd_tilde_lt_top (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v < ⊤ := by
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  have hBS := ball_mid_subset_openSquare hu hv
  have hw : ∀ K ⊆ Metric.ball ((u + v) / 2) ‖v - u‖,
      dzzWall (tildeBox u v) (dzzMuIn γ W ω) K = wickQArea γ W ω K := fun K hKB =>
    dzzWall_tilde_eq hu hv hKB
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
  have hum : u ∈ Metric.ball ((u + v) / 2) ‖v - u‖ := by
    rw [Metric.mem_ball, dist_eq_norm, show u - (u + v) / 2 = -((v - u) / 2) by ring, norm_neg,
      norm_div]
    simp only [Complex.norm_ofNat]; linarith
  have hvm : v ∈ Metric.ball ((u + v) / 2) ‖v - u‖ := by
    rw [Metric.mem_ball, dist_eq_norm, show v - (u + v) / 2 = (v - u) / 2 by ring, norm_div]
    simp only [Complex.norm_ofNat]; linarith
  exact lgdDZZ_lt_top_of_convex Metric.isOpen_ball (convex_ball _ _)
    (fun K hKc hKB => by rw [hw K hKB]; exact hK K hKc (hKB.trans hBS))
    (fun x hx => by rw [hw {x} (singleton_subset_iff.mpr hx)]; exact hat x (hBS hx))
    hδ hum hvm

lemma integral_le_toReal_lintegral {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    ∫ ω, f ω ∂P ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal := by
  by_cases hi : Integrable f P
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hi.aestronglyMeasurable]
  · rw [integral_undef hi]; exact ENNReal.toReal_nonneg

/-- **`hM`** (DZZ (eq-very-crude) for `D̃`): `χ_{2^{-k}}(u,v) ≤ M` for all `k` and all
`u ≠ v ∈ 𝕍̄` -/
theorem chiDy_tilde_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ M : ℝ, ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ k : ℕ,
      chiDy P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v k ≤ M := by
  obtain ⟨A, B, hA, hB, h⟩ := lintegral_log_tilde_le (P := P) hW hγ hγ2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨A / Real.log 2 + B, fun u hu v hv huv k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [chiDy, Nat.cast_zero, zero_mul, div_zero]; positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hδ0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hδ2 : (2 : ℝ)⁻¹ ^ k ≤ 1 / 2 := by
    rw [one_div]; exact pow_le_of_le_one (by norm_num) (by norm_num) hk.ne'
  have hL : Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ = k * Real.log 2 := by
    rw [inv_pow, inv_inv, Real.log_pow]
  have hI := (integral_le_toReal_lintegral (P := P) fun ω => logMinLGD_nonneg _ _ _ _).trans
    (ENNReal.toReal_le_of_le_ofReal (by rw [hL]; positivity) (h u hu v hv huv _ hδ0 hδ2))
  rw [hL] at hI
  have hkl : 0 < (k : ℝ) * Real.log 2 := by positivity
  simp only [chiDy]
  rw [div_le_iff₀ hkl]
  have e : A / Real.log 2 * (k * Real.log 2) = A * k := by field_simp
  have : A ≤ A * k := by nlinarith
  nlinarith

/-- **`hint`**: `log D̃_δ(u,v)` is integrable, given a.e.-measurable `M^W`-ball masses -/
theorem integrable_log_tilde (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hmeas : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => wickQArea γ W ω (ball c r)) P)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ω => logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}) P := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨A, B, hA, hB, h⟩ := lintegral_log_tilde_le (P := P) hW hγ hγ2
  have hbm : ∀ (c : ℂ) (r : ℝ), AEMeasurable
      (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω) (ball c r)) P := fun c r => by
    simp only [dzzWall, dzzMuIn, Measure.add_apply, Measure.smul_apply]
    exact ((hmeas c r).add aemeasurable_const).add aemeasurable_const
  have hm : AEStronglyMeasurable
      (fun ω => logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}) P := by
    simp only [logMinLGD_singleton]
    exact (measurable_log_toNat.comp_aemeasurable
      (aemeasurable_lgdDZZ hbm δ u v)).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => logMinLGD_nonneg _ _ _ _)]
  set δ' := min δ (1 / 2)
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := A + B * Real.log δ'⁻¹))
  refine le_trans ?_ (h u hu v hv huv δ' hδ' (min_le_right _ _))
  refine lintegral_mono_ae ?_
  filter_upwards [ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ'] with ω hω
  exact ENNReal.ofReal_le_ofReal
    (logMinLGD_singleton_anti _ hδ'.le (min_le_left _ _) u v hω)

/-- **DZZ Lemma 5.3 at `μIn`** from its part 1 (`hsub`, DZZ l. 2306–2420), part 3 (`hindep`,
l. 2423) and the measurability of `ω ↦ M^W(B(c,r))`; the crude bound, finiteness and
integrability are discharged above. -/
theorem dzzLem53Exp_dzzMuIn_of_subadd (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hmeas : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => wickQArea γ W ω (ball c r)) P)
    (hsub : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Subadd P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v 0.01)
    (hindep : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ u' ∈ dzzVbar, ∀ v' ∈ dzzVbar, u' ≠ v' →
      Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u' v') (dzzMuIn γ W ω)) δ {u'} {v'}
        ∂P) / Real.log δ⁻¹ - (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}
        ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 0)) :
    ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ := by
  obtain ⟨M, hM⟩ := chiDy_tilde_le (P := P) hW hγ hγ2
  exact dzzLem53Exp_of_subadd (by norm_num) (by norm_num) hsub hM
    (fun u hu v hv huv δ hδ => ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ)
    (fun u hu v hv huv δ hδ => integrable_log_tilde hW hγ hγ2 hmeas hu hv huv hδ) hindep

end DZZ
end LQGMetric
