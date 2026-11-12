/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim6A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim5

/-!
# P-317K-SIM, part 6A: one scale of DZZ's P3.17 proof through the coupling

DZZ's proof of Proposition 3.17 (l. 1526–1530) combines (Eq.boundDprime)/P3.2 with the
concentration of `log D'`; through the similarity coupling (lem-scaling-coupling,
l. 611–624) and the walled Corollary 3.9 (l. 1235–1244) it gives, at one target scale `δ`
(`wsim_step`): outside an event of probability `≤ p`,
`|log D^{θB̄₀}_δ(A, B) − E log D^{θB̄₀}_δ(A, B)| ≤ 2w + 2 L₂^{0.9} + log F + 4`
whenever the four exceptional probabilities sum to `≤ p ≤ 1/4` and `M² p ≤ 1`
(`E X² ≤ M²`). `wsim_scale`: the deterministic facts on `δ₁ = δe^{λ}/α`, `δ₂ = δe^{−λ}/α`,
`λ = (log δ⁻¹)^{0.6}`. Own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **One target scale.** -/
theorem wsim_step {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ} {W₁ W₂ : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW₁ : IsWhiteNoise P' W₁) (hW₂ : IsWhiteNoise P' W₂) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {a b : ℂ} (ha : a ≠ 0) {C lam : ℝ}
    (hcpl : P'.real {ω | ¬ ∀ x ∈ wsimB₀.closedBox, ∀ y ∈ wsimB₀.closedBox, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ x y ∧
          lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ x y ≤
            lgdDZZ (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp (-lam)) (simMap a b x) (simMap a b y)} ≤
        C * Real.exp (-lam ^ 2 / C))
    {S : Set DyBox} {ξ : ℝ} (hξ : 0 < ξ) {A B : Set ℂ}
    (hA : simMap a b ⁻¹' A ⊆ kXi wsimB₀.closedBox ξ)
    (hB : simMap a b ⁻¹' B ⊆ kXi wsimB₀.closedBox ξ)
    (hAne : (simMap a b ⁻¹' A).Nonempty) (hBne : (simMap a b ⁻¹' B).Nonempty)
    {δ δ₁ δ₂ : ℝ} (hδ : 0 < δ) (e₁ : δ * Real.exp lam / ‖a‖ = δ₁)
    (e₂ : δ * Real.exp (-lam) / ‖a‖ = δ₂) (hδ₂ : δ₂ ∈ Ioo (0 : ℝ) 1) (hδ₂₁ : δ₂ ≤ δ₁)
    (hδ₁ : δ₁ ≤ 1) {w T₂ T₃ T₄ p M Wd : ℝ}
    (h2 : P' (prop32EventOn S γ W₁ (fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ₂
      (simMap a b ⁻¹' A) (simMap a b ⁻¹' B))ᶜ ≤ ENNReal.ofReal T₂)
    (h3 : P' {ω | |logApproxLGDOn S γ W₁ δ₂ (simMap a b ⁻¹' A) (simMap a b ⁻¹' B) ω -
      ∫ ω', logApproxLGDOn S γ W₁ δ₂ (simMap a b ⁻¹' A) (simMap a b ⁻¹' B) ω' ∂P'| ≤ w}ᶜ ≤
        ENNReal.ofReal T₃)
    (h4 : P' (cor39Event (fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W₁ ω)) δ₁ δ₂
      (simMap a b ⁻¹' A) (simMap a b ⁻¹' B))ᶜ ≤ ENNReal.ofReal T₄)
    (hT2 : 0 ≤ T₂) (hT3 : 0 ≤ T₃) (hT4 : 0 ≤ T₄) (hC : 0 ≤ C * Real.exp (-lam ^ 2 / C))
    (hT : C * Real.exp (-lam ^ 2 / C) + T₂ + T₃ + T₄ ≤ p) (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (hM : 0 < M) (hMp : M ^ 2 * p ≤ 1)
    (hXm : MemLp (fun ω => logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox)
      (dzzMuIn γ W ω)) δ A B) 2 P)
    (hXM : ∫ ω, logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ A B ^ 2
      ∂P ≤ M ^ 2)
    (hWd : 2 * w + 2 * Real.log δ₂⁻¹ ^ (0.9 : ℝ) + Real.log (cor39Fac δ₁ δ₂) + 4 ≤ Wd) :
    P {ω | ¬ |logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω)) δ A B -
      ∫ ω', logMinLGD (dzzWall (simMap a b '' wsimB₀.closedBox) (dzzMuIn γ W ω')) δ A B ∂P| ≤
        Wd} ≤ ENNReal.ofReal p := by
  have := hW.isProbabilityMeasure
  subst e₁ e₂
  set K₀ := wsimB₀.closedBox
  set A₀ := simMap a b ⁻¹' A
  set B₀ := simMap a b ⁻¹' B
  obtain ⟨x, hx⟩ := hAne
  obtain ⟨y, hy⟩ := hBne
  have hfin := ae_lgdMinSet_wall_lt_top (P := P') hW₁ hγ hγ2 (convex_closedBox wsimB₀)
    (isClosed_closedBox wsimB₀).measurableSet wsimB₀_subset_openSquare hδ₂.1 hx hy
    (kXi_sub_interior hξ (hA hx)) (kXi_sub_interior hξ (hB hy))
  have hF := one_le_cor39Fac hδ₂.1 hδ₂₁ hδ₁
  have hw := wsim_window_target (S := S) hW hW₂ hγ hγ2 ha hcpl
    (hA.trans (wsim_kXi_subset hξ)) (hB.trans (wsim_kXi_subset hξ)) hδ hfin hδ₂ hF
    (∫ ω', logApproxLGDOn S γ W₁ (δ * Real.exp (-lam) / ‖a‖) A₀ B₀ ω' ∂P') w
  rw [wsim_image_preimage ha, wsim_image_preimage ha] at hw
  set X := fun ω => logMinLGD (dzzWall (simMap a b '' K₀) (dzzMuIn γ W ω)) δ A B
  set lo := (∫ ω', logApproxLGDOn S γ W₁ (δ * Real.exp (-lam) / ‖a‖) A₀ B₀ ω' ∂P') - w -
    Real.log (δ * Real.exp (-lam) / ‖a‖)⁻¹ ^ (0.9 : ℝ) -
    Real.log (cor39Fac (δ * Real.exp lam / ‖a‖) (δ * Real.exp (-lam) / ‖a‖))
  set hi := (∫ ω', logApproxLGDOn S γ W₁ (δ * Real.exp (-lam) / ‖a‖) A₀ B₀ ω' ∂P') + w +
    Real.log (δ * Real.exp (-lam) / ‖a‖)⁻¹ ^ (0.9 : ℝ)
  have hG : P {ω | ¬ (lo ≤ X ω ∧ X ω ≤ hi)} ≤ ENNReal.ofReal p := by
    refine hw.trans ?_
    refine (add_le_add (add_le_add (add_le_add le_rfl h2) h3) h4).trans ?_
    rw [← ENNReal.ofReal_add hC hT2, ← ENNReal.ofReal_add (by positivity) hT3,
      ← ENNReal.ofReal_add (by positivity) hT4]
    exact ENNReal.ofReal_le_ofReal hT
  have hsq : M * Real.sqrt p ≤ 1 := by
    have e : (M * Real.sqrt p) ^ 2 = M ^ 2 * p := by rw [mul_pow, Real.sq_sqrt hp.le]
    have h0 : 0 ≤ M * Real.sqrt p := by positivity
    nlinarith
  refine (measure_mono fun ω hω => ?_).trans hG
  simp only [mem_ofPred_eq] at hω ⊢
  intro hb
  apply hω
  have := wsim_abs_sub_integral_le (X := X) (fun ω => logMinLGD_nonneg _ _ _ _) hXm hM hXM hp
    hp4 hG hb.1 hb.2
  have hhl : hi - lo = 2 * w + 2 * Real.log (δ * Real.exp (-lam) / ‖a‖)⁻¹ ^ (0.9 : ℝ) +
      Real.log (cor39Fac (δ * Real.exp lam / ‖a‖) (δ * Real.exp (-lam) / ‖a‖)) := by
    simp only [hi, lo]; ring
  linarith

/-- **The deterministic scale facts** for `L = log δ⁻¹` in the range of `wsim_ev_basic`. -/
lemma wsim_scale {α ξ δ D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 4)
    (hD : 0 ≤ D) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hL : 1 ≤ Real.log δ⁻¹ ∧ D ≤ Real.log δ⁻¹ / 2 ∧ 0 < Real.log δ⁻¹ ^ (0.6 : ℝ) ∧
      Real.log δ⁻¹ ^ (0.6 : ℝ) ≤ Real.log δ⁻¹ / 4 ∧
      Real.log δ⁻¹ / 2 ≤ Real.log δ⁻¹ - Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α ∧
      Real.log δ⁻¹ - Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α <
        Real.log δ⁻¹ + Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α ∧
      Real.log δ⁻¹ + Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α ≤ 2 * Real.log δ⁻¹) :
    Real.log (δ * Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) / α)⁻¹ =
        Real.log δ⁻¹ - Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α ∧
      Real.log (δ * Real.exp (-(Real.log δ⁻¹ ^ (0.6 : ℝ))) / α)⁻¹ =
        Real.log δ⁻¹ + Real.log δ⁻¹ ^ (0.6 : ℝ) + Real.log α ∧
      0 < δ * Real.exp (-(Real.log δ⁻¹ ^ (0.6 : ℝ))) / α ∧
      δ * Real.exp (-(Real.log δ⁻¹ ^ (0.6 : ℝ))) / α <
        δ * Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) / α ∧
      δ * Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) / α ≤ Real.exp (-D) ∧
      (δ * Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ)) / α) ^ (2 * ξ) ≤ δ ^ ξ / α := by
  obtain ⟨hL1, hDL, hl0, hl4, h1, h12, h2⟩ := hL
  set L := Real.log δ⁻¹ with hLd
  set l := L ^ (0.6 : ℝ)
  have hlα : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1
  have e1 := wsim_log_inv_scale (μ := l) hδ.1 hα
  have e2 := wsim_log_inv_scale (μ := -l) hδ.1 hα
  rw [sub_neg_eq_add] at e2
  have p1 : 0 < δ * Real.exp l / α := by have := hδ.1; positivity
  refine ⟨e1, e2, by have := hδ.1; positivity, ?_, ?_, ?_⟩
  · rw [div_lt_div_iff_of_pos_right hα]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 (by linarith)) hδ.1
  · have : δ * Real.exp l / α = Real.exp (-Real.log (δ * Real.exp l / α)⁻¹) := by
      rw [Real.log_inv, neg_neg, Real.exp_log p1]
    rw [this, e1]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [rpow_eq_exp_log_inv p1, e1, rpow_eq_exp_log_inv hδ.1, ← hLd,
      ← Real.exp_log hα, ← Real.exp_sub, Real.exp_log hα]
    refine Real.exp_le_exp.2 ?_
    have k1 : 0 ≤ (1 - 2 * ξ) * (-Real.log α) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ ξ * (L - 2 * l) := mul_nonneg hξ.le (by linarith)
    nlinarith

end DZZ
end LQGMetric
