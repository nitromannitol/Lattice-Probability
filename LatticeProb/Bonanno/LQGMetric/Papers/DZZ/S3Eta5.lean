/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta4

/-!
# DZZ (eq-LQG-negative-moment) for the η-chaos `M̃_{γ,δ,η}` (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 684–688): for `B` of diameter `ξ` and `δ ≤ ξ`,
`E (ξ^{-2} M̃(B))^p ≤ C_{γ,p}` for `p < 0`. DZZ state it for `M̃_{γ,δ}`; their use in the proof of
Prop. 3.2 (l. 1202, "`1 − β C_{γ,−1}`") is for `M̃_{γ,ε²s',η}`, for which it follows by the same
argument (Kahane, with the η-band covariance below the `h̃`-band covariance, `S3Eta4`):

* **`lintegral_etaChaos_rpow_le_of_neg`**: `p < 0`, `U ⊇ B(x, ξ)` of finite measure, `δ ≤ ξ`:
  `E (ξ^{-2} M̃_{γ,δ,η}(U))^p ≤ C` with `C` depending only on `γ, p`. Route as
  `GMCIdent6.lintegral_tildeM_rpow_le_of_neg`: the square `a + L[0,1)²` (`L = 3ξ/8`) inside the
  ball, `lintegral_square_etaDens_rpow_le`, and Fatou along the a.s. convergent approximations
  (`ae_tendsto_etaApprox`).
* **`measure_etaChaos_le_le`**: `P(ξ^{-2} M̃_{γ,δ,η}(U) ≤ β) ≤ β C_{γ,−1}` (Markov for the `−1`-st
  moment; the bound on `P(𝒜_j^c)` in DZZ l. 1202).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 GMCIdent6 DGMC QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

attribute [local irreducible] etaDensR etaDens etaApprox etaChaos in
/-- **DZZ (eq-LQG-negative-moment) for `M̃_{γ,δ,η}`** -/
theorem lintegral_etaChaos_rpow_le_of_neg (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {p : ℝ} (hp : p < 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (δ : ℝ) (x : ℂ) (ξ : ℝ) (U : Set ℂ), 0 < δ → MeasurableSet U →
      volume U ≠ ⊤ → ball x ξ ⊆ U → δ ≤ ξ →
      ∫⁻ ω, ((ENNReal.ofReal ξ ^ 2)⁻¹ * etaChaos W γ δ U ω) ^ p ∂P ≤ C := by
  obtain ⟨Ω₀, _, P₀, X, _, hX⟩ := exists_zeroGFF_openSquare
  obtain ⟨c, hZ⟩ := logCorr_midZ hX γ
  have hβ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨C₀, hC₀⟩ := hZ.exists_uniform_neg_moment (by positivity) hβ4 hp
  set B := ENNReal.ofReal (Real.exp (p * (p - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀)
  set κ : ℝ≥0∞ := ENNReal.ofReal ((3 / 8 : ℝ) ^ 2)
  have hκ0 : κ ≠ 0 := by simp [κ]
  have hκt : κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκp : κ ^ p ≠ ⊤ := by
    rw [Ne, ENNReal.rpow_eq_top_iff]; simp [hκ0, hκt]
  refine ⟨κ ^ p * B, ENNReal.mul_ne_top hκp ENNReal.ofReal_ne_top,
    fun δ x ξ U hδ hU hUf hBU hδξ => ?_⟩
  have hP := hW.isProbabilityMeasure
  have hξ0 : 0 < ξ := hδ.trans_le hδξ
  set L : ℝ := 3 / 8 * ξ
  have hL : 0 < L := by positivity
  set a : ℂ := x - ⟨L / 2, L / 2⟩
  have hδL : δ ≤ 4 * L := by simp only [L]; linarith
  set S : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ y in cell0, ENNReal.ofReal (etaDensR W γ δ n (a + (L : ℂ) * y) ω)
  set c₀ : ℝ≥0∞ := (ENNReal.ofReal ξ ^ 2)⁻¹
  have hc0 : c₀ ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hξ0).ne')
  have hcκ : c₀ * ENNReal.ofReal (L ^ 2) = κ := ofReal_sq_eq hξ0 (3 / 8) (by norm_num)
  have hQU : ∀ y ∈ cell0, a + (L : ℂ) * y ∈ U := fun y hy => hBU (by
    rw [mem_ball, dist_eq_norm]
    exact (norm_le_of_mem_cell0 hL hy).trans_lt (by simp only [L]; linarith))
  have hSle : ∀ n ω, ENNReal.ofReal (L ^ 2) * S n ω ≤ etaApprox W γ δ n U ω := fun n ω => by
    have h := square_le_setLIntegral (fun z => etaDens W γ δ n z ω)
      ((measurable_etaDens hW γ δ n).comp (measurable_id.prodMk measurable_const)) hU a hL hQU
    simp only [etaDens_eq_ofReal] at h
    rw [etaApprox]
    simpa only [etaDens_eq_ofReal] using h
  have hcont : Continuous fun y : ℝ≥0∞ => (c₀ * y) ^ p :=
    ENNReal.continuous_rpow_const.comp (ENNReal.continuous_const_mul hc0)
  have hlim : ∀ᵐ ω ∂P, (c₀ * etaChaos W γ δ U ω) ^ p ≤
      liminf (fun n => (κ * S n ω) ^ p) atTop := by
    filter_upwards [ae_tendsto_etaApprox hW γ δ hU hUf] with ω ht
    have ht' := (hcont.tendsto _).comp ht
    rw [← ht'.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    simp only [Function.comp]
    rw [← hcκ, mul_assoc]
    exact Neg3.ennrpow_anti hp.le (by gcongr; exact hSle n ω)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : ℝ)⁻¹ ^ N ≤ δ := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (show (2 : ℝ)⁻¹ < 1 by norm_num)
    exact ⟨N, hN.le⟩
  have hmS : ∀ n, Measurable (S n) := fun n =>
    (ENNReal.measurable_ofReal.comp ((measurable_etaDensR hW γ δ n).comp
      ((measurable_const.add (measurable_const.mul measurable_snd)).prodMk
        measurable_fst))).lintegral_prod_right'
  calc ∫⁻ ω, (c₀ * etaChaos W γ δ U ω) ^ p ∂P
      ≤ ∫⁻ ω, liminf (fun n => (κ * S n ω) ^ p) atTop ∂P := lintegral_mono_ae hlim
    _ ≤ liminf (fun n => ∫⁻ ω, (κ * S n ω) ^ p ∂P) atTop :=
        lintegral_liminf_le fun n => ((hmS n).const_mul _).pow_const _
    _ ≤ _ := by
        refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (2 : ℝ)⁻¹ ^ n ≤ δ :=
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN
        simp_rw [mul_rpow_of_pos_ne_top hκ0 hκt]
        rw [lintegral_const_mul _ ((hmS n).pow_const _)]
        gcongr
        exact lintegral_square_etaDens_rpow_le hW γ hZ (Or.inl hp) (fun j => hC₀ j j le_rfl)
          δ hn' a hL hδL

/-- **the bound on `P(𝒜_j^c)`** (DZZ l. 1202): `P(ξ^{-2} M̃_{γ,δ,η}(U) ≤ β) ≤ β C_{γ,−1}` -/
theorem measure_etaChaos_le_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (δ : ℝ) (x : ℂ) (ξ : ℝ) (U : Set ℂ), 0 < δ → MeasurableSet U →
      volume U ≠ ⊤ → ball x ξ ⊆ U → δ ≤ ξ → ∀ β : ℝ≥0∞, β ≠ 0 → β ≠ ⊤ →
      P {ω | (ENNReal.ofReal ξ ^ 2)⁻¹ * etaChaos W γ δ U ω ≤ β} ≤ β * C := by
  obtain ⟨C, hC, hmom⟩ := lintegral_etaChaos_rpow_le_of_neg hW hγ hγ2 (p := -1) (by norm_num)
  refine ⟨C, hC, fun δ x ξ U hδ hU hUf hBU hδξ β hβ0 hβt => ?_⟩
  set c₀ : ℝ≥0∞ := (ENNReal.ofReal ξ ^ 2)⁻¹
  have hm : Measurable fun ω => (c₀ * etaChaos W γ δ U ω) ^ (-1 : ℝ) :=
    ((measurable_etaChaos hW γ δ U).const_mul _).pow_const _
  have hsub : {ω | c₀ * etaChaos W γ δ U ω ≤ β} ⊆
      {ω | β⁻¹ ≤ (c₀ * etaChaos W γ δ U ω) ^ (-1 : ℝ)} := fun ω hω => by
    simp only [mem_ofPred_eq, ENNReal.rpow_neg_one] at hω ⊢
    exact ENNReal.inv_le_inv.2 hω
  calc P {ω | c₀ * etaChaos W γ δ U ω ≤ β}
      ≤ P {ω | β⁻¹ ≤ (c₀ * etaChaos W γ δ U ω) ^ (-1 : ℝ)} := measure_mono hsub
    _ ≤ (∫⁻ ω, (c₀ * etaChaos W γ δ U ω) ^ (-1 : ℝ) ∂P) / β⁻¹ :=
        meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.inv_ne_zero.2 hβt)
          (ENNReal.inv_ne_top.2 hβ0)
    _ ≤ C / β⁻¹ := by gcongr; exact hmom δ x ξ U hδ hU hUf hBU hδξ
    _ = β * C := by rw [div_eq_mul_inv, inv_inv, mul_comm]

end DZZ
end LQGMetric
