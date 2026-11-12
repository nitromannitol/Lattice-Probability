/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17V4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2HatTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiSupTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17 at `𝕍`-scale, part 4: the `m³` term and the smooth window (P2-DG317V)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), proof of Prop 3.17, Step 1
(DG:1541–1555), D121. Two estimates for the transport of Step 1 from `𝕍` to `𝕊`:
* `p17v_cub`: at `ε = δ^{(2+γ)²}` and level `m = m_δ + 1`, the cubic term `(m+1)³` of the
  `𝕍`-scale target of Lemma 3.13 is dominated by its second term (the hypothesis `hcub` of
  `p17v_lemma313`): the second term is `≥ 2^{-3(2+γ)²/d} 2^{(2+γ+γ²/2) n/d}`, `n = m + 1`;
* `p17v_window`: the smooth window `φ_{1,2}[W]` of `ĥ_δ[W'] ∘ T = ĥ_{2δ}[W] + φ_{1,2}[W]`
  (`ae_phiVer_p17vW`) is `< ζ log δ⁻¹` on `[0,1]²` w.p. `≥ 1 − Cδ` (Gaussian sup tail,
  `DZZ.dzz_hat_sup_tail`, as in `dgLem37V_l37W`).
Own elementary estimates (DV-DG317V-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Asymptotics
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

/-- **the `m³` term is dominated** at `ε = δ^{(2+γ)²}`, `m = m_δ + 1` -/
lemma p17v_cub {γ d η : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d) (hη : 0 < η) (hη1 : η < 1) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → δ < 1 →
      (((Blueprint.dgM δ + 1 + 1 : ℕ)) : ℝ) ^ 3 ≤ (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
        (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * ((Blueprint.dgM δ + 1 : ℕ) : ℝ) / d)) *
          Real.exp (γ / d * (-(3 * (((Blueprint.dgM δ + 1 + 1 : ℕ) : ℝ) * Real.log 2)))) := by
  have hd0 : 0 < d := by linarith
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set B := (2 + γ) ^ 2 with hB
  set e := 2 + γ + γ ^ 2 / 2 with he
  have he0 : 0 < e := by positivity
  set b := e * Real.log 2 / d with hb
  have hb0 : 0 < b := by positivity
  set c := Real.exp (-(3 * B * Real.log 2 / d)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((_root_.isLittleO_pow_exp_pos_mul_atTop 3 hb0).bound hc0)
  set N' := max N 0
  refine ⟨Real.exp (-(N' * Real.log 2)), Real.exp_pos _, fun δ hδ hδ₁ hδ1 => ?_⟩
  set M := Blueprint.dgM δ
  obtain ⟨-, -, hM3, hM4⟩ := p17s_dgM hδ hδ1
  set L := Real.log δ⁻¹ with hL
  have hlogb : Real.logb 2 δ⁻¹ = L / Real.log 2 := rfl
  have hLN : N' * Real.log 2 < L := by
    rw [hL, Real.log_inv, lt_neg]
    have := Real.log_lt_log hδ hδ₁
    rwa [Real.log_exp] at this
  have hMN : N ≤ (M : ℝ) + 2 := by
    have : N' < Real.logb 2 δ⁻¹ := by rw [hlogb, lt_div_iff₀ hl2]; exact hLN
    linarith [le_max_left N 0]
  have hLM : ((M : ℝ) - 1) * Real.log 2 ≤ L := by
    have : (M : ℝ) - 1 < L / Real.log 2 := by rw [← hlogb]; linarith
    rw [lt_div_iff₀ hl2] at this; linarith
  set n : ℝ := (M : ℝ) + 2 with hn
  have hn0 : 0 ≤ n := by positivity
  have hcast2 : (((M + 1 + 1 : ℕ)) : ℝ) = n := by push_cast; ring
  have hcast1 : (((M + 1 : ℕ)) : ℝ) = n - 1 := by push_cast; ring
  rw [hcast2, hcast1]
  -- the cubic bound from the little-o
  have hcub : n ^ 3 ≤ c * Real.exp (b * n) := by
    have := hN n hMN
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.exp_pos _).le] at this
  refine hcub.trans ?_
  -- the three factors
  have hδB : 0 < δ ^ B := Real.rpow_pos_of_pos hδ _
  have hδB1 : δ ^ B ≤ 1 := Real.rpow_le_one hδ.le hδ1.le (by positivity)
  have hdη : 0 < d - η := by linarith
  have hX1 : Real.exp (B / d * L) ≤ (δ ^ B) ^ (-(1 / (d - η))) := by
    have e1 : (δ ^ B) ^ (-(1 / d)) = Real.exp (B / d * L) := by
      rw [← Real.rpow_mul hδ.le, p17s_exp_log hδ]; ring_nf
    rw [← e1]
    refine Real.rpow_le_rpow_of_exponent_ge hδB hδB1 ?_
    rw [neg_le_neg_iff]
    exact one_div_le_one_div_of_le hdη (by linarith)
  have hX2 : Real.exp (-(2 + γ ^ 2 / 2) * n * Real.log 2 / d) ≤
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * (n - 1) / d)) := by
    rw [Real.rpow_def_of_pos two_pos]
    refine Real.exp_le_exp.2 ?_
    have h1 : (2 + γ ^ 2 / 2 - η) * (n - 1) ≤ (2 + γ ^ 2 / 2) * n := by nlinarith
    have : Real.log 2 * (-((2 + γ ^ 2 / 2 - η) * (n - 1) / d)) =
        -(Real.log 2 * ((2 + γ ^ 2 / 2 - η) * (n - 1))) / d := by ring
    rw [this, show -(2 + γ ^ 2 / 2) * n * Real.log 2 / d =
      -(Real.log 2 * ((2 + γ ^ 2 / 2) * n)) / d by ring]
    exact div_le_div_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left h1 hl2.le)) hd0.le
  have hX1' : Real.exp (B / d * ((n - 3) * Real.log 2)) ≤ Real.exp (B / d * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by rw [hn]; linarith) (by positivity))
  calc c * Real.exp (b * n)
      = Real.exp (B / d * ((n - 3) * Real.log 2)) *
          Real.exp (-(2 + γ ^ 2 / 2) * n * Real.log 2 / d) *
          Real.exp (γ / d * (-(3 * (n * Real.log 2)))) := by
        rw [hc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [hb, he, hB]; field_simp; ring
    _ ≤ (δ ^ B) ^ (-(1 / (d - η))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * (n - 1) / d)) *
          Real.exp (γ / d * (-(3 * (n * Real.log 2)))) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hX1'.trans hX1) hX2 (Real.exp_pos _).le
          (Real.rpow_nonneg hδB.le _)) (Real.exp_pos _).le

/-- `|f(x)| ≤ sup_{[0,1]²} |f|` for continuous `f` -/
lemma p17v_abs_le_iSup {f : ℂ → ℝ} (hf : Continuous f) {x : ℂ}
    (hx : x ∈ Blueprint.closedUnitSquare) :
    |f x| ≤ ⨆ v : SupTail.ferniqueBox 0 1, |f v| := by
  have hx' : x ∈ SupTail.ferniqueBox 0 1 := by
    obtain ⟨h1, h2, h3, h4⟩ := hx
    simp only [SupTail.ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.zero_re,
      Complex.zero_im, zero_add]
    exact ⟨⟨h1, h2⟩, h3, h4⟩
  exact le_ciSup (f := fun v : SupTail.ferniqueBox 0 1 => |f v|)
    (SupTail.bddAbove_abs_of_compact (SupTail.isCompact_ferniqueBox _ _) hf) ⟨x, hx'⟩

/-- **the smooth window** `φ_{1,2}[W]` is `< ζ log δ⁻¹` on `[0,1]²` w.p. `≥ 1 − Cδ` -/
lemma p17v_window {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ζ * Real.log δ⁻¹ ≤ ⨆ v : SupTail.ferniqueBox 0 1, |DDDF.phiVer W P 1 2 v ω|} ≤
        ENNReal.ofReal (C * δ ^ (1 : ℝ)) := by
  have hP := hW.isProbabilityMeasure
  have hB := DDDF.isPhiVersion_phiVer (P := P) hW one_pos (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨C, hC, eT⟩ := DZZ.dzz_hat_sup_tail hW one_pos (by norm_num : (1 : ℝ) ≤ 2)
    (x₀ := 0) (s := 1) one_pos hB.cont hB.ae_eq
  refine ⟨C, min (1 / 2) (Real.exp (-(C / ζ ^ 2))), lt_min (by norm_num) (Real.exp_pos _),
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδδ⟩ := hδ
  have hδ2 : δ < 1 / 2 := hδδ.trans_le (min_le_left _ _)
  have hδe : δ < Real.exp (-(C / ζ ^ 2)) := hδδ.trans_le (min_le_right _ _)
  have hL0 : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv₀ hδ0 |>.2 (by linarith))
  rw [Real.rpow_one, ← ofReal_measureReal (measure_ne_top P _)]
  refine ENNReal.ofReal_le_ofReal ((eT _ (by positivity)).trans ?_)
  gcongr
  have hlog : C / ζ ^ 2 ≤ Real.log δ⁻¹ := by
    rw [Real.log_inv, le_neg]
    exact ((Real.log_lt_log hδ0 hδe).trans_eq (Real.log_exp _)).le
  calc Real.exp (-(ζ * Real.log δ⁻¹) ^ 2 / C) ≤ Real.exp (-Real.log δ⁻¹) := by
        gcongr
        rw [div_le_iff₀ hC]
        have hζ2 : 0 < ζ ^ 2 := by positivity
        rw [div_le_iff₀ hζ2] at hlog
        nlinarith [mul_le_mul_of_nonneg_left hlog hL0]
    _ = δ := by rw [Real.exp_neg, Real.exp_log (inv_pos.2 hδ0), inv_inv]

end DG
end LQGMetric
