/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6XiQ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1F
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc

/-!
# DDDF: `1 − ξQ ≤ 2ξ` and Prop 28 Part 2 Step 1 without `α ≥ 1` (task P2-DDDFW)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1478–1481: "We recall that `α > ξQ + 2ξ`, and in
particular `α > 1`: indeed, `1 − ξQ ≤ 2ξ` follows from a comparison with the infimum of the
field."

Formalized as in DDDF: the comparison `L^{(n)}_{1,1} ≥ e^{ξ inf_{[0,1]²} φ_{0,n}}`
(`le_lowerMedian_lenObs`, DDDF.S2.c) together with the sup tail (2.11) of `φ_{0,n}`
(`S6P28.phiVer_sup_tail_unif`, `P(sup|φ_{0,n}| ≥ C + 2(n+1) log 2 + 1) ≤ e^{-2} < 1/2`) gives
`λ_n ≥ e^{-ξ(C + 2(n+1) log 2 + 1)}` (`lambdaN_ge_inf_field`); the upper bound
`λ_n ≤ 2^{-n(1 − ξQ − ζ)}` ((5.78) = DDDF `eq:DGupperQuantile`, l. 1276–1281, which DDDF also
uses at l. 1478 in the form of Prop 26) then forces `1 − ξQ − ζ ≤ 2ξ` for every `ζ > 0`
(`one_sub_mul_le_of_578`). Hence `ξ(Q + 2) < α` implies `1 < α`, and `s6_lowerStep1'` is
`S6P28L.s6_lowerStep1` without the hypothesis `1 ≤ α`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6XiQ

open WhiteNoise SupTail S6P28

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **comparison with the infimum of the field** (DDDF l. 1480): for `n ≥ 1`,
`λ_n ≥ e^{-ξ (C_F √6 + 2(n+1) log 2 + 1)}`. -/
theorem lambdaN_ge_inf_field (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(ξ * (ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + 1)))) ≤
      lambdaN ξ W P n := by
  have hP := hW.isProbabilityMeasure
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n with hδ_def
  set M := ferniqueCF * Real.sqrt 6 + (2 * (n + 1) * Real.log 2 + 1) with hM_def
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδ3 : δ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hY : phiMN W P 0 n = phiVer W P δ 1 := by simp [phiMN, hδ_def]
  have hφ := isPhiVersion_phiVer hW hδ0 hδ1
  have hδa : ((2 : ℝ) ^ n)⁻¹ ≤ 2 * δ := by
    have : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
    rw [hδ_def, inv_pow]; linarith
  have hδb : δ ≤ ((2 : ℝ) ^ n)⁻¹ := by rw [hδ_def, inv_pow]
  have htail := phiVer_sup_tail_unif hW n hδa hδb hδ3 (m := 1) zero_le_one
  have hM : P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M} < 2⁻¹ := by
    have hsub : {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M} ⊆
        {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := by
      intro ω hω
      simp only [not_forall, not_le, mem_ofPred_eq] at hω ⊢
      obtain ⟨x, hx, hlt⟩ := hω
      have hbdd : BddAbove (range fun v : ferniqueBox 0 1 => |phiVer W P δ 1 v ω|) := by
        have := (isCompact_ferniqueBox 0 1).bddAbove_image
          (continuous_abs.comp (hφ.cont ω)).continuousOn
        rwa [Set.image_eq_range] at this
      exact hlt.le.trans (le_ciSup hbdd ⟨x, S6DG.unit_subset_fernique hx⟩)
    have he : Real.exp (-(2 * 1)) < 2⁻¹ := by
      have h3 := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
      rw [Real.exp_neg, mul_one]
      exact inv_strictAnti₀ two_pos (by linarith)
    calc P {ω | ¬ ∀ x ∈ (rectAB 1 1).toSet, |phiVer W P δ 1 x ω| ≤ M}
        ≤ P {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | M ≤ ⨆ z : ferniqueBox 0 1, |phiVer W P δ 1 z ω|}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * 1))) := ENNReal.ofReal_le_ofReal htail
      _ < ENNReal.ofReal 2⁻¹ := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 he
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
  have h := le_lowerMedian_lenObs (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB 1 1)
    (by simp [rectAB]) (by simp [rectAB]) hM
  rw [abs_of_nonneg hξ, show (rectAB 1 1).crossWidth = 1 by simp [MarkedRect.crossWidth, rectAB],
    mul_one] at h
  have e : lambdaN ξ W P n = lowerMedianLaw (P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1))) := by
    rw [lambdaN, lenN, lenMN, hY]
  rw [e]
  exact h

/-- **`1 − ξq ≤ 2ξ`** (DDDF l. 1480) from (5.78) and the comparison with the infimum of the
field. -/
theorem one_sub_mul_le_of_578 (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) {q : ℝ}
    (h578 : S6Eq5_78 ξ q W P) : 1 - ξ * q ≤ 2 * ξ := by
  by_contra hcon
  rw [not_le] at hcon
  set a := 1 - ξ * q - 2 * ξ with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set L := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set C := ferniqueCF * Real.sqrt 6 + 2 * L + 1 with hC_def
  obtain ⟨K₀, hK₀⟩ := h578 (a / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (ξ * C / (L * (a / 2)))
  set n := max (max K₀ N) 1 with hn_def
  have hn1 : 1 ≤ n := le_max_right _ _
  have hnK : K₀ ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
  have h1 := lambdaN_ge_inf_field (P := P) (W := W) hW hξ hn1
  have h2 := hK₀ n hnK
  have h3 : (2 : ℝ) ^ (-((n : ℝ) * (1 - ξ * q - a / 2))) =
      Real.exp (-((n : ℝ) * (1 - ξ * q - a / 2)) * L) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  rw [h3] at h2
  have h4 := Real.exp_le_exp.1 (h1.trans h2)
  -- `n L a/2 ≤ ξ C`
  have h5 : (n : ℝ) * (L * (a / 2)) ≤ ξ * C := by
    rw [hC_def]; rw [ha_def] at h4 ⊢; nlinarith
  have h6 : ξ * C / (L * (a / 2)) < n := hN.trans_le hnN
  rw [div_lt_iff₀ (by positivity)] at h6
  linarith

/-- `ξ(Q + 2) < α ⇒ 1 < α` for `ξ = γ/d_γ` (DDDF l. 1478–1480) -/
theorem one_lt_of_xiQ2_lt {γ : ℝ} (hγ : 0 < γ) (hW : IsWhiteNoise P W)
    (h578 : S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) {α : ℝ}
    (hα : xiGamma γ * (LQGMetric.Q γ + 2) < α) : 1 < α := by
  have := one_sub_mul_le_of_578 hW (xiGamma_pos' hγ).le h578
  nlinarith

/-- **DDDF Prop 28, Part 2 Step 1 for the family** (l. 1455–1481) without `1 ≤ α`. -/
theorem s6_lowerStep1' {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P)
    (h578 : S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) {α : ℝ}
    (hα : xiGamma γ * (LQGMetric.Q γ + 2) < α) : S6P28.S6LowerStep1 (xiGamma γ) W P α :=
  S6P28L.s6_lowerStep1 hγ hγ2 hW h554 h578 (one_lt_of_xiQ2_lt hγ hW h578 hα).le hα

end S6XiQ
end DDDF
end LQGMetric
