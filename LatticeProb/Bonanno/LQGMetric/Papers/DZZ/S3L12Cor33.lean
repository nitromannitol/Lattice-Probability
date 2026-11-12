/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Cor33 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L10Exp

/-!
# DZZ Corollary 3.3 (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Corollary 3.3 (`cor-approximate-LGD-expectation`,
l. 859–862), proved there from (eq-very-crude-prime), (eq-very-crude) (l. 849–857) and Proposition 3.2.

* `abs_integral_sub_le_of_highProb`: the generic step (as in the proof of `dzz_lemma310_exp`, of which it is
  the abstract form): if `|X_δ − Y_δ| ≤ C (log δ⁻¹)^{0.9}` on events of high probability and
  `E X_δ², E Y_δ² ≤ K (log δ⁻¹)²`, then `|E X_δ − E Y_δ| ≤ K' (log δ⁻¹)^{0.9}` (AM–GM form of Cauchy–Schwarz).
* **`dzz_cor33`**: `|E log D_{γ,δ}(u,v)/log δ⁻¹ − E log D'_{γ,δ}(u,v)/log δ⁻¹| ≤ K' (log δ⁻¹)^{−0.1}`.

**Rate (DEVIATION, statement question).** DZZ state the bound `e^{−(log δ⁻¹)^{0.9}}`. It does not follow
from the argument they give: Proposition 3.2 only controls `|log D − log D'| ≤ (log δ⁻¹)^{0.9}`, so the
difference of the normalized expectations is `O((log δ⁻¹)^{−0.1})`, which is what is proved here (the
consumer, (eq-oferberlin1)-type comparisons at scale `(log δ⁻¹)^{0.9}`, only needs this rate).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Abstract form of the proof of (eq-oferberlin1) / Corollary 3.3. -/
theorem abs_integral_sub_le_of_highProb [IsProbabilityMeasure P] {E : ℝ → Set Ω}
    {X Y : ℝ → Ω → ℝ} {C K : ℝ} (hC : 0 ≤ C) (hgood : HighProb P E)
    (hE : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω ∈ E δ, |X δ ω - Y δ ω| ≤ C * Real.log δ⁻¹ ^ (0.9 : ℝ))
    (hX : ∀ δ ∈ Ioo (0 : ℝ) 1, MemLp (X δ) 2 P ∧ ∫ ω, X δ ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1, MemLp (Y δ) 2 P ∧ ∫ ω, Y δ ω ^ 2 ∂P ≤ K * Real.log δ⁻¹ ^ 2) :
    ∃ K' δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      |(∫ ω, X δ ω ∂P) - ∫ ω, Y δ ω ∂P| ≤ K' * Real.log δ⁻¹ ^ (0.9 : ℝ) := by
  obtain ⟨c, hc, δ₁, hδ₁, hb⟩ := hgood
  set K₀ := max K 0
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  refine ⟨C + (4 * K₀ + 1) / c, min δ₁ (Real.exp (-1)), by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδa : δ < δ₁ := hδ.2.trans_le (min_le_left _ _)
  have hδe : δ < Real.exp (-1) := hδ.2.trans_le (min_le_right _ _)
  set L := Real.log δ⁻¹ with hLdef
  have hLlog : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    linarith
  have hδ1 : δ < 1 := hδe.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  obtain ⟨hXm, hX2⟩ := hX δ ⟨hδ0, hδ1⟩
  obtain ⟨hYm, hY2⟩ := hY δ ⟨hδ0, hδ1⟩
  set x := L ^ (0.9 : ℝ) with hxdef
  have hx1 : 1 ≤ x := Real.one_le_rpow hL1 (by norm_num)
  set S := toMeasurable P (E δ)ᶜ
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hPS : P.real S ≤ δ ^ c := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hb δ ⟨hδ0, hδa⟩)
  set ε := δ ^ (c / 2) / L
  have hε : 0 < ε := by positivity
  have hpt : ∀ ω, |X δ ω - Y δ ω| ≤
      C * x + (ε * (X δ ω - Y δ ω) ^ 2 + S.indicator (fun _ => (1 : ℝ)) ω / ε) / 2 := by
    intro ω
    have hsq : 0 ≤ ε * (X δ ω - Y δ ω) ^ 2 := by positivity
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω]
      have key : (ε * (X δ ω - Y δ ω) ^ 2 + 1 / ε) / 2 - |X δ ω - Y δ ω| =
          (ε * |X δ ω - Y δ ω| - 1) ^ 2 / (2 * ε) := by
        rw [← sq_abs (X δ ω - Y δ ω)]
        field_simp
        ring
      have : 0 ≤ (ε * |X δ ω - Y δ ω| - 1) ^ 2 / (2 * ε) := by positivity
      have : 0 ≤ C * x := by positivity
      linarith
    · rw [indicator_of_notMem hω, zero_div, add_zero]
      have hEω : ω ∈ E δ := by
        by_contra h
        exact hω (subset_toMeasurable _ _ h)
      have : |X δ ω - Y δ ω| ≤ C * x := hE δ ⟨hδ0, hδ1⟩ ω hEω
      have : 0 ≤ ε * (X δ ω - Y δ ω) ^ 2 / 2 := by positivity
      linarith
  have hD2 : Integrable (fun ω => (X δ ω - Y δ ω) ^ 2) P := (hXm.sub hYm).integrable_sq
  have hI : Integrable (S.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hSm
  have hDint : Integrable (fun ω => X δ ω - Y δ ω) P :=
    (hXm.integrable one_le_two).sub (hYm.integrable one_le_two)
  have g1 : Integrable (fun ω => ε * (X δ ω - Y δ ω) ^ 2) P := hD2.const_mul ε
  have g2 : Integrable (fun ω => S.indicator (fun _ => (1 : ℝ)) ω / ε) P := hI.div_const ε
  have g3 : Integrable
      (fun ω => ε * (X δ ω - Y δ ω) ^ 2 + S.indicator (fun _ => (1 : ℝ)) ω / ε) P := g1.add g2
  have g4 : Integrable
      (fun ω => (ε * (X δ ω - Y δ ω) ^ 2 + S.indicator (fun _ => (1 : ℝ)) ω / ε) / 2) P :=
    g3.div_const 2
  have hint : Integrable (fun ω => C * x +
      (ε * (X δ ω - Y δ ω) ^ 2 + S.indicator (fun _ => (1 : ℝ)) ω / ε) / 2) P :=
    (integrable_const _).add g4
  have hmain : ∫ ω, |X δ ω - Y δ ω| ∂P ≤
      C * x + (ε * ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P + P.real S / ε) / 2 := by
    refine (integral_mono hDint.abs hint hpt).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) g4, integral_div, integral_add g1 g2,
      integral_div, integral_indicator hSm, setIntegral_const]
    simp [integral_const_mul]
  have hD2le : ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P ≤ 4 * K₀ * L ^ 2 := by
    have h1 : ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P ≤ ∫ ω, (2 * X δ ω ^ 2 + 2 * Y δ ω ^ 2) ∂P :=
      integral_mono hD2 ((hXm.integrable_sq.const_mul 2).add (hYm.integrable_sq.const_mul 2))
        fun ω => by nlinarith [sq_nonneg (X δ ω + Y δ ω)]
    rw [integral_add (hXm.integrable_sq.const_mul 2) (hYm.integrable_sq.const_mul 2),
      integral_const_mul, integral_const_mul] at h1
    have hK : K ≤ K₀ := le_max_left _ _
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith [mul_le_mul_of_nonneg_right hK hL2]
  have hδc2 : δ ^ (c / 2) = Real.exp (-(c / 2 * L)) := by
    rw [Real.rpow_def_of_pos hδ0, hLlog]; ring_nf
  have hLδ : L * δ ^ (c / 2) ≤ 2 / c := by
    rw [hδc2]
    have := Real.add_one_le_exp (c / 2 * L)
    have hexp := Real.exp_pos (c / 2 * L)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp hc]
    nlinarith
  have hδc : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hbad : (ε * ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P + P.real S / ε) / 2 ≤ (4 * K₀ + 1) / c := by
    have hL0 : 0 < L := by linarith
    have hdp : 0 < δ ^ (c / 2) := by positivity
    have t1 : ε * ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P ≤ 4 * K₀ * (L * δ ^ (c / 2)) := by
      calc ε * ∫ ω, (X δ ω - Y δ ω) ^ 2 ∂P ≤ ε * (4 * K₀ * L ^ 2) :=
            mul_le_mul_of_nonneg_left hD2le hε.le
        _ = 4 * K₀ * (L * δ ^ (c / 2)) := by
            simp only [ε]; field_simp
    have t2 : P.real S / ε ≤ L * δ ^ (c / 2) := by
      rw [div_le_iff₀ hε]
      calc P.real S ≤ δ ^ c := hPS
        _ = L * δ ^ (c / 2) * ε := by rw [hδc]; simp only [ε]; field_simp
    have t3 : 4 * K₀ * (L * δ ^ (c / 2)) ≤ 4 * K₀ * (2 / c) :=
      mul_le_mul_of_nonneg_left hLδ (by positivity)
    have e : (4 * K₀ * (2 / c) + 2 / c) / 2 = (4 * K₀ + 1) / c := by field_simp
    linarith
  have hfin : (4 * K₀ + 1) / c ≤ (4 * K₀ + 1) / c * x :=
    le_mul_of_one_le_right (by positivity) hx1
  rw [← integral_sub (hXm.integrable one_le_two) (hYm.integrable one_le_two)]
  refine (abs_integral_le_integral_abs).trans (hmain.trans ?_)
  nlinarith

/-- `log D'_{γ,δ}(A, B)` (junk `0` if infinite). -/
def logApproxLGD (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (A B : Set ℂ) (ω : Ω) : ℝ :=
  Real.log ((approxLGDSet γ W δ A B ω).toNat : ℝ)

end DZZ
end LQGMetric
