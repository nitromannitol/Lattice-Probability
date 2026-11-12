/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_10Moment at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Propositions 3.9–3.10: from tail bounds to moment bounds

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.10, last sentence (T:1914–1915): "For `p ∈ (0, 4d_γ/γ²)`, we can multiply
this last estimate by `C̃^{p-1}` and integrate to get the desired `p`th moment bound." We use the
dyadic form of this layer-cake step: `X^p ≤ (2t₀)^p + Σ_k (t₀2^{k+2})^p 1{X > t₀2^k}`, which
needs no measurability of `X` (we pass to measurable hulls of the level sets).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS

/-- the moment bound produced by `lintegral_rpow_le_of_tail` -/
def momBd (p a C t₀ : ℝ) : ℝ :=
  (2 * t₀) ^ p + 4 ^ p * C * t₀ ^ (p - a) / (1 - (2 : ℝ) ^ (p - a))

lemma rpow_dyadic_identity {p a C t₀ : ℝ} (ht₀ : 0 < t₀) (k : ℕ) :
    (t₀ * 2 ^ (k + 2)) ^ p * (C * (t₀ * 2 ^ k) ^ (-a)) =
      4 ^ p * C * t₀ ^ (p - a) * ((2 : ℝ) ^ (p - a)) ^ k := by
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hA : (t₀ * 2 ^ (k + 2)) ^ p = t₀ ^ p * 4 ^ p * ((2 : ℝ) ^ p) ^ k := by
    rw [Real.mul_rpow ht₀.le (by positivity), ← Real.rpow_pow_comm h2, pow_add,
      Real.rpow_pow_comm h2 p 2]
    norm_num
    ring
  have hB : (t₀ * 2 ^ k) ^ (-a) = t₀ ^ (-a) * ((2 : ℝ) ^ (-a)) ^ k := by
    rw [Real.mul_rpow ht₀.le h2k, ← Real.rpow_pow_comm h2]
  rw [hA, hB, sub_eq_add_neg, Real.rpow_add ht₀, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    mul_pow]
  ring

/-- **Tail to moment** (T:1914–1915): if `P(X > t) ≤ C t^{-a}` for `t ≥ t₀ ≥ 1` and `0 < p < a`,
then `E[X^p] ≤ momBd p a C t₀`. No measurability of `X` is needed. -/
theorem lintegral_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) {p a C t₀ : ℝ} (hp : 0 < p) (hpa : p < a) (hC : 0 ≤ C) (ht₀ : 1 ≤ t₀)
    (hT : ∀ t : ℝ, t₀ ≤ t → P {ω | ENNReal.ofReal t < X ω} ≤ ENNReal.ofReal (C * t ^ (-a))) :
    ∫⁻ ω, X ω ^ p ∂P ≤ ENNReal.ofReal (momBd p a C t₀) := by
  have ht0 : 0 < t₀ := by linarith
  set S : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal (t₀ * 2 ^ k) < X ω} with hS
  set M : ℕ → Set Ω := fun k => toMeasurable P (S k) with hM
  set c : ℕ → ℝ := fun k => (t₀ * 2 ^ (k + 2)) ^ p with hc
  have hc1 : ∀ k, 1 ≤ c k := fun k => Real.one_le_rpow
    (one_le_mul_of_one_le_of_one_le ht₀ (one_le_pow₀ (by norm_num))) hp.le
  have hpt : ∀ ω, X ω ^ p ≤ ENNReal.ofReal ((2 * t₀) ^ p) +
      ∑' k, (M k).indicator (fun _ => ENNReal.ofReal (c k)) ω := by
    intro ω
    have hmem : ∀ k, ω ∈ S k → (M k).indicator (fun _ => ENNReal.ofReal (c k)) ω =
        ENNReal.ofReal (c k) := fun k hk => indicator_of_mem (subset_toMeasurable P _ hk) _
    rcases le_or_gt (X ω) (ENNReal.ofReal (2 * t₀)) with h1 | h1
    · refine le_trans ?_ le_self_add
      rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith) hp.le]
      exact ENNReal.rpow_le_rpow h1 hp.le
    rcases eq_or_ne (X ω) ⊤ with htop | htop
    · have hall : ∀ k, ω ∈ S k := fun k => by simp [hS, htop]
      have : ∑' k, (M k).indicator (fun _ => ENNReal.ofReal (c k)) ω = ⊤ := by
        refine top_le_iff.1 ?_
        rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [hmem k (hall k)]
        exact ENNReal.one_le_ofReal.2 (hc1 k)
      rw [this, add_top]; exact le_top
    · set x := (X ω).toReal / (2 * t₀) with hx
      have hXr : 2 * t₀ < (X ω).toReal := by
        rwa [← ENNReal.ofReal_lt_iff_lt_toReal (by linarith) htop]
      have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by linarith)]; linarith
      obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
      rw [hx, le_div_iff₀ (by linarith)] at hn1
      rw [hx, div_lt_iff₀ (by linarith)] at hn2
      have hSn : ω ∈ S n := by
        show ENNReal.ofReal (t₀ * 2 ^ n) < X ω
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop]
        have : 0 < t₀ * 2 ^ n := by positivity
        linarith
      refine le_trans ?_ (le_trans (ENNReal.le_tsum n) le_add_self)
      rw [hmem n hSn, hc, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le]
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [← ENNReal.ofReal_toReal htop]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [pow_add, pow_succ] at hn2 ⊢
      nlinarith
  have hMm : ∀ k, MeasurableSet (M k) := fun k => measurableSet_toMeasurable P _
  calc ∫⁻ ω, X ω ^ p ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal ((2 * t₀) ^ p) +
          ∑' k, (M k).indicator (fun _ => ENNReal.ofReal (c k)) ω) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal ((2 * t₀) ^ p) * P univ + ∑' k, ENNReal.ofReal (c k) * P (S k) := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum fun k => (measurable_const.indicator (hMm k)).aemeasurable]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator_const (hMm k), measure_toMeasurable]
    _ ≤ ENNReal.ofReal ((2 * t₀) ^ p) * 1 +
          ∑' k, ENNReal.ofReal (4 ^ p * C * t₀ ^ (p - a) * ((2 : ℝ) ^ (p - a)) ^ k) := by
        gcongr
        · exact prob_le_one
        rename_i k
        have hk : t₀ ≤ t₀ * 2 ^ k := le_mul_of_one_le_right ht0.le (one_le_pow₀ (by norm_num))
        rw [← rpow_dyadic_identity ht0 k, ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_right (hT _ hk) _
    _ = ENNReal.ofReal (momBd p a C t₀) := by
        have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (p - a) := by positivity
        have hr1 : (2 : ℝ) ^ (p - a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
          (by linarith)
        have hK : 0 ≤ 4 ^ p * C * t₀ ^ (p - a) := by positivity
        rw [mul_one, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left _), tsum_mul_left,
          tsum_geometric_of_lt_one hr0 hr1, ← ENNReal.ofReal_add (by positivity)
          (by have : 0 < 1 - (2 : ℝ) ^ (p - a) := by linarith
              positivity), momBd, div_eq_mul_inv]

/-- **Negative moments from a lower tail**: if `P(X < 1/t) ≤ C t^{-a}` for `t ≥ t₀ ≥ 1` and
`0 < -p < a`, then `E[X^p] ≤ momBd (-p) a C t₀`. -/
theorem lintegral_rpow_neg_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) {p a C t₀ : ℝ} (hp : p < 0) (hpa : -p < a) (hC : 0 ≤ C) (ht₀ : 1 ≤ t₀)
    (hT : ∀ t : ℝ, t₀ ≤ t → P {ω | X ω < ENNReal.ofReal t⁻¹} ≤ ENNReal.ofReal (C * t ^ (-a))) :
    ∫⁻ ω, X ω ^ p ∂P ≤ ENNReal.ofReal (momBd (-p) a C t₀) := by
  have hX : ∀ ω, X ω ^ p = (X ω)⁻¹ ^ (-p) := fun ω => by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
  simp_rw [hX]
  refine lintegral_rpow_le_of_tail P (fun ω => (X ω)⁻¹) (by linarith) hpa hC ht₀ fun t ht => ?_
  refine le_trans (measure_mono fun ω hω => ?_) (hT t ht)
  simp only [mem_ofPred_eq] at hω ⊢
  have ht0 : 0 < t := by linarith
  rw [ENNReal.ofReal_inv_of_pos ht0]
  exact ENNReal.lt_inv_iff_lt_inv.1 hω

end LQGMetric.DFGPS
