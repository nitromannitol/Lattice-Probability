/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperProb at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperMoment
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Decision D52; the fractional-moment bound `prob_sum_exp_gt_le` applied to a straight walk
(`prob_walk_le`) and to the dyadic scale sum (`prob_scale_sum_le`), and the geometric sum of the
box failure probabilities (`box_geom_le`). Variance bound `Var h_ρ(z) ≤ log ρ⁻¹ + 2 log 4`
(`DG.gffCircleCov_self_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open LQGDimension (IsGFFCircleAverage)

lemma exp_var_le {ρ s : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 3) :
    Real.exp (LQGDimension.gffCircleCov ρ z ρ z * s ^ 2 / 2) ≤
      ρ ^ (-(s ^ 2 / 2)) * Real.exp (Real.log 4 * s ^ 2) := by
  have hv := DG.gffCircleCov_self_le hρ hρ1 hz
  rw [Real.rpow_def_of_pos hρ, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have : 0 ≤ s ^ 2 := sq_nonneg s
  nlinarith

lemma walk_sum_eq (δ ξ : ℝ) (Φ : ℂ → ℝ) (k k' : ℤ × ℤ) :
    ((gridWalk δ k k').map fun x => Real.exp (ξ * Φ x)).sum =
      ∑ j ∈ Finset.range (wlen k k' + 1), 1 * Real.exp (ξ * Φ (wpt δ k k' j)) := by
  unfold gridWalk
  generalize wlen k k' + 1 = m
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- walk tail bound -/
theorem prob_walk_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : IsGFFCircleAverage H P) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {k k' : ℤ × ℤ}
    (hk : gpt δ k ∈ rS 1) (hk' : gpt δ k' ∈ rS 1) (ξ : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {T : ℝ} (hT : 0 < T) :
    P {ω | T < ((gridWalk δ k k').map fun x => Real.exp (ξ * H δ x ω)).sum} ≤
      ENNReal.ofReal (T ^ (-θ) * ((wlen k k' + 1 : ℕ) : ℝ) *
        (δ ^ (-((θ * ξ) ^ 2 / 2)) * Real.exp (Real.log 4 * (θ * ξ) ^ 2))) := by
  have hmem : ∀ j, wpt δ k k' j ∈ rS 1 := fun j => by
    by_cases hj : j < wlen k k' + 1
    · exact (isGraphPath_gridWalk hδ hk hk').2.1 _
        (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩) |>.1
    · have : wpt δ k k' j = gpt δ k' := by
        unfold wpt
        rw [cstep_of_le, cstep_of_le]
        · simp
        · have : (k'.2 - k.2).natAbs ≤ wlen k k' := le_max_right _ _
          have : (k'.2 - k.2).natAbs ≤ j := by omega
          rw [Int.abs_eq_natAbs]; exact_mod_cast this
        · have : (k'.1 - k.1).natAbs ≤ wlen k k' := le_max_left _ _
          have : (k'.1 - k.1).natAbs ≤ j := by omega
          rw [Int.abs_eq_natAbs]; exact_mod_cast this
      rw [this]; exact hk'
  simp_rw [walk_sum_eq δ ξ _ k k']
  refine (prob_sum_exp_gt_le hH _ (fun _ => 1) (fun _ => zero_le_one) (fun _ => δ)
    (fun _ => hδ) (wpt δ k k') ξ hθ0 hθ1 hT).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le _)
  calc ∑ j ∈ Finset.range (wlen k k' + 1), (1:ℝ) ^ θ *
        Real.exp (LQGDimension.gffCircleCov δ (wpt δ k k' j) δ (wpt δ k k' j) * (θ * ξ) ^ 2 / 2)
      ≤ ∑ j ∈ Finset.range (wlen k k' + 1),
        (δ ^ (-((θ * ξ) ^ 2 / 2)) * Real.exp (Real.log 4 * (θ * ξ) ^ 2)) :=
        Finset.sum_le_sum fun j _ => by
          rw [Real.one_rpow, one_mul]
          exact exp_var_le hδ hδ1 (norm_le_three_of_mem_rS (hmem j))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- scale-sum tail bound: `Σ_{k<n} r_k^{s} e^{ξ h_{r_k}(c)}`, `r_k = 2^{−k−1}` -/
theorem prob_scale_sum_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : IsGFFCircleAverage H P) (n : ℕ) {c : ℂ} (hc : ‖c‖ ≤ 3) {ξ s : ℝ} (hs : 0 ≤ s)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hu : 0 < θ * s - (θ * ξ) ^ 2 / 2) {T : ℝ} (hT : 0 < T) :
    P {ω | T < ∑ k ∈ Finset.range n, rk k ^ s * Real.exp (ξ * H (rk k) c ω)} ≤
      ENNReal.ofReal (T ^ (-θ) * Real.exp (Real.log 4 * (θ * ξ) ^ 2) /
        (2 ^ (θ * s - (θ * ξ) ^ 2 / 2) - 1)) := by
  set u := θ * s - (θ * ξ) ^ 2 / 2 with hudef
  refine (prob_sum_exp_gt_le hH _ (fun k => rk k ^ s)
    (fun k => Real.rpow_nonneg (rk_pos k).le _) rk rk_pos (fun _ => c) ξ hθ0 hθ1 hT).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h2u : 1 < (2:ℝ) ^ u := Real.one_lt_rpow (by norm_num) hu
  have hterm : ∀ k, (rk k ^ s) ^ θ * Real.exp (LQGDimension.gffCircleCov (rk k) c (rk k) c *
      (θ * ξ) ^ 2 / 2) ≤ Real.exp (Real.log 4 * (θ * ξ) ^ 2) * ((2:ℝ) ^ u)⁻¹ ^ (k + 1) := by
    intro k
    have hr := rk_pos k
    have h1 := exp_var_le (s := θ * ξ) hr ((rk_le_half k).trans (by norm_num)) hc
    have hrk : rk k = (2:ℝ) ^ (-((k:ℝ) + 1)) := by
      unfold rk
      rw [Real.rpow_neg (by norm_num), show ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, one_div, inv_pow]
    have e : (rk k ^ s) ^ θ * rk k ^ (-((θ * ξ) ^ 2 / 2)) = ((2:ℝ) ^ u)⁻¹ ^ (k + 1) := by
      rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr, hrk,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_natCast ((2:ℝ) ^ (-u)) (k + 1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; rw [hudef]; push_cast; ring
    calc _ ≤ (rk k ^ s) ^ θ * (rk k ^ (-((θ * ξ) ^ 2 / 2)) *
          Real.exp (Real.log 4 * (θ * ξ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Real.rpow_nonneg hr.le _) _)
      _ = _ := by rw [← mul_assoc, e, mul_comm]
  have hq0 : 0 ≤ ((2:ℝ) ^ u)⁻¹ := by positivity
  have hq1 : ((2:ℝ) ^ u)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2u
  have hgeo : ∑ k ∈ Finset.range n, ((2:ℝ) ^ u)⁻¹ ^ (k + 1) ≤ 1 / (2 ^ u - 1) := by
    set q := ((2:ℝ) ^ u)⁻¹ with hq
    have hs := geom_sum_eq (ne_of_lt hq1) n
    have e : ∑ k ∈ Finset.range n, q ^ (k + 1) = q * ∑ k ∈ Finset.range n, q ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, hs]
    have hpos : 0 < 1 - q := by linarith
    have hn : 0 ≤ q ^ n := pow_nonneg hq0 n
    have h1 : (q ^ n - 1) / (q - 1) ≤ 1 / (1 - q) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
      exact div_le_div_of_nonneg_right (by linarith) hpos.le
    have h3 : q * (1 / (1 - q)) = 1 / (2 ^ u - 1) := by
      have h2 : (0:ℝ) < 2 ^ u := by positivity
      rw [hq]; field_simp
    calc q * ((q ^ n - 1) / (q - 1)) ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left h1 hq0
      _ = _ := h3
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le _)
  calc _ ≤ ∑ k ∈ Finset.range n, Real.exp (Real.log 4 * (θ * ξ) ^ 2) *
        ((2:ℝ) ^ u)⁻¹ ^ (k + 1) := Finset.sum_le_sum fun k _ => hterm k
    _ = Real.exp (Real.log 4 * (θ * ξ) ^ 2) * ∑ k ∈ Finset.range n, ((2:ℝ) ^ u)⁻¹ ^ (k + 1) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (Real.log 4 * (θ * ξ) ^ 2) * (1 / (2 ^ u - 1)) :=
        mul_le_mul_of_nonneg_left hgeo (Real.exp_pos _).le
    _ = _ := by ring

/-- geometric sum of the box failure probabilities: `Σ_{k<n} (δ/r_k)^p ≤ (2^n δ)^p 2^p/(2^p − 1)`
-/
theorem box_geom_le {δ p : ℝ} (hδ : 0 < δ) (hp : 0 < p) (n : ℕ) :
    ∑ k ∈ Finset.range n, (δ / rk k) ^ p ≤ (2 ^ n * δ) ^ p * (2 ^ p / (2 ^ p - 1)) := by
  have h2p : 1 < (2:ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  have hterm : ∀ k, (δ / rk k) ^ p = δ ^ p * ((2:ℝ) ^ p) ^ (k + 1) := fun k => by
    unfold rk
    rw [Real.div_rpow hδ.le (by positivity), div_eq_mul_inv, ← Real.inv_rpow (by positivity)]
    congr 1
    rw [one_div, inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeo := geom_sum_eq (ne_of_gt h2p) n
  have e : ∑ k ∈ Finset.range n, ((2:ℝ) ^ p) ^ (k + 1) =
      (2:ℝ) ^ p * ∑ k ∈ Finset.range n, ((2:ℝ) ^ p) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, hgeo]
  have hpow : ((2:ℝ) ^ p) ^ n = (2 ^ n) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm]
  rw [Real.mul_rpow (by positivity) hδ.le, hpow]
  have hden : 0 < (2:ℝ) ^ p - 1 := by linarith
  have hn : 0 ≤ ((2:ℝ) ^ n) ^ p := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hδp : 0 ≤ δ ^ p := Real.rpow_nonneg hδ.le _
  have hinv : 0 ≤ ((2:ℝ) ^ p - 1)⁻¹ := inv_nonneg.2 hden.le
  have h2 : 0 < (2:ℝ) ^ p := by positivity
  nlinarith [mul_nonneg (mul_nonneg hδp h2.le) hinv]

end LQGMetric.DFGPS.L36
