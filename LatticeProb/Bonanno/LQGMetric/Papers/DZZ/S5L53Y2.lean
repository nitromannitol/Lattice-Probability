/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Y2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Y1

/-!
# DZZ Lemma 5.3 part 1, R1: the per-pair far bound `C₀ K⁻⁴` (P2-DZZ53Y, packet P-131F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2474 and l. 2490–2502
("we combine the preceding inequality with Corollary 3.9 and Proposition 3.17 and deduce
`P(log D̃_{δδ̃}(z,z') ≥ E log D̃_{δ̃}(u,v) + L^{0.97} | 𝓕*) ≤ O(K⁻⁴)`"), for the proxy
`ν_𝖡 = c_B · M̃_{γ,2^{-m},η}` (`proxyMass`, S5L53K1; DEC-131 §3 P-131F and §9).

* **`l53_far_bound_gen`**: one coupling (`l53_far_pair_couple`, S5L53Y1, with the coupling of
  `fineChaos_sim_couple`, S5L53X4, as hypothesis), the `(u,v)`-side `l53_uv_step` and `l53_uv_far`
  (S5L53G6, with its inputs `h317`, `hcor`): `P(far) ≤ C ρ² e^{−λ²/(C(log ρ+1))} + K⁻⁴`,
  `ρ = ‖a‖2^m ≥ 1`, whenever `‖a‖ δ̃ e^{−L^{0.95}} e^{λ} ρ^{γ²/4} ≤ δδ̃/√c_B`.
* **`l53_far_bound`**: DZZ's choice `λ = L^{0.8}`, `c_B = δ² s⁻² e^{L^{0.91}}` (DZZ l. 2455, the
  constant of `l53MB`, DEC-131-IF G-M), threshold `δ · 2^{-l}`: `P(far) ≤ 2 K⁻⁴` for `L ≥ L₀`,
  under the size conditions `‖a‖ ≤ s`, `2^{-m} ≤ ‖a‖`, `‖a‖ 2^m ≤ e^{L^{0.52}}` (at DZZ's scales with
  `ℓ = 4κ + ℓ₀`, DEC-131-IF S/F-3: `ρ ∈ [2^ℓ K⁻⁴/|u−v|, 2^{ℓ+1}/|u−v|]`).
* **`l53_far_bound_dy`** (DEC-131-IF G-F1): the same for `z, z' ∈ ∂𝖡` of a dyadic sub-box `𝖡`, with
  `S = 𝕍_{c_𝖡, 5 s_𝖡}`, `δ = 2^{-k}`, `L = k log 2`, threshold `2^{-(k+l)}`.
* `l53_exists_sim`: the similarity with `θu = z`, `θv = z'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

/-- the similarity `θ = simMap a b` with `θu = z`, `θv = z'` -/
lemma l53_exists_sim {u v : ℂ} (huv : u ≠ v) (z z' : ℂ) :
    ∃ a b : ℂ, simMap a b u = z ∧ simMap a b v = z' ∧ ‖a‖ = ‖z' - z‖ / ‖v - u‖ := by
  have hvu : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
  refine ⟨(z' - z) / (v - u), z - (z' - z) / (v - u) * u, ?_, ?_, norm_div _ _⟩
  · simp only [simMap]; ring
  · simp only [simMap]; field_simp; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### DZZ's parameters -/

/-- the threshold and tail inequalities for large `L` -/
lemma l53_far_eventually (C D : ℝ) (hD : 0 < D) : ∀ᶠ L : ℝ in atTop,
    L ^ (0.8 : ℝ) + L ^ (0.52 : ℝ) + L ^ (0.91 : ℝ) / 2 ≤ L ^ (0.95 : ℝ) ∧
    C * Real.exp (2 * L ^ (0.52 : ℝ) - L ^ (1.08 : ℝ) / D) ≤
      ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 := by
  have t1 := tendsto_rpow_atTop (show (0 : ℝ) < 0.04 by norm_num)
  have t2 := tendsto_rpow_atTop (show (0 : ℝ) < 0.56 by norm_num)
  have t3 := tendsto_rpow_atTop (show (0 : ℝ) < 0.52 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), t1.eventually_ge_atTop (5 / 2),
    t2.eventually_ge_atTop (6 * D), t3.eventually_ge_atTop (|Real.log (max C 1)|)]
    with L hL1 h1 h2 h3
  have hL0 : 0 < L := by linarith
  have p8 : L ^ (0.8 : ℝ) ≤ L ^ (0.91 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have p52 : L ^ (0.52 : ℝ) ≤ L ^ (0.91 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have p51 : L ^ (0.51 : ℝ) ≤ L ^ (0.52 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have e95 : L ^ (0.95 : ℝ) = L ^ (0.91 : ℝ) * L ^ (0.04 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have e108 : L ^ (1.08 : ℝ) = L ^ (0.52 : ℝ) * L ^ (0.56 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h91 : 0 ≤ L ^ (0.91 : ℝ) := by positivity
  have h51 : 0 ≤ L ^ (0.51 : ℝ) := by positivity
  have h52 : 0 ≤ L ^ (0.52 : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · rw [e95]; nlinarith
  · have hK : Real.exp (-(4 * Real.log 2 * L ^ (0.51 : ℝ))) ≤
        ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 := by
      have hfl : (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) ≤ L ^ (0.51 : ℝ) := Nat.floor_le h51
      have e : ((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4 =
          Real.exp (-(4 * Real.log 2 * (⌊L ^ (0.51 : ℝ)⌋₊ : ℝ))) := by
        have h2 : (2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊ =
            Real.exp ((⌊L ^ (0.51 : ℝ)⌋₊ : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log two_pos]
        rw [h2, ← Real.exp_neg, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [e]
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      nlinarith
    refine le_trans ?_ hK
    have hlog2 : Real.log 2 < 3 / 4 := by
      have := Real.log_two_lt_d9; linarith
    have hCle : C ≤ Real.exp (|Real.log (max C 1)|) := by
      calc C ≤ max C 1 := le_max_left _ _
        _ = Real.exp (Real.log (max C 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
        _ ≤ Real.exp (|Real.log (max C 1)|) := Real.exp_le_exp.2 (le_abs_self _)
    have hq : L ^ (1.08 : ℝ) / D ≥ 6 * L ^ (0.52 : ℝ) := by
      rw [ge_iff_le, le_div_iff₀ hD, e108]; nlinarith
    calc C * Real.exp (2 * L ^ (0.52 : ℝ) - L ^ (1.08 : ℝ) / D)
        ≤ Real.exp (|Real.log (max C 1)|) * Real.exp (2 * L ^ (0.52 : ℝ) - L ^ (1.08 : ℝ) / D) :=
          mul_le_mul_of_nonneg_right hCle (Real.exp_pos _).le
      _ = Real.exp (|Real.log (max C 1)| + (2 * L ^ (0.52 : ℝ) - L ^ (1.08 : ℝ) / D)) := by
          rw [← Real.exp_add]
      _ ≤ Real.exp (-(4 * Real.log 2 * L ^ (0.51 : ℝ))) := by
          refine Real.exp_le_exp.2 ?_
          nlinarith

/-- `√(δ² s⁻² e^X) = δ s⁻¹ e^{X/2}` -/
lemma l53_sqrt_cB {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (X : ℝ) :
    Real.sqrt (δ ^ 2 / s ^ 2 * Real.exp X) = δ / s * Real.exp (X / 2) := by
  have e : δ ^ 2 / s ^ 2 * Real.exp X = (δ / s * Real.exp (X / 2)) ^ 2 := by
    rw [mul_pow, div_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [e]; exact Real.sqrt_sq (by positivity)

end DZZ
end LQGMetric
