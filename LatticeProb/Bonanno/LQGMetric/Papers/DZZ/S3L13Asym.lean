/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L13Asym at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Cov
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S3

/-!
# DZZ Lemma 3.13: the size inequality `s_B log(1/s_B) < ε* s_𝖢 / 10` (P2-DZZ313)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1334–1335: "on `𝓔_{δ,α*,u,v}`,
`s_𝖢 ≥ δ^{C_mc}`, thus `s_B log(1/s_B) = (ε*)² s_𝖢 log(1/((ε*)² s_𝖢)) < ε* s_𝖢 / 10`." Here in the form used
by `L313GeomC`: `ρ((ε*)² s) + 2 (ε*)² s ≤ ε* s / 10` for `δ^K ≤ s ≤ 1` and small `δ`
(`ρ(t) = t log t⁻¹ + t` is twice the range of the fine field). Own elementary asymptotics
(`e^X ≥ X³/6`, `X = α* √L log L`, `L = log δ⁻¹ ≤ X²`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

lemma l313_rho_eq (t : ℝ) : l313Rho t = t * Real.log t⁻¹ + t := by
  unfold l313Rho
  rw [← inv_pow, Real.log_pow]
  push_cast; ring

/-- **DZZ l. 1334–1335**: `ρ((ε*)² s) + 2 (ε*)² s ≤ ε* s / 10` for `δ^K ≤ s ≤ 1`, `δ` small. -/
theorem l313_size_asym {αs K : ℝ} (hαs : 0 < αs) (hK : 0 ≤ K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ s : ℝ, δ ^ K ≤ s → 0 < s →
      l313Rho (s * epsStar αs δ ^ 2) + 2 * (s * epsStar αs δ ^ 2) ≤ epsStar αs δ * s / 10 := by
  set L₀ : ℝ := max (max 1 (Real.exp αs⁻¹)) ((60 * K + 420) ^ 2)
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun δ hδ s hs hs0 => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  have hL : L₀ < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ.1).2 hδ.2
  have hL1 : 1 ≤ L := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hL.le
  have hLe : Real.exp αs⁻¹ ≤ L := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hL.le
  have hLK : (60 * K + 420) ^ 2 ≤ L := (le_max_right _ _).trans hL.le
  have hL0 : 0 < L := by linarith
  have hlogL : αs⁻¹ ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; exact hLe
  have hαlog : 1 ≤ αs * Real.log L := by
    rw [← mul_inv_cancel₀ hαs.ne']; exact mul_le_mul_of_nonneg_left hlogL hαs.le
  set X := αs * Real.sqrt L * Real.log L with hX
  have hsq1 : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL1
  have hXsq : Real.sqrt L ≤ X := by
    rw [hX, mul_right_comm]; nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hLX : L ≤ X ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hXsq 2
    rwa [Real.sq_sqrt hL0.le] at this
  have hXK : 60 * K + 420 ≤ X := by
    have : 60 * K + 420 ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) hL0.le]; exact hLK
    linarith
  -- bounds on `ε* = 2^{-N}`
  set N := epsStarN αs δ
  have hε : epsStar αs δ = (2 : ℝ)⁻¹ ^ N := rfl
  have hε0 : 0 < epsStar αs δ := by rw [hε]; positivity
  have hεX : epsStar αs δ ≤ Real.exp (-X) := epsStar_le_thr αs δ
  have h4 := four_pow_epsStarN_le αs δ hX0
  have h2N : (2 : ℝ) ^ N ≤ 2 * Real.exp X := by
    have e4 : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e : 4 * Real.exp (2 * X) = (2 * Real.exp X) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    rw [e4, e] at h4
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4
  have hNlog : (N : ℝ) * Real.log 2 ≤ Real.log 2 + X := by
    rw [← Real.log_pow, ← Real.log_exp X, ← Real.log_mul (by norm_num) (Real.exp_pos _).ne']
    exact Real.log_le_log (by positivity) h2N
  -- `log t⁻¹ ≤ K L + 2 N log 2`
  set t := s * epsStar αs δ ^ 2 with ht
  have ht0 : 0 < t := mul_pos hs0 (pow_pos hε0 2)
  have hlogs : Real.log s⁻¹ ≤ K * L := by
    rw [Real.log_inv, hLdef, Real.log_inv, neg_le, neg_mul_eq_mul_neg, neg_neg]
    have := Real.log_le_log (Real.rpow_pos_of_pos hδ.1 K) hs
    rwa [Real.log_rpow hδ.1] at this
  have hlogt : Real.log t⁻¹ = Real.log s⁻¹ + 2 * ((N : ℝ) * Real.log 2) := by
    rw [ht, hε, mul_inv, Real.log_mul (by positivity) (by positivity), ← pow_mul, inv_pow,
      inv_inv, Real.log_pow]
    push_cast; ring
  have hlt : Real.log t⁻¹ + 3 ≤ K * X ^ 2 + 2 * X + 5 := by
    have : K * L ≤ K * X ^ 2 := mul_le_mul_of_nonneg_left hLX hK
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    rw [hlogt]; linarith
  -- `10 (K X² + 2 X + 5) ≤ X³/6 ≤ e^X`
  have hexp : X ^ 3 / 6 ≤ Real.exp X := by
    have := Real.pow_div_factorial_le_exp X hX0 3
    simpa [Nat.factorial] using this
  have hpoly : 10 * (K * X ^ 2 + 2 * X + 5) ≤ X ^ 3 / 6 := by
    have hX1 : 1 ≤ X := by linarith
    have a1 : 2 * X ≤ 2 * X ^ 2 := by nlinarith
    have a2 : (5 : ℝ) ≤ 5 * X ^ 2 := by nlinarith
    have a3 : (60 * K + 420) * X ^ 2 ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right hXK (by positivity)
    nlinarith
  have hεpoly : epsStar αs δ * (K * X ^ 2 + 2 * X + 5) ≤ 1 / 10 := by
    have hpos : 0 ≤ K * X ^ 2 + 2 * X + 5 := by positivity
    calc epsStar αs δ * (K * X ^ 2 + 2 * X + 5) ≤ Real.exp (-X) * (K * X ^ 2 + 2 * X + 5) :=
          mul_le_mul_of_nonneg_right hεX hpos
      _ ≤ Real.exp (-X) * (Real.exp X / 10) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 / 10 := by rw [Real.exp_neg]; field_simp
  rw [l313_rho_eq t]
  have hs' : 0 < epsStar αs δ * s := by positivity
  calc t * Real.log t⁻¹ + t + 2 * t = t * (Real.log t⁻¹ + 3) := by ring
    _ ≤ t * (K * X ^ 2 + 2 * X + 5) := mul_le_mul_of_nonneg_left hlt ht0.le
    _ = (epsStar αs δ * s) * (epsStar αs δ * (K * X ^ 2 + 2 * X + 5)) := by rw [ht]; ring
    _ ≤ (epsStar αs δ * s) * (1 / 10) := mul_le_mul_of_nonneg_left hεpoly hs'.le
    _ = epsStar αs δ * s / 10 := by ring

end DZZ
end LQGMetric
