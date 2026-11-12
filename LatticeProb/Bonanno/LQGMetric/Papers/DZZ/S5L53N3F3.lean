/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N3F3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N3F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N3P3

/-!
# DZZ Lemma 5.3 part 1, node 3 closed: `L53Node3PartAll` (P2-DZZ53N3F)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2425–2514. **`l53_node3_part : L53Node3PartAll`**
(S5L53FN3): `l53n3_cell_core` (S5L53N3F2) at the parameters of P2-DZZ53N3P
(`l53_node3_params αs 13`, S5L53N3P3: `κ = ⌊L^{0.51}⌋`, `2^κ = 2N + 2`, `n = N - ⌈L²⌉`,
`j = ⌈L²⌉`), with `q = 3/2`. The remaining side conditions of the core: the covering condition
`20 (2(N-n) + 3 + 128 j) 2^{-κ} < ε*²` of O2A (from the room `j 2^{2n_{ε*}+13} ≤ 2^κ`),
`2^{127} ≤ N + 1`, and the threshold step `L^{0.97} + log((2N+2)² + 1) ≤ 2 L^{0.98}`
(`l53n3_thr_ev`). Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma l53n3_tendsto_L :
    Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos one_lt_two)

/-- The threshold step: `L^{0.97} + log((2N+2)² + 1) ≤ 2 L^{0.98}` for `2N + 2 = 2^{⌊L^{0.51}⌋}`. -/
lemma l53n3_thr_ev : ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ N : ℕ,
    2 ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ = 2 * N + 2 →
    ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ) + Real.log ((((2 * N + 2) ^ 2 : ℕ) : ℝ) + 1) ≤
      2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ) := by
  have h47 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.47)).comp l53n3_tendsto_L
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    ((h47.eventually_ge_atTop 3).and (l53n3_tendsto_L.eventually_ge_atTop 1))
  refine ⟨k₀, fun k hk N hK => ?_⟩
  obtain ⟨h3, h1⟩ := hk₀ k hk
  simp only [Function.comp] at h3
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  set κ : ℕ := ⌊L ^ (0.51 : ℝ)⌋₊ with hκ
  have hL0 : 0 < L := by linarith
  have hκL : (κ : ℝ) ≤ L ^ (0.51 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hcast : (((2 * N + 2) ^ 2 : ℕ) : ℝ) = ((2 : ℝ) ^ κ) ^ 2 := by
    rw [← hK]; push_cast; ring
  have hx1 : (1 : ℝ) ≤ (2 : ℝ) ^ κ := one_le_pow₀ (by norm_num)
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : Real.log (((2 : ℝ) ^ κ) ^ 2 + 1) ≤ Real.log 2 + 2 * κ * Real.log 2 := by
    have hp : (0 : ℝ) < ((2 : ℝ) ^ κ) ^ 2 := by positivity
    calc Real.log (((2 : ℝ) ^ κ) ^ 2 + 1) ≤ Real.log (2 * ((2 : ℝ) ^ κ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + 2 * κ * Real.log 2 := by
          rw [Real.log_mul (by norm_num) hp.ne', ← pow_mul, Real.log_pow]; push_cast; ring
  have h98 : L ^ (0.98 : ℝ) = L ^ (0.51 : ℝ) * L ^ (0.47 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h97 : L ^ (0.97 : ℝ) ≤ L ^ (0.98 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have h51 : 1 ≤ L ^ (0.51 : ℝ) := Real.one_le_rpow h1 (by norm_num)
  rw [hcast]
  have hκ0 : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  have : 2 * (κ : ℝ) * Real.log 2 ≤ 2 * L ^ (0.51 : ℝ) := by nlinarith
  nlinarith

lemma l53n3_kap_ev : ∃ k₀ : ℕ, ∀ k ≥ k₀, 128 ≤ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.51)).comp l53n3_tendsto_L
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h.eventually_ge_atTop 128)
  exact ⟨k₀, fun k hk => Nat.le_floor (by exact_mod_cast hk₀ k hk)⟩

/-- **The node-3 part of `L53HbadBParts`, for every white noise** (DZZ l. 2425–2514), with
`q = 3/2`: closes `L53Node3PartAll` (S5L53FN3). -/
theorem l53_node3_part : L53Node3PartAll := by
  intro Ω _ P W hW γ hγ hγ2 αs _hαs u hu v hv huv
  obtain ⟨k₁, h₁⟩ := l53n3_cell_core hW hγ hγ2 αs hu hv huv
  obtain ⟨k₂, h₂⟩ := l53_node3_params αs 13
  obtain ⟨k₃, h₃⟩ := l53n3_thr_ev
  obtain ⟨k₄, h₄⟩ := l53n3_kap_ev
  obtain ⟨k₅, h₅⟩ := eventually_atTop.1 (l53n3_tendsto_L.eventually_gt_atTop 0)
  refine ⟨1.5, by norm_num, max (max k₁ k₂) (max (max k₃ k₄) k₅), fun k l hk hl hlk => ?_⟩
  simp only [max_le_iff] at hk
  obtain ⟨⟨hk1, hk2⟩, ⟨⟨hk3, hk4⟩, hk5⟩⟩ := hk
  obtain ⟨hK, hn, hnN, hNn, -, -, -, -, -, hroom, hβ⟩ := h₂ k hk2
  refine ⟨_, hβ, ?_⟩
  have hK' : 2 ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ = 2 * l53n3N k + 2 := hK
  -- `2^{127} ≤ N + 1`
  have hNbig : (2 : ℝ) ^ 127 ≤ l53n3N k + 1 := by
    have h1 : 2 ^ 128 ≤ 2 ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ :=
      Nat.pow_le_pow_right (by norm_num) (h₄ k hk4)
    rw [hK'] at h1
    have h2 : 2 ^ 127 ≤ l53n3N k + 1 := by omega
    exact_mod_cast h2
  -- the covering condition
  have hM1 : (1 : ℝ) ≤ l53n3M k := by
    have : 0 < l53n3M k := Nat.ceil_pos.2 (by have := h₅ k hk5; positivity)
    exact_mod_cast this
  have hNnR : (l53n3N k : ℝ) - l53n3n k = l53n3M k := by
    rw [← Nat.cast_sub hnN, hNn]
  have hpar : 20 * (2 * ((l53n3N k : ℝ) - l53n3n k) + 3 + 128 * l53n3M k) *
      (2 : ℝ)⁻¹ ^ ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊ <
        epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 := by
    rw [hNnR]
    set e := epsStarN αs ((2 : ℝ)⁻¹ ^ k)
    set κ := ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊
    have hroom' : (l53n3M k : ℝ) * (2 : ℝ) ^ (2 * e + 13) ≤ 2 ^ κ := hroom
    have he : epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * (2 : ℝ) ^ (2 * e) = 1 := by
      rw [epsStar, ← pow_mul, mul_comm e 2, ← mul_pow,
        inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    rw [pow_add] at hroom'
    have hε0 : 0 ≤ epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 := sq_nonneg _
    have hk2pos : (0 : ℝ) < (2 : ℝ) ^ κ := by positivity
    have key : (l53n3M k : ℝ) * 8192 ≤ epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 * 2 ^ κ := by
      have := mul_le_mul_of_nonneg_left hroom' hε0
      have e13 : (2 : ℝ) ^ 13 = 8192 := by norm_num
      rw [e13] at this
      nlinarith
    rw [inv_pow, ← div_eq_mul_inv, div_lt_iff₀ hk2pos]
    nlinarith
  exact h₁ k l hk1 hlk (l53n3N k) (l53n3n k) (l53n3M k) hK' hn hnN hNbig hpar
    (h₃ k hk3 _ hK')

end DZZ
end LQGMetric
