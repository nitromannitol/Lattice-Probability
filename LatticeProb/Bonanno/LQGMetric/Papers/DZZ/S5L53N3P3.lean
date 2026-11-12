/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53N3P3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N3P2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GB5

/-!
# DZZ Lemma 5.3, node 3: the parameters `(K, N, n, j, θ)` (P2-DZZ53N3P)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2502–2514; AUDIT-2026-10-03-N row N11 and §3,
AUDIT-2026-10-03-P row P6 (grid count = cut-off = `K_L`); handoffs P2-DZZ53GB, P2-DZZ53NUM.
With `L = k log 2`:
* `κ = ⌊L^{0.51}⌋₊`, `K = 2^κ = 2N + 2` (`N = 2^{κ-1} - 1`, the `l53Sub` grid of GB4/GB5),
  cut-off threshold `K⁻¹ μH¹(∂𝖡)` (NU3 as is);
* `M = ⌈L²⌉₊`, `n = N - M` (so `N - n = M`, first Peierls term `≤ 4K 2^{-L²}`), `j = M`;
* `θ = 1/16`, per-site `ε = 2 · 2K⁻⁴ · K² = 4K⁻²` (NU3 / P56 `l53_site_bound_eq`).
`l53_node3_params`: the side conditions of GB5 (`8θ ≤ 1/2`, `ε ≤ θ^{64}`, `8 ≤ K`), the
hypotheses `2^κ = 2N+2`, `N - n ≤ M`, `8(M+2) ≤ 2^κ` of P56's `l53_box_rhs_le_KL` (S5L53P56A,
not imported), `K ≥ 40/ε*²` (for `hcardP`), the room `j 2^{2n_{ε*}+c} ≤ K` (for `hcovP`,
`hcovN`), and the closed-form bound `4(2N+1)2^{-(N-n+1)} + 32·2^{-j} ≤ e^{-L^{1.5}}`.
Deviation from N11's suggestion: `j = ⌈L²⌉` instead of `j ≍ ε*² K/400` (any `j` with
`j ≥ L^{1.5}/log 2 + 5` and `j ≲ ε*² K` works; the smaller `j` makes `hcovP`/`hcovN` easier,
and `j 2^{2n_{ε*}+c} ≤ K` is provided for them). Own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `κ = ⌊L^{0.51}⌋₊`, `L = k log 2`. -/
def l53n3Kap (k : ℕ) : ℕ := ⌊((k : ℝ) * Real.log 2) ^ (0.51 : ℝ)⌋₊

/-- `N = 2^{κ-1} - 1`, so that `2^κ = 2N + 2`. -/
def l53n3N (k : ℕ) : ℕ := 2 ^ (l53n3Kap k - 1) - 1

/-- `M = ⌈L²⌉₊` (the depth `N - n` and the Peierls exponent `j`). -/
def l53n3M (k : ℕ) : ℕ := ⌈((k : ℝ) * Real.log 2) ^ 2⌉₊

/-- `n = N - M`. -/
def l53n3n (k : ℕ) : ℕ := l53n3N k - l53n3M k

/-- The per-site bound `ε = 2 · 2K⁻⁴ · K²` of NU3 (cut-off `K = 2^κ`). -/
def l53n3Eps (k : ℕ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (2 * ((2 : ℝ) ^ l53n3Kap k)⁻¹ ^ 4) *
    ENNReal.ofReal ((2 : ℝ) ^ l53n3Kap k) ^ 2

/-- (Proof copied from P56's `l53_site_bound_eq`, S5L53P56A.) -/
lemma l53n3Eps_eq (k : ℕ) : l53n3Eps k =
    ENNReal.ofReal (4 * (((2 : ℝ) ^ l53n3Kap k)⁻¹) ^ 2) := by
  have hK : (0 : ℝ) < 2 ^ l53n3Kap k := by positivity
  rw [l53n3Eps, ← ENNReal.ofReal_pow hK.le, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

lemma l53n3_inv_two_pow (a : ℕ) : (2⁻¹ : ℝ≥0∞) ^ a = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ a) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num

/-- **The node-3 parameters** (DZZ l. 2502–2514, AUDIT-N N11, AUDIT-P P6): for every `c`, for
all large `k`, the choice above satisfies the side conditions of `l53_box_desirable_prob_proxy`
(S5L53GB5) at cut-off `K`, the hypotheses of `l53_box_rhs_le_KL` (S5L53P56A) with `c := M`,
`K ≥ 40/ε*²`, the room `j 2^{2n_{ε*}+c} ≤ K`, and the closed-form Peierls bound is
`≤ e^{-L^{1.5}}`. -/
theorem l53_node3_params (αs : ℝ) (c : ℕ) : ∃ k₀ : ℕ, ∀ k ≥ k₀,
    2 ^ l53n3Kap k = 2 * l53n3N k + 2 ∧ 1 ≤ l53n3n k ∧ l53n3n k ≤ l53n3N k ∧
    l53n3N k - l53n3n k = l53n3M k ∧
    8 * ((l53n3M k : ℝ) + 2) ≤ (2 : ℝ) ^ l53n3Kap k ∧
    (8 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ l53n3Kap k) ∧
    40 / epsStar αs ((2 : ℝ)⁻¹ ^ k) ^ 2 ≤ (2 : ℝ) ^ l53n3Kap k ∧
    8 * (16⁻¹ : ℝ≥0∞) ≤ 2⁻¹ ∧
    l53n3Eps k ≤ (16⁻¹ : ℝ≥0∞) ^ ((7 + 1) ^ 2) ∧
    (l53n3M k : ℝ) * (2 : ℝ) ^ (2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) + c) ≤ 2 ^ l53n3Kap k ∧
    4 * ((2 * l53n3N k + 1 : ℕ) * (2⁻¹ : ℝ≥0∞) ^ (l53n3N k - l53n3n k + 1)) +
        32 * (2⁻¹ : ℝ≥0∞) ^ l53n3M k ≤
      ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1.5 : ℝ))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨L₁, hL₁⟩ := l53n3_ev_room αs (c + 136)
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 (l53n3_ev_beta.and (eventually_ge_atTop (1 : ℝ)))
  have hLk : Tendsto (fun k : ℕ => (k : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hl2
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hLk.eventually (eventually_ge_atTop (max L₁ L₂)))
  refine ⟨k₀, fun k hk => ?_⟩
  set L : ℝ := (k : ℝ) * Real.log 2 with hLdef
  have hL := hk₀ k hk
  obtain ⟨hβ, hL1⟩ := hL₂ L ((le_max_right _ _).trans hL)
  have hroom := hL₁ k ((le_max_left _ _).trans hL)
  rw [← hLdef] at hroom
  set κ := l53n3Kap k with hκdef
  set e := epsStarN αs ((2 : ℝ)⁻¹ ^ k) with hedef
  set M := l53n3M k with hMdef
  have hroom' : (L ^ 2 + 2) * (2 : ℝ) ^ (2 * e + (c + 136)) ≤ 2 ^ κ := hroom
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hexp : 2 * e + (c + 136) ≤ κ := by
    refine (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 ?_
    have : (0 : ℝ) < 2 ^ (2 * e + (c + 136)) := by positivity
    nlinarith
  have hKN : 2 ^ κ = 2 * l53n3N k + 2 := by
    obtain ⟨κ', hκ'⟩ : ∃ κ', κ = κ' + 1 := ⟨κ - 1, by omega⟩
    have h1 : 1 ≤ 2 ^ κ' := Nat.one_le_two_pow
    rw [l53n3N, ← hκdef, hκ', Nat.add_sub_cancel, pow_succ]
    omega
  have hKNR : (2 : ℝ) ^ κ = 2 * l53n3N k + 2 := by exact_mod_cast hKN
  have hMlt : (M : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hML : L ^ 2 ≤ M := Nat.le_ceil _
  have h16 : (16 : ℝ) ≤ 2 ^ (2 * e + (c + 136)) := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have h8M : 8 * ((M : ℝ) + 2) ≤ 2 ^ κ := by nlinarith
  have hNM : M + 1 ≤ l53n3N k := by
    have : (M : ℝ) + 1 < l53n3N k + 1 := by nlinarith
    have : (M : ℝ) < l53n3N k := by linarith
    exact_mod_cast this
  have hn1 : 1 ≤ l53n3n k := by rw [l53n3n]; omega
  have hnN : l53n3n k ≤ l53n3N k := Nat.sub_le _ _
  have hNn : l53n3N k - l53n3n k = M := by rw [l53n3n]; omega
  have h136 : (2 : ℝ) ^ (2 * e + 136) ≤ 2 ^ κ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK136 : (2 : ℝ) ^ 136 ≤ 2 ^ κ := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨hKN, hn1, hnN, hNn, h8M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `8 ≤ K`
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num]
    exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num) hK136)
  · -- `40/ε*² ≤ K`
    rw [epsStar, ← hedef, inv_pow, inv_pow, div_inv_eq_mul]
    refine le_trans ?_ h136
    rw [pow_add, pow_mul, show ((2 : ℝ) ^ e) ^ 2 = (2 ^ 2) ^ e by
      rw [← pow_mul, ← pow_mul, mul_comm]]
    have : (0 : ℝ) ≤ (2 ^ 2) ^ e := by positivity
    nlinarith
  · -- `8θ ≤ 1/2`
    rw [show (16 : ℝ≥0∞) = 2 * 8 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      mul_comm (2⁻¹ : ℝ≥0∞), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  · -- `ε ≤ θ^{64}`
    rw [l53n3Eps_eq, show (16⁻¹ : ℝ≥0∞) = ENNReal.ofReal 16⁻¹ by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num, ← ENNReal.ofReal_pow (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hi : ((2 : ℝ) ^ κ)⁻¹ ≤ ((2 : ℝ) ^ 136)⁻¹ := inv_anti₀ (by positivity) hK136
    calc 4 * ((2 : ℝ) ^ κ)⁻¹ ^ 2 ≤ 4 * ((2 : ℝ) ^ 136)⁻¹ ^ 2 := by gcongr
      _ ≤ (16⁻¹ : ℝ) ^ ((7 + 1) ^ 2) := by norm_num
  · -- the room for `j`
    calc (M : ℝ) * (2 : ℝ) ^ (2 * e + c) ≤ (L ^ 2 + 2) * (2 : ℝ) ^ (2 * e + (c + 136)) := by
          gcongr
          · linarith
          · norm_num
          · omega
      _ ≤ _ := hroom'
  · -- the closed-form bound
    have hKe : (2 * (l53n3N k : ℝ) + 2) ≤ Real.exp (L ^ (0.51 : ℝ)) := by
      rw [← hKNR]; exact l53nu_two_pow_floor_le (by positivity)
    have hb := hβ (l53n3N k) M hKe hML
    rw [hNn, l53n3_inv_two_pow, l53n3_inv_two_pow, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      show (32 : ℝ≥0∞) = ENNReal.ofReal 32 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    exact hb

end DZZ
end LQGMetric
