/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L13A at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DG Lemma 3.13: the exponent bookkeeping (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.13
(`lem-rectangle-dist`, DG:1282–1312), the chain of inequalities (eqn-rectangle-dist-T)
(DG:1303–1309): on the event (eqn-use-mid-scale-compare) (DG:1296–1299),
`T_R ≥ 2^{(2+γ²/2+o(1))m} exp(−γ (d−ζ̃)/d · min_{R'} ĥ_{2^{-m}})`, so that the bound of
Lemma 3.11 at `T_R ε` and `n = 2^k` is at most the bound (eqn-rectangle-dist).

Here this is one deterministic inequality `l313_thr_le_tgt` between DG's threshold
`n² max{A, e^{√n} (T ε)^{-1/(d−ζ₁)}}`, `T = s^{-(2+γ²/2)} e^{−γ M}`, `s = 2^{-(m+k)}`, and
DG's target `max{m³, ε^{-1/(d−ζ)} 2^{-(2+γ²/2−ζ)m/d} e^{(γ/d) m₀}}`, for `M ≤ m₀ + ζ̃ m log 2`
(DG's second inequality of (eqn-use-mid-scale-compare)) and `|m₀| ≤ (2+ζ̃) m log 2` (the first).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DG

open Real

/-- DG's threshold in Lemma 3.11 at `T_R ε` (DG:1305–1310): `n = 2^k`, `s = 2^{-(m+k)}`,
`T = s^{-(2+γ²/2)} e^{−γ M}` with `M = max_{R'} ĥ_s` -/
def l313Thr (A γ d ζ₁ ε : ℝ) (m k : ℕ) (M : ℝ) : ℝ :=
  ((2 : ℝ) ^ k) ^ 2 * max A (Real.exp (√((2 : ℝ) ^ k)) *
    (ε * (((2 : ℝ)⁻¹ ^ (m + k)) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * M))) ^ (-(1 / (d - ζ₁))))

/-- DG's bound (eqn-rectangle-dist) (DG:1287–1290), with `m₀ = min_{R'} ĥ_{2^{-m}}` -/
def l313Tgt (γ d ζ ε : ℝ) (m : ℕ) (m₀ : ℝ) : ℝ :=
  max ((m : ℝ) ^ 3) (ε ^ (-(1 / (d - ζ))) * (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - ζ) * m / d)) *
    Real.exp (γ / d * m₀))

lemma log_two_pow_le_sqrt (k : ℕ) : (k : ℝ) * Real.log 2 ≤ 2 * √((2 : ℝ) ^ k) := by
  have h := Real.log_le_rpow_div (x := (2 : ℝ) ^ k) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_pow] at h
  rw [Real.sqrt_eq_rpow]
  linarith

/-- **the deterministic step of DG Lemma 3.13** (DG:1303–1310) -/
theorem l313_thr_le_tgt {A γ d ζ ζ₁ ζt ε M m₀ : ℝ} {m k : ℕ} (hγ : 0 < γ) (hd : 0 < d)
    (hζ₁ : 0 ≤ ζ₁) (hζ₁ζ : ζ₁ ≤ ζ) (hζd : ζ < d)
    (hkey : 1 / (d - ζ₁) * γ * ζt + γ * (1 / (d - ζ₁) - 1 / d) * (2 + ζt) ≤ ζ / (2 * d))
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hnA : ((2 : ℝ) ^ k) ^ 2 * A ≤ (m : ℝ) ^ 3)
    (hn : 5 * √((2 : ℝ) ^ k) ≤ ζ * Real.log 2 / (2 * d) * m)
    (hM : M ≤ m₀ + ζt * m * Real.log 2) (hm₀ : |m₀| ≤ (2 + ζt) * m * Real.log 2) :
    l313Thr A γ d ζ₁ ε m k M ≤ l313Tgt γ d ζ ε m m₀ := by
  unfold l313Thr l313Tgt
  rw [mul_max_of_nonneg _ _ (by positivity)]
  refine max_le_max hnA ?_
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set n : ℝ := (2 : ℝ) ^ k with hn_def
  have hdz₁ : 0 < d - ζ₁ := by linarith
  have hdz : 0 < d - ζ := by linarith
  set α₁ := 1 / (d - ζ₁) with hα₁
  set α := 1 / (d - ζ) with hα
  have hα₁α : α₁ ≤ α := one_div_le_one_div_of_le hdz (by linarith)
  have hα₁d : 1 / d ≤ α₁ := one_div_le_one_div_of_le hdz₁ (by linarith)
  set ξ := 2 + γ ^ 2 / 2 with hξ
  have hξ0 : 0 < ξ := by positivity
  have hs : 0 < ((2 : ℝ)⁻¹ ^ (m + k)) := by positivity
  have hx : 0 < ε * (((2 : ℝ)⁻¹ ^ (m + k)) ^ ξ)⁻¹ * Real.exp (-(γ * M)) := by positivity
  have hlogx : Real.log (ε * (((2 : ℝ)⁻¹ ^ (m + k)) ^ ξ)⁻¹ * Real.exp (-(γ * M))) =
      Real.log ε + ξ * ((m + k) * L) - γ * M := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hε.ne' (by positivity),
      Real.log_inv, Real.log_rpow hs, Real.log_pow, Real.log_inv, Real.log_exp]
    push_cast; ring
  have hn2 : n ^ 2 = Real.exp (2 * (k * L)) := by
    rw [hn_def, ← pow_mul, show (2 : ℝ) ^ (k * 2) = Real.exp (Real.log 2 * ((k * 2 : ℕ) : ℝ)) by
      rw [← Real.rpow_def_of_pos (by norm_num), Real.rpow_natCast]]
    push_cast; congr 1; rw [hL]; ring
  rw [Real.rpow_def_of_pos hx, hlogx, hn2, Real.rpow_def_of_pos hε,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  -- linear bookkeeping (DG:1303–1309)
  have hle : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have h1 : α₁ * Real.log ε ≥ α * Real.log ε := mul_le_mul_of_nonpos_right hα₁α hle
  have hmL : 0 ≤ (m : ℝ) * L := by positivity
  have h2 : α₁ * (ξ * ((m + k) * L)) ≥ 1 / d * (ξ * (m * L)) := by
    have : ξ * (m * L) ≤ ξ * ((m + k) * L) := by
      have : (m : ℝ) * L ≤ (m + k) * L := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      exact mul_le_mul_of_nonneg_left this hξ0.le
    exact mul_le_mul hα₁d this (by positivity) (by positivity)
  have h3 : α₁ * (γ * M) ≤ α₁ * (γ * (m₀ + ζt * m * L)) := by
    have : 0 < α₁ := by positivity
    gcongr
  have h4 : γ * (α₁ - 1 / d) * m₀ ≤ γ * (α₁ - 1 / d) * ((2 + ζt) * m * L) := by
    have : 0 ≤ γ * (α₁ - 1 / d) := mul_nonneg hγ.le (by linarith)
    exact mul_le_mul_of_nonneg_left ((le_abs_self m₀).trans hm₀) this
  have h5 : (α₁ * γ * ζt + γ * (α₁ - 1 / d) * (2 + ζt)) * (m * L) ≤ ζ / (2 * d) * (m * L) :=
    mul_le_mul_of_nonneg_right hkey hmL
  have h6 := log_two_pow_le_sqrt k
  have hdd : ζ / (2 * d) * (m * L) = ζ * L / (2 * d) * m := by ring
  have hz : ((2 + ζ - ζ) * m / d) = 2 * m / d := by ring
  have e7 : -((ξ - ζ) * m / d) * L = -(1 / d * (ξ * (m * L))) + ζ / d * (m * L) := by
    field_simp; ring
  have e8 : γ / d * m₀ = α₁ * γ * m₀ - γ * (α₁ - 1 / d) * m₀ := by ring
  have e9 : ζ / d * (m * L) = 2 * (ζ / (2 * d) * (m * L)) := by field_simp
  rw [show L * -((ξ - ζ) * m / d) = -((ξ - ζ) * m / d) * L by ring, e7, e8]
  linarith [h1, h2, h3, h4, h5, h6, hn, hdd, e9]

/-- DG's choice "`ζ̃` sufficiently small" (DG:1310): one small `t` serves as `ζ₁` (the `ζ` of
Lemma 3.11) and as `ζ̃` (the slack of (eqn-use-mid-scale-compare)) -/
lemma l313_exists_param {γ d ζ : ℝ} (hd : 0 < d) (hζ : 0 < ζ) :
    ∃ t : ℝ, 0 < t ∧ t < ζ ∧ t ≤ 1 / 2 ∧
      1 / (d - t) * γ * t + γ * (1 / (d - t) - 1 / d) * (2 + t) ≤ ζ / (2 * d) := by
  have hc : ContinuousAt (fun t : ℝ => 1 / (d - t) * γ * t + γ * (1 / (d - t) - 1 / d) * (2 + t))
      0 := by
    have : (d - 0 : ℝ) ≠ 0 := by simpa using hd.ne'
    fun_prop (disch := assumption)
  have h0 : (fun t : ℝ => 1 / (d - t) * γ * t + γ * (1 / (d - t) - 1 / d) * (2 + t)) 0 = 0 := by
    simp
  have hev := hc.eventually (gt_mem_nhds (a := ζ / (2 * d)) (by rw [h0]; positivity))
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t ∧ t < ζ ∧ t ≤ 1 / 2 ∧
      1 / (d - t) * γ * t + γ * (1 / (d - t) - 1 / d) * (2 + t) < ζ / (2 * d) := by
    have h1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < min ζ (1 / 2) :=
      nhdsWithin_le_nhds (gt_mem_nhds (by positivity))
    filter_upwards [h1, h2, nhdsWithin_le_nhds hev] with t h1 h2 h3
    exact ⟨h1, h2.trans_le (min_le_left _ _), (h2.trans_le (min_le_right _ _)).le, h3⟩
  obtain ⟨t, h1, h2, h3, h4⟩ := hev'.exists
  exact ⟨t, h1, h2, h3, h4.le⟩

/-- `c m < exp((m L)^{1−t})` for `t ≤ 1/2` and `m` large (the range `A < e^{(log δ⁻¹)^{1−ζ}}` of
Lemma 3.6 for `A = 2^{n_m}`, DG:1296) -/
lemma l313_lt_exp {c L t x : ℝ} (hc : 0 < c) (hL : 0 < L) (ht : t ≤ 1 / 2)
    (hx1 : 1 ≤ x * L) (hx : 64 * c < x * L ^ 2) : c * x < Real.exp ((x * L) ^ (1 - t)) := by
  have hx0 : 0 < x := by
    by_contra h; rw [not_lt] at h; nlinarith [sq_nonneg L]
  set y := √(x * L) with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyy : y ^ 2 = x * L := Real.sq_sqrt (by positivity)
  have h1 : y ≤ (x * L) ^ (1 - t) := by
    rw [hy, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : (y / 2) ^ 2 / 2 ≤ Real.exp (y / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := y / 2) (by positivity)
    nlinarith
  have h3 : ((y / 2) ^ 2 / 2) ^ 2 ≤ Real.exp y := by
    have : Real.exp y = Real.exp (y / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h4 : ((y / 2) ^ 2 / 2) ^ 2 = (x * L) ^ 2 / 64 := by rw [← hyy]; ring
  have h5 : c * x < (x * L) ^ 2 / 64 := by
    have : (x * L) ^ 2 / 64 = x * (x * L ^ 2) / 64 := by ring
    rw [this]
    have := mul_lt_mul_of_pos_left hx hx0
    linarith
  calc c * x < (x * L) ^ 2 / 64 := h5
    _ ≤ Real.exp y := h4 ▸ h3
    _ ≤ _ := Real.exp_le_exp.2 h1

end DG
end LQGMetric
