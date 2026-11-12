/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Geom

/-!
# DZZ Lemma 3.1 (cell sizes) (P2-DZZ3A, WP-113)

Ding–Zeitouni–Zhang (arXiv:1807.00422), Lemma 3.1 (`lem-partition-minimal-cell`, l. 799–803),
proof l. 833–848: for `γ ∈ (0, 2)` there are `C_mc, C_Mc > 0` depending only on `γ` such that with
high probability every cell of `𝒱_δ` has side in `[δ^{C_mc}, δ^{C_Mc}]`.

Proof (DZZ's union bound over the dyadic centers of one level, l. 836–846; the maximal-cell half
"follows from a similar (simple) computation", l. 847): with `ε = 2^{-k} ≤ δ^θ`,
`P(∃ B of level k, M_{γ,ε}(B) ≥ δ²) ≤ e^{2p(p−1)γ²} δ` (Chernoff with `p = (γ²+4)/(2γ²)`, the
exponent `(p−1)(2 − pγ²/2) = (4−γ²)²/(8γ²) > 0` exactly because `γ < 2`), and for the levels
`n ≤ K`, `2^{(5+γ²)K} ≤ δ⁻¹`, `P(∃ B of level ≤ K, M(B) < δ²) ≤ e^{4γ²} δ`. On the complement
the splitting halts by level `k` and never before level `K + 1` (`S3L1Geom`). We also record that
every point of `𝕍` lies in a cell (DZZ use this implicitly: `𝖢_{v,δ}` exists).

* `dzzCmc γ`, `dzzCMc γ = 1/(5+γ²)`: the constants `C_mc`, `C_Mc` (fixed for the rest of §3).
* `cellSizeEvent γ W δ`: the event of the lemma.
* `dzz_lemma31_bound`: `P(event ᶜ) ≤ (e^{2p(p−1)γ²} + e^{4γ²}) δ` for `δ ≤ 1/2`;
* `dzz_lemma31`: the event holds with high probability (`HighProb`, exponent `1/2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- Chernoff exponent of the minimal-cell bound. -/
def l31p (γ : ℝ) : ℝ := (γ ^ 2 + 4) / (2 * γ ^ 2)
/-- `(p − 1)(2 − pγ²/2)`. -/
def l31q (γ : ℝ) : ℝ := (4 - γ ^ 2) ^ 2 / (8 * γ ^ 2)
/-- `ε ≤ δ^θ` at the minimal level. -/
def l31theta (γ : ℝ) : ℝ := (2 * l31p γ + 1) / l31q γ

/-- **`C_mc`** of DZZ Lemma 3.1. -/
def dzzCmc (γ : ℝ) : ℝ := l31theta γ + 1
/-- **`C_Mc`** of DZZ Lemma 3.1. -/
def dzzCMc (γ : ℝ) : ℝ := 1 / (5 + γ ^ 2)

/-- The constant of `dzz_lemma31_bound`. -/
def l31const (γ : ℝ) : ℝ :=
  Real.exp (2 * l31p γ * (l31p γ - 1) * γ ^ 2) + Real.exp (4 * γ ^ 2)

lemma dzzCMc_pos (γ : ℝ) : 0 < dzzCMc γ := by unfold dzzCMc; positivity

lemma l31q_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < l31q γ := by
  unfold l31q
  have : 0 < 4 - γ ^ 2 := by nlinarith
  positivity

lemma l31theta_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < l31theta γ := by
  unfold l31theta l31p
  have := l31q_pos hγ hγ2
  positivity

lemma dzzCMc_le_dzzCmc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : dzzCMc γ ≤ dzzCmc γ := by
  have h1 : dzzCMc γ ≤ 1 := by
    unfold dzzCMc; rw [div_le_one (by positivity)]; nlinarith
  have := l31theta_pos hγ hγ2
  unfold dzzCmc; linarith

/-- The event of DZZ Lemma 3.1 (plus: every point of `𝕍` lies in a cell). -/
def cellSizeEvent {Ω : Type*} (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) : Set Ω :=
  {ω | (∀ v ∈ dzzV, ∃ b, IsCell (approxLQG γ W ω) δ b ∧ b.Mem v) ∧
    ∀ b, IsCell (approxLQG γ W ω) δ b → δ ^ dzzCmc γ ≤ b.side ∧ b.side ≤ δ ^ dzzCMc γ}

/-- The level-`n` box with column `j` and row `k`. -/
def levelBox (n : ℕ) (j k : Fin (2 ^ n)) : DyBox := ⟨n, j, k, j.2, k.2⟩

/-- Union bound over the `4ⁿ` boxes of level `n`. -/
lemma measureReal_level_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (n : ℕ) (S : DyBox → Set Ω) {B : ℝ} (hB : ∀ b : DyBox, b.n = n → P.real (S b) ≤ B) :
    P.real {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ S b} ≤ ((2 : ℝ) ^ n) ^ 2 * B := by
  have hsub : {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ S b} ⊆ ⋃ j, ⋃ k, S (levelBox n j k) := by
    rintro ω ⟨b, rfl, hb⟩
    exact mem_iUnion.2 ⟨⟨b.j, b.hj⟩, mem_iUnion.2 ⟨⟨b.k, b.hk⟩, hb⟩⟩
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc ∑ j, P.real (⋃ k, S (levelBox n j k)) ≤ ∑ _j : Fin (2 ^ n), ((2 : ℝ) ^ n * B) := by
        refine Finset.sum_le_sum fun j _ => (measureReal_iUnion_fintype_le _).trans ?_
        calc ∑ k, P.real (S (levelBox n j k)) ≤ ∑ _k : Fin (2 ^ n), B :=
              Finset.sum_le_sum fun k _ => hB _ rfl
          _ = (2 : ℝ) ^ n * B := by simp
    _ = ((2 : ℝ) ^ n) ^ 2 * B := by simp; ring

lemma two_pow_sq_eq (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = Real.exp (2 * n * Real.log 2) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2), Real.log_pow, Real.log_pow]
  push_cast; ring_nf

lemma side_ge_rpow {δ θ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hθ : 0 ≤ θ) {b : DyBox}
    (hb : (b.n : ℝ) ≤ ⌈θ * Real.log δ⁻¹ / Real.log 2⌉₊) : δ ^ (θ + 1) ≤ b.side := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log δ⁻¹ :=
    Real.log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) hδ0]; linarith)
  have hc := Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg hθ (hl2.le.trans hL)) hl2.le : (0 : ℝ) ≤ θ * Real.log δ⁻¹ / Real.log 2)
  rw [Real.rpow_def_of_pos hδ0, ← Real.exp_log b.side_pos, Real.exp_le_exp, log_side,
    Real.log_inv] at *
  have h1 : (b.n : ℝ) * Real.log 2 < θ * -Real.log δ + Real.log 2 := by
    have := mul_lt_mul_of_pos_right (hb.trans_lt hc) hl2
    rw [add_mul, div_mul_cancel₀ _ hl2.ne', one_mul] at this
    exact this
  nlinarith

lemma side_le_rpow {δ c : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1) (hc : 0 < c) {b : DyBox}
    (hb : ⌊Real.log δ⁻¹ / (c⁻¹ * Real.log 2)⌋₊ < b.n) : b.side ≤ δ ^ c := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos (by rw [lt_inv_comm₀ one_pos hδ0]; simpa)
  have hf := Nat.lt_floor_add_one (Real.log δ⁻¹ / (c⁻¹ * Real.log 2))
  have hn : Real.log δ⁻¹ / (c⁻¹ * Real.log 2) < b.n := by
    have : (⌊Real.log δ⁻¹ / (c⁻¹ * Real.log 2)⌋₊ : ℝ) + 1 ≤ b.n := by exact_mod_cast hb
    linarith
  rw [Real.rpow_def_of_pos hδ0, ← Real.exp_log b.side_pos, Real.exp_le_exp, log_side]
  rw [div_lt_iff₀ (by positivity), Real.log_inv] at hn
  have : -Real.log δ * c < b.n * Real.log 2 := by
    have := mul_lt_mul_of_pos_left hn hc
    have e : c * (↑b.n * (c⁻¹ * Real.log 2)) = b.n * Real.log 2 := by field_simp
    rw [e] at this
    linarith
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : WNSpace → Ω → ℝ}

/-- Minimal level `k = ⌈θ log δ⁻¹ / log 2⌉`: `P(∃ B of level k, M(B) ≥ δ²) ≤ e^{log δ + 2p(p−1)γ²}`
(DZZ (eq-010518a), l. 838–841). -/
lemma l31_min_level (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ}
    (hδ0 : 0 < δ) :
    P.real {ω | ∃ b : DyBox, b.n = ⌈l31theta γ * Real.log δ⁻¹ / Real.log 2⌉₊ ∧
      ω ∈ {ω | δ ^ 2 ≤ approxLQG γ W ω b}} ≤
      Real.exp (Real.log δ + 2 * l31p γ * (l31p γ - 1) * γ ^ 2) := by
  set k := ⌈l31theta γ * Real.log δ⁻¹ / Real.log 2⌉₊ with hk
  set p := l31p γ with hpdef
  have hp : 1 ≤ p := by
    rw [hpdef, l31p, le_div_iff₀ (by positivity)]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l := Real.log 2
  refine (measureReal_level_le k _ (B := Real.exp (2 * p * (-(k * l) - Real.log δ) +
      p * (p - 1) * γ ^ 2 / 2 * (-(-(k * l)) + 4))) fun b hb => ?_).trans ?_
  · refine (approxLQG_ge_tail hW hγ hδ0 hp b).trans (le_of_eq ?_)
    rw [Real.log_inv, log_side, hb]
  rw [two_pow_sq_eq, ← Real.exp_add, Real.exp_le_exp]
  have hq : l31q γ = 2 * p - 2 - p * (p - 1) * γ ^ 2 / 2 := by
    rw [hpdef]; unfold l31q l31p; field_simp; ring
  have hθq : l31theta γ * l31q γ = 2 * p + 1 := by
    unfold l31theta; rw [hpdef]; field_simp [(l31q_pos hγ hγ2).ne']
  have hx : l31theta γ * Real.log δ⁻¹ ≤ k * l := by
    have := Nat.le_ceil (l31theta γ * Real.log δ⁻¹ / l)
    rw [← hk, div_le_iff₀ hl2] at this
    exact this
  have hqx := mul_le_mul_of_nonneg_left hx (l31q_pos hγ hγ2).le
  rw [← mul_assoc, mul_comm (l31q γ), hθq, Real.log_inv] at hqx
  have key : 2 * (k : ℝ) * l + (2 * p * (-(k * l) - Real.log δ) +
      p * (p - 1) * γ ^ 2 / 2 * (-(-(k * l)) + 4)) =
      -(l31q γ * (k * l)) + 2 * p * (-Real.log δ) + 2 * p * (p - 1) * γ ^ 2 := by
    rw [hq]; ring
  rw [key]
  nlinarith

/-- Levels `n ≤ K`, `(5 + γ²) K log 2 ≤ log δ⁻¹`: `P(∃ B of level ≤ K, M(B) < δ²) ≤ e^{log δ + 4γ²}`
(DZZ l. 847, "similar (simple) computation"). -/
lemma l31_max_levels (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1) :
    P.real (⋃ n : Fin (⌊Real.log δ⁻¹ / ((dzzCMc γ)⁻¹ * Real.log 2)⌋₊ + 1),
      {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ {ω | approxLQG γ W ω b < δ ^ 2}}) ≤
      Real.exp (Real.log δ + 4 * γ ^ 2) := by
  set K := ⌊Real.log δ⁻¹ / ((dzzCMc γ)⁻¹ * Real.log 2)⌋₊ with hK
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l := Real.log 2
  have hKL : (5 + γ ^ 2) * K * l ≤ -Real.log δ := by
    have := Nat.floor_le (a := Real.log δ⁻¹ / ((dzzCMc γ)⁻¹ * l))
      (div_nonneg (Real.log_nonneg (by rw [le_inv_comm₀ one_pos hδ0]; simpa using hδ.le))
        (by unfold dzzCMc; positivity))
    rw [← hK, le_div_iff₀ (by unfold dzzCMc; positivity), Real.log_inv] at this
    unfold dzzCMc at this
    rw [one_div, inv_inv] at this
    linarith
  set E := Real.exp ((4 + γ ^ 2) * K * l + 2 * Real.log δ + 4 * γ ^ 2)
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc ∑ n : Fin (K + 1), P.real {ω | ∃ b : DyBox, b.n = n ∧
        ω ∈ {ω | approxLQG γ W ω b < δ ^ 2}}
      ≤ ∑ _n : Fin (K + 1), E := by
        refine Finset.sum_le_sum fun n _ => ?_
        refine (measureReal_level_le (n : ℕ) _ (B := Real.exp (2 * (Real.log δ - -(n * l)) +
          γ ^ 2 * (-(-(n * l)) + 4))) fun b hb => ?_).trans ?_
        · refine (approxLQG_lt_tail hW hγ hδ0 b).trans (le_of_eq ?_)
          rw [Real.log_inv, log_side, hb]
        rw [two_pow_sq_eq, ← Real.exp_add, Real.exp_le_exp]
        have hn : (n : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp n.2
        nlinarith [mul_le_mul_of_nonneg_right hn hl2.le]
    _ = (K + 1) * E := by simp
    _ ≤ Real.exp (K * l) * E := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h1 : ((K : ℝ) + 1) ≤ (2 : ℝ) ^ K := by exact_mod_cast Nat.lt_two_pow_self
        refine h1.trans (le_of_eq ?_)
        rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ K), Real.log_pow]
    _ ≤ Real.exp (Real.log δ + 4 * γ ^ 2) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        nlinarith

/-- **DZZ Lemma 3.1, quantitative form**: for `γ ∈ (0, 2)` and `δ ∈ (0, 1/2]`,
`P(some cell has side ∉ [δ^{C_mc}, δ^{C_Mc}] or some point of 𝕍 is in no cell) ≤ C(γ) δ`. -/
theorem dzz_lemma31_bound (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    P.real (cellSizeEvent γ W δ)ᶜ ≤ l31const γ * δ := by
  have hδ1 : δ < 1 := by linarith
  set k := ⌈l31theta γ * Real.log δ⁻¹ / Real.log 2⌉₊ with hk
  set K := ⌊Real.log δ⁻¹ / ((dzzCMc γ)⁻¹ * Real.log 2)⌋₊ with hK
  set S1 := {ω | ∃ b : DyBox, b.n = k ∧ ω ∈ {ω | δ ^ 2 ≤ approxLQG γ W ω b}}
  set S2 := ⋃ n : Fin (K + 1),
    {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ {ω | approxLQG γ W ω b < δ ^ 2}}
  have hsub : (cellSizeEvent γ W δ)ᶜ ⊆ S1 ∪ S2 := by
    rw [compl_subset_comm, compl_union]
    rintro ω ⟨h1, h2⟩
    have g1 : ∀ b : DyBox, b.n = k → approxLQG γ W ω b < δ ^ 2 := fun b hb => by
      by_contra h; exact h1 ⟨b, hb, not_lt.mp h⟩
    have g2 : ∀ b : DyBox, b.n ≤ K → δ ^ 2 ≤ approxLQG γ W ω b := fun b hb => by
      by_contra h
      exact h2 (mem_iUnion.2 ⟨⟨b.n, Nat.lt_succ_of_le hb⟩, b, rfl, not_le.mp h⟩)
    refine ⟨fun v hv => exists_isCell_of_level g1 hv, fun b hb => ⟨?_, ?_⟩⟩
    · have := IsCell.n_le_of_level g1 hb
      exact side_ge_rpow hδ0 hδ (l31theta_pos hγ hγ2).le (by exact_mod_cast this)
    · exact side_le_rpow hδ0 hδ1 (dzzCMc_pos γ) (IsCell.lt_n_of_levels g2 hb)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have e1 := l31_min_level hW hγ hγ2 hδ0 (P := P)
  have e2 := l31_max_levels hW hγ hδ0 hδ1 (P := P)
  rw [Real.exp_add, Real.exp_log hδ0] at e1 e2
  unfold l31const
  nlinarith

/-- **DZZ Lemma 3.1** (`lem-partition-minimal-cell`): with high probability every cell of `𝒱_δ`
has side length in `[δ^{C_mc}, δ^{C_Mc}]` (and every point of `𝕍` lies in a cell). The constants
`C_mc = dzzCmc γ`, `C_Mc = dzzCMc γ` and the probability bound depend only on `γ`. -/
theorem dzz_lemma31 (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    HighProb P (fun δ => cellSizeEvent γ W δ) := by
  have hC : 0 < l31const γ := by unfold l31const; positivity
  refine ⟨1 / 2, by norm_num, min (1 / 2) (1 / l31const γ ^ 2), by positivity, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 / 2 := hδ.2.le.trans (min_le_left _ _)
  have hδ2 : δ ≤ 1 / l31const γ ^ 2 := hδ.2.le.trans (min_le_right _ _)
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ((dzz_lemma31_bound hW hγ hγ2 hδ0 hδ1).trans ?_)
  rw [← Real.sqrt_eq_rpow]
  have hs : Real.sqrt δ ≤ 1 / l31const γ := by
    calc Real.sqrt δ ≤ Real.sqrt (1 / l31const γ ^ 2) := Real.sqrt_le_sqrt hδ2
      _ = 1 / l31const γ := by
        rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hC.le, Real.sqrt_one]
  have hsq := Real.mul_self_sqrt hδ0.le
  have h0 := Real.sqrt_nonneg δ
  calc l31const γ * δ = (l31const γ * Real.sqrt δ) * Real.sqrt δ := by rw [mul_assoc, hsq]
    _ ≤ 1 * Real.sqrt δ := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        rw [le_div_iff₀ hC] at hs; linarith
    _ = Real.sqrt δ := one_mul _

end DZZ
end LQGMetric
