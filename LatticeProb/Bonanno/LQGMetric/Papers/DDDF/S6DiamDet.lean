/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamGeo
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable

/-!
# DDDF Prop 27, Step 1: the chaining inequality `eq:Chaining` (task P2-DDDF6d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1340–1345 (`eq:Chaining`); the argument is DF
(arXiv:1809.02607) l. 1013–1021, "(6.1)". For a continuous `f` and `n ≥ 0`, with `B k` a bound
on the crossing lengths of the `4 · 4^k` halves `2^{-(k+1)} R_{2,1}` (moved by `T20E.eH`,
`T20E.eV`) of the dyadic squares of side `2^{-k}` in `[0,1]²`, and `f ≤ M` on `[0,1]²`:

`D_f(x, y; [0,1]²) ≤ 2 e^{ξM} 4·2^{-n} + 8 Σ_{k ≤ n} 4 B k` for `x, y ∈ [0,1]²`
(`diam_chain_det`). DDDF state it with the long rectangles `2^{-k}(3,1)`, DF with the halves
`2^{-k-1}(2,1)` used here; the constants are not tracked in either.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E Blueprint

/-- the motions of the four halves of the dyadic square `(i, j)` of level `k` -/
def hm (k i j : ℕ) : Fin 4 → Circle × ℂ :=
  ![eH (k + 1) ((2 * i : ℕ) : ℤ) ((2 * j : ℕ) : ℤ), eH (k + 1) ((2 * i : ℕ) : ℤ) ((2 * j + 1 : ℕ) : ℤ),
    eV (k + 1) ((2 * i + 1 : ℕ) : ℤ) ((2 * j : ℕ) : ℤ),
    eV (k + 1) ((2 * i + 2 : ℕ) : ℤ) ((2 * j : ℕ) : ℤ)]

theorem sqSys_of_adm {k i j : ℕ} {γ : Fin 4 → ℝ → ℂ}
    (h : ∀ e, Adm21 (k + 1) (hm k i j e) (γ e)) :
    SqSys (2 * i * (2 : ℝ)⁻¹ ^ (k + 1)) (2 * j * (2 : ℝ)⁻¹ ^ (k + 1)) ((2 : ℝ)⁻¹ ^ (k + 1)) γ := by
  have h0 := adm_eH (h 0)
  have h1 := adm_eH (h 1)
  have h2 := adm_eV (h 2)
  have h3 := adm_eV (h 3)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Int.cast_mul,
    Int.cast_add, Int.cast_ofNat, Int.cast_one, Int.cast_natCast] at h0 h1 h2 h3
  set u : ℝ := (2 : ℝ)⁻¹ ^ (k + 1)
  refine ⟨fun e => ?_, h0.2.1, h0.2.2, ?_, h1.2.2, ?_, h2.2.2, ?_, h3.2.2⟩
  · obtain rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by fin_cases e <;> simp
    exacts [h0.1, h1.1, h2.1, h3.1]
  · intro t ht
    obtain ⟨a, b⟩ := h1.2.1 t ht
    exact ⟨a, ⟨by linarith [b.1], by linarith [b.2]⟩⟩
  · intro t ht
    obtain ⟨a, b⟩ := h2.2.1 t ht
    exact ⟨⟨by linarith [a.1], by linarith [a.2]⟩, b⟩
  · intro t ht
    obtain ⟨a, b⟩ := h3.2.1 t ht
    exact ⟨⟨by linarith [a.1], by linarith [a.2]⟩, b⟩

lemma idx_le {k i : ℕ} (hi : i < 2 ^ k) : ((i : ℝ) + 1) * (2 : ℝ)⁻¹ ^ k ≤ 1 := by
  have h1 : ((i : ℝ) + 1) ≤ 2 ^ k := by exact_mod_cast hi
  rw [inv_pow]
  rw [mul_inv_le_iff₀ (by positivity)]
  linarith

/-- the index of the column of level `n` containing `t ∈ [0,1]` -/
def colIdx (n : ℕ) (t : ℝ) : ℕ := min ⌊t * 2 ^ n⌋₊ (2 ^ n - 1)

lemma colIdx_lt (n : ℕ) (t : ℝ) : colIdx n t < 2 ^ n :=
  lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) one_pos)

lemma abs_sub_colIdx {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (colIdx n t : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ t ∧ t ≤ ((colIdx n t : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e : (2 : ℝ)⁻¹ ^ n = 1 / 2 ^ n := by rw [inv_pow, one_div]
  rw [e, ← mul_div_assoc, mul_one, ← mul_div_assoc, mul_one, div_le_iff₀ hp, le_div_iff₀ hp]
  have h0 : 0 ≤ t * 2 ^ n := by nlinarith [ht.1]
  unfold colIdx
  rcases le_total ⌊t * 2 ^ n⌋₊ (2 ^ n - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one _).le⟩
  · rw [min_eq_right h]
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have hc : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub h1]; push_cast; ring
    have hf : ((2 ^ n - 1 : ℕ) : ℝ) ≤ t * 2 ^ n := by
      have := Nat.floor_le h0
      exact le_trans (by exact_mod_cast h) this
    rw [hc] at hf ⊢
    constructor
    · exact hf
    · nlinarith [ht.2]

lemma colIdx_div_succ (n k : ℕ) (hk : k < n) (t : ℝ) :
    colIdx n t / 2 ^ (n - (k + 1)) / 2 = colIdx n t / 2 ^ (n - k) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]; congr 2; omega

lemma colIdx_div_lt {n k : ℕ} (hk : k ≤ n) (t : ℝ) : colIdx n t / 2 ^ (n - k) < 2 ^ k := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hk]
  exact colIdx_lt n t

end S6D
end DDDF
end LQGMetric
