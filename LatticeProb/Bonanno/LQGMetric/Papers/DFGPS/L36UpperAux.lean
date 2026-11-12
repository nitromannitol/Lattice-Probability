/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperAux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperGood
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperProb

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Auxiliary bounds for the assembly of the upper half of DFGPS Lemma 3.6

Decision D52: choice of the number of dyadic boxes (`exists_scale`: the walk endpoint scale
`ρ = 2^{−N−2}` lies in `[δ^{1−a}, 2δ^{1−a})`) and the lengths of the two corner walks
(`≤ 2δ^{−a} + 3` vertices).
-/

noncomputable section

open Set

namespace LQGMetric.DFGPS.L36

lemma exists_scale {δ a : ℝ} (hδ : 0 < δ) (h : δ ^ (1 - a) ≤ 1/4) :
    ∃ N : ℕ, δ ^ (1 - a) ≤ rk (N + 1) ∧ rk (N + 1) < 2 * δ ^ (1 - a) := by
  have hp : 0 < δ ^ (1 - a) := Real.rpow_pos_of_pos hδ _
  have hx : 1 ≤ (δ ^ (1 - a))⁻¹ / 4 := by
    rw [le_div_iff₀ (by norm_num), one_mul, le_inv_comm₀ (by norm_num) hp]; linarith
  obtain ⟨N, h1, h2⟩ := exists_nat_pow_near hx one_lt_two
  refine ⟨N, ?_, ?_⟩
  · have e : rk (N + 1) = (4 * 2 ^ N)⁻¹ := by
      unfold rk; rw [one_div, inv_pow, pow_add, pow_add]; ring_nf
    rw [e, le_inv_comm₀ hp (by positivity)]
    rw [le_div_iff₀ (by norm_num)] at h1; linarith
  · have e : rk (N + 1) = (4 * 2 ^ N)⁻¹ := by
      unfold rk; rw [one_div, inv_pow, pow_add, pow_add]; ring_nf
    rw [e, inv_lt_comm₀ (by positivity) (by positivity)]
    rw [div_lt_iff₀ (by norm_num), pow_succ] at h2
    rw [mul_inv]
    nlinarith

lemma wlen_le {k k' : ℤ × ℤ} {D : ℝ} (h1 : |((k'.1 - k.1 : ℤ) : ℝ)| ≤ D)
    (h2 : |((k'.2 - k.2 : ℤ) : ℝ)| ≤ D) : (wlen k k' : ℝ) ≤ D := by
  unfold wlen
  rw [Nat.cast_max]
  refine max_le ?_ ?_
  · rw [Nat.cast_natAbs, Int.cast_abs]; exact h1
  · rw [Nat.cast_natAbs, Int.cast_abs]; exact h2

lemma abs_round_sub_le {δ x : ℝ} (hδ : 0 < δ) (k : ℤ) :
    |((round (x / δ) - k : ℤ) : ℝ)| ≤ |x / δ - k| + 1/2 := by
  have := abs_sub_round (x / δ)
  push_cast
  calc |(round (x / δ) : ℝ) - k| = |(x / δ - k) - (x / δ - round (x / δ))| := by ring_nf
    _ ≤ |x / δ - k| + |x / δ - round (x / δ)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- the left corner walk has `≤ ρ/δ + 3` vertices -/
lemma wlen_walkL_le {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ((wlen (1, 1) (rnd δ (xL (N + 1))) + 1 : ℕ) : ℝ) ≤ rk (N + 1) / δ + 3 := by
  have hρ := rk_pos (N + 1)
  have hre : (xL (N + 1)).re = rk (N + 1) := by simp [xL, aL]
  have him : (xL (N + 1)).im = rk (N + 1) := by simp [xL, aL]
  have hq : 0 ≤ rk (N + 1) / δ := by positivity
  have b : |rk (N + 1) / δ - ((1:ℤ):ℝ)| ≤ rk (N + 1) / δ + 1 := by
    rw [abs_le]; push_cast; constructor <;> linarith
  have := wlen_le (k := (1, 1)) (k' := rnd δ (xL (N + 1))) (D := rk (N + 1) / δ + 3/2)
    (by simp only [rnd, hre]; linarith [abs_round_sub_le (x := rk (N + 1)) hδ 1])
    (by simp only [rnd, him]; linarith [abs_round_sub_le (x := rk (N + 1)) hδ 1])
  push_cast; linarith

/-- the right corner walk has `≤ ρ/δ + 4` vertices -/
lemma wlen_walkR_le {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ((wlen (rnd δ (xR (N + 1))) (mR δ, 1) + 1 : ℕ) : ℝ) ≤ rk (N + 1) / δ + 4 := by
  have hρ := rk_pos (N + 1)
  have hre : (xR (N + 1)).re = 1 - rk (N + 1) := by simp [xR, aR]; ring
  have him : (xR (N + 1)).im = rk (N + 1) := by simp [xR, aR]
  have hq : 0 ≤ rk (N + 1) / δ := by positivity
  obtain ⟨m1, m2⟩ := mR_mul_bounds hδ
  have hm1 : 1 / δ - 1 ≤ (mR δ : ℝ) := by
    rw [div_sub_one hδ.ne', div_le_iff₀ hδ]; linarith
  have hm2 : (mR δ : ℝ) < 1 / δ := by rw [lt_div_iff₀ hδ]; linarith
  have e : (1 - rk (N + 1)) / δ = 1 / δ - rk (N + 1) / δ := by ring
  have c1 : |((mR δ - (rnd δ (xR (N + 1))).1 : ℤ) : ℝ)| ≤ rk (N + 1) / δ + 5/2 := by
    have := abs_round_sub_le (x := 1 - rk (N + 1)) hδ (mR δ)
    rw [abs_sub_comm] at this
    have h' : |((round ((1 - rk (N + 1)) / δ) - mR δ : ℤ) : ℝ)| =
        |((mR δ - (rnd δ (xR (N + 1))).1 : ℤ) : ℝ)| := by
      simp only [rnd, hre]; push_cast; rw [abs_sub_comm]
    rw [← h']
    refine (abs_round_sub_le (x := 1 - rk (N + 1)) hδ (mR δ)).trans ?_
    have : |(1 - rk (N + 1)) / δ - (mR δ : ℝ)| ≤ rk (N + 1) / δ + 2 := by
      rw [e, abs_le]; constructor <;> linarith
    linarith
  have c2 : |((1 - (rnd δ (xR (N + 1))).2 : ℤ) : ℝ)| ≤ rk (N + 1) / δ + 5/2 := by
    have h' : |((round (rk (N + 1) / δ) - 1 : ℤ) : ℝ)| =
        |((1 - (rnd δ (xR (N + 1))).2 : ℤ) : ℝ)| := by
      simp only [rnd, him]; push_cast; rw [abs_sub_comm]
    rw [← h']
    refine (abs_round_sub_le (x := rk (N + 1)) hδ 1).trans ?_
    have : |rk (N + 1) / δ - ((1:ℤ):ℝ)| ≤ rk (N + 1) / δ + 2 := by
      rw [abs_le]; push_cast; constructor <;> linarith
    linarith
  have := wlen_le (k := rnd δ (xR (N + 1))) (k' := (mR δ, 1)) c1 c2
  push_cast; linarith

end LQGMetric.DFGPS.L36
