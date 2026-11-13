/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4LocalGreen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4HeatKernel

 















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

theorem killIter_pt_le_freeP (U : Finset (ℤ × ℤ)) (t : ℕ) (a b : ℤ × ℤ) :
    (killOp U)^[t] (pt U b) a ≤ freeP t a b := by
  refine (killIter_le_avgIter U t (pt_nonneg U b) a).trans ?_
  unfold freeP
  apply avgIter_mono
  intro c
  unfold pt
  split_ifs with h1 h2 <;> first | exact le_rfl | exact absurd h1.1 h2 | norm_num

theorem tsum_alive_le (U : Finset (ℤ × ℤ)) (z1 R : ℤ) (hU : ∀ c ∈ U, |c.1 - z1| < R)
    (a : ℤ × ℤ) : ∑' s, alive U s a ≤ 2 * (R : ℝ) ^ 2 :=
  Real.tsum_le_of_sum_range_le (fun s => alive_nonneg U s a) (sum_alive_le U z1 R hU · a)

 
theorem green_le_far (U : Finset (ℤ × ℤ)) (z1 R : ℤ) (hU : ∀ c ∈ U, |c.1 - z1| < R)
    (a b : ℤ × ℤ) (r : ℕ) (hr : 0 < r)
    (hab : (r : ℝ) ≤ |((b.1 - a.1 : ℤ) : ℝ)| ∨ (r : ℝ) ≤ |((b.2 - a.2 : ℤ) : ℝ)|) :
    green U a b ≤ 16 + 2 * (R : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
  set T : ℕ := r ^ 2 with hT
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hTr : (T : ℝ) = (r : ℝ) ^ 2 := by rw [hT]; push_cast; ring
  have hTpos : 0 < T := by positivity
  unfold green
  have hsum := summable_killIter_pt U b a
  rw [← hsum.sum_add_tsum_nat_add (2 * T)]
  
  have hearly : ∑ t ∈ range (2 * T), (killOp U)^[t] (pt U b) a ≤ 16 := by
    have hterm : ∀ t, (killOp U)^[t] (pt U b) a ≤ 8 / (r : ℝ) ^ 2 := by
      intro t
      have h1 := killIter_pt_le_freeP U t a b
      have h2 := freeP_mul_sq_le t a b r hrpos hab
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc ∑ t ∈ range (2 * T), (killOp U)^[t] (pt U b) a
        ≤ ∑ t ∈ range (2 * T), 8 / (r : ℝ) ^ 2 := Finset.sum_le_sum fun t _ => hterm t
      _ = (2 * T : ℕ) * (8 / (r : ℝ) ^ 2) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ = 16 := by
        push_cast
        rw [hTr]
        field_simp
        norm_num
  
  have hlate : ∑' s, (killOp U)^[s + 2 * T] (pt U b) a ≤ 2 * (R : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
    have hterm : ∀ s, (killOp U)^[s + 2 * T] (pt U b) a ≤ (1 / (T + 1 : ℝ)) * alive U s a := by
      intro s
      have hsplit : (killOp U)^[s + 2 * T] (pt U b) a =
          (killOp U)^[s + T] ((killOp U)^[T] (pt U b)) a := by
        rw [show s + 2 * T = (s + T) + T by ring, Function.iterate_add_apply]
      rw [hsplit]
      have hbd : ∀ c, (killOp U)^[T] (pt U b) c ≤ (1 / (T + 1 : ℝ)) * ind U c := by
        intro c
        by_cases hc : c ∈ U
        · have h1 := killIter_pt_le_freeP U T c b
          have h2 := freeP_mul_le T c b
          unfold ind
          rw [if_pos hc, mul_one, le_div_iff₀ (by positivity)]
          have : (killOp U)^[T] (pt U b) c * (T + 1) ≤ freeP T c b * (T + 1) := by
            gcongr
          linarith
        · rw [killIter_pt_of_not_mem U T b hc]
          unfold ind
          rw [if_neg hc, mul_zero]
      have h1 := killIter_le_alive U (s + T) hbd a
      have h2 := alive_anti U (Nat.le_add_right s T) a
      have h3 : (0 : ℝ) ≤ 1 / (T + 1 : ℝ) := by positivity
      calc (killOp U)^[s + T] ((killOp U)^[T] (pt U b)) a
          ≤ (1 / (T + 1 : ℝ)) * alive U (s + T) a := h1
        _ ≤ (1 / (T + 1 : ℝ)) * alive U s a := mul_le_mul_of_nonneg_left h2 h3
    have hsum2 : Summable fun s => (1 / (T + 1 : ℝ)) * alive U s a :=
      (summable_alive U a).mul_left _
    calc ∑' s, (killOp U)^[s + 2 * T] (pt U b) a
        ≤ ∑' s, (1 / (T + 1 : ℝ)) * alive U s a :=
          Summable.tsum_le_tsum hterm
            ((summable_nat_add_iff (f := fun t => (killOp U)^[t] (pt U b) a) (2 * T)).mpr hsum)
            hsum2
      _ = (1 / (T + 1 : ℝ)) * ∑' s, alive U s a := tsum_mul_left
      _ ≤ (1 / (T + 1 : ℝ)) * (2 * (R : ℝ) ^ 2) := by
          gcongr
          exact tsum_alive_le U z1 R hU a
      _ ≤ 2 * (R : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
          rw [← hTr]
          have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
          rw [div_mul_eq_mul_div, one_mul]
          apply div_le_div_of_nonneg_left (by positivity) hT0 (by linarith)
  linarith

end SupercriticalLQGUniqueness.B2.QPos.P4
