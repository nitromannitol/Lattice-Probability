/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2Induction at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

 












set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j2_abstract_induction {Λ r V : ℕ → ℝ} {Ccmp cq Cv s : ℝ}
    (hCcmp : 0 < Ccmp) (hcq : 0 ≤ cq) (hCv : 0 ≤ Cv) (hs : 0 ≤ s)
    (hΛr : ∀ n, Λ n ≤ Ccmp * (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r)
    (hr0 : ∀ k, 0 ≤ r k) (hrV : ∀ k, r k ≤ Real.exp (cq * Real.sqrt (V k)))
    (hV0 : ∀ k, V k ≤ Cv * max (k : ℝ) 1)
    (hstep : ∀ C : ℝ, 0 ≤ C → ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K → ∀ k : ℕ, K ≤ k →
      Λ (k - K) ≤ Real.exp (C * Real.sqrt K) → V k ≤ (s + 1) * K) :
    ∃ K : ℕ, 1 ≤ K ∧ (∀ k, V k ≤ max (s + 1) Cv * K) ∧
      ∀ n, Λ n ≤ Real.exp ((cq * Real.sqrt (max (s + 1) Cv) + 1) * Real.sqrt K) := by
  set M : ℝ := max (s + 1) Cv with hM
  have hM0 : 0 ≤ M := le_trans (by linarith) (le_max_left _ _)
  set C : ℝ := cq * Real.sqrt M + 1 with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨K₁, hK₁⟩ := hstep C hC
  set K : ℕ := max (max K₁ 1) ⌈(|Real.log Ccmp|) ^ 2⌉₊ with hKdef
  have hKK₁ : K₁ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK1 : 1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hCcmpK : Ccmp ≤ Real.exp (Real.sqrt K) := by
    have h1 : (|Real.log Ccmp|) ^ 2 ≤ (K : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _ : _ ≤ K))
    have h2 : |Real.log Ccmp| ≤ Real.sqrt K := by
      rw [show |Real.log Ccmp| = Real.sqrt ((|Real.log Ccmp|) ^ 2) by
        rw [Real.sqrt_sq (abs_nonneg _)]]
      exact Real.sqrt_le_sqrt h1
    calc Ccmp = Real.exp (Real.log Ccmp) := (Real.exp_log hCcmp).symm
      _ ≤ Real.exp (Real.sqrt K) :=
          Real.exp_le_exp.mpr ((le_abs_self _).trans h2)
  
  have hVk : ∀ k : ℕ, (K ≤ k → Λ (k - K) ≤ Real.exp (C * Real.sqrt K)) → V k ≤ M * K := by
    intro k hk
    by_cases hkK : K ≤ k
    · exact (hK₁ K hKK₁ k hkK (hk hkK)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg K))
    · push_neg at hkK
      have hmax : max (k : ℝ) 1 ≤ K := max_le (by exact_mod_cast hkK.le) hK1r
      calc V k ≤ Cv * max (k : ℝ) 1 := hV0 k
        _ ≤ Cv * K := mul_le_mul_of_nonneg_left hmax hCv
        _ ≤ M * K := mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg K)
  have hrk : ∀ k : ℕ, V k ≤ M * K → r k ≤ Real.exp ((cq * Real.sqrt M) * Real.sqrt K) := by
    intro k hk
    refine (hrV k).trans (Real.exp_le_exp.mpr ?_)
    rw [mul_assoc, ← Real.sqrt_mul hM0]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hk) hcq
  
  have hclaim : ∀ n, Λ n ≤ Real.exp (C * Real.sqrt K) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hsup : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r ≤
          Real.exp ((cq * Real.sqrt M) * Real.sqrt K) := by
        refine Finset.sup'_le _ _ fun k hk => hrk k (hVk k fun hkK => ih (k - K) ?_)
        have := Finset.mem_range.1 hk
        omega
      calc Λ n ≤ Ccmp * (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r := hΛr n
        _ ≤ Real.exp (Real.sqrt K) * Real.exp ((cq * Real.sqrt M) * Real.sqrt K) :=
            mul_le_mul hCcmpK hsup
              (le_trans (hr0 0)
                (Finset.le_sup' r (Finset.mem_range.2 (Nat.succ_pos n))))
              (Real.exp_pos _).le
        _ = Real.exp (C * Real.sqrt K) := by rw [← Real.exp_add, hCdef]; ring_nf
  exact ⟨K, hK1, fun k => hVk k fun _ => hclaim _, hclaim⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
