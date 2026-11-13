/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5InductionEngine at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem repaired_induction_engine
    (P : ℕ → ℝ → Prop) (K : ℕ) (hK : 8 ≤ K)
    (F r₀ : ℝ) (hr₀ : 0 < r₀) (hFbase : 8 ≤ F * r₀)
    (hF : 8 ≤ F)
    (hmono : ∀ n R S, R ≤ S → P n S → P n R)
    (hbase : ∀ m, 4 ≤ m → P m r₀)
    (hstep : ∀ n, K + 3 ≤ n → ∀ R, 0 < R →
      (∀ m, n - K + 1 ≤ m → m ≤ n - (K + 1) / 2 → P m R) →
        P n (F * R)) :
    ∀ n, K + 3 ≤ n → P n ((2 : ℝ) ^ ((n : ℝ) / (K : ℝ))) := by
  intro n hn
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n ≤ 2 * K + 2
      · have hpred (m : ℕ) (hmlo : n - K + 1 ≤ m)
            (_hmhi : m ≤ n - (K + 1) / 2) : P m r₀ :=
          hbase m (by omega)
        have hp := hstep n hn r₀ hr₀ hpred
        have hcap : (n : ℝ) / (K : ℝ) ≤ 3 := by
          have hnk : n ≤ 3 * K := by omega
          have hnk' : (n : ℝ) ≤ 3 * (K : ℝ) := by exact_mod_cast hnk
          exact (div_le_iff₀ hKpos).2 (by nlinarith)
        have hpow : (2 : ℝ) ^ ((n : ℝ) / (K : ℝ)) ≤ 8 := by
          calc
            _ ≤ (2 : ℝ) ^ (3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hcap
            _ = 8 := by norm_num
        exact hmono n _ _ (hpow.trans hFbase) hp
      · have hlarge : 2 * K + 3 ≤ n := by omega
        let R : ℝ := (2 : ℝ) ^ ((n : ℝ) / (K : ℝ) - 1)
        have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
        have hpred (m : ℕ) (hmlo : n - K + 1 ≤ m)
            (hmhi : m ≤ n - (K + 1) / 2) : P m R := by
          have hmK : K + 3 ≤ m := by omega
          have hmlt : m < n := by omega
          have hmnow := ih m hmlt hmK
          have hmk : n ≤ m + K := by omega
          have hmk' : (n : ℝ) ≤ (m : ℝ) + (K : ℝ) := by exact_mod_cast hmk
          have hexp : (n : ℝ) / (K : ℝ) - 1 ≤
              (m : ℝ) / (K : ℝ) := by
            apply (le_div_iff₀ hKpos).2
            have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
            field_simp
            nlinarith
          have hRle : R ≤ (2 : ℝ) ^ ((m : ℝ) / (K : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
          exact hmono m R _ hRle hmnow
        have hp := hstep n hn R hR hpred
        have hpow : (2 : ℝ) ^ ((n : ℝ) / (K : ℝ)) = 2 * R := by
          dsimp [R]
          rw [show (n : ℝ) / (K : ℝ) =
            1 + ((n : ℝ) / (K : ℝ) - 1) by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          norm_num
        have hfactor : 2 * R ≤ F * R := by
          nlinarith [hR.le]
        exact hmono n _ _ (hpow.le.trans hfactor) hp

end SupercriticalLQGUniqueness.B2.QPos
