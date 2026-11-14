/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatDyadicPairGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatDyadicPowerCompare

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_dyadic_pair_geometry
    (n₁ n₂ : ℕ) (s₁ s₂ δ₁ δ₂ : ℝ)
    (hs₁ : 0 < s₁) (hs₁' : s₁ ≤ 1)
    (hs₂ : 0 < s₂) (hs₂' : s₂ ≤ 1)
    (hδ₁ : δ₁ = (2 : ℝ) ^ (-((n₁ : ℝ) + s₁)))
    (hδ₂ : δ₂ = (2 : ℝ) ^ (-((n₂ : ℝ) + s₂)))
    (hδ : δ₁ < δ₂) :
    n₂ ≤ n₁ ∧
      δ₁ / δ₂ =
        (2 : ℝ) ^ (-(((n₁ - n₂ : ℕ) : ℝ) + s₁ - s₂)) := by
  have hn : n₂ ≤ n₁ := by
    by_contra hh
    have hnat : n₁ + 1 ≤ n₂ := by omega
    have hcast : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) := by exact_mod_cast hnat
    have hexp : -((n₂ : ℝ) + s₂) < -((n₁ : ℝ) + s₁) := by linarith
    have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
    rw [← hδ₁, ← hδ₂] at hpow
    exact (not_lt_of_ge hpow.le) hδ
  refine ⟨hn, ?_⟩
  rw [hδ₁, hδ₂, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [Nat.cast_sub hn]
  ring

end SupercriticalLQGUniqueness.B2.DG20Pt
