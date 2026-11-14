/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RRegular
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate

 









set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneA4RSlack (ξ Q ζ : ℝ) : ℝ := ζ / (4 * (1 + (ξ + |Q|) / ξ))

theorem laneA4RSlack_pos {ξ Q ζ : ℝ} (hξ : 0 < ξ) (hζ : 0 < ζ) : 0 < laneA4RSlack ξ Q ζ := by
  unfold laneA4RSlack; positivity

 
theorem laneA4R_final_rate {ξ Q ζ E : ℝ} (hξ : 0 < ξ) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      let ζ₁ := laneA4RSlack ξ Q ζ
      let β := Q + (ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ
      let α := hitExponent ξ Q
      let g := ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) ^ 2 * (2 : ℝ) ^ ((ζ₁ - ξ * Q) * K) *
        Real.exp ((ξ * min ξ β - (min ξ β) ^ 2 / 2) * ((K : ℝ) * Real.log 2))
      let M := 2 * E + 4 * |α| + 4 * ζ + 8
      2 * g ^ 2 + 4 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E * K) ≤
        (2 : ℝ) ^ (-(2 * (α - ζ)) * K) := by
  set Λ := 2 + 2 * ((ξ + |Q|) / ξ) with hΛ
  obtain ⟨K₁, hK₁⟩ := laneC_sublinear_power_le (a := 2 / 3) (C := 2 * Λ) (ζ := ζ)
    (by norm_num) hζ
  obtain ⟨K₂, hK₂⟩ := exists_nat_gt (4 / ζ)
  refine ⟨max 1 (max K₁ K₂), le_max_left _ _, ?_⟩
  intro K hK
  intro ζ₁ β α g M
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hK0 : (0 : ℝ) < K := by linarith
  have hKK₁ : K₁ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKK₂ : (K₂ : ℝ) ≤ K := by
    exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  set a := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos (by norm_num)
  set x₀ := (K : ℝ) ^ (2 / 3 : ℝ)
  have hx₀ : (K : ℝ) ^ (-(1 / 3 : ℝ)) * K = x₀ := by
    rw [show (K : ℝ) ^ (-(1 / 3 : ℝ)) * K = (K : ℝ) ^ (-(1 / 3 : ℝ) + 1) by
      rw [Real.rpow_add hK0, Real.rpow_one]]
    norm_num [x₀]
  have hζ₁ : 0 < ζ₁ := laneA4RSlack_pos hξ hζ
  have hζ₁eq : ζ₁ * (1 + (ξ + |Q|) / ξ) = ζ / 4 := by
    simp only [ζ₁, laneA4RSlack]; field_simp
  
  set f : ℝ → ℝ := fun x => ξ * min ξ x - (min ξ x) ^ 2 / 2
  have hβQ : Q ≤ β := by
    simp only [β]
    have : 0 ≤ (ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ := by positivity
    linarith
  have hlip := laneA4R_hitProfile_lipschitz hξ hβQ
  have hcancel := laneA4_exponent_cancel ξ Q
  have hfβ : f β ≤ ξ * Q - α + (ξ + |Q|) * ((ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ) := by
    have e : β - Q = (ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ := by simp only [β]; ring
    simp only [f]
    rw [e] at hlip
    simp only [α]
    linarith
  
  have h2 : ∀ y : ℝ, (2 : ℝ) ^ y = Real.exp (y * a) := fun y => by
    rw [Real.rpow_def_of_pos (by norm_num), ha, mul_comm]
  set eg := 2 * x₀ + (ζ₁ - ξ * Q) * K + f β * K with heg
  have hg : g = (2 : ℝ) ^ eg := by
    simp only [g, eg, f]
    rw [h2, h2, h2, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1; push_cast; ring
  have hegle : eg ≤ -α * K + ζ / 4 * K + Λ * x₀ := by
    have h1 : f β * K ≤ (ξ * Q - α + (ξ + |Q|) * ((ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ)) * K :=
      mul_le_mul_of_nonneg_right hfβ hK0.le
    have e : (ξ * Q - α + (ξ + |Q|) * ((ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ)) * K =
        (ξ * Q - α) * K + ζ₁ * ((ξ + |Q|) / ξ) * K +
          2 * ((ξ + |Q|) / ξ) * ((K : ℝ) ^ (-(1 / 3 : ℝ)) * K) := by
      field_simp
      ring
    rw [e, hx₀] at h1
    have : ζ₁ * K + ζ₁ * ((ξ + |Q|) / ξ) * K = ζ / 4 * K := by
      rw [← hζ₁eq]; ring
    simp only [eg, Λ]
    nlinarith
  
  have hgood : 2 * g ^ 2 ≤ (2 : ℝ) ^ (-(2 * (α - ζ)) * K - 1) := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have hpow : (2 : ℝ) * (2 : ℝ) ^ (eg * ((2 : ℕ) : ℝ)) = (2 : ℝ) ^ (1 + eg * 2) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; norm_num
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hs := hK₁ K hKK₁
    have hK₂' : (4 / ζ : ℝ) < K := lt_of_lt_of_le hK₂ hKK₂
    have h4 : 4 ≤ ζ * K := by
      have := (div_lt_iff₀ hζ).mp hK₂'
      linarith
    nlinarith
  
  have hbad : 4 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E * K) ≤
      (2 : ℝ) ^ (-(2 * (α - ζ)) * K - 1) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [h4, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hα : α ≤ |α| := le_abs_self α
    simp only [M]
    nlinarith
  have hsum := add_le_add hgood hbad
  calc 2 * g ^ 2 + 4 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E * K)
      ≤ (2 : ℝ) ^ (-(2 * (α - ζ)) * K - 1) + (2 : ℝ) ^ (-(2 * (α - ζ)) * K - 1) := hsum
    _ = (2 : ℝ) ^ (-(2 * (α - ζ)) * K) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_one]; ring

end SupercriticalLQGUniqueness.B2.DG20Conc
