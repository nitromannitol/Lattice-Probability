/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceCutoffRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1TwoRateAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

def j1CutoffRate (ξ c cg : ℝ) : ℝ :=
  min (c / 4) (cg * (1 / (2 * ξ))^2)

theorem j1_cutoff_rate_pos {ξ c cg : ℝ}
    (hξ : 0 < ξ) (hc : 0 < c) (hcg : 0 < cg) :
    0 < j1CutoffRate ξ c cg := by
  dsimp [j1CutoffRate]
  apply lt_min
  · positivity
  · positivity

theorem j1_cutoff_half_lower_fine_rate
    (ξ c cg D T : ℝ) (hξ : 0 < ξ) (hc : 0 < c) (hcg : 0 < cg)
    (hD : 0 < D) (hT : 0 < T) :
    Real.exp (-c * (Real.log (T^(1 / 2 : ℝ)))^2 / D) ≤
      Real.exp (-j1CutoffRate ξ c cg * (Real.log T)^2 / D) := by
  rw [Real.log_rpow hT]
  have hcoef : j1CutoffRate ξ c cg ≤ c / 4 := min_le_left _ _
  apply Real.exp_le_exp.mpr
  have hsq : 0 ≤ (Real.log T)^2 := sq_nonneg _
  apply (div_le_div_iff_of_pos_right hD).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcoef hsq]

theorem j1_cutoff_gaussian_lower_rate
    (ξ c cg D T : ℝ) (hξ : 0 < ξ) (hc : 0 < c) (hcg : 0 < cg)
    (hD : 1 ≤ D) :
    Real.exp (-(cg * ((1 / (2 * ξ) : ℝ) * Real.log T)^2)) ≤
      Real.exp (-j1CutoffRate ξ c cg * (Real.log T)^2 / D) := by
  have hrate : 0 < j1CutoffRate ξ c cg :=
    j1_cutoff_rate_pos hξ hc hcg
  have hDpos : 0 < D := by linarith
  have hcoef : j1CutoffRate ξ c cg ≤
      cg * (1 / (2 * ξ))^2 := min_le_right _ _
  have hcoef' : j1CutoffRate ξ c cg / D ≤
      cg * (1 / (2 * ξ))^2 := by
    calc
      _ ≤ j1CutoffRate ξ c cg := div_le_self hrate.le hD
      _ ≤ _ := hcoef
  apply Real.exp_le_exp.mpr
  have hsq : 0 ≤ (Real.log T)^2 := sq_nonneg _
  have hh := mul_le_mul_of_nonneg_right hcoef' hsq
  calc
    -(cg * ((1 / (2 * ξ) : ℝ) * Real.log T)^2) =
        -(cg * (1 / (2 * ξ))^2 * (Real.log T)^2) := by ring
    _ ≤ -(j1CutoffRate ξ c cg / D * (Real.log T)^2) := by linarith
    _ = -j1CutoffRate ξ c cg * (Real.log T)^2 / D := by ring

theorem j1_cutoff_half_upper_fine_rate
    (ξ c cg D T : ℝ) (hξ : 0 < ξ) (hc : 0 < c) (hcg : 0 < cg)
    (hD : 0 < D) (hT : 1 < T)
    (hll' : 0 < Real.log (Real.log (T^(1 / 2 : ℝ)))) :
    Real.exp (-c * (Real.log (T^(1 / 2 : ℝ)))^2 /
      (D * Real.log (Real.log (T^(1 / 2 : ℝ))))) ≤
      Real.exp (-j1CutoffRate ξ c cg * (Real.log T)^2 /
        (D * Real.log (Real.log T))) := by
  have hT'pos : 0 < T^(1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hT'le : T^(1 / 2 : ℝ) ≤ T :=
    Real.rpow_le_self_of_one_le hT.le (by norm_num)
  have hlog' : 0 < Real.log (T^(1 / 2 : ℝ)) := by
    have hT'one : 1 < T^(1 / 2 : ℝ) :=
      Real.one_lt_rpow hT (by norm_num)
    have h : 1 < Real.log (T^(1 / 2 : ℝ)) :=
      (Real.log_pos_iff (Real.log_pos hT'one).le).mp hll'
    linarith
  have hlogle : Real.log (T^(1 / 2 : ℝ)) ≤ Real.log T :=
    Real.log_le_log hT'pos hT'le
  have hllle : Real.log (Real.log (T^(1 / 2 : ℝ))) ≤
      Real.log (Real.log T) := Real.log_le_log hlog' hlogle
  have hll : 0 < Real.log (Real.log T) := lt_of_lt_of_le hll' hllle
  have hden' : 0 < D * Real.log (Real.log (T^(1 / 2 : ℝ))) :=
    mul_pos hD hll'
  have hden : 0 < D * Real.log (Real.log T) := mul_pos hD hll
  have hdenle : D * Real.log (Real.log (T^(1 / 2 : ℝ))) ≤
      D * Real.log (Real.log T) :=
    mul_le_mul_of_nonneg_left hllle hD.le
  have hcoef : j1CutoffRate ξ c cg ≤ c / 4 := min_le_left _ _
  have hsq : 0 ≤ (Real.log T)^2 := sq_nonneg _
  have hnum : 0 ≤ j1CutoffRate ξ c cg * (Real.log T)^2 :=
    mul_nonneg (j1_cutoff_rate_pos hξ hc hcg).le hsq
  have hfrac : j1CutoffRate ξ c cg * (Real.log T)^2 /
      (D * Real.log (Real.log T)) ≤
      (c / 4) * (Real.log T)^2 /
        (D * Real.log (Real.log (T^(1 / 2 : ℝ)))) := by
    calc
      _ ≤ j1CutoffRate ξ c cg * (Real.log T)^2 /
          (D * Real.log (Real.log (T^(1 / 2 : ℝ)))) :=
        div_le_div_of_nonneg_left hnum hden' hdenle
      _ ≤ _ := (div_le_div_iff_of_pos_right hden').mpr
        (mul_le_mul_of_nonneg_right hcoef hsq)
  apply Real.exp_le_exp.mpr
  rw [Real.log_rpow (by linarith : 0 < T)]
  rw [Real.log_rpow (by linarith : 0 < T)] at hfrac
  have hs : ((1 / 2 : ℝ) * Real.log T)^2 =
      (Real.log T)^2 / 4 := by ring
  rw [hs]
  calc
    -c * ((Real.log T)^2 / 4) /
        (D * Real.log ((1 / 2 : ℝ) * Real.log T)) =
      -((c / 4) * (Real.log T)^2 /
        (D * Real.log ((1 / 2 : ℝ) * Real.log T))) := by ring
    _ ≤ -(j1CutoffRate ξ c cg * (Real.log T)^2 /
        (D * Real.log (Real.log T))) := neg_le_neg hfrac
    _ = -j1CutoffRate ξ c cg * (Real.log T)^2 /
        (D * Real.log (Real.log T)) := by ring

theorem j1_cutoff_gaussian_upper_rate
    (ξ c cg D T : ℝ) (hξ : 0 < ξ) (hc : 0 < c) (hcg : 0 < cg)
    (hD : 1 ≤ D) (hll : 1 ≤ Real.log (Real.log T)) :
    Real.exp (-(cg * ((1 / (2 * ξ) : ℝ) * Real.log T)^2)) ≤
      Real.exp (-j1CutoffRate ξ c cg * (Real.log T)^2 /
        (D * Real.log (Real.log T))) := by
  exact j1_cutoff_gaussian_lower_rate ξ c cg
    (D * Real.log (Real.log T)) T hξ hc hcg
    (by nlinarith)

theorem j1_cutoff_two_rate_absorb (K : ℕ)
    (CN Cg f g r : ℝ)
    (hCN : 0 ≤ CN) (hCg : 0 ≤ Cg)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hfr : f ≤ r) (hgr : g ≤ r) :
    ENNReal.ofReal (CN * (5 : ℝ)^K * f) + ENNReal.ofReal (Cg * g) ≤
      ENNReal.ofReal ((CN + Cg) * (5 : ℝ)^K * r) := by
  have h5 : 1 ≤ (5 : ℝ)^K := one_le_pow₀ (by norm_num)
  have h50 : 0 ≤ (5 : ℝ)^K := by linarith
  have hcf : CN * (5 : ℝ)^K * f ≤ CN * (5 : ℝ)^K * r :=
    mul_le_mul_of_nonneg_left hfr (mul_nonneg hCN h50)
  have hcg : Cg * g ≤ Cg * (5 : ℝ)^K * r := by
    calc
      Cg * g ≤ Cg * r := mul_le_mul_of_nonneg_left hgr hCg
      _ ≤ Cg * (5 : ℝ)^K * r := by
        have hh : Cg ≤ Cg * (5 : ℝ)^K := by
          nlinarith [mul_le_mul_of_nonneg_left h5 hCg]
        exact mul_le_mul_of_nonneg_right hh hr
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ CN * (5 : ℝ)^K * f)
    (by positivity : 0 ≤ Cg * g)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hcf, hcg])

theorem j1_source_rate_weaken (K : ℕ)
    (D T C₁ c₁ C c : ℝ) (hD : 0 < D)
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C)
    (hc : c ≤ c₁) :
    ENNReal.ofReal (C₁ * (5 : ℝ)^K *
      Real.exp (-c₁ * (Real.log T)^2 / D)) ≤
    ENNReal.ofReal (C * (5 : ℝ)^K *
      Real.exp (-c * (Real.log T)^2 / D)) := by
  have hsq : 0 ≤ (Real.log T)^2 := sq_nonneg _
  have hrate : Real.exp (-c₁ * (Real.log T)^2 / D) ≤
      Real.exp (-c * (Real.log T)^2 / D) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hD).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hsq]
  have h5 : 0 ≤ (5 : ℝ)^K := by positivity
  have hC0 : 0 ≤ C := hC₁.trans hC
  apply ENNReal.ofReal_le_ofReal
  calc
    C₁ * (5 : ℝ)^K * Real.exp (-c₁ * (Real.log T)^2 / D) ≤
      C₁ * (5 : ℝ)^K * Real.exp (-c * (Real.log T)^2 / D) :=
      mul_le_mul_of_nonneg_left hrate (mul_nonneg hC₁ h5)
    _ ≤ C * (5 : ℝ)^K * Real.exp (-c * (Real.log T)^2 / D) := by
      have hh : C₁ * (5 : ℝ)^K ≤ C * (5 : ℝ)^K :=
        mul_le_mul_of_nonneg_right hC h5
      exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end SupercriticalLQGUniqueness.B2.DG20Conc
