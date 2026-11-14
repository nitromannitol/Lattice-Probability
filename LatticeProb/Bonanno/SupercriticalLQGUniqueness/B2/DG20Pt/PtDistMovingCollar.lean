/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingCollar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingChain

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem dist_inv_real_mul (r : ℝ) (hr : 0 < r) (u v : ℂ) :
    dist ((r⁻¹ : ℂ) * u) ((r⁻¹ : ℂ) * v) =
      r⁻¹ * dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private theorem real_mul_inv_real_mul (r : ℝ) (hr : 0 < r) (u : ℂ) :
    (r : ℂ) * ((r⁻¹ : ℂ) * u) = u := by
  simp [hr.ne']

private theorem inv_real_mul_real_mul (r : ℝ) (hr : 0 < r) (u : ℂ) :
    (r⁻¹ : ℂ) * ((r : ℂ) * u) = u := by
  simp [hr.ne']

theorem pt_dist_scaled_collar
    (U K : Set ℂ) (k : ℕ)
    (hcollar : ∀ v ∈ K, ∀ x : ℂ,
      dist v x < ((2 : ℝ)⁻¹) ^ k / 4 →
        ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ U)
    (r : ℝ) (hr : 1 ≤ r)
    (v : ℂ) (hv : v ∈ K) (x : ℂ)
    (hx : dist ((r : ℂ) * v) x < ((2 : ℝ)⁻¹) ^ k / 4) :
    ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆
      ((fun y : ℂ => (r : ℂ) * y) '' U) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hri0 : 0 ≤ r⁻¹ := (inv_pos.mpr hr0).le
  have hri1 : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
  let x' : ℂ := (r⁻¹ : ℂ) * x
  have hx' : dist v x' < ((2 : ℝ)⁻¹) ^ k / 4 := by
    have hd := dist_inv_real_mul r hr0 ((r : ℂ) * v) x
    rw [inv_real_mul_real_mul r hr0 v] at hd
    change dist v x' = r⁻¹ * dist ((r : ℂ) * v) x at hd
    rw [hd]
    have hrad : 0 ≤ ((2 : ℝ)⁻¹) ^ k / 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hri1 (dist_nonneg : 0 ≤
      dist ((r : ℂ) * v) x)
    nlinarith
  have hbase := hcollar v hv x' hx'
  intro y hy
  let y' : ℂ := (r⁻¹ : ℂ) * y
  have hy' : y' ∈ ball x' (17 * ((2 : ℝ)⁻¹) ^ k) := by
    rw [mem_ball] at hy ⊢
    have hd := dist_inv_real_mul r hr0 y x
    change dist y' x' = r⁻¹ * dist y x at hd
    rw [hd]
    have hrad : 0 ≤ 17 * ((2 : ℝ)⁻¹) ^ k := by positivity
    have hmul := mul_le_mul_of_nonneg_right hri1 (dist_nonneg : 0 ≤ dist y x)
    nlinarith
  exact ⟨y', hbase hy', real_mul_inv_real_mul r hr0 y⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
