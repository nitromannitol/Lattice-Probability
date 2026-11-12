/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5Asym at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Cross

/-!
# DZZ Lemma 3.5: the asymptotic inequalities (P2-DZZ3G)

The elementary inequalities used at the end of the proof of DZZ Lemma 3.5 (arXiv:1807.00422,
`LBM_LGDarXiv.tex` l. 1079–1083), for `L = log δ⁻¹` large:
`1024 C² L² e^{L^{0.7}} ≤ e^{L^{0.8}}` (so `4^{k+2}(λ+1) ≤ (δ/δ')³ e^{L^{0.8}}/2`),
`2 δ^c (20 δ^{-c/2} + 1) < ξ` (Eq.lowerboundforDprime with `ι = c/2`), `4 δ^c < δ^{ξd}` (a
connected end of diameter `≥ δ^{ξd}` lies in no `𝖢_large`), `8 ≤ C L`. Own elementary proof
(`u = L^{1/10}`, `e^y ≥ 1 + y`, `e^y ≥ y³/6`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

lemma l35_asym {C c ξ ξd : ℝ} (hC : 0 < C) (hc : 0 < c) (hξ : 0 < ξ) (hξd : ξd < c) :
    ∃ δ₀ > 0, ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      1024 * C ^ 2 * Real.log δ⁻¹ ^ 2 * Real.exp (Real.log δ⁻¹ ^ (0.7 : ℝ)) ≤
        Real.exp (Real.log δ⁻¹ ^ (0.8 : ℝ)) ∧
      2 * δ ^ c * (20 * δ ^ (-(c / 2)) + 1) < ξ ∧ 4 * δ ^ c < δ ^ ξd ∧
      8 ≤ C * Real.log δ⁻¹ := by
  set U := max 2 (49152 * C ^ 2 + 1) with hUdef
  set L₀ := max (U ^ 10) (max (84 / (c * ξ) + 1) (max (2 / (c - ξd) + 1) (8 / C + 1)))
    with hL₀def
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  rintro δ ⟨hδ0, hδ1⟩
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hL : L₀ < L := by
    have := Real.log_lt_log hδ0 hδ1
    rw [Real.log_exp] at this; linarith
  have hU2 : 2 ≤ U := le_max_left _ _
  have hL1 : U ^ 10 < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hL2 : 84 / (c * ξ) < L := by
    have := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hL; linarith
  have hL3 : 2 / (c - ξd) < L := by
    have := lt_of_le_of_lt (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)) hL; linarith
  have hL4 : 8 / C < L := by
    have := lt_of_le_of_lt (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)) hL; linarith
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL1
  have hδe : ∀ x : ℝ, δ ^ x = Real.exp (-(L * x)) := fun x => by
    rw [Real.rpow_def_of_pos hδ0, hlogδ]; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · set u := L ^ ((1 : ℝ) / 10) with hudef
    have hu10 : u ^ 10 = L := by
      rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hu7 : L ^ (0.7 : ℝ) = u ^ 7 := by
      rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hu8 : L ^ (0.8 : ℝ) = u ^ 8 := by
      rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have huU : U ≤ u := by
      have h1 : (U ^ 10) ^ ((1 : ℝ) / 10) = U := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
      rw [← h1]; exact Real.rpow_le_rpow (by positivity) hL1.le (by norm_num)
    have hu2 : 2 ≤ u := hU2.trans huU
    have huC : 49152 * C ^ 2 ≤ u := by linarith [le_max_right 2 (49152 * C ^ 2 + 1)]
    rw [hu7, hu8, ← hu10]
    have hy : u ^ 8 / 2 ≤ u ^ 8 - u ^ 7 := by
      have : u ^ 8 = u * u ^ 7 := by ring
      have h7 : 0 ≤ u ^ 7 := by positivity
      nlinarith
    have hexp : (u ^ 8 / 2) ^ 3 / 6 ≤ Real.exp (u ^ 8 - u ^ 7) := by
      have := Real.pow_div_factorial_le_exp (u ^ 8 / 2) (by positivity) 3
      refine le_trans ?_ (this.trans (Real.exp_le_exp.2 hy))
      norm_num [Nat.factorial]
    have hpoly : 1024 * C ^ 2 * (u ^ 10) ^ 2 ≤ (u ^ 8 / 2) ^ 3 / 6 := by
      have e : (u ^ 8 / 2) ^ 3 / 6 = u ^ 20 * u ^ 4 / 48 := by ring
      have hu4 : u ≤ u ^ 4 := by
        have h1 : 1 ≤ u ^ 3 := one_le_pow₀ (by linarith)
        nlinarith
      have h20 : 0 ≤ u ^ 20 := by positivity
      rw [e]
      nlinarith
    calc 1024 * C ^ 2 * (u ^ 10) ^ 2 * Real.exp (u ^ 7) ≤
          Real.exp (u ^ 8 - u ^ 7) * Real.exp (u ^ 7) :=
          mul_le_mul_of_nonneg_right (hpoly.trans hexp) (Real.exp_pos _).le
      _ = Real.exp (u ^ 8) := by rw [← Real.exp_add]; ring_nf
  · rw [hδe, hδe]
    have hcξ : 0 < c * ξ := by positivity
    have h1 : 84 / ξ < c * L := by
      rw [div_lt_iff₀ hcξ] at hL2; rw [div_lt_iff₀ hξ]; nlinarith
    have h2 : 1 + c * L / 2 ≤ Real.exp (c * L / 2) := by
      have := Real.add_one_le_exp (c * L / 2); linarith
    have h3 : 42 < ξ * Real.exp (c * L / 2) := by
      rw [div_lt_iff₀ hξ] at h1; nlinarith
    have e1 : Real.exp (-(L * c)) * Real.exp (-(L * -(c / 2))) = Real.exp (-(c * L / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(L * c)) ≤ Real.exp (-(c * L / 2)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e3 : Real.exp (-(c * L / 2)) * Real.exp (c * L / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-(c * L / 2))
    nlinarith
  · rw [hδe, hδe]
    have h1 : 2 < (c - ξd) * L := by
      rw [div_lt_iff₀ (by linarith)] at hL3; linarith
    have h2 : (4 : ℝ) < Real.exp ((c - ξd) * L) := by
      have := Real.add_one_le_exp ((c - ξd) * L)
      have h3 : Real.exp 2 > 4 := by
        have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have h5 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        nlinarith
      linarith [Real.exp_lt_exp.2 h1]
    have e : Real.exp (-(L * ξd)) = Real.exp ((c - ξd) * L) * Real.exp (-(L * c)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_lt_mul_of_pos_right h2 (Real.exp_pos _)
  · rw [div_lt_iff₀ hC] at hL4; linarith

end DZZ
end LQGMetric
