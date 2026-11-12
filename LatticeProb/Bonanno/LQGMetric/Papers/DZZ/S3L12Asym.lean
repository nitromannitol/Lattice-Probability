/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Asym at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Union

/-!
# DZZ Lemma 3.12: elementary asymptotics (P2-DZZ312)

Own elementary proofs of the bookkeeping in the proof of Lemma 3.12 (DZZ l. 1430–1434), in `L = log δ⁻¹`:
`e^{−c₁L} + e^{−c₂L} + (AL + 1) e^{−10L} + 18 (AL + 1) e^{−√L} ≤ e^{−L^{1/4}}` for large `L`
(`l312_asym`), and the level bounds `l312_n_le`, `l312_one_le_n`, `l312_two_pow_sq_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace LQGMetric
namespace DZZ

lemma l312_tend {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    Tendsto (fun L : ℝ => (A * L + 1) * Real.exp (L ^ (1 / 4 : ℝ) - c * L ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun t : ℝ => A * (t ^ 4 * Real.exp (-t)) + Real.exp (-t)) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul A).add
      Real.tendsto_exp_neg_atTop_nhds_zero
  have hr : Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ L : ℝ in atTop, max 1 ((2 / c) ^ 4) ≤ L := eventually_ge_atTop _
  refine squeeze_zero' ?_ ?_ (hg.comp hr)
  · filter_upwards [hev] with L hL
    have : 0 ≤ L := le_trans (by positivity) hL
    positivity
  · filter_upwards [hev] with L hL
    have hL0 : 0 ≤ L := le_trans (by positivity) hL
    set t := L ^ (1 / 4 : ℝ) with ht
    have ht0 : 0 ≤ t := Real.rpow_nonneg hL0 _
    have h4 : t ^ 4 = L := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
    have h2 : L ^ (1 / 2 : ℝ) = t ^ 2 := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
    have htc : 2 / c ≤ t := by
      have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hL)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have e : ((2 / c) ^ 4) ^ (1 / 4 : ℝ) = 2 / c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [e] at h; exact h
    have hct : 2 ≤ c * t := by rwa [div_le_iff₀ hc, mul_comm] at htc
    have hexp : Real.exp (t - c * t ^ 2) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simp only [Function.comp, h2]
    have : 0 ≤ A * t ^ 4 + 1 := by positivity
    calc (A * L + 1) * Real.exp (t - c * t ^ 2) = (A * t ^ 4 + 1) * Real.exp (t - c * t ^ 2) := by
          rw [h4]
      _ ≤ (A * t ^ 4 + 1) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left hexp this
      _ = A * (t ^ 4 * Real.exp (-t)) + Real.exp (-t) := by ring

/-- `e^{−c₁L} + e^{−c₂L} + (AL + 1) e^{−10L} + 18 (AL + 1) e^{−√L} ≤ e^{−L^{1/4}}` for large `L`. -/
lemma l312_asym {c₁ c₂ A : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-(c₁ * L)) + Real.exp (-(c₂ * L)) +
      (A * L + 1) * Real.exp (-(10 * L)) + 18 * ((A * L + 1) * Real.exp (-Real.sqrt L)) ≤
        Real.exp (-(L ^ (1 / 4 : ℝ))) := by
  have t1 := (l312_tend hc₁ le_rfl).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have t2 := (l312_tend hc₂ le_rfl).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have t3 := (l312_tend one_pos hA).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 80))
  filter_upwards [t1, t2, t3, eventually_ge_atTop 1] with L h1 h2 h3 hL
  simp only [zero_mul, zero_add, one_mul] at h1 h2 h3
  have hL0 : 0 ≤ L := by linarith
  set q := L ^ (1 / 4 : ℝ)
  have hs : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  have hsL : L ^ (1 / 2 : ℝ) ≤ L := by
    calc L ^ (1 / 2 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = L := Real.rpow_one L
  have hsp : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL0 _
  have eq : ∀ x : ℝ, Real.exp (-x) = Real.exp (-q) * Real.exp (q - x) := by
    intro x; rw [← Real.exp_add]; ring_nf
  have e1 : Real.exp (-(c₁ * L)) ≤ Real.exp (-q) * (1 / 4) := by
    rw [eq]; gcongr
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans h1.le
  have e2 : Real.exp (-(c₂ * L)) ≤ Real.exp (-q) * (1 / 4) := by
    rw [eq]; gcongr
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans h2.le
  have hAL : 0 ≤ A * L + 1 := by positivity
  have e4 : (A * L + 1) * Real.exp (-Real.sqrt L) ≤ Real.exp (-q) * (1 / 80) := by
    rw [eq, hs, mul_left_comm]; gcongr
  have e3 : (A * L + 1) * Real.exp (-(10 * L)) ≤ (A * L + 1) * Real.exp (-Real.sqrt L) := by
    gcongr; rw [hs]; linarith
  have hq := Real.exp_pos (-q)
  nlinarith

end DZZ
end LQGMetric
