/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateMerge at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateScaleENN

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_three_rate_merge (A B D a b g L : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < g)
    (hL : 3 ≤ L) :
    let c : ℝ := min a (min b g)
    0 < c ∧
      A * Real.exp (-a * (L ^ 2 / Real.log L)) +
        B * Real.exp (-b * (L ^ 2 / Real.log L)) +
        D * Real.exp (-g * L ^ 2) ≤
      (A + B + D) * Real.exp (-c * (L ^ 2 / Real.log L)) := by
  let c := min a (min b g)
  have hc : 0 < c := lt_min ha (lt_min hb hg)
  have hca : c ≤ a := min_le_left _ _
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hcg : c ≤ g := (min_le_right _ _).trans (min_le_right _ _)
  have hlog : 1 < Real.log L := by
    apply (Real.lt_log_iff_exp_lt (by linarith : 0 < L)).2
    exact Real.exp_one_lt_three.trans_le hL
  have hq0 : 0 ≤ L ^ 2 / Real.log L := by positivity
  have hq : L ^ 2 / Real.log L ≤ L ^ 2 := by
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [sq_nonneg L]
  have h₁ : Real.exp (-a * (L ^ 2 / Real.log L)) ≤
      Real.exp (-c * (L ^ 2 / Real.log L)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h₂ : Real.exp (-b * (L ^ 2 / Real.log L)) ≤
      Real.exp (-c * (L ^ 2 / Real.log L)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h₃ : Real.exp (-g * L ^ 2) ≤
      Real.exp (-c * (L ^ 2 / Real.log L)) := by
    apply Real.exp_le_exp.mpr
    have hmul : c * (L ^ 2 / Real.log L) ≤ g * L ^ 2 :=
      (mul_le_mul_of_nonneg_left hq hc.le).trans
        (mul_le_mul_of_nonneg_right hcg (sq_nonneg L))
    linarith
  dsimp
  refine ⟨hc, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left h₁ hA,
    mul_le_mul_of_nonneg_left h₂ hB,
    mul_le_mul_of_nonneg_left h₃ hD]

end SupercriticalLQGUniqueness.B2.DG20Pt
