/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.AroundFailureGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.AroundFourTail

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem around_failure_subset_four_bad
    {Ω : Type} (ξ : ℝ) (φ : Ω → ℂ → ℝ) (c : Ω → ℝ)
    (x : ℂ) {r : ℝ} (hr : 0 < r) {T lam : ℝ}
    (hT : 0 < T) (hlam : 0 < lam) :
    {ω | ¬ Inputs.HasAroundLoop ξ (φ ω) x r hr
      (ENNReal.ofReal (T * r * lam * Real.exp (c ω)))} ⊆
      ⋃ j : Fin 4,
        {ω | ENNReal.ofReal (Real.exp (c ω)) *
            ENNReal.ofReal ((T / 16) * r * lam) <
          crossLenIn ξ (φ ω)
            (Strong.cfgOpens (Inputs.annulus48 x r hr) j)
            (Strong.cfgSet₁ (Inputs.annulus48 x r hr) j)
            (Strong.cfgSet₂ (Inputs.annulus48 x r hr) j)} := by
  let A := Inputs.annulus48 x r hr
  intro ω hfail
  by_contra hnot
  let e : ℝ := Real.exp (c ω)
  have he : 0 < e := Real.exp_pos _
  let v : ℝ := (T / 8) * r * lam * e
  let a : ℝ≥0∞ := ENNReal.ofReal v
  let L : ℝ≥0∞ := ENNReal.ofReal (T * r * lam * e)
  have hv : 0 < v := by dsimp [v]; positivity
  have hL : 0 < T * r * lam * e := by positivity
  have hsmall : ENNReal.ofReal e * ENNReal.ofReal ((T / 16) * r * lam) < a := by
    rw [← ENNReal.ofReal_mul he.le]
    apply (ENNReal.ofReal_lt_ofReal_iff hv).2
    dsimp [v]
    nlinarith [mul_pos (mul_pos hT hr) hlam, he]
  have hcross (j : Fin 4) :
      crossLenIn ξ (φ ω) (Strong.cfgOpens A j)
        (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j) < a := by
    have hnotj : ¬ ω ∈
        {ω | ENNReal.ofReal (Real.exp (c ω)) *
            ENNReal.ofReal ((T / 16) * r * lam) <
          crossLenIn ξ (φ ω) (Strong.cfgOpens A j)
            (Strong.cfgSet₁ A j) (Strong.cfgSet₂ A j)} := by
      intro hj
      exact hnot (mem_iUnion.mpr ⟨j, hj⟩)
    exact (le_of_not_gt hnotj).trans_lt hsmall
  have hbudget : a + a + a + a < L := by
    have hsum : a + a + a + a = ENNReal.ofReal (4 * v) := by
      calc
        a + a + a + a = (4 : ℝ≥0∞) * a := by ring
        _ = ENNReal.ofReal (4 * v) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [hsum]
    apply (ENNReal.ofReal_lt_ofReal_iff hL).2
    dsimp [v, L]
    nlinarith [mul_pos (mul_pos hT hr) hlam, he]
  have hloop := around_loop_of_four_crossLen A ξ (φ ω)
    a a a a L (hcross 0) (hcross 1) (hcross 2) (hcross 3) hbudget
  exact hfail hloop

end SupercriticalLQGUniqueness.B2.DG20Pt
