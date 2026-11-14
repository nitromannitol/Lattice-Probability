/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLoop

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneCRepeatLift (M : ℝ → ℂ) : ℝ → ℂ :=
  SupercriticalLQGUniqueness.B2.Strong.glue4 M
    (fun u => M u + (M 1 - M 0))
    (fun _ => M 1 + (M 1 - M 0))
    (fun _ => M 1 + (M 1 - M 0))

theorem laneC_repeatLift_continuousOn
    {M : ℝ → ℂ} (hM : ContinuousOn M (Icc (0 : ℝ) 1)) :
    ContinuousOn (laneCRepeatLift M) (Icc (0 : ℝ) 2) := by
  have h₁ : ContinuousOn (fun u => M u + (M 1 - M 0)) (Icc (0 : ℝ) 1) :=
    hM.add continuousOn_const
  have hG := SupercriticalLQGUniqueness.B2.Strong.continuousOn_glue4
    M (fun u => M u + (M 1 - M 0))
    (fun _ => M 1 + (M 1 - M 0))
    (fun _ => M 1 + (M 1 - M 0))
    hM h₁ continuousOn_const continuousOn_const
    (by ring) rfl rfl
  exact hG.mono (Icc_subset_Icc (by norm_num) (by norm_num))

theorem laneC_repeatLift_first (M : ℝ → ℂ) :
    EqOn (laneCRepeatLift M) M (Icc (0 : ℝ) 1) :=
  SupercriticalLQGUniqueness.B2.Strong.glue4_eqOn₀ _ _ _ _

theorem laneC_repeatLift_second (M : ℝ → ℂ) :
    EqOn (laneCRepeatLift M)
      (fun x => M (x - 1) + (M 1 - M 0)) (Icc (1 : ℝ) 2) := by
  simpa only [laneCRepeatLift] using
    (SupercriticalLQGUniqueness.B2.Strong.glue4_eqOn₁
      M (fun u => M u + (M 1 - M 0))
      (fun _ => M 1 + (M 1 - M 0))
      (fun _ => M 1 + (M 1 - M 0)) (by ring))

theorem laneC_repeatLift_shift (M : ℝ → ℂ)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    laneCRepeatLift M (u + 1) = M u + (M 1 - M 0) := by
  by_cases h0 : u = 0
  · subst u
    have h := (laneC_repeatLift_first M) (x := (1 : ℝ)) (by norm_num)
    have heq : M 1 = M 0 + (M 1 - M 0) := by ring
    simpa only [zero_add, h] using heq
  · have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
    have hmem : u + 1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith [hu.2]⟩
    simpa using (laneC_repeatLift_second M) (x := u + 1) hmem

 

theorem laneC_repeatLift_exp
    {τ M : ℝ → ℂ} {c : ℂ} (hc : τ 0 = τ 1)
    (hexp : ∀ u ∈ Icc (0 : ℝ) 1, Complex.exp (M u) = τ u - c) :
    ∀ x ∈ Icc (0 : ℝ) 2,
      Complex.exp (laneCRepeatLift M x) = laneCRepeatLoop τ x - c := by
  have hperiod : Complex.exp (M 1 - M 0) = 1 := by
    rw [Complex.exp_sub]
    have h0 := hexp 0 (by simp)
    have h1 := hexp 1 (by simp)
    rw [h1, ← hc, ← h0]
    exact div_self (Complex.exp_ne_zero _)
  intro x hx
  by_cases hx1 : x ≤ 1
  · have hm := (laneC_repeatLift_first M) (x := x) ⟨hx.1, hx1⟩
    have hτ := (laneC_repeatLoop_first τ) (x := x) ⟨hx.1, hx1⟩
    rw [hm, hτ]
    exact hexp x ⟨hx.1, hx1⟩
  · have hx12 : x ∈ Icc (1 : ℝ) 2 := ⟨le_of_not_ge hx1, hx.2⟩
    have hu : x - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx12.1, hx12.2]
    have hm := (laneC_repeatLift_second M) (x := x) hx12
    have hτ := (laneC_repeatLoop_second hc) (x := x) hx12
    rw [hm, hτ, Complex.exp_add, hperiod, mul_one]
    exact hexp (x - 1) hu

end SupercriticalLQGUniqueness.B2.DG20Conc
