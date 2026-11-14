/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RBranch at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RExt

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def laneC1RQc : Set ℂ := {z | z.re ≤ 0 ∨ 1 ≤ z.im}

theorem laneC1RQc_closed : IsClosed laneC1RQc :=
  (isClosed_le Complex.continuous_re continuous_const).union
    (isClosed_le continuous_const Complex.continuous_im)

 
def laneC1RBranch (p z : ℂ) : ℂ :=
  Complex.log ((z - p) * (-(1 + I))) - Complex.log (-(1 + I))

theorem laneC1R_branch_slit {p z : ℂ} (hp0 : 0 < p.re) (hp1 : p.im < 1)
    (hz : z ∈ laneC1RQc) : (z - p) * (-(1 + I)) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hre : ((z - p) * (-(1 + I))).re = (z.im - p.im) - (z.re - p.re) := by
    simp [Complex.mul_re]
    ring
  have him : ((z - p) * (-(1 + I))).im = -((z.re - p.re) + (z.im - p.im)) := by
    simp [Complex.mul_im]
    ring
  rw [hre, him]
  by_cases hsum : (z.re - p.re) + (z.im - p.im) = 0
  · left
    rcases hz with hz | hz
    · linarith
    · linarith
  · right
    intro h
    exact hsum (by linarith)

theorem laneC1R_ne_of_mem_Qc {p z : ℂ} (hp0 : 0 < p.re) (hp1 : p.im < 1)
    (hz : z ∈ laneC1RQc) : z ≠ p := by
  rintro rfl
  rcases hz with hz | hz <;> linarith

theorem laneC1R_branch_continuousOn {p : ℂ} (hp0 : 0 < p.re) (hp1 : p.im < 1) :
    ContinuousOn (laneC1RBranch p) laneC1RQc := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold laneC1RBranch
  apply ContinuousAt.sub _ continuousAt_const
  have hf : ContinuousAt (fun w : ℂ => (w - p) * (-(1 + I))) z := by fun_prop
  exact (continuousAt_clog (laneC1R_branch_slit hp0 hp1 hz)).comp
    (f := fun w : ℂ => (w - p) * (-(1 + I))) hf

theorem laneC1R_branch_exp {p z : ℂ} (hp0 : 0 < p.re) (hp1 : p.im < 1)
    (hz : z ∈ laneC1RQc) : Complex.exp (laneC1RBranch p z) = z - p := by
  have hu : (-(1 + I) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hw : z - p ≠ 0 := sub_ne_zero.mpr (laneC1R_ne_of_mem_Qc hp0 hp1 hz)
  unfold laneC1RBranch
  rw [Complex.exp_sub, Complex.exp_log (mul_ne_zero hw hu), Complex.exp_log hu,
    mul_div_assoc, div_self hu, mul_one]

end SupercriticalLQGUniqueness.B2.DG20Conc
