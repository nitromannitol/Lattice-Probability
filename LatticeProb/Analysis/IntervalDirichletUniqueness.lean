import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # Uniqueness for the classical interval Dirichlet problem -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A continuous function with vanishing second derivative in an interval and
zero endpoint values vanishes throughout the interval. -/
theorem eq_zero_on_Icc_of_deriv_deriv_eq_zero {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b))
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt (deriv f) 0 x)
    (ha : f a = 0) (hb : f b = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  obtain ⟨c, hc'⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected
    (fun x hx => (hdd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hdd x hx).deriv)
  let g : ℝ → ℝ := fun x => f x - c * x
  have hg : DifferentiableOn ℝ g (Ioo a b) := by
    intro x hx
    have h := (hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    exact (h.sub ((hasDerivAt_id x).const_mul c).differentiableAt).differentiableWithinAt
  have hg' : (Ioo a b).EqOn (deriv g) 0 := by
    intro x hx
    have hx' := (hd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    change deriv g x = 0
    have h := hx'.hasDerivAt.sub ((hasDerivAt_id x).const_mul c)
    change HasDerivAt g (deriv f x - c * 1) x at h
    rw [hc' x hx] at h
    simpa only [mul_one, sub_self] using h.deriv
  obtain ⟨d, hd'⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected hg hg'
  have heq : (Ioo a b).EqOn f (fun x => c * x + d) := by
    intro x hx
    have h := hd' x hx
    dsimp [g] at h
    linarith
  have heq' : (Icc a b).EqOn f (fun x => c * x + d) :=
    heq.of_subset_closure hc (by fun_prop) Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  have hca := heq' ⟨le_rfl, hab.le⟩
  have hcb := heq' ⟨hab.le, le_rfl⟩
  rw [ha] at hca
  rw [hb] at hcb
  have hz : c = 0 := by nlinarith
  have hz' : d = 0 := by rw [hz] at hca; simpa using hca.symm
  intro x hx
  rw [heq' hx, hz, hz']
  ring

end LatticeProb
