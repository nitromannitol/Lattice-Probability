import LatticeProb.Prob.ConeWindowGeometry

/-! # Cone-window witnesses and strict entrance times -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A cone-window witness is equivalent to a finite greatest lower bound of
the strict admissible starts lying between the window's left endpoint and the
covered time. -/
theorem mem_coneWindowWitness_iff_strict_start_isGLB
    (z : C(ℝ, ℝ) × C(ℝ, ℝ)) (l r x t : ℝ) :
    ((z, x), t) ∈ coneWindowWitness l r ↔
      l < x ∧ x < t ∧ t ≤ r ∧
      ∃ a : ℝ, l ≤ a ∧ a < x ∧
        IsGLB {s : ℝ | s < t ∧ ∀ v ∈ Icc s t,
          z.1 t ≤ z.1 v ∧ z.2 t ≤ z.2 v} a := by
  constructor
  · intro h
    rcases (mem_coneWindowWitness_iff_least_start z l r x t).1 h with
      ⟨hlx, hxt, htr, a, hla, hax, ha⟩
    refine ⟨hlx, hxt, htr, a, hla, hax, ?_⟩
    apply IsLeast.isGLB
    refine ⟨⟨lt_trans hax hxt, ha.1.2⟩, ?_⟩
    intro s hs
    exact ha.2 ⟨hs.1.le, hs.2⟩
  · rintro ⟨hlx, hxt, htr, a, hla, hax, ha⟩
    obtain ⟨s, hs, _, hsx⟩ := ha.exists_between hax
    obtain ⟨q, hsq, hqx⟩ := exists_rat_btwn hsx
    have hqt : (q : ℝ) < t := lt_trans hqx hxt
    have hq : ∀ v ∈ Icc (q : ℝ) t,
        z.1 t ≤ z.1 v ∧ z.2 t ≤ z.2 v := by
      intro v hv
      exact hs.2 v ⟨le_trans hsq.le hv.1, hv.2⟩
    refine ⟨hlx, hxt, htr, ⟨q, hqx, hqt, hq⟩, ?_⟩
    intro p hpl hp
    have hap : a ≤ (p : ℝ) := ha.1 hp
    exact (not_le_of_gt (lt_of_lt_of_le hpl hla)) hap

end LatticeProb
