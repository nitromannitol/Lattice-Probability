import LatticeProb.Prob.ConeWindowStrictEntrance

/-! # Cone-window coverage from an interval complement of measure zero -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- If a family of cone intervals covers almost every point of a window,
then the rationally encoded cone-window event holds almost everywhere. -/
theorem ae_coneWindowCoverage_of_null_interval_complement
    (z : C(ℝ, ℝ) × C(ℝ, ℝ)) (a b : ℝ) (σ τ : ℝ → ℝ)
    (hnull : volume (Icc a b \ ⋃ t ∈ Icc a b, Ioo (σ t) (τ t)) = 0)
    (hinterval : ∀ t ∈ Icc a b, σ t < τ t →
      a ≤ σ t ∧ τ t ≤ b ∧
      IsGLB {s : ℝ | s < τ t ∧ ∀ v ∈ Icc s (τ t),
        z.1 (τ t) ≤ z.1 v ∧ z.2 (τ t) ≤ z.2 v} (σ t)) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      (z, x) ∈ Prod.fst '' coneWindowWitness a b := by
  have hbad : ∀ᵐ x ∂volume,
      x ∉ Icc a b \ ⋃ t ∈ Icc a b, Ioo (σ t) (τ t) := by
    rw [ae_iff]
    apply measure_mono_null _ hnull
    intro x hx
    exact not_not.mp hx
  filter_upwards [ae_restrict_of_ae hbad, ae_restrict_mem measurableSet_Ioo] with x hx hxab
  have hxunion : x ∈ ⋃ t ∈ Icc a b, Ioo (σ t) (τ t) := by
    by_contra h
    exact hx ⟨⟨hxab.1.le, hxab.2.le⟩, h⟩
  simp only [mem_iUnion] at hxunion
  obtain ⟨t, ht, hxt⟩ := hxunion
  obtain ⟨ha, hb, hglb⟩ := hinterval t ht (lt_trans hxt.1 hxt.2)
  refine ⟨((z, x), τ t), ?_, rfl⟩
  exact (mem_coneWindowWitness_iff_strict_start_isGLB z a b x (τ t)).2
    ⟨hxab.1, hxt.2, hb, σ t, ha, hxt.1, hglb⟩

end LatticeProb
