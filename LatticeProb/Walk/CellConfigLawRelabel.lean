import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-! # Relabelling random-walk laws by cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open ReflectedGMS.GMS

namespace LatticeProb.CellConfigSRW

open Classical in
/-- A random walk whose transitions agree with those of a cell configuration has the
cell walk law after relabelling its vertices by cells. -/
theorem isSRWLaw_map_of_cylinder {V : Type*} [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (H : CellConfig) [Countable H.cells]
    (e : V ≃ H.cells) (a : V) (Q : Measure (ℕ → V)) [IsProbabilityMeasure Q]
    (p : V → V → ℝ≥0∞)
    (hcyl : ∀ (n : ℕ) (x : Fin (n + 1) → V),
      Q {ω | ∀ i : Fin (n + 1), ω i = x i} =
        (if x 0 = a then 1 else 0) * ∏ i : Fin n, p (x i.castSucc) (x i.succ))
    (hp : ∀ v w, p v w = ENNReal.ofReal (H.transition (e v) (e w))) :
    H.IsSRWLaw (e a) (Q.map (fun ω n => e (ω n))) := by
  classical
  have hm : Measurable (fun ω : ℕ → V => fun n => e (ω n)) :=
    Measurable.of_eval fun n => (measurable_of_countable e).comp (measurable_pi_apply n)
  refine ⟨by infer_instance, fun n x => ?_⟩
  have hs : MeasurableSet {ω : ℕ → H.cells | ∀ i : Fin (n + 1), ω i = x i} := by
    have he : {ω : ℕ → H.cells | ∀ i : Fin (n + 1), ω i = x i} =
        ⋂ i : Fin (n + 1), (fun ω : ℕ → H.cells => ω i) ⁻¹' {x i} := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun i => measurable_pi_apply _ (measurableSet_singleton _)
  rw [Measure.map_apply hm hs]
  have he : (fun ω : ℕ → V => fun n => e (ω n)) ⁻¹'
      {ω : ℕ → H.cells | ∀ i : Fin (n + 1), ω i = x i} =
      {ω | ∀ i : Fin (n + 1), ω i = e.symm (x i)} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, ← e.eq_symm_apply]
  rw [he, hcyl]
  simp only [hp, Equiv.apply_symm_apply, Equiv.symm_apply_eq]

end LatticeProb.CellConfigSRW
end
