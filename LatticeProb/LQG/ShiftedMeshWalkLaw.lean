import LatticeProb.LQG.ShiftedMeshWalkDomain
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableLawCylinders
import LatticeProb.Prob.CountablePathMeasureKernel

/-! # Coded walk laws on shifted meshes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal

namespace LatticeProb

instance : MeasurableSingletonClass MeshGridStateCode := ⟨fun s => by
  cases s with
  | inl x => simpa only [Set.image_singleton] using
      (MeasurableSet.inl_image (β := MeshGridDartCode) (measurableSet_singleton x))
  | inr d => simpa only [Set.image_singleton] using
      (MeasurableSet.inr_image (α := ℤ) (measurableSet_singleton d))⟩

abbrev ShiftedMeshParameter := (MatedCRT.Path2 × ℝ × ℝ) × ℤ

/-- The encoded graph walk law, extended by zero when the graph is not locally finite. -/
def shiftedMeshCodedWalkLaw (p : ShiftedMeshParameter) : Measure (ℕ → MeshGridStateCode) := by
  classical
  let w := shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2
  exact if h : MatedCRT.IsLocallyFinite 1 w then
    Measure.map (fun path i => meshGridEncodeMatedState (path i))
      ((MatedCRT.graph 1 w h).walkLaw p.2)
    else 0

private theorem measurable_encode_path (w : MatedCRT.Path2)
    (h : MatedCRT.IsLocallyFinite 1 w) :
    Measurable (fun path : ℕ → (MatedCRT.graph 1 w h).State =>
      fun i => meshGridEncodeMatedState (path i)) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.of_discrete.comp (measurable_pi_apply i)

open Classical in
/-- The coded walk is a probability measure on the local-finiteness domain. -/
theorem shiftedMeshCodedWalkLaw_univ (p : ShiftedMeshParameter) :
    shiftedMeshCodedWalkLaw p univ =
      if MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) then 1 else 0 := by
  classical
  unfold shiftedMeshCodedWalkLaw
  dsimp only
  by_cases h : MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)
  · rw [dite_eq_left h, ite_eq_left h, Measure.map_apply (measurable_encode_path _ h) MeasurableSet.univ]
    simp
  · simp [h]

instance (p : ShiftedMeshParameter) : IsFiniteMeasure (shiftedMeshCodedWalkLaw p) := by
  constructor
  rw [shiftedMeshCodedWalkLaw_univ]
  split <;> simp

/-- Total mass is jointly measurable in the path, grid, and starting vertex. -/
theorem measurable_shiftedMeshCodedWalkLaw_univ :
    Measurable (fun p : ShiftedMeshParameter => shiftedMeshCodedWalkLaw p univ) := by
  classical
  simp_rw [shiftedMeshCodedWalkLaw_univ]
  exact Measurable.ite (measurableSet_shiftedMesh_isLocallyFinite.preimage measurable_fst)
    measurable_const measurable_const

open Classical in
/-- A prefix has its product mass exactly when all of its codes are valid. -/
theorem shiftedMeshCodedWalkLaw_prefix (p : ShiftedMeshParameter)
    (s : ℕ → MeshGridStateCode) (n : ℕ) :
    shiftedMeshCodedWalkLaw p {path | ∀ i ≤ n, path i = s i} =
      if MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) ∧
          shiftedMeshCodePrefixValid p.1 s n then
        meshGridCodePrefixWeight 1 p.2 s n (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)
      else 0 := by
  classical
  have hset : MeasurableSet {path : ℕ → MeshGridStateCode | ∀ i ≤ n, path i = s i} := by
    rw [show {path : ℕ → MeshGridStateCode | ∀ i ≤ n, path i = s i} =
      ⋂ i : Fin (n + 1), {path | path i = s i} by
        ext path
        simp only [mem_ofPred_eq, mem_iInter]
        constructor
        · intro h i
          exact h i (Nat.lt_succ_iff.mp i.isLt)
        · intro h i hi
          exact h ⟨i, Nat.lt_succ_iff.mpr hi⟩]
    exact MeasurableSet.iInter (fun i => (measurableSet_singleton _).preimage (measurable_pi_apply (i : ℕ)))
  have hv : shiftedMeshCodePrefixValid p.1 s n ↔
      meshGridCodePrefixValid 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) n s := by
    rfl
  by_cases h : MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)
  · rw [shiftedMeshCodedWalkLaw, dite_eq_left h, Measure.map_apply (measurable_encode_path _ h) hset]
    by_cases hs : shiftedMeshCodePrefixValid p.1 s n
    · simp only [h, hs, and_self, ite_true]
      exact meshGridWalkLaw_codeCylinder 1 _ h p.2 n s (hv.mp hs)
    · simp only [h, hs, and_false, ite_false]
      exact meshGridWalkLaw_codeCylinder_invalid 1 _ h p.2 n s (fun hc => hs (hv.mpr hc))
  · simp [shiftedMeshCodedWalkLaw, h]

/-- Fixed coded-prefix probabilities vary measurably with the shifted grid and start. -/
theorem measurable_shiftedMeshCodedWalkLaw_prefix
    (s : ℕ → MeshGridStateCode) (n : ℕ) :
    Measurable (fun p : ShiftedMeshParameter =>
      shiftedMeshCodedWalkLaw p {path | ∀ i ≤ n, path i = s i}) := by
  classical
  simp_rw [shiftedMeshCodedWalkLaw_prefix]
  apply Measurable.ite
    ((measurableSet_shiftedMesh_isLocallyFinite.inter
      (measurableSet_shiftedMeshCodePrefixValid s n)).preimage measurable_fst)
  · exact measurable_shiftedMeshCodePrefixWeight_start s n
  · exact measurable_const

/-- The coded walk-law family is jointly measurable. -/
theorem measurable_shiftedMeshCodedWalkLaw : Measurable shiftedMeshCodedWalkLaw := by
  apply measurable_measure_of_countable_prefixes shiftedMeshCodedWalkLaw
    measurable_shiftedMeshCodedWalkLaw_univ
  intro n s
  classical
  let t : ℕ → MeshGridStateCode := fun i =>
    if hi : i ≤ n then s ⟨i, Finset.mem_Iic.mpr hi⟩ else Sum.inl 0
  have heq : cylinder (α := fun _ : ℕ => MeshGridStateCode) (Finset.Iic n) {s} = {path | ∀ i ≤ n, path i = t i} := by
    ext path
    simp only [mem_cylinder, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · intro h i hi
      have ht : t i = s ⟨i, Finset.mem_Iic.mpr hi⟩ := by simp [t, hi]
      rw [ht]
      exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h
      funext i
      have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
      simpa [t, hi] using h i hi
  rw [heq]
  exact measurable_shiftedMeshCodedWalkLaw_prefix t n

/-- The shifted coded walk law as a finite kernel. -/
def shiftedMeshCodedWalkKernel : Kernel ShiftedMeshParameter (ℕ → MeshGridStateCode) :=
  ⟨shiftedMeshCodedWalkLaw, measurable_shiftedMeshCodedWalkLaw⟩

instance : IsFiniteKernel shiftedMeshCodedWalkKernel := by
  refine ⟨⟨1, by simp, ?_⟩⟩
  intro p
  change shiftedMeshCodedWalkLaw p univ ≤ 1
  rw [shiftedMeshCodedWalkLaw_univ]
  split <;> simp

end LatticeProb
