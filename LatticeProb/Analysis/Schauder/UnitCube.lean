import LatticeProb.Analysis.Schauder.Continuum

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.TwoScale.UnitCube`.

# The topology of the unit cube

The open unit cube `Q = (0,1)^d` is open and measurable, its closure is the closed cube
`[0,1]^d`, defined coordinatewise, and the closed cube is compact. The closure statement is a
single equality, from which the two inclusions used elsewhere are read off. Nothing about
functions on the cube is proved here.
-/

open MeasureTheory

noncomputable section

namespace LatticeProb.Analysis.Schauder

variable {d : ℕ}

/-- The closed unit cube `[0,1]^d`. -/
def closedCube (d : ℕ) : Set (Euc d) := {z | ∀ i, z i ∈ Set.Icc (0 : ℝ) 1}

/-- The open unit cube is open. -/
theorem isOpen_unitCube : IsOpen (unitCube d) := by
  have h : unitCube d = ⋂ i : Fin d, {y : Euc d | 0 < y i} ∩ {y | y i < 1} := by
    ext y
    simp [unitCube]
  rw [h]
  refine isOpen_iInter_of_finite fun i => ?_
  have hcont : Continuous (fun y : Euc d => y i) := by fun_prop
  exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)

/-- The open unit cube is measurable. -/
theorem measurableSet_unitCube : MeasurableSet (unitCube d) :=
  isOpen_unitCube.measurableSet

/-- The open unit cube lies in the closed unit cube. -/
theorem unitCube_subset_closedCube : unitCube d ⊆ closedCube d :=
  fun _ hz i => ⟨(hz i).1.le, (hz i).2.le⟩

/-- The closure of the open unit cube `(0,1)^d` is the closed unit cube `[0,1]^d`: the closure
of a product of intervals is the product of the closures. -/
theorem closure_unitCube_eq_closedCube : closure (unitCube d) = closedCube d := by
  have h : unitCube d = (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph ⁻¹'
      Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [unitCube]
  rw [h, ← Homeomorph.preimage_closure, closure_pi_set]
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
    closure_Ioo (zero_ne_one' ℝ)]
  rfl

/-- The closed unit cube lies in the closure of the open one. -/
theorem closedCube_subset_closure_unitCube : closedCube d ⊆ closure (unitCube d) :=
  closure_unitCube_eq_closedCube.ge

/-- Every point of the closure of the open unit cube has all coordinates in `[0,1]`. -/
theorem coord_mem_Icc_of_mem_closure_unitCube {z : Euc d} (hz : z ∈ closure (unitCube d))
    (i : Fin d) : 0 ≤ z i ∧ z i ≤ 1 :=
  closure_unitCube_eq_closedCube.le hz i

/-- The closed unit cube is compact. -/
theorem isCompact_closedCube : IsCompact (closedCube d) := by
  have : closedCube d =
      (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
    ext z
    simp only [closedCube, Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    exact ⟨fun h => ⟨z.ofLp, h, rfl⟩, fun ⟨y, hy, hyz⟩ => hyz ▸ hy⟩
  rw [this]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

/-- The closure of the open unit cube is compact. -/
theorem isCompact_closure_unitCube : IsCompact (closure (unitCube d)) := by
  rw [closure_unitCube_eq_closedCube]
  exact isCompact_closedCube

end LatticeProb.Analysis.Schauder

end
