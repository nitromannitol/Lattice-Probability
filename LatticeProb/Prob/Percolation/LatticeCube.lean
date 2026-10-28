import LatticeProb.Prob.Percolation.FiniteRegionMeasurable
import Mathlib.Data.Int.Interval

/-!
# Closed lattice cubes

A cube is the integer intersection of a closed real cube of positive radius.
Its coordinate faces use extrema among the actual lattice points, including when
there are no such points.
-/

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- The lattice points in a closed real cube of positive radius. -/
def latticeCubeSet (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) : Set (Vertex d) :=
  {z | ∀ i, |(z i : ℝ) - c i| ≤ r.val}

/-- Membership is the coordinatewise integer interval condition. -/
theorem mem_latticeCubeSet_iff (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (z : Vertex d) :
    z ∈ latticeCubeSet c r ↔
      ∀ i, ⌈c i - r.val⌉ ≤ z i ∧ z i ≤ ⌊c i + r.val⌋ := by
  simp only [latticeCubeSet, Set.mem_setOf_eq, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · intro hz i
    obtain ⟨ha, hb⟩ := hz i
    constructor <;> linarith
  · intro hz i
    obtain ⟨ha, hb⟩ := hz i
    constructor <;> linarith

/-- The closed lattice cube has finitely many vertices. -/
theorem finite_latticeCubeSet (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) :
    (latticeCubeSet c r).Finite := by
  have h := Set.Finite.pi' (fun i : Fin d =>
    Set.finite_Icc (⌈c i - r.val⌉) (⌊c i + r.val⌋))
  apply h.subset
  intro z hz i
  exact (mem_latticeCubeSet_iff c r z).mp hz i

/-- The finite carrier of the closed lattice cube. -/
def latticeCube (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) : Finset (Vertex d) :=
  (finite_latticeCubeSet c r).toFinset

/-- The finite carrier has exactly the defining cube vertices. -/
theorem mem_latticeCube_iff (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) (z : Vertex d) :
    z ∈ latticeCube c r ↔ ∀ i, |(z i : ℝ) - c i| ≤ r.val := by
  exact Set.Finite.mem_toFinset _

/-- The lower coordinate face consists of the actual minimizers in the cube. -/
def latticeCubeLowerFace (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) : Finset (Vertex d) :=
  (latticeCube c r).filter fun z => ∀ w ∈ latticeCube c r, z i ≤ w i

/-- The upper coordinate face consists of the actual maximizers in the cube. -/
def latticeCubeUpperFace (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) : Finset (Vertex d) :=
  (latticeCube c r).filter fun z => ∀ w ∈ latticeCube c r, w i ≤ z i

/-- A lower face vertex is exactly a cube vertex at the lower integer endpoint. -/
theorem mem_latticeCubeLowerFace_iff (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) (z : Vertex d) :
    z ∈ latticeCubeLowerFace c r i ↔
      z ∈ latticeCube c r ∧ z i = ⌈c i - r.val⌉ := by
  classical
  simp only [latticeCubeLowerFace, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hmin⟩
    have bounds := (mem_latticeCubeSet_iff c r z).mp
      ((Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mp hz)
    let w : Vertex d := Function.update z i ⌈c i - r.val⌉
    have hw : w ∈ latticeCube c r := by
      apply (Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mpr
      apply (mem_latticeCubeSet_iff c r w).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa [w] using And.intro (le_refl ⌈c i - r.val⌉)
          (le_trans (bounds i).1 (bounds i).2)
      · simpa [w, Function.update_of_ne hji] using bounds j
    refine ⟨hz, le_antisymm ?_ (bounds i).1⟩
    simpa [w] using hmin w hw
  · rintro ⟨hz, heq⟩
    refine ⟨hz, ?_⟩
    intro w hw
    rw [heq]
    exact ((mem_latticeCubeSet_iff c r w).mp
      ((Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mp hw) i).1

/-- An upper face vertex is exactly a cube vertex at the upper integer endpoint. -/
theorem mem_latticeCubeUpperFace_iff (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) (z : Vertex d) :
    z ∈ latticeCubeUpperFace c r i ↔
      z ∈ latticeCube c r ∧ z i = ⌊c i + r.val⌋ := by
  classical
  simp only [latticeCubeUpperFace, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hmax⟩
    have bounds := (mem_latticeCubeSet_iff c r z).mp
      ((Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mp hz)
    let w : Vertex d := Function.update z i ⌊c i + r.val⌋
    have hw : w ∈ latticeCube c r := by
      apply (Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mpr
      apply (mem_latticeCubeSet_iff c r w).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa [w] using And.intro (le_trans (bounds i).1 (bounds i).2)
          (le_refl ⌊c i + r.val⌋)
      · simpa [w, Function.update_of_ne hji] using bounds j
    refine ⟨hz, le_antisymm (bounds i).2 ?_⟩
    simpa [w] using hmax w hw
  · rintro ⟨hz, heq⟩
    refine ⟨hz, ?_⟩
    intro w hw
    rw [heq]
    exact ((mem_latticeCubeSet_iff c r w).mp
      ((Set.Finite.mem_toFinset (finite_latticeCubeSet c r)).mp hw) i).2

/-- A nonempty cube has a nonempty lower coordinate face. -/
theorem latticeCubeLowerFace_nonempty (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) (h : (latticeCube c r).Nonempty) :
    (latticeCubeLowerFace c r i).Nonempty := by
  classical
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (latticeCube c r) (fun z => z i) h
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, hmin⟩⟩

/-- A nonempty cube has a nonempty upper coordinate face. -/
theorem latticeCubeUpperFace_nonempty (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) (h : (latticeCube c r).Nonempty) :
    (latticeCubeUpperFace c r i).Nonempty := by
  classical
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (latticeCube c r) (fun z => z i) h
  exact ⟨z, Finset.mem_filter.mpr ⟨hz, hmax⟩⟩

/-- If the cube is empty, both of its coordinate faces are empty. -/
theorem latticeCube_faces_eq_empty (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (i : Fin d) (h : latticeCube c r = ∅) :
    latticeCubeLowerFace c r i = ∅ ∧ latticeCubeUpperFace c r i = ∅ := by
  simp [latticeCubeLowerFace, latticeCubeUpperFace, h]

/-- One component meets both extremal faces in every coordinate direction. -/
def latticeCubeComponentCrosses (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (G : SimpleGraph {z : Vertex d // z ∈ latticeCube c r})
    (C : G.ConnectedComponent) : Prop :=
  ∀ i, ∃ x y, x ∈ C.supp ∧ y ∈ C.supp ∧
    x.val ∈ latticeCubeLowerFace c r i ∧ y.val ∈ latticeCubeUpperFace c r i

/-- Component crossing is witnessed in each direction by an injective induced-graph path. -/
theorem latticeCubeComponentCrosses_iff_path (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (G : SimpleGraph {z : Vertex d // z ∈ latticeCube c r})
    (C : G.ConnectedComponent) :
    latticeCubeComponentCrosses c r G C ↔
      ∀ i, ∃ x y, x ∈ C.supp ∧ y ∈ C.supp ∧
        x.val ∈ latticeCubeLowerFace c r i ∧ y.val ∈ latticeCubeUpperFace c r i ∧
        ∃ p : G.Walk x y, p.IsPath := by
  constructor
  · intro h i
    obtain ⟨x, y, hx, hy, hxl, hyu⟩ := h i
    obtain ⟨p, hp⟩ := (C.reachable_of_mem_supp hx hy).exists_isPath
    exact ⟨x, y, hx, hy, hxl, hyu, p, hp⟩
  · intro h i
    obtain ⟨x, y, hx, hy, hxl, hyu, _⟩ := h i
    exact ⟨x, y, hx, hy, hxl, hyu⟩

/-- The cube crossing event uses one component of the actual induced open graph. -/
def latticeCubeCrossingEvent (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) :
    Set (Configuration d) :=
  {ω | ∃ C : ((openGraph ω).induce (latticeCube c r : Set (Vertex d))).ConnectedComponent,
    latticeCubeComponentCrosses c r ((openGraph ω).induce (latticeCube c r : Set (Vertex d))) C}

/-- Crossing a fixed finite lattice cube is a measurable bond event. -/
theorem measurableSet_latticeCubeCrossingEvent (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) :
    MeasurableSet (latticeCubeCrossingEvent c r) := by
  exact measurableSet_induced_openGraph (latticeCube c r)
    (fun G => ∃ C : G.ConnectedComponent, latticeCubeComponentCrosses c r G C)

/-- In the cube centered at one quarter with radius three quarters, coordinates are 0 or 1. -/
theorem quarter_cube_mem_iff (z : Vertex 2) :
    z ∈ latticeCube (fun _ => (1 : ℝ) / 4) ⟨(3 : ℝ) / 4, by norm_num⟩ ↔
      ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
  change z ∈ (finite_latticeCubeSet (fun _ => (1 : ℝ) / 4)
    ⟨(3 : ℝ) / 4, by norm_num⟩).toFinset ↔ _
  rw [Set.Finite.mem_toFinset, mem_latticeCubeSet_iff]
  norm_num

/-- The all-open two-dimensional quarter-centered cube crosses both coordinate directions. -/
theorem allOpen_quarter_cube_crosses :
    allOpen 2 ∈ latticeCubeCrossingEvent (fun _ => (1 : ℝ) / 4)
      ⟨(3 : ℝ) / 4, by norm_num⟩ := by
  classical
  let c : Fin 2 → ℝ := fun _ => (1 : ℝ) / 4
  let r : Set.Ioi (0 : ℝ) := ⟨(3 : ℝ) / 4, by norm_num⟩
  have hzero : (0 : Vertex 2) ∈ latticeCube c r := by
    apply (quarter_cube_mem_iff 0).mpr
    intro i
    simp
  have hunit (i : Fin 2) : LatticeProb.unit i ∈ latticeCube c r := by
    apply (quarter_cube_mem_iff (LatticeProb.unit i)).mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [LatticeProb.unit]
  let G := (openGraph (allOpen 2)).induce (latticeCube c r : Set (Vertex 2))
  let x : {z : Vertex 2 // z ∈ latticeCube c r} := ⟨0, hzero⟩
  let C := G.connectedComponentMk x
  change ∃ C : G.ConnectedComponent, latticeCubeComponentCrosses c r G C
  refine ⟨C, ?_⟩
  intro i
  let y : {z : Vertex 2 // z ∈ latticeCube c r} := ⟨LatticeProb.unit i, hunit i⟩
  have hx : x ∈ C.supp := by simp [C]
  have hxy : G.Adj x y := by
    change (openGraph (allOpen 2)).Adj 0 (LatticeProb.unit i)
    rw [openGraph_allOpen]
    exact LatticeProb.Graph.Zd.adj_iff.mpr ⟨i, Or.inl (by simp)⟩
  have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hxy
  refine ⟨x, y, hx, hy, ?_, ?_⟩
  · apply (mem_latticeCubeLowerFace_iff c r i 0).mpr
    refine ⟨hzero, ?_⟩
    norm_num [c, r]
  · apply (mem_latticeCubeUpperFace_iff c r i (LatticeProb.unit i)).mpr
    refine ⟨hunit i, ?_⟩
    simp only [LatticeProb.unit, Pi.single_eq_same]
    norm_num [c, r]

/-- A small cube centered at one half contains no lattice vertices. -/
theorem half_cube_empty :
    latticeCube (fun _ : Fin 2 => (1 : ℝ) / 2) ⟨(1 : ℝ) / 8, by norm_num⟩ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h := (mem_latticeCubeSet_iff (fun _ : Fin 2 => (1 : ℝ) / 2)
    ⟨(1 : ℝ) / 8, by norm_num⟩ z).mp
      ((finite_latticeCubeSet _ _).mem_toFinset.mp hz)
  have h0 := h 0
  norm_num at h0
  omega

end
end LatticeProb.Percolation
