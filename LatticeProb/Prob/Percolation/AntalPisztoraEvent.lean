import LatticeProb.Prob.Percolation.LatticeCubeConnectivity

/-!
# A finite-box event for Bernoulli bond percolation

The outer cube has radius `5N/4`.  Each tested inner cube has integer corners
and side exactly `N`.  A single outer component must cross the outer cube;
its paths crossing an inner cube may belong to different inner components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- The outer cube at an integer center and positive integer scale. -/
def apOuter (c : Vertex d) (N : {n : ℕ // 0 < n}) : Finset (Vertex d) :=
  latticeCube (fun i => (c i : ℝ))
    ⟨5 * (N.val : ℝ) / 4, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩

/-- The cube with lower integer corner `a` and side exactly `N`. -/
def apInner (a : Vertex d) (N : {n : ℕ // 0 < n}) : Finset (Vertex d) :=
  latticeCube (fun i => (a i : ℝ) + (N.val : ℝ) / 2)
    ⟨(N.val : ℝ) / 2, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩

/-- The lower face of an integer-side inner cube. -/
def apInnerLower (a : Vertex d) (N : {n : ℕ // 0 < n}) (i : Fin d) :
    Finset (Vertex d) :=
  latticeCubeLowerFace (fun j => (a j : ℝ) + (N.val : ℝ) / 2)
    ⟨(N.val : ℝ) / 2, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩ i

/-- The upper face of an integer-side inner cube. -/
def apInnerUpper (a : Vertex d) (N : {n : ℕ // 0 < n}) (i : Fin d) :
    Finset (Vertex d) :=
  latticeCubeUpperFace (fun j => (a j : ℝ) + (N.val : ℝ) / 2)
    ⟨(N.val : ℝ) / 2, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩ i

/-- Membership in the integer-side cube is the literal closed coordinate condition. -/
theorem mem_apInner_iff (a z : Vertex d) (N : {n : ℕ // 0 < n}) :
    z ∈ apInner a N ↔ ∀ i, (a i : ℝ) ≤ (z i : ℝ) ∧
      (z i : ℝ) ≤ (a i : ℝ) + N.val := by
  rw [apInner, mem_latticeCube_iff]
  simp only [abs_le]
  constructor <;> intro h i <;> have := h i <;> constructor <;> linarith

/-- The outer cube has exactly the stated coordinate bounds. -/
theorem mem_apOuter_iff (c z : Vertex d) (N : {n : ℕ // 0 < n}) :
    z ∈ apOuter c N ↔ ∀ i, |(z i : ℝ) - (c i : ℝ)| ≤ 5 * (N.val : ℝ) / 4 := by
  exact mem_latticeCube_iff _ _ _

/-- The inner lower face is the cube face with coordinate equal to the lower corner. -/
theorem mem_apInnerLower_iff (a z : Vertex d) (N : {n : ℕ // 0 < n}) (i : Fin d) :
    z ∈ apInnerLower a N i ↔ z ∈ apInner a N ∧ z i = a i := by
  rw [apInnerLower, mem_latticeCubeLowerFace_iff]
  change z ∈ apInner a N ∧ z i = ⌈(a i : ℝ) + (N.val : ℝ) / 2 -
    (N.val : ℝ) / 2⌉ ↔ _
  have h : (a i : ℝ) + (N.val : ℝ) / 2 - (N.val : ℝ) / 2 = (a i : ℝ) := by ring
  rw [h, Int.ceil_intCast]

/-- The inner upper face is the cube face with coordinate equal to the upper corner. -/
theorem mem_apInnerUpper_iff (a z : Vertex d) (N : {n : ℕ // 0 < n}) (i : Fin d) :
    z ∈ apInnerUpper a N i ↔ z ∈ apInner a N ∧ z i = a i + N.val := by
  rw [apInnerUpper, mem_latticeCubeUpperFace_iff]
  change z ∈ apInner a N ∧ z i = ⌊(a i : ℝ) + (N.val : ℝ) / 2 +
    (N.val : ℝ) / 2⌋ ↔ _
  have h : (a i : ℝ) + (N.val : ℝ) / 2 + (N.val : ℝ) / 2 =
      ((a i + (N.val : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.floor_intCast]

/-- A component crosses an inner cube by a path in its intersection with the cube,
independently for each direction. -/
def apComponentCrossesInner (c : Vertex d) (N : {n : ℕ // 0 < n})
    (G : SimpleGraph {z : Vertex d // z ∈ apOuter c N})
    (C : G.ConnectedComponent) (a : Vertex d) : Prop :=
  ∀ i, ∃ x y : {z : Vertex d // z ∈ apOuter c N},
    x.val ∈ apInnerLower a N i ∧ y.val ∈ apInnerUpper a N i ∧
    ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ C.supp ∧ z.val ∈ apInner a N

/-- The projected finite-graph property: a unique outer crossing component, attachment
of every sufficiently wide walk, and crossings of all contained side-`N` cubes. -/
def apProjectedProperty (c : Vertex d) (N : {n : ℕ // 0 < n})
    (G : SimpleGraph {z : Vertex d // z ∈ apOuter c N}) : Prop :=
  ∃ C : G.ConnectedComponent,
    latticeCubeComponentCrosses (fun i => (c i : ℝ))
      ⟨5 * (N.val : ℝ) / 4, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩ G C ∧
    (∀ D : G.ConnectedComponent,
      latticeCubeComponentCrosses (fun i => (c i : ℝ))
        ⟨5 * (N.val : ℝ) / 4, by
      simp only [Set.mem_Ioi]
      have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
      positivity⟩ G D → D = C) ∧
    (∀ x y : {z : Vertex d // z ∈ apOuter c N}, ∀ w : G.Walk x y,
      (∃ u ∈ w.support, ∃ v ∈ w.support, ∃ i : Fin d,
        (N.val : ℝ) / 2 < |(u.val i : ℝ) - (v.val i : ℝ)|) → x ∈ C.supp) ∧
    ∀ a : Vertex d, apInner a N ⊆ apOuter c N → apComponentCrossesInner c N G C a

/-- The event uses only the open graph induced on the actual outer lattice cube. -/
def apProjectedEvent (c : Vertex d) (N : {n : ℕ // 0 < n}) : Set (Configuration d) :=
  {ω | apProjectedProperty c N ((openGraph ω).induce (apOuter c N : Set (Vertex d)))}

/-- The projected event is measurable because it depends only on the finite induced graph. -/
theorem measurableSet_apProjectedEvent (c : Vertex d) (N : {n : ℕ // 0 < n}) :
    MeasurableSet (apProjectedEvent c N) :=
  measurableSet_induced_openGraph (apOuter c N) (apProjectedProperty c N)

/-- The all-open configuration satisfies the entire projected event at every positive scale. -/
theorem allOpen_mem_apProjectedEvent (c : Vertex d) (N : {n : ℕ // 0 < n}) :
    allOpen d ∈ apProjectedEvent c N := by
  classical
  have hN : (0 : ℝ) < N.val := by exact_mod_cast N.property
  let oc : Fin d → ℝ := fun i => (c i : ℝ)
  let orad : Set.Ioi (0 : ℝ) := ⟨5 * (N.val : ℝ) / 4, by
    simp only [Set.mem_Ioi]
    positivity⟩
  have hc : c ∈ apOuter c N := by
    rw [mem_apOuter_iff]
    intro i
    simp only [sub_self, abs_zero]
    positivity
  let G := (openGraph (allOpen d)).induce (apOuter c N : Set (Vertex d))
  let x : {z : Vertex d // z ∈ apOuter c N} := ⟨c, hc⟩
  let C := G.connectedComponentMk x
  have hpre : G.Preconnected := latticeCube_allOpen_preconnected oc orad
  have hmem (z : {z : Vertex d // z ∈ apOuter c N}) : z ∈ C.supp := by
    change G.connectedComponentMk z = G.connectedComponentMk x
    exact SimpleGraph.ConnectedComponent.sound (hpre z x)
  letI : Subsingleton G.ConnectedComponent := hpre.subsingleton_connectedComponent
  change apProjectedProperty c N G
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro i
    have hnonempty : (latticeCube oc orad).Nonempty := ⟨c, hc⟩
    obtain ⟨u, hu⟩ := latticeCubeLowerFace_nonempty oc orad i hnonempty
    obtain ⟨v, hv⟩ := latticeCubeUpperFace_nonempty oc orad i hnonempty
    have hu' : u ∈ apOuter c N := (Finset.mem_filter.mp hu).1
    have hv' : v ∈ apOuter c N := (Finset.mem_filter.mp hv).1
    exact ⟨⟨u, hu'⟩, ⟨v, hv'⟩, hmem _, hmem _, hu, hv⟩
  · intro D _
    exact Subsingleton.elim D C
  · intro u v w _
    exact hmem u
  · intro a hsub i
    let ic : Fin d → ℝ := fun j => (a j : ℝ) + (N.val : ℝ) / 2
    let ir : Set.Ioi (0 : ℝ) := ⟨(N.val : ℝ) / 2, by
      simp only [Set.mem_Ioi]
      positivity⟩
    have ha : a ∈ apInner a N := by
      rw [mem_apInner_iff]
      intro j
      constructor
      · exact le_rfl
      · linarith
    have hnonempty : (latticeCube ic ir).Nonempty := ⟨a, ha⟩
    obtain ⟨u, hu⟩ := latticeCubeLowerFace_nonempty ic ir i hnonempty
    obtain ⟨v, hv⟩ := latticeCubeUpperFace_nonempty ic ir i hnonempty
    have hu' : u ∈ apInner a N := (Finset.mem_filter.mp hu).1
    have hv' : v ∈ apInner a N := (Finset.mem_filter.mp hv).1
    let Gi := (openGraph (allOpen d)).induce (apInner a N : Set (Vertex d))
    let ui : {z : Vertex d // z ∈ apInner a N} := ⟨u, hu'⟩
    let vi : {z : Vertex d // z ∈ apInner a N} := ⟨v, hv'⟩
    have hi : Gi.Preconnected := latticeCube_allOpen_preconnected ic ir
    let f : Gi →g G := ⟨fun z => ⟨z.val, hsub z.property⟩, by
      intro p q hpq
      exact hpq⟩
    obtain ⟨w⟩ := hi ui vi
    refine ⟨f ui, f vi, hu, hv, w.map f, ?_⟩
    intro z hz
    constructor
    · exact hmem z
    · rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact v.property

/-- Membership expands to the unique outer crossing component, attachment of wide walks,
and the shared-component paths in every contained integer-side cube. -/
theorem mem_apProjectedEvent_iff (c : Vertex d) (N : {n : ℕ // 0 < n})
    (ω : Configuration d) :
    ω ∈ apProjectedEvent c N ↔
      ∃ C : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).ConnectedComponent,
        latticeCubeComponentCrosses (fun i => (c i : ℝ))
          ⟨5 * (N.val : ℝ) / 4, by
            simp only [Set.mem_Ioi]
            have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
            positivity⟩ ((openGraph ω).induce (apOuter c N : Set (Vertex d))) C ∧
        (∀ D : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).ConnectedComponent,
          latticeCubeComponentCrosses (fun i => (c i : ℝ))
            ⟨5 * (N.val : ℝ) / 4, by
              simp only [Set.mem_Ioi]
              have h : (0 : ℝ) < N.val := by exact_mod_cast N.property
              positivity⟩ ((openGraph ω).induce (apOuter c N : Set (Vertex d))) D → D = C) ∧
        (∀ x y : {z : Vertex d // z ∈ apOuter c N},
          ∀ w : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).Walk x y,
            (∃ u ∈ w.support, ∃ v ∈ w.support, ∃ i : Fin d,
              (N.val : ℝ) / 2 < |(u.val i : ℝ) - (v.val i : ℝ)|) → x ∈ C.supp) ∧
        ∀ a : Vertex d, apInner a N ⊆ apOuter c N → ∀ i,
          ∃ x y : {z : Vertex d // z ∈ apOuter c N},
            x.val ∈ apInnerLower a N i ∧ y.val ∈ apInnerUpper a N i ∧
            ∃ w : ((openGraph ω).induce (apOuter c N : Set (Vertex d))).Walk x y,
              ∀ z ∈ w.support, z ∈ C.supp ∧ z.val ∈ apInner a N := by
  rfl

/-- The all-closed configuration fails the projected event at the eligible scale 16. -/
theorem allClosed_not_mem_apProjectedEvent_sixteen :
    allClosed 2 ∉ apProjectedEvent (0 : Vertex 2) ⟨16, by decide⟩ := by
  intro h
  obtain ⟨C, hcross, _⟩ := h
  obtain ⟨x, y, hx, hy, hxl, hyu⟩ := hcross (0 : Fin 2)
  have hreach := C.reachable_of_mem_supp hx hy
  have hb :
      (⊥ : SimpleGraph {z : Vertex 2 // z ∈ apOuter 0 ⟨16, by decide⟩}).Reachable x y := by
    simpa only [openGraph_allClosed, SimpleGraph.induce_bot] using hreach
  have hxy := SimpleGraph.reachable_bot.mp hb
  have hl := (mem_latticeCubeLowerFace_iff _ _ (0 : Fin 2) x.val).mp hxl
  have hu := (mem_latticeCubeUpperFace_iff _ _ (0 : Fin 2) y.val).mp hyu
  have heq : x.val (0 : Fin 2) = y.val (0 : Fin 2) := by rw [hxy]
  norm_num at hl hu
  omega

end
end LatticeProb.Percolation
