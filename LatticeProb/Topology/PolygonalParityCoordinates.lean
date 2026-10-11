/-
# Original coordinate plane and Euclidean polygonal parity

The literal coordinate map `(x, y) ↦ !₂[x, y]` is a linear equivalence and a
continuous map. It takes closed and open segments to their exact Euclidean
counterparts and takes cyclic coordinate edge lists to cyclic Euclidean lists.
Thus geometric local separation applies on the original product plane to
arbitrary preconnected sets and actual continuous paths. Neighborhoods are
pulled back as open sets; no product norm ball is identified with a round disk.
-/
import LatticeProb.Topology.PolygonalParityLocalSides



open Metric Set
namespace LatticeProb.Topology.PolygonalParity

/-- The linear coordinate identification `(x, y) ↦ !₂[x, y]`; its inverse is
`z ↦ (z 0, z 1)`. -/
noncomputable def coordinateEquiv : (ℝ × ℝ) ≃ₗ[ℝ] Plane where
  toFun z := Plane.mk z.1 z.2
  invFun z := (z 0, z 1)
  left_inv _ := rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

/-- The coordinate identification is continuous for the original product
 topology and the Euclidean plane topology. -/
theorem continuous_coordinateEquiv : Continuous coordinateEquiv := by
  change Continuous (fun z : ℝ × ℝ => WithLp.toLp 2 ![z.1, z.2])
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

/-- A closed coordinate segment has exactly the corresponding Euclidean image. -/
theorem coordinateEquiv_image_segment (a b : ℝ × ℝ) :
    coordinateEquiv '' segment ℝ a b = segment ℝ (coordinateEquiv a) (coordinateEquiv b) :=
  image_segment ℝ coordinateEquiv.toAffineEquiv.toAffineMap a b

/-- An open coordinate segment has exactly the corresponding Euclidean image. -/
theorem coordinateEquiv_image_openSegment (a b : ℝ × ℝ) :
    coordinateEquiv '' openSegment ℝ a b =
      openSegment ℝ (coordinateEquiv a) (coordinateEquiv b) :=
  image_openSegment ℝ coordinateEquiv.toAffineEquiv.toAffineMap a b

/-- The determinant in the original product coordinates. -/
def coordinateDet (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

/-- The coordinate map preserves the determinant exactly. -/
theorem det_coordinateEquiv (a b : ℝ × ℝ) :
    Plane.det (coordinateEquiv a) (coordinateEquiv b) = coordinateDet a b := rfl

/-- The union of the closed segments in an original-coordinate edge list. -/
def coordinateEdgeTrace (L : List ((ℝ × ℝ) × (ℝ × ℝ))) : Set (ℝ × ℝ) :=
  ⋃ P ∈ L, segment ℝ P.1 P.2

/-- Map both endpoints of each coordinate edge into the Euclidean plane. -/
noncomputable def coordinateEdges (L : List ((ℝ × ℝ) × (ℝ × ℝ))) : List Piece :=
  L.map (fun P => (coordinateEquiv P.1, coordinateEquiv P.2))

/-- Mapping an edge list preserves its exact trace. -/
theorem coordinateEquiv_image_edgeTrace (L : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    coordinateEquiv '' coordinateEdgeTrace L = cover (coordinateEdges L) := by
  ext z
  simp only [coordinateEdgeTrace, cover, coordinateEdges, mem_image, mem_iUnion,
    exists_prop, List.mem_map]
  constructor
  · rintro ⟨w, ⟨P, hP, hw⟩, rfl⟩
    refine ⟨(coordinateEquiv P.1, coordinateEquiv P.2), ⟨P, hP, rfl⟩, ?_⟩
    change coordinateEquiv w ∈ segment ℝ (coordinateEquiv P.1) (coordinateEquiv P.2)
    rw [← coordinateEquiv_image_segment]
    exact ⟨w, hw, rfl⟩
  · rintro ⟨_, ⟨P, hP, rfl⟩, hz⟩
    change z ∈ segment ℝ (coordinateEquiv P.1) (coordinateEquiv P.2) at hz
    rw [← coordinateEquiv_image_segment] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, ⟨P, hP, hw⟩, rfl⟩

/-- Cyclic coordinate edges map to the exact cyclic Euclidean edge list. -/
theorem coordinateEdges_zip_rotate (vs : List (ℝ × ℝ)) :
    coordinateEdges (vs.zip (vs.rotate 1)) = edgesOf (vs.map coordinateEquiv) := by
  rw [coordinateEdges, edgesOf, ← List.map_rotate, List.zip_map]
  rfl

/-- **Local separation on the original plane.** An isolated edge interior in
an actual cyclic coordinate list has an open neighborhood whose opposite
determinant sides cannot be joined by a preconnected set avoiding the loop.
Closedness, ray genericity and parity separation are all derived in the proof. -/
theorem exists_coordinate_local_separation (vs : List (ℝ × ℝ))
    {L₁ L₂ : List ((ℝ × ℝ) × (ℝ × ℝ))} {a b p : ℝ × ℝ}
    (hedges : vs.zip (vs.rotate 1) = L₁ ++ (a, b) :: L₂)
    (hnd : ∀ P ∈ vs.zip (vs.rotate 1), P.1 ≠ P.2)
    (hp : p ∈ openSegment ℝ a b)
    (h1 : p ∉ coordinateEdgeTrace L₁) (h2 : p ∉ coordinateEdgeTrace L₂) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧ ∀ x y : ℝ × ℝ,
      x ∈ U → y ∈ U → coordinateDet (b - a) p < coordinateDet (b - a) x →
      coordinateDet (b - a) y < coordinateDet (b - a) p →
      x ∉ coordinateEdgeTrace (vs.zip (vs.rotate 1)) ∧
      y ∉ coordinateEdgeTrace (vs.zip (vs.rotate 1)) ∧
      ∀ S : Set (ℝ × ℝ), IsPreconnected S → x ∈ S → y ∈ S →
        (S ∩ coordinateEdgeTrace (vs.zip (vs.rotate 1))).Nonempty := by
  let E := vs.zip (vs.rotate 1)
  have hE : coordinateEdges E = coordinateEdges L₁ ++
      (coordinateEquiv a, coordinateEquiv b) :: coordinateEdges L₂ := by
    change coordinateEdges (vs.zip (vs.rotate 1)) = _
    rw [hedges, coordinateEdges, List.map_append, List.map_cons]
    rfl
  have hC : IsClosedChain (coordinateEdges L₁ ++
      (coordinateEquiv a, coordinateEquiv b) :: coordinateEdges L₂) := by
    rw [← hE]
    change IsClosedChain (coordinateEdges (vs.zip (vs.rotate 1)))
    rw [coordinateEdges_zip_rotate]
    exact isClosedChain_edgesOf _
  have hnondeg : ∀ P ∈ coordinateEdges L₁ ++
      (coordinateEquiv a, coordinateEquiv b) :: coordinateEdges L₂, P.Nondeg := by
    rw [← hE]
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    exact fun heq => hnd Q hQ (coordinateEquiv.injective heq)
  have hp' : coordinateEquiv p ∈ openSegment ℝ (coordinateEquiv a) (coordinateEquiv b) := by
    rw [← coordinateEquiv_image_openSegment]
    exact ⟨p, hp, rfl⟩
  have hnot : ∀ L : List ((ℝ × ℝ) × (ℝ × ℝ)), p ∉ coordinateEdgeTrace L →
      coordinateEquiv p ∉ cover (coordinateEdges L) := by
    intro L hpmem hpcov
    rw [← coordinateEquiv_image_edgeTrace] at hpcov
    obtain ⟨q, hq, heq⟩ := hpcov
    exact hpmem (coordinateEquiv.injective heq ▸ hq)
  obtain ⟨ε, hε, hsep⟩ := exists_halfBall_separation hnondeg hC hp' (hnot L₁ h1) (hnot L₂ h2)
  let U := coordinateEquiv ⁻¹' ball (coordinateEquiv p) ε
  refine ⟨U, isOpen_ball.preimage continuous_coordinateEquiv, mem_ball_self hε,
    fun x y hx hy hxside hyside => ?_⟩
  have hxside' : Plane.det (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv p) <
      Plane.det (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv x) := by
    exact hxside
  have hyside' : Plane.det (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv y) <
      Plane.det (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv p) := by
    exact hyside
  obtain ⟨hxavoid, hyavoid, hmeet⟩ := hsep _ _ hx hy hxside' hyside'
  have himage : coordinateEquiv '' coordinateEdgeTrace E =
      cover (coordinateEdges L₁ ++ (coordinateEquiv a, coordinateEquiv b) :: coordinateEdges L₂) := by
    rw [coordinateEquiv_image_edgeTrace, hE]
  refine ⟨fun hxE => hxavoid (himage ▸ ⟨x, hxE, rfl⟩),
    fun hyE => hyavoid (himage ▸ ⟨y, hyE, rfl⟩), fun S hS hxS hyS => ?_⟩
  obtain ⟨z, hzS, hzE⟩ := hmeet (coordinateEquiv '' S)
    (hS.image coordinateEquiv continuous_coordinateEquiv.continuousOn)
    ⟨x, hxS, rfl⟩ ⟨y, hyS, rfl⟩
  rw [← himage] at hzE
  obtain ⟨w, hwS, rfl⟩ := hzS
  obtain ⟨q, hqE, heq⟩ := hzE
  exact ⟨w, hwS, coordinateEquiv.injective heq ▸ hqE⟩

/-- An actual continuous path joining opposite determinant sides in the
produced coordinate neighborhood intersects the original cyclic polygonal
trace. Connectedness and endpoint membership come from the path itself. -/
theorem exists_coordinate_path_intersection (vs : List (ℝ × ℝ))
    {L₁ L₂ : List ((ℝ × ℝ) × (ℝ × ℝ))} {a b p : ℝ × ℝ}
    (hedges : vs.zip (vs.rotate 1) = L₁ ++ (a, b) :: L₂)
    (hnd : ∀ P ∈ vs.zip (vs.rotate 1), P.1 ≠ P.2)
    (hp : p ∈ openSegment ℝ a b)
    (h1 : p ∉ coordinateEdgeTrace L₁) (h2 : p ∉ coordinateEdgeTrace L₂) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧ ∀ x y : ℝ × ℝ,
      x ∈ U → y ∈ U → coordinateDet (b - a) p < coordinateDet (b - a) x →
      coordinateDet (b - a) y < coordinateDet (b - a) p →
      ∀ r : Path x y, ∃ t : unitInterval, r t ∈ coordinateEdgeTrace (vs.zip (vs.rotate 1)) := by
  obtain ⟨U, hU, hpU, hsep⟩ := exists_coordinate_local_separation vs hedges hnd hp h1 h2
  refine ⟨U, hU, hpU, fun x y hx hy hxside hyside r => ?_⟩
  obtain ⟨_, _, hmeet⟩ := hsep x y hx hy hxside hyside
  obtain ⟨z, hzrange, hztrace⟩ := hmeet (range r)
    (isConnected_range r.continuous).isPreconnected r.source_mem_range r.target_mem_range
  obtain ⟨t, rfl⟩ := hzrange
  exact ⟨t, hztrace⟩

end LatticeProb.Topology.PolygonalParity
