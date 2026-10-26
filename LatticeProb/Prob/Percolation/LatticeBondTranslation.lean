import LatticeProb.Prob.Percolation.LatticeBondGraph

/-!
# Translation of canonical unordered lattice bonds

Bonds translate by adding `z` to both endpoints. Configurations use the pullback by `-z`,
so an open bond from `x` to `y` moves to the bond from `x + z` to `y + z`.
All constructions act on the entire canonical bond and configuration carriers.
-/

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- Adding the same lattice vector to both endpoints preserves ℓ¹ distance. -/
theorem latticeL1Dist_add_right (x y z : Vertex d) :
    latticeL1Dist (x + z) (y + z) = latticeL1Dist x y := by
  simp only [latticeL1Dist, Pi.add_apply, add_sub_add_right_eq_sub]

/-- Nearest-neighbor adjacency is covariant under endpoint addition. -/
theorem nearestNeighborGraph_adj_add_iff (x y z : Vertex d) :
    (nearestNeighborGraph d).Adj (x + z) (y + z) ↔
      (nearestNeighborGraph d).Adj x y := by
  rw [lattice_adj_iff_l1Dist, lattice_adj_iff_l1Dist, latticeL1Dist_add_right]

/-- Literal endpoint addition on unordered bonds, retaining the distance-one witness. -/
private def translateBond (z : Vertex d) (e : Bond d) : Bond d :=
  ⟨e.val.map (fun x => x + z), by
    obtain ⟨x, y, hxy, hdist⟩ := e.property
    refine ⟨x + z, y + z, ?_, ?_⟩
    · rw [hxy, Sym2.map_mk]
    · exact (latticeL1Dist_add_right x y z).trans hdist⟩

/-- Endpoint addition composes by addition of the displacement vectors. -/
private theorem translateBond_add (z w : Vertex d) (e : Bond d) :
    translateBond z (translateBond w e) = translateBond (w + z) e := by
  apply Subtype.ext
  obtain ⟨x, y, hxy, _⟩ := e.property
  simp only [translateBond, hxy, Sym2.map_mk, add_assoc]

/-- Zero endpoint displacement fixes each genuine bond. -/
private theorem translateBond_zero (e : Bond d) : translateBond 0 e = e := by
  apply Subtype.ext
  obtain ⟨x, y, hxy, _⟩ := e.property
  simp only [translateBond, hxy, Sym2.map_mk, add_zero]

/-- The equivalence on genuine bonds adding `z` to both unordered endpoints. -/
def bondTranslation (z : Vertex d) : Bond d ≃ Bond d where
  toFun := translateBond z
  invFun := translateBond (-z)
  left_inv e := by rw [translateBond_add, add_neg_cancel, translateBond_zero]
  right_inv e := by rw [translateBond_add, neg_add_cancel, translateBond_zero]

/-- Every endpoint presentation translates to precisely the two translated endpoints. -/
theorem bondTranslation_endpoints (z : Vertex d) (e : Bond d) (x y : Vertex d)
    (h : e.val = s(x, y)) :
    (bondTranslation z e).val = s(x + z, y + z) := by
  change Sym2.map (fun t => t + z) e.val = _
  rw [h, Sym2.map_mk]

/-- The full underlying unordered pair is mapped by literal endpoint addition. -/
theorem bondTranslation_val (z : Vertex d) (e : Bond d) :
    (bondTranslation z e).val = e.val.map (fun x => x + z) := rfl

/-- The inverse bond equivalence subtracts the same displacement. -/
theorem bondTranslation_symm (z : Vertex d) :
    (bondTranslation z).symm = bondTranslation (-z) := by
  apply Equiv.ext
  intro e
  rfl

/-- Translation by zero fixes every bond. -/
theorem bondTranslation_zero (e : Bond d) : bondTranslation 0 e = e :=
  translateBond_zero e

/-- Successive translations add their displacements. -/
theorem bondTranslation_add (z w : Vertex d) (e : Bond d) :
    bondTranslation z (bondTranslation w e) = bondTranslation (z + w) e := by
  rw [add_comm z w]
  exact translateBond_add z w e

/-- A translated adjacency witness gives the translated genuine unordered bond. -/
theorem bondTranslation_bondOfAdjacent (z : Vertex d) {x y : Vertex d}
    (h : (nearestNeighborGraph d).Adj x y) :
    bondTranslation z (bondOfAdjacent h) =
      bondOfAdjacent ((nearestNeighborGraph_adj_add_iff x y z).mpr h) := by
  apply Subtype.ext
  exact bondTranslation_endpoints z (bondOfAdjacent h) x y rfl

/-- Configuration translation is product reindexing by the inverse bond translation. -/
def configurationTranslation (z : Vertex d) : Configuration d ≃ Configuration d where
  toFun ω e := ω (bondTranslation (-z) e)
  invFun ω e := ω (bondTranslation z e)
  left_inv ω := by
    funext e
    change ω (bondTranslation (-z) (bondTranslation z e)) = ω e
    rw [bondTranslation_add, neg_add_cancel, bondTranslation_zero]
  right_inv ω := by
    funext e
    change ω (bondTranslation z (bondTranslation (-z) e)) = ω e
    rw [bondTranslation_add, add_neg_cancel, bondTranslation_zero]

/-- The value at every bond is exactly the original value at its translate by `-z`. -/
theorem configurationTranslation_apply (z : Vertex d) (ω : Configuration d) (e : Bond d) :
    configurationTranslation z ω e = ω (bondTranslation (-z) e) := rfl

/-- Moving a bond and its configuration together preserves its Boolean status. -/
theorem configurationTranslation_apply_translated (z : Vertex d)
    (ω : Configuration d) (e : Bond d) :
    configurationTranslation z ω (bondTranslation z e) = ω e := by
  rw [configurationTranslation_apply, bondTranslation_add, neg_add_cancel, bondTranslation_zero]

/-- The inverse configuration translation has the negative displacement. -/
theorem configurationTranslation_symm (z : Vertex d) :
    (configurationTranslation z).symm = configurationTranslation (-z) := by
  apply Equiv.ext
  intro ω
  funext e
  change ω (bondTranslation z e) = ω (bondTranslation (-(-z)) e)
  rw [neg_neg]

/-- Zero displacement fixes every configuration. -/
theorem configurationTranslation_zero (ω : Configuration d) :
    configurationTranslation 0 ω = ω := by
  funext e
  simp only [configurationTranslation_apply, neg_zero, bondTranslation_zero]

/-- Configuration translations obey the additive group law pointwise. -/
theorem configurationTranslation_add (z w : Vertex d) (ω : Configuration d) :
    configurationTranslation z (configurationTranslation w ω) =
      configurationTranslation (z + w) ω := by
  funext e
  simp only [configurationTranslation_apply, bondTranslation_add, neg_add, add_comm]

/-- Open adjacency moves by `+z` under the chosen configuration pullback convention. -/
theorem openGraph_adj_translation_iff (z : Vertex d) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (configurationTranslation z ω)).Adj (x + z) (y + z) ↔
      (openGraph ω).Adj x y := by
  constructor
  · rintro ⟨h, ho⟩
    have hxy := (nearestNeighborGraph_adj_add_iff x y z).mp h
    refine ⟨hxy, ?_⟩
    have hb := bondTranslation_bondOfAdjacent z hxy
    rw [← hb, configurationTranslation_apply_translated] at ho
    exact ho
  · rintro ⟨h, ho⟩
    refine ⟨(nearestNeighborGraph_adj_add_iff x y z).mpr h, ?_⟩
    rw [← bondTranslation_bondOfAdjacent z h, configurationTranslation_apply_translated]
    exact ho

end LatticeProb.Percolation
