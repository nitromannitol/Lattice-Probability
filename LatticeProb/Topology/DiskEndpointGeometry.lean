module

/-
# Radial geometry at a polygonal disk endpoint

A nondegenerate chord from a unit-circle point into the closed coordinate disk
has strictly negative radial pairing. A simple finite chain has a neighborhood
of its first endpoint meeting only its first segment. The proofs use the exact
squared coordinate radius and compactness of the remaining finite trace.
-/
public import LatticeProb.Topology.DiskCircleParityInternal

@[expose] public section



open Set Metric
namespace LatticeProb.Topology
open PolygonalParity

/-- The radial pairing of the displacement from `a` to `b`, in the original
product coordinates. -/
def coordinateRadial (a b : ℝ × ℝ) : ℝ :=
  a.1 * (b.1 - a.1) + a.2 * (b.2 - a.2)

/-- A nonzero coordinate vector has strictly positive squared radius. -/
theorem coordinate_square_pos {z : ℝ × ℝ} (hz : z ≠ 0) :
    0 < z.1 ^ 2 + z.2 ^ 2 := by
  have hn : coordinateEquiv z ≠ 0 := by
    intro h
    exact hz (coordinateEquiv.injective (h.trans (coordinateEquiv.map_zero).symm))
  have h := sq_pos_of_pos (norm_pos_iff.mpr hn)
  rwa [Plane.norm_sq_eq] at h

/-- **Strict inward chord pairing.** A nondegenerate chord from a unit-circle
point into the closed round coordinate disk has negative radial pairing.
This includes chords whose second endpoint also lies on the circle. -/
theorem coordinateRadial_neg_of_mem_disk {a b : ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) (hb : b.1 ^ 2 + b.2 ^ 2 ≤ 1)
    (hab : a ≠ b) : coordinateRadial a b < 0 := by
  have hd := coordinate_square_pos (sub_ne_zero.mpr hab.symm)
  have hid : 2 * coordinateRadial a b =
      (b.1 ^ 2 + b.2 ^ 2) - (a.1 ^ 2 + a.2 ^ 2) -
        ((b - a).1 ^ 2 + (b - a).2 ^ 2) := by
    simp only [coordinateRadial, Prod.fst_sub, Prod.snd_sub]
    ring
  rw [ha] at hid
  linarith only [hd, hb, hid]

/-- An outward radial endpoint has positive radial pairing. -/
theorem coordinateRadial_smul_pos {a : ℝ × ℝ} {r : ℝ}
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1) (hr : 1 < r) :
    0 < coordinateRadial a (r • a) := by
  have hid : coordinateRadial a (r • a) =
      (r - 1) * (a.1 ^ 2 + a.2 ^ 2) := by
    change a.1 * (r * a.1 - a.1) + a.2 * (r * a.2 - a.2) = _
    ring
  rw [hid, ha, mul_one]
  exact sub_pos.mpr hr

/-- The first endpoint of a simple nondegenerate chain is absent from its
remaining trace. -/
theorem IsSimplePolygonalChain.head_not_mem_tail {a b : ℝ × ℝ}
    {rest : List (ℝ × ℝ)} (hs : IsSimplePolygonalChain (a :: b :: rest)) :
    a ∉ polygonalChain (b :: rest) := by
  intro ha
  have hab : a = b := mem_singleton_iff.mp
    (hs.2.2 ▸ (show a ∈ segment ℝ a b ∩ polygonalChain (b :: rest) from
      ⟨left_mem_segment ℝ a b, ha⟩))
  exact hs.1 hab

/-- A neighborhood of the first endpoint of a simple finite chain sees
exactly its first closed segment. -/
theorem IsSimplePolygonalChain.exists_head_ball {a b : ℝ × ℝ}
    {rest : List (ℝ × ℝ)} (hs : IsSimplePolygonalChain (a :: b :: rest)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball a ε,
      (z ∈ polygonalChain (a :: b :: rest) ↔ z ∈ segment ℝ a b) := by
  have hclosed := (isCompact_polygonal_chain (b :: rest)).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a hs.head_not_mem_tail
  refine ⟨ε, hε, fun z hz => ?_⟩
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact (hball hz h).elim
  · exact Or.inl

/-- The first actual edge of a simple coordinate disk chain points strictly
inward at its original unit-circle endpoint. -/
theorem IsSimplePolygonalChain.head_radial_neg {a b : ℝ × ℝ}
    {rest : List (ℝ × ℝ)} (hs : IsSimplePolygonalChain (a :: b :: rest))
    (ha : a.1 ^ 2 + a.2 ^ 2 = 1)
    (hD : polygonalChain (a :: b :: rest) ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) :
    coordinateRadial a b < 0 :=
  coordinateRadial_neg_of_mem_disk ha (hD (Or.inl (right_mem_segment ℝ a b))) hs.1

end LatticeProb.Topology
