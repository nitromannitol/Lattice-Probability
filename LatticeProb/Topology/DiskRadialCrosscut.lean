/-
# Original circle parity for a finite disk crosscut

Complete a simple inside chain by a finite outside chain retaining its first
radial segment. Choose a generic outward ray from finite edge and vertex data.
The endpoint jump and circle interval constancy then give opposite parity on
the two complementary original angular intervals.
-/
import LatticeProb.Topology.DiskRadialCompletion
import LatticeProb.Topology.DiskCircleEndpointJump



open Set Metric
namespace LatticeProb.Topology.PolygonalParity

/-- The radial displacement pairing is preserved by the exact coordinate
identification, with the Euclidean inner product on the target. -/
theorem inner_displacement_coordinateEquiv (a b : ℝ × ℝ) :
    inner ℝ (coordinateEquiv b - coordinateEquiv a) (coordinateEquiv a) =
      coordinateRadial a b := by
  rw [Plane.inner_eq]
  change (b.1 - a.1) * a.1 + (b.2 - a.2) * a.2 = _
  rw [coordinateRadial]
  ring

/-- Every original unit-circle point is a Euclidean unit direction. -/
theorem isDirection_coordinate_circle (θ : ℝ) :
    Plane.IsDirection (coordinateEquiv (Real.cos θ, Real.sin θ)) := by
  have hsq : ‖coordinateEquiv (Real.cos θ, Real.sin θ)‖ ^ 2 = 1 := by
    rw [Plane.norm_sq_eq]
    exact Real.cos_sq_add_sin_sq θ
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hsq.trans (one_pow 2).symm)

/-- **Generic outward endpoint ray.** Finite edge directions and nonincident endpoint heights can be avoided
while retaining an outward ray at an endpoint with inward and outward germs. -/
theorem exists_generic_endpoint_direction {a b c : Plane} {R : List Piece}
    (ha : Plane.IsDirection a) (hb : inner ℝ (b - a) a < 0)
    (hc : 0 < inner ℝ (c - a) a) (hnd : ∀ P ∈ R, P.Nondeg)
    (haR : a ∉ cover R) :
    ∃ u : Plane, Plane.IsDirection u ∧ 0 < fwd u a ∧
      hgt u a ≠ hgt u b ∧ hgt u a ≠ hgt u c ∧
      (∀ P ∈ R, hgt u P.1 ≠ hgt u P.2) ∧
      (∀ P ∈ R, hgt u a ≠ hgt u P.1 ∧ hgt u a ≠ hgt u P.2) := by
  let L : List Piece := (a, b) :: (a, c) :: R
  let S := (L.finite_toSet.image (fun P : Piece => P.2 - P.1)).union
    ((R.finite_toSet.image (fun P : Piece => P.1 - a)).union
      (R.finite_toSet.image (fun P : Piece => P.2 - a)))
  have hfb : fwd a b < fwd a a := by
    change fwd a (b - a) < 0 at hb
    rw [fwd_sub] at hb
    exact sub_neg.mp hb
  have hfc : fwd a a < fwd a c := by
    change 0 < fwd a (c - a) at hc
    rw [fwd_sub] at hc
    exact sub_pos.mp hc
  obtain ⟨u, hu, _, _, hout, hdet⟩ := exists_generic_direction_radial ha hfb hfc S
  have hLnd : ∀ P ∈ L, P.Nondeg := by
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · intro heq
      change a = b at heq
      rw [heq, sub_self, inner_zero_left] at hb
      exact lt_irrefl 0 hb
    · rcases List.mem_cons.mp hP with rfl | hP
      · intro heq
        change a = c at heq
        rw [heq, sub_self, inner_zero_left] at hc
        exact lt_irrefl 0 hc
      · exact hnd P hP
  have hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2 := by
    intro P hP heq
    have hz : hgt u (P.2 - P.1) = 0 := by rw [hgt_sub, heq, sub_self]
    exact hdet _ (Or.inl ⟨P, hP, rfl⟩)
      (sub_ne_zero.mpr (hLnd P hP).symm) hz
  refine ⟨u, hu, hout, hL (a, b) List.mem_cons_self,
    hL (a, c) (List.mem_cons_of_mem _ List.mem_cons_self),
    fun P hP => hL P (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hP)), ?_⟩
  intro P hP
  have h1 : P.1 ≠ a := by
    intro heq
    apply haR
    apply mem_cover hP
    rw [← heq]
    exact left_mem_segment ℝ _ _
  have h2 : P.2 ≠ a := by
    intro heq
    apply haR
    apply mem_cover hP
    rw [← heq]
    exact right_mem_segment ℝ _ _
  constructor
  · intro heq
    have hz : hgt u (P.1 - a) = 0 := by rw [hgt_sub, heq, sub_self]
    exact hdet _ (Or.inr (Or.inl ⟨P, hP, rfl⟩)) (sub_ne_zero.mpr h1) hz
  · intro heq
    have hz : hgt u (P.2 - a) = 0 := by rw [hgt_sub, heq, sub_self]
    exact hdet _ (Or.inr (Or.inr ⟨P, hP, rfl⟩)) (sub_ne_zero.mpr h2) hz

end LatticeProb.Topology.PolygonalParity
