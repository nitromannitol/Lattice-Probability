/-
# Geometric local sides of a polygonal edge

At an isolated edge interior, a ball minus the edge has two convex halfballs,
defined by the sign of the determinant against the edge vector. Each halfball
avoids the other edges and has constant crossing parity. The proved ray flip
places their parities on opposite values. Consequently any preconnected set
joining points in the two halfballs intersects the original closed edge chain.
-/
import LatticeProb.Topology.PolygonalParitySeparation
import Mathlib.Analysis.Convex.PathConnected



open Metric Set
namespace LatticeProb.Topology.PolygonalParity

/-- The determinant against a fixed vector is a real linear function. -/
theorem isLinearMap_det (v : Plane) : IsLinearMap ℝ (Plane.det v) where
  map_add := Plane.det_add_right v
  map_smul := fun r x => Plane.det_smul_right r v x

/-- The determinant against an edge vector is constant along that edge. -/
theorem det_eq_of_mem_segment {a b x y : Plane} (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : Plane.det (b - a) x = Plane.det (b - a) y := by
  rw [segment_eq_image' ℝ a b] at hx hy
  obtain ⟨r, _, rfl⟩ := hx
  obtain ⟨s, _, rfl⟩ := hy
  rw [Plane.det_add_right, Plane.det_add_right, Plane.det_smul_right,
    Plane.det_smul_right, Plane.det_self, mul_zero, add_zero, mul_zero, add_zero]

/-- A positive determinant halfball is convex and hence preconnected. -/
theorem isPreconnected_positive_halfBall (v p : Plane) (ε : ℝ) :
    IsPreconnected (ball p ε ∩ {z | Plane.det v p < Plane.det v z}) :=
  ((convex_ball p ε).inter (convex_halfSpace_gt (isLinearMap_det v) _)).isPreconnected

/-- A negative determinant halfball is convex and hence preconnected. -/
theorem isPreconnected_negative_halfBall (v p : Plane) (ε : ℝ) :
    IsPreconnected (ball p ε ∩ {z | Plane.det v z < Plane.det v p}) :=
  ((convex_ball p ε).inter (convex_halfSpace_lt (isLinearMap_det v) _)).isPreconnected

/-- **Geometric local separation.** At an isolated interior point of one edge
in a finite nondegenerate closed chain, sufficiently close points on opposite
determinant sides have different crossing parities. Every preconnected set
containing both points intersects the chain. The ray direction is constructed,
and the test points need not avoid vertex heights. -/
theorem exists_halfBall_separation {L₁ L₂ : List Piece} {a b p : Plane}
    (hnd : ∀ P ∈ L₁ ++ (a, b) :: L₂, P.Nondeg)
    (hC : IsClosedChain (L₁ ++ (a, b) :: L₂))
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y : Plane,
      x ∈ ball p ε → y ∈ ball p ε →
      Plane.det (b - a) p < Plane.det (b - a) x →
      Plane.det (b - a) y < Plane.det (b - a) p →
      x ∉ cover (L₁ ++ (a, b) :: L₂) ∧ y ∉ cover (L₁ ++ (a, b) :: L₂) ∧
      ∀ S : Set Plane, IsPreconnected S → x ∈ S → y ∈ S →
        (S ∩ cover (L₁ ++ (a, b) :: L₂)).Nonempty := by
  obtain ⟨u, hu, hL⟩ := exists_direction_hgt_ne (L₁ ++ (a, b) :: L₂) hnd
  have hab : hgt u a ≠ hgt u b := hL (a, b) (by simp)
  have hother : p ∉ cover (L₁ ++ L₂) := by
    rw [cover_append]
    exact fun h => h.elim h1 h2
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding hother
  obtain ⟨δ, hδ, hflip⟩ := parity_flip hu hL hp h1 h2
  let t : ℝ := min ε δ / 2
  have ht : 0 < t := half_pos (lt_min hε hδ)
  have htε : t < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left ε δ)
  have htδ : t < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right ε δ)
  clear_value t
  have hpm : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have havoid : ∀ z ∈ ball p ε, Plane.det (b - a) z ≠ Plane.det (b - a) p →
      z ∉ cover (L₁ ++ (a, b) :: L₂) := by
    intro z hz hdet hcov
    rw [cover_append, cover_cons] at hcov
    rcases hcov with hz1 | hzedge | hz2
    · exact hball z hz (by rw [cover_append]; exact Or.inl hz1)
    · exact hdet (det_eq_of_mem_segment hzedge hpm)
    · exact hball z hz (by rw [cover_append]; exact Or.inr hz2)
  have hposmiss : ∀ z ∈ ball p ε ∩ {z | Plane.det (b - a) p < Plane.det (b - a) z},
      z ∉ cover (L₁ ++ (a, b) :: L₂) :=
    fun z hz => havoid z hz.1 (ne_of_gt hz.2)
  have hnegmiss : ∀ z ∈ ball p ε ∩ {z | Plane.det (b - a) z < Plane.det (b - a) p},
      z ∉ cover (L₁ ++ (a, b) :: L₂) :=
    fun z hz => havoid z hz.1 (ne_of_lt hz.2)
  have hposconst : ∀ {x y : Plane},
      x ∈ ball p ε ∩ {z | Plane.det (b - a) p < Plane.det (b - a) z} →
      y ∈ ball p ε ∩ {z | Plane.det (b - a) p < Plane.det (b - a) z} →
      parity u (L₁ ++ (a, b) :: L₂) x = parity u (L₁ ++ (a, b) :: L₂) y :=
    fun hx hy => parity_eq_of_isPreconnected hu hL hC
      (isPreconnected_positive_halfBall (b - a) p ε) hposmiss hx hy
  have hnegconst : ∀ {x y : Plane},
      x ∈ ball p ε ∩ {z | Plane.det (b - a) z < Plane.det (b - a) p} →
      y ∈ ball p ε ∩ {z | Plane.det (b - a) z < Plane.det (b - a) p} →
      parity u (L₁ ++ (a, b) :: L₂) x = parity u (L₁ ++ (a, b) :: L₂) y :=
    fun hx hy => parity_eq_of_isPreconnected hu hL hC
      (isPreconnected_negative_halfBall (b - a) p ε) hnegmiss hx hy
  have hplusball : p + t • u ∈ ball p ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hu, mul_one]
    exact htε
  have hminusball : p - t • u ∈ ball p ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hu, mul_one]
    exact htε
  have hdetplus : Plane.det (b - a) (p + t • u) =
      Plane.det (b - a) p + t * Plane.det (b - a) u := by
    rw [Plane.det_add_right, Plane.det_smul_right]
  have hdetminus : Plane.det (b - a) (p - t • u) =
      Plane.det (b - a) p - t * Plane.det (b - a) u := by
    rw [sub_eq_add_neg p (t • u), Plane.det_add_right]
    have hneg : -(t • u) = (-t) • u := (neg_smul t u).symm
    rw [hneg, Plane.det_smul_right]
    ring
  have hdu : Plane.det (b - a) u ≠ 0 := by
    intro hzero
    have hzero' : hgt u (b - a) = 0 := by
      rw [hgt, Plane.det_comm, hzero, neg_zero]
    rw [hgt_sub, sub_eq_zero] at hzero'
    exact hab hzero'.symm
  obtain ⟨_, _, hflipval⟩ := hflip t ht htδ
  have hflipne : parity u (L₁ ++ (a, b) :: L₂) (p - t • u) ≠
      parity u (L₁ ++ (a, b) :: L₂) (p + t • u) := by
    intro heq
    have hone : (1 : ZMod 2) = 0 :=
      add_left_cancel ((hflipval.symm.trans heq).trans (add_zero _).symm)
    exact one_ne_zero hone
  refine ⟨ε, hε, fun x y hx hy hxside hyside => ?_⟩
  have hxy : parity u (L₁ ++ (a, b) :: L₂) x ≠ parity u (L₁ ++ (a, b) :: L₂) y := by
    rcases lt_or_gt_of_ne hdu with hd | hd
    · have hmul : t * Plane.det (b - a) u < 0 := mul_neg_of_pos_of_neg ht hd
      have hxminus := hposconst ⟨hx, hxside⟩
        ⟨hminusball, by
          change Plane.det (b - a) p < Plane.det (b - a) (p - t • u)
          rw [hdetminus]
          exact lt_sub_iff_add_lt.mpr (add_lt_of_neg_right _ hmul)⟩
      have hyplus := hnegconst ⟨hy, hyside⟩
        ⟨hplusball, by
          change Plane.det (b - a) (p + t • u) < Plane.det (b - a) p
          rw [hdetplus]
          exact add_lt_of_neg_right _ hmul⟩
      rw [hxminus, hyplus]
      exact hflipne
    · have hmul : 0 < t * Plane.det (b - a) u := mul_pos ht hd
      have hxplus := hposconst ⟨hx, hxside⟩
        ⟨hplusball, by
          change Plane.det (b - a) p < Plane.det (b - a) (p + t • u)
          rw [hdetplus]
          exact lt_add_of_pos_right _ hmul⟩
      have hyminus := hnegconst ⟨hy, hyside⟩
        ⟨hminusball, by
          change Plane.det (b - a) (p - t • u) < Plane.det (b - a) p
          rw [hdetminus]
          exact sub_lt_self _ hmul⟩
      rw [hxplus, hyminus]
      exact hflipne.symm
  exact ⟨hposmiss x ⟨hx, hxside⟩, hnegmiss y ⟨hy, hyside⟩,
    fun S hS hxS hyS => inter_cover_nonempty_of_parity_ne hu hL hC hS hxS hyS hxy⟩

end LatticeProb.Topology.PolygonalParity
