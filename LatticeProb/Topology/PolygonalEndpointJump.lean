/-
# A finite crossing jump at an isolated polygonal endpoint

Away from endpoint heights and the segment itself, one edge's half-open ray
marker is locally constant. At a vertex with one edge pointing backward and
one pointing forward, a small transverse displacement changes only the forward
incident marker. Summing the markers gives a parity difference of one. These
are local finite geometry statements; no Jordan or separation premise is used.
-/
import LatticeProb.Topology.PolygonalEndpointDirection



open Set Metric Filter
open scoped Topology
namespace LatticeProb.Topology.PolygonalParity

/-- The forward coordinate of the level-line meeting point is continuous
as a function of the ray base point, including for the totalized division. -/
theorem continuous_fwd_meet (u a b : Plane) :
    Continuous (fun q => fwd u (meet u a b (hgt u q))) := by
  simp only [fwd_meet]
  exact continuous_const.add
    (((continuous_hgt_right u).sub continuous_const).div_const _ |>.mul continuous_const)

/-- An edge marker is locally constant at a point off the edge whose height
differs from both endpoint heights. All three crossing inequalities are handled
using continuity, with the forward equality excluded by exact segment incidence. -/
theorem mark_eventually_eq {u a : Plane} {P : Piece} (hu : Plane.IsDirection u)
    (hP : hgt u P.1 ≠ hgt u P.2) (ha : a ∉ P.seg)
    (ha1 : hgt u a ≠ hgt u P.1) (ha2 : hgt u a ≠ hgt u P.2) :
    ∀ᶠ q in 𝓝 a, mark u P q = mark u P a := by
  have hmin : hgt u a ≠ min (hgt u P.1) (hgt u P.2) := by
    rcases le_total (hgt u P.1) (hgt u P.2) with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hmax : hgt u a ≠ max (hgt u P.1) (hgt u P.2) := by
    rcases le_total (hgt u P.1) (hgt u P.2) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  by_cases hlo : hgt u a < min (hgt u P.1) (hgt u P.2)
  · have he := (continuous_hgt_right u).continuousAt.eventually_lt
      continuousAt_const hlo
    filter_upwards [he] with q hq
    have hqa : ¬ Crosses u P q := fun h => (not_le_of_gt hq) h.1
    have haa : ¬ Crosses u P a := fun h => (not_le_of_gt hlo) h.1
    rw [mark, mark, if_neg hqa, if_neg haa]
  by_cases hhi : max (hgt u P.1) (hgt u P.2) < hgt u a
  · have he := continuousAt_const.eventually_lt
      (continuous_hgt_right u).continuousAt hhi
    filter_upwards [he] with q hq
    have hqa : ¬ Crosses u P q := fun h => (not_lt_of_ge hq.le) h.2.1
    have haa : ¬ Crosses u P a := fun h => (not_lt_of_ge hhi.le) h.2.1
    rw [mark, mark, if_neg hqa, if_neg haa]
  have hlo' : min (hgt u P.1) (hgt u P.2) < hgt u a :=
    lt_of_le_of_ne (not_lt.mp hlo) hmin.symm
  have hhi' : hgt u a < max (hgt u P.1) (hgt u P.2) :=
    lt_of_le_of_ne (not_lt.mp hhi) hmax
  have hfne : fwd u a ≠ fwd u (meet u P.1 P.2 (hgt u a)) := by
    intro heq
    have heqa : a = meet u P.1 P.2 (hgt u a) :=
      eq_of_coords hu heq (hgt_meet hP _).symm
    exact ha (heqa ▸ meet_mem_seg hP hlo'.le hhi'.le)
  have helo := continuousAt_const.eventually_lt
    (continuous_hgt_right u).continuousAt hlo'
  have hehi := (continuous_hgt_right u).continuousAt.eventually_lt
    continuousAt_const hhi'
  rcases lt_or_gt_of_ne hfne with hf | hf
  · have hef := (continuous_fwd_right u).continuousAt.eventually_lt
      (continuous_fwd_meet u P.1 P.2).continuousAt hf
    filter_upwards [helo, hehi, hef] with q hqlo hqhi hqf
    rw [mark, mark, if_pos ⟨hqlo.le, hqhi, hqf⟩, if_pos ⟨hlo'.le, hhi', hf⟩]
  · have hef := (continuous_fwd_meet u P.1 P.2).continuousAt.eventually_lt
      (continuous_fwd_right u).continuousAt hf
    filter_upwards [hef] with q hqf
    have hqa : ¬ Crosses u P q := fun h => (not_lt_of_ge hqf.le) h.2.2
    have haa : ¬ Crosses u P a := fun h => (not_lt_of_ge hf.le) h.2.2
    rw [mark, mark, if_neg hqa, if_neg haa]

/-- Finite edge parity is locally constant off the trace and every endpoint
height, even when the edge list is open. -/
theorem parity_eventually_eq_of_endpoint_heights {u a : Plane} {L : List Piece}
    (hu : Plane.IsDirection u) (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (ha : a ∉ cover L)
    (hheight : ∀ P ∈ L, hgt u a ≠ hgt u P.1 ∧ hgt u a ≠ hgt u P.2) :
    ∀ᶠ q in 𝓝 a, parity u L q = parity u L a := by
  induction L with
  | nil => exact Eventually.of_forall (fun _ => rfl)
  | cons P L ih =>
    have hm := mark_eventually_eq hu (hL P List.mem_cons_self)
      (fun h => ha (mem_cover List.mem_cons_self h))
      (hheight P List.mem_cons_self).1 (hheight P List.mem_cons_self).2
    have ht := ih (fun Q hQ => hL Q (List.mem_cons_of_mem P hQ))
      (fun h => ha (by rw [cover_cons]; exact Or.inr h))
      (fun Q hQ => hheight Q (List.mem_cons_of_mem P hQ))
    filter_upwards [hm, ht] with q hqm hqt
    rw [parity_cons, parity_cons, hqm, hqt]

/-- A backward incident edge contributes no crossing to any ray base point
with the same forward coordinate as its endpoint. -/
theorem mark_incident_backward_eq_zero {u a b q : Plane}
    (hab : hgt u a ≠ hgt u b) (hb : fwd u b < fwd u a)
    (hq : fwd u q = fwd u a) : mark u (a, b) q = 0 := by
  apply if_neg
  rintro ⟨hlo, hhi, hf⟩
  have hm := meet_mem_seg hab hlo hhi.le
  change meet u a b (hgt u q) ∈ segment ℝ a b at hm
  rw [segment_eq_image' ℝ a b] at hm
  obtain ⟨r, hr, heq⟩ := hm
  have hle : fwd u (meet u a b (hgt u q)) ≤ fwd u a := by
    rw [← heq, fwd_lin]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hr.1 (sub_nonpos.mpr hb.le))
  rw [hq] at hf
  exact (not_lt_of_ge hle) hf

/-- A forward incident edge contributes exactly one of the two nearby
transverse markers. The lower endpoint remains included and the upper excluded. -/
theorem mark_incident_forward_sum {u a c : Plane} (hu : Plane.IsDirection u)
    (hac : hgt u a ≠ hgt u c) (hc : fwd u a < fwd u c)
    {t : ℝ} (ht : 0 < t) (htc : t < |hgt u c - hgt u a|) :
    mark u (a, c) (a + (-t) • Plane.perp u) +
      mark u (a, c) (a + t • Plane.perp u) = 1 := by
  have hdiff : hgt u c - hgt u a ≠ 0 := sub_ne_zero.mpr hac.symm
  rcases lt_or_gt_of_ne hdiff with hd | hd
  · have hca : hgt u c < hgt u a := sub_neg.mp hd
    rw [abs_of_neg hd] at htc
    have hminus : Crosses u (a, c) (a + (-t) • Plane.perp u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [min_eq_right hca.le, hgt_across hu]
        linarith only [htc]
      · rw [max_eq_left hca.le, hgt_across hu]
        exact add_lt_of_neg_right _ (neg_neg_of_pos ht)
      · rw [fwd_across, hgt_across hu, fwd_meet, add_sub_cancel_left]
        exact lt_add_of_pos_right _ (mul_pos (div_pos_of_neg_of_neg (neg_neg_of_pos ht) hd)
          (sub_pos.mpr hc))
    have hplus : ¬ Crosses u (a, c) (a + t • Plane.perp u) := by
      rintro ⟨_, h, _⟩
      rw [max_eq_left hca.le, hgt_across hu] at h
      exact (not_lt_of_ge (le_add_of_nonneg_right ht.le)) h
    rw [mark, mark, if_pos hminus, if_neg hplus, add_zero]
  · have hac' : hgt u a < hgt u c := sub_pos.mp hd
    rw [abs_of_pos hd] at htc
    have hplus : Crosses u (a, c) (a + t • Plane.perp u) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [min_eq_left hac'.le, hgt_across hu]
        exact le_add_of_nonneg_right ht.le
      · rw [max_eq_right hac'.le, hgt_across hu]
        linarith only [htc]
      · rw [fwd_across, hgt_across hu, fwd_meet, add_sub_cancel_left]
        exact lt_add_of_pos_right _ (mul_pos (div_pos ht hd) (sub_pos.mpr hc))
    have hminus : ¬ Crosses u (a, c) (a + (-t) • Plane.perp u) := by
      rintro ⟨h, _, _⟩
      rw [min_eq_left hac'.le, hgt_across hu] at h
      exact (not_le_of_gt (add_lt_of_neg_right _ (neg_neg_of_pos ht))) h
    rw [mark, mark, if_neg hminus, if_pos hplus, zero_add]

/-- **Finite endpoint parity jump.** At an isolated endpoint with one
backward and one forward incident edge, sufficiently small opposite transverse
displacements have opposite parity. Genericity away from other endpoint heights
is explicit finite geometry; the other markers are proved locally fixed. -/
theorem exists_transverse_endpoint_jump {u a b c : Plane} {R : List Piece}
    (hu : Plane.IsDirection u) (hab : hgt u a ≠ hgt u b)
    (hac : hgt u a ≠ hgt u c) (hb : fwd u b < fwd u a)
    (hc : fwd u a < fwd u c) (hR : ∀ P ∈ R, hgt u P.1 ≠ hgt u P.2)
    (haR : a ∉ cover R)
    (hheight : ∀ P ∈ R, hgt u a ≠ hgt u P.1 ∧ hgt u a ≠ hgt u P.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      parity u ((a, b) :: (a, c) :: R) (a + (-t) • Plane.perp u) =
        parity u ((a, b) :: (a, c) :: R) (a + t • Plane.perp u) + 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (parity_eventually_eq_of_endpoint_heights hu hR haR hheight)
  let δ := min ε |hgt u c - hgt u a|
  have hδ : 0 < δ := lt_min hε (abs_pos.mpr (sub_ne_zero.mpr hac.symm))
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  have htε : t < ε := htδ.trans_le (min_le_left _ _)
  have htc : t < |hgt u c - hgt u a| := htδ.trans_le (min_le_right _ _)
  have hd : ∀ s : ℝ, |s| < ε → a + s • Plane.perp u ∈ ball a ε := by
    intro s hs
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      Plane.norm_perp, hu, mul_one]
    exact hs
  have hm := hball (a + (-t) • Plane.perp u) (hd (-t) (by rwa [abs_neg, abs_of_pos ht]))
  have hp := hball (a + t • Plane.perp u) (hd t (by rwa [abs_of_pos ht]))
  have hbm := mark_incident_backward_eq_zero hab hb (fwd_across (u := u) a (-t))
  have hbp := mark_incident_backward_eq_zero hab hb (fwd_across (u := u) a t)
  have hout := mark_incident_forward_sum hu hac hc ht htc
  rw [parity_cons, parity_cons, parity_cons, parity_cons, hbm, hbp, zero_add, zero_add,
    hm, hp]
  have harith : ∀ x y z : ZMod 2, x + y = 1 → x + z = y + z + 1 := by decide
  exact harith _ _ _ hout

end LatticeProb.Topology.PolygonalParity
