/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.CurveSides
import LatticeProb.Lattice.Planar.ExplChain

open Finset List

namespace LatticeProb.Lattice.Planar

/-- The quadruple of a face: its position in the twice-doubled lattice. -/
def quad (z : Site) : Site := z + z + (z + z)

theorem mem_of_double_mem_dbl {c : List Site} (hc : IsClosedWalk c) {p : Site}
    (h : p + p ∈ dbl c) : p ∈ c := by
  rcases mem_dbl.1 h with ⟨a, ha, hpa⟩ | ⟨s, hs, hab⟩
  · have : p = a := by
      obtain ⟨p1, p2⟩ := p; obtain ⟨a1, a2⟩ := a
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at hpa
      ext <;> simp <;> omega
    rw [this]; exact ha
  · exfalso
    have hu := steps_unit hc hs
    obtain ⟨p1, p2⟩ := p; obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
    rw [isUnit_iff'] at hu
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hab
    omega

theorem mid_notMem_dbl_of_notMem {c : List Site} (hc : IsClosedWalk c) {z v : Site}
    (hv : IsUnit v) (h : z + v ∉ c) : z + z + v ∉ dbl c := by
  intro hm
  rcases (mid_mem_dbl_iff hc hv).1 hm with hs | hs
  · exact h (mem_steps hs).2
  · exact h (mem_steps hs).1

theorem mid_notMem_dbl_of_notMem' {c : List Site} (hc : IsClosedWalk c) {z v : Site}
    (hv : IsUnit v) (h : z ∉ c) : z + z + v ∉ dbl c := by
  intro hm
  rcases (mid_mem_dbl_iff hc hv).1 hm with hs | hs
  · exact h (mem_steps hs).1
  · exact h (mem_steps hs).2

/-- Along a doubled-lattice bond `z₁ → z₁ + v` with `z₁ + v ∉ c`, the twice-doubled points
`2(z₁ + v)` and the midpoint `2z₁ + v` are connected off `dbl c`. -/
theorem reach_mid_of_notMem {c : List Site} (hc : IsClosedWalk c) {z₁ v : Site} (hv : IsUnit v)
    (h : z₁ + v ∉ c) :
    Relation.ReflTransGen (OffAdj (dbl c)) (z₁ + v + (z₁ + v)) (z₁ + z₁ + v) := by
  refine Relation.ReflTransGen.single ⟨?_, mid_notMem_dbl_of_notMem hc hv h, ?_⟩
  · intro hm; exact h (mem_of_double_mem_dbl hc hm)
  · have : z₁ + z₁ + v - (z₁ + v + (z₁ + v)) = -v := by abel
    rw [this]
    rcases hv with rfl | rfl | rfl | rfl <;> simp [IsUnit]

/-- From `2(z₁ + v)` to the midpoint of `z₁ → z₁ + v` and on to `2z₁` when both endpoints are
off `c`. -/
theorem reach_double_of_notMem {c : List Site} (hc : IsClosedWalk c) {z₁ v : Site} (hv : IsUnit v)
    (h1 : z₁ ∉ c) (h2 : z₁ + v ∉ c) :
    Relation.ReflTransGen (OffAdj (dbl c)) (z₁ + v + (z₁ + v)) (z₁ + z₁) := by
  refine (reach_mid_of_notMem hc hv h2).trans (Relation.ReflTransGen.single
    ⟨mid_notMem_dbl_of_notMem hc hv h2, ?_, ?_⟩)
  · intro hm; exact h1 (mem_of_double_mem_dbl hc hm)
  · have : z₁ + z₁ - (z₁ + z₁ + v) = -v := by abel
    rw [this]
    rcases hv with rfl | rfl | rfl | rfl <;> simp [IsUnit]

/-- A step between adjacent faces off `J₁` (doubles and the bond midpoint off `J₁`) gives a
path between their quadruples off `dbl J₁`. -/
theorem faceStep_reach {J₁ : List Site} (hc : IsClosedWalk J₁) {q q' : Site} (hu : IsUnit (q' - q))
    (h1 : q + q ∉ J₁) (h2 : q + q' ∉ J₁) (h3 : q' + q' ∉ J₁) :
    Relation.ReflTransGen (OffAdj (dbl J₁)) (quad q) (quad q') := by
  have e1 : q + q' = q + q + (q' - q) := by abel
  have e2 : q' + q' = q + q' + (q' - q) := by abel
  have r1 : Relation.ReflTransGen (OffAdj (dbl J₁)) (q + q' + (q + q')) (q + q + (q + q)) := by
    rw [e1]
    have := reach_double_of_notMem hc hu h1 (by rw [← e1]; exact h2)
    convert this using 2
  have r2 : Relation.ReflTransGen (OffAdj (dbl J₁)) (q' + q' + (q' + q')) (q + q' + (q + q')) := by
    rw [e2]
    have := reach_double_of_notMem hc hu h2 (by rw [← e2]; exact h3)
    convert this using 2
  unfold quad
  exact reflTransGen_offAdj_symm (r2.trans r1)

/-- A path through faces off `J₁` gives a path between quadruples off `dbl J₁`. -/
theorem avoidReach_quad {J₁ : List Site} (hc : IsClosedWalk J₁) {V : Finset Site}
    (hV : ∀ q, q ∉ V → q + q ∉ J₁)
    (hV2 : ∀ q q', q ∉ V → q' ∉ V → IsUnit (q' - q) → q + q' ∉ J₁) {y z : Site}
    (h : AvoidReach V y z) : Relation.ReflTransGen (OffAdj (dbl J₁)) (quad y) (quad z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.trans (faceStep_reach hc (isUnit_of_adj hbc.2.2) (hV _ hbc.1)
      (hV2 _ _ hbc.1 hbc.2.1 (isUnit_of_adj hbc.2.2)) (hV _ hbc.2.1))

/-- A face in the unbounded component reaches points arbitrarily far away. -/
theorem exists_far_of_not_inFiniteComponent {V : Finset Site} {y : Site} (hy : y ∉ V)
    (h : ¬ InFiniteComponent V y) : ∀ M : ℤ, ∃ z, AvoidReach V y z ∧ (M < |z.1| ∨ M < |z.2|) := by
  intro M
  rw [inFiniteComponent_iff, not_and] at h
  have hinf := h hy
  by_contra hcon
  push Not at hcon
  apply hinf
  refine (Set.finite_Icc ((-M, -M) : Site) (M, M)).subset ?_
  intro z hz
  have := hcon z hz
  simp only [Set.mem_Icc, Prod.le_def]
  rw [abs_le, abs_le] at this
  omega

/-- The separation lemma. -/
theorem separation {J₁ : List Site} (hJ : IsSimpleClosed J₁) {V : Finset Site}
    (hV : ∀ q, q ∉ V → q + q ∉ J₁)
    (hV2 : ∀ q q', q ∉ V → q' ∉ V → IsUnit (q' - q) → q + q' ∉ J₁)
    {t t' : Site × Site} (ht : t ∈ steps J₁) (ht' : t' ∈ steps J₁) {NE y : Site}
    (hNE : Relation.ReflTransGen (OffAdj (dbl J₁)) (quad NE) (rightPt t.1 t.2))
    (hy : Relation.ReflTransGen (OffAdj (dbl J₁)) (quad y) (leftPt t'.1 t'.2))
    (hNEV : NE ∉ V) (hyV : y ∉ V)
    (hNEout : ¬ InFiniteComponent V NE) (hyout : ¬ InFiniteComponent V y) : False := by
  have hc2 := isClosedWalk_dbl hJ.closed
  have hzero : ∀ z, z ∉ V → ¬ InFiniteComponent V z → wind (dbl J₁) (quad z) = 0 := by
    intro z hzV hzout
    refine wind_eq_zero_of_unbounded hc2 (fun M => ?_)
    obtain ⟨z', hz', hfar⟩ := exists_far_of_not_inFiniteComponent hzV hzout M
    refine ⟨quad z', avoidReach_quad hJ.closed hV hV2 hz', ?_⟩
    simp only [quad, Prod.fst_add, Prod.snd_add]
    rcases hfar with hfar | hfar
    · left; rw [lt_abs] at hfar ⊢; omega
    · right; rw [lt_abs] at hfar ⊢; omega
  have h1 := wind_eq_of_reflTransGen hc2 hNE
  have h2 := wind_eq_of_reflTransGen hc2 hy
  have h3 := wind_leftPt_sub_rightPt hJ ht' ht
  rw [hzero NE hNEV hNEout] at h1
  rw [hzero y hyV hyout] at h2
  rw [← h1, ← h2] at h3
  simp at h3

end LatticeProb.Lattice.Planar
