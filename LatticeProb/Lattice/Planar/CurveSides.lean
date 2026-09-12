/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Ring

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

/-- A simple closed walk of unit steps with at least three distinct vertices. -/
structure IsSimpleClosed (c : List Site) : Prop where
  closed : IsClosedWalk c
  nodup : c.tail.Nodup
  three : 3 ≤ c.tail.length

theorem steps_map_snd : ∀ (c : List Site), (steps c).map Prod.snd = c.tail
  | [] => rfl
  | [_] => rfl
  | _ :: b :: l => by
    rw [steps_cons_cons, List.map_cons, steps_map_snd (b :: l)]
    rfl

theorem steps_map_fst : ∀ (c : List Site), (steps c).map Prod.fst = c.dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [steps_cons_cons, List.map_cons, steps_map_fst (b :: l),
      List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]

theorem steps_snd_nodup {c : List Site} (hc : c.tail.Nodup) : ((steps c).map Prod.snd).Nodup := by
  rw [steps_map_snd]; exact hc

theorem dropLast_nodup_of_closed {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup) :
    c.dropLast.Nodup := by
  rcases c with _ | ⟨a, l⟩
  · simp
  rcases l with _ | ⟨b, l⟩
  · simp
  rw [List.tail_cons] at hnd
  rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
  have hcl : (b :: l).getLast (List.cons_ne_nil _ _) = a := by
    have := hc.closed
    rw [List.head?_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at this
    simpa using this.symm
  refine List.nodup_cons.2 ⟨fun h => ?_, hnd.sublist (List.dropLast_sublist _)⟩
  have hsplit := List.dropLast_append_getLast (List.cons_ne_nil b l)
  rw [hcl] at hsplit
  rw [← hsplit] at hnd
  exact (List.nodup_append.1 hnd).2.2 a h a (List.mem_singleton_self _) rfl

theorem steps_fst_nodup {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup) :
    ((steps c).map Prod.fst).Nodup := by
  rw [steps_map_fst]; exact dropLast_nodup_of_closed hc hnd

theorem step_tail_unique {c : List Site} (hnd : c.tail.Nodup) {z p p' : Site}
    (h1 : (p, z) ∈ steps c) (h2 : (p', z) ∈ steps c) : p = p' := by
  have := List.inj_on_of_nodup_map (steps_snd_nodup hnd) h1 h2 rfl
  rw [Prod.mk.injEq] at this
  exact this.1

theorem step_head_unique {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup) {z q q' : Site}
    (h1 : (z, q) ∈ steps c) (h2 : (z, q') ∈ steps c) : q = q' := by
  have := List.inj_on_of_nodup_map (steps_fst_nodup hc hnd) h1 h2 rfl
  rw [Prod.mk.injEq] at this
  exact this.2

theorem mid_mem_dbl_iff {c : List Site} (hc : IsClosedWalk c) {z v : Site} (hv : IsUnit v) :
    z + z + v ∈ dbl c ↔ (z, z + v) ∈ steps c ∨ (z + v, z) ∈ steps c := by
  constructor
  · intro h
    rcases mem_dbl.1 h with ⟨a, -, ha⟩ | ⟨s, hs, hab⟩
    · exfalso
      obtain ⟨z1, z2⟩ := z; obtain ⟨a1, a2⟩ := a
      rcases hv with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at ha <;> omega
    · have hu := steps_unit hc hs
      have hzv : IsUnit (z + v - z) := by rw [add_sub_cancel_left]; exact hv
      have hm : z + (z + v) = s.1 + s.2 := by rw [← hab]; abel
      rcases bond_eq_of_mid_eq hzv hu hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have : (z, z + v) = s := Prod.ext h1 h2
        rw [this]; exact hs
      · right
        have : (z + v, z) = s := Prod.ext h2 h1
        rw [this]; exact hs
  · rintro (h | h)
    · exact mem_dbl.2 (Or.inr ⟨_, h, by simp; abel⟩)
    · exact mem_dbl.2 (Or.inr ⟨_, h, by simp; abel⟩)

/-- The even ring indices are the unit directions. -/
theorem ringOff_isUnit_of_even (l : Fin 8) (hl : Even l.val) : IsUnit (ringOff l) := by
  fin_cases l <;> simp [Nat.even_iff] at hl <;> decide

theorem dirIdx_ringOff_of_even (l : Fin 8) (hl : Even l.val) : dirIdx (ringOff l) = l := by
  fin_cases l <;> simp [Nat.even_iff] at hl <;> rfl

/-- The points of an arc between the two directions of `c` at `z` are off `dbl c`. -/
theorem arc_offDbl {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup) {p z q : Site}
    (hin : (p, z) ∈ steps c) (hout : (z, q) ∈ steps c) {i j : Fin 8}
    (hij : (i = dirIdx (q - z) ∧ j = dirIdx (p - z)) ∨ (i = dirIdx (p - z) ∧ j = dirIdx (q - z))) :
    ∀ l, Between i j l → ringPt (z + z) l ∉ dbl c := by
  intro l hl hmem
  rcases Nat.even_or_odd l.val with he | ho
  · -- an even index: the midpoint of the bond in direction `ringOff l`
    have hv := ringOff_isUnit_of_even l he
    have hmid : z + z + ringOff l ∈ dbl c := hmem
    rcases (mid_mem_dbl_iff hc hv).1 hmid with hs | hs
    · have := step_head_unique hc hnd hout hs
      have hl' : l = dirIdx (q - z) := by
        rw [← dirIdx_ringOff_of_even l he, this, add_sub_cancel_left]
      rcases hij with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · rw [hl'] at hl; simp [Between] at hl
      · rw [hl'] at hl; simp [Between] at hl
    · have := step_tail_unique hnd hin hs
      have hl' : l = dirIdx (p - z) := by
        rw [← dirIdx_ringOff_of_even l he, this, add_sub_cancel_left]
      rcases hij with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · rw [hl'] at hl; simp [Between] at hl
      · rw [hl'] at hl; simp [Between] at hl
  · -- an odd index: an odd-odd point
    have hz : Even (z + z).1 ∧ Even (z + z).2 := ⟨⟨z.1, rfl⟩, ⟨z.2, rfl⟩⟩
    have := ringPt_odd (z + z) hz.1 hz.2 l ho
    exact oddodd_notMem_dbl hc this.1 this.2 hmem

theorem rev_notMem_steps' {c : List Site} (h : IsSimpleClosed c) {p z : Site}
    (hs : (p, z) ∈ steps c) : (z, p) ∉ steps c :=
  rev_notMem_steps h.closed h.nodup h.three hs

/-- The left points of two consecutive steps are connected off `dbl c`. -/
theorem leftPt_reach_consecutive {c : List Site} (h : IsSimpleClosed c) {p z q : Site}
    (hin : (p, z) ∈ steps c) (hout : (z, q) ∈ steps c) :
    Relation.ReflTransGen (OffAdj (dbl c)) (leftPt p z) (leftPt z q) := by
  have hu : IsUnit (z - p) := steps_unit h.closed hin
  have hw : IsUnit (q - z) := steps_unit h.closed hout
  have hne : q - z ≠ -(z - p) := by
    intro he
    have : q = p := by
      have := congrArg (fun d => d + z) he
      simp only [sub_add_cancel, neg_sub, sub_add_cancel] at this
      exact this
    subst this
    exact rev_notMem_steps' h hin hout
  have hidx : dirIdx (q - z) ≠ dirIdx (-(z - p)) :=
    fun h' => hne (dirIdx_injective hw (by rcases hu with h|h|h|h <;> rw [h] <;> simp [IsUnit]) h')
  have hp : p = z - (z - p) := by abel
  have hq : q = z + (q - z) := by abel
  obtain ⟨hb1, hb2⟩ := between_corners (dirIdx (q - z)) (dirIdx (-(z - p))) (dirIdx_even hw)
    (dirIdx_even (by rcases hu with h|h|h|h <;> rw [h] <;> simp [IsUnit])) hidx
  have hoff := arc_offDbl h.closed h.nodup hin hout (i := dirIdx (q - z)) (j := dirIdx (-(z - p)))
    (Or.inl ⟨rfl, by rw [neg_sub]⟩)
  have e1 : leftPt p z = ringPt (z + z) (dirIdx (-(z - p)) - 1) := by
    conv_lhs => rw [hp]
    exact leftPt_in_eq z (z - p) hu
  have e2 : leftPt z q = ringPt (z + z) (dirIdx (q - z) + 1) := by
    conv_lhs => rw [hq]
    exact leftPt_out_eq z (q - z) hw
  rw [e1, e2]
  exact ringPt_reach_of_between (z + z) _ _ hoff hb2 hb1

/-- The right points of two consecutive steps are connected off `dbl c`. -/
theorem rightPt_reach_consecutive {c : List Site} (h : IsSimpleClosed c) {p z q : Site}
    (hin : (p, z) ∈ steps c) (hout : (z, q) ∈ steps c) :
    Relation.ReflTransGen (OffAdj (dbl c)) (rightPt p z) (rightPt z q) := by
  have hu : IsUnit (z - p) := steps_unit h.closed hin
  have hw : IsUnit (q - z) := steps_unit h.closed hout
  have hu' : IsUnit (-(z - p)) := by rcases hu with h|h|h|h <;> rw [h] <;> simp [IsUnit]
  have hne : q - z ≠ -(z - p) := by
    intro he
    have : q = p := by
      have := congrArg (fun d => d + z) he
      simp only [sub_add_cancel, neg_sub, sub_add_cancel] at this
      exact this
    subst this
    exact rev_notMem_steps' h hin hout
  have hidx : dirIdx (-(z - p)) ≠ dirIdx (q - z) :=
    fun h' => hne (dirIdx_injective hw hu' h'.symm)
  have hp : p = z - (z - p) := by abel
  have hq : q = z + (q - z) := by abel
  obtain ⟨hb1, hb2⟩ := between_corners (dirIdx (-(z - p))) (dirIdx (q - z)) (dirIdx_even hu')
    (dirIdx_even hw) hidx
  have hoff := arc_offDbl h.closed h.nodup hin hout (i := dirIdx (-(z - p))) (j := dirIdx (q - z))
    (Or.inr ⟨by rw [neg_sub], rfl⟩)
  have e1 : rightPt p z = ringPt (z + z) (dirIdx (-(z - p)) + 1) := by
    conv_lhs => rw [hp]
    exact rightPt_in_eq z (z - p) hu
  have e2 : rightPt z q = ringPt (z + z) (dirIdx (q - z) - 1) := by
    conv_lhs => rw [hq]
    exact rightPt_out_eq z (q - z) hw
  rw [e1, e2]
  exact ringPt_reach_of_between (z + z) _ _ hoff hb1 hb2

/-- Consecutive steps of a walk share a vertex. -/
theorem steps_consecutive {c : List Site} (i : ℕ) (hi : i + 1 < (steps c).length) :
    ((steps c)[i]).2 = ((steps c)[i + 1]).1 := by
  unfold steps at hi ⊢
  simp only [List.getElem_zip, List.getElem_tail]

/-- Any two left points of `c` are connected off `dbl c`. -/
theorem leftPt_reach {c : List Site} (h : IsSimpleClosed c) :
    ∀ (i j : ℕ) (hi : i < (steps c).length) (hj : j < (steps c).length),
      Relation.ReflTransGen (OffAdj (dbl c))
        (leftPt ((steps c)[i]).1 ((steps c)[i]).2) (leftPt ((steps c)[j]).1 ((steps c)[j]).2) := by
  have key : ∀ (i m : ℕ) (him : i ≤ m) (hm : m < (steps c).length),
      Relation.ReflTransGen (OffAdj (dbl c))
        (leftPt ((steps c)[i]).1 ((steps c)[i]).2)
        (leftPt ((steps c)[m]).1 ((steps c)[m]).2) := by
    intro i m
    induction m with
    | zero =>
      intro him _
      have : i = 0 := by omega
      subst this
      exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro him hm
      rcases Nat.eq_or_lt_of_le him with h' | h'
      · subst h'; exact Relation.ReflTransGen.refl
      · refine (ih (by omega) (by omega)).trans ?_
        have hs := steps_consecutive (c := c) m hm
        have h1 : (steps c)[m] ∈ steps c := List.getElem_mem _
        have h2 : (steps c)[m + 1] ∈ steps c := List.getElem_mem _
        have := leftPt_reach_consecutive h (p := ((steps c)[m]).1) (z := ((steps c)[m]).2)
          (q := ((steps c)[m + 1]).2) h1 (by rw [hs]; exact h2)
        rw [← hs]
        exact this
  intro i j hi hj
  rcases le_or_gt i j with hij | hij
  · exact key i j hij hj
  · exact reflTransGen_offAdj_symm (key j i hij.le hi)

theorem rightPt_reach {c : List Site} (h : IsSimpleClosed c) :
    ∀ (i j : ℕ) (hi : i < (steps c).length) (hj : j < (steps c).length),
      Relation.ReflTransGen (OffAdj (dbl c))
        (rightPt ((steps c)[i]).1 ((steps c)[i]).2) (rightPt ((steps c)[j]).1 ((steps c)[j]).2) := by
  have key : ∀ (i m : ℕ) (him : i ≤ m) (hm : m < (steps c).length),
      Relation.ReflTransGen (OffAdj (dbl c))
        (rightPt ((steps c)[i]).1 ((steps c)[i]).2)
        (rightPt ((steps c)[m]).1 ((steps c)[m]).2) := by
    intro i m
    induction m with
    | zero =>
      intro him _
      have : i = 0 := by omega
      subst this
      exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro him hm
      rcases Nat.eq_or_lt_of_le him with h' | h'
      · subst h'; exact Relation.ReflTransGen.refl
      · refine (ih (by omega) (by omega)).trans ?_
        have hs := steps_consecutive (c := c) m hm
        have h1 : (steps c)[m] ∈ steps c := List.getElem_mem _
        have h2 : (steps c)[m + 1] ∈ steps c := List.getElem_mem _
        have := rightPt_reach_consecutive h (p := ((steps c)[m]).1) (z := ((steps c)[m]).2)
          (q := ((steps c)[m + 1]).2) h1 (by rw [hs]; exact h2)
        rw [← hs]
        exact this
  intro i j hi hj
  rcases le_or_gt i j with hij | hij
  · exact key i j hij hj
  · exact reflTransGen_offAdj_symm (key j i hij.le hi)

/-- The winding number of `dbl c` at every left point exceeds that at every right point by one. -/
theorem wind_leftPt_sub_rightPt {c : List Site} (h : IsSimpleClosed c) {s t : Site × Site}
    (hs : s ∈ steps c) (ht : t ∈ steps c) :
    wind (dbl c) (leftPt s.1 s.2) - wind (dbl c) (rightPt t.1 t.2) = 1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
  have hc2 := isClosedWalk_dbl h.closed
  have hL := wind_eq_of_reflTransGen hc2 (leftPt_reach h i j hi hj)
  have hR := wind_eq_of_reflTransGen hc2 (rightPt_reach h j j hj hj)
  rw [hL]
  exact wind_dbl_left_sub_right h.closed h.nodup h.three (List.getElem_mem hj)

end LatticeProb.Lattice.Planar
