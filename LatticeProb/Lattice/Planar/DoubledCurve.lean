/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Winding

open Finset

namespace LatticeProb.Lattice.Planar

/-- The doubled walk. -/
def dbl : List Site → List Site
  | [] => []
  | [a] => [a + a]
  | a :: b :: l => (a + a) :: (a + b) :: dbl (b :: l)

theorem dbl_ne_nil {c : List Site} (hc : c ≠ []) : dbl c ≠ [] := by
  rcases c with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [dbl]

theorem dbl_head? : ∀ (c : List Site), (dbl c).head? = c.head?.map (fun a => a + a)
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem dbl_getLast? : ∀ (c : List Site), (dbl c).getLast? = c.getLast?.map (fun a => a + a)
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    obtain ⟨q, l', hq⟩ := List.exists_cons_of_ne_nil (dbl_ne_nil (List.cons_ne_nil b l))
    have ih := dbl_getLast? (b :: l)
    show ((a + a) :: (a + b) :: dbl (b :: l)).getLast? = _
    rw [hq, List.getLast?_cons_cons, List.getLast?_cons_cons, ← hq, ih, List.getLast?_cons_cons]

theorem mem_dbl : ∀ {c : List Site} {q : Site},
    q ∈ dbl c ↔ (∃ a ∈ c, q = a + a) ∨ ∃ s ∈ steps c, q = s.1 + s.2
  | [], q => by simp [dbl, steps]
  | [a], q => by simp [dbl, steps]
  | a :: b :: l, q => by
    rw [dbl, List.mem_cons, List.mem_cons, mem_dbl (c := b :: l)]
    simp only [steps_cons_cons, List.mem_cons]
    constructor
    · rintro (rfl | rfl | ⟨a', ha', rfl⟩ | ⟨s, hs, rfl⟩)
      · exact Or.inl ⟨a, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨(a, b), Or.inl rfl, rfl⟩
      · exact Or.inl ⟨a', Or.inr ha', rfl⟩
      · exact Or.inr ⟨s, Or.inr hs, rfl⟩
    · rintro (⟨a', (rfl | ha'), rfl⟩ | ⟨s, (rfl | hs), rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨a', ha', rfl⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨s, hs, rfl⟩))

theorem mem_steps_dbl : ∀ {c : List Site} {s : Site × Site},
    s ∈ steps (dbl c) ↔ ∃ t ∈ steps c, s = (t.1 + t.1, t.1 + t.2) ∨ s = (t.1 + t.2, t.2 + t.2)
  | [], s => by simp [dbl, steps]
  | [a], s => by simp [dbl, steps]
  | a :: b :: l, s => by
    have h : dbl (a :: b :: l) = (a + a) :: (a + b) :: dbl (b :: l) := rfl
    have hne : dbl (b :: l) ≠ [] := dbl_ne_nil (List.cons_ne_nil _ _)
    obtain ⟨q, l', hq⟩ : ∃ q l', dbl (b :: l) = q :: l' := List.exists_cons_of_ne_nil hne
    have hq' : q = b + b := by
      have := dbl_head? (b :: l)
      rw [hq] at this
      simpa using this
    rw [h, hq, steps_cons_cons, steps_cons_cons, ← hq, List.mem_cons, List.mem_cons,
      mem_steps_dbl (c := b :: l), steps_cons_cons, hq']
    simp only [List.mem_cons]
    constructor
    · rintro (rfl | rfl | ⟨t, ht, ht'⟩)
      · exact ⟨(a, b), Or.inl rfl, Or.inl rfl⟩
      · exact ⟨(a, b), Or.inl rfl, Or.inr rfl⟩
      · exact ⟨t, Or.inr ht, ht'⟩
    · rintro ⟨t, (rfl | ht), (rfl | rfl)⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩)
      · exact Or.inr (Or.inr ⟨t, ht, Or.inr rfl⟩)

/-- The doubled walk of a closed walk is a closed walk. -/
theorem isClosedWalk_dbl {c : List Site} (hc : IsClosedWalk c) : IsClosedWalk (dbl c) where
  ne_nil := dbl_ne_nil hc.ne_nil
  closed := by rw [dbl_head?, dbl_getLast?, hc.closed]
  unit := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hs : ((dbl c)[i], (dbl c)[i + 1]) ∈ steps (dbl c) := by
      unfold steps
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [List.length_zip]; omega, ?_⟩
      rw [List.getElem_zip, List.getElem_tail]
    obtain ⟨t, ht, h⟩ := mem_steps_dbl.1 hs
    have hu := steps_unit hc ht
    rcases h with h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h <;> rw [h1, h2]
    · convert hu using 1; abel
    · convert hu using 1; abel

/-- Points of the doubled walk have an even coordinate. -/
theorem mem_dbl_even {c : List Site} (hc : IsClosedWalk c) {q : Site} (hq : q ∈ dbl c) :
    Even q.1 ∨ Even q.2 := by
  rcases mem_dbl.1 hq with ⟨a, -, rfl⟩ | ⟨s, hs, rfl⟩
  · exact Or.inl ⟨a.1, rfl⟩
  · have hu := steps_unit hc hs
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
    rw [isUnit_iff'] at hu
    simp only [Prod.fst_add, Prod.snd_add]
    rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inr ⟨a2, by omega⟩
    · exact Or.inr ⟨a2, by omega⟩
    · exact Or.inl ⟨a1, by omega⟩
    · exact Or.inl ⟨a1, by omega⟩

theorem oddodd_notMem_dbl {c : List Site} (hc : IsClosedWalk c) {q : Site} (h1 : Odd q.1)
    (h2 : Odd q.2) : q ∉ dbl c := by
  intro hq
  rcases mem_dbl_even hc hq with h | h
  · exact (Int.not_even_iff_odd.2 h1) h
  · exact (Int.not_even_iff_odd.2 h2) h

theorem steps_unit' {c : List Site} (hch : c.IsChain (fun a b => IsUnit (b - a)))
    {s : Site × Site} (hs : s ∈ steps c) : IsUnit (s.2 - s.1) := by
  unfold steps at hs
  obtain ⟨i, hi, hs'⟩ := List.mem_iff_getElem.1 hs
  rw [List.getElem_zip] at hs'
  subst hs'
  simp only [List.length_zip, List.length_tail, lt_min_iff] at hi
  have := List.isChain_iff_getElem.1 hch i (by omega)
  simpa [List.getElem_tail] using this

/-- A midpoint determines its bond. -/
theorem bond_eq_of_mid_eq {a b a' b' : Site} (h : IsUnit (b - a)) (h' : IsUnit (b' - a'))
    (hm : a + b = a' + b') : (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := a'; obtain ⟨d1, d2⟩ := b'
  rw [isUnit_iff'] at h h'
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at hm ⊢
  omega

/-- The doubled list of a nodup list with unit steps is nodup. -/
theorem dbl_nodup_of_nodup : ∀ {t : List Site}, t.Nodup → t.IsChain (fun a b => IsUnit (b - a)) →
    (dbl t).Nodup
  | [], _, _ => List.nodup_nil
  | [_], _, _ => List.nodup_singleton _
  | b :: c :: l, hnd, hch => by
    have hch' := hch
    rw [List.isChain_cons_cons] at hch'
    have hnd' := List.nodup_cons.1 hnd
    have ih := dbl_nodup_of_nodup hnd'.2 hch'.2
    show ((b + b) :: (b + c) :: dbl (c :: l)).Nodup
    have hmem : ∀ q ∈ dbl (c :: l), (∃ a ∈ c :: l, q = a + a) ∨ ∃ s ∈ steps (c :: l), q = s.1 + s.2 :=
      fun q hq => mem_dbl.1 hq
    have hunit : ∀ s ∈ steps (c :: l), IsUnit (s.2 - s.1) := fun s hs => steps_unit' hch'.2 hs
    have hsteps_mem : ∀ s ∈ steps (c :: l), s.1 ∈ c :: l ∧ s.2 ∈ c :: l := fun s hs => mem_steps hs
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih⟩⟩
    · rw [List.mem_cons, not_or]
      refine ⟨fun h => hnd'.1 ?_, fun h => ?_⟩
      · have : b = c := by
          have := congrArg (fun p => p - b) h
          simpa using this
        rw [this]; exact List.mem_cons_self
      · rcases hmem _ h with ⟨a, ha, hab⟩ | ⟨s, hs, hab⟩
        · have : b = a := by
            obtain ⟨b1, b2⟩ := b; obtain ⟨a1, a2⟩ := a
            simp only [Prod.mk_add_mk, Prod.mk.injEq] at hab
            ext <;> simp <;> omega
          exact hnd'.1 (this ▸ ha)
        · have hu := hunit s hs
          obtain ⟨b1, b2⟩ := b
          obtain ⟨⟨a1, a2⟩, ⟨d1, d2⟩⟩ := s
          rw [isUnit_iff'] at hu
          simp only [Prod.mk_add_mk, Prod.mk.injEq] at hab
          omega
    · intro h
      rcases hmem _ h with ⟨a, ha, hab⟩ | ⟨s, hs, hab⟩
      · have hu := hch'.1
        obtain ⟨b1, b2⟩ := b
        obtain ⟨c1, c2⟩ := c
        obtain ⟨a1, a2⟩ := a
        rw [isUnit_iff'] at hu
        simp only [Prod.mk_add_mk, Prod.mk.injEq] at hab
        omega
      · rcases bond_eq_of_mid_eq hch'.1 (hunit s hs) hab with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hnd'.1 (h1 ▸ (hsteps_mem s hs).1)
        · exact hnd'.1 (h1 ▸ (hsteps_mem s hs).2)

/-- The doubled walk of a simple closed walk is simple. -/
theorem dbl_tail_nodup {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup)
    (h3 : 3 ≤ c.tail.length) : (dbl c).tail.Nodup := by
  rcases c with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exact absurd rfl hc.ne_nil
  · simp at h3
  rw [List.tail_cons] at hnd h3
  have hch : (b :: l).IsChain (fun a b => IsUnit (b - a)) := (List.isChain_cons_cons.1 hc.unit).2
  have hab : IsUnit (b - a) := (List.isChain_cons_cons.1 hc.unit).1
  show ((a + b) :: dbl (b :: l)).Nodup
  refine List.nodup_cons.2 ⟨?_, dbl_nodup_of_nodup hnd hch⟩
  intro h
  rcases mem_dbl.1 h with ⟨z, -, hz⟩ | ⟨s, hs, hab'⟩
  · obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨z1, z2⟩ := z
    rw [isUnit_iff'] at hab
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hz
    omega
  · -- the bond `{a, b}` is a step of `b :: l`: impossible for a simple closed walk of length ≥ 3
    have hu := steps_unit' hch hs
    have hlast : (b :: l).getLast (List.cons_ne_nil _ _) = a := by
      have := hc.closed
      rw [List.head?_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
        List.getLast_cons_cons] at this
      simpa using this.symm
    unfold steps at hs
    obtain ⟨i, hi, hs'⟩ := List.mem_iff_getElem.1 hs
    rw [List.getElem_zip, List.getElem_tail] at hs'
    simp only [List.length_zip, List.length_tail, lt_min_iff, List.length_cons] at hi
    rcases bond_eq_of_mid_eq hab hu hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `a = (b :: l)[i]` and `b = (b :: l)[i+1]`: `b` occurs at index 0 and `i + 1`
      rw [← hs'] at h1 h2
      simp only at h1 h2
      have hb0 : (b :: l)[0] = b := rfl
      have := List.Nodup.getElem_inj_iff hnd (i := i + 1) (j := 0)
        (hi := by simp only [List.length_cons] at hi ⊢; omega)
        (hj := by simp) |>.1 (by rw [hb0]; exact h2.symm)
      omega
    · -- `a = (b :: l)[i+1]` and `b = (b :: l)[i]`: then `i = 0` and `a` at index `1` and the last
      rw [← hs'] at h1 h2
      simp only at h1 h2
      have hb0 : (b :: l)[0] = b := rfl
      have hi0 : i = 0 := List.Nodup.getElem_inj_iff hnd (i := i) (j := 0)
        (hi := by simp only [List.length_cons] at hi ⊢; omega) (hj := by simp) |>.1
        (by rw [hb0]; exact h2.symm)
      subst hi0
      have hlast' : (b :: l)[(b :: l).length - 1] = a := by
        rw [List.getElem_length_sub_one_eq_getLast]; exact hlast
      have := List.Nodup.getElem_inj_iff hnd (i := 0 + 1) (j := (b :: l).length - 1)
        (hi := by simp only [List.length_cons] at hi ⊢; omega)
        (hj := by simp only [List.length_cons]; omega) |>.1 (by rw [hlast']; exact h1.symm)
      simp only [List.length_cons] at this h3
      omega

/-- The reverse of a step of a simple closed walk is not a step. -/
theorem rev_notMem_steps {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup)
    (h3 : 3 ≤ c.tail.length) {a b : Site} (hs : (a, b) ∈ steps c) : (b, a) ∉ steps c := by
  intro hs'
  -- both `(a, b)` and `(b, a)` are steps of the doubled walk's underlying cyclic order:
  -- their midpoints coincide, contradicting `dbl_tail_nodup` unless they are the same step.
  have hnd2 := dbl_tail_nodup hc hnd h3
  have hne : a ≠ b := by
    intro h; subst h
    have := steps_unit hc hs
    simp [IsUnit, Prod.ext_iff] at this
  -- the two doubled midpoints `a + b` and `b + a` are equal, and the corresponding steps of
  -- `dbl c` are `(a + a, a + b)` and `(b + b, a + b)`: two distinct steps with the same head
  have h1 : (a + a, a + b) ∈ steps (dbl c) := mem_steps_dbl.2 ⟨(a, b), hs, Or.inl rfl⟩
  have h2 : (b + b, b + a) ∈ steps (dbl c) := mem_steps_dbl.2 ⟨(b, a), hs', Or.inl rfl⟩
  rw [add_comm b a] at h2
  -- in `zip (dbl c) (dbl c).tail` a head determines its step when the tail is nodup
  have key : ∀ {l : List Site}, l.tail.Nodup → ∀ {p q q' : Site}, (q, p) ∈ steps l → (q', p) ∈ steps l → q = q' := by
    intro l hl p q q' hq hq'
    unfold steps at hq hq'
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.1 hq
    obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.1 hq'
    rw [List.getElem_zip, Prod.mk.injEq] at hi' hj'
    simp only [List.length_zip, List.length_tail, lt_min_iff] at hi hj
    obtain ⟨hi1, hi2⟩ := hi'
    obtain ⟨hj1, hj2⟩ := hj'
    have := List.Nodup.getElem_inj_iff hl (i := i) (j := j) (hi := by simpa using hi.2)
      (hj := by simpa using hj.2) |>.1 (hi2.trans hj2.symm)
    subst this
    rw [← hi1, ← hj1]
  have := key hnd2 h1 h2
  apply hne
  have := congrArg (fun p => p - a) this
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq] at this
  ext <;> simp <;> omega

/-- The left point of the step `a → b`: the odd-odd point to the left of its midpoint. -/
def leftPt (a b : Site) : Site := a + b + rotL (b - a)

/-- The right point of the step `a → b`. -/
def rightPt (a b : Site) : Site := a + b + rotR (b - a)

theorem leftPt_odd {a b : Site} (h : IsUnit (b - a)) : Odd (leftPt a b).1 ∧ Odd (leftPt a b).2 := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  rw [isUnit_iff'] at h
  simp only [leftPt, rotL, Prod.mk_sub_mk, Prod.mk_add_mk, Int.odd_iff]
  omega

theorem rightPt_odd {a b : Site} (h : IsUnit (b - a)) :
    Odd (rightPt a b).1 ∧ Odd (rightPt a b).2 := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  rw [isUnit_iff'] at h
  simp only [rightPt, rotR, Prod.mk_sub_mk, Prod.mk_add_mk, Int.odd_iff]
  omega

/-- The vertical crossing identity in count form. -/
theorem wind_cross_vertical_count {c : List Site} (hc : IsClosedWalk c) (a : Site)
    (hR : a + (1, 0) ∉ c) :
    wind c (a + (-1, 0)) - wind c (a + (1, 0)) =
      ((steps c).count (a, a + (0, 1)) : ℤ) - (steps c).count (a + (0, 1), a) := by
  unfold wind
  rw [sum_map_sub']
  have : ((steps c).map (fun s => stepWind (a + (-1, 0)) s - stepWind (a + (1, 0)) s)).sum =
      ((steps c).map (fun s => (if s = (a, a + (0, 1)) then (1 : ℤ) else 0) -
        (if s = (a + (0, 1), a) then (1 : ℤ) else 0))).sum := by
    congr 1
    refine List.map_congr_left (fun s hs' => ?_)
    have hm := mem_steps hs'
    exact stepWind_cross_vertical a (steps_unit hc hs') (fun h => hR (h ▸ hm.1))
      (fun h => hR (h ▸ hm.2))
  rw [this, ← sum_map_sub', sum_map_indicator, sum_map_indicator]

/-- The horizontal crossing identity in count form. -/
theorem wind_cross_horizontal_count {c : List Site} (hc : IsClosedWalk c) (a : Site)
    (hU : a + (0, 1) ∉ c) :
    wind c (a + (0, 1)) - wind c (a + (0, -1)) =
      ((steps c).count (a, a + (1, 0)) : ℤ) - (steps c).count (a + (1, 0), a) := by
  have hA : wind c a = wind c (a + (0, 1)) := wind_eq_up hc hU
  have key := sum_steps_sub_closed hc
    (fun p => if a.1 + 1 ≤ p.1 ∧ p.2 = a.2 then (1 : ℤ) else 0)
  have : ((steps c).map (fun s =>
      (if a.1 + 1 ≤ s.2.1 ∧ s.2.2 = a.2 then (1 : ℤ) else 0) -
        (if a.1 + 1 ≤ s.1.1 ∧ s.1.2 = a.2 then (1 : ℤ) else 0))).sum =
      ((steps c).map (fun s => (stepWind (a + (0, -1)) s - stepWind a s) +
        ((if s = (a, a + (1, 0)) then (1 : ℤ) else 0) -
          (if s = (a + (1, 0), a) then (1 : ℤ) else 0)))).sum := by
    congr 1
    exact List.map_congr_left (fun s hs' => stepWind_row_horiz a (steps_unit hc hs'))
  rw [this, List.sum_map_add, ← sum_map_sub', ← sum_map_sub', sum_map_indicator,
    sum_map_indicator] at key
  unfold wind at hA ⊢
  linarith

theorem count_eq_one_of_mem_nodup {l : List (Site × Site)} (h : l.Nodup) {s : Site × Site}
    (hs : s ∈ l) : l.count s = 1 := List.count_eq_one_of_mem h hs

/-- Across a step of a simple closed walk, the winding number of the doubled walk is larger by
one on the left. -/
theorem wind_dbl_left_sub_right {c : List Site} (hc : IsClosedWalk c) (hnd : c.tail.Nodup)
    (h3 : 3 ≤ c.tail.length) {a b : Site} (hs : (a, b) ∈ steps c) :
    wind (dbl c) (leftPt a b) - wind (dbl c) (rightPt a b) = 1 := by
  have hc2 := isClosedWalk_dbl hc
  have hnd2 := steps_nodup (dbl_tail_nodup hc hnd h3)
  have hrev := rev_notMem_steps hc hnd h3 hs
  have hu := steps_unit hc hs
  have h1 : (a + a, a + b) ∈ steps (dbl c) := mem_steps_dbl.2 ⟨(a, b), hs, Or.inl rfl⟩
  have h2 : (a + b, b + b) ∈ steps (dbl c) := mem_steps_dbl.2 ⟨(a, b), hs, Or.inr rfl⟩
  have hL := leftPt_odd hu
  have hRt := rightPt_odd hu
  have hLoff : leftPt a b ∉ dbl c := oddodd_notMem_dbl hc hL.1 hL.2
  have hRoff : rightPt a b ∉ dbl c := oddodd_notMem_dbl hc hRt.1 hRt.2
  -- the reverses of the doubled steps are absent
  have hr : ∀ s ∈ steps (dbl c), s ≠ (a + b, a + a) ∧ s ≠ (b + b, a + b) := by
    intro s hs'
    obtain ⟨t, ht, ht'⟩ := mem_steps_dbl.1 hs'
    have htu := steps_unit hc ht
    obtain ⟨⟨t1, t2⟩, ⟨t3, t4⟩⟩ := t
    obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    rw [isUnit_iff'] at hu htu
    have hba : ((t1, t2), (t3, t4)) = ((b1, b2), (a1, a2)) → False := fun h => hrev (h ▸ ht)
    constructor
    · rintro rfl
      rcases ht' with h | h <;> simp only [Prod.mk_add_mk, Prod.mk.injEq] at h
      · omega
      · exact hba (by simp only [Prod.mk.injEq]; omega)
    · rintro rfl
      rcases ht' with h | h <;> simp only [Prod.mk_add_mk, Prod.mk.injEq] at h
      · exact hba (by simp only [Prod.mk.injEq]; omega)
      · omega
  have hr1 : (a + b, a + a) ∉ steps (dbl c) := fun h => (hr _ h).1 rfl
  have hr2 : (b + b, a + b) ∉ steps (dbl c) := fun h => (hr _ h).2 rfl
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  have hu' := hu
  rw [isUnit_iff'] at hu'
  rcases hu' with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst b1 b2
  · -- east: the doubled step `m → m + (1, 0)`, `m = a + b`
    set m : Site := (a1, a2) + (a1 + 1, a2) with hm
    have hm1 : m + (1, 0) = (a1 + 1, a2) + (a1 + 1, a2) := by rw [hm]; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
    have hm2 : m + (0, 1) = leftPt (a1, a2) (a1 + 1, a2) := by
      rw [hm]; simp [leftPt, rotL]
    have hm3 : m + (0, -1) = rightPt (a1, a2) (a1 + 1, a2) := by
      rw [hm]; simp [rightPt, rotR]
    have key := wind_cross_horizontal_count hc2 m (by rw [hm2]; exact hLoff)
    rw [hm1, hm2, hm3] at key
    rw [key, count_eq_one_of_mem_nodup hnd2 h2, List.count_eq_zero_of_not_mem hr2]
    simp
  · -- west: the doubled step `m + (1, 0) → m`
    set m : Site := (a1, a2) + (a1 - 1, a2) with hm
    have hm1 : m + (1, 0) = (a1, a2) + (a1, a2) := by rw [hm]; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
    have hm2 : m + (0, 1) = rightPt (a1, a2) (a1 - 1, a2) := by
      rw [hm]; simp [rightPt, rotR]
    have hm3 : m + (0, -1) = leftPt (a1, a2) (a1 - 1, a2) := by
      rw [hm]; simp [leftPt, rotL]
    have key := wind_cross_horizontal_count hc2 m (by rw [hm2]; exact hRoff)
    rw [hm1, hm2, hm3] at key
    rw [List.count_eq_zero_of_not_mem hr1, count_eq_one_of_mem_nodup hnd2 h1] at key
    simp only [Nat.cast_zero, Nat.cast_one] at key
    linarith
  · -- north: the doubled step `m → m + (0, 1)`
    set m : Site := (a1, a2) + (a1, a2 + 1) with hm
    have hm1 : m + (0, 1) = (a1, a2 + 1) + (a1, a2 + 1) := by rw [hm]; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
    have hm2 : m + (-1, 0) = leftPt (a1, a2) (a1, a2 + 1) := by
      rw [hm]; simp [leftPt, rotL]
    have hm3 : m + (1, 0) = rightPt (a1, a2) (a1, a2 + 1) := by
      rw [hm]; simp [rightPt, rotR]
    have key := wind_cross_vertical_count hc2 m (by rw [hm3]; exact hRoff)
    rw [hm1, hm2, hm3] at key
    rw [key, count_eq_one_of_mem_nodup hnd2 h2, List.count_eq_zero_of_not_mem hr2]
    simp
  · -- south: the doubled step `m + (0, 1) → m`
    set m : Site := (a1, a2) + (a1, a2 - 1) with hm
    have hm1 : m + (0, 1) = (a1, a2) + (a1, a2) := by rw [hm]; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
    have hm2 : m + (-1, 0) = rightPt (a1, a2) (a1, a2 - 1) := by
      rw [hm]; simp [rightPt, rotR]
    have hm3 : m + (1, 0) = leftPt (a1, a2) (a1, a2 - 1) := by
      rw [hm]; simp [leftPt, rotL]
    have key := wind_cross_vertical_count hc2 m (by rw [hm3]; exact hLoff)
    rw [hm1, hm2, hm3] at key
    rw [List.count_eq_zero_of_not_mem hr1, count_eq_one_of_mem_nodup hnd2 h1] at key
    simp only [Nat.cast_zero, Nat.cast_one] at key
    linarith

end LatticeProb.Lattice.Planar
