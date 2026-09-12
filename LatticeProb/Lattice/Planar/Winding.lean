/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.DualGeom

open Finset

namespace LatticeProb.Lattice.Planar

/-- The steps of a walk: the consecutive pairs. -/
def steps (c : List Site) : List (Site × Site) := c.zip c.tail

/-- A closed walk of unit steps. -/
structure IsClosedWalk (c : List Site) : Prop where
  ne_nil : c ≠ []
  closed : c.head? = c.getLast?
  unit : c.IsChain (fun a b => IsUnit (b - a))

/-- The signed crossing of the eastward ray from `y` (at height `y.2 + 1/2`) by the step `s`. -/
def stepWind (y : Site) (s : Site × Site) : ℤ :=
  if s.1.1 = s.2.1 ∧ y.1 < s.1.1 ∧ min s.1.2 s.2.2 = y.2 then s.2.2 - s.1.2 else 0

/-- The winding number of the closed walk `c` about `y`. -/
def wind (c : List Site) (y : Site) : ℤ := ((steps c).map (stepWind y)).sum

theorem steps_cons_cons (a b : Site) (l : List Site) :
    steps (a :: b :: l) = (a, b) :: steps (b :: l) := rfl

theorem steps_singleton (a : Site) : steps [a] = [] := rfl

theorem steps_nil : steps [] = [] := rfl

/-- Telescoping along a walk. -/
theorem sum_steps_sub (g : Site → ℤ) : ∀ (a : Site) (l : List Site),
    ((steps (a :: l)).map (fun s => g s.2 - g s.1)).sum = g ((a :: l).getLast (by simp)) - g a
  | a, [] => by simp [steps]
  | a, b :: l => by
    rw [steps_cons_cons, List.map_cons, List.sum_cons, sum_steps_sub g b l]
    simp only [List.getLast_cons_cons]
    ring

theorem sum_steps_sub_closed {c : List Site} (hc : IsClosedWalk c) (g : Site → ℤ) :
    ((steps c).map (fun s => g s.2 - g s.1)).sum = 0 := by
  rcases c with _ | ⟨a, l⟩
  · exact absurd rfl hc.ne_nil
  rw [sum_steps_sub g a l]
  have := hc.closed
  rw [List.head?_cons, List.getLast?_eq_some_getLast (by simp)] at this
  simp only [Option.some.injEq] at this
  rw [← this, sub_self]

theorem mem_steps {c : List Site} {s : Site × Site} (hs : s ∈ steps c) : s.1 ∈ c ∧ s.2 ∈ c := by
  unfold steps at hs
  obtain ⟨i, hi, hs'⟩ := List.mem_iff_getElem.1 hs
  rw [List.getElem_zip] at hs'
  subst hs'
  simp only [List.length_zip, List.length_tail, lt_min_iff] at hi
  refine ⟨List.getElem_mem _, ?_⟩
  rw [List.getElem_tail]
  exact List.getElem_mem _

theorem steps_unit {c : List Site} (hc : IsClosedWalk c) {s : Site × Site} (hs : s ∈ steps c) :
    IsUnit (s.2 - s.1) := by
  unfold steps at hs
  obtain ⟨i, hi, hs'⟩ := List.mem_iff_getElem.1 hs
  rw [List.getElem_zip] at hs'
  subst hs'
  simp only [List.length_zip, List.length_tail, lt_min_iff] at hi
  have := List.isChain_iff_getElem.1 hc.unit i (by omega)
  simpa [List.getElem_tail] using this

theorem isUnit_iff' {a1 a2 b1 b2 : ℤ} : IsUnit ((b1, b2) - (a1, a2)) ↔
    (b1 = a1 + 1 ∧ b2 = a2) ∨ (b1 = a1 - 1 ∧ b2 = a2) ∨ (b1 = a1 ∧ b2 = a2 + 1) ∨
      (b1 = a1 ∧ b2 = a2 - 1) := by
  simp only [IsUnit, Prod.mk_sub_mk, Prod.mk.injEq]
  omega

theorem sum_map_sub' (l : List (Site × Site)) (f g : Site × Site → ℤ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun s => f s - g s)).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- The per-step accounting for a vertical neighbour: entries into the row above `y`. -/
theorem stepWind_row (y : Site) {s : Site × Site} (hu : IsUnit (s.2 - s.1))
    (h1 : s.1 ≠ y + (0, 1)) (h2 : s.2 ≠ y + (0, 1)) :
    stepWind y s - stepWind (y + (0, 1)) s =
      (if y.1 + 1 ≤ s.2.1 ∧ s.2.2 = y.2 + 1 then (1 : ℤ) else 0) -
        (if y.1 + 1 ≤ s.1.1 ∧ s.1.2 = y.2 + 1 then (1 : ℤ) else 0) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨y1, y2⟩ := y
  rw [isUnit_iff'] at hu
  simp only [Prod.mk_add_mk, Prod.mk.injEq, ne_eq, not_and] at h1 h2 ⊢
  unfold stepWind
  dsimp only
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> split_ifs <;> omega

/-- Vertical neighbours off `c` have the same winding number. -/
theorem wind_eq_up {c : List Site} (hc : IsClosedWalk c) {y : Site} (hy : y + (0, 1) ∉ c) :
    wind c y = wind c (y + (0, 1)) := by
  have key : ((steps c).map (fun s => stepWind y s - stepWind (y + (0, 1)) s)).sum =
      ((steps c).map (fun s => (if y.1 + 1 ≤ s.2.1 ∧ s.2.2 = y.2 + 1 then (1 : ℤ) else 0) -
        (if y.1 + 1 ≤ s.1.1 ∧ s.1.2 = y.2 + 1 then (1 : ℤ) else 0))).sum := by
    congr 1
    refine List.map_congr_left (fun s hs => ?_)
    have hm := mem_steps hs
    exact stepWind_row y (steps_unit hc hs) (fun h => hy (h ▸ hm.1)) (fun h => hy (h ▸ hm.2))
  rw [sum_steps_sub_closed hc (fun p => if y.1 + 1 ≤ p.1 ∧ p.2 = y.2 + 1 then (1 : ℤ) else 0)]
    at key
  unfold wind
  rw [← sub_eq_zero, sum_map_sub']
  exact key

/-- Horizontal neighbours off `c` have the same winding number. -/
theorem wind_eq_right {c : List Site} (hc : IsClosedWalk c) {y : Site} (hy : y + (1, 0) ∉ c) :
    wind c y = wind c (y + (1, 0)) := by
  unfold wind
  rw [← sub_eq_zero, sum_map_sub']
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have hm := mem_steps hs
  have hu := steps_unit hc hs
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨y1, y2⟩ := y
  have h1 : (a1, a2) ≠ (y1 + 1, y2) := fun h => hy (by rw [Prod.mk_add_mk, add_zero, ← h]; exact hm.1)
  have h2 : (b1, b2) ≠ (y1 + 1, y2) := fun h => hy (by rw [Prod.mk_add_mk, add_zero, ← h]; exact hm.2)
  rw [isUnit_iff'] at hu
  simp only [Prod.mk_add_mk, Prod.mk.injEq, ne_eq, not_and] at h1 h2 ⊢
  unfold stepWind
  dsimp only
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> split_ifs <;> omega

/-- Adjacent points off `c` have the same winding number. -/
theorem wind_eq_of_adj {c : List Site} (hc : IsClosedWalk c) {y z : Site} (hy : y ∉ c) (hz : z ∉ c)
    (hyz : IsUnit (z - y)) : wind c y = wind c z := by
  have hz' : z = y + (z - y) := by abel
  rcases hyz with h | h | h | h <;> rw [h] at hz' <;> subst hz'
  · exact wind_eq_right hc hz
  · have e : y + (-1, 0) + (1, 0) = y := by ext <;> simp
    have := wind_eq_right hc (y := y + (-1, 0)) (by rwa [e])
    rw [e] at this
    exact this.symm
  · exact wind_eq_up hc hz
  · have e : y + (0, -1) + (0, 1) = y := by ext <;> simp
    have := wind_eq_up hc (y := y + (0, -1)) (by rwa [e])
    rw [e] at this
    exact this.symm

/-- Far to the right of `c` the winding number vanishes. -/
theorem wind_eq_zero_of_far {c : List Site} {y : Site} (hy : ∀ p ∈ c, p.1 ≤ y.1) :
    wind c y = 0 := by
  unfold wind
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have h := hy _ (mem_steps hs).1
  unfold stepWind
  split_ifs <;> omega

/-- The steps of a simple closed walk are distinct. -/
theorem steps_nodup {c : List Site} (hc : c.tail.Nodup) : (steps c).Nodup := by
  rcases c with _ | ⟨a, l⟩
  · exact List.nodup_nil
  have : (steps (a :: l)).map Prod.snd = l := by
    unfold steps
    rw [List.map_snd_zip]
    · rfl
    · simp
  rw [List.tail_cons] at hc
  rw [← this] at hc
  exact hc.of_map _

/-- Winding numbers are constant along lattice paths off `c`. -/
theorem wind_eq_of_reflTransGen {c : List Site} (hc : IsClosedWalk c) {y z : Site}
    (h : Relation.ReflTransGen (fun p q => p ∉ c ∧ q ∉ c ∧ IsUnit (q - p)) y z) :
    wind c y = wind c z := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (wind_eq_of_adj hc hbc.1 hbc.2.1 hbc.2.2)

theorem sum_map_indicator (l : List (Site × Site)) (x : Site × Site) :
    (l.map (fun s => if s = x then (1 : ℤ) else 0)).sum = l.count x := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : s = x
    · subst h
      simp only [if_true, beq_self_eq_true, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [if_neg h, Nat.cast_add]
      rw [if_neg (by simpa using h)]
      simp

/-- The per-step accounting across a vertical step `a → a + (0, 1)`: only that step and its
reverse separate the points `a ± (1, 0)`. -/
theorem stepWind_cross_vertical (a : Site) {s : Site × Site} (hu : IsUnit (s.2 - s.1))
    (h1 : s.1 ≠ a + (1, 0)) (h2 : s.2 ≠ a + (1, 0)) :
    stepWind (a + (-1, 0)) s - stepWind (a + (1, 0)) s =
      (if s = (a, a + (0, 1)) then (1 : ℤ) else 0) -
        (if s = (a + (0, 1), a) then (1 : ℤ) else 0) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨x1, x2⟩ := a
  rw [isUnit_iff'] at hu
  simp only [Prod.mk_add_mk, Prod.mk.injEq, ne_eq, not_and] at h1 h2 ⊢
  unfold stepWind
  dsimp only
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h h' <;> split_ifs <;> omega

/-- Across an upward step of a simple closed walk the winding number increases by one from
right to left. -/
theorem wind_cross_vertical {c : List Site} (hc : IsClosedWalk c) (hnd : (steps c).Nodup)
    {a : Site} (hs : (a, a + (0, 1)) ∈ steps c) (hrev : (a + (0, 1), a) ∉ steps c)
    (hR : a + (1, 0) ∉ c) :
    wind c (a + (-1, 0)) - wind c (a + (1, 0)) = 1 := by
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
  rw [this, ← sum_map_sub', sum_map_indicator, sum_map_indicator,
    List.count_eq_one_of_mem hnd hs, List.count_eq_zero_of_not_mem hrev]
  simp

/-- The per-step accounting for the row of an eastward step `a → a + (1, 0)`, to its right:
entries and exits of the row, with the step itself and its reverse crossing the left end. -/
theorem stepWind_row_horiz (a : Site) {s : Site × Site} (hu : IsUnit (s.2 - s.1)) :
    (if a.1 + 1 ≤ s.2.1 ∧ s.2.2 = a.2 then (1 : ℤ) else 0) -
      (if a.1 + 1 ≤ s.1.1 ∧ s.1.2 = a.2 then (1 : ℤ) else 0) =
    (stepWind (a + (0, -1)) s - stepWind a s) +
      ((if s = (a, a + (1, 0)) then (1 : ℤ) else 0) - (if s = (a + (1, 0), a) then (1 : ℤ) else 0)) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨x1, x2⟩ := a
  rw [isUnit_iff'] at hu
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  unfold stepWind
  dsimp only
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h h' <;> split_ifs <;> omega

/-- Across an eastward step of a simple closed walk the winding number increases by one from
the point below to the point above. -/
theorem wind_cross_horizontal {c : List Site} (hc : IsClosedWalk c) (hnd : (steps c).Nodup)
    {a : Site} (hs : (a, a + (1, 0)) ∈ steps c) (hrev : (a + (1, 0), a) ∉ steps c)
    (hU : a + (0, 1) ∉ c) :
    wind c (a + (0, 1)) - wind c (a + (0, -1)) = 1 := by
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
    sum_map_indicator, List.count_eq_one_of_mem hnd hs, List.count_eq_zero_of_not_mem hrev] at key
  unfold wind at hA ⊢
  simp only [Nat.cast_one, Nat.cast_zero] at key
  linarith

end LatticeProb.Lattice.Planar
