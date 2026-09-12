/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.DoubledCurve

open Finset Fin.NatCast

namespace LatticeProb.Lattice.Planar

/-- The offsets of the eight neighbours, counterclockwise from east. -/
def ringOff : Fin 8 → Site
  | 0 => (1, 0) | 1 => (1, 1) | 2 => (0, 1) | 3 => (-1, 1)
  | 4 => (-1, 0) | 5 => (-1, -1) | 6 => (0, -1) | 7 => (1, -1)

/-- `-1` as an element of `Fin 8`. -/
theorem fin8_neg_one : (-1 : Fin 8) = 7 := by decide

/-- The `i`-th point of the ring around `p`. -/
def ringPt (p : Site) (i : Fin 8) : Site := p + ringOff i

instance instDecidablePredSiteIsUnit : DecidablePred IsUnit := fun d => by unfold IsUnit; infer_instance

theorem ringPt_adj (p : Site) (i : Fin 8) : IsUnit (ringPt p (i + 1) - ringPt p i) := by
  simp only [ringPt, add_sub_add_left_eq_sub]
  fin_cases i <;> decide

/-- The index of a unit direction. -/
def dirIdx (d : Site) : Fin 8 :=
  if d = (1, 0) then 0 else if d = (0, 1) then 2 else if d = (-1, 0) then 4 else 6

theorem ringOff_dirIdx {d : Site} (hd : IsUnit d) : ringOff (dirIdx d) = d := by
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

theorem dirIdx_neg {d : Site} (hd : IsUnit d) : dirIdx (-d) = dirIdx d + 4 := by
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

theorem dirIdx_rotL {d : Site} (hd : IsUnit d) : dirIdx (rotL d) = dirIdx d + 2 := by
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

theorem dirIdx_rotR {d : Site} (hd : IsUnit d) : dirIdx (rotR d) = dirIdx d + 6 := by
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

theorem dirIdx_even {d : Site} (hd : IsUnit d) : Even (dirIdx d).val := by
  rcases hd with rfl | rfl | rfl | rfl <;> decide

theorem dirIdx_injective {d d' : Site} (hd : IsUnit d) (hd' : IsUnit d') (h : dirIdx d = dirIdx d') :
    d = d' := by
  rcases hd with rfl | rfl | rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl <;> first | rfl | exact absurd h (by decide)

/-- `k` lies strictly between `i` and `j`, counterclockwise from `i`. -/
def Between (i j k : Fin 8) : Prop := 0 < (k - i).val ∧ (k - i).val < (j - i).val

instance instDecidableBetween (i j k : Fin 8) : Decidable (Between i j k) := by unfold Between; infer_instance

/-- The odd-odd points of the ring are the odd indices. -/
theorem ringPt_odd (p : Site) (hp1 : Even p.1) (hp2 : Even p.2) (i : Fin 8) (hi : Odd i.val) :
    Odd (ringPt p i).1 ∧ Odd (ringPt p i).2 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨m, hm⟩ := hp1
  obtain ⟨n, hn⟩ := hp2
  simp only at hm hn
  subst hm hn
  fin_cases i <;> simp only [Nat.odd_iff] at hi <;>
    simp only [ringPt, ringOff, Prod.mk_add_mk, Int.odd_iff] <;> omega

/-- The relation "adjacent and both off `c`". -/
def OffAdj (c : List Site) (x y : Site) : Prop := x ∉ c ∧ y ∉ c ∧ IsUnit (y - x)

theorem OffAdj.symm {c : List Site} {x y : Site} (h : OffAdj c x y) : OffAdj c y x := by
  refine ⟨h.2.1, h.1, ?_⟩
  have := h.2.2
  rcases this with h' | h' | h' | h'
  all_goals
    have e : x - y = -(y - x) := by abel
    rw [e, h']
    simp [IsUnit]

theorem reflTransGen_offAdj_symm {c : List Site} {x y : Site}
    (h : Relation.ReflTransGen (OffAdj c) x y) : Relation.ReflTransGen (OffAdj c) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single hbc.symm).trans ih

/-- Consecutive ring points off `c` are connected. -/
theorem ringPt_reach_succ {c : List Site} (p : Site) (i : Fin 8) (h1 : ringPt p i ∉ c)
    (h2 : ringPt p (i + 1) ∉ c) :
    Relation.ReflTransGen (OffAdj c) (ringPt p i) (ringPt p (i + 1)) :=
  Relation.ReflTransGen.single ⟨h1, h2, ringPt_adj p i⟩

/-- The points of an arc off `c` are connected: from `i + m` to `i + m'` for `m ≤ m'` inside the
arc. -/
theorem ringPt_reach_arc {c : List Site} (p : Site) (i j : Fin 8)
    (hoff : ∀ l, Between i j l → ringPt p l ∉ c) :
    ∀ (m m' : ℕ), 0 < m → m ≤ m' → m' < (j - i).val →
      Relation.ReflTransGen (OffAdj c) (ringPt p (i + (m : Fin 8))) (ringPt p (i + (m' : Fin 8))) := by
  intro m m' hm hmm' hm'
  induction m' with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · have hn : 0 < n := by omega
      have hb1 : Between i j (i + (n : Fin 8)) := by
        refine ⟨?_, ?_⟩ <;> simp only [add_sub_cancel_left, Fin.val_natCast] <;> omega
      have hb2 : Between i j (i + ((n + 1 : ℕ) : Fin 8)) := by
        refine ⟨?_, ?_⟩ <;> simp only [add_sub_cancel_left, Fin.val_natCast] <;> omega
      refine (ih (by omega) (by omega)).trans ?_
      have e : i + (n : Fin 8) + 1 = i + ((n + 1 : ℕ) : Fin 8) := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_natCast, Fin.val_one]
        omega
      have := ringPt_reach_succ p (i + (n : Fin 8)) (hoff _ hb1) (by rw [e]; exact hoff _ hb2)
      rw [e] at this
      exact this
    · have : m = n + 1 := by omega
      subst this
      exact Relation.ReflTransGen.refl

/-- Any two points of the arc from `i` to `j` are connected off `c`. -/
theorem ringPt_reach_of_between {c : List Site} (p : Site) (i j : Fin 8)
    (hoff : ∀ l, Between i j l → ringPt p l ∉ c) {k k' : Fin 8} (hk : Between i j k)
    (hk' : Between i j k') : Relation.ReflTransGen (OffAdj c) (ringPt p k) (ringPt p k') := by
  have ek : k = i + ((k - i).val : ℕ) := by simp
  have ek' : k' = i + ((k' - i).val : ℕ) := by simp
  rcases le_or_gt (k - i).val (k' - i).val with h | h
  · rw [ek, ek']
    exact ringPt_reach_arc p i j hoff _ _ hk.1 h hk'.2
  · rw [ek, ek']
    exact reflTransGen_offAdj_symm (ringPt_reach_arc p i j hoff _ _ hk'.1 h.le hk.2)

/-- The corner just counterclockwise of the outgoing direction and the corner just clockwise
of the reverse incoming direction lie in the left arc, whenever the walk does not reverse. -/
theorem between_corners (i j : Fin 8) (hi : Even i.val) (hj : Even j.val) (hij : i ≠ j) :
    Between i j (i + 1) ∧ Between i j (j - 1) := by
  revert i j; decide

/-- The left point of the step into `z` is the corner clockwise of the reverse incoming
direction. -/
theorem leftPt_in_eq (z u : Site) (hu : IsUnit u) :
    leftPt (z - u) z = ringPt (z + z) (dirIdx (-u) - 1) := by
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp [leftPt, ringPt, rotL, dirIdx, ringOff, Prod.ext_iff, fin8_neg_one] <;> ring_nf

/-- The left point of the step out of `z` is the corner counterclockwise of the outgoing
direction. -/
theorem leftPt_out_eq (z w : Site) (hw : IsUnit w) :
    leftPt z (z + w) = ringPt (z + z) (dirIdx w + 1) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [leftPt, ringPt, rotL, dirIdx, ringOff, Prod.ext_iff] <;> ring_nf

theorem rightPt_in_eq (z u : Site) (hu : IsUnit u) :
    rightPt (z - u) z = ringPt (z + z) (dirIdx (-u) + 1) := by
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp [rightPt, ringPt, rotR, dirIdx, ringOff, Prod.ext_iff] <;> ring_nf

theorem rightPt_out_eq (z w : Site) (hw : IsUnit w) :
    rightPt z (z + w) = ringPt (z + z) (dirIdx w - 1) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [rightPt, ringPt, rotR, dirIdx, ringOff, Prod.ext_iff, fin8_neg_one] <;> ring_nf

/-- The midpoint of the bond from `z` in the direction `v` is a ring point. -/
theorem mid_eq_ringPt (z v : Site) (hv : IsUnit v) : z + z + v = ringPt (z + z) (dirIdx v) := by
  rw [ringPt, ringOff_dirIdx hv]

end LatticeProb.Lattice.Planar
