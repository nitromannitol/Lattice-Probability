/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ExplCover

open Finset Classical

namespace LatticeProb.Lattice.Planar

/-- The `ℓ^∞` distance on `ℤ²`. -/
def linfDist (x y : Site) : ℤ := max |x.1 - y.1| |x.2 - y.2|

theorem squareGraph_adj_add_east (x : Site) : squareGraph.Adj x (x + (1, 0)) := by
  rw [squareGraph_adj]; simp

theorem squareGraph_adj_add_west (x : Site) : squareGraph.Adj x (x + (-1, 0)) := by
  rw [squareGraph_adj]; simp

theorem squareGraph_adj_add_north (x : Site) : squareGraph.Adj x (x + (0, 1)) := by
  rw [squareGraph_adj]; simp

theorem squareGraph_adj_add_south (x : Site) : squareGraph.Adj x (x + (0, -1)) := by
  rw [squareGraph_adj]; simp

theorem squareGraph_reachable (x y : Site) : squareGraph.Reachable x y := by
  have key : ∀ n : ℕ, ∀ x y : Site, (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = n →
      squareGraph.Reachable x y := by
    intro n
    induction n with
    | zero =>
      intro x y h
      have hx : x = y := by
        obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
        simp only [Prod.mk.injEq]; omega
      rw [hx]
    | succ n ih =>
      intro x y h
      rcases lt_trichotomy x.1 y.1 with h1 | h1 | h1
      · exact (squareGraph_adj_add_east x).reachable.trans (ih (x + (1, 0)) y (by
          simp only [Prod.fst_add, Prod.snd_add]; omega))
      · rcases lt_or_gt_of_ne (show x.2 ≠ y.2 by intro h2; omega) with h2 | h2
        · exact (squareGraph_adj_add_north x).reachable.trans (ih (x + (0, 1)) y (by
            simp only [Prod.fst_add, Prod.snd_add]; omega))
        · exact (squareGraph_adj_add_south x).reachable.trans (ih (x + (0, -1)) y (by
            simp only [Prod.fst_add, Prod.snd_add]; omega))
      · exact (squareGraph_adj_add_west x).reachable.trans (ih (x + (-1, 0)) y (by
          simp only [Prod.fst_add, Prod.snd_add]; omega))
  exact key _ x y rfl

theorem squareGraph_connected : squareGraph.Connected :=
  ⟨fun x y => squareGraph_reachable x y⟩

theorem squareGraph_degree (v : Site) : squareGraph.degree v = 4 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (nbr v).symm]
  rfl

theorem dist_le_l1 (u w : Site) : (squareGraph.dist u w : ℤ) ≤ |w.1 - u.1| + |w.2 - u.2| := by
  have hconn := squareGraph_connected
  suffices h : ∀ n : ℕ, ∀ u w : Site, (|w.1 - u.1| + |w.2 - u.2|).toNat = n →
      (squareGraph.dist u w : ℤ) ≤ |w.1 - u.1| + |w.2 - u.2| from h _ u w rfl
  intro n
  induction n with
  | zero =>
    intro u w hn
    have h0 : |w.1 - u.1| + |w.2 - u.2| = 0 := by
      have := Int.toNat_of_nonneg (show 0 ≤ |w.1 - u.1| + |w.2 - u.2| by positivity)
      omega
    have hu : u = w := by
      obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
      simp only [abs_eq_max_neg] at h0
      ext <;> simp <;> omega
    subst hu
    simp
  | succ n ih =>
    intro u w hn
    obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
    -- a neighbour `u'` of `u` one step closer to `w`
    obtain ⟨u', hadj, hdist⟩ : ∃ u' : Site, squareGraph.Adj (u1, u2) u' ∧
        (|w1 - u'.1| + |w2 - u'.2|).toNat = n := by
      rcases lt_trichotomy u1 w1 with h | h | h
      · refine ⟨(u1 + 1, u2), ?_, ?_⟩
        · rw [squareGraph_adj]; simp
        · simp only at hn ⊢
          rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
      · subst h
        rcases lt_trichotomy u2 w2 with h2 | h2 | h2
        · refine ⟨(u1, u2 + 1), ?_, ?_⟩
          · rw [squareGraph_adj]; simp
          · simp only at hn ⊢
            rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
        · subst h2; simp at hn
        · refine ⟨(u1, u2 - 1), ?_, ?_⟩
          · rw [squareGraph_adj]; simp
          · simp only at hn ⊢
            rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
      · refine ⟨(u1 - 1, u2), ?_, ?_⟩
        · rw [squareGraph_adj]; simp
        · simp only at hn ⊢
          rw [abs_eq_max_neg] at hn ⊢; rw [abs_eq_max_neg] at hn ⊢; omega
    have h1 := ih u' (w1, w2) hdist
    have htri := hconn.dist_triangle (u := (u1, u2)) (v := u') (w := (w1, w2))
    have hone : squareGraph.dist (u1, u2) u' = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj
    have htri' : (squareGraph.dist (u1, u2) (w1, w2) : ℤ) ≤
        (squareGraph.dist (u1, u2) u' : ℤ) + squareGraph.dist u' (w1, w2) := by exact_mod_cast htri
    have hone' : (squareGraph.dist (u1, u2) u' : ℤ) = 1 := by exact_mod_cast hone
    have hsum : |w1 - u1| + |w2 - u2| = |w1 - u'.1| + |w2 - u'.2| + 1 := by
      have := Int.toNat_of_nonneg (show 0 ≤ |w1 - u1| + |w2 - u2| by positivity)
      have := Int.toNat_of_nonneg (show 0 ≤ |w1 - u'.1| + |w2 - u'.2| by positivity)
      dsimp only at hn
      omega
    dsimp only at h1 ⊢
    omega

theorem dist_le_two_linf (u w : Site) : (squareGraph.dist u w : ℤ) ≤ 2 * linfDist w u := by
  have := dist_le_l1 u w
  unfold linfDist
  obtain ⟨u1, u2⟩ := u; obtain ⟨w1, w2⟩ := w
  simp only at this ⊢
  have h1 : |w1 - u1| ≤ max |w1 - u1| |w2 - u2| := le_max_left _ _
  have h2 : |w2 - u2| ≤ max |w1 - u1| |w2 - u2| := le_max_right _ _
  omega

theorem linfDist_comm (a b : Site) : linfDist a b = linfDist b a := by
  simp [linfDist, abs_sub_comm]

theorem rightFace_near (v : Site) (a : Dir) : linfDist (rightFace v a) v ≤ 1 := by
  obtain ⟨v1, v2⟩ := v
  fin_cases a <;> simp [rightFace, dirVec, linfDist, abs_eq_max_neg]

theorem exists_far_visited {V : Finset Site} {g f₀ : Site} (h : InFiniteComponent V g) :
    ∃ g' ∈ V, linfDist g f₀ ≤ linfDist g' f₀ := by
  rw [inFiniteComponent_iff] at h
  obtain ⟨hgV, hfin⟩ := h
  have hgS : g ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact Relation.ReflTransGen.refl
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun z => linfDist z f₀) ⟨g, hgS⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hz
  have hzV : z ∉ V := AvoidReach.notMem hgV hz
  -- a neighbour of `z` one step farther from `f₀`
  obtain ⟨z', hadj, hfar⟩ : ∃ z' : Site, squareGraph.Adj z z' ∧ linfDist z' f₀ = linfDist z f₀ + 1 := by
    obtain ⟨z1, z2⟩ := z; obtain ⟨f1, f2⟩ := f₀
    simp only [linfDist]
    rcases le_or_gt |z2 - f2| |z1 - f1| with hx | hx
    · rcases le_or_gt 0 (z1 - f1) with hs | hs
      · refine ⟨(z1 + 1, z2), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
      · refine ⟨(z1 - 1, z2), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
    · rcases le_or_gt 0 (z2 - f2) with hs | hs
      · refine ⟨(z1, z2 + 1), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
      · refine ⟨(z1, z2 - 1), by rw [squareGraph_adj]; simp, ?_⟩
        simp only [abs_eq_max_neg] at hx ⊢; omega
  by_cases hz'V : z' ∈ V
  · refine ⟨z', hz'V, ?_⟩
    have := hmax g hgS
    omega
  · exfalso
    have hz'S : z' ∈ hfin.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Relation.ReflTransGen.tail hz ⟨hzV, hz'V, hadj⟩
    have := hmax z' hz'S
    omega

end LatticeProb.Lattice.Planar
