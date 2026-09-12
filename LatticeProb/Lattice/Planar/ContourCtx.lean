/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ContourPath
import LatticeProb.Lattice.Planar.SectorFacts
import LatticeProb.Lattice.Planar.Separation

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

theorem dbl_length : ∀ (w : List Site), w ≠ [] → (dbl w).length = 2 * w.length - 1
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: l, _ => by
    rw [dbl, List.length_cons, List.length_cons, dbl_length (b :: l) (List.cons_ne_nil _ _)]
    simp only [List.length_cons]
    omega

theorem isSimpleClosed_dbl {J : List Site} (hJ : IsSimpleClosed J) : IsSimpleClosed (dbl J) where
  closed := isClosedWalk_dbl hJ.closed
  nodup := dbl_tail_nodup hJ.closed hJ.nodup hJ.three
  three := by
    have h1 := hJ.three
    have h2 := dbl_length J hJ.closed.ne_nil
    have h3 : (dbl J).tail.length = (dbl J).length - 1 := List.length_tail
    have h4 : J.tail.length = J.length - 1 := List.length_tail
    omega

/-- A point of the left arc at the vertex `2z` of `dbl J` is connected to the left point of
the step into `2z`. -/
theorem left_of_arc {J₁ : List Site} (hJ₁ : IsSimpleClosed J₁) {z p q : Site}
    (hin : (p + z, z + z) ∈ steps J₁) (hout : (z + z, z + q) ∈ steps J₁) {v : Site}
    (hb : Between (dirIdx (q - z)) (dirIdx (p - z)) (dirIdx v)) {Y : Site}
    (hreach : Relation.ReflTransGen (OffAdj (dbl J₁)) Y (ringPt (z + z + (z + z)) (dirIdx v))) :
    Relation.ReflTransGen (OffAdj (dbl J₁)) Y (leftPt (p + z) (z + z)) := by
  have hu : IsUnit (z + z - (p + z)) := steps_unit hJ₁.closed hin
  have hw : IsUnit (z + q - (z + z)) := steps_unit hJ₁.closed hout
  have e1 : z + z - (p + z) = z - p := by abel
  have e2 : z + q - (z + z) = q - z := by abel
  rw [e1] at hu; rw [e2] at hw
  have hpq : q ≠ p := by
    rintro rfl
    have := rev_notMem_steps' hJ₁ hin
    rw [show z + q = q + z by abel] at hout
    exact this hout
  have hne : dirIdx (q - z) ≠ dirIdx (p - z) := fun h =>
    hpq (by have := dirIdx_injective hw (isUnit_sub_comm hu) h; exact sub_left_inj.1 this)
  have hoff := arc_offDbl hJ₁.closed hJ₁.nodup hin hout (i := dirIdx (q - z)) (j := dirIdx (p - z))
    (Or.inl ⟨by rw [e2], by rw [show p + z - (z + z) = p - z by abel]⟩)
  have hb2 := (between_corners (dirIdx (q - z)) (dirIdx (p - z)) (dirIdx_even hw)
    (dirIdx_even (isUnit_sub_comm hu)) hne).2
  have e3 : leftPt (p + z) (z + z) = ringPt (z + z + (z + z)) (dirIdx (p - z) - 1) := by
    have := leftPt_in_eq (z + z) (z - p) hu
    rw [show z + z - (z - p) = p + z by abel, neg_sub] at this
    exact this
  rw [e3]
  exact hreach.trans (ringPt_reach_of_between _ _ _ hoff hb hb2)

/-- The quadruple of an adjacent face off `J₁` reaches the ring point in its direction. -/
theorem quad_reach_ringPt {J₁ : List Site} (hc : IsClosedWalk J₁) {z v : Site} (hv : IsUnit v)
    (h1 : z + z + v ∉ J₁) (h2 : z + v + (z + v) ∉ J₁) :
    Relation.ReflTransGen (OffAdj (dbl J₁)) (quad (z + v)) (ringPt (z + z + (z + z)) (dirIdx v)) := by
  have r1 := reach_double_of_notMem hc hv (z₁ := z + z + v) (v := v) h1
    (by rw [show z + z + v + v = z + v + (z + v) by abel]; exact h2)
  have r2 := reach_mid_of_notMem hc hv (z₁ := z + z) (v := v) h1
  rw [← mid_eq_ringPt (z + z) v hv]
  refine (Relation.ReflTransGen.trans ?_ r1).trans r2
  rw [show z + z + v + v + (z + z + v + v) = quad (z + v) by unfold quad; abel]

/-- The data of the contour argument.  `J₁` is a simple closed unit walk in the doubled
lattice containing the doubled path from the tail `τ` of the closed side `σ` to the tail `x` of
`E`; it leaves `2x` towards `x + q₀` and enters `2τ` from `p₀ + τ`, where `(τ, p₀)` is `σ`. -/
structure Ctx (f d : Site) (s : ExplState) (x : Site) (xs' : List Site) (e : Site × Site)
    (F₁ : List (Site × Site)) (Fs' : List (List (Site × Site))) (τ p₀ q₀ : Site) (l : List Site)
    (k : ℕ) (J₁ : List Site) : Prop where
  hd : IsUnit d
  hinv : ExplInv s
  hdfs : DFS0 f d s (x :: xs') ((e :: F₁) :: Fs')
  hout : ExplOuter s
  hact : s.active = e :: (F₁ ++ Fs'.flatten)
  hex : e.1 = x
  hl : ChainTo s (x :: xs') τ l
  hk : k < (x :: xs').length
  hlast : l.getLast? = some (x :: xs')[k]
  hτx : τ ≠ x
  hclosed : (τ, p₀, false) ∈ s.tested
  hJ₁ : IsSimpleClosed J₁
  hP : ∀ a b, (a, b) ∈ steps (pathP l (x :: xs') k) →
    (a + a, a + b) ∈ steps J₁ ∧ (a + b, b + b) ∈ steps J₁
  hbot : (x + x, x + q₀) ∈ steps J₁
  htop : (p₀ + τ, τ + τ) ∈ steps J₁
  hconv : ∀ p y, IsUnit (x - p) → IsUnit (y - x) → y ≠ q₀ →
    Between (dirIdx (e.2 - x)) (dirIdx (p - x)) (dirIdx (y - x)) →
    Between (dirIdx (q₀ - x)) (dirIdx (p - x)) (dirIdx (y - x))
  hq₀head : ∀ y, y ∉ s.visited → (x, y) ≠ e → y ≠ q₀
  hq₀par : ∀ par, (x :: xs')[1]? = some par → par ≠ q₀
  hV : ∀ q, q ∉ s.visited → q + q ∉ J₁
  hV2 : ∀ q q', q ∉ s.visited → q' ∉ s.visited → IsUnit (q' - q) → q + q' ∉ J₁
  hoffP : ∀ w, w ∉ pathP l (x :: xs') k → w + w ∉ J₁
  hmidP : ∀ z w, z ∈ pathP l (x :: xs') k → w ∉ pathP l (x :: xs') k → IsUnit (w - z) →
    (z, w) ≠ e → (z, w) ≠ (τ, p₀) → z + w ∉ J₁
  hoff2 : ∀ z w, z ∉ pathP l (x :: xs') k → w ∉ pathP l (x :: xs') k → IsUnit (w - z) →
    z + w ∉ J₁
  hNE : ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad e.2) (rightPt t.1 t.2)

end LatticeProb.Lattice.Planar
namespace LatticeProb.Lattice.Planar.Ctx

variable {f d : Site} {s : ExplState} {x : Site} {xs' : List Site} {e : Site × Site}

  {F₁ : List (Site × Site)} {Fs' : List (List (Site × Site))} {τ p₀ q₀ : Site} {l : List Site}

  {k : ℕ} {J₁ : List Site} (c : Ctx f d s x xs' e F₁ Fs' τ p₀ q₀ l k J₁)

include c

theorem he_active : e ∈ s.active := by rw [c.hact]; exact List.mem_cons_self

theorem hadjE : squareGraph.Adj x e.2 := by
  have := c.hinv.active_adj e c.he_active
  rwa [c.hex] at this

theorem hNEV : e.2 ∉ s.visited := c.hinv.active_head e c.he_active

theorem hNEout : ¬ InFiniteComponent s.visited e.2 := c.hout e c.he_active

theorem hTauVis : τ ∈ s.visited := c.hinv.tested_tail _ c.hclosed

theorem hnt : (τ, p₀, true) ∉ s.tested ∧ (p₀, τ, true) ∉ s.tested :=
  not_open_of_closed c.hinv c.hclosed

theorem hPV : ∀ y ∈ pathP l (x :: xs') k, y ∈ s.visited := by
  intro y hy
  rcases mem_pathP.1 hy with hy | hy
  · exact c.hl.visited y hy
  · exact c.hdfs.branch_visited y (List.mem_of_mem_take hy)

theorem notMem_P_of_notMem_visited {q : Site} (hq : q ∉ s.visited) :
    q ∉ pathP l (x :: xs') k :=
  fun h => hq (c.hPV q h)

theorem x_mem_P : x ∈ pathP l (x :: xs') k :=
  List.mem_of_mem_getLast? (pathP_getLast? c.hk c.hlast)

theorem junction_mem_P : (x :: xs')[k]'c.hk ∈ pathP l (x :: xs') k := by
  unfold pathP
  exact List.mem_append_left _ (List.mem_of_mem_getLast? c.hlast)

theorem tau_eq_of_mem_branch (h : τ ∈ x :: xs') : τ = (x :: xs')[k]'c.hk :=
  chain_mem_branch c.hl c.hk c.hlast τ (List.mem_of_mem_head? c.hl.head) h

/-- The tail of an edge of the head frame is the current face. -/
theorem head_frame_tail {g : Site × Site} (hg : g ∈ e :: F₁) : g.1 = x := by
  obtain ⟨pre, post, hfr, hsub, -⟩ := c.hdfs.head x (e :: F₁) rfl rfl
  have hmem : g ∈ frameOf f d (x :: xs')[1]? x := by
    rw [hfr]; exact List.mem_append_right _ (hsub.subset hg)
  have := frameOf_tail f d _ x g hmem
  rcases hp : (x :: xs')[1]? with _ | p
  · rw [hp] at this
    dsimp only at this
    rw [this]
    have hroot := c.hdfs.root
    rcases xs' with _ | ⟨p', xs''⟩
    · simpa using hroot.symm
    · simp at hp
  · rw [hp] at this; exact this

/-- The tail of an edge of a deeper frame is its branch vertex. -/
theorem deep_frame_tail {i : ℕ} {G : List (Site × Site)} (hG : Fs'[i]? = some G)
    {g : Site × Site} (hg : g ∈ G) {z : Site} (hz : (x :: xs')[i + 1]? = some z) : g.1 = z := by
  have hsub := c.hdfs.frame_sub (i + 1) z G hz (by simpa using hG)
  have hmem := hsub.subset hg
  have := frameOf_tail f d _ z g hmem
  rcases hp : (x :: xs')[i + 1 + 1]? with _ | p
  · rw [hp] at this
    dsimp only at this
    rw [this]
    have hroot := c.hdfs.root
    have hlen : (x :: xs').length = i + 2 := by
      have h1 := (List.getElem?_eq_some_iff.1 hz).1
      have h2 := List.getElem?_eq_none_iff.1 hp
      omega
    rw [List.getLast?_eq_getElem?, hlen, show i + 2 - 1 = i + 1 by omega, hz] at hroot
    simpa using hroot.symm
  · rw [hp] at this; exact this

theorem g_facts {g : Site × Site} (hg : g ∈ F₁ ++ Fs'.flatten) :
    g.2 ∉ s.visited ∧ ¬ InFiniteComponent s.visited g.2 ∧ squareGraph.Adj g.1 g.2 ∧ g ≠ e ∧
      g ≠ (τ, p₀) := by
  have hgact : g ∈ s.active := by rw [c.hact]; exact List.mem_cons_of_mem _ hg
  refine ⟨c.hinv.active_head g hgact, c.hout g hgact, c.hinv.active_adj g hgact, ?_, ?_⟩
  · rintro rfl
    have := c.hinv.active_nodup
    rw [c.hact, List.nodup_cons] at this
    exact this.1 hg
  · intro h
    exact c.hinv.active_tested g hgact _ c.hclosed (by rw [h])

/-- The general ending: a vertex `w ∉ P` adjacent to a path vertex `z` in the left arc, reached
from `quad y`. -/
theorem left_of_arc_reach {z p q w y : Site} (hin : (p + z, z + z) ∈ steps J₁)
    (hout : (z + z, z + q) ∈ steps J₁) (hz : z ∈ pathP l (x :: xs') k)
    (hw : w ∉ pathP l (x :: xs') k) (hadj : squareGraph.Adj z w) (hwe : (z, w) ≠ e)
    (hwτ : (z, w) ≠ (τ, p₀)) (hb : Between (dirIdx (q - z)) (dirIdx (p - z)) (dirIdx (w - z)))
    (hreach : Relation.ReflTransGen (OffAdj (dbl J₁)) (quad y) (quad w)) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad y) (leftPt t.1 t.2) := by
  have hv : IsUnit (w - z) := isUnit_of_adj hadj
  have hr := quad_reach_ringPt c.hJ₁.closed hv (z := z)
    (by rw [show z + z + (w - z) = z + w by abel]; exact c.hmidP z w hz hw hv hwe hwτ)
    (by rw [show z + (w - z) + (z + (w - z)) = w + w by abel]; exact c.hoffP w hw)
  rw [show z + (w - z) = w by abel] at hr
  exact ⟨(p + z, z + z), hin, left_of_arc c.hJ₁ hin hout hb (hreach.trans hr)⟩

/-- A head `y` adjacent to a path vertex `z` in the left arc. -/
theorem left_of_head {z p q y : Site} (hin : (p + z, z + z) ∈ steps J₁)
    (hout : (z + z, z + q) ∈ steps J₁) (hz : z ∈ pathP l (x :: xs') k) (hyV : y ∉ s.visited)
    (hadj : squareGraph.Adj z y) (hye : (z, y) ≠ e) (hyτ : (z, y) ≠ (τ, p₀))
    (hb : Between (dirIdx (q - z)) (dirIdx (p - z)) (dirIdx (y - z))) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad y) (leftPt t.1 t.2) :=
  c.left_of_arc_reach hin hout hz (c.notMem_P_of_notMem_visited hyV) hadj hye hyτ hb
    Relation.ReflTransGen.refl

theorem pred_unit {p : Site}
    (hp : (1 ≤ k ∧ (x :: xs')[1]? = some p) ∨ (k = 0 ∧ (x, p, true) ∈ s.tested)) :
    IsUnit (x - p) := by
  rcases hp with ⟨-, hp⟩ | ⟨-, hp⟩
  · have := c.hinv.tested_adj _ (c.hdfs.tree 0 x p rfl hp)
    simpa using isUnit_of_adj this
  · have := c.hinv.tested_adj _ hp
    exact isUnit_sub_comm (by simpa using isUnit_of_adj this)

/-- The head frame split at `E`. -/
theorem head_split : ∃ pre post : List (Site × Site),
    frameOf f d (x :: xs')[1]? x = pre ++ (x, e.2) :: post ∧ F₁ <+ post ∧
      ∀ w o, (x, w, o) ∈ s.tested → (x, w) ∈ pre := by
  obtain ⟨pre, post, hfr, hsub, hopen⟩ := c.hdfs.head x (e :: F₁) rfl rfl
  obtain ⟨q, post', hpost, hsub'⟩ := sublist_cons_split hsub
  have he : e = (x, e.2) := by rw [← c.hex]
  exact ⟨pre ++ q, post', by rw [hfr, hpost, he]; simp, hsub',
    fun w o hw => List.mem_append_left _ (hopen w o hw)⟩

/-- A head-frame edge after `E` lies strictly between `E` and the predecessor `p` of `x`. -/
theorem between_head {p y : Site}
    (hp : (1 ≤ k ∧ (x :: xs')[1]? = some p) ∨ (k = 0 ∧ (x, p, true) ∈ s.tested))
    {pre post : List (Site × Site)} (hfr : frameOf f d (x :: xs')[1]? x = pre ++ (x, e.2) :: post)
    (hopen : ∀ w o, (x, w, o) ∈ s.tested → (x, w) ∈ pre) (hy : (x, y) ∈ post) :
    Between (dirIdx (e.2 - x)) (dirIdx (p - x)) (dirIdx (y - x)) := by
  have hu := c.pred_unit hp
  rcases hp with ⟨-, hp⟩ | ⟨-, hp⟩
  · rw [hp] at hfr
    simp only [frameOf] at hfr
    exact between_of_after_child hu hfr hy
  · have hpre : (x, p) ∈ pre := hopen p true hp
    rcases hxs : (x :: xs')[1]? with _ | par
    · rw [hxs] at hfr
      simp only [frameOf] at hfr
      have hxf : x = f := by
        have hroot := c.hdfs.root
        rcases xs' with _ | ⟨p', xs''⟩
        · simpa using hroot
        · simp at hxs
      subst hxf
      exact between_root_of_before_after c.hd hfr hpre hy
    · rw [hxs] at hfr
      simp only [frameOf] at hfr
      have hpar : IsUnit (x - par) := by
        have := c.hdfs.tree 0 x par rfl hxs
        have := c.hinv.tested_adj _ this
        simpa using isUnit_of_adj this
      exact between_of_before_after hpar hfr hpre hy

/-- An active edge of the head frame other than `E`. -/
theorem other_left_head {g : Site × Site} (hg : g ∈ F₁) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (leftPt t.1 t.2) := by
  obtain ⟨hyV, -, hadjg, hge, hgτ⟩ := c.g_facts (List.mem_append_left _ hg)
  have hg1 : g.1 = x := c.head_frame_tail (List.mem_cons_of_mem _ hg)
  have hgx : (x, g.2) = g := by rw [← hg1]
  rw [hg1] at hadjg
  obtain ⟨p, hin, hp⟩ := pathP_pred c.hl c.hk c.hlast c.hτx
  obtain ⟨pre, post, hfr, hsub, hopen⟩ := c.head_split
  have hb0 := c.between_head hp hfr hopen (by rw [hgx]; exact hsub.subset hg)
  have hb := c.hconv p g.2 (c.pred_unit hp) (isUnit_of_adj hadjg)
    (c.hq₀head g.2 hyV (by rw [hgx]; exact hge)) hb0
  exact c.left_of_head (c.hP p x hin).2 c.hbot c.x_mem_P hyV hadjg (by rw [hgx]; exact hge)
    (by rw [hgx]; exact hgτ) hb

/-- An active edge at a branch vertex strictly below the junction. -/
theorem other_left_below {i : ℕ} {G : List (Site × Site)} (hG : Fs'[i]? = some G)
    {g : Site × Site} (hg : g ∈ G) (hik : i + 1 < k) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (leftPt t.1 t.2) := by
  have hgmem : g ∈ F₁ ++ Fs'.flatten :=
    List.mem_append_right _ (List.mem_flatten.2 ⟨G, List.mem_of_getElem? hG, hg⟩)
  obtain ⟨hyV, -, hadjg, hge, hgτ⟩ := c.g_facts hgmem
  have hk := c.hk
  have hz : (x :: xs')[i + 1]? = some (x :: xs')[i + 1] := List.getElem?_eq_getElem (by omega)
  have hz1 : g.1 = (x :: xs')[i + 1] := c.deep_frame_tail hG hg hz
  rw [hz1] at hadjg
  have hgz : ((x :: xs')[i + 1], g.2) = g := by rw [← hz1]
  have hc : (x :: xs')[i]? = some (x :: xs')[i] := List.getElem?_eq_getElem (by omega)
  have hpar : (x :: xs')[i + 2]? = some (x :: xs')[i + 2] := List.getElem?_eq_getElem (by omega)
  obtain ⟨pre, post, hfr, hsub, -⟩ := c.hdfs.after_child i _ _ G hz hc (by simpa using hG)
  rw [hpar] at hfr
  simp only [frameOf] at hfr
  have hu : IsUnit ((x :: xs')[i + 1] - (x :: xs')[i + 2]) := by
    have := c.hdfs.tree (i + 1) _ _ hz hpar
    have := c.hinv.tested_adj _ this
    simpa using isUnit_of_adj this
  have hb := between_of_after_child hu hfr (by rw [hgz]; exact hsub.subset hg)
  have hin : ((x :: xs')[i + 2] + (x :: xs')[i + 1], (x :: xs')[i + 1] + (x :: xs')[i + 1]) ∈
      steps J₁ := by
    rcases Nat.lt_or_ge (i + 2) k with h | h
    · exact (c.hP _ _ (pathP_step_seg (l := l) (xs := x :: xs') (k := k) hk.le (j := i + 1) h)).2
    · have hk2 : k = i + 2 := by omega
      subst hk2
      have := pathP_step_junction (l := l) (xs := x :: xs') (k := i + 2) hk (by omega) c.hlast
      simpa using (c.hP _ _ this).2
  have hout := (c.hP _ _ (pathP_step_seg (l := l) (xs := x :: xs') (k := k) hk.le (j := i) hik)).1
  exact c.left_of_head hin hout (branch_mem_pathP (by omega) (by omega)) hyV hadjg
    (by rw [hgz]; exact hge) (by rw [hgz]; exact hgτ) hb

/-- The predecessor of the junction on `J₁`, and its position before the child. -/
theorem junction_pred_pre {child : Site} {pre : List (Site × Site)}
    (htest : ∀ w o, ((x :: xs')[k]'c.hk, w, o) ∈ s.tested → (o = true ∧ w = child) ∨
      ((x :: xs')[k]'c.hk, w) ∈ pre) (hchild : child ∈ x :: xs') :
    ∃ c₀, (c₀ + (x :: xs')[k]'c.hk, (x :: xs')[k]'c.hk + (x :: xs')[k]'c.hk) ∈ steps J₁ ∧
      ((x :: xs')[k]'c.hk, c₀) ∈ pre := by
  rcases pathP_junction_pred c.hl c.hk c.hlast with ⟨c₀, hin, ht, hc₀x⟩ | hτ
  · refine ⟨c₀, (c.hP _ _ hin).2, ?_⟩
    rcases htest c₀ true ht with ⟨-, hcc⟩ | hpre
    · exact absurd (hcc ▸ hchild) hc₀x
    · exact hpre
  · refine ⟨p₀, by rw [hτ]; exact c.htop, ?_⟩
    rcases htest p₀ false (by rw [hτ]; exact c.hclosed) with ⟨h, -⟩ | hpre
    · simp at h
    · exact hpre

/-- An active edge at the junction. -/
theorem other_left_junction {i : ℕ} {G : List (Site × Site)} (hG : Fs'[i]? = some G)
    {g : Site × Site} (hg : g ∈ G) (hik : i + 1 = k) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (leftPt t.1 t.2) := by
  have hgmem : g ∈ F₁ ++ Fs'.flatten :=
    List.mem_append_right _ (List.mem_flatten.2 ⟨G, List.mem_of_getElem? hG, hg⟩)
  obtain ⟨hyV, -, hadjg, hge, hgτ⟩ := c.g_facts hgmem
  have hk := c.hk
  have hlast := c.hlast
  subst hik
  have hz : (x :: xs')[i + 1]? = some (x :: xs')[i + 1] := List.getElem?_eq_getElem hk
  have hz1 : g.1 = (x :: xs')[i + 1] := c.deep_frame_tail hG hg hz
  rw [hz1] at hadjg
  have hgz : ((x :: xs')[i + 1], g.2) = g := by rw [← hz1]
  have hc : (x :: xs')[i]? = some (x :: xs')[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨pre, post, hfr, hsub, htest⟩ := c.hdfs.after_child i _ _ G hz hc (by simpa using hG)
  have hgpost : g ∈ post := hsub.subset hg
  have hout : ((x :: xs')[i + 1] + (x :: xs')[i + 1], (x :: xs')[i + 1] + (x :: xs')[i]) ∈
      steps J₁ := by
    have := pathP_step_junction (l := l) (xs := x :: xs') (k := i + 1) hk (by omega) hlast
    simpa using (c.hP _ _ this).1
  obtain ⟨c₀, hin, hpre⟩ := c.junction_pred_pre htest (List.getElem_mem _)
  have hb : Between (dirIdx ((x :: xs')[i] - (x :: xs')[i + 1]))
      (dirIdx (c₀ - (x :: xs')[i + 1])) (dirIdx (g.2 - (x :: xs')[i + 1])) := by
    rcases hpar : (x :: xs')[i + 1 + 1]? with _ | par
    · rw [hpar] at hfr
      simp only [frameOf] at hfr
      have hlen : (x :: xs').length = i + 2 := by
        have h2 := List.getElem?_eq_none_iff.1 hpar
        omega
      have hxf : (x :: xs')[i + 1] = f := by
        have hroot := c.hdfs.root
        rw [List.getLast?_eq_getElem?, hlen, show i + 2 - 1 = i + 1 by omega, hz] at hroot
        simpa using hroot
      rw [hxf] at hfr hpre hgz ⊢
      exact between_root_of_before_after c.hd hfr hpre (by rw [hgz]; exact hgpost)
    · rw [hpar] at hfr
      simp only [frameOf] at hfr
      have hu : IsUnit ((x :: xs')[i + 1] - par) := by
        have := c.hdfs.tree (i + 1) _ _ hz hpar
        have := c.hinv.tested_adj _ this
        simpa using isUnit_of_adj this
      exact between_of_before_after hu hfr hpre (by rw [hgz]; exact hgpost)
  exact c.left_of_head hin hout c.junction_mem_P hyV hadjg (by rw [hgz]; exact hge)
    (by rw [hgz]; exact hgτ) hb

/-- At the junction, the parent direction lies in the left arc. -/
theorem junction_left {par : Site} (hpar : (x :: xs')[k + 1]? = some par) :
    ∃ p q, (p + (x :: xs')[k]'c.hk, (x :: xs')[k]'c.hk + (x :: xs')[k]'c.hk) ∈ steps J₁ ∧
      ((x :: xs')[k]'c.hk + (x :: xs')[k]'c.hk, (x :: xs')[k]'c.hk + q) ∈ steps J₁ ∧
      Between (dirIdx (q - (x :: xs')[k]'c.hk)) (dirIdx (p - (x :: xs')[k]'c.hk))
        (dirIdx (par - (x :: xs')[k]'c.hk)) := by
  have hk := c.hk
  have hlast := c.hlast
  have hu : IsUnit ((x :: xs')[k] - par) := by
    have := c.hdfs.tree k _ _ (List.getElem?_eq_getElem hk) hpar
    have := c.hinv.tested_adj _ this
    simpa using isUnit_of_adj this
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    simp only [List.getElem_cons_zero] at hlast hu ⊢
    have hpar' : (x :: xs')[1]? = some par := hpar
    obtain ⟨p, hin, hp⟩ := pathP_pred c.hl hk hlast c.hτx
    rcases hp with ⟨hk1, -⟩ | ⟨-, hp⟩
    · omega
    obtain ⟨pre, post, hfr, -, hopen⟩ := c.head_split
    rw [hpar'] at hfr
    simp only [frameOf] at hfr
    have hpre : (x, p) ∈ pre := hopen p true hp
    have hup : IsUnit (x - p) := c.pred_unit (Or.inr ⟨rfl, hp⟩)
    have hb0 := between_parent_of_before hu hfr hpre
    have hvpar : IsUnit (par - x) := isUnit_sub_comm hu
    exact ⟨p, q₀, (c.hP p x hin).2, c.hbot, c.hconv p par hup hvpar (c.hq₀par par hpar') hb0⟩
  · have hout := (c.hP _ _ (pathP_step_junction (l := l) (xs := x :: xs') hk hk0 hlast)).1
    have hz : (x :: xs')[k - 1 + 1]? = some (x :: xs')[k] := by
      rw [show k - 1 + 1 = k by omega]; exact List.getElem?_eq_getElem hk
    have hc : (x :: xs')[k - 1]? = some (x :: xs')[k - 1] := List.getElem?_eq_getElem (by omega)
    have hlenF := c.hdfs.len
    simp only [List.length_cons] at hlenF
    have hk' : k < xs'.length + 1 := by simpa using hk
    have hFb : k - 1 < Fs'.length := by omega
    have hF : Fs'[k - 1]? = some (Fs'[k - 1]'hFb) := List.getElem?_eq_getElem hFb
    obtain ⟨pre, post, hfr, -, htest⟩ := c.hdfs.after_child (k - 1) _ _ (Fs'[k - 1]'hFb) hz hc
      (by rw [List.getElem?_cons_succ]; exact hF)
    rw [show k - 1 + 2 = k + 1 by omega, hpar] at hfr
    simp only [frameOf] at hfr
    obtain ⟨c₀, hin, hpre⟩ := c.junction_pred_pre htest (List.getElem_mem _)
    exact ⟨c₀, _, hin, hout, between_parent_of_before hu hfr hpre⟩

/-- Branch vertices strictly above the junction are connected to the first one above it. -/
theorem descend_branch : ∀ n z', (x :: xs')[k + 1 + n]? = some z' →
    k + 1 + n < (x :: xs').length →
    Relation.ReflTransGen (OffAdj (dbl J₁)) (quad z') (quad ((x :: xs')[k + 1]?.getD x)) := by
  have hk := c.hk
  have hlast := c.hlast
  intro n
  induction n with
  | zero =>
    intro z' hz' _
    simp only [Nat.add_zero] at hz'
    rw [hz']
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro z' hz' hlt
    have hz'' : (x :: xs')[k + 1 + n]? = some (x :: xs')[k + 1 + n] :=
      List.getElem?_eq_getElem (by omega)
    have htree := c.hdfs.tree (k + 1 + n) _ z' hz'' (by
      rw [show k + 1 + n + 1 = k + 1 + (n + 1) by omega]; exact hz')
    have hu : IsUnit ((x :: xs')[k + 1 + n] - z') := by
      have := c.hinv.tested_adj _ htree
      simpa using isUnit_of_adj this
    obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.1 hz'
    have h1 : (x :: xs')[k + 1 + (n + 1)] ∉ pathP l (x :: xs') k :=
      branch_notMem_pathP c.hdfs c.hl hk hlast hb (by omega)
    have h2 : (x :: xs')[k + 1 + n] ∉ pathP l (x :: xs') k :=
      branch_notMem_pathP c.hdfs c.hl hk hlast (by omega) (by omega)
    exact (faceStep_reach c.hJ₁.closed hu (c.hoffP _ h1) (c.hoff2 _ _ h1 h2 hu)
      (c.hoffP _ h2)).trans (ih _ hz'' (by omega))

/-- An active edge at a branch vertex strictly above the junction. -/
theorem other_left_above {i : ℕ} {G : List (Site × Site)} (hG : Fs'[i]? = some G)
    {g : Site × Site} (hg : g ∈ G) (hik : k < i + 1) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (leftPt t.1 t.2) := by
  have hgmem : g ∈ F₁ ++ Fs'.flatten :=
    List.mem_append_right _ (List.mem_flatten.2 ⟨G, List.mem_of_getElem? hG, hg⟩)
  obtain ⟨hyV, -, hadjg, -, -⟩ := c.g_facts hgmem
  have hk := c.hk
  have hlast := c.hlast
  have hlenF := c.hdfs.len
  simp only [List.length_cons] at hlenF
  have hi := (List.getElem?_eq_some_iff.1 hG).1
  have hlen : i + 1 < (x :: xs').length := by simp only [List.length_cons] at hlenF ⊢; omega
  have hz : (x :: xs')[i + 1]? = some (x :: xs')[i + 1] := List.getElem?_eq_getElem hlen
  have hz1 : g.1 = (x :: xs')[i + 1] := c.deep_frame_tail hG hg hz
  rw [hz1] at hadjg
  have hzP : (x :: xs')[i + 1] ∉ pathP l (x :: xs') k :=
    branch_notMem_pathP c.hdfs c.hl hk hlast hlen hik
  have hyP : g.2 ∉ pathP l (x :: xs') k := c.notMem_P_of_notMem_visited hyV
  have hu : IsUnit ((x :: xs')[i + 1] - g.2) := isUnit_sub_comm (isUnit_of_adj hadjg)
  have r1 : Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (quad (x :: xs')[i + 1]) :=
    faceStep_reach c.hJ₁.closed hu (c.hV _ hyV) (c.hoff2 _ _ hyP hzP hu) (c.hoffP _ hzP)
  have hpar : (x :: xs')[k + 1]? = some (x :: xs')[k + 1] := List.getElem?_eq_getElem (by omega)
  have r2 := c.descend_branch (i - k) _ (by rw [show k + 1 + (i - k) = i + 1 by omega]; exact hz)
    (by omega)
  rw [hpar] at r2
  simp only [Option.getD_some] at r2
  have hparP : (x :: xs')[k + 1] ∉ pathP l (x :: xs') k :=
    branch_notMem_pathP c.hdfs c.hl hk hlast (by omega) (by omega)
  have htree := c.hdfs.tree k _ _ (List.getElem?_eq_getElem hk) hpar
  have hadjpar : squareGraph.Adj (x :: xs')[k] (x :: xs')[k + 1] :=
    (c.hinv.tested_adj _ htree).symm
  have hne_e : ((x :: xs')[k], (x :: xs')[k + 1]) ≠ e := by
    intro h
    have h2 : (x :: xs')[k + 1] = e.2 := by rw [← h]
    exact c.hNEV (h2 ▸ c.hdfs.branch_visited _ (List.getElem_mem _))
  have hne_τ : ((x :: xs')[k], (x :: xs')[k + 1]) ≠ (τ, p₀) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2] at htree
    exact c.hnt.2 htree
  obtain ⟨p, q, hin, hout, hb⟩ := c.junction_left hpar
  exact c.left_of_arc_reach hin hout c.junction_mem_P hparP hadjpar hne_e hne_τ hb (r1.trans r2)

/-- Every active head other than `E`'s is connected to a left point. -/
theorem other_left {g : Site × Site} (hg : g ∈ F₁ ++ Fs'.flatten) :
    ∃ t ∈ steps J₁, Relation.ReflTransGen (OffAdj (dbl J₁)) (quad g.2) (leftPt t.1 t.2) := by
  rcases List.mem_append.1 hg with hg | hg
  · exact c.other_left_head hg
  · obtain ⟨G, hG, hgG⟩ := List.mem_flatten.1 hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hG
    have hG' : Fs'[i]? = some Fs'[i] := List.getElem?_eq_getElem hi
    rcases lt_trichotomy (i + 1) k with h | h | h
    · exact c.other_left_below hG' hgG h
    · exact c.other_left_junction hG' hgG h
    · exact c.other_left_above hG' hgG h

/-- The active list is `[E]`. -/
theorem active_eq : s.active = [e] := by
  rw [c.hact]
  rcases hF : F₁ ++ Fs'.flatten with _ | ⟨g, rest⟩
  · rfl
  · exfalso
    have hg : g ∈ F₁ ++ Fs'.flatten := by rw [hF]; exact List.mem_cons_self
    obtain ⟨hyV, hyout, -, -, -⟩ := c.g_facts hg
    obtain ⟨t, ht, hNE⟩ := c.hNE
    obtain ⟨t', ht', hy⟩ := c.other_left hg
    exact separation c.hJ₁ c.hV c.hV2 ht ht' hNE hy c.hNEV hyV c.hNEout hyout

end LatticeProb.Lattice.Planar.Ctx
namespace LatticeProb.Lattice.Planar

end LatticeProb.Lattice.Planar
