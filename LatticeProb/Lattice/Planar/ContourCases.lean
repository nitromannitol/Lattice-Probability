/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ContourCtx

open Finset List Fin.NatCast

namespace LatticeProb.Lattice.Planar

section SCase

variable {f d : Site} {s : ExplState} {x : Site} {xs' : List Site} {e : Site × Site}

  {F₁ : List (Site × Site)} {Fs' : List (List (Site × Site))} {SW : Site} {l : List Site} {k : ℕ}

/-- The contour context of the `S` case: `J₁ = dbl J` with `J` the closed dual curve. -/
theorem ctxS (hd : IsUnit d) (hinv : ExplInv s) (hdfs : DFS0 f d s (x :: xs') ((e :: F₁) :: Fs'))
    (hout : ExplOuter s) (hact : s.active = e :: (F₁ ++ Fs'.flatten)) (hex : e.1 = x)
    (hl : ChainTo s (x :: xs') SW l) (hk : k < (x :: xs').length)
    (hlast : l.getLast? = some (x :: xs')[k]) (hSclosed : (SW, x, false) ∈ s.tested)
    (hdir : e.2 - x = rotR (SW - x)) :
    Ctx f d s x xs' e F₁ Fs' SW x SW l k (dbl (curveS l (x :: xs') k SW)) := by
  have hadjS : squareGraph.Adj SW x := by
    have := hinv.tested_adj _ hSclosed
    simpa using this
  have hne : SW ≠ x := hadjS.ne
  have hnt := not_open_of_closed hinv hSclosed
  have hJ : IsSimpleClosed (curveS l (x :: xs') k SW) :=
    ⟨curveS_closed hinv hdfs hl hk hlast hadjS.symm, curveS_tail_nodup hdfs hl hk hlast,
      curveS_three hdfs hl hk hlast hne hnt.1 hnt.2⟩
  have hJ₁ : IsSimpleClosed (dbl (curveS l (x :: xs') k SW)) := isSimpleClosed_dbl hJ
  have hJV : ∀ y ∈ curveS l (x :: xs') k SW, y ∈ s.visited :=
    curveS_subset_visited hl hdfs.branch_visited (hinv.tested_tail _ hSclosed)
  have hSWP : SW ∈ pathP l (x :: xs') k := List.mem_of_mem_head? (pathP_head? hl k)
  have hmemP : ∀ w, w ∈ curveS l (x :: xs') k SW → w ∈ pathP l (x :: xs') k := by
    intro w hw
    rw [curveS_eq_pathP, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hw
    · exact hSWP
  have he_active : e ∈ s.active := by rw [hact]; exact List.mem_cons_self
  have hNEV : e.2 ∉ s.visited := hinv.active_head e he_active
  have hadjE : squareGraph.Adj x e.2 := by
    have := hinv.active_adj e he_active
    rwa [hex] at this
  have hlast_step : (x, SW) ∈ steps (curveS l (x :: xs') k SW) := curveS_last_step hk hlast
  have hV : ∀ q, q ∉ s.visited → q + q ∉ dbl (curveS l (x :: xs') k SW) :=
    fun q hq hm => hq (hJV q (mem_of_double_mem_dbl hJ.closed hm))
  have hmid : ∀ z w, w ∉ pathP l (x :: xs') k → IsUnit (w - z) →
      z + w ∉ dbl (curveS l (x :: xs') k SW) := by
    intro z w hw hu hm
    rw [show z + w = z + z + (w - z) by abel] at hm
    rcases (mid_mem_dbl_iff hJ.closed hu).1 hm with hs | hs
    · exact hw (hmemP w (by rw [show z + (w - z) = w by abel] at hs; exact (mem_steps hs).2))
    · exact hw (hmemP w (by rw [show z + (w - z) = w by abel] at hs; exact (mem_steps hs).1))
  have hw : IsUnit (SW - x) := isUnit_of_adj hadjS.symm
  -- `NE` is connected to a right point
  have hNE : ∃ t ∈ steps (dbl (curveS l (x :: xs') k SW)),
      Relation.ReflTransGen (OffAdj (dbl (dbl (curveS l (x :: xs') k SW)))) (quad e.2)
        (rightPt t.1 t.2) := by
    obtain ⟨p, hin, -⟩ := curveS_pred hl hk hlast hne
    have hout := hlast_step
    have hpV : p ∈ s.visited := hJV p (mem_steps hin).1
    have hpNE : p ≠ e.2 := fun h => hNEV (h ▸ hpV)
    have hpSW : p ≠ SW := by
      rintro rfl
      exact rev_notMem_steps' hJ hout hin
    have hin₁ : (p + x, x + x) ∈ steps (dbl (curveS l (x :: xs') k SW)) :=
      mem_steps_dbl.2 ⟨(p, x), hin, Or.inr rfl⟩
    have hout₁ : (x + x, x + SW) ∈ steps (dbl (curveS l (x :: xs') k SW)) :=
      mem_steps_dbl.2 ⟨(x, SW), hout, Or.inl rfl⟩
    have hu : IsUnit (x - p) := by have := steps_unit hJ.closed hin; simpa using this
    have hdiru : IsUnit (e.2 - x) := isUnit_of_adj hadjE
    have hb1 : Between (dirIdx (-(x - p))) (dirIdx (SW - x)) (dirIdx (e.2 - x)) := by
      rw [hdir]
      refine between_rotR hu hw ?_ ?_
      · intro h
        rw [neg_sub] at h
        exact hpSW (sub_right_injective h)
      · intro h
        apply hpNE
        have h' : rotL (SW - x) = -(e.2 - x) := by
          rw [hdir]
          rcases hw with h | h | h | h <;> rw [h] <;> simp [rotL, rotR]
        rw [h', neg_sub] at h
        exact sub_right_injective h
    have hne' : dirIdx (-(x - p)) ≠ dirIdx (SW - x) := by
      intro h
      apply hpSW
      have := dirIdx_injective (isUnit_neg hu) hw h
      rw [neg_sub] at this
      exact sub_left_injective this
    have hb2 := (between_corners (dirIdx (-(x - p))) (dirIdx (SW - x))
      (dirIdx_even (isUnit_neg hu)) (dirIdx_even hw) hne').1
    have hoff := arc_offDbl hJ₁.closed hJ₁.nodup hin₁ hout₁ (i := dirIdx (-(x - p)))
      (j := dirIdx (SW - x)) (Or.inr ⟨by rw [show p + x - (x + x) = -(x - p) by abel],
        by rw [show x + SW - (x + x) = SW - x by abel]⟩)
    refine ⟨(p + x, x + x), hin₁, ?_⟩
    have e3 : rightPt (p + x) (x + x) = ringPt (x + x + (x + x)) (dirIdx (-(x - p)) + 1) := by
      have := rightPt_in_eq (x + x) (x - p) hu
      rw [show x + x - (x - p) = p + x by abel] at this
      exact this
    rw [e3]
    have hreach := quad_reach_ringPt hJ₁.closed hdiru (z := x)
      (mid_notMem_dbl_of_notMem hJ.closed hdiru (by
        rw [show x + (e.2 - x) = e.2 by abel]; exact fun h => hNEV (hJV _ h)))
      (by rw [show x + (e.2 - x) = e.2 by abel]; exact hV e.2 hNEV)
    rw [show x + (e.2 - x) = e.2 by abel] at hreach
    exact hreach.trans (ringPt_reach_of_between _ _ _ hoff hb1 hb2)
  refine ⟨hd, hinv, hdfs, hout, hact, hex, hl, hk, hlast, hne, hSclosed, hJ₁, ?_, ?_, ?_, ?_, ?_,
    ?_, hV, ?_, ?_, ?_, ?_, hNE⟩
  · intro a b hab
    have hab' := steps_curveS_of_steps_pathP (SW := SW) hab
    exact ⟨mem_steps_dbl.2 ⟨(a, b), hab', Or.inl rfl⟩, mem_steps_dbl.2 ⟨(a, b), hab', Or.inr rfl⟩⟩
  · exact mem_steps_dbl.2 ⟨(x, SW), hlast_step, Or.inl rfl⟩
  · exact mem_steps_dbl.2 ⟨(x, SW), hlast_step, Or.inr rfl⟩
  · intro p y hu hvy hySW hb0
    rw [hdir] at hb0
    have hvw : y - x ≠ SW - x := fun h => hySW (sub_left_injective h)
    have := between_of_between_rotR hu hw hvy (by rw [neg_sub]; exact hb0) hvw
    rwa [neg_sub] at this
  · intro y hyV _ h
    exact hyV (h ▸ hinv.tested_tail _ hSclosed)
  · intro par hpar h
    rw [h] at hpar
    exact hnt.1 (hdfs.tree 0 x SW rfl hpar)
  · intro q q' hq hq' hu hm
    rw [show q + q' = q + q + (q' - q) by abel] at hm
    rcases (mid_mem_dbl_iff hJ.closed hu).1 hm with hs | hs
    · exact hq (hJV q (mem_steps hs).1)
    · exact hq (hJV q (mem_steps hs).2)
  · intro w hw hm
    exact hw (hmemP w (mem_of_double_mem_dbl hJ.closed hm))
  · intro z w _ hw hu _ _
    exact hmid z w hw hu
  · intro z w _ hw hu
    exact hmid z w hw hu

end SCase

theorem active_list_S (f : Site) {d : Site} (hd : IsUnit d) (ρ : Config squareGraph) (n : ℕ)
    {e : Site × Site} {rest : List (Site × Site)} (he : (explore ρ f d n).active = e :: rest)
    (hS : TestedAs (explore ρ f d n).tested (sideS e.1 e.2) false) : rest = [] := by
  have hinv := explInv_explore ρ f hd n
  obtain ⟨xs, Fs, hdfs⟩ := dfs_explore ρ f hd n
  have hout := explOuter_explore ρ f hd n
  obtain ⟨x, xs', F₁, Fs', rfl, rfl, hrest, hex⟩ := dfs_head_shape hdfs he
  have hadjE : squareGraph.Adj e.1 e.2 :=
    hinv.active_adj e (by rw [he]; exact List.mem_cons_self)
  have hS' : ((sideS e.1 e.2).1, (sideS e.1 e.2).2, false) ∈ (explore ρ f d n).tested := hS
  rw [sideS_fst, sideS_snd, rightFace_primal hadjE] at hS'
  have hdir : e.2 - e.1 =
      rotR (rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 1) - e.1) := by
    have := corner_NE_sub_SE (primalTail e.1 e.2) (primalDir e.1 e.2)
    rwa [rightFace_primal hadjE, leftFace_primal hadjE] at this
  have hnd : (explore ρ f d n).tested.Nodup := hinv.tested_nodup.of_map _
  rw [hex] at hS' hdir
  have hSWvis : rightFace (primalTail x e.2) (primalDir x e.2 + 1) ∈ (explore ρ f d n).visited :=
    hinv.tested_tail _ hS'
  obtain ⟨l, hl⟩ := exists_chainTo hdfs.toDFS0 hnd hSWvis
  obtain ⟨y, hy⟩ : ∃ y, l.getLast? = some y := by
    rcases hl' : l.getLast? with _ | y
    · exact absurd (List.getLast?_eq_none_iff.1 hl') (chain_ne_nil hl)
    · exact ⟨y, rfl⟩
  obtain ⟨k, hk, hxk⟩ := List.getElem_of_mem (hl.last_mem y hy)
  rw [← hxk] at hy
  have c := ctxS hd hinv hdfs.toDFS0 hout (by rw [he, hrest]) hex hl hk hy hS' hdir
  have := c.active_eq
  rw [he] at this
  simpa using this

theorem rotR_rotL (u : Site) : rotR (rotL u) = u := by
  obtain ⟨a, b⟩ := u; simp [rotL, rotR]

theorem rotL_rotR (u : Site) : rotL (rotR u) = u := by
  obtain ⟨a, b⟩ := u; simp [rotL, rotR]

theorem double_ne_double_add_unit {n : Site} (hn : IsUnit n) (a z : Site) : a + a ≠ z + z + n := by
  intro h
  obtain ⟨a1, a2⟩ := a; obtain ⟨z1, z2⟩ := z
  rcases hn with rfl | rfl | rfl | rfl <;> simp only [Prod.mk_add_mk, Prod.mk.injEq] at h <;> omega

theorem double_ne_oddodd {n : Site} (hn : IsUnit n) (a z : Site) :
    a + a ≠ z + z + (n + rotL n) := by
  intro h
  obtain ⟨a1, a2⟩ := a; obtain ⟨z1, z2⟩ := z
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [rotL, Prod.mk_add_mk, Prod.mk.injEq] at h <;> omega

theorem mid_ne_oddodd {u n : Site} (hu : IsUnit u) (hn : IsUnit n) (a z : Site) :
    a + a + u ≠ z + z + (n + rotL n) := by
  intro h
  obtain ⟨a1, a2⟩ := a; obtain ⟨z1, z2⟩ := z
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [rotL, Prod.mk_add_mk, Prod.mk.injEq] at h <;> omega

theorem mid_ne_double {u : Site} (hu : IsUnit u) (a z : Site) : a + a + u ≠ z + z := by
  intro h
  obtain ⟨a1, a2⟩ := a; obtain ⟨z1, z2⟩ := z
  rcases hu with rfl | rfl | rfl | rfl <;> simp only [Prod.mk_add_mk, Prod.mk.injEq] at h <;> omega

theorem double_inj {a b : Site} (h : a + a = b + b) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at h ⊢
  omega

theorem oddodd_coords {n : Site} (hn : IsUnit n) (z : Site) :
    Odd (z + z + (n + rotL n)).1 ∧ Odd (z + z + (n + rotL n)).2 := by
  obtain ⟨z1, z2⟩ := z
  rcases hn with rfl | rfl | rfl | rfl <;> simp only [rotL, Prod.mk_add_mk, Int.odd_iff] <;> omega

theorem unit_add_rotL_ne_zero {n : Site} (hn : IsUnit n) : n + rotL n ≠ 0 := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide

/-- The chord through the square from `2x` to `2NW`: the `E`-midpoint, the centre, the
`W`-midpoint, then `2NW`; here `NE = x + n`, `SW = x + rotL n`, `NW = x + n + rotL n`. -/
def chordW (x n : Site) : List Site :=
  [x + (x + n), x + (x + n + rotL n), (x + rotL n) + (x + n + rotL n),
    (x + n + rotL n) + (x + n + rotL n)]

/-- The closed curve of the `W` case in the doubled lattice. -/
def curveW (l xs : List Site) (k : ℕ) (x n : Site) : List Site :=
  dbl (pathP l xs k) ++ chordW x n

theorem chordW_isChain {n : Site} (hn : IsUnit n) (x : Site) :
    (chordW x n).IsChain (fun a b => IsUnit (b - a)) := by
  have hrot := isUnit_rotL hn
  simp only [chordW, List.isChain_cons_cons, List.isChain_singleton, and_true]
  refine ⟨?_, ?_, ?_⟩
  · convert hrot using 1; abel
  · convert hrot using 1; abel
  · convert hn using 1; abel

theorem chordW_nodup {n : Site} (hn : IsUnit n) (x : Site) : (chordW x n).Nodup := by
  obtain ⟨x1, x2⟩ := x
  rcases hn with rfl | rfl | rfl | rfl <;> simp [chordW, rotL, Prod.ext_iff] <;> omega

theorem mem_chordW {n x q : Site} : q ∈ chordW x n ↔
    q = x + (x + n) ∨ q = x + (x + n + rotL n) ∨ q = (x + rotL n) + (x + n + rotL n) ∨
      q = (x + n + rotL n) + (x + n + rotL n) := by
  simp [chordW]

section WCase

variable {f d : Site} {s : ExplState} {x : Site} {xs' : List Site} {e : Site × Site}

  {F₁ : List (Site × Site)} {Fs' : List (List (Site × Site))} {n : Site} {l : List Site} {k : ℕ}

/-- The contour context of the `W` case. -/
theorem ctxW (hd : IsUnit d) (hinv : ExplInv s) (hdfs : DFS0 f d s (x :: xs') ((e :: F₁) :: Fs'))
    (hout : ExplOuter s) (hact : s.active = e :: (F₁ ++ Fs'.flatten)) (hex : e.1 = x)
    (hn : IsUnit n) (hNE : e.2 = x + n) (hl : ChainTo s (x :: xs') (x + n + rotL n) l)
    (hk : k < (x :: xs').length) (hlast : l.getLast? = some (x :: xs')[k])
    (hWclosed : (x + n + rotL n, x + rotL n, false) ∈ s.tested) :
    Ctx f d s x xs' e F₁ Fs' (x + n + rotL n) (x + rotL n) (x + n) l k
      (curveW l (x :: xs') k x n) := by
  have hrot : IsUnit (rotL n) := isUnit_rotL hn
  have hτx : x + n + rotL n ≠ x := by
    intro h
    apply unit_add_rotL_ne_zero hn
    have : x + n + rotL n - x = 0 := by rw [h]; abel
    rw [← this]; abel
  have hnt := not_open_of_closed hinv hWclosed
  have hPch := pathP_isChain hinv hdfs hl hk hlast
  have hPnd := pathP_nodup hdfs hl hk hlast
  have hPne := pathP_ne_nil hl k
  have hdblne : dbl (pathP l (x :: xs') k) ≠ [] := dbl_ne_nil hPne
  have hhead : (dbl (pathP l (x :: xs') k)).head? = some ((x + n + rotL n) + (x + n + rotL n)) := by
    rw [dbl_head?, pathP_head? hl k]; rfl
  have hlastd : (dbl (pathP l (x :: xs') k)).getLast? = some (x + x) := by
    rw [dbl_getLast?, pathP_getLast? hk hlast]; rfl
  have hPV : ∀ y ∈ pathP l (x :: xs') k, y ∈ s.visited := by
    intro y hy
    rcases mem_pathP.1 hy with hy | hy
    · exact hl.visited y hy
    · exact hdfs.branch_visited y (List.mem_of_mem_take hy)
  have he_active : e ∈ s.active := by rw [hact]; exact List.mem_cons_self
  have hNEV : e.2 ∉ s.visited := hinv.active_head e he_active
  have hxvis : x ∈ s.visited := by
    have := hinv.active_tail e he_active
    rwa [hex] at this
  have hNEP : x + n ∉ pathP l (x :: xs') k := fun h => hNEV (hNE ▸ hPV _ h)
  have hxP : x ∈ pathP l (x :: xs') k := List.mem_of_mem_getLast? (pathP_getLast? hk hlast)
  have hNWP : x + n + rotL n ∈ pathP l (x :: xs') k := List.mem_of_mem_head? (pathP_head? hl k)
  have hNWvis : x + n + rotL n ∈ s.visited := hinv.tested_tail _ hWclosed
  have hst : ∀ a b, (a, b) ∈ steps (pathP l (x :: xs') k) →
      (a, b, true) ∈ s.tested ∨ (b, a, true) ∈ s.tested :=
    fun a b h => pathP_step_tested hdfs hl hk hlast h
  -- the chord points off the doubled path
  have c1 : x + (x + n) ∉ dbl (pathP l (x :: xs') k) := by
    intro hm
    rw [show x + (x + n) = x + x + n by abel] at hm
    rcases (mid_mem_dbl_iff' hPch hn).1 hm with hs | hs
    · exact hNEP (mem_steps hs).2
    · exact hNEP (mem_steps hs).1
  have c2 : x + (x + n + rotL n) ∉ dbl (pathP l (x :: xs') k) := by
    rw [show x + (x + n + rotL n) = x + x + (n + rotL n) by abel]
    exact oddodd_notMem_dbl' hPch (oddodd_coords hn x).1 (oddodd_coords hn x).2
  have c3 : (x + rotL n) + (x + n + rotL n) ∉ dbl (pathP l (x :: xs') k) := by
    intro hm
    rw [show (x + rotL n) + (x + n + rotL n) = (x + rotL n) + (x + rotL n) + n by abel] at hm
    rcases (mid_mem_dbl_iff' hPch hn).1 hm with hs | hs
    · rw [show x + rotL n + n = x + n + rotL n by abel] at hs
      rcases hst _ _ hs with h | h
      · exact hnt.2 h
      · exact hnt.1 h
    · rw [show x + rotL n + n = x + n + rotL n by abel] at hs
      rcases hst _ _ hs with h | h
      · exact hnt.1 h
      · exact hnt.2 h
  have c4 : (x + n + rotL n) + (x + n + rotL n) ∉ (dbl (pathP l (x :: xs') k)).tail := by
    have hnd := dbl_nodup_of_nodup hPnd hPch
    rw [← List.cons_head?_tail hhead, List.nodup_cons] at hnd
    exact hnd.1
  have hJ₁ : IsSimpleClosed (curveW l (x :: xs') k x n) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · unfold curveW; exact List.append_ne_nil_of_right_ne_nil _ (by simp [chordW])
    · unfold curveW
      rw [List.head?_append_of_ne_nil _ hdblne, hhead,
        List.getLast?_append_of_ne_nil _ (by simp [chordW])]
      rfl
    · unfold curveW
      rw [List.isChain_append]
      refine ⟨dbl_isChain hPch, chordW_isChain hn x, ?_⟩
      intro a ha b hb
      rw [hlastd] at ha
      simp only [Option.mem_def, Option.some.injEq] at ha
      subst ha
      simp only [chordW, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      convert hn using 1; abel
    · unfold curveW
      rw [List.tail_append_of_ne_nil hdblne, List.nodup_append]
      refine ⟨(dbl_nodup_of_nodup hPnd hPch).sublist (List.tail_sublist _), chordW_nodup hn x, ?_⟩
      intro a ha b hb hab
      subst hab
      rcases mem_chordW.1 hb with rfl | rfl | rfl | rfl
      · exact c1 (List.mem_of_mem_tail ha)
      · exact c2 (List.mem_of_mem_tail ha)
      · exact c3 (List.mem_of_mem_tail ha)
      · exact c4 ha
    · unfold curveW
      rw [List.tail_append_of_ne_nil hdblne]
      simp [chordW]
  have hbot : (x + x, x + (x + n)) ∈ steps (curveW l (x :: xs') k x n) :=
    mem_steps_append_of_getLast?_head? hlastd (by simp [chordW])
  have hchord : ∀ st ∈ steps (chordW x n), st ∈ steps (curveW l (x :: xs') k x n) := by
    intro st hst'
    unfold curveW
    obtain ⟨a, b⟩ := st
    exact steps_of_steps_suffix hst'
  have htop : ((x + rotL n) + (x + n + rotL n), (x + n + rotL n) + (x + n + rotL n)) ∈
      steps (curveW l (x :: xs') k x n) :=
    hchord _ (by simp [steps, chordW])
  have hV : ∀ q, q ∉ s.visited → q + q ∉ curveW l (x :: xs') k x n := by
    intro q hq hm
    unfold curveW at hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hq (hPV q (mem_of_double_mem_dbl' hPch hm))
    · rcases mem_chordW.1 hm with h | h | h | h
      · exact double_ne_double_add_unit hn q x (by rw [h]; abel)
      · exact double_ne_oddodd hn q x (by rw [h]; abel)
      · exact double_ne_double_add_unit hn q (x + rotL n) (by rw [h]; abel)
      · exact hq (double_inj h ▸ hNWvis)
  have hmidW : ∀ z w, IsUnit (w - z) → z + w ∈ curveW l (x :: xs') k x n →
      (z, w) ∈ steps (pathP l (x :: xs') k) ∨ (w, z) ∈ steps (pathP l (x :: xs') k) ∨
      (z = x ∧ w = x + n) ∨ (z = x + n ∧ w = x) ∨
      (z = x + rotL n ∧ w = x + n + rotL n) ∨ (z = x + n + rotL n ∧ w = x + rotL n) := by
    intro z w hu hm
    unfold curveW at hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · rw [show z + w = z + z + (w - z) by abel] at hm
      rcases (mid_mem_dbl_iff' hPch hu).1 hm with hs | hs
      · rw [show z + (w - z) = w by abel] at hs; exact Or.inl hs
      · rw [show z + (w - z) = w by abel] at hs; exact Or.inr (Or.inl hs)
    · rcases mem_chordW.1 hm with h | h | h | h
      · have hn' : IsUnit (x + n - x) := by rw [add_sub_cancel_left]; exact hn
        rcases bond_eq_of_mid_eq hu hn' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exfalso
        exact mid_ne_oddodd hu hn z x (by rw [show z + z + (w - z) = z + w by abel, h]; abel)
      · have hn' : IsUnit (x + n + rotL n - (x + rotL n)) := by
          rw [show x + n + rotL n - (x + rotL n) = n by abel]; exact hn
        rcases bond_eq_of_mid_eq hu hn' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))
      · exfalso
        exact mid_ne_double hu z (x + n + rotL n) (by rw [show z + z + (w - z) = z + w by abel, h])
  have hNE' : ∃ t ∈ steps (curveW l (x :: xs') k x n),
      Relation.ReflTransGen (OffAdj (dbl (curveW l (x :: xs') k x n))) (quad e.2)
        (rightPt t.1 t.2) := by
    refine ⟨(x + (x + n), x + (x + n + rotL n)), hchord _ (by simp [steps, chordW]), ?_⟩
    have hq : quad e.2 = (x + (x + n)) + (x + (x + n)) + n + n := by
      rw [hNE]; unfold quad; abel
    have hr : rightPt (x + (x + n)) (x + (x + n + rotL n)) =
        (x + (x + n)) + (x + (x + n)) + n + rotL n := by
      unfold rightPt
      rw [show x + (x + n + rotL n) - (x + (x + n)) = rotL n by abel, rotR_rotL]
      abel
    rw [hq, hr]
    have h2e : (x + n) + (x + n) ∉ curveW l (x :: xs') k x n := hV (x + n) (hNE ▸ hNEV)
    have hA : (x + (x + n)) + (x + (x + n)) + n + n ∉ dbl (curveW l (x :: xs') k x n) := by
      intro hm
      rw [show (x + (x + n)) + (x + (x + n)) + n + n = ((x + n) + (x + n)) + ((x + n) + (x + n))
        by abel] at hm
      exact h2e (mem_of_double_mem_dbl hJ₁.closed hm)
    have hB : (x + (x + n)) + (x + (x + n)) + n ∉ dbl (curveW l (x :: xs') k x n) :=
      mid_notMem_dbl_of_notMem hJ₁.closed hn (by
        rw [show x + (x + n) + n = (x + n) + (x + n) by abel]; exact h2e)
    have hC : (x + (x + n)) + (x + (x + n)) + n + rotL n ∉ dbl (curveW l (x :: xs') k x n) := by
      rw [← hr]
      have hodd := rightPt_odd (a := x + (x + n)) (b := x + (x + n + rotL n)) (by
        rw [show x + (x + n + rotL n) - (x + (x + n)) = rotL n by abel]; exact hrot)
      exact oddodd_notMem_dbl hJ₁.closed hodd.1 hodd.2
    refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single ⟨hA, hB, ?_⟩)
      (Relation.ReflTransGen.single ⟨hB, hC, ?_⟩)
    · rw [show (x + (x + n)) + (x + (x + n)) + n - ((x + (x + n)) + (x + (x + n)) + n + n) = -n
        by abel]
      exact isUnit_neg hn
    · rw [show (x + (x + n)) + (x + (x + n)) + n + rotL n -
        ((x + (x + n)) + (x + (x + n)) + n) = rotL n by abel]
      exact hrot
  refine ⟨hd, hinv, hdfs, hout, hact, hex, hl, hk, hlast, hτx, hWclosed, hJ₁, ?_, hbot, htop, ?_,
    ?_, ?_, hV, ?_, ?_, ?_, ?_, hNE'⟩
  · intro a b hab
    unfold curveW
    exact ⟨steps_of_steps_prefix (mem_steps_dbl.2 ⟨(a, b), hab, Or.inl rfl⟩),
      steps_of_steps_prefix (mem_steps_dbl.2 ⟨(a, b), hab, Or.inr rfl⟩)⟩
  · intro p y _ _ _ h
    rw [hNE] at h
    exact h
  · intro y _ hne h
    apply hne
    rw [h, ← hNE, ← hex]
  · intro par hpar h
    have := hdfs.branch_visited par (List.mem_of_getElem? hpar)
    rw [h, ← hNE] at this
    exact hNEV this
  · intro q q' hq hq' hu hm
    rcases hmidW q q' hu hm with h | h | ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hq (hPV q (mem_steps h).1)
    · exact hq (hPV q (mem_steps h).2)
    · exact hq hxvis
    · exact hq' hxvis
    · exact hq' hNWvis
    · exact hq hNWvis
  · intro w hw hm
    unfold curveW at hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hw (mem_of_double_mem_dbl' hPch hm)
    · rcases mem_chordW.1 hm with h | h | h | h
      · exact double_ne_double_add_unit hn w x (by rw [h]; abel)
      · exact double_ne_oddodd hn w x (by rw [h]; abel)
      · exact double_ne_double_add_unit hn w (x + rotL n) (by rw [h]; abel)
      · exact hw (double_inj h ▸ hNWP)
  · intro z w hz hw hu hze hzτ hm
    rcases hmidW z w hu hm with h | h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hw (mem_steps h).2
    · exact hw (mem_steps h).1
    · exact hze (by rw [← hNE, ← hex])
    · exact hw hxP
    · exact hw hNWP
    · exact hzτ rfl
  · intro z w hz hw hu hm
    rcases hmidW z w hu hm with h | h | ⟨rfl, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hz (mem_steps h).1
    · exact hz (mem_steps h).2
    · exact hz hxP
    · exact hw hxP
    · exact hw hNWP
    · exact hz hNWP

end WCase

theorem active_list_W (f : Site) {d : Site} (hd : IsUnit d) (ρ : Config squareGraph) (n : ℕ)
    {e : Site × Site} {rest : List (Site × Site)} (he : (explore ρ f d n).active = e :: rest)
    (hW : TestedAs (explore ρ f d n).tested (sideW e.1 e.2) false) : rest = [] := by
  have hinv := explInv_explore ρ f hd n
  obtain ⟨xs, Fs, hdfs⟩ := dfs_explore ρ f hd n
  have hout := explOuter_explore ρ f hd n
  obtain ⟨x, xs', F₁, Fs', rfl, rfl, hrest, hex⟩ := dfs_head_shape hdfs he
  have hadjE : squareGraph.Adj e.1 e.2 :=
    hinv.active_adj e (by rw [he]; exact List.mem_cons_self)
  have hn : IsUnit (e.2 - e.1) := isUnit_of_adj hadjE
  have hW' : ((sideW e.1 e.2).1, (sideW e.1 e.2).2, false) ∈ (explore ρ f d n).tested := hW
  rw [sideW_fst, sideW_snd] at hW'
  have h1 : e.2 - e.1 =
      rotR (rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 1) - e.1) := by
    have := corner_NE_sub_SE (primalTail e.1 e.2) (primalDir e.1 e.2)
    rwa [rightFace_primal hadjE, leftFace_primal hadjE] at this
  have h2 : rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 2) -
      rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 1) = e.2 - e.1 := by
    have := corner_NW_sub_SW (primalTail e.1 e.2) (primalDir e.1 e.2)
    rwa [rightFace_primal hadjE, leftFace_primal hadjE] at this
  have hSW : rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 1) = e.1 + rotL (e.2 - e.1) := by
    rw [h1, rotL_rotR]; abel
  have hNW : rightFace (primalTail e.1 e.2) (primalDir e.1 e.2 + 2) =
      e.1 + (e.2 - e.1) + rotL (e.2 - e.1) := by
    rw [show e.1 + (e.2 - e.1) + rotL (e.2 - e.1) = (e.1 + rotL (e.2 - e.1)) + (e.2 - e.1) by abel,
      ← hSW, ← h2]
    abel
  rw [hSW, hNW, hex] at hW'
  rw [hex] at hn
  have hNE : e.2 = x + (e.2 - x) := by abel
  have hnd : (explore ρ f d n).tested.Nodup := hinv.tested_nodup.of_map _
  have hNWvis : x + (e.2 - x) + rotL (e.2 - x) ∈ (explore ρ f d n).visited :=
    hinv.tested_tail _ hW'
  obtain ⟨l, hl⟩ := exists_chainTo hdfs.toDFS0 hnd hNWvis
  obtain ⟨y, hy⟩ : ∃ y, l.getLast? = some y := by
    rcases hl' : l.getLast? with _ | y
    · exact absurd (List.getLast?_eq_none_iff.1 hl') (chain_ne_nil hl)
    · exact ⟨y, rfl⟩
  obtain ⟨k, hk, hxk⟩ := List.getElem_of_mem (hl.last_mem y hy)
  rw [← hxk] at hy
  have c := ctxW hd hinv hdfs.toDFS0 hout (by rw [he, hrest]) hex hn hNE hl hk hy hW'
  have := c.active_eq
  rw [he] at this
  simpa using this

end LatticeProb.Lattice.Planar
