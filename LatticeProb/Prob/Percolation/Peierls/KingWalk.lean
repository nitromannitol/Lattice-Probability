/-
Ported from the Exploding-Sandpiles repository (Apache-2.0): `Exploding/Support/ExtMHCount.lean`,
declarations `xmh_conn_walk_aux` through `xmh_SConn_iff_preconnected`. Names and statements are
kept; the namespace is `LatticeProb.Percolation.Peierls`.
-/
import LatticeProb.Prob.Percolation.Peierls.StarCount
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# King walks and `*`-connected sets

A connected finite graph is the support of a closed walk of length at most twice its number of
vertices (`xmh_conn_walk_aux`). King walks are encoded by their king directions, and a
`*`-connected set is preconnected in the induced king graph (`xmh_SConn_iff_preconnected`).
-/

namespace LatticeProb.Percolation.Peierls

open SimpleGraph LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### A connected finite graph is the support of a short closed walk -/

/-- **Short closed walk.**  A connected finite graph on `V` has a closed walk from any vertex
whose support is all of `V` and whose length is at most `2 * (|V| - 1)`. -/
theorem xmh_conn_walk_aux : ∀ n : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n → ∀ (G : SimpleGraph V) (p : V), G.Connected →
      ∃ w : G.Walk p p, (∀ x, x ∈ w.support) ∧ w.length ≤ 2 * (Fintype.card V - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    intro V _ _ hcard G p hconn
    by_cases hle : Fintype.card V ≤ 1
    · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hle
      refine ⟨Walk.nil, fun x => ?_, by simp⟩
      rw [Walk.support_nil]
      exact List.mem_singleton.mpr (Subsingleton.elim x p)
    · have h2 : 1 < Fintype.card V := by omega
      have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp h2
      obtain ⟨v, hvconn⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
      by_cases hvp : v = p
      · -- the removed vertex is the root: prepend and append the root to a walk of the rest
        rw [hvp] at hvconn
        obtain ⟨u, hpu⟩ : ∃ u, G.Adj p u := by
          have hpos : 0 < G.degree p :=
            lt_of_lt_of_le hconn.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree p)
          obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
          exact ⟨u, by simpa [SimpleGraph.mem_neighborFinset] using hu⟩
        let W := {x : V // x ≠ p}
        let G' := G.induce ({p}ᶜ : Set V)
        have hcard' : Fintype.card W = n - 1 := by
          rw [Fintype.card_subtype_compl (fun x => x = p), hcard]
          simp
        have hG'conn : G'.Connected := hvconn
        have hlt : Fintype.card W < n := by rw [hcard']; omega
        obtain ⟨w', hw'supp, hw'len⟩ :=
          ih (Fintype.card W) hlt W rfl G' (Subtype.mk u hpu.ne.symm : W) hG'conn
        let hmap : G.Walk u u := w'.map (xmh_induceHom G ({p}ᶜ : Set V))
        refine ⟨(Walk.cons hpu hmap).concat hpu.symm, ?_, ?_⟩
        · intro x
          rw [Walk.support_concat, Walk.support_cons, List.mem_append, List.mem_cons,
            List.mem_singleton]
          by_cases hxp : x = p
          · exact Or.inl (Or.inl hxp)
          · refine Or.inl (Or.inr ?_)
            have hxW : (Subtype.mk x hxp : W) ∈ w'.support := hw'supp (Subtype.mk x hxp : W)
            show x ∈ (Walk.map (xmh_induceHom G ({p}ᶜ : Set V)) w').support
            exact (congrArg (fun l : List V => x ∈ l)
              (Walk.support_map (xmh_induceHom G ({p}ᶜ : Set V)) w')).mpr
              (List.mem_map.mpr ⟨Subtype.mk x hxp, hxW, rfl⟩)
        · rw [Walk.length_concat, Walk.length_cons]
          have hlen : (Walk.map (xmh_induceHom G ({p}ᶜ : Set V)) w').length = w'.length :=
            Walk.length_map _ w'
          change (Walk.map (xmh_induceHom G ({p}ᶜ : Set V)) w').length + 1 + 1
            ≤ 2 * (Fintype.card V - 1)
          rw [hlen]
          have := hw'len
          rw [hcard'] at this
          omega
      · -- the removed vertex is not the root: insert it by a two-step detour
        let W := {x : V // x ≠ v}
        let G' := G.induce ({v}ᶜ : Set V)
        have hcard' : Fintype.card W = n - 1 := by
          rw [Fintype.card_subtype_compl (fun x => x = v), hcard]
          simp
        have hlt : Fintype.card W < n := by rw [hcard']; omega
        let p' : W := Subtype.mk p (fun h => hvp h.symm)
        obtain ⟨w', hw'supp, hw'len⟩ :=
          ih (Fintype.card W) hlt W rfl G' p' hvconn
        let hmap : G.Walk p p := w'.map (xmh_induceHom G ({v}ᶜ : Set V))
        obtain ⟨u, hvu⟩ : ∃ u, G.Adj v u := by
          have hpos : 0 < G.degree v :=
            lt_of_lt_of_le hconn.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree v)
          obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
          exact ⟨u, by simpa [SimpleGraph.mem_neighborFinset] using hu⟩
        have huv : u ≠ v := fun h => hvu.ne h.symm
        have huW : (Subtype.mk u huv : W) ∈ w'.support := hw'supp (Subtype.mk u huv : W)
        have hmem : u ∈ hmap.support := by
          show u ∈ (Walk.map (xmh_induceHom G ({v}ᶜ : Set V)) w').support
          exact (congrArg (fun l : List V => u ∈ l)
            (Walk.support_map (xmh_induceHom G ({v}ᶜ : Set V)) w')).mpr
            (List.mem_map.mpr ⟨Subtype.mk u huv, huW, rfl⟩)
        let mid : G.Walk u u := Walk.cons hvu.symm (Walk.cons hvu Walk.nil)
        refine ⟨(hmap.takeUntil u hmem).append (mid.append (hmap.dropUntil u hmem)), ?_, ?_⟩
        · intro x
          rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff]
          by_cases hxv : x = v
          · have hvmid : v ∈ mid.support := by
              simp only [mid, Walk.support_cons, Walk.support_nil]
              simp
            refine Or.inr (Or.inl ?_)
            rw [hxv]
            exact hvmid
          · have hxW : (Subtype.mk x (hxv) : W) ∈ w'.support :=
              hw'supp (Subtype.mk x (hxv) : W)
            have hxmap : x ∈ hmap.support := by
              show x ∈ (Walk.map (xmh_induceHom G ({v}ᶜ : Set V)) w').support
              exact (congrArg (fun l : List V => x ∈ l)
                (Walk.support_map (xmh_induceHom G ({v}ᶜ : Set V)) w')).mpr
                (List.mem_map.mpr ⟨Subtype.mk x (hxv), hxW, rfl⟩)
            have hdecomp : x ∈ ((hmap.takeUntil u hmem).append
                (hmap.dropUntil u hmem)).support := by
              rwa [Walk.take_spec]
            rw [Walk.mem_support_append_iff] at hdecomp
            rcases hdecomp with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        · have h1 : (hmap.takeUntil u hmem).length + (hmap.dropUntil u hmem).length
              = hmap.length := by
            rw [Walk.length_takeUntil, Walk.length_dropUntil]
            have hidx := List.idxOf_lt_length_of_mem hmem
            rw [Walk.length_support] at hidx
            omega
          have hmid : mid.length = 2 := by simp [mid, Walk.length_cons]
          have hlen : hmap.length = w'.length := by
            show (Walk.map (xmh_induceHom G ({v}ᶜ : Set V)) w').length = w'.length
            exact Walk.length_map _ w'
          rw [Walk.length_append, Walk.length_append]
          have := hw'len
          rw [hcard'] at this
          omega

end LatticeProb.Percolation.Peierls

namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory SimpleGraph

variable {d : ℕ}

/-! ### Encoding walks by king directions -/

/-- A king direction: a coordinatewise offset in `{-1, 0, 1}`. -/
def xmh_KingDir (d : ℕ) : Type := Fin d → Fin 3

/-- The lattice offset of a king direction. -/
def xmh_off (dir : xmh_KingDir d) : Site d := fun i => (dir i : ℤ) - 1

instance xmh_instFintypeKingDir (d : ℕ) : Fintype (xmh_KingDir d) :=
  inferInstanceAs (Fintype (Fin d → Fin 3))

/-- The zero king direction. -/
def xmh_zeroDir (d : ℕ) : xmh_KingDir d := fun _ => 1

theorem xmh_off_zero (d : ℕ) : xmh_off (xmh_zeroDir d) = 0 := by
  ext i; simp [xmh_off, xmh_zeroDir]

/-- The king direction from `a` to `b`, when the two are king neighbours. -/
def xmh_dirOf (a b : Site d) : xmh_KingDir d :=
  fun i => if b i < a i then (0 : Fin 3) else if b i = a i then 1 else 2

theorem xmh_off_dirOf {a b : Site d} (h : xmh_star a b) :
    xmh_off (xmh_dirOf a b) = b - a := by
  funext i
  have hi := (abs_le.mp (h.2 i))
  simp only [xmh_off, xmh_dirOf, Pi.sub_apply]
  rcases lt_trichotomy (b i) (a i) with hlt | heq | hgt
  · have hb : b i - a i = -1 := by omega
    rw [ite_eq_left hlt, hb]
    norm_num
  · have hb : b i - a i = 0 := by omega
    rw [ite_eq_right (not_lt.mpr heq.ge), ite_eq_left heq, hb]
    norm_num
  · have hb : b i - a i = 1 := by omega
    rw [ite_eq_right (not_lt.mpr hgt.le), ite_eq_right (ne_of_gt hgt), hb]
    norm_num

/-- The list of positions of a king walk given by its list of directions. -/
def xmh_posList (p : Site d) : List (xmh_KingDir d) → List (Site d)
  | [] => [p]
  | dir :: ds => p :: xmh_posList (p + xmh_off dir) ds

/-- The directions of a walk in the king graph. -/
def xmh_walkOffs : (p q : Site d) → (xmh_kingGraph d).Walk p q → List (xmh_KingDir d)
  | _, _, .nil => []
  | p, q, @Walk.cons _ _ _ v _ _ w' => xmh_dirOf p v :: xmh_walkOffs v q w'

theorem xmh_posList_walkOffs {p q : Site d} (w : (xmh_kingGraph d).Walk p q) :
    xmh_posList p (xmh_walkOffs p q w) = w.support := by
  induction w with
  | nil => simp [xmh_walkOffs, xmh_posList, Walk.support_nil]
  | cons h w ih =>
    simp only [xmh_walkOffs, xmh_posList, Walk.support_cons]
    rw [xmh_off_dirOf h, add_sub_cancel]
    exact congrArg (List.cons _) ih

theorem xmh_length_walkOffs {p q : Site d} (w : (xmh_kingGraph d).Walk p q) :
    (xmh_walkOffs p q w).length = w.length := by
  induction w with
  | nil => simp [xmh_walkOffs]
  | cons h w ih => simp [xmh_walkOffs, ih, Walk.length_cons]

/-- The total offset of a list of directions. -/
def xmh_lastOff (ds : List (xmh_KingDir d)) : Site d := (ds.map xmh_off).sum

theorem xmh_lastOff_walkOffs {p q : Site d} (w : (xmh_kingGraph d).Walk p q) :
    xmh_lastOff (xmh_walkOffs p q w) = q - p := by
  induction w with
  | nil => simp [xmh_walkOffs, xmh_lastOff]
  | cons h w ih =>
    simp only [xmh_walkOffs, xmh_lastOff, List.map_cons, List.sum_cons, xmh_off_dirOf h]
    simp only [xmh_lastOff] at ih
    rw [ih]; abel

theorem xmh_posList_append (p : Site d) (ds es : List (xmh_KingDir d)) :
    xmh_posList p (ds ++ es) = xmh_posList p ds ++ (xmh_posList (p + xmh_lastOff ds) es).tail := by
  induction ds generalizing p with
  | nil => cases es <;> simp [xmh_posList, xmh_lastOff]
  | cons dir ds ih =>
    simp only [List.cons_append, xmh_posList]
    rw [ih (p + xmh_off dir)]
    congr 1
    congr 1
    simp only [xmh_lastOff, List.map_cons, List.sum_cons]
    abel

theorem xmh_posList_replicate_zero (p : Site d) (n : ℕ) :
    xmh_posList p (List.replicate n (xmh_zeroDir d)) = List.replicate (n + 1) p := by
  induction n with
  | zero => simp [xmh_posList]
  | succ n ih =>
    rw [List.replicate_succ, xmh_posList, xmh_off_zero, add_zero, ih]
    simp [List.replicate_succ, Nat.add_assoc]

end LatticeProb.Percolation.Peierls

namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory SimpleGraph Relation

variable {d : ℕ}

/-- A `ReflTransGen` chain of `*`-moves in a set projects to a chain in the induced subtype. -/
theorem xmh_rtg_val {F : Set (Site d)} {a b : Site d} (ha : a ∈ F) (hb : b ∈ F)
    (h : ReflTransGen (fun u v => u ∈ F ∧ v ∈ F ∧ xmh_star u v) a b) :
    ReflTransGen (fun x y : ↥F => xmh_star x.val y.val) ⟨a, ha⟩ ⟨b, hb⟩ := by
  revert hb
  refine ReflTransGen.rec (motive := fun (x : Site d) _ => ∀ hx : x ∈ F,
      ReflTransGen (fun x y : ↥F => xmh_star x.val y.val) ⟨a, ha⟩ ⟨x, hx⟩) ?_ ?_ h
  · intro hx
    simpa using (ReflTransGen.refl :
      ReflTransGen (fun x y : ↥F => xmh_star x.val y.val) ⟨a, ha⟩ ⟨a, ha⟩)
  · intro b c hab hbc ih hc
    simpa using (ReflTransGen.tail (ih hbc.1) hbc.2.2)

/-- A chain in the induced subtype yields a chain of `*`-moves in the ambient set. -/
theorem xmh_rtg_val_inv {F : Set (Site d)} {a b : Site d} (ha : a ∈ F) (hb : b ∈ F)
    (h : ReflTransGen (fun x y : ↥F => xmh_star x.val y.val) ⟨a, ha⟩ ⟨b, hb⟩) :
    ReflTransGen (fun u v => u ∈ F ∧ v ∈ F ∧ xmh_star u v) a b := by
  refine ReflTransGen.rec (motive := fun (x : ↥F) _ =>
      ReflTransGen (fun u v => u ∈ F ∧ v ∈ F ∧ xmh_star u v) a x.val) ?_ ?_ h
  · exact ReflTransGen.refl
  · intro b c hab hbc ih
    exact ReflTransGen.tail ih ⟨b.property, c.property, hbc⟩

/-- `*`-connectedness of a set is preconnectedness of the induced king graph. -/
theorem xmh_SConn_iff_preconnected (F : Set (Site d)) :
    xmh_SConn F ↔ ((xmh_kingGraph d).induce F).Preconnected := by
  constructor
  · intro h a b
    exact (reachable_iff_reflTransGen a b).mpr
      (xmh_rtg_val a.property b.property (h a.val a.property b.val b.property))
  · intro h x hx y hy
    exact xmh_rtg_val_inv hx hy
      ((reachable_iff_reflTransGen (G := (xmh_kingGraph d).induce F) ⟨x, hx⟩ ⟨y, hy⟩).mp (h ⟨x, hx⟩ ⟨y, hy⟩))

end LatticeProb.Percolation.Peierls

