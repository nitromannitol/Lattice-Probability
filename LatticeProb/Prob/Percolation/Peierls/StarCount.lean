/-
Ported from the Exploding-Sandpiles repository (Apache-2.0): `Exploding/Support/ExtMHBase.lean`
and the king-graph section of `Exploding/Support/ExtMHCount.lean`. Names and statements are
kept; the namespace is `LatticeProb.Percolation.Peierls`, and the site, lattice and component
notions are those of `LatticeProb/Site.lean`.
-/
import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# `*`-connected sets in `ℤ^d`

King adjacency on `ℤ^d`, `*`-connected sets, the two combinatorial facts used by the Peierls
estimate on the holes of an infinite cluster (the `*`-connectedness of the boundary between two
connected sets, `xmh_BoundaryStar`, and the exponential count of `*`-connected sets,
`xmh_StarCount`), and the growth of a `*`-connected set to a prescribed size inside a larger one.
-/

namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory Relation SimpleGraph

variable {d : ℕ}

/-! ### Relations -/

theorem xmh_rtg_symm {α : Type*} {R : α → α → Prop} (h : ∀ a b, R a b → R b a) {a b : α}
    (hab : ReflTransGen R a b) : ReflTransGen R b a := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (h _ _ hbc) ih

/-- A component is closed under an adjacent step that remains in the underlying set. -/
theorem xmh_componentIn_step {S : Set (Site d)} {x b z : Site d}
    (hb : b ∈ componentIn S x) (hz : z ∈ S) (hbz : (lattice d).Adj b z) :
    z ∈ componentIn S x := by
  obtain ⟨hx, hbS, hreach⟩ := hb
  refine ⟨hx, hz, hreach.trans ?_⟩
  exact SimpleGraph.Adj.reachable (by simpa [SimpleGraph.induce_adj] using hbz)

/-- Membership in a component supplies a finite nearest-neighbour walk within the underlying
set, represented as a sequence of sites. -/
theorem xmh_walk_of_component {S : Set (Site d)} {x y : Site d}
    (h : y ∈ componentIn S x) :
    ∃ (m : ℕ) (c : ℕ → Site d), c 0 = x ∧ c m = y ∧ (∀ s, s ≤ m → c s ∈ S) ∧
      ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1)) := by
  obtain ⟨hx, hy, hreach⟩ := h
  obtain ⟨w⟩ := hreach
  refine ⟨w.length, fun s => (w.getVert s).1, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only
    rw [SimpleGraph.Walk.getVert_length]
  · intro s _
    exact (w.getVert s).2
  · intro s hs
    have := w.adj_getVert_succ hs
    simpa [SimpleGraph.induce_adj] using this

/-! ### King adjacency and `*`-connected sets -/

/-- King adjacency on `ℤ^d`: two distinct sites at sup-norm distance at most one. -/
def xmh_star (a b : Site d) : Prop := a ≠ b ∧ ∀ i, |a i - b i| ≤ 1

theorem xmh_star_symm {a b : Site d} (h : xmh_star a b) : xmh_star b a := by
  refine ⟨h.1.symm, fun i => ?_⟩
  rw [abs_sub_comm]
  exact h.2 i

/-- A set of sites is `*`-connected: any two of its points are joined by a chain of king moves
inside it. -/
def xmh_SConn (F : Set (Site d)) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ xmh_star a b) x y

/-- **The boundary between two connected sets is `*`-connected.**  `A` and `B` are disjoint
connected sets of nearest-neighbour adjacency, with `B` closed under adjacency outside `A`
(`B` is a component of the complement of `A`); the sites of `B` adjacent to `A` are joined by
chains of king moves inside that boundary. -/
def xmh_BoundaryStar (d : ℕ) : Prop :=
  ∀ A B : Set (Site d),
    (∀ u ∈ A, ∀ v ∈ A, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) u v) →
    (∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v) →
    (∀ z, z ∈ A → z ∈ B → False) →
    (∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B) →
    ∀ x y : Site d, (x ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c x) →
      (y ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c y) →
      ReflTransGen (fun a b => (a ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c a) ∧
        (b ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c b) ∧ xmh_star a b) x y

/-- **Exponentially many `*`-connected sets.**  For some constant `K`, the finite `*`-connected
sets of `m` sites containing a given site lie in a family of at most `K ^ m` sets. -/
def xmh_StarCount (d : ℕ) : Prop :=
  ∃ K : ℕ, ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
    ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T

/-! ### Growth of `*`-connected sets -/

theorem xmh_SConn_singleton (p : Site d) : xmh_SConn ({p} : Set (Site d)) := by
  intro x hx y hy
  rw [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]

theorem xmh_SConn_insert {S : Set (Site d)} (hS : xmh_SConn S) {a b : Site d} (ha : a ∈ S)
    (hab : xmh_star a b) : xmh_SConn (insert b S) := by
  set R' : Site d → Site d → Prop :=
    fun u v => u ∈ insert b S ∧ v ∈ insert b S ∧ xmh_star u v with hR'
  have hsymm : ∀ u v, R' u v → R' v u := fun u v h => ⟨h.2.1, h.1, xmh_star_symm h.2.2⟩
  have hto : ∀ z ∈ insert b S, ReflTransGen R' a z := by
    intro z hz
    rcases hz with rfl | hz
    · exact ReflTransGen.single ⟨Set.mem_insert_of_mem _ ha, Set.mem_insert _ _, hab⟩
    · exact ReflTransGen.mono (fun u v h =>
        ⟨Set.mem_insert_of_mem _ h.1, Set.mem_insert_of_mem _ h.2.1, h.2.2⟩) _ _ (hS a ha z hz)
  intro x hx y hy
  exact (xmh_rtg_symm hsymm (hto x hx)).trans (hto y hy)

/-- A `*`-connected set `F` and a proper subset `S` of it containing a point: some point of `S`
is a king neighbour of a point of `F` outside `S`. -/
theorem xmh_exit {F S : Set (Site d)} (hF : xmh_SConn F) (hSF : S ⊆ F) {p y : Site d}
    (hp : p ∈ S) (hy : y ∈ F) (hyS : y ∉ S) :
    ∃ a ∈ S, ∃ b ∈ F, b ∉ S ∧ xmh_star a b := by
  have key : ∀ z, ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ xmh_star a b) p z →
      z ∈ S ∨ ∃ a ∈ S, ∃ b ∈ F, b ∉ S ∧ xmh_star a b := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hp
    | @tail u v _ hbc ih =>
      rcases ih with h | h
      · by_cases hv : v ∈ S
        · exact Or.inl hv
        · exact Or.inr ⟨u, h, v, hbc.2.1, hv, hbc.2.2⟩
      · exact Or.inr h
  rcases key y (hF p (hSF hp) y hy) with h | h
  · exact absurd h hyS
  · exact h

/-- A `*`-connected set containing `p` with at least `m ≥ 1` points contains a `*`-connected
finite set of exactly `m` points containing `p`. -/
theorem xmh_grow {F : Set (Site d)} (hF : xmh_SConn F) {p : Site d} (hp : p ∈ F) :
    ∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ F.encard →
      ∃ F' : Finset (Site d), p ∈ F' ∧ (F' : Set (Site d)) ⊆ F ∧ F'.card = m ∧
        xmh_SConn (F' : Set (Site d)) := by
  classical
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    refine ⟨{p}, by simp, by simpa using hp, by simp, ?_⟩
    simpa using xmh_SConn_singleton p
  | succ m hm ih =>
    intro hcard
    obtain ⟨F', hpF', hF'F, hF'card, hF'conn⟩ :=
      ih (le_trans (by exact_mod_cast Nat.le_succ m) hcard)
    have hnot : ¬ F ⊆ (F' : Set (Site d)) := by
      intro hsub
      have h1 : F.encard ≤ (F' : Set (Site d)).encard := Set.encard_le_encard hsub
      rw [Set.encard_coe_eq_coe_finsetCard, hF'card] at h1
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans hcard h1
      have h3 : m + 1 ≤ m := by exact_mod_cast h2
      omega
    obtain ⟨y, hyF, hyF'⟩ := Set.not_subset.1 hnot
    obtain ⟨a, haF', b, hbF, hbF', hab⟩ :=
      xmh_exit hF hF'F (Finset.mem_coe.2 hpF') hyF hyF'
    refine ⟨insert b F', Finset.mem_insert_of_mem hpF', ?_, ?_, ?_⟩
    · intro z hz
      rw [Finset.coe_insert] at hz
      rcases hz with rfl | hz
      · exact hbF
      · exact hF'F hz
    · rw [Finset.card_insert_of_notMem (fun h => hbF' (Finset.mem_coe.2 h)), hF'card]
    · rw [Finset.coe_insert]
      exact xmh_SConn_insert hF'conn haF' hab


/-! ### King adjacency as a graph -/

/-- King adjacency as a simple graph on the lattice. -/
def xmh_kingGraph (d : ℕ) : SimpleGraph (Site d) where
  Adj := xmh_star
  symm := Std.Symm.mk fun _ _ h => xmh_star_symm h
  loopless := Std.Irrefl.mk fun _ h => h.1 rfl

/-- The inclusion of an induced subgraph as a graph homomorphism. -/
def xmh_induceHom {V : Type*} (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

end LatticeProb.Percolation.Peierls
