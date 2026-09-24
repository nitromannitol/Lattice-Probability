/-
Moved from nitromannitol/Divisible-Sandpile-Percolation, Apache-2.0; copyright
2026 Ahmed Bou-Rabee and Yuval Peres.  Sources:

* `Sandpile/Support/CrossingDefinitions.lean` (`IsLatticeRectangle`,
  `IsCrossingPath`, `crossingValue`), `sandpile.tex:3442-3450`;
* `Sandpile/Support/PlaneRectangle.lean`, only its generic opening section
  (`planeRectangle` through `card_planeRectangle_aspect_le_cube`); the rest of
  that file (`planeTranslate`, `farCutoff`, `exists_gaussian_aspect_rectangle_
  comparison`) is the paper's own Gaussian far-field comparison for the
  divisible-sandpile continuum field and is not moved;
* `Sandpile/Support/RectangleMonotonicity.lean`, only `walk_prefix_hit_integer`
  and `walk_mem_support_of_induce`, which the file itself states for a bare
  `{V} {G : SimpleGraph V} (f : V → ℤ)`.  The file's other three declarations
  (`crossingValue_width_height_mono`, `measurableSet_planarCrossingEvent`,
  `planarCrossingEvent_width_height_mono`) are stated for the specific object
  `planarCrossingEvent` of `Sandpile/Support/PlanarLaw.lean` and reach, through
  `crossingValue_spec`/`le_crossingValue_of_walk` (`Sandpile/Support/
  CrossingWitness.lean`) and `RectangleBottleneck.lean`, into the paper's own
  Gaussian kernel and increment-bound machinery; they are not self-contained
  over Mathlib and `LatticeProb` and are not moved.

`Site 2` here is `LatticeProb.Site 2` (`Fin 2 → ℤ`), the library's general
`d`-dimensional lattice site at `d = 2`; this is a different type from
`LatticeProb.Lattice.Planar.Site := ℤ × ℤ` (the rotor-formalization plane),
even though both model the same lattice `ℤ²`.  `LatticeProb.Prob.Percolation.
BondPercolation` uses the latter; nothing here is unified with it, since the
two types are not definitionally equal.
-/
import LatticeProb.Site

open LatticeProb

/-!
# Lattice rectangles and the crossing value of a planar field

A finite lattice rectangle (`IsLatticeRectangle`) is a `Finset (Site 2)` cut
out coordinatewise by two corners.  A crossing path (`IsCrossingPath`) is a
simple path within a set of sites, from the sites minimising the first
coordinate to the sites maximising it.  The crossing value of a real field `F`
on `Q` (`crossingValue`) is `max_Γ min_{z ∈ Γ} F z` over crossing paths `Γ` of
`Q`; `planeRectangle w h` is the standard rectangle `[0,w] × [0,h]`.

`walk_prefix_hit_integer` and `walk_mem_support_of_induce`, from the same
cluster of results, are general facts about a walk in an arbitrary
`SimpleGraph`: the first records that a walk along which an integer-valued
function increases by at most one at each step must, on any initial segment,
hit every intermediate value; the second, that pulling a walk's support back
through an induced-subgraph embedding recovers membership in the ambient
walk's support.
-/

namespace LatticeProb.Percolation

/-- A finite axis-parallel lattice rectangle of `ℤ²`: the sites lying
coordinatewise between two corners (`sandpile.tex:3442-3443`). -/
def IsLatticeRectangle (Q : Finset (Site 2)) : Prop :=
  ∃ a b : Site 2, ∀ z : Site 2, z ∈ Q ↔ ∀ i : Fin 2, a i ≤ z i ∧ z i ≤ b i

/-- A simple path in `Q` from the left to the right (`sandpile.tex:3448-3450`):
a nonempty list of sites of `Q`, without repetitions, consecutive entries
adjacent in `ℤ²`, the first entry on the left side of `Q` and the last entry on
its right side. -/
def IsCrossingPath (Q : Finset (Site 2)) (Γ : List Q) : Prop :=
  Γ ≠ [] ∧ Γ.Nodup ∧
    List.IsChain (fun z w : Q => (lattice 2).Adj (z : Site 2) (w : Site 2)) Γ ∧
    (∀ z ∈ Γ.head?, ∀ w ∈ Q, (z : Site 2) 0 ≤ w 0) ∧
    (∀ z ∈ Γ.getLast?, ∀ w ∈ Q, w 0 ≤ (z : Site 2) 0)

/-- The crossing value `L_Q(F) = max_Γ min_{z∈Γ} F_z` of
`sandpile.tex:3444-3450`. -/
noncomputable def crossingValue (Q : Finset (Site 2)) (F : Q → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ Γ : List Q, IsCrossingPath Q Γ ∧ a = sInf (F '' {z : Q | z ∈ Γ})}

/-! ### The standard rectangle `[0,w] × [0,h]` -/

/-- The lattice rectangle `[0,w] × [0,h]`. -/
noncomputable def planeRectangle (w h : ℕ) : Finset (Site 2) :=
  Fintype.piFinset (fun i => Finset.Icc (0 : ℤ) (![(w : ℤ), (h : ℤ)] i))

theorem mem_planeRectangle (w h : ℕ) (z : Site 2) :
    z ∈ planeRectangle w h ↔ 0 ≤ z 0 ∧ z 0 ≤ w ∧ 0 ≤ z 1 ∧ z 1 ≤ h := by
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

theorem isLatticeRectangle_planeRectangle (w h : ℕ) : IsLatticeRectangle (planeRectangle w h) := by
  refine ⟨0, ![w, h], ?_⟩
  intro z
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]

theorem card_planeRectangle (w h : ℕ) : (planeRectangle w h).card = (w + 1) * (h + 1) := by
  simp [planeRectangle, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc]

theorem height_le_card_planeRectangle (w h : ℕ) : h ≤ (planeRectangle w h).card := by
  rw [card_planeRectangle]
  exact (Nat.le_succ h).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos w))

/-- A rectangle of aspect ratio at most `ϑ` and height `r` has at most `r ^ 3`
sites, once `r` is large enough relative to `ϑ`. -/
theorem card_planeRectangle_aspect_le_cube {ϑ : ℝ} (hϑ : 1 ≤ ϑ) {r : ℕ}
    (hr : 2 * (ϑ + 1) ≤ (r : ℝ)) : (planeRectangle ⌊ϑ * r⌋₊ r).card ≤ r ^ 3 := by
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hϑ0 : 0 ≤ ϑ := by linarith
  have hfloor := Nat.floor_le (mul_nonneg hϑ0 hr0)
  have hcard : ((planeRectangle ⌊ϑ * r⌋₊ r).card : ℝ) ≤ (r : ℝ) ^ 3 := by
    rw [card_planeRectangle]
    push_cast
    calc
      _ ≤ (ϑ * r + 1) * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ ((ϑ + 1) * r) * (2 * r) := mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
      _ = (2 * (ϑ + 1)) * (r : ℝ) ^ 2 := by ring
      _ ≤ (r : ℝ) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
      _ = _ := by ring
  exact_mod_cast hcard

/-! ### Two general facts about walks in a `SimpleGraph` -/

/-- If an integer-valued function changes by at most one along each step of a
walk, then the walk has an initial segment ending at any intermediate value
of the function between its values at the endpoints. -/
theorem walk_prefix_hit_integer {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hstep : ∀ x y, G.Adj x y → |f y - f x| ≤ 1) {a b : V} (p : G.Walk a b) (k : ℤ) :
    f a ≤ k → k ≤ f b → ∃ (c : V) (q : G.Walk a c), f c = k ∧ q.support ⊆ p.support ∧
      ∀ z ∈ q.support, f z ≤ k := by
  induction p with
  | @nil a =>
    intro ha hb
    refine ⟨_, .nil, le_antisymm ha hb, fun _ hz => hz, ?_⟩
    intro z hz
    have he : z = a := by simpa using hz
    simpa only [he] using ha
  | @cons a b c hab p ih =>
    intro ha hc
    by_cases he : f a = k
    · refine ⟨a, .nil, he, ?_, ?_⟩
      · intro z hz
        have hz' : z = a := by simpa using hz
        subst z
        exact (SimpleGraph.Walk.cons hab p).start_mem_support
      · intro z hz
        have hz' : z = a := by simpa using hz
        simpa only [hz'] using ha
    · have hb : f b ≤ k := by
        have hh := (abs_le.mp (hstep a b hab)).2
        omega
      obtain ⟨z, q, hz, hsub, hbound⟩ := ih hb hc
      refine ⟨z, .cons hab q, hz, ?_, ?_⟩
      · intro t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht ⊢
        exact ht.imp_right (fun ht => hsub ht)
      · intro t ht
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ha
        · exact hbound t ht

/-- Pulling a walk's support back through an induced-subgraph embedding
recovers membership in the ambient walk's support. -/
theorem walk_mem_support_of_induce {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (hp : ∀ z ∈ p.support, z ∈ S) {z : S}
    (hz : z ∈ (p.induce S hp).support) : (z : V) ∈ p.support := by
  have hm : (z : V) ∈ ((p.induce S hp).map (SimpleGraph.Embedding.induce S).toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  rw [SimpleGraph.Walk.map_induce] at hm
  exact hm

end LatticeProb.Percolation
