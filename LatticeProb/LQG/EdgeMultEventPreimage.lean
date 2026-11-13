import LatticeProb.LQG.Lemma311GoodRealCongr
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsAProp210
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBMain

/-!
# The Proposition 2.10 failure event and the Lemma 3.11 good event are preimages of sets of (curve, edge multiplicities)

For a pair `(bm, η)` of a boundary-length path and an area-parametrized curve on a probability
space `Ω`, the failure event `GMSMain.EpsAProp210Bad bm η ε V f A tol` of [18] Proposition 2.10 and
the good event `GMSMain.EpsB.Lemma311GoodReal bm η ε ρ β p` of [18] Lemma 3.11 at the mesh `ε` see
the boundary-length path only through the edge multiplicities of the `ε`-mated-CRT map. Hence both
are preimages, under `ω ↦ (η ω, edgeMult ε (bm ω))`, of fixed sets of pairs (curve, edge
multiplicities):

* `LFMultigraph.uDens_eq_of_edgeEquiv`, `LFMultigraph.prop210Bound_iff_of_edgeEquiv`: the density
  `u^ε` of [18] (2.12) and the bound of [18] Proposition 2.10 are invariant under a bijection of the
  edges preserving both ends, for cellular embeddings with the same cells (they see the multigraph
  only through the cells and the degrees);
* `MatedCRT.mem_epsAProp210Bad_iff_of_edgeMult`, `MatedCRT.mem_lemma311GoodReal_iff_of_edgeMult`:
  for one curve, the two events hold for a boundary-length path iff they hold for any other path
  with the same edge multiplicities;
* `MatedCRT.epsAProp210BadSet`, `MatedCRT.epsAProp210Bad_eq_preimage`, `MatedCRT.lemma311GoodSet`,
  `MatedCRT.lemma311GoodReal_eq_preimage`: the two events as preimages of sets of pairs
  (curve, edge multiplicities).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E E' : Type*}

/-- **The density `u^ε` of [18] (2.12) is invariant under relabelling the edges**: for multigraphs
related by a bijection of the edges preserving both ends and cellular embeddings with the same
cells, the densities `∑_x 1_{H_x} diam(H_x)² deg(x) / area(H_x)` agree. -/
theorem uDens_eq_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) {o : V}
    (H : CellularEmbedding G o) (H' : CellularEmbedding G' o) (hcell : H'.cell = H.cell) :
    GMS3.uDens H' = GMS3.uDens H := by
  have hcoef : ∀ x, GMS3.uCoef H' x = GMS3.uCoef H x := by
    intro x
    unfold GMS3.uCoef GMS3.cellDiam
    rw [hcell, deg_eq_of_edgeEquiv G G' σ hs ht x]
  funext z
  unfold GMS3.uDens
  rw [hcell]
  simp only [hcoef]

/-- **The bound of [18] Proposition 2.10 is invariant under relabelling the edges**: for
multigraphs related by a bijection of the edges preserving both ends and cellular embeddings with
the same cells, `∫_D f u^ε ≤ A ∫_D f + tol` holds for one iff it holds for the other. -/
theorem prop210Bound_iff_of_edgeEquiv (G : LFMultigraph V E) (G' : LFMultigraph V E') (σ : E ≃ E')
    (hs : ∀ e, G'.src (σ e) = G.src e) (ht : ∀ e, G'.tgt (σ e) = G.tgt e) {o : V}
    (H : CellularEmbedding G o) (H' : CellularEmbedding G' o) (hcell : H'.cell = H.cell)
    {D : Set ℂ} {f : ℂ → ℝ} {A tol : ℝ} :
    GMS3.Prop210Bound H' D f A tol ↔ GMS3.Prop210Bound H D f A tol := by
  unfold GMS3.Prop210Bound
  rw [uDens_eq_of_edgeEquiv G G' σ hs ht H H' hcell]

end LFMultigraph

namespace MatedCRT

/-- The `ε`-mated-CRT maps of two boundary-length paths with the same edge multiplicities have the
same adjacency. -/
theorem adj_graph_eq_of_edgeMult {ε : ℝ} {b b' : Path2}
    (hmult : ∀ x y : ℤ, edgeMult ε b x y = edgeMult ε b' x y) (h : IsLocallyFinite ε b)
    (h' : IsLocallyFinite ε b') : (graph ε b' h').adj = (graph ε b h).adj :=
  LFMultigraph.adj_eq_of_edgeEquiv (graph ε b h) (graph ε b' h') (edgeEquivOfEdgeMult hmult)
    (fun _ => rfl) (fun _ => rfl)

/-- One direction of `mem_epsAProp210Bad_iff_of_edgeMult`, for the complement of the failure
event: the map is locally finite, the cells `c([ε(x−1), εx])` form a cellular embedding of it, and
every such embedding satisfies the bound of [18] Proposition 2.10. -/
theorem epsAProp210Good_of_edgeMult {ε : ℝ} {V : Set ℂ} {f : ℂ → ℝ} {A tol : ℝ} {b b' : Path2}
    (c : C(ℝ, ℂ)) (hmult : ∀ x y : ℤ, edgeMult ε b x y = edgeMult ε b' x y)
    (hgood : (∃ (h : IsLocallyFinite ε b) (H : CellularEmbedding (graph ε b h) 0),
        ∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (h : IsLocallyFinite ε b) (H : CellularEmbedding (graph ε b h) 0),
        (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
          GMS3.Prop210Bound H V f A tol) :
    (∃ (h : IsLocallyFinite ε b') (H : CellularEmbedding (graph ε b' h) 0),
        ∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
      ∀ (h : IsLocallyFinite ε b') (H : CellularEmbedding (graph ε b' h) 0),
        (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
          GMS3.Prop210Bound H V f A tol := by
  obtain ⟨⟨h, H, hc⟩, hall⟩ := hgood
  have hsymm : ∀ x y : ℤ, edgeMult ε b' x y = edgeMult ε b x y := fun x y => (hmult x y).symm
  have h₁ : IsLocallyFinite ε b' := isLocallyFinite_of_edgeMult hmult h
  refine ⟨⟨h₁, H.ofAdjEq (adj_graph_eq_of_edgeMult hmult h h₁), hc⟩, ?_⟩
  intro h' H' hc'
  have h₀ : IsLocallyFinite ε b := isLocallyFinite_of_edgeMult hsymm h'
  have hadj : (graph ε b h₀).adj = (graph ε b' h').adj := adj_graph_eq_of_edgeMult hsymm h' h₀
  have hs : ∀ e, (graph ε b h₀).src (edgeEquivOfEdgeMult hsymm e) = (graph ε b' h').src e :=
    fun _ => rfl
  have ht : ∀ e, (graph ε b h₀).tgt (edgeEquivOfEdgeMult hsymm e) = (graph ε b' h').tgt e :=
    fun _ => rfl
  exact (LFMultigraph.prop210Bound_iff_of_edgeEquiv (graph ε b' h') (graph ε b h₀) _ hs ht H'
    (H'.ofAdjEq hadj) rfl).1 (hall h₀ (H'.ofAdjEq hadj) hc')

/-- **The failure event of [18] Proposition 2.10 sees the boundary-length path only through the
edge multiplicities.** For one curve `c` and two boundary-length paths `b, b'` whose `ε`-mated-CRT
maps have the same edge multiplicities, `(b, c)` lies in the failure event iff `(b', c)` does. -/
theorem mem_epsAProp210Bad_iff_of_edgeMult {ε : ℝ} {V : Set ℂ} {f : ℂ → ℝ} {A tol : ℝ}
    {b b' : Path2} (c : C(ℝ, ℂ)) (hmult : ∀ x y : ℤ, edgeMult ε b x y = edgeMult ε b' x y) :
    (b, c) ∈ GMSMain.EpsAProp210Bad Prod.fst Prod.snd ε V f A tol ↔
      (b', c) ∈ GMSMain.EpsAProp210Bad Prod.fst Prod.snd ε V f A tol := by
  simp only [GMSMain.EpsAProp210Bad, Set.mem_ofPred_eq]
  exact not_congr ⟨epsAProp210Good_of_edgeMult c hmult,
    epsAProp210Good_of_edgeMult c fun x y => (hmult x y).symm⟩

/-- **The failure event of [18] Proposition 2.10 as a set of pairs (curve, edge
multiplicities)**: the pairs `(c, m)` such that some boundary-length path with edge multiplicities
`m` at mesh `ε` lies, together with `c`, in the failure event. -/
def epsAProp210BadSet (ε : ℝ) (V : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) :
    Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {p | ∃ b : Path2, (∀ x y, edgeMult ε b x y = p.2 x y) ∧
    (b, p.1) ∈ GMSMain.EpsAProp210Bad Prod.fst Prod.snd ε V f A tol}

/-- **The failure event of [18] Proposition 2.10 is the preimage of `epsAProp210BadSet` under
`ω ↦ (η ω, edgeMult ε (bm ω))`.** -/
theorem epsAProp210Bad_eq_preimage {Ω : Type*} (bm : Ω → Path2) (η : Ω → C(ℝ, ℂ)) (ε : ℝ)
    (V : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) :
    GMSMain.EpsAProp210Bad bm η ε V f A tol =
      (fun ω => (η ω, fun x y => edgeMult ε (bm ω) x y)) ⁻¹' epsAProp210BadSet ε V f A tol := by
  ext ω
  simp only [Set.mem_preimage, epsAProp210BadSet, Set.mem_ofPred_eq]
  constructor
  · intro hω
    exact ⟨bm ω, fun _ _ => rfl, hω⟩
  · rintro ⟨b, hb, hbad⟩
    exact (mem_epsAProp210Bad_iff_of_edgeMult (b' := bm ω) (η ω) hb).1 hbad

/-- **The good event of [18] Lemma 3.11 sees the boundary-length path only through the edge
multiplicities.** For one curve `c` and two boundary-length paths `b, b'` whose `ε`-mated-CRT maps
have the same edge multiplicities, `(b, c)` lies in the good event iff `(b', c)` does. -/
theorem mem_lemma311GoodReal_iff_of_edgeMult {ε ρ β p : ℝ} {b b' : Path2} (c : C(ℝ, ℂ))
    (hmult : ∀ x y : ℤ, edgeMult ε b x y = edgeMult ε b' x y) :
    (b, c) ∈ GMSMain.EpsB.Lemma311GoodReal Prod.fst Prod.snd ε ρ β p ↔
      (b', c) ∈ GMSMain.EpsB.Lemma311GoodReal Prod.fst Prod.snd ε ρ β p := by
  simp only [GMSMain.EpsB.Lemma311GoodReal, Set.mem_ofPred_eq]
  exact exists_lemma311Holds_iff_of_edgeMult c hmult

/-- **The good event of [18] Lemma 3.11 as a set of pairs (curve, edge multiplicities)**: the
pairs `(c, m)` such that some boundary-length path with edge multiplicities `m` at mesh `ε` lies,
together with `c`, in the good event. -/
def lemma311GoodSet (ε ρ β p : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {q | ∃ b : Path2, (∀ x y, edgeMult ε b x y = q.2 x y) ∧
    (b, q.1) ∈ GMSMain.EpsB.Lemma311GoodReal Prod.fst Prod.snd ε ρ β p}

/-- **The good event of [18] Lemma 3.11 is the preimage of `lemma311GoodSet` under
`ω ↦ (η ω, edgeMult ε (bm ω))`.** -/
theorem lemma311GoodReal_eq_preimage {Ω : Type*} (bm : Ω → Path2) (η : Ω → C(ℝ, ℂ))
    (ε ρ β p : ℝ) :
    GMSMain.EpsB.Lemma311GoodReal bm η ε ρ β p =
      (fun ω => (η ω, fun x y => edgeMult ε (bm ω) x y)) ⁻¹' lemma311GoodSet ε ρ β p := by
  ext ω
  simp only [Set.mem_preimage, lemma311GoodSet, Set.mem_ofPred_eq]
  constructor
  · intro hω
    exact ⟨bm ω, fun _ _ => rfl, hω⟩
  · rintro ⟨b, hb, hgood⟩
    exact (mem_lemma311GoodReal_iff_of_edgeMult (b' := bm ω) (η ω) hb).1 hgood

end MatedCRT

end MatedCRTHarmonic
