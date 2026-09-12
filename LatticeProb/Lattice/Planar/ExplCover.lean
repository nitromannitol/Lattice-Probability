/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.DualGeom

open Finset

namespace LatticeProb.Lattice.Planar

/-- Reachability from `x` to `y` through faces outside `V`. -/
def AvoidReach (V : Finset Site) (x y : Site) : Prop :=
  Relation.ReflTransGen (fun a b => a ∉ V ∧ b ∉ V ∧ squareGraph.Adj a b) x y

theorem AvoidReach.notMem {V : Finset Site} {x y : Site} (hx : x ∉ V) (h : AvoidReach V x y) :
    y ∉ V := by
  induction h with
  | refl => exact hx
  | tail _ hbc _ => exact hbc.2.1

theorem reachable_induce_of_avoidReach (V : Finset Site) {x y : Site} (h : AvoidReach V x y)
    (hx : x ∉ V) (hy : y ∉ V) :
    (squareGraph.induce {z : Site | z ∉ V}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    have hb : b ∉ V := hbc.1
    refine (ih hb).trans (SimpleGraph.Adj.reachable ?_)
    exact hbc.2.2

theorem avoidReach_of_reachable_induce (V : Finset Site) :
    ∀ (p q : {z : Site // z ∉ V}), (squareGraph.induce {z : Site | z ∉ V}).Reachable p q →
      AvoidReach V p.1 q.1 := by
  intro p q h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ⟨b.2, c.2, hbc⟩

theorem inFiniteComponent_iff (V : Finset Site) (y : Site) :
    InFiniteComponent V y ↔ y ∉ V ∧ Set.Finite {z | AvoidReach V y z} := by
  unfold InFiniteComponent
  constructor
  · rintro ⟨hy, hfin⟩
    refine ⟨hy, hfin.subset ?_⟩
    intro z hz
    have hz' : z ∉ V := AvoidReach.notMem hy hz
    exact ⟨hz', hy, reachable_induce_of_avoidReach V hz hy hz'⟩
  · rintro ⟨hy, hfin⟩
    refine ⟨hy, hfin.subset ?_⟩
    rintro z ⟨hz, hy', hr⟩
    exact avoidReach_of_reachable_induce V ⟨y, hy'⟩ ⟨z, hz⟩ hr

theorem InFiniteComponent.mono {V V' : Finset Site} (hVV' : V ⊆ V') {y : Site}
    (h : InFiniteComponent V y) : y ∈ V' ∨ InFiniteComponent V' y := by
  by_cases hy : y ∈ V'
  · exact Or.inl hy
  right
  rw [inFiniteComponent_iff] at h ⊢
  refine ⟨hy, h.2.subset ?_⟩
  intro z hz
  exact Relation.ReflTransGen.mono
    (fun a b hab => ⟨fun h => hab.1 (hVV' h), fun h => hab.2.1 (hVV' h), hab.2.2⟩) _ _ hz

theorem InFiniteComponent.adj {V : Finset Site} {x y : Site} (h : InFiniteComponent V x)
    (hxy : squareGraph.Adj x y) : y ∈ V ∨ InFiniteComponent V y := by
  by_cases hy : y ∈ V
  · exact Or.inl hy
  right
  rw [inFiniteComponent_iff] at h ⊢
  refine ⟨hy, h.2.subset ?_⟩
  intro z hz
  exact (Relation.ReflTransGen.single ⟨h.1, hy, hxy⟩).trans hz

theorem edgesFrom_cover (f : Site) {d : Site} (hd : IsUnit d) {y : Site}
    (h : squareGraph.Adj f y) : (f, y) ∈ edgesFrom f d := by
  have hy : y = f + (y - f) := by abel
  rcases isUnit_of_adj h with hu | hu | hu | hu <;> rw [hu] at hy <;> subst hy <;>
  rcases hd with rfl | rfl | rfl | rfl <;> simp [edgesFrom, rotL]

theorem continuations_cover {a b : Site} (h : squareGraph.Adj a b) {y : Site}
    (hy : squareGraph.Adj b y) : y = a ∨ (b, y) ∈ continuations a b := by
  have hb : b = a + (b - a) := by abel
  have hy' : y = b + (y - b) := by abel
  rcases isUnit_of_adj hy with hu | hu | hu | hu <;> rw [hu] at hy' <;> subst hy' <;>
  rcases isUnit_of_adj h with hu' | hu' | hu' | hu' <;> rw [hu'] at hb <;> subst hb <;>
  simp [continuations, rotL, rotR, Prod.ext_iff]

end LatticeProb.Lattice.Planar
