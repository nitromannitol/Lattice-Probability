import LatticeProb.Lattice.Planar.ExteriorBoundaryCochain
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Clusters

/-!
# Visibility from infinity

The set of vertices admitting an injective ray avoiding a given set is closed under adjoining
edges that avoid the set.
-/

set_option autoImplicit false

namespace LatticeProb.Lattice.Planar

open HigherDimLFPP.Perc

/-- The sum-of-distances and unit-vector formulations of nearest-neighbour adjacency agree. -/
lemma lAdj_iff_lattice_adj {d : ℕ} {x y : Site d} : LAdj x y ↔ (lattice d).Adj x y := by
  constructor
  · intro h
    exact h.exists_eq_add_single
  · rintro ⟨i, h | h⟩
    · subst y
      exact lAdj_add_single x i
    · subst x
      exact (lAdj_add_single y i).symm

/-- Vertices from which there is an injective path avoiding `D`. -/
def visible {V : Type*} (G : SimpleGraph V) (D : Set V) (x : V) : Prop :=
  ∃ p : ℕ → V, Function.Injective p ∧ p 0 = x ∧ ∀ n, p n ∉ D ∧ G.Adj (p n) (p (n + 1))

lemma visible_notMem {V : Type*} {G : SimpleGraph V} {D : Set V} {x : V}
    (hx : visible G D x) : x ∉ D := by
  obtain ⟨p, -, hp0, hp⟩ := hx
  rw [← hp0]
  exact (hp 0).1

/-- Visibility persists along an edge avoiding the set. -/
lemma visible_of_adj {V : Type*} {G : SimpleGraph V} {D : Set V} {x y : V}
    (hx : visible G D x) (hy : y ∉ D) (hxy : G.Adj x y) : visible G D y := by
  classical
  obtain ⟨p, hp, hp0, hpstep⟩ := hx
  by_cases h : y ∈ Set.range p
  · obtain ⟨m, hm⟩ := h
    refine ⟨fun n => p (m + n), ?_, ?_, ?_⟩
    · intro a b hab
      have := hp hab
      omega
    · simpa using hm
    · intro n
      have hn := hpstep (m + n)
      simpa [Nat.add_assoc] using hn
  · let q : ℕ → V := fun n => Nat.casesOn n y p
    have hq0 : q 0 = y := rfl
    have hqsucc : ∀ n, q (n + 1) = p n := fun _ => rfl
    refine ⟨q, ?_, hq0, ?_⟩
    · intro a b hab
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ b =>
          exfalso
          apply h
          exact ⟨b, by simpa [hq0, hqsucc] using hab.symm⟩
      | succ a =>
        cases b with
        | zero =>
          exfalso
          apply h
          exact ⟨a, by simpa [hq0, hqsucc] using hab⟩
        | succ b =>
          congr 1
          apply hp
          simpa [hqsucc] using hab
    · intro n
      cases n with
      | zero =>
        simp only [hq0, hqsucc]
        exact ⟨hy, by simpa [hp0] using hxy.symm⟩
      | succ n =>
        simpa [hqsucc, Nat.succ_eq_add_one] using hpstep n

/-- A bounded lattice box contains only finitely many sites. -/
lemma finite_withinInf_box {d : ℕ} (R : ℤ) :
    {x : Zd d | WithinInf R x 0}.Finite := by
  have hf : {x : Zd d | ∀ i, x i ∈ Set.Icc (-R) R}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc (-R) R)
  apply hf.subset
  intro x hx i
  have h := hx i
  simpa [WithinInf, abs_le] using h

/-- A visible site lies in the box exterior of a finite set contained in the box. -/
lemma visible_mem_ext {d : ℕ} (hd : 2 ≤ d) {D : Set (Site d)} {R : ℤ}
    (hD : ∀ x ∈ D, WithinInf R x 0) {x : Site d}
    (hx : visible (lattice d) D x) : x ∈ Ext R D := by
  obtain ⟨p, hp, hp0, hpath⟩ := hx
  have hout : ∃ n, ¬ WithinInf R (p n) 0 := by
    by_contra h
    push Not at h
    have hrange : Set.range p ⊆ {x : Zd d | WithinInf R x 0} := by
      rintro _ ⟨n, rfl⟩
      exact h n
    exact (Set.infinite_range_of_injective hp) ((finite_withinInf_box R).subset hrange)
  obtain ⟨n, hn⟩ := hout
  have hreach : ∀ n, Relation.ReflTransGen (StepIn Dᶜ LAdj) (p 0) (p n) := by
    intro k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      exact ih.tail ⟨(hpath k).1, (hpath (k + 1)).1, lAdj_iff_lattice_adj.mpr (hpath k).2⟩
  rw [← hp0]
  exact (hreach n).trans (mem_ext_of_not_withinInf hd hD hn)

/-- An avoiding path starting at a visible site consists entirely of visible sites. -/
lemma reflTransGen_stepIn_visible {d : ℕ} {D : Set (Site d)} {x y : Site d}
    (hx : visible (lattice d) D x) (h : Relation.ReflTransGen (StepIn Dᶜ LAdj) x y) :
    Relation.ReflTransGen (StepIn {z | visible (lattice d) D z} LAdj) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v _ huv ih =>
    have hu : visible (lattice d) D u := mem_of_reflTransGen_stepIn ih hx
    have hv := visible_of_adj hu huv.2.1 (lAdj_iff_lattice_adj.mp huv.2.2)
    exact ih.tail ⟨hu, hv, huv.2.2⟩

/-- The visible exterior of a bounded set is nearest-neighbour connected in dimension at least
two. -/
lemma visible_connected {d : ℕ} (hd : 2 ≤ d) {D : Set (Site d)} {R : ℤ}
    (hD : ∀ x ∈ D, WithinInf R x 0) :
    ConnIn {x | visible (lattice d) D x} LAdj := by
  intro x hx y hy
  have hxE := visible_mem_ext hd hD hx
  have hyE := visible_mem_ext hd hD hy
  exact reflTransGen_stepIn_visible hx (hxE.trans (reflTransGen_lAdj_symm hyE))

/-- A finite set of lattice sites is contained in a bounded box. -/
lemma finite_subset_withinInf {d : ℕ} {D : Set (Site d)} (hD : D.Finite) :
    ∃ R : ℤ, ∀ x ∈ D, WithinInf R x 0 := by
  classical
  have hfinite : {n : ℕ | ∃ x ∈ D, ∃ i : Fin d, n = (x i).natAbs}.Finite := by
    apply (hD.biUnion fun x _ => Set.finite_range fun i : Fin d => (x i).natAbs).subset
    rintro n ⟨x, hx, i, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hx, i, rfl⟩
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  refine ⟨N, ?_⟩
  intro x hx i
  have hi : (x i).natAbs ≤ N := hN ⟨x, hx, i, rfl⟩
  simpa [WithinInf, Int.natCast_natAbs] using (show ((x i).natAbs : ℤ) ≤ N by exact_mod_cast hi)

end LatticeProb.Lattice.Planar
