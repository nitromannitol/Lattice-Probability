import LatticeProb.Prob.Percolation.LatticeCube

/-!
# Paths in lattice cubes

Coordinate steps in the all-open graph can be taken without leaving a closed
lattice cube when their integer coordinates remain between its endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- Moving one coordinate upward within its integer interval gives a path inside the cube. -/
theorem latticeCube_reachable_update_up (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (x : {z : Vertex d // z ∈ latticeCube c r}) (i : Fin d) (t : ℤ)
    (hxt : x.val i ≤ t) (ht : t ≤ ⌊c i + r.val⌋) :
    ∃ y : {z : Vertex d // z ∈ latticeCube c r},
      y.val = Function.update x.val i t ∧
      ((openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))).Reachable x y := by
  classical
  let z (n : ℕ) : Vertex d := Function.update x.val i (x.val i + n)
  have hx := (mem_latticeCubeSet_iff c r x.val).mp
    ((finite_latticeCubeSet c r).mem_toFinset.mp x.property)
  have hz (n : ℕ) (hn : x.val i + (n : ℤ) ≤ t) : z n ∈ latticeCube c r := by
    apply (finite_latticeCubeSet c r).mem_toFinset.mpr
    apply (mem_latticeCubeSet_iff c r (z n)).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp only [z, Function.update_self]
      have hxi := hx i
      constructor <;> omega
    · simpa [z, Function.update_of_ne hji] using hx j
  let G := (openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))
  have hwalk (n : ℕ) : ∀ hn : x.val i + (n : ℤ) ≤ t,
      G.Reachable x ⟨z n, hz n hn⟩ := by
    induction n with
    | zero =>
        intro hn
        have heq : (⟨z 0, hz 0 hn⟩ : {z : Vertex d // z ∈ latticeCube c r}) = x := by
          apply Subtype.ext
          simp [z]
        rw [heq]
    | succ n ih =>
        intro hn
        have hn' : x.val i + (n : ℤ) ≤ t := by omega
        apply (ih hn').trans
        apply SimpleGraph.Adj.reachable
        change (openGraph (allOpen d)).Adj (z n) (z (n + 1))
        rw [openGraph_allOpen]
        apply Graph.Zd.adj_iff.mpr
        refine ⟨i, Or.inl ?_⟩
        funext j
        by_cases hji : j = i
        · subst j
          simp [z, LatticeProb.unit]
          omega
        · simp [z, Function.update_of_ne hji, LatticeProb.unit, Pi.single_eq_of_ne hji]
  let k := (t - x.val i).toNat
  have hk : x.val i + (k : ℤ) = t := by
    dsimp [k]
    have := Int.toNat_of_nonneg (sub_nonneg.mpr hxt)
    omega
  have hk' : x.val i + (k : ℤ) ≤ t := le_of_eq hk
  refine ⟨⟨z k, hz k hk'⟩, ?_, hwalk k hk'⟩
  simp [z, hk]

/-- Moving either way in one coordinate remains within the cube. -/
theorem latticeCube_reachable_update (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (x : {z : Vertex d // z ∈ latticeCube c r}) (i : Fin d) (t : ℤ)
    (htl : ⌈c i - r.val⌉ ≤ t) (htu : t ≤ ⌊c i + r.val⌋) :
    ∃ y : {z : Vertex d // z ∈ latticeCube c r},
      y.val = Function.update x.val i t ∧
      ((openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))).Reachable x y := by
  classical
  by_cases hxt : x.val i ≤ t
  · exact latticeCube_reachable_update_up c r x i t hxt htu
  · have hx := (mem_latticeCubeSet_iff c r x.val).mp
      ((finite_latticeCubeSet c r).mem_toFinset.mp x.property)
    have hy : Function.update x.val i t ∈ latticeCube c r := by
      apply (finite_latticeCubeSet c r).mem_toFinset.mpr
      apply (mem_latticeCubeSet_iff c r _).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa using And.intro htl htu
      · simpa [Function.update_of_ne hji] using hx j
    let y : {z : Vertex d // z ∈ latticeCube c r} := ⟨Function.update x.val i t, hy⟩
    have hyx : y.val i ≤ x.val i := by
      simpa [y] using le_of_lt (lt_of_not_ge hxt)
    obtain ⟨z, hz, hreach⟩ := latticeCube_reachable_update_up c r y i (x.val i) hyx (hx i).2
    have hzx : z = x := by
      apply Subtype.ext
      rw [hz]
      funext j
      by_cases hji : j = i
      · subst j
        simp [y]
      · simp [y, Function.update_of_ne hji]
    refine ⟨y, rfl, ?_⟩
    rw [hzx] at hreach
    exact hreach.symm

/-- Any two cube vertices are connected by an all-open path inside the cube. -/
theorem latticeCube_allOpen_preconnected (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ)) :
    ((openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))).Preconnected := by
  classical
  intro x y
  let G := (openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))
  have hx := (mem_latticeCubeSet_iff c r x.val).mp
    ((finite_latticeCubeSet c r).mem_toFinset.mp x.property)
  have hy := (mem_latticeCubeSet_iff c r y.val).mp
    ((finite_latticeCubeSet c r).mem_toFinset.mp y.property)
  let mix (s : Finset (Fin d)) : Vertex d := fun j => if j ∈ s then y.val j else x.val j
  have hm (s : Finset (Fin d)) : mix s ∈ latticeCube c r := by
    apply (finite_latticeCubeSet c r).mem_toFinset.mpr
    apply (mem_latticeCubeSet_iff c r _).mpr
    intro j
    by_cases hj : j ∈ s
    · simpa [mix, hj] using hy j
    · simpa [mix, hj] using hx j
  have hr (s : Finset (Fin d)) : G.Reachable x ⟨mix s, hm s⟩ := by
    induction s using Finset.induction_on with
    | empty =>
        have heq : (⟨mix ∅, hm ∅⟩ : {z : Vertex d // z ∈ latticeCube c r}) = x := by
          apply Subtype.ext
          funext j
          simp [mix]
        rw [heq]
    | @insert i s hi ih =>
        obtain ⟨z, hz, hstep⟩ := latticeCube_reachable_update c r ⟨mix s, hm s⟩
          i (y.val i) (hy i).1 (hy i).2
        have heq : z = ⟨mix (insert i s), hm (insert i s)⟩ := by
          apply Subtype.ext
          rw [hz]
          funext j
          by_cases hji : j = i
          · subst j
            simp [mix]
          · simp [mix, hji]
        rw [heq] at hstep
        exact ih.trans hstep
  have heq : (⟨mix Finset.univ, hm Finset.univ⟩ :
      {z : Vertex d // z ∈ latticeCube c r}) = y := by
    apply Subtype.ext
    funext j
    simp [mix]
  rw [← heq]
  exact hr Finset.univ

/-- A nonempty lattice cube induces a connected all-open graph. -/
theorem latticeCube_allOpen_connected (c : Fin d → ℝ) (r : Set.Ioi (0 : ℝ))
    (h : (latticeCube c r).Nonempty) :
    ((openGraph (allOpen d)).induce (latticeCube c r : Set (Vertex d))).Connected := by
  obtain ⟨x, hx⟩ := h
  letI : Nonempty {z : Vertex d // z ∈ latticeCube c r} := ⟨⟨x, hx⟩⟩
  exact ⟨latticeCube_allOpen_preconnected c r⟩

end
end LatticeProb.Percolation
