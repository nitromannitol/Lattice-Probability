import LatticeProb.Prob.Percolation.FiniteGradientBondDeletion
import LatticeProb.Prob.Percolation.LatticeIncidentCard

/-!
# A nonconstant finite-energy consumer on the fully open plane

The indicator of the actual origin has integer drops and finite ordered energy.
Its canonical patch is exactly the four incident bonds. The flip changes the configuration
and isolates the origin, with the exact induced deletion equality on the full old carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation.FiniteGradientConsumer

open scoped BigOperators

noncomputable section

/-- The actual infinite component of the fully open plane. -/
abbrev planeComponent := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)

/-- Every ambient vertex belongs to this actual component. -/
def planeVertex (x : Vertex 2) : planeComponent :=
  ⟨x, by
    change x ∈ (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    exact Set.mem_univ x⟩

/-- The real indicator of the actual origin. -/
def originIndicator (x : planeComponent) : ℝ := by
  classical
  exact if x = planeVertex 0 then 1 else 0

/-- An indicator drop is integer on every actual component edge. -/
theorem originIndicator_integer (x y : planeComponent)
    (_hxy : (componentGraph planeComponent).Adj x y) :
    ∃ z : ℤ, originIndicator x - originIndicator y = (z : ℝ) := by
  classical
  unfold originIndicator
  split_ifs
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- For adjacent vertices the indicator changes exactly on edges incident to the origin. -/
theorem originIndicator_ne_iff {x y : planeComponent}
    (hxy : (componentGraph planeComponent).Adj x y) :
    originIndicator x ≠ originIndicator y ↔ x = planeVertex 0 ∨ y = planeVertex 0 := by
  classical
  have hne := hxy.ne
  by_cases hx : x = planeVertex 0 <;> by_cases hy : y = planeVertex 0 <;>
    simp_all only [originIndicator, if_pos, if_neg, ne_eq, one_ne_zero, zero_ne_one,
      not_false_eq_true, or_true, or_false, not_true_eq_false]

/-- The energy is supported on the finite ordered list of edges incident to the origin. -/
theorem originIndicator_energy :
    ∃ M : ℝ, ∀ A : Finset (planeComponent × planeComponent),
      (∀ e ∈ A, (componentGraph planeComponent).Adj e.1 e.2) →
        ∑ e ∈ A, (originIndicator e.1 - originIndicator e.2) ^ 2 ≤ M := by
  classical
  let N := (componentGraph planeComponent).neighborFinset (planeVertex 0)
  let T := N.image (fun y => (planeVertex 0, y)) ∪ N.image (fun x => (x, planeVertex 0))
  let f := fun e : planeComponent × planeComponent =>
    (originIndicator e.1 - originIndicator e.2) ^ 2
  refine ⟨∑ e ∈ T, f e, ?_⟩
  intro A hA
  have hzero : ∀ e ∈ A, e ∉ T → f e = 0 := by
    intro e he hnot
    have heq : originIndicator e.1 = originIndicator e.2 := by
      by_contra hne
      rcases (originIndicator_ne_iff (hA e he)).mp hne with hx | hy
      · apply hnot
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨e.2, (SimpleGraph.mem_neighborFinset _ _ _).mpr (hx ▸ hA e he), Prod.ext hx.symm rfl⟩)
      · apply hnot
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨e.1, (SimpleGraph.mem_neighborFinset _ _ _).mpr (hy ▸ (hA e he).symm),
            Prod.ext rfl hy.symm⟩)
    simp only [f, heq, sub_self, zero_pow (by decide : 2 ≠ 0)]
  calc
    ∑ e ∈ A, f e ≤ ∑ e ∈ A ∪ T, f e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun _ _ _ => sq_nonneg _)
    _ = ∑ e ∈ T, f e := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro e he hnot
      exact hzero e ((Finset.mem_union.mp he).resolve_right hnot) hnot

/-- The exact gradient-edge set for the nonconstant indicator is finite. -/
theorem originIndicator_edges_finite :
    (componentGradientEdges planeComponent originIndicator).Finite :=
  componentGradientEdges_finite_of_integer_energy planeComponent originIndicator
    originIndicator_integer originIndicator_energy

/-- The canonical, genuinely nonempty patch for the indicator. -/
def originPatch : Finset (Bond 2) :=
  componentGradientPatch planeComponent originIndicator originIndicator_edges_finite

/-- A genuine bond is selected exactly when one of its endpoints is the origin. -/
theorem mem_originPatch (e : Bond 2) :
    e ∈ originPatch ↔ (0 : Vertex 2) ∈ e.val := by
  rw [originPatch, mem_componentGradientPatch]
  constructor
  · rintro ⟨x, y, he, hxy, hne⟩
    rw [he, Sym2.mem_iff]
    rcases (originIndicator_ne_iff hxy).mp hne with hx | hy
    · exact Or.inl (congrArg Subtype.val hx).symm
    · exact Or.inr (congrArg Subtype.val hy).symm
  · intro he
    obtain ⟨x, y, heq, hdist⟩ := e.property
    have hxy : (componentGraph planeComponent).Adj (planeVertex x) (planeVertex y) :=
      ⟨lattice_adj_iff_l1Dist.mpr hdist, rfl⟩
    refine ⟨planeVertex x, planeVertex y, heq, hxy, (originIndicator_ne_iff hxy).mpr ?_⟩
    rw [heq, Sym2.mem_iff] at he
    exact he.elim (fun hx => Or.inl (congrArg planeVertex hx.symm))
      (fun hy => Or.inr (congrArg planeVertex hy.symm))

/-- The ambient image is exactly the usual radius-zero incident-bond enumeration. -/
theorem originPatch_image :
    originPatch.image Subtype.val = LatticeIncident.incidentBonds 2 0 := by
  classical
  ext e
  rw [Finset.mem_image, LatticeIncident.mem_incidentBonds]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨x, y, he, hd⟩ := b.property
    have hor := (mem_originPatch b).mp hb
    rw [he, Sym2.mem_iff] at hor
    have hxy := lattice_adj_iff_l1Dist.mpr hd
    rcases hor with hx | hy
    · subst x
      exact ⟨0, by
        rw [LatticeIncident.mem_centered_box]
        intro i
        exact ⟨by norm_num, by norm_num⟩, y, hxy, he.symm⟩
    · subst y
      exact ⟨0, by
        rw [LatticeIncident.mem_centered_box]
        intro i
        exact ⟨by norm_num, by norm_num⟩, x, hxy.symm, Sym2.eq_swap.trans he.symm⟩
  · rintro ⟨x, hx, y, hxy, he⟩
    have hx0 : x = 0 := by
      have hb := LatticeIncident.mem_centered_box.mp hx
      funext i
      have hi := hb i
      simpa only [Pi.zero_apply] using (show x i = 0 by simpa using le_antisymm hi.2 hi.1)
    subst x
    refine ⟨bondOfAdjacent hxy, (mem_originPatch _).mpr ?_, he⟩
    exact Sym2.mem_mk_left _ _

/-- Four undirected open bonds are deleted, rather than an empty or constant test. -/
theorem originPatch_card : originPatch.card = 4 := by
  classical
  rw [← Finset.card_image_of_injective originPatch Subtype.val_injective,
    originPatch_image, LatticeIncident.card_incidentBonds_two_zero]

/-- Every bond in this nonempty patch is open. -/
theorem originPatch_all_open : ∀ e ∈ originPatch, allOpen 2 e = true := fun _ _ => rfl

/-- The nonconstant indicator takes distinct values at legitimate neighboring vertices. -/
theorem originIndicator_nonconstant :
    originIndicator (planeVertex 0) ≠ originIndicator (planeVertex (unit (0 : Fin 2))) := by
  have hxy : (componentGraph planeComponent).Adj
      (planeVertex 0) (planeVertex (unit (0 : Fin 2))) := allOpen_two_unit_adj
  exact (originIndicator_ne_iff hxy).mpr (Or.inl rfl)

/-- The nonempty patch actually changes the configuration. -/
theorem originPatch_flip_ne : finiteBondFlip originPatch (allOpen 2) ≠ allOpen 2 := by
  classical
  have hcard := originPatch_card
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < originPatch.card by omega)
  intro h
  have hc := congrFun h e
  simp only [finiteBondFlip, BernoulliFiniteFlip.flip, he, if_pos, allOpen,
    Bool.not_true, Bool.false_eq_true] at hc

/-- The whole old subtype graph is precisely the canonical gradient-edge deletion. -/
theorem originPatch_induce_eq :
    (openGraph (finiteBondFlip originPatch (allOpen 2))).induce planeComponent.supp =
      (componentGraph planeComponent).deleteEdges
        (componentGradientEdges planeComponent originIndicator) :=
  componentGradientPatch_induce_eq_deleteEdges planeComponent originIndicator
    originIndicator_edges_finite

/-- The actual origin is isolated after deleting its four incident bonds. -/
theorem originPatch_origin_isolated (y : planeComponent) :
    ¬ ((openGraph (finiteBondFlip originPatch (allOpen 2))).induce planeComponent.supp).Adj
      (planeVertex 0) y := by
  rw [originPatch_induce_eq, SimpleGraph.deleteEdges_adj]
  rintro ⟨hxy, hnot⟩
  exact hnot ⟨planeVertex 0, y, rfl, hxy, (originIndicator_ne_iff hxy).mpr (Or.inl rfl)⟩

/-- The explicit consumer is zero outside its singleton exceptional set. -/
theorem originIndicator_cofinite :
    ∀ x : planeComponent, x ∉ ({planeVertex 0} : Finset planeComponent) →
      originIndicator x = 0 := by
  classical
  intro x hx
  exact if_neg (Finset.notMem_singleton.mp hx)

end

end LatticeProb.Percolation.FiniteGradientConsumer
