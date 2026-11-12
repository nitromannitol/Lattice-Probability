import LatticeProb.Topology.PlaneTopology

/-!
# Separation of a frontier by a crosscut

The set-topological part of the crosscut argument in the proof of Torhorst's theorem (Torhorst (1921); Whyburn,
*Analytic Topology*, Chapter VI; Kuratowski, *Topology* II, §61). Let `C` be an open set and `γ` a closed set; in
the application `C` is a complementary domain of a locally connected plane continuum and `γ` is a crosscut of `C`
(an arc through `C` joining two points of its frontier).

* `closure_connectedComponentIn_inter_subset`: the closure of a component of a set `O` meets `O` only inside the
  component.
* `not_isPreconnected_of_closure_components`: if `E ⊆ closure O`, `O` is not connected, the closure of every
  component of `O` meets `E`, no point of `E` lies in the closures of two distinct components of `O`, and the
  components of `O` are locally finite at the points of `E`, then `E` is not connected.
* `closure_inter_frontier_diff_nonempty`: when `γᶜ` is connected and `C ∪ γ` is not the whole space, the closure of
  every component of `C \ γ` meets `frontier C \ γ`.
* `not_isPreconnected_frontier_diff_of_crosscut`: the combination for `O = C \ γ` and `E = frontier C \ γ`.
-/

open Set
open scoped Topology

namespace LatticeProb.Topology

variable {α : Type*} [TopologicalSpace α]

/-- The closure of the component of `u` in a set `O` meets `O` only inside that component. -/
theorem closure_connectedComponentIn_inter_subset (O : Set α) (u : α) :
    closure (connectedComponentIn O u) ∩ O ⊆ connectedComponentIn O u := by
  rintro y ⟨hyc, hyO⟩
  by_cases hu : u ∈ O
  · have hpre : IsPreconnected (insert y (connectedComponentIn O u)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hyc subset_closure)
    exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hu))
      (insert_subset hyO (connectedComponentIn_subset O u)) (mem_insert _ _)
  · rw [connectedComponentIn_eq_empty hu, closure_empty] at hyc
    exact hyc.elim

/-- **Separation by the closures of components.** Let `E ⊆ closure O`. Suppose that `O` is not preconnected, that
the closure of every component of `O` meets `E`, that no point of `E` lies in the closures of two distinct components
of `O`, and that every point of `E` has a neighbourhood met by only finitely many components of `O`. Then `E` is not
preconnected: the points of `E` in the closure of one component form a nonempty proper relatively clopen subset. -/
theorem not_isPreconnected_of_closure_components {O E : Set α} (hO : ¬ IsPreconnected O)
    (hE : E ⊆ closure O) (hmeet : ∀ U ∈ connectedComponentsIn O, (closure U ∩ E).Nonempty)
    (hkey : ∀ x ∈ E, ∀ U ∈ connectedComponentsIn O, ∀ V ∈ connectedComponentsIn O,
      x ∈ closure U → x ∈ closure V → U = V)
    (hfin : ∀ x ∈ E, ∃ N ∈ 𝓝 x, {U ∈ connectedComponentsIn O | (U ∩ N).Nonempty}.Finite) :
    ¬ IsPreconnected E := by
  obtain ⟨z, hz⟩ : O.Nonempty := by
    by_contra h
    exact hO (by rw [not_nonempty_iff_eq_empty.1 h]; exact isPreconnected_empty)
  set U₀ := connectedComponentIn O z with hU₀
  have hU₀m : U₀ ∈ connectedComponentsIn O := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwU⟩ : ∃ w ∈ O, connectedComponentIn O w ≠ U₀ := by
    by_contra h
    push Not at h
    apply hO
    have hOU : O = U₀ := Subset.antisymm
      (fun v hv => by rw [← h v hv]; exact mem_connectedComponentIn hv) (connectedComponentIn_subset O z)
    rw [hOU]
    exact isPreconnected_connectedComponentIn
  -- the points of `E` in `closure U₀` form a relatively open subset of `E`
  have hloc : ∀ x ∈ E, x ∈ closure U₀ → ∃ N' ∈ 𝓝 x, E ∩ N' ⊆ closure U₀ := by
    intro x hxE hxU
    obtain ⟨N, hN, hNfin⟩ := hfin x hxE
    set S := {U ∈ connectedComponentsIn O | (U ∩ N).Nonempty} with hS
    have hSfin : (S \ {U₀}).Finite := hNfin.subset sdiff_subset
    set T := ⋃ U ∈ S \ {U₀}, closure U with hT
    have hTc : IsClosed T := hSfin.isClosed_biUnion fun U _ => isClosed_closure
    have hxT : x ∉ T := by
      rw [hT, mem_iUnion₂]
      rintro ⟨U, ⟨⟨hU, -⟩, hne⟩, hxU'⟩
      exact hne (hkey x hxE U hU U₀ hU₀m hxU' hxU)
    have hopen : IsOpen (interior N ∩ Tᶜ) := isOpen_interior.inter hTc.isOpen_compl
    refine ⟨interior N ∩ Tᶜ, hopen.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, hxT⟩, ?_⟩
    rintro y ⟨hyE, hyN⟩
    have hy : y ∈ closure ((interior N ∩ Tᶜ) ∩ O) := hopen.inter_closure ⟨hyN, hE hyE⟩
    have hsub : (interior N ∩ Tᶜ) ∩ O ⊆ U₀ ∪ ⋃ U ∈ S \ {U₀}, U := by
      rintro o ⟨⟨hoN, -⟩, hoO⟩
      by_cases ho : connectedComponentIn O o = U₀
      · left
        rw [← ho]
        exact mem_connectedComponentIn hoO
      · right
        exact mem_biUnion (x := connectedComponentIn O o)
          ⟨⟨⟨o, hoO, rfl⟩, ⟨o, mem_connectedComponentIn hoO, interior_subset hoN⟩⟩, ho⟩
          (mem_connectedComponentIn hoO)
    have hy' := closure_mono hsub hy
    rw [closure_union, hSfin.closure_biUnion] at hy'
    rcases hy' with h | h
    · exact h
    · exact (hyN.2 h).elim
  intro hEpre
  have hcov : E ⊆ interior (closure U₀ ∪ Eᶜ) ∪ (closure U₀)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ closure U₀
    · left
      obtain ⟨N', hN', hsub⟩ := hloc x hx hxU
      refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hN' fun y hy => ?_)
      by_cases hyE : y ∈ E
      · exact Or.inl (hsub ⟨hyE, hy⟩)
      · exact Or.inr hyE
    · exact Or.inr hxU
  have hdisj : E ∩ (interior (closure U₀ ∪ Eᶜ) ∩ (closure U₀)ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x ⟨hxE, hxi, hxU⟩ => ?_
    rcases interior_subset hxi with h | h
    · exact hxU h
    · exact h hxE
  rcases isPreconnected_iff_subset_of_disjoint.1 hEpre _ _ isOpen_interior isClosed_closure.isOpen_compl
    hcov hdisj with h | h
  · obtain ⟨y, hyV, hyE⟩ := hmeet _ ⟨w, hw, rfl⟩
    rcases interior_subset (h hyE) with h' | h'
    · exact hwU (hkey y hyE _ ⟨w, hw, rfl⟩ _ hU₀m hyV h')
    · exact h' hyE
  · obtain ⟨y, hyU, hyE⟩ := hmeet U₀ hU₀m
    exact h hyE hyU

/-- Each component of `C \ γ` reaches the frontier of `C` off `γ`, when `C` is open, `γ` is closed, `γᶜ` is
preconnected and `C ∪ γ` is not the whole space. Otherwise the component would be relatively clopen in `γᶜ`, hence
equal to `γᶜ`, which leaves `C`. -/
theorem closure_inter_frontier_diff_nonempty [LocallyConnectedSpace α] {C γ U : Set α} (hC : IsOpen C)
    (hγ : IsClosed γ) (hγc : IsPreconnected γᶜ) (hout : (Cᶜ \ γ).Nonempty)
    (hU : U ∈ connectedComponentsIn (C \ γ)) : (closure U ∩ (frontier C \ γ)).Nonempty := by
  obtain ⟨u, hu, rfl⟩ := hU
  have hUo : IsOpen (connectedComponentIn (C \ γ) u) := (hC.sdiff hγ).connectedComponentIn
  by_contra hne
  have hsub : γᶜ ⊆ connectedComponentIn (C \ γ) u := by
    refine hγc.subset_of_closure_inter_subset hUo ⟨u, hu.2, mem_connectedComponentIn hu⟩ ?_
    rintro y ⟨hyc, hyγ⟩
    by_cases hyC : y ∈ C
    · exact closure_connectedComponentIn_inter_subset _ _ ⟨hyc, hyC, hyγ⟩
    · have hyF : y ∈ frontier C := by
        rw [hC.frontier_eq]
        exact ⟨closure_mono ((connectedComponentIn_subset _ _).trans sdiff_subset) hyc, hyC⟩
      exact (hne ⟨y, hyc, hyF, hyγ⟩).elim
  obtain ⟨p, hpC, hpγ⟩ := hout
  exact hpC (connectedComponentIn_subset _ _ (hsub hpγ)).1

/-- **A crosscut separates the frontier.** Let `C` be open and `γ` closed in a locally connected space, with `γᶜ`
preconnected and `C ∪ γ` not the whole space. If `C \ γ` is not preconnected, no point of `frontier C \ γ` lies in
the closures of two distinct components of `C \ γ`, and the components of `C \ γ` are locally finite at the points
of `frontier C \ γ`, then `frontier C \ γ` is not preconnected. -/
theorem not_isPreconnected_frontier_diff_of_crosscut [LocallyConnectedSpace α] {C γ : Set α} (hC : IsOpen C)
    (hγ : IsClosed γ) (hγc : IsPreconnected γᶜ) (hout : (Cᶜ \ γ).Nonempty)
    (hsep : ¬ IsPreconnected (C \ γ))
    (hkey : ∀ x ∈ frontier C \ γ, ∀ U ∈ connectedComponentsIn (C \ γ),
      ∀ V ∈ connectedComponentsIn (C \ γ), x ∈ closure U → x ∈ closure V → U = V)
    (hfin : ∀ x ∈ frontier C \ γ, ∃ N ∈ 𝓝 x,
      {U ∈ connectedComponentsIn (C \ γ) | (U ∩ N).Nonempty}.Finite) :
    ¬ IsPreconnected (frontier C \ γ) := by
  refine not_isPreconnected_of_closure_components hsep (fun x hx => ?_)
    (fun U hU => closure_inter_frontier_diff_nonempty hC hγ hγc hout hU) hkey hfin
  have hx' := hγ.isOpen_compl.inter_closure ⟨hx.2, frontier_subset_closure hx.1⟩
  rwa [inter_comm, ← sdiff_eq] at hx'

end LatticeProb.Topology
