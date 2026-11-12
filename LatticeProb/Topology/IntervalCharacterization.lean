import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# The order characterisation of the unit interval

A nontrivial, densely ordered, complete linear order whose order topology is separable is order isomorphic,
hence homeomorphic, to the unit interval `[0, 1]` (Cantor; see Kuratowski, *Topology* II, §47, and Nadler,
*Continuum Theory*, Theorem 6.17, where it is the order-theoretic step of the characterisation of the arc).

* `exists_orderIso_extend_of_orderDense`: an order isomorphism between order-dense subsets of two complete linear
  orders extends to an order isomorphism of the complete orders (the extension is `x ↦ ⨆_{d ≤ x} g d`).
* `exists_countable_orderDense`: a separable densely ordered bounded linear order with an order-closed topology
  has a countable order-dense subset of the open interval `(⊥, ⊤)`.
* `nonempty_orderIso_of_separableSpace`: two nontrivial, densely ordered, complete linear orders with separable
  order topologies are order isomorphic.
* `nonempty_orderIso_unitInterval`, `nonempty_homeomorph_unitInterval`: the case of `[0, 1]`.
* `exists_isLUB_of_compactSpace`, `completeLinearOrderOfCompactSpace`: a compact linearly ordered space with its
  order topology is a complete linear order.
* `orderTopology_of_compactSpace`: a compact topology on a linear order in which all open rays are open is the
  order topology.
* `nonempty_homeomorph_unitInterval_of_compactSpace`, `nonempty_homeomorph_unitInterval_of_isOpen_rays`: a
  nontrivial, compact, connected, separable linearly ordered space (with its order topology, or with a compact
  topology in which the open rays are open) is homeomorphic to `[0, 1]`.
-/

namespace LatticeProb.Topology

open Set
open scoped _root_.Topology

variable {α β : Type*}

/-- An order isomorphism between order-dense subsets of two complete linear orders extends to an order
isomorphism of the complete linear orders. Here `D ⊆ α` is order dense if every nonempty open interval of `α`
meets `D`. -/
theorem exists_orderIso_extend_of_orderDense [CompleteLinearOrder α] [CompleteLinearOrder β]
    {D : Set α} {E : Set β} (hD : ∀ x y : α, x < y → ∃ d ∈ D, x < d ∧ d < y)
    (hE : ∀ x y : β, x < y → ∃ e ∈ E, x < e ∧ e < y) (g : D ≃o E) :
    ∃ F : α ≃o β, ∀ d : D, F d = g d := by
  classical
  set F : α → β := fun x => ⨆ (d : D) (_ : (d : α) ≤ x), (g d : β) with hFdef
  have hF_le : ∀ x (d : D), (d : α) ≤ x → (g d : β) ≤ F x := fun x d hd =>
    le_iSup₂_of_le (f := fun (d : D) (_ : (d : α) ≤ x) => (g d : β)) d hd le_rfl
  have hF_ub : ∀ (x : α) (d : D), x < (d : α) → F x ≤ g d := by
    intro x d hd
    refine iSup₂_le fun d' hd' => ?_
    have h : d' < d := show (d' : α) < d from lt_of_le_of_lt hd' hd
    exact (g.lt_iff_lt.2 h).le
  have hmono : StrictMono F := by
    intro x y hxy
    obtain ⟨m, -, hxm, hmy⟩ := hD x y hxy
    obtain ⟨d₁, hd₁, hxd₁, hd₁m⟩ := hD x m hxm
    obtain ⟨d₂, hd₂, hmd₂, hd₂y⟩ := hD m y hmy
    have h12 : (⟨d₁, hd₁⟩ : D) < ⟨d₂, hd₂⟩ := show d₁ < d₂ from hd₁m.trans hmd₂
    calc F x ≤ g ⟨d₁, hd₁⟩ := hF_ub x ⟨d₁, hd₁⟩ hxd₁
      _ < g ⟨d₂, hd₂⟩ := g.lt_iff_lt.2 h12
      _ ≤ F y := hF_le y ⟨d₂, hd₂⟩ hd₂y.le
  have hsurj : Function.Surjective F := by
    intro y
    set x : α := ⨆ (e : E) (_ : (e : β) ≤ y), (g.symm e : α) with hx
    refine ⟨x, le_antisymm ?_ ?_⟩
    · refine iSup₂_le fun d hd => ?_
      by_contra h
      push Not at h
      obtain ⟨e, he, hye, hed⟩ := hE y (g d) h
      have hxe : x ≤ g.symm ⟨e, he⟩ := by
        refine iSup₂_le fun e' he' => ?_
        have h' : e' ≤ (⟨e, he⟩ : E) := show (e' : β) ≤ e from he'.trans hye.le
        exact g.symm.monotone h'
      have hed' : g.symm ⟨e, he⟩ < d := by
        have h' : (⟨e, he⟩ : E) < g d := hed
        simpa using g.symm.lt_iff_lt.2 h'
      exact absurd (lt_of_le_of_lt (hd.trans hxe) hed') (lt_irrefl _)
    · by_contra h
      push Not at h
      obtain ⟨e, he, hxe, hey⟩ := hE _ y h
      have h1 : ((g.symm ⟨e, he⟩ : D) : α) ≤ x :=
        le_iSup₂_of_le (f := fun (e : E) (_ : (e : β) ≤ y) => (g.symm e : α)) ⟨e, he⟩ hey.le le_rfl
      have h2 := hF_le x _ h1
      simp only [OrderIso.apply_symm_apply] at h2
      exact absurd (lt_of_le_of_lt h2 hxe) (lt_irrefl _)
  refine ⟨StrictMono.orderIsoOfSurjective F hmono hsurj, fun d => ?_⟩
  change F d = g d
  refine le_antisymm (iSup₂_le fun d' hd' => ?_) (hF_le d d le_rfl)
  exact g.monotone (show d' ≤ d from hd')

/-- A separable, densely ordered, bounded linear order with an order-closed topology has a countable subset of
the open interval `(⊥, ⊤)` meeting every nonempty open interval. -/
theorem exists_countable_orderDense [LinearOrder α] [BoundedOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderClosedTopology α] [TopologicalSpace.SeparableSpace α] :
    ∃ D : Set α, D.Countable ∧ D ⊆ Ioo ⊥ ⊤ ∧ ∀ x y : α, x < y → ∃ d ∈ D, x < d ∧ d < y := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense α
  refine ⟨s ∩ Ioo ⊥ ⊤, hsc.mono inter_subset_left, inter_subset_right, fun x y hxy => ?_⟩
  obtain ⟨z, hzs, hxz, hzy⟩ := hsd.exists_between hxy
  exact ⟨z, ⟨hzs, lt_of_le_of_lt bot_le hxz, lt_of_lt_of_le hzy le_top⟩, hxz, hzy⟩

/-- A countable order-dense subset of `(⊥, ⊤)` in a nontrivial bounded linear order is, as an ordered type, a
nonempty countable dense linear order without endpoints. -/
theorem orderDense_subtype_props [LinearOrder α] [BoundedOrder α] [Nontrivial α] {D : Set α}
    (hDsub : D ⊆ Ioo ⊥ ⊤) (hD : ∀ x y : α, x < y → ∃ d ∈ D, x < d ∧ d < y) :
    DenselyOrdered D ∧ NoMinOrder D ∧ NoMaxOrder D ∧ Nonempty D := by
  refine ⟨⟨fun a b hab => ?_⟩, ⟨fun a => ?_⟩, ⟨fun a => ?_⟩, ?_⟩
  · obtain ⟨d, hd, had, hdb⟩ := hD a b hab
    exact ⟨⟨d, hd⟩, had, hdb⟩
  · obtain ⟨d, hd, -, hda⟩ := hD ⊥ a (hDsub a.2).1
    exact ⟨⟨d, hd⟩, hda⟩
  · obtain ⟨d, hd, had, -⟩ := hD a ⊤ (hDsub a.2).2
    exact ⟨⟨d, hd⟩, had⟩
  · obtain ⟨d, hd, -⟩ := hD ⊥ ⊤ bot_lt_top
    exact ⟨⟨d, hd⟩⟩

/-- **Order characterisation of the arc, order-theoretic step.** Two nontrivial, densely ordered, complete linear
orders whose order topologies are separable are order isomorphic. -/
theorem nonempty_orderIso_of_separableSpace
    [CompleteLinearOrder α] [DenselyOrdered α] [Nontrivial α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace.SeparableSpace α]
    [CompleteLinearOrder β] [DenselyOrdered β] [Nontrivial β] [TopologicalSpace β] [OrderTopology β]
    [TopologicalSpace.SeparableSpace β] :
    Nonempty (α ≃o β) := by
  obtain ⟨D, hDc, hDsub, hD⟩ := exists_countable_orderDense (α := α)
  obtain ⟨E, hEc, hEsub, hE⟩ := exists_countable_orderDense (α := β)
  obtain ⟨_, _, _, _⟩ := orderDense_subtype_props hDsub hD
  obtain ⟨_, _, _, _⟩ := orderDense_subtype_props hEsub hE
  have := hDc.to_subtype
  have := hEc.to_subtype
  obtain ⟨g⟩ := Order.iso_of_countable_dense D E
  obtain ⟨F, -⟩ := exists_orderIso_extend_of_orderDense hD hE g
  exact ⟨F⟩

/-- A nontrivial, densely ordered, complete linear order with separable order topology is order isomorphic to
the unit interval. -/
theorem nonempty_orderIso_unitInterval
    [CompleteLinearOrder α] [DenselyOrdered α] [Nontrivial α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace.SeparableSpace α] :
    Nonempty (α ≃o unitInterval) :=
  nonempty_orderIso_of_separableSpace

/-- A nontrivial, densely ordered, complete linear order with separable order topology is homeomorphic to the
unit interval. -/
theorem nonempty_homeomorph_unitInterval
    [CompleteLinearOrder α] [DenselyOrdered α] [Nontrivial α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace.SeparableSpace α] :
    Nonempty (α ≃ₜ unitInterval) :=
  let ⟨e⟩ := nonempty_orderIso_unitInterval (α := α)
  ⟨e.toHomeomorph⟩

/-- In a nonempty compact linearly ordered space with its order topology every set has a least upper bound. -/
theorem exists_isLUB_of_compactSpace [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [CompactSpace α]
    [Nonempty α] (s : Set α) : ∃ x, IsLUB s x := by
  obtain ⟨m, hm⟩ := isCompact_univ.exists_isGreatest (univ_nonempty (α := α))
  have hcl : IsClosed (upperBounds s) := by
    have h : upperBounds s = ⋂ a ∈ s, Ici a := by
      ext x
      simp [upperBounds]
    rw [h]
    exact isClosed_biInter fun a _ => isClosed_Ici
  have hne : (upperBounds s).Nonempty := ⟨m, fun a _ => hm.2 (mem_univ a)⟩
  exact hcl.isCompact.exists_isLeast hne

/-- The complete linear order structure of a nonempty compact linearly ordered space with its order topology. -/
noncomputable abbrev completeLinearOrderOfCompactSpace (α : Type*) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [CompactSpace α] [Nonempty α] : CompleteLinearOrder α :=
  letI : SupSet α := ⟨fun s => Classical.choose (exists_isLUB_of_compactSpace s)⟩
  letI : CompleteLattice α :=
    completeLatticeOfSup α fun s => Classical.choose_spec (exists_isLUB_of_compactSpace s)
  { (inferInstance : LinearOrder α), LinearOrder.toBiheytingAlgebra α,
    (inferInstance : CompleteLattice α) with }

/-- The order topology of a linear order is Hausdorff. -/
theorem t2Space_preorderTopology (α : Type*) [LinearOrder α] : @T2Space α (Preorder.topology α) :=
  letI := Preorder.topology α
  haveI : OrderTopology α := ⟨rfl⟩
  inferInstance

/-- A compact topology on a linear order in which every open ray is open is the order topology. -/
theorem orderTopology_of_compactSpace [LinearOrder α] [t : TopologicalSpace α] [CompactSpace α]
    (hIio : ∀ x : α, IsOpen (Iio x)) (hIoi : ∀ x : α, IsOpen (Ioi x)) : OrderTopology α := by
  have hle : t ≤ Preorder.topology α := by
    refine le_generateFrom ?_
    rintro s ⟨a, rfl | rfl⟩
    exacts [hIoi a, hIio a]
  have hcl : ∀ s : Set α, IsClosed s → IsClosed[Preorder.topology α] s := fun s hs => by
    have h := @Continuous.isClosedMap α α t (Preorder.topology α) _ (t2Space_preorderTopology α) id
      (continuous_id_of_le hle)
    simpa using h s hs
  refine ⟨le_antisymm hle fun s hs => ?_⟩
  exact (@isClosed_compl_iff α (Preorder.topology α) s).1 (hcl sᶜ hs.isClosed_compl)

/-- **A compact connected separable linearly ordered space is an arc.** A nontrivial linear order whose order
topology is compact, connected and separable is homeomorphic to the unit interval. -/
theorem nonempty_homeomorph_unitInterval_of_compactSpace [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [CompactSpace α] [ConnectedSpace α] [TopologicalSpace.SeparableSpace α]
    [Nontrivial α] : Nonempty (α ≃ₜ unitInterval) := by
  have : DenselyOrdered α := denselyOrdered_of_preconnectedSpace
  let : CompleteLinearOrder α := completeLinearOrderOfCompactSpace α
  exact nonempty_homeomorph_unitInterval

/-- A nontrivial linear order with a compact, connected, separable topology in which every open ray is open is
homeomorphic to the unit interval. -/
theorem nonempty_homeomorph_unitInterval_of_isOpen_rays [LinearOrder α] [TopologicalSpace α]
    [CompactSpace α] [ConnectedSpace α] [TopologicalSpace.SeparableSpace α] [Nontrivial α]
    (hIio : ∀ x : α, IsOpen (Iio x)) (hIoi : ∀ x : α, IsOpen (Ioi x)) : Nonempty (α ≃ₜ unitInterval) := by
  have := orderTopology_of_compactSpace hIio hIoi
  exact nonempty_homeomorph_unitInterval_of_compactSpace

end LatticeProb.Topology
