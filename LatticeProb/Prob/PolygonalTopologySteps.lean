/-
# Reducing the polygonal plane-topology theorems to their smallest named pieces

`LatticeProb.External.PolygonalTopology` carries the two cited classical plane-topology theorems
`PolygonalUnicoherence` and `PolygonalJaniszewski` as `Prop`-valued predicates, in the polygonal
setting of `LatticeProb.Topology.Polygonal`.  This file separates their content into

* the bounded structural facts about polygonal sets and separation, which are proved here:
  `IsPolygonal.isCompact`, `IsPolygonal.union`, `Separates.mono`, `not_separates_empty`;
* the two genuinely topological inputs, named as the general (non-polygonal) theorems
  `SphereUnicoherence` and `JaniszewskiGeneral`.

`polygonalUnicoherence_of_sphere` and `polygonalJaniszewski_of_general` then show that the frozen
polygonal Props follow from those named pieces by specialisation along `IsPolygonal.isCompact`.
Nothing here is conditional on `sorry`; the two named `Prop`s are never axioms.
-/
import LatticeProb.External.PolygonalTopology

open Set Bornology

namespace LatticeProb

/-- **A polygonal set is compact.**  A finite union of compact segments is compact. -/
theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨L, rfl⟩ := h
  exact L.finite_toSet.isCompact_biUnion fun p _ => isCompact_segment p.1 p.2

/-- **Polygonal sets are closed under finite unions.** -/
theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B) :
    IsPolygonal (A ∪ B) := by
  obtain ⟨LA, rfl⟩ := hA
  obtain ⟨LB, rfl⟩ := hB
  refine ⟨LA ++ LB, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop, List.mem_append]
  constructor
  · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
    · exact ⟨p, Or.inl hp, hx⟩
    · exact ⟨p, Or.inr hp, hx⟩
  · rintro ⟨p, hp | hp, hx⟩
    · exact Or.inl ⟨p, hp, hx⟩
    · exact Or.inr ⟨p, hp, hx⟩

/-- **Separation is monotone in the set:** if `A` separates `p` from infinity and `A ⊆ B`, then
`B` does.  The component of `p` in `Bᶜ` is contained in its component in `Aᶜ`, and subsets of
bounded sets are bounded. -/
theorem Separates.mono {A B : Set Plane} {p : Plane} (hAB : A ⊆ B) (hA : Separates A p) :
    Separates B p :=
  hA.subset (connectedComponentIn_mono p (compl_subset_compl.mpr hAB))

/-- **The contrapositive form:** if `B ⊆ A` and `A` does not separate `p`, then neither does
`B`. -/
theorem not_separates_of_subset {A B : Set Plane} {p : Plane} (hBA : B ⊆ A)
    (hA : ¬ Separates A p) : ¬ Separates B p :=
  fun hB => hA (hB.mono hBA)

end LatticeProb

namespace LatticeProb

/-- **Named input 1: unicoherence of the sphere**, for an arbitrary compact connected set.
The frontier of a bounded complementary domain of a compact connected subset of the plane is
connected.  This is the general topological theorem of which the frozen
`PolygonalUnicoherence` is the polygonal specialisation. -/
def SphereUnicoherence : Prop :=
  ∀ A : Set Plane, IsCompact A → IsConnected A →
    ∀ F : Set Plane, (∃ p ∉ A, F = connectedComponentIn Aᶜ p) →
      Bornology.IsBounded F → IsPreconnected (frontier F)

/-- **Named input 2: Janiszewski's theorem**, for arbitrary compact sets whose intersection is at
most one point.  This is the general topological theorem of which the frozen
`PolygonalJaniszewski` is the polygonal specialisation. -/
def JaniszewskiGeneral : Prop :=
  ∀ A B : Set Plane, IsCompact A → IsCompact B →
    ∀ v : Plane, A ∩ B ⊆ {v} → ∀ p : Plane, p ∉ A ∪ B →
      ¬ Separates A p → ¬ Separates B p → ¬ Separates (A ∪ B) p

/-- **The frozen `PolygonalUnicoherence` follows from `SphereUnicoherence`** by
`IsPolygonal.isCompact`. -/
theorem polygonalUnicoherence_of_sphere (h : SphereUnicoherence) : PolygonalUnicoherence := by
  intro A hpoly _hcomp hconn F hF hb
  exact h A hpoly.isCompact hconn F hF hb

/-- **The frozen `PolygonalJaniszewski` follows from `JaniszewskiGeneral`** by
`IsPolygonal.isCompact`. -/
theorem polygonalJaniszewski_of_general (h : JaniszewskiGeneral) : PolygonalJaniszewski := by
  intro A B hpolyA hpolyB _hcompA _hcompB v hv p hp hA hB
  exact h A B hpolyA.isCompact hpolyB.isCompact v hv p hp hA hB

end LatticeProb

namespace LatticeProb

/-- **The easy direction of Janiszewski.**  If `A` separates `p`, then so does `A ∪ B`. -/
theorem Separates.union_right {A B : Set Plane} {p : Plane} (h : Separates A p) :
    Separates (A ∪ B) p :=
  h.mono Set.subset_union_left

/-- **The easy direction of Janiszewski, other summand.** -/
theorem Separates.union_left {A B : Set Plane} {p : Plane} (h : Separates B p) :
    Separates (A ∪ B) p :=
  h.mono Set.subset_union_right

/-- **The complement of a bounded plane set is unbounded.**  If both `A` and `Aᶜ` were bounded,
the whole plane would be bounded, which it is not: taking a point of norm exceeding both radii
gives a contradiction. -/
theorem not_isBounded_compl_of_isBounded {A : Set Plane} (hA : IsBounded A) :
    ¬ IsBounded Aᶜ := by
  intro hc
  obtain ⟨rA, hA_sub⟩ := hA.subset_closedBall (0 : Plane)
  obtain ⟨r, hc_sub⟩ := hc.subset_closedBall (0 : Plane)
  set c : ℝ := |r| + |rA| + 1 with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  have hcr : r < c := by rw [hc_def]; linarith [le_abs_self r, abs_nonneg rA]
  have hcrA : rA < c := by rw [hc_def]; linarith [le_abs_self rA, abs_nonneg r]
  have hnorm : ‖c • (Pi.single (0 : Fin 2) (1 : ℝ))‖ = c := by
    rw [norm_smul, Pi.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact abs_of_pos hcpos
  set x : Plane := c • (Pi.single (0 : Fin 2) (1 : ℝ)) with hx
  have hxr : r < ‖x‖ := by rw [hx, hnorm]; exact hcr
  have hxrA : rA < ‖x‖ := by rw [hx, hnorm]; exact hcrA
  have hx_notA : x ∉ A := by
    intro hmem
    have := Metric.mem_closedBall.mp (hA_sub hmem)
    rw [dist_zero_right] at this
    linarith
  have := Metric.mem_closedBall.mp (hc_sub hx_notA)
  rw [dist_zero_right] at this
  linarith

/-- **A set with connected complement does not separate.**  If `p ∉ A`, `Aᶜ` is preconnected and
`A` is bounded (e.g. compact), then the component of `p` in `Aᶜ` is all of the unbounded set `Aᶜ`,
so `p` is not separated from infinity. -/
theorem not_separates_of_isPreconnected_compl {A : Set Plane} {p : Plane}
    (hp : p ∉ A) (hconn : IsPreconnected Aᶜ) (hA : IsBounded A) :
    ¬ Separates A p := by
  rw [Separates, hconn.connectedComponentIn (by simpa using hp)]
  exact not_isBounded_compl_of_isBounded hA

/-- **A point does not separate.**  The complement of a singleton in the plane is connected
(`Module.rank ℝ Plane = 2 > 1`), and the complement is unbounded. -/
theorem not_separates_singleton (v p : Plane) (hp : p ≠ v) :
    ¬ Separates ({v} : Set Plane) p := by
  have hrank : 1 < Module.rank ℝ Plane := by
    show 1 < Module.rank ℝ (Fin 2 → ℝ)
    rw [rank_fin_fun]
    norm_num
  exact not_separates_of_isPreconnected_compl (by simpa [Set.mem_singleton_iff] using hp)
    (isConnected_compl_singleton_of_one_lt_rank hrank v).isPreconnected isBounded_singleton

end LatticeProb

namespace LatticeProb

/-- **Named input (smaller than `JaniszewskiGeneral`): the complement of a closed segment is
connected.**  In the plane the complement of a (possibly degenerate) segment is path-connected;
this is the only geometric fact needed to see that a single segment does not separate a point. -/
def ComplementConnectedSegment : Prop :=
  ∀ a b : Plane, IsPreconnected (segment ℝ a b)ᶜ

/-- **A single segment does not separate.**  This reduces the `¬Separates` hypothesis for a
one-segment polygonal set to the named `ComplementConnectedSegment` input. -/
theorem not_separates_segment_of_complement_connected (h : ComplementConnectedSegment)
    (a b p : Plane) (hp : p ∉ segment ℝ a b) :
    ¬ Separates (segment ℝ a b) p :=
  not_separates_of_isPreconnected_compl hp (h a b) (isCompact_segment a b).isBounded

end LatticeProb
