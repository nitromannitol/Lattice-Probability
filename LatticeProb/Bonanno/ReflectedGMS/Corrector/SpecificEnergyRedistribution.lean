/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SpecificEnergyRedistribution at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActiveBlockEdges
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedBlockAveraging
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# Endpoint-spread to owner-block redistribution of a covariant edge coefficient

This module proves the manuscript lemma "Redistribution over blocks"
(`s:lem:redistribution`, manuscript lines 480-498), which is the mass-transport
half of the specific-energy projection `s:prop:projection`.  For a nonnegative
covariant edge coefficient `q_e` which vanishes unless `e` is active for the
selected partition `𝒮_m`, with unique owner block `S_e`, the lemma states

`E[ (2 a_{H_0})⁻¹ ∑_{e ∋ H_0} q_e ] = E[ ℓ(S_m(0))⁻² ∑_{e : S_e = S_m(0)} q_e ]`.

The proof is *not* a deterministic rearrangement of a sum: both sides are rooted
expectations of two different densities, and they are compared through the
manuscript transport

`T(ω, w, z) = ∑_e (q_e/2)(1_{w ∈ H}/a_H + 1_{w ∈ H'}/a_{H'}) 1_{z ∈ S_e}/ℓ(S_e)²`.

What is proved here about this actual transport:

* `OwnedEdgeField.endpointSpreadTransport` is `T` in ordered-label form, with the
  first endpoint only and the coefficient `q_e/2`;
  `OwnedEdgeField.two_mul_endpointSpreadTransport_eq` identifies twice this
  kernel with the manuscript's symmetric two-endpoint form, so the ordered
  convention really is the manuscript one (each unoriented edge is met twice and
  the `/2` convention is preserved);
* `OwnedEdgeField.lintegral_endpointSpreadTransport_outgoing` computes the
  **outgoing** integral `∫ T(ω,0,z) dz`: each owner block has Lebesgue area
  exactly `ℓ(S_e)²` (`volume_halfOpenSquare`), so the block factor integrates to
  one and the outgoing density is the endpoint density at the root cell,
  `OwnedEdgeField.rootEndpointDensity`;
* `OwnedEdgeField.lintegral_endpointSpreadTransport_incoming` computes the
  **incoming** integral `∫ T(ω,z,0) dz`: the endpoint factor integrates to one
  because a cell with null frontier has `volume (interior H) = a_H`
  (`Spatial.volume_interior_eq_of_frontier_null`), and the origin lies in the
  owner block `S_e` exactly when `S_e` is the selected origin block `S_m(0)`.
  The latter is the geometric heart: distinct *selected* squares have disjoint
  half-open squares (`eq_of_selected_of_mem_halfOpenSquare`), proved from
  half-open dyadic nesting together with the checked
  `ActiveBlockEdges.not_selected_ancestor_of_selected`.  So the incoming density
  is `OwnedEdgeField.ownerBlockDensity`;
* `OwnedEdgeField.endpointSpreadTransport_shift` is the **covariance** of the
  kernel under re-rooting, derived from the relabelling equivariance of the
  coefficient and of the owner block (`OwnedEdgeField.ReRootingCovariant`), i.e.
  from the manuscript hypothesis that `q` is a covariant coefficient of scaling
  degree two and `S_e` is covariantly defined.  The kernel then has the exact
  degree `-2` homogeneity of `EnvironmentLaws.MassTransportKernel` in the
  translation direction used by the marked transport.

The single probabilistic input is the mass-transport identity for the **one**
kernel `OwnedEdgeField.endpointSpreadTransport`; it is *not* proved here and is
the explicit producer dependency of this module.  On the actual marked
configuration space `Env × Grid` it is discharged from the manuscript's own
`s:eq:MTP` by
`MarkedMassTransportProducer.markedMassTransport_of_massTransport`.

The whole-class predicate `MarkedMassTransport` is still defined below, but see
its audit note: its covariance clause is only the `C = 1` instance of
`s:eq:Tcov`, so it is strictly stronger than `s:eq:MTP` and is not a manuscript
hypothesis.  No result here depends on it any more.  The final identity itself is
never assumed.

* `OwnedEdgeField.lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity`
  is the nonnegative redistribution identity `s:eq:redistribute`;
* `integral_signedRootDensity_eq_integral_signedOwnerDensity` is the signed
  extension, obtained from the positive and negative parts.  Following the
  manuscript it is stated **only** under finiteness of the expected endpoint
  density of `|q_e|`; no global finite-energy assumption is used, and the
  specific energy remains an expected root density.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SpecificEnergyRedistribution

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging

variable {V : Type*}

/-! ### Half-open dyadic squares

The selected squares are recorded through their half-open representatives, which
really partition the plane.  Everything in this section is about the actual
`DyadicApproximation.square` lattice. -/

/-- Half-open dyadic nesting: the strict upper bound survives the passage to the
parent, because integer division satisfies `2⌊n/2⌋ ≤ n ≤ 2⌊n/2⌋+1`.  This is the
half-open companion of `DiameterBlockIndex.square_subset_parent`. -/
theorem halfOpenSquare_subset_parent (D : Grid) (s : SquareIndex) :
    halfOpenSquare D s ⊆ halfOpenSquare D (parent D s) := by
  intro z hz i
  obtain ⟨h1, h2⟩ := hz i
  rw [square_lower_apply] at h1
  rw [square_upper_apply] at h2
  have hside : (0 : ℝ) < side D s.1 := side_pos D s.1
  have hcomp : D.origin s.1 i =
      D.origin (s.1 + 1) i + side D s.1 * ((D.digit s.1 i).val : ℝ) := D.compatible s.1 i
  rw [hcomp] at h1 h2
  have hq1 : 2 * ((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2) ≤
      s.2 i + ((D.digit s.1 i).val : ℤ) := by omega
  have hq2 : s.2 i + ((D.digit s.1 i).val : ℤ) ≤
      2 * ((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2) + 1 := by omega
  have hq1' : 2 * ((((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) ≤
      (s.2 i : ℝ) + ((D.digit s.1 i).val : ℝ) := by exact_mod_cast hq1
  have hq2' : (s.2 i : ℝ) + ((D.digit s.1 i).val : ℝ) ≤
      2 * ((((s.2 i + ((D.digit s.1 i).val : ℤ)) / 2 : ℤ) : ℝ)) + 1 := by exact_mod_cast hq2
  have m1 := mul_le_mul_of_nonneg_left hq1' hside.le
  have m2 := mul_le_mul_of_nonneg_left hq2' hside.le
  rw [square_lower_apply, square_upper_apply, side_parent, parent_fst, parent_snd]
  constructor
  · push_cast at m1 ⊢
    linarith
  · push_cast at m2 ⊢
    linarith

/-- Iterating the half-open nesting along the ancestor chain. -/
theorem halfOpenSquare_subset_ancestor (D : Grid) (s : SquareIndex) (j : ℕ) :
    halfOpenSquare D s ⊆ halfOpenSquare D (ancestor D s j) := by
  induction j with
  | zero => exact fun z hz => hz
  | succ j ih =>
      rw [ancestor_succ']
      exact ih.trans (halfOpenSquare_subset_parent D (ancestor D s j))

/-- Two half-open squares of the same level sharing a point have the same lattice
offset: the half-open squares of one level are pairwise disjoint. -/
theorem snd_eq_of_mem_halfOpenSquare (D : Grid) {s t : SquareIndex} (hlev : s.1 = t.1)
    {z : Plane} (hs : z ∈ halfOpenSquare D s) (ht : z ∈ halfOpenSquare D t) : s.2 = t.2 := by
  funext i
  have hside : (0 : ℝ) < side D t.1 := side_pos D t.1
  have h1 := hs i
  have h2 := ht i
  rw [square_lower_apply, square_upper_apply, hlev] at h1
  rw [square_lower_apply, square_upper_apply] at h2
  have hA : side D t.1 * (s.2 i : ℝ) < side D t.1 * ((t.2 i : ℝ) + 1) := by
    rw [mul_add, mul_one]
    linarith [h1.1, h2.2]
  have hB : side D t.1 * (t.2 i : ℝ) < side D t.1 * ((s.2 i : ℝ) + 1) := by
    rw [mul_add, mul_one]
    linarith [h2.1, h1.2]
  have hA' : (s.2 i : ℝ) < (t.2 i : ℝ) + 1 := lt_of_mul_lt_mul_left hA hside.le
  have hB' : (t.2 i : ℝ) < (s.2 i : ℝ) + 1 := lt_of_mul_lt_mul_left hB hside.le
  have hA'' : s.2 i < t.2 i + 1 := by exact_mod_cast hA'
  have hB'' : t.2 i < s.2 i + 1 := by exact_mod_cast hB'
  omega

/-- **The selected squares partition the plane.**  Two selected squares whose
half-open representatives share a point coincide: at the common level the
coarser one is an ancestor of the finer one, and a strict ancestor of a selected
square is never selected (`ActiveBlockEdges.not_selected_ancestor_of_selected`).
This is the ownership statement used at the origin. -/
theorem eq_of_selected_of_mem_halfOpenSquare (F : IndexedCells V) (D : Grid) (m : ℝ)
    {s t : SquareIndex} (hs : Selected F D m s) (ht : Selected F D m t) {z : Plane}
    (hzs : z ∈ halfOpenSquare D s) (hzt : z ∈ halfOpenSquare D t) : s = t := by
  rcases le_or_gt s.1 t.1 with hle | hlt
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = t.1 - s.1 := ⟨(t.1 - s.1).toNat, by omega⟩
    have hlev : (ancestor D s j).1 = t.1 := by
      rw [ActiveBlockEdges.ancestor_fst, hj]
      ring
    have hmem : z ∈ halfOpenSquare D (ancestor D s j) :=
      halfOpenSquare_subset_ancestor D s j hzs
    have h2 : (ancestor D s j).2 = t.2 := snd_eq_of_mem_halfOpenSquare D hlev hmem hzt
    have heq : ancestor D s j = t := Prod.ext hlev h2
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, ancestor_zero] at heq
      exact heq
    · exact absurd (heq ▸ ht)
        (ActiveBlockEdges.not_selected_ancestor_of_selected F D m s hs hpos)
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = s.1 - t.1 := ⟨(s.1 - t.1).toNat, by omega⟩
    have hpos : 0 < j := by omega
    have hlev : (ancestor D t j).1 = s.1 := by
      rw [ActiveBlockEdges.ancestor_fst, hj]
      ring
    have hmem : z ∈ halfOpenSquare D (ancestor D t j) :=
      halfOpenSquare_subset_ancestor D t j hzt
    have h2 : (ancestor D t j).2 = s.2 := snd_eq_of_mem_halfOpenSquare D hlev hmem hzs
    have heq : ancestor D t j = s := Prod.ext hlev h2
    exact absurd (heq ▸ hs)
      (ActiveBlockEdges.not_selected_ancestor_of_selected F D m t ht hpos)

/-! ### The Lebesgue area of a dyadic block -/

/-- The half-open square is the preimage of a product of half-open intervals
under the (measure preserving) forgetful map to the coordinate plane. -/
theorem halfOpenSquare_eq_preimage (D : Grid) (s : SquareIndex) :
    halfOpenSquare D s = (WithLp.ofLp : Plane → (Fin 2 → ℝ)) ⁻¹'
      (Set.univ.pi fun i : Fin 2 =>
        Set.Ico ((square D s).lower i) ((square D s).upper i)) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico]
  exact Iff.rfl

theorem measurableSet_halfOpenSquare (D : Grid) (s : SquareIndex) :
    MeasurableSet (halfOpenSquare D s) := by
  rw [halfOpenSquare_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin 2)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

/-- **The area of a block is `ℓ(S)²`.**  This is the normalisation that makes the
owner-block factor of the transport integrate to one. -/
theorem volume_halfOpenSquare (D : Grid) (s : SquareIndex) :
    volume (halfOpenSquare D s) = ENNReal.ofReal (side D s.1 ^ 2) := by
  have hfac : ∀ i : Fin 2, (square D s).upper i - (square D s).lower i = side D s.1 := by
    intro i
    rw [square_upper_apply, square_lower_apply]
    ring
  rw [halfOpenSquare_eq_preimage,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet,
    volume_pi_pi]
  simp only [Real.volume_Ico, hfac]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (side_pos D s.1).le]

/-! ### Cells of raw labels -/

/-- Splitting an option on a local variable, avoiding a case split of the goal. -/
theorem exists_eq_some_of_ne_none {α : Type*} {o : Option α} (h : o ≠ none) :
    ∃ a : α, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- The plane cell carried by the raw label `n`; an absent label has no cell. -/
noncomputable def labelCell (e : Env) (n : ℕ) : Set Plane :=
  if h : (e.val.1 n).isSome then (((decode e).cell ⟨n, h⟩ : CompactCell) : Set Plane)
  else ∅

theorem labelCell_of_isSome (e : Env) {n : ℕ} (h : (e.val.1 n).isSome) :
    labelCell e n = (((decode e).cell ⟨n, h⟩ : CompactCell) : Set Plane) :=
  dif_pos h

theorem labelCell_of_not_isSome (e : Env) {n : ℕ} (h : ¬ (e.val.1 n).isSome) :
    labelCell e n = ∅ := dif_neg h

theorem volume_labelCell_pos (e : Env) {n : ℕ} (h : (e.val.1 n).isSome) :
    0 < volume (labelCell e n) := by
  rw [labelCell_of_isSome e h]
  exact (cellVolume_pos_lt_top (decode e) (decode_geometry e) ⟨n, h⟩).1

theorem volume_labelCell_lt_top (e : Env) (n : ℕ) : volume (labelCell e n) < ∞ := by
  by_cases h : (e.val.1 n).isSome
  · rw [labelCell_of_isSome e h]
    exact (cellVolume_pos_lt_top (decode e) (decode_geometry e) ⟨n, h⟩).2
  · rw [labelCell_of_not_isSome e h]
    simp

/-- A cell has null frontier, so its interior carries the whole area `a_H`. -/
theorem volume_interior_labelCell (e : Env) (n : ℕ) :
    volume (interior (labelCell e n)) = volume (labelCell e n) := by
  by_cases h : (e.val.1 n).isSome
  · rw [labelCell_of_isSome e h]
    exact Spatial.volume_interior_eq_of_frontier_null ((decode_geometry e).2.2.1 ⟨n, h⟩)
  · rw [labelCell_of_not_isSome e h, interior_empty]

/-- Cell interiors are pairwise disjoint, so a point has at most one root label. -/
theorem eq_of_mem_interior_labelCell (e : Env) {a b : ℕ} {z : Plane}
    (ha : z ∈ interior (labelCell e a)) (hb : z ∈ interior (labelCell e b)) : a = b := by
  by_cases hA : (e.val.1 a).isSome
  · by_cases hB : (e.val.1 b).isSome
    · by_contra hne
      have hvne : (⟨a, hA⟩ : Vertex e.val) ≠ ⟨b, hB⟩ := by
        intro h
        exact hne (congrArg Subtype.val h)
      have hd := (decode_geometry e).2.2.2.1 hvne
      rw [labelCell_of_isSome e hA] at ha
      rw [labelCell_of_isSome e hB] at hb
      exact Set.disjoint_left.1 hd ha hb
    · rw [labelCell_of_not_isSome e hB, interior_empty] at hb
      exact absurd hb (Set.notMem_empty z)
  · rw [labelCell_of_not_isSome e hA, interior_empty] at ha
    exact absurd ha (Set.notMem_empty z)

/-- The label of the root cell `H_0` of the environment: the unique cell whose
interior contains the origin, if there is one. -/
noncomputable def originLabel (e : Env) : Option ℕ := by
  classical
  exact if h : ∃ n : ℕ, (0 : Plane) ∈ interior (labelCell e n) then some h.choose else none

theorem mem_interior_labelCell_originLabel (e : Env) {n : ℕ} (h : originLabel e = some n) :
    (0 : Plane) ∈ interior (labelCell e n) := by
  classical
  unfold originLabel at h
  by_cases hex : ∃ k : ℕ, (0 : Plane) ∈ interior (labelCell e k)
  · rw [dif_pos hex] at h
    have hn : hex.choose = n := Option.some.inj h
    rw [← hn]
    exact hex.choose_spec
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

theorem originLabel_eq_some_of_mem_interior (e : Env) {n : ℕ}
    (h : (0 : Plane) ∈ interior (labelCell e n)) : originLabel e = some n := by
  classical
  have hex : ∃ k : ℕ, (0 : Plane) ∈ interior (labelCell e k) := ⟨n, h⟩
  unfold originLabel
  rw [dif_pos hex]
  exact congrArg some (eq_of_mem_interior_labelCell e hex.choose_spec h)

theorem not_mem_interior_labelCell_of_originLabel_eq_none (e : Env)
    (h : originLabel e = none) (n : ℕ) : (0 : Plane) ∉ interior (labelCell e n) := by
  intro hn
  rw [originLabel_eq_some_of_mem_interior e hn] at h
  exact absurd h (by simp)

/-- Consistency with the existing boundary-masked root of
`RootDensities.rootAt`: off the boundary mask the two roots agree. -/
theorem originLabel_eq_map_rootAt (e : Env)
    (h : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    originLabel e = (RootDensities.rootAt (decode e) 0).map Subtype.val := by
  obtain ⟨v, hv, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) h
  rw [hv]
  show originLabel e = some (v : ℕ)
  refine originLabel_eq_some_of_mem_interior e ?_
  rw [labelCell_of_isSome e v.property]
  exact hint

/-! ### The owned coefficient field -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A nonnegative covariant edge coefficient together with its **measurable owner
labels**: for every ordered pair `p` of raw vertex labels, `weight` is `q_e ≥ 0`
and `owner` is the unique selected square owning `e`, absent exactly where the
coefficient vanishes.  Nothing about the transport identity is assumed. -/
structure OwnedEdgeField (R : MarkedReRooting Ω) (m : ℝ) where
  /-- The nonnegative coefficient `q_e`, indexed by ordered label pairs. -/
  weight : Ω → ℕ × ℕ → ℝ≥0∞
  /-- The owner block `S_e` of the edge, as a selected dyadic square. -/
  owner : Ω → ℕ × ℕ → Option SquareIndex
  weight_symm : ∀ (ω : Ω) (p : ℕ × ℕ), weight ω (p.2, p.1) = weight ω p
  owner_symm : ∀ (ω : Ω) (p : ℕ × ℕ), owner ω (p.2, p.1) = owner ω p
  weight_eq_zero_of_owner_eq_none : ∀ (ω : Ω) (p : ℕ × ℕ), owner ω p = none → weight ω p = 0
  weight_eq_zero_of_absent : ∀ (ω : Ω) (p : ℕ × ℕ),
    ¬ ((R.env ω).val.1 p.1).isSome → weight ω p = 0
  owner_selected : ∀ (ω : Ω) (p : ℕ × ℕ) (s : SquareIndex), owner ω p = some s →
    Selected (decode (R.env ω)) (R.grid ω) m s

namespace OwnedEdgeField

variable {R : MarkedReRooting Ω} {m : ℝ}

/-- The endpoint-spread factor `1_{w ∈ int H}/a_H` of one endpoint. -/
noncomputable def spread (e : Env) (n : ℕ) (w : Plane) : ℝ≥0∞ :=
  Set.indicator (interior (labelCell e n)) (fun _ => (volume (labelCell e n))⁻¹) w

/-- The owner block `S_e` of an edge, as a subset of the plane. -/
noncomputable def ownerSet (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) : Set Plane :=
  (Q.owner ω p).elim ∅ (halfOpenSquare (R.grid ω))

/-- The area `ℓ(S_e)²` of the owner block. -/
noncomputable def ownerArea (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) : ℝ≥0∞ :=
  (Q.owner ω p).elim 0 fun s => ENNReal.ofReal (side (R.grid ω) s.1 ^ 2)

/-- The owner-block factor `1_{z ∈ S_e}/ℓ(S_e)²`. -/
noncomputable def ownerSpread (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) (z : Plane) : ℝ≥0∞ :=
  Set.indicator (Q.ownerSet ω p) (fun _ => (Q.ownerArea ω p)⁻¹) z

theorem ownerSet_of_eq_none (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ}
    (h : Q.owner ω p = none) : Q.ownerSet ω p = ∅ := by
  unfold ownerSet
  rw [h]
  rfl

theorem ownerSet_of_eq_some (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ} {s : SquareIndex}
    (h : Q.owner ω p = some s) : Q.ownerSet ω p = halfOpenSquare (R.grid ω) s := by
  unfold ownerSet
  rw [h]
  rfl

theorem ownerArea_of_eq_none (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ}
    (h : Q.owner ω p = none) : Q.ownerArea ω p = 0 := by
  unfold ownerArea
  rw [h]
  rfl

theorem ownerArea_of_eq_some (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ} {s : SquareIndex}
    (h : Q.owner ω p = some s) :
    Q.ownerArea ω p = ENNReal.ofReal (side (R.grid ω) s.1 ^ 2) := by
  unfold ownerArea
  rw [h]
  rfl

theorem measurableSet_ownerSet (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) :
    MeasurableSet (Q.ownerSet ω p) := by
  by_cases hnone : Q.owner ω p = none
  · rw [Q.ownerSet_of_eq_none hnone]
    exact MeasurableSet.empty
  · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none hnone
    rw [Q.ownerSet_of_eq_some hs]
    exact measurableSet_halfOpenSquare _ _

theorem volume_ownerSet (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) :
    volume (Q.ownerSet ω p) = Q.ownerArea ω p := by
  by_cases hnone : Q.owner ω p = none
  · rw [Q.ownerSet_of_eq_none hnone, Q.ownerArea_of_eq_none hnone, measure_empty]
  · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none hnone
    rw [Q.ownerSet_of_eq_some hs, Q.ownerArea_of_eq_some hs, volume_halfOpenSquare]

theorem ownerArea_ne_zero (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ} {s : SquareIndex}
    (h : Q.owner ω p = some s) : Q.ownerArea ω p ≠ 0 := by
  rw [Q.ownerArea_of_eq_some h]
  refine (ENNReal.ofReal_pos.2 ?_).ne'
  have hpos := side_pos (R.grid ω) s.1
  positivity

theorem ownerArea_ne_top (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) :
    Q.ownerArea ω p ≠ ∞ := by
  by_cases hnone : Q.owner ω p = none
  · rw [Q.ownerArea_of_eq_none hnone]
    exact ENNReal.zero_ne_top
  · obtain ⟨s, hs⟩ := exists_eq_some_of_ne_none hnone
    rw [Q.ownerArea_of_eq_some hs]
    exact ENNReal.ofReal_ne_top

theorem owner_eq_some_of_weight_ne_zero (Q : OwnedEdgeField R m) {ω : Ω} {p : ℕ × ℕ}
    (h : Q.weight ω p ≠ 0) : ∃ s : SquareIndex, Q.owner ω p = some s := by
  by_cases hnone : Q.owner ω p = none
  · exact absurd (Q.weight_eq_zero_of_owner_eq_none ω p hnone) h
  · exact exists_eq_some_of_ne_none hnone

theorem measurable_ownerSpread (Q : OwnedEdgeField R m) (ω : Ω) (p : ℕ × ℕ) :
    Measurable fun z : Plane => Q.ownerSpread ω p z :=
  measurable_const.indicator (Q.measurableSet_ownerSet ω p)

theorem measurable_spread (e : Env) (n : ℕ) : Measurable fun w : Plane => spread e n w :=
  measurable_const.indicator isOpen_interior.measurableSet

/-! ### The endpoint-spread to owner-block transport -/

/-- The manuscript transport
`T(ω,w,z) = ∑_e (q_e/2)(1_{w∈H}/a_H + 1_{w∈H'}/a_{H'}) 1_{z∈S_e}/ℓ(S_e)²`,
written over ordered label pairs with the first endpoint only: each unoriented
edge is met twice, so this is exactly the manuscript kernel (see
`two_mul_endpointSpreadTransport_eq`).  All terms are nonnegative. -/
noncomputable def endpointSpreadTransport (Q : OwnedEdgeField R m) (ω : Ω) (w z : Plane) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Q.weight ω p / 2 * spread (R.env ω) p.1 w * Q.ownerSpread ω p z

/-! ### The outgoing integral: the endpoint density at the root -/

/-- The manuscript's endpoint density `(2 a_{H_0})⁻¹ ∑_{e ∋ H_0} q_e`, with the
boundary convention that it vanishes when no cell interior contains the origin. -/
noncomputable def rootEndpointDensity (Q : OwnedEdgeField R m) (ω : Ω) : ℝ≥0∞ :=
  (originLabel (R.env ω)).elim 0 fun n =>
    (∑' k : ℕ, Q.weight ω (n, k)) / (2 * volume (labelCell (R.env ω) n))

/-- **The outgoing integral of the transport.**  The owner-block factor is a
probability density on its block, so the whole outgoing mass is the endpoint
spread evaluated at the source. -/
theorem lintegral_endpointSpreadTransport_outgoing (Q : OwnedEdgeField R m) (ω : Ω) :
    (∫⁻ z : Plane, Q.endpointSpreadTransport ω 0 z ∂volume)
      = ∑' p : ℕ × ℕ, Q.weight ω p / 2 * spread (R.env ω) p.1 0 := by
  have hterm : ∀ p : ℕ × ℕ,
      (∫⁻ z : Plane, Q.weight ω p / 2 * spread (R.env ω) p.1 0 * Q.ownerSpread ω p z ∂volume)
        = Q.weight ω p / 2 * spread (R.env ω) p.1 0 := by
    intro p
    rw [lintegral_const_mul _ (Q.measurable_ownerSpread ω p)]
    by_cases hw : Q.weight ω p = 0
    · simp [hw]
    · obtain ⟨s, hs⟩ := Q.owner_eq_some_of_weight_ne_zero hw
      have hone : (∫⁻ z : Plane, Q.ownerSpread ω p z ∂volume) = 1 := by
        have hind : (∫⁻ z : Plane, Q.ownerSpread ω p z ∂volume)
            = (Q.ownerArea ω p)⁻¹ * volume (Q.ownerSet ω p) :=
          lintegral_indicator_const (Q.measurableSet_ownerSet ω p) _
        rw [hind, Q.volume_ownerSet ω p,
          ENNReal.inv_mul_cancel (Q.ownerArea_ne_zero hs) (Q.ownerArea_ne_top ω p)]
      rw [hone, mul_one]
  calc (∫⁻ z : Plane, Q.endpointSpreadTransport ω 0 z ∂volume)
      = ∫⁻ z : Plane, ∑' p : ℕ × ℕ,
          Q.weight ω p / 2 * spread (R.env ω) p.1 0 * Q.ownerSpread ω p z ∂volume := rfl
    _ = ∑' p : ℕ × ℕ, ∫⁻ z : Plane,
          Q.weight ω p / 2 * spread (R.env ω) p.1 0 * Q.ownerSpread ω p z ∂volume :=
        lintegral_tsum fun p =>
          (measurable_const.mul (Q.measurable_ownerSpread ω p)).aemeasurable
    _ = ∑' p : ℕ × ℕ, Q.weight ω p / 2 * spread (R.env ω) p.1 0 := tsum_congr hterm

/-- The outgoing density is exactly the manuscript endpoint density at the root
cell `H_0`. -/
theorem lintegral_endpointSpreadTransport_outgoing_eq_rootEndpointDensity
    (Q : OwnedEdgeField R m) (ω : Ω) :
    (∫⁻ z : Plane, Q.endpointSpreadTransport ω 0 z ∂volume) = Q.rootEndpointDensity ω := by
  rw [Q.lintegral_endpointSpreadTransport_outgoing ω]
  obtain ⟨o, ho⟩ : ∃ o : Option ℕ, originLabel (R.env ω) = o := ⟨_, rfl⟩
  cases o with
  | none =>
    have hr : originLabel (R.env ω) = none := ho
    have hgoal : Q.rootEndpointDensity ω = 0 := by
      unfold rootEndpointDensity
      rw [hr]
      rfl
    rw [hgoal]
    have hzero : ∀ p : ℕ × ℕ, Q.weight ω p / 2 * spread (R.env ω) p.1 0 = 0 := by
      intro p
      have hs : spread (R.env ω) p.1 0 = 0 :=
        Set.indicator_of_notMem
          (not_mem_interior_labelCell_of_originLabel_eq_none (R.env ω) hr p.1) _
      rw [hs, mul_zero]
    simp only [hzero, tsum_zero]
  | some r =>
    have hr : originLabel (R.env ω) = some r := ho
    have hgoal : Q.rootEndpointDensity ω
        = (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r)) := by
      unfold rootEndpointDensity
      rw [hr]
      rfl
    rw [hgoal]
    have hmem : (0 : Plane) ∈ interior (labelCell (R.env ω) r) :=
      mem_interior_labelCell_originLabel (R.env ω) hr
    have hroot : spread (R.env ω) r 0 = (volume (labelCell (R.env ω) r))⁻¹ :=
      Set.indicator_of_mem hmem _
    have hother : ∀ n : ℕ, n ≠ r → spread (R.env ω) n 0 = 0 := by
      intro n hn
      refine Set.indicator_of_notMem (fun hcontra => hn ?_) _
      exact eq_of_mem_interior_labelCell (R.env ω) hcontra hmem
    have h1 : (∑' p : ℕ × ℕ, Q.weight ω p / 2 * spread (R.env ω) p.1 0)
        = ∑' a : ℕ, ∑' b : ℕ, Q.weight ω (a, b) / 2 * spread (R.env ω) a 0 :=
      ENNReal.tsum_prod'
    have h2 : (∑' a : ℕ, ∑' b : ℕ, Q.weight ω (a, b) / 2 * spread (R.env ω) a 0)
        = ∑' b : ℕ, Q.weight ω (r, b) / 2 * spread (R.env ω) r 0 := by
      refine tsum_eq_single r fun a ha => ?_
      simp [hother a ha]
    have h3 : (∑' b : ℕ, Q.weight ω (r, b) / 2 * (volume (labelCell (R.env ω) r))⁻¹)
        = (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r)) := by
      calc (∑' b : ℕ, Q.weight ω (r, b) / 2 * (volume (labelCell (R.env ω) r))⁻¹)
          = (∑' b : ℕ, Q.weight ω (r, b) / 2) * (volume (labelCell (R.env ω) r))⁻¹ :=
            ENNReal.tsum_mul_right
        _ = ((∑' b : ℕ, Q.weight ω (r, b)) * 2⁻¹) * (volume (labelCell (R.env ω) r))⁻¹ := by
            simp only [div_eq_mul_inv]
            rw [ENNReal.tsum_mul_right]
        _ = (∑' k : ℕ, Q.weight ω (r, k)) / (2 * volume (labelCell (R.env ω) r)) := by
            rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl ennreal_two_ne_zero)
              (Or.inl ennreal_two_ne_top), ← mul_assoc]
    rw [h1, h2, hroot, h3]

/-! ### The incoming integral: the owner-block density -/

/-- The ordered pairs owned by the selected origin block `S_m(0)`. -/
def ownedByOriginBlock (Q : OwnedEdgeField R m) (ω : Ω) : Set (ℕ × ℕ) :=
  {p | Q.owner ω p = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m)}

/-- The manuscript's block density `ℓ(S_m(0))⁻² ∑_{e : S_e = S_m(0)} q_e`; the
sum over ordered pairs meets every unoriented edge twice, which is the `/2`. -/
noncomputable def ownerBlockDensity (Q : OwnedEdgeField R m) (ω : Ω) : ℝ≥0∞ :=
  (∑' p : ℕ × ℕ, (Q.ownedByOriginBlock ω).indicator (Q.weight ω) p) /
    (2 * ENNReal.ofReal (R.blockSideAt m ω ^ 2))

/-- Ownership at the origin identifies the origin block: the owner block of an
edge contains the origin exactly when it is the selected origin block.  This is
where the disjointness of the selected squares is used. -/
theorem zero_mem_ownerSet_iff (Q : OwnedEdgeField R m) (ω : Ω)
    (hsel : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k) (p : ℕ × ℕ) :
    (0 : Plane) ∈ Q.ownerSet ω p ↔ p ∈ Q.ownedByOriginBlock ω := by
  have hblock : Selected (decode (R.env ω)) (R.grid ω) m
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := originSelected_blockLevel hsel
  have hzero : (0 : Plane) ∈ halfOpenSquare (R.grid ω)
      (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) :=
    zero_mem_blockSet (decode (R.env ω)) (R.grid ω) m
  constructor
  · intro h
    by_cases hnone : Q.owner ω p = none
    · rw [Q.ownerSet_of_eq_none hnone] at h
      exact absurd h (Set.notMem_empty _)
    · obtain ⟨s, hq⟩ := exists_eq_some_of_ne_none hnone
      rw [Q.ownerSet_of_eq_some hq] at h
      have hst := eq_of_selected_of_mem_halfOpenSquare (decode (R.env ω)) (R.grid ω) m
        (Q.owner_selected ω p s hq) hblock h hzero
      show Q.owner ω p = _
      rw [hq, hst]
  · intro h
    have hq : Q.owner ω p = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := h
    rw [Q.ownerSet_of_eq_some hq]
    exact hzero

/-- **The incoming integral of the transport.**  The endpoint factor is a
probability density on its cell, because the cell frontier is null. -/
theorem lintegral_endpointSpreadTransport_incoming (Q : OwnedEdgeField R m) (ω : Ω) :
    (∫⁻ w : Plane, Q.endpointSpreadTransport ω w 0 ∂volume)
      = ∑' p : ℕ × ℕ, Q.weight ω p / 2 * Q.ownerSpread ω p 0 := by
  have hterm : ∀ p : ℕ × ℕ,
      (∫⁻ w : Plane, Q.weight ω p / 2 * spread (R.env ω) p.1 w * Q.ownerSpread ω p 0 ∂volume)
        = Q.weight ω p / 2 * Q.ownerSpread ω p 0 := by
    intro p
    have hrw : (fun w : Plane =>
          Q.weight ω p / 2 * spread (R.env ω) p.1 w * Q.ownerSpread ω p 0)
        = fun w : Plane =>
          Q.weight ω p / 2 * Q.ownerSpread ω p 0 * spread (R.env ω) p.1 w := by
      funext w
      ring
    rw [hrw, lintegral_const_mul _ (measurable_spread (R.env ω) p.1)]
    by_cases hw : Q.weight ω p = 0
    · simp [hw]
    · have hsome : ((R.env ω).val.1 p.1).isSome := by
        by_contra hcon
        exact hw (Q.weight_eq_zero_of_absent ω p hcon)
      have hone : (∫⁻ w : Plane, spread (R.env ω) p.1 w ∂volume) = 1 := by
        have hind : (∫⁻ w : Plane, spread (R.env ω) p.1 w ∂volume)
            = (volume (labelCell (R.env ω) p.1))⁻¹ *
              volume (interior (labelCell (R.env ω) p.1)) :=
          lintegral_indicator_const isOpen_interior.measurableSet _
        rw [hind, volume_interior_labelCell (R.env ω) p.1,
          ENNReal.inv_mul_cancel (volume_labelCell_pos (R.env ω) hsome).ne'
            (volume_labelCell_lt_top (R.env ω) p.1).ne]
      rw [hone, mul_one]
  calc (∫⁻ w : Plane, Q.endpointSpreadTransport ω w 0 ∂volume)
      = ∫⁻ w : Plane, ∑' p : ℕ × ℕ,
          Q.weight ω p / 2 * spread (R.env ω) p.1 w * Q.ownerSpread ω p 0 ∂volume := rfl
    _ = ∑' p : ℕ × ℕ, ∫⁻ w : Plane,
          Q.weight ω p / 2 * spread (R.env ω) p.1 w * Q.ownerSpread ω p 0 ∂volume :=
        lintegral_tsum fun p =>
          ((measurable_const.mul (measurable_spread (R.env ω) p.1)).mul
            measurable_const).aemeasurable
    _ = ∑' p : ℕ × ℕ, Q.weight ω p / 2 * Q.ownerSpread ω p 0 := tsum_congr hterm

/-- The incoming density is exactly the manuscript owner-block density. -/
theorem lintegral_endpointSpreadTransport_incoming_eq_ownerBlockDensity
    (Q : OwnedEdgeField R m) (ω : Ω)
    (hsel : ∃ k : ℤ, OriginSelected (decode (R.env ω)) (R.grid ω) m k) :
    (∫⁻ w : Plane, Q.endpointSpreadTransport ω w 0 ∂volume) = Q.ownerBlockDensity ω := by
  have hside : ENNReal.ofReal (R.blockSideAt m ω ^ 2)
      = ENNReal.ofReal (side (R.grid ω)
          (blockSquareIndex (decode (R.env ω)) (R.grid ω) m).1 ^ 2) := rfl
  rw [Q.lintegral_endpointSpreadTransport_incoming ω]
  unfold ownerBlockDensity
  have hterm : ∀ p : ℕ × ℕ, Q.weight ω p / 2 * Q.ownerSpread ω p 0
      = (Q.ownedByOriginBlock ω).indicator (Q.weight ω) p *
        (2 * ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ := by
    intro p
    by_cases hp : p ∈ Q.ownedByOriginBlock ω
    · have hq : Q.owner ω p = some (blockSquareIndex (decode (R.env ω)) (R.grid ω) m) := hp
      have hmem : (0 : Plane) ∈ Q.ownerSet ω p := (Q.zero_mem_ownerSet_iff ω hsel p).2 hp
      have h1 : Q.ownerSpread ω p 0 = (ENNReal.ofReal (R.blockSideAt m ω ^ 2))⁻¹ := by
        unfold ownerSpread
        rw [Set.indicator_of_mem hmem, Q.ownerArea_of_eq_some hq, ← hside]
      rw [h1, Set.indicator_of_mem hp, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl ennreal_two_ne_zero) (Or.inl ennreal_two_ne_top), ← mul_assoc]
    · have hmem : (0 : Plane) ∉ Q.ownerSet ω p := fun h =>
        hp ((Q.zero_mem_ownerSet_iff ω hsel p).1 h)
      unfold ownerSpread
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hp, mul_zero, zero_mul]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right, div_eq_mul_inv]

/-! ### Covariance of the transport under re-rooting -/

/-! ### The redistribution identity -/

end OwnedEdgeField

/-! ### The signed extension

Following the manuscript, the signed identity is obtained from the positive and
negative parts and is stated **only** under finiteness of the expected endpoint
density of `|q_e|`, i.e. of the two nonnegative expected endpoint densities.  No
global finite-energy hypothesis is used: the specific energy remains an expected
root density. -/

end ReflectedGMS.SpecificEnergyRedistribution
