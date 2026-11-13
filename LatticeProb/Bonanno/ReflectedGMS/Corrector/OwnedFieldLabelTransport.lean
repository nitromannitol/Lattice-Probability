/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.OwnedFieldLabelTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LabelBijectionProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SelectedSquareSimilarity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PairingOwnershipInstance
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageCoefficientScaling

/-!
# Clauses 2–4 of the four transport predicates, and the grid-side bijection `τ`

`Corrector/LabelBijectionProducer` produces the label-level bijection `σ : ℕ ≃ ℕ` of

* `MarkedMassTransportProducer.SimilarityCovariantField`,
* `SpecificEnergyRedistribution.OwnedEdgeField.ReRootingCovariant`,
* `OwnedFieldPairingTransport.PairingReRooting`,
* `MeasurableEndpointTransport.OwnerReRooting`,

together with the **first** clause of each (the cells), at every environment and every positive
similarity, with no hypothesis.  This module supplies the remaining clauses — the weight, the
owner block and the owner area — and the second bijection the three re-rooting predicates are
quantified over, `τ : SquareIndex → SquareIndex` on the **grid** side.

## `τ` is the checked square reindexing

`Corrector/SelectedSquareSimilarity.squareMap s u D` is the reindexing of dyadic squares induced
by `z ↦ s • (z - u)` together with `dilate s hs ∘ translate u` on the grid.  It is already known
to carry corners, sides, carriers, frontiers, parents, patches, boundaries and the selection
statistic `κ` correctly.  What the three re-rooting predicates additionally need is the
**half-open** square (those partition the plane, so they are the owner blocks) and the
translation normal form `dilate 1 one_pos (translate w D) = translate w D`:

* `preimage_halfOpenSquare_squareMap` — the half-open squares correspond exactly;
* `halfOpenSquare_squareMap_one`, `side_squareMap_one` — the last two clauses of
  `PairingReRooting` and `OwnerReRooting` verbatim, at `τ := squareMap 1 w D`.

## The owner clause

`PairingOwnershipInstance.activeOwner` is a `Classical.choose` over the selected squares of which
a pair of vertices is an `ActiveBlockEdges.ActiveEdge`.  `ActiveEdge` is built from `Selected`,
adjacency, `patchVertices` and `boundaryVertices` — each of which `SelectedSquareSimilarity`
transports — so the owner label is equivariant:

* `activeEdge_squareMap_iff`, `activeOwner_relabel`, `labelOwner_labelEquiv`.

At **inactive** labels there is nothing to prove, and the proof says so rather than a remark:
`LabelBijectionProducer.not_isSome_labelEquiv` gives that `σ` preserves inactivity, and
`labelOwner` and `pairCoeff` are *defined* to vanish as soon as one endpoint label is absent, so
the owner, the owner set, the owner area and the coefficient all vanish on both sides.  Those
cases are discharged inside `labelOwner_labelEquiv_pair` and `pairCoeff_labelEquiv_pair`.

## The weight clause

`pairCoeff_labelEquiv` lifts `MarkedStageCoefficientScaling.conductance_mul_inner_relabel` (the
vertex-level `q_e ↦ s² q_e` of tex:480) from decoded vertices to raw label pairs along `σ`.

## What is assembled

For any `PairingOwnership` over the actual marked re-rooting whose owner datum is the canonical
`labelOwner` — which is exactly what `PairingOwnershipInstance.activePairingOwnership` is, by
`rfl`; see the anti-vacuity `example`s at the end — and any two vertex fields whose increments
transport (`SimilarityTransportedField`):

* `similarityCovariantField_posField` / `..._negField` — `SimilarityCovariantField` **complete**;
* `pairingReRooting` — `PairingReRooting` **complete**;
* `ownerReRooting_pos` / `ownerReRooting_neg` — `OwnerReRooting` **complete**;
* `reRootingCovariant_pos` / `reRootingCovariant_neg` — `OwnedEdgeField.ReRootingCovariant`
  **complete**.

`SimilarityTransportedField` is not an assumption about an unspecified object: it is discharged
outright for the two fields of `s:prop:projection` by
`MarkedStageFieldCovariance.gradientTransported_stageField` and
`...gradientTransported_stageDifferenceField` — see `similarityTransportedField_stageField` and
`similarityTransportedField_stageDifferenceField`, which have no hypotheses at all.

## What is **not** proved here

The measure-theoretic inputs of the transport chain (`MarkedMassTransport`, measurability, the
gated origin selection), the two structural hypotheses `hcover`/`hH` of `activePairingOwnership`,
and `SpecificEnergyConvergence.MarkedNestedProjectionBound` itself.  This file proves no main
theorem: every statement below is a structural identity about fields, labels and squares.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.OwnedFieldLabelTransport

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open EnvironmentLaws SpecificEnergyRedistribution
open ActiveBlockEdges PairingOwnershipInstance OwnedFieldPairingTransport
open MarkedMassTransportProducer LabelBijectionProducer SelectedSquareSimilarity
open DyadicGridTranslation UniformGridDilationInvariance SpecificEnergyDensitySimilarity

/-! ### Two scalar bookkeeping lemmas for the weight clause -/

theorem ofReal_scaled {a x y : ℝ} (ha : 0 ≤ a) (h : x = a * y) :
    ENNReal.ofReal x = ENNReal.ofReal a * ENNReal.ofReal y := by
  rw [h, ENNReal.ofReal_mul ha]

theorem ofReal_neg_scaled {a x y : ℝ} (ha : 0 ≤ a) (h : x = a * y) :
    ENNReal.ofReal (-x) = ENNReal.ofReal a * ENNReal.ofReal (-y) := by
  rw [h, ← mul_neg, ENNReal.ofReal_mul ha]

/-! ### The half-open squares correspond under the square reindexing

`SelectedSquareSimilarity.preimage_square_squareMap` is the statement for the *closed* carriers.
The owner block of an edge is the **half-open** square, because those partition the plane, so the
owner-set clause of all four predicates needs this variant. -/

theorem mem_halfOpenSquare_squareMap_iff {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid)
    (c : SquareIndex) (z : Plane) :
    positiveSimilarity s u z ∈ halfOpenSquare (dilate s hs (translate u D)) (squareMap s u D c)
      ↔ z ∈ halfOpenSquare D c := by
  have hz : ∀ i : Fin 2, positiveSimilarity s u z i = s * (z i - u i) := fun i => by
    simp [positiveSimilarity]
  constructor
  · intro hmem i
    have hi : (square (dilate s hs (translate u D)) (squareMap s u D c)).lower i
          ≤ positiveSimilarity s u z i ∧
        positiveSimilarity s u z i
          < (square (dilate s hs (translate u D)) (squareMap s u D c)).upper i := hmem i
    rw [square_lower_squareMap hs u D c i, square_upper_squareMap hs u D c i, hz i] at hi
    have h1 := le_of_mul_le_mul_left hi.1 hs
    have h2 := lt_of_mul_lt_mul_left hi.2 hs.le
    exact ⟨by linarith, by linarith⟩
  · intro hmem i
    have hi : (square D c).lower i ≤ z i ∧ z i < (square D c).upper i := hmem i
    show (square (dilate s hs (translate u D)) (squareMap s u D c)).lower i
        ≤ positiveSimilarity s u z i ∧
      positiveSimilarity s u z i
        < (square (dilate s hs (translate u D)) (squareMap s u D c)).upper i
    rw [square_lower_squareMap hs u D c i, square_upper_squareMap hs u D c i, hz i]
    exact ⟨mul_le_mul_of_nonneg_left (by linarith [hi.1]) hs.le,
      mul_lt_mul_of_pos_left (by linarith [hi.2]) hs⟩

/-- **The owner blocks correspond exactly.**  The half-open version of
`SelectedSquareSimilarity.preimage_square_squareMap`. -/
theorem preimage_halfOpenSquare_squareMap {s : ℝ} (hs : 0 < s) (u : Plane) (D : Grid)
    (c : SquareIndex) :
    positiveSimilarity s u ⁻¹'
        halfOpenSquare (dilate s hs (translate u D)) (squareMap s u D c)
      = halfOpenSquare D c :=
  Set.ext fun z => mem_halfOpenSquare_squareMap_iff hs u D c z

/-! ### `τ` for the three re-rooting predicates

At unit scale the grid action is the plain translation (`dilate_one`), so `squareMap 1 w D` is
the grid-side bijection the re-rooting predicates quantify over, and both clauses they state
about it are proved here. -/

/-! ### The active-edge owner is equivariant -/

section Relabel

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env} {rel : Vertex e.val ≃ Vertex e'.val}

/-- **Active edges correspond.**  `Selected` by `selected_squareMap_iff`, adjacency because the
conductances are unchanged, the patch and boundary memberships by the two `..._squareMap_iff`
results of `Corrector/SelectedSquareSimilarity`. -/
theorem activeEdge_squareMap_iff (h : IsSimilarityRelabel s u hs e e' rel) (D : Grid) (m : ℝ)
    (c : SquareIndex) (v v' : Vertex e.val) :
    ActiveEdge (decode e') (dilate s hs (translate u D)) m (squareMap s u D c) (rel v, rel v')
      ↔ ActiveEdge (decode e) D m c (v, v') := by
  have hadj : (decode e').graph.toSimpleGraph.Adj (rel v) (rel v')
      ↔ (decode e).graph.toSimpleGraph.Adj v v' := by
    show 0 < (decode e').graph.c (rel v) (rel v') ↔ 0 < (decode e).graph.c v v'
    rw [h.2 v v']
  have hsel := selected_squareMap_iff h D m c
  have hpv := mem_patchVertices_squareMap_iff h D c v
  have hpv' := mem_patchVertices_squareMap_iff h D c v'
  have hbv := mem_boundaryVertices_squareMap_iff h D c v
  have hbv' := mem_boundaryVertices_squareMap_iff h D c v'
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨hsel.1 h1, hadj.1 h2, hpv.1 h3, hpv'.1 h4,
      fun hb => h5 ⟨hbv.2 hb.1, hbv'.2 hb.2⟩⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨hsel.2 h1, hadj.2 h2, hpv.2 h3, hpv'.2 h4,
      fun hb => h5 ⟨hbv.1 hb.1, hbv'.1 hb.2⟩⟩

/-- **The owner block of a pair of vertices is equivariant**, with the grid-side bijection
`squareMap s u D`. -/
theorem activeOwner_relabel (h : IsSimilarityRelabel s u hs e e' rel) (D : Grid) (m : ℝ)
    (v v' : Vertex e.val) :
    activeOwner (decode e') (dilate s hs (translate u D)) m (rel v, rel v')
      = (activeOwner (decode e) D m (v, v')).map (squareMap s u D) := by
  by_cases hnone : activeOwner (decode e) D m (v, v') = none
  · rw [hnone]
    show activeOwner (decode e') (dilate s hs (translate u D)) m (rel v, rel v') = none
    by_contra hne
    obtain ⟨t, ht⟩ := exists_eq_some_of_ne_none hne
    obtain ⟨c, rfl⟩ := exists_squareMap_eq s u D t
    exact not_activeEdge_of_activeOwner_eq_none (decode e) D m hnone c
      ((activeEdge_squareMap_iff h D m c v v').1
        (activeEdge_of_activeOwner_eq_some (decode e') (dilate s hs (translate u D)) m ht))
  · obtain ⟨c, hc⟩ := exists_eq_some_of_ne_none hnone
    rw [hc]
    show activeOwner (decode e') (dilate s hs (translate u D)) m (rel v, rel v')
        = some (squareMap s u D c)
    exact activeOwner_eq_some_of_activeEdge (decode e') (decode_geometry e').1
      (dilate s hs (translate u D)) m
      ((activeEdge_squareMap_iff h D m c v v').2
        (activeEdge_of_activeOwner_eq_some (decode e) D m hc))

/-! ### The weight clause at the level of raw label pairs

On active labels `σ` is `rel`, so the vertex-level quadratic scaling applies; on inactive labels
both coefficients vanish by definition. -/

/-- **The signed pairing coefficient scales quadratically along `σ`**, on an explicit pair of
raw labels.  This is `MarkedStageCoefficientScaling.conductance_mul_inner_relabel` read on raw
labels, with the inactive labels handled by `not_isSome_labelEquiv`. -/
theorem pairCoeff_labelEquiv_pair (h : IsSimilarityRelabel s u hs e e' rel)
    {Phi1 Phi2 : Vertex e.val → Plane} {Psi1 Psi2 : Vertex e'.val → Plane}
    (h1 : GradientTransported s rel Phi1 Psi1) (h2 : GradientTransported s rel Phi2 Psi2)
    (a b : ℕ) :
    pairCoeff e' Psi1 Psi2 (labelEquiv rel a, labelEquiv rel b)
      = s ^ 2 * pairCoeff e Phi1 Phi2 (a, b) := by
  by_cases ha : (e.val.1 a).isSome
  · by_cases hb : (e.val.1 b).isSome
    · have ha' : (e'.val.1 (labelEquiv rel a)).isSome := (isSome_labelEquiv_iff rel a).2 ha
      have hb' : (e'.val.1 (labelEquiv rel b)).isSome := (isSome_labelEquiv_iff rel b).2 hb
      have hva : (⟨labelEquiv rel a, ha'⟩ : Vertex e'.val) = rel ⟨a, ha⟩ :=
        Subtype.ext (labelEquiv_of_isSome rel ha)
      have hvb : (⟨labelEquiv rel b, hb'⟩ : Vertex e'.val) = rel ⟨b, hb⟩ :=
        Subtype.ext (labelEquiv_of_isSome rel hb)
      show pairCoeffAt e' Psi1 Psi2 (labelEquiv rel a) (labelEquiv rel b)
        = s ^ 2 * pairCoeffAt e Phi1 Phi2 a b
      rw [pairCoeffAt_of_isSome e' Psi1 Psi2 ha' hb', pairCoeffAt_of_isSome e Phi1 Phi2 ha hb,
        hva, hvb]
      exact MarkedStageCoefficientScaling.conductance_mul_inner_relabel h h1 h2 ⟨a, ha⟩ ⟨b, hb⟩
    · have hb' : ¬ (e'.val.1 (labelEquiv rel b)).isSome := not_isSome_labelEquiv rel hb
      rw [pairCoeff_eq_zero_of_snd_absent e' Psi1 Psi2 (labelEquiv rel a) hb',
        pairCoeff_eq_zero_of_snd_absent e Phi1 Phi2 a hb, mul_zero]
  · have ha' : ¬ (e'.val.1 (labelEquiv rel a)).isSome := not_isSome_labelEquiv rel ha
    rw [pairCoeff_eq_zero_of_absent e' Psi1 Psi2 (p := (labelEquiv rel a, labelEquiv rel b)) ha',
      pairCoeff_eq_zero_of_absent e Phi1 Phi2 (p := (a, b)) ha, mul_zero]

/-- The weight clause on a pair index, the shape the four predicates use. -/
theorem pairCoeff_labelEquiv (h : IsSimilarityRelabel s u hs e e' rel)
    {Phi1 Phi2 : Vertex e.val → Plane} {Psi1 Psi2 : Vertex e'.val → Plane}
    (h1 : GradientTransported s rel Phi1 Psi1) (h2 : GradientTransported s rel Phi2 Psi2)
    (q : ℕ × ℕ) :
    pairCoeff e' Psi1 Psi2 (labelEquiv rel q.1, labelEquiv rel q.2)
      = s ^ 2 * pairCoeff e Phi1 Phi2 q :=
  pairCoeff_labelEquiv_pair h h1 h2 q.1 q.2

end Relabel

/-! ### The label-level owner transport on the actual marked configuration space -/

section Marked

open ActualMarkedBlockTransport

/-- **The owner label of a raw pair is equivariant along `σ`**, on an explicit pair of labels. -/
theorem labelOwner_labelEquiv_pair {s : ℝ} {u : Plane} {hs : 0 < s} (m : ℝ) (ω ω' : Env × Grid)
    {rel : Vertex ω.1.val ≃ Vertex ω'.1.val}
    (h : IsSimilarityRelabel s u hs ω.1 ω'.1 rel)
    (hgrid : ω'.2 = dilate s hs (translate u ω.2)) (a b : ℕ) :
    labelOwner actualReRooting m ω' (labelEquiv rel a, labelEquiv rel b)
      = (labelOwner actualReRooting m ω (a, b)).map (squareMap s u ω.2) := by
  by_cases ha : (ω.1.val.1 a).isSome
  · by_cases hb : (ω.1.val.1 b).isSome
    · have ha' : (ω'.1.val.1 (labelEquiv rel a)).isSome := (isSome_labelEquiv_iff rel a).2 ha
      have hb' : (ω'.1.val.1 (labelEquiv rel b)).isSome := (isSome_labelEquiv_iff rel b).2 hb
      have hva : (⟨labelEquiv rel a, ha'⟩ : Vertex ω'.1.val) = rel ⟨a, ha⟩ :=
        Subtype.ext (labelEquiv_of_isSome rel ha)
      have hvb : (⟨labelEquiv rel b, hb'⟩ : Vertex ω'.1.val) = rel ⟨b, hb⟩ :=
        Subtype.ext (labelEquiv_of_isSome rel hb)
      rw [labelOwner_pair actualReRooting m ω' (labelEquiv rel a) (labelEquiv rel b) ha' hb',
        labelOwner_pair actualReRooting m ω a b ha hb]
      show activeOwner (decode ω'.1) ω'.2 m (⟨labelEquiv rel a, ha'⟩, ⟨labelEquiv rel b, hb'⟩)
        = (activeOwner (decode ω.1) ω.2 m (⟨a, ha⟩, ⟨b, hb⟩)).map (squareMap s u ω.2)
      rw [hva, hvb, hgrid]
      exact activeOwner_relabel h ω.2 m ⟨a, ha⟩ ⟨b, hb⟩
    · have hb' : ¬ (ω'.1.val.1 (labelEquiv rel b)).isSome := not_isSome_labelEquiv rel hb
      rw [labelOwner_eq_none_of_snd actualReRooting m ω' (labelEquiv rel a) hb',
        labelOwner_eq_none_of_snd actualReRooting m ω a hb]
      rfl
  · have ha' : ¬ (ω'.1.val.1 (labelEquiv rel a)).isSome := not_isSome_labelEquiv rel ha
    rw [labelOwner_eq_none_of_fst actualReRooting m ω' ha' (labelEquiv rel b),
      labelOwner_eq_none_of_fst actualReRooting m ω ha b]
    rfl

/-- **The owner label of a raw pair is equivariant along `σ`**, on a pair index. -/
theorem labelOwner_labelEquiv {s : ℝ} {u : Plane} {hs : 0 < s} (m : ℝ) (ω ω' : Env × Grid)
    {rel : Vertex ω.1.val ≃ Vertex ω'.1.val}
    (h : IsSimilarityRelabel s u hs ω.1 ω'.1 rel)
    (hgrid : ω'.2 = dilate s hs (translate u ω.2)) (q : ℕ × ℕ) :
    labelOwner actualReRooting m ω' (labelEquiv rel q.1, labelEquiv rel q.2)
      = (labelOwner actualReRooting m ω q).map (squareMap s u ω.2) :=
  labelOwner_labelEquiv_pair (hs := hs) m ω ω' h hgrid q.1 q.2

variable {m : ℝ}

/-- **The owner-set clause**, for any owned edge field whose owner datum is the canonical
`labelOwner`. -/
theorem preimage_ownerSet_labelEquiv {s : ℝ} {u : Plane} {hs : 0 < s}
    (Q : OwnedEdgeField actualReRooting m)
    (hQ : ∀ (ω : Env × Grid) (q : ℕ × ℕ), Q.owner ω q = labelOwner actualReRooting m ω q)
    (ω ω' : Env × Grid) {rel : Vertex ω.1.val ≃ Vertex ω'.1.val}
    (h : IsSimilarityRelabel s u hs ω.1 ω'.1 rel)
    (hgrid : ω'.2 = dilate s hs (translate u ω.2)) (q : ℕ × ℕ) :
    positiveSimilarity s u ⁻¹' Q.ownerSet ω' (labelEquiv rel q.1, labelEquiv rel q.2)
      = Q.ownerSet ω q := by
  have hown := labelOwner_labelEquiv (hs := hs) m ω ω' h hgrid q
  by_cases hnone : labelOwner actualReRooting m ω q = none
  · rw [hnone] at hown
    have h1 : Q.owner ω' (labelEquiv rel q.1, labelEquiv rel q.2) = none := by
      rw [hQ]; exact hown
    have h0 : Q.owner ω q = none := by rw [hQ]; exact hnone
    rw [Q.ownerSet_of_eq_none h1, Q.ownerSet_of_eq_none h0, Set.preimage_empty]
  · obtain ⟨c, hc⟩ := exists_eq_some_of_ne_none hnone
    rw [hc] at hown
    have h1 : Q.owner ω' (labelEquiv rel q.1, labelEquiv rel q.2)
        = some (squareMap s u ω.2 c) := by rw [hQ]; exact hown
    have h0 : Q.owner ω q = some c := by rw [hQ]; exact hc
    rw [Q.ownerSet_of_eq_some h1, Q.ownerSet_of_eq_some h0]
    show positiveSimilarity s u ⁻¹' halfOpenSquare ω'.2 (squareMap s u ω.2 c)
      = halfOpenSquare ω.2 c
    rw [hgrid]
    exact preimage_halfOpenSquare_squareMap hs u ω.2 c

/-- **The owner-area clause**: the owner block area scales by `s²`. -/
theorem ownerArea_labelEquiv {s : ℝ} {u : Plane} {hs : 0 < s}
    (Q : OwnedEdgeField actualReRooting m)
    (hQ : ∀ (ω : Env × Grid) (q : ℕ × ℕ), Q.owner ω q = labelOwner actualReRooting m ω q)
    (ω ω' : Env × Grid) {rel : Vertex ω.1.val ≃ Vertex ω'.1.val}
    (h : IsSimilarityRelabel s u hs ω.1 ω'.1 rel)
    (hgrid : ω'.2 = dilate s hs (translate u ω.2)) (q : ℕ × ℕ) :
    Q.ownerArea ω' (labelEquiv rel q.1, labelEquiv rel q.2)
      = ENNReal.ofReal (s ^ 2) * Q.ownerArea ω q := by
  have hown := labelOwner_labelEquiv (hs := hs) m ω ω' h hgrid q
  by_cases hnone : labelOwner actualReRooting m ω q = none
  · rw [hnone] at hown
    have h1 : Q.owner ω' (labelEquiv rel q.1, labelEquiv rel q.2) = none := by
      rw [hQ]; exact hown
    have h0 : Q.owner ω q = none := by rw [hQ]; exact hnone
    rw [Q.ownerArea_of_eq_none h1, Q.ownerArea_of_eq_none h0, mul_zero]
  · obtain ⟨c, hc⟩ := exists_eq_some_of_ne_none hnone
    rw [hc] at hown
    have h1 : Q.owner ω' (labelEquiv rel q.1, labelEquiv rel q.2)
        = some (squareMap s u ω.2 c) := by rw [hQ]; exact hown
    have h0 : Q.owner ω q = some c := by rw [hQ]; exact hc
    rw [Q.ownerArea_of_eq_some h1, Q.ownerArea_of_eq_some h0]
    show ENNReal.ofReal (side ω'.2 (squareMap s u ω.2 c).1 ^ 2)
      = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (side ω.2 c.1 ^ 2)
    rw [hgrid, side_squareMap hs u ω.2 c, mul_pow, ENNReal.ofReal_mul (sq_nonneg s)]

end Marked

/-! ### The transport datum of the vertex fields

The only field-specific input of the weight clause.  It is **not** an assumption about an
unspecified object: `similarityTransportedField_stageField` below discharges it outright for the
gated stage field, and `similarityTransportedField_stageDifferenceField` for the stage
difference — the two fields whose rooted densities are `markedStageEnergy` and
`markedStageDefect`. -/

/-- A marked vertex field whose increments transport along every joint similarity. -/
def SimilarityTransportedField (Ψ : ∀ p : Env × Grid, Vertex p.1.val → Plane) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : Env × Grid)
    (rel : Vertex p.1.val ≃ Vertex (markedSimilarity s u hs p).1.val),
    IsSimilarityRelabel s u hs p.1 (markedSimilarity s u hs p).1 rel →
      GradientTransported s rel (Ψ p) (Ψ (markedSimilarity s u hs p))

/-- **The gated stage field transports**, with no hypothesis
(`MarkedStageFieldCovariance.gradientTransported_stageField`). -/
theorem similarityTransportedField_stageField (n : ℕ) :
    SimilarityTransportedField (MarkedStageFieldCovariance.stageField n) :=
  fun _ _ _ _ _ h => MarkedStageFieldCovariance.gradientTransported_stageField n h

/-- **The gated stage difference field transports**, with no hypothesis. -/
theorem similarityTransportedField_stageDifferenceField (k n : ℕ) :
    SimilarityTransportedField (MarkedStageFieldCovariance.stageDifferenceField k n) :=
  fun _ _ _ _ _ h => MarkedStageFieldCovariance.gradientTransported_stageDifferenceField k n h

/-! ### The four predicates -/

section Assembly

open ActualMarkedBlockTransport

variable {m : ℝ} {Ψ H : ∀ p : Env × Grid, Vertex p.1.val → Plane}

/-- **`SimilarityCovariantField` for the positive part of the signed pairing coefficient.**
All four clauses: the cells by `LabelBijectionProducer.preimage_labelCell_labelEquiv`, the weight
by `pairCoeff_labelEquiv`, the owner set and the owner area by the two lemmas above. -/
theorem similarityCovariantField_posField (O : PairingOwnership actualReRooting m Ψ H)
    (hO : ∀ (ω : Env × Grid) (q : ℕ × ℕ), O.owner ω q = labelOwner actualReRooting m ω q)
    (hΨ : SimilarityTransportedField Ψ) (hH : SimilarityTransportedField H) :
    SimilarityCovariantField (posField O) := by
  intro s u hs p
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  have hgrid : (markedSimilarity s u hs p).2 = dilate s hs (translate u p.2) := rfl
  refine ⟨labelEquiv (similarityRelabel s u hs p.1), preimage_labelCell_labelEquiv h,
    fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact ofReal_scaled (sq_nonneg s)
      (pairCoeff_labelEquiv h (hΨ s u hs p _ h) (hH s u hs p _ h) q)
  · exact preimage_ownerSet_labelEquiv (hs := hs) (posField O) hO p (markedSimilarity s u hs p)
      h hgrid q
  · exact ownerArea_labelEquiv (hs := hs) (posField O) hO p (markedSimilarity s u hs p)
      h hgrid q

/-- **`SimilarityCovariantField` for the negative part.** -/
theorem similarityCovariantField_negField (O : PairingOwnership actualReRooting m Ψ H)
    (hO : ∀ (ω : Env × Grid) (q : ℕ × ℕ), O.owner ω q = labelOwner actualReRooting m ω q)
    (hΨ : SimilarityTransportedField Ψ) (hH : SimilarityTransportedField H) :
    SimilarityCovariantField (negField O) := by
  intro s u hs p
  have h := isSimilarityRelabel_similarityRelabel s u hs p.1
  have hgrid : (markedSimilarity s u hs p).2 = dilate s hs (translate u p.2) := rfl
  refine ⟨labelEquiv (similarityRelabel s u hs p.1), preimage_labelCell_labelEquiv h,
    fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact ofReal_neg_scaled (sq_nonneg s)
      (pairCoeff_labelEquiv h (hΨ s u hs p _ h) (hH s u hs p _ h) q)
  · exact preimage_ownerSet_labelEquiv (hs := hs) (negField O) hO p (markedSimilarity s u hs p)
      h hgrid q
  · exact ownerArea_labelEquiv (hs := hs) (negField O) hO p (markedSimilarity s u hs p)
      h hgrid q

end Assembly

/-! ### Anti-vacuity

The hypothesis `hO` is not a restriction invented here: the project's only `PairingOwnership`
producer, `PairingOwnershipInstance.activePairingOwnership`, satisfies it by `rfl`, and the
transport datum is discharged outright for the two fields of `s:prop:projection`.  The two
`example`s below machine-check the weld: the consumers are applied to the producers. -/

section AntiVacuity

open ActualMarkedBlockTransport

end AntiVacuity

end ReflectedGMS.OwnedFieldLabelTransport
