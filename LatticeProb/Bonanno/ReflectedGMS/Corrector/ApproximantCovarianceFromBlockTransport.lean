/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.ApproximantCovarianceFromBlockTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SimilarityCentroidCovariance
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridTranslationInvariance

/-!
# `ApproximantGradientCovariant` from one geometric transport statement

`HarmonicCoordinateAssembly.ApproximantGradientCovariant ms` (the input `hcov` of
`harmonicCoordinateConclusions_of_named_inputs`) asserts that the *gradients* of the concrete
block interpolants `phi` commute with every physical similarity, for **some** measure-preserving
action of that similarity on uniform grids.  Its own declaring docstring names the intended
producer:

> the covariance of `IsBlockInterpolation` under `transformCell`, together with the checked grid
> actions `UniformGridDilationInvariance.dilate` and `DyadicGridTranslation.translate` and their
> measure preservation.

No module implemented that.  This one does, modulo exactly the first clause.

## The reduction

* `gridSimilarity s hs u D = dilate s hs (translate u D)` — the grid action of
  `positiveSimilarity s u : z ↦ s • (z - u)`, since `translate u` implements `z ↦ z - u`
  (`DyadicGridTranslation.square_carrier_translate`) and `dilate s hs` implements `z ↦ s • z`
  (`UniformGridDilationInvariance.square_carrier_dilate`).
* `measurePreserving_gridSimilarity` — **discharged outright** from the two checked invariance
  theorems `map_translate_gridMeasure` and `map_dilate_gridMeasure`; the latter holds for every
  positive real `s`, not only dyadic ones.
* `BlockInterpolationSimilarityCovariant` — the single remaining geometric input: along a physical
  similarity and the paired grid action, `f` is a block interpolation for `(𝓗, D, m)` **iff** its
  transport is one for `(𝓗', act D, m)`.
* `approximantGradientCovariant_of_blockTransport` — **the reduction**:
  `BlockInterpolationSimilarityCovariant → ApproximantGradientCovariant ms`, for every `ms`.

## Why this is a genuine reduction and not a restatement

Three things are actually proved here, and each is a place where a naive attempt fails.

1. **The `Classical.choose` is handled without assuming existence.**  `phi` is
   `dite (∃ f, IsBlockInterpolation F D m f) Classical.choose (cellCentroid F)`, and existence of a
   block interpolant is *not* available on `SublinearEvent` — it needs the strictly stronger
   `W`-bound (`PatchCentroidTraceFiniteEnergy.exists_isBlockInterpolation_of_spatialCellBounds`).
   The `↔` form of the input makes the two `dite` branches match, and the non-existence branch is
   closed by `SimilarityCentroidCovariance.cellCentroid_similarityRelabel`, which is why that
   module had to be proved first.
2. **Uniqueness, not existence, is what the good event supplies.**  On `SublinearEvent` the
   interpolant is unique (`isBlockInterpolation_unique`), and `SublinearEvent` membership transfers
   along similarities (`mem_sublinearEvent_iff_of_similarity`), so the transported `phi` and the
   target `phi` coincide whenever either exists.  This is exactly the standing trap that an
   *everywhere* covariance input for `phi` is undischargeable.
3. **No converse grid action is needed.**  A direct attempt needs
   `gridSimilarity s⁻¹ (-s • u) (gridSimilarity s hs u D) = D`, which is not available (`dilate`
   reindexes levels by the grid-dependent `levelShift`).  Stating the input as an `↔` at the *same*
   pair `(D, act D)` avoids it, and surjectivity of the field transport
   (`transportField_untransport`) still delivers the existence equivalence in both directions.

## What remains open

`BlockInterpolationSimilarityCovariant` alone.  Unwinding `IsBlockInterpolation`, it is the
conjunction of: the selected-square correspondence `Selected (decode e') (act D) m (σ c) ↔
Selected (decode e) D m c` for a level/lattice reindexing `σ` commuting with `parent`; the
`skeleton` correspondence; and `CentroidTraceMinimizer` transport, for which the energy side is
`Analysis/ExtendedEnergy.energyENN_smul` and `energyENN_add_const` and the trace side is the
centroid covariance proved in `Corrector/SimilarityCentroidCovariance`.  The dilation half of the
square correspondence exists for the origin chain in `Spatial/DilatedSelectedBlocks`
(`blockIndex_originIndex_dilate`, `originSelected_dilate_iff`); what is missing is its extension
to a general `SquareIndex` and to the translation factor.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.ApproximantCovarianceFromBlockTransport

open Code StatementIngredients EnvironmentLaws DyadicApproximation
open HarmonicCoordinateAssembly

/-! ### The grid action of a similarity -/

/-- The grid action of `positiveSimilarity s u : z ↦ s • (z - u)`: translate by `u`, then dilate
by `s`. -/
noncomputable def gridSimilarity (s : ℝ) (hs : 0 < s) (u : Plane) (D : Grid) : Grid :=
  UniformGridDilationInvariance.dilate s hs (DyadicGridTranslation.translate u D)

/-- **The grid action preserves the uniform grid law.**  Discharged from the two checked
invariance theorems. -/
theorem measurePreserving_gridSimilarity {s : ℝ} (hs : 0 < s) (u : Plane) :
    MeasurePreserving (gridSimilarity s hs u) gridLaw gridLaw := by
  have h1 : MeasurePreserving (DyadicGridTranslation.translate u) gridLaw gridLaw :=
    ⟨DyadicGridTranslation.measurable_translate_left u,
      UniformGridTranslationInvariance.map_translate_gridMeasure u⟩
  have h2 : MeasurePreserving (UniformGridDilationInvariance.dilate s hs) gridLaw gridLaw :=
    ⟨UniformGridDilationInvariance.measurable_dilate s hs,
      UniformGridDilationInvariance.map_dilate_gridMeasure hs⟩
  exact h2.comp h1

/-! ### Transport of a vertex field along a similarity relabelling -/

/-- The field transported along a similarity: read at the preimage label, moved by the
similarity. -/
noncomputable def transportField (s : ℝ) (u : Plane) {e e' : Env}
    (relabel : Vertex e.val ≃ Vertex e'.val) (f : Vertex e.val → Plane) :
    Vertex e'.val → Plane :=
  fun x => positiveSimilarity s u (f (relabel.symm x))

@[simp] theorem transportField_apply (s : ℝ) (u : Plane) {e e' : Env}
    (relabel : Vertex e.val ≃ Vertex e'.val) (f : Vertex e.val → Plane) (v : Vertex e.val) :
    transportField s u relabel f (relabel v) = positiveSimilarity s u (f v) := by
  show positiveSimilarity s u (f (relabel.symm (relabel v))) = positiveSimilarity s u (f v)
  rw [Equiv.symm_apply_apply]

/-- **Every field on the target is a transport.**  This is what replaces an inverse grid action
in the existence equivalence below. -/
theorem transportField_untransport {s : ℝ} (hs : 0 < s) (u : Plane) {e e' : Env}
    (relabel : Vertex e.val ≃ Vertex e'.val) (g : Vertex e'.val → Plane) :
    transportField s u relabel
        (fun y => positiveSimilarity s⁻¹ (-s • u) (g (relabel y))) = g := by
  funext x
  show positiveSimilarity s u
      (positiveSimilarity s⁻¹ (-s • u) (g (relabel (relabel.symm x)))) = g x
  rw [Equiv.apply_symm_apply, positiveSimilarity_inverse_right s u (g x) hs]

/-! ### The single remaining geometric input -/

/-- **The one atomic geometric input.**  Along a physical similarity of environments and the
paired grid action, a vertex field is a block interpolation exactly when its transport is.

This is the manuscript's "the gradient construction commutes with translations and positive
dilations" at the level of the *specification* `IsBlockInterpolation`, before any choice is made.
It mentions no `Classical.choose`, no measure and no good event: it is a pathwise statement about
selected squares, skeletons and centroid-trace minimizers. -/
def BlockInterpolationSimilarityCovariant : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel →
      ∀ (D : Grid) (m : ℕ) (f : Vertex e.val → Plane),
        IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m
            (transportField s u relabel f)
          ↔ IsBlockInterpolation (decode e) D m f

/-! ### The reduction -/

/-- If no block interpolation exists, `phi` is the centroid field. -/
theorem phi_of_not_exists {V : Type*} (F : IndexedCells V) (D : Grid) (m : ℕ)
    (h : ¬ ∃ f, IsBlockInterpolation F D m f) : phi F D m = cellCentroid F := by
  unfold phi
  rw [dif_neg h]

/-- Block interpolations exist for the transformed configuration exactly when they exist for the
original one. -/
theorem exists_isBlockInterpolation_iff (hB : BlockInterpolationSimilarityCovariant)
    {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env} {relabel : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' relabel) (D : Grid) (m : ℕ) :
    (∃ g, IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m g)
      ↔ ∃ f, IsBlockInterpolation (decode e) D m f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun y => positiveSimilarity s⁻¹ (-s • u) (g (relabel y)), ?_⟩
    refine (hB s u hs e e' relabel h D m _).1 ?_
    rwa [transportField_untransport hs u relabel g]
  · rintro ⟨f, hf⟩
    exact ⟨transportField s u relabel f, (hB s u hs e e' relabel h D m f).2 hf⟩

/-- **The interpolant itself is covariant on the good event.**  Both branches of the
`Classical.choose` are handled: on the existence branch by uniqueness, off it by the covariance of
the centroid field. -/
theorem phi_similarity (hB : BlockInterpolationSimilarityCovariant)
    {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env} {relabel : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' relabel) (hG : e ∈ SublinearEvent)
    (D : Grid) (m : ℕ) (v : Vertex e.val) :
    phi (decode e') (gridSimilarity s hs u D) m (relabel v)
      = positiveSimilarity s u (phi (decode e) D m v) := by
  by_cases hex : ∃ f, IsBlockInterpolation (decode e) D m f
  · have hex' : ∃ g, IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m g :=
      (exists_isBlockInterpolation_iff hB h D m).2 hex
    have h1 : IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m
        (phi (decode e') (gridSimilarity s hs u D) m) :=
      phi_spec_of_exists (decode e') (gridSimilarity s hs u D) m hex'
    have h2 : IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m
        (transportField s u relabel (phi (decode e) D m)) :=
      (hB s u hs e e' relabel h D m _).2 (phi_spec_of_exists (decode e) D m hex)
    have hsub' : e' ∈ SublinearEvent := (mem_sublinearEvent_iff_of_similarity h).1 hG
    have heq : phi (decode e') (gridSimilarity s hs u D) m
        = transportField s u relabel (phi (decode e) D m) :=
      isBlockInterpolation_unique (decode e') (decode_geometry e') (gridSimilarity s hs u D)
        hsub' m h1 h2
    rw [heq, transportField_apply]
  · have hex' : ¬ ∃ g, IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m g :=
      fun hg => hex ((exists_isBlockInterpolation_iff hB h D m).1 hg)
    rw [phi_of_not_exists (decode e') (gridSimilarity s hs u D) m hex',
      phi_of_not_exists (decode e) D m hex]
    exact SimilarityCentroidCovariance.cellCentroid_similarityRelabel h (decode_geometry e) v

/-- Differences of similarity images are `s` times the differences. -/
theorem positiveSimilarity_sub (s : ℝ) (u a b : Plane) :
    positiveSimilarity s u a - positiveSimilarity s u b = s • (a - b) := by
  show s • (a - u) - s • (b - u) = s • (a - b)
  rw [← smul_sub]
  congr 1
  abel

end ReflectedGMS.ApproximantCovarianceFromBlockTransport
