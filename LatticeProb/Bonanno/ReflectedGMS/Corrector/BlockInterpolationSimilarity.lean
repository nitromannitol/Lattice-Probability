/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BlockInterpolationSimilarity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SelectedSquareSimilarity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ApproximantCovarianceFromBlockTransport
import LatticeProb.Bonanno.ReflectedGMS.Corrector.VaryingVertexIndexing

/-!
# Similarity covariance of the block-interpolation specification — `hcov` closed

`Corrector/ApproximantCovarianceFromBlockTransport.approximantGradientCovariant_of_blockTransport`
reduces the input `hcov : ApproximantGradientCovariant ms` of
`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs` to the single pathwise
statement `BlockInterpolationSimilarityCovariant`.  This module proves that statement outright,
so **`hcov` is discharged for every subsequence `ms`**, with no hypothesis
(`approximantGradientCovariant`).

## The three ingredients

* **Squares, `κ`, selection, skeleton** — `Corrector/SelectedSquareSimilarity`, for every
  `SquareIndex` and the composite similarity.
* **Centroids** — `Corrector/SimilarityCentroidCovariance.cellCentroid_similarityRelabel`.
* **The trace-minimization problem** (`centroidTraceMinimizer_transport_iff`, proved here).
  The relabelling restricts to an equivalence of patches (`patchEquiv`) that preserves
  conductances, so it is an `IsFullEmbedding` in the sense of
  `Corrector/VaryingVertexIndexing` and energies transfer with no finiteness hypothesis
  (`isFullEmbedding_patchEquiv`).  A similarity multiplies every increment by `s`, so
  vector energies pick up exactly `s²` (`vectorEnergy_positiveSimilarity`, from
  `Analysis/ExtendedEnergy.energyENN_smul` and `energyENN_sub_const`).  Boundary vertices
  correspond (frontiers are carried by the homeomorphism), the prescribed traces correspond by the
  centroid covariance, and every competitor on the target patch is the transport of a competitor
  on the source patch.  Since `0 < s² < ∞`, the finiteness clause and the minimality clause are
  both invariant.

`isBlockInterpolation_transport_iff` assembles the `m = 0` clause (centroid field) and the
`m ≠ 0` clauses (skeleton trace and selected-square minimization) into
`BlockInterpolationSimilarityCovariant`.

Nothing here assumes a law, the good event, existence or uniqueness of interpolants: the
`Classical.choose` in `phi` is handled once, on `SublinearEvent`, inside the checked reduction.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.BlockInterpolationSimilarity

open StatementIngredients DyadicApproximation Code EnvironmentLaws
open UniformGridDilationInvariance DyadicGridTranslation
open ApproximantCovarianceFromBlockTransport SelectedSquareSimilarity HarmonicCoordinateAssembly

/-! ### Energies under a similarity of the values -/

/-- **A similarity of the values multiplies vector energies by `s²`.** -/
theorem vectorEnergy_positiveSimilarity {V : Type*} (G : ReflectedWalk.ConductanceGraph V)
    (s : ℝ) (u : Plane) (f : V → Plane) :
    vectorEnergy G (fun v => positiveSimilarity s u (f v))
      = ENNReal.ofReal (s ^ 2) * vectorEnergy G f := by
  rw [vectorEnergy_eq_sum, vectorEnergy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun v => positiveSimilarity s u (f v) i)
      = fun v => (s • fun w => f w i) v - s * u i := by
    funext v
    simp [positiveSimilarity, mul_sub]
  rw [hfun, energyENN_sub_const, energyENN_smul]

section Transport

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-- The relabelling of a similarity, restricted to corresponding patches. -/
def patchEquiv (h : IsSimilarityRelabel s u hs e e' relabel) {Q Q' : Rectangle}
    (hQ : positiveSimilarity s u ⁻¹' Q'.carrier = Q.carrier) :
    patchVertices (decode e) Q ≃ patchVertices (decode e') Q' :=
  relabel.subtypeEquiv fun v => (hits_relabel_iff h hQ v).symm

/-- **The patch relabelling is a full embedding of the restricted conductance graphs.**  It is
a bijection preserving conductances, so no edge leaves its image. -/
theorem isFullEmbedding_patchEquiv (h : IsSimilarityRelabel s u hs e e' relabel)
    {Q Q' : Rectangle} (hQ : positiveSimilarity s u ⁻¹' Q'.carrier = Q.carrier) :
    VaryingVertexIndexing.IsFullEmbedding
      (restrictGraph (decode e).graph (patchVertices (decode e) Q))
      (restrictGraph (decode e').graph (patchVertices (decode e') Q'))
      (patchEquiv h hQ) where
  injective := (patchEquiv h hQ).injective
  conductance v w := h.2 v.1 w.1
  vanishing a _ ha := absurd ((patchEquiv h hQ).surjective a) ha

/-- **Energy of a transported competitor.**  Moving a patch field to the image patch and
applying the similarity to its values multiplies the energy by `s²`. -/
theorem vectorEnergy_patch_transport (h : IsSimilarityRelabel s u hs e e' relabel)
    {Q Q' : Rectangle} (hQ : positiveSimilarity s u ⁻¹' Q'.carrier = Q.carrier)
    (g : patchVertices (decode e) Q → Plane) :
    vectorEnergy (restrictGraph (decode e').graph (patchVertices (decode e') Q'))
        (fun v' => positiveSimilarity s u (g ((patchEquiv h hQ).symm v')))
      = ENNReal.ofReal (s ^ 2)
          * vectorEnergy (restrictGraph (decode e).graph (patchVertices (decode e) Q)) g := by
  rw [← (isFullEmbedding_patchEquiv h hQ).vectorEnergy_comp,
    ← vectorEnergy_positiveSimilarity _ s u g]
  congr 1
  funext v
  rw [Equiv.symm_apply_apply]

/-- The energy of the transported field on the image patch. -/
theorem vectorEnergy_patch_transportField (h : IsSimilarityRelabel s u hs e e' relabel)
    {Q Q' : Rectangle} (hQ : positiveSimilarity s u ⁻¹' Q'.carrier = Q.carrier)
    (f : Vertex e.val → Plane) :
    vectorEnergy (restrictGraph (decode e').graph (patchVertices (decode e') Q'))
        (fun v' => transportField s u relabel f v'.1)
      = ENNReal.ofReal (s ^ 2)
          * vectorEnergy (restrictGraph (decode e).graph (patchVertices (decode e) Q))
              (fun v => f v.1) :=
  vectorEnergy_patch_transport h hQ (fun v => f v.1)

/-- **The centroid-trace minimization problem is similarity covariant.** -/
theorem centroidTraceMinimizer_transport_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    {Q Q' : Rectangle} (hQ : positiveSimilarity s u ⁻¹' Q'.carrier = Q.carrier)
    (f : Vertex e.val → Plane) :
    CentroidTraceMinimizer (decode e') Q' (transportField s u relabel f)
      ↔ CentroidTraceMinimizer (decode e) Q f := by
  have hF := decode_geometry e
  have hB : ∀ v, relabel v ∈ boundaryVertices (decode e') Q'
      ↔ v ∈ boundaryVertices (decode e) Q :=
    fun v => hits_relabel_iff h (preimage_frontier_eq hs hQ) v
  have hs2 : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hs 2)).ne'
  have hEf := vectorEnergy_patch_transportField h hQ f
  constructor
  · rintro ⟨hfin, hbd, hmin⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hEf] at hfin
      refine lt_top_iff_ne_top.2 fun htop => ?_
      rw [htop, ENNReal.mul_top hs2] at hfin
      exact lt_irrefl _ hfin
    · intro v hv
      apply SimilarityCentroidCovariance.positiveSimilarity_injective hs u
      have hv' := hbd (patchEquiv h hQ v) ((hB v.1).2 hv)
      change transportField s u relabel f (relabel v.1) = cellCentroid (decode e') (relabel v.1)
        at hv'
      rw [transportField_apply, SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v.1]
        at hv'
      exact hv'
    · intro g hg
      have hg' : ∀ v' : patchVertices (decode e') Q',
          (v' : Vertex e'.val) ∈ boundaryVertices (decode e') Q' →
            positiveSimilarity s u (g ((patchEquiv h hQ).symm v'))
              = cellCentroid (decode e') v'.1 := by
        intro v' hv'
        obtain ⟨v, rfl⟩ := (patchEquiv h hQ).surjective v'
        change relabel v.1 ∈ boundaryVertices (decode e') Q' at hv'
        change positiveSimilarity s u (g ((patchEquiv h hQ).symm (patchEquiv h hQ v)))
          = cellCentroid (decode e') (relabel v.1)
        rw [Equiv.symm_apply_apply, hg v ((hB v.1).1 hv'),
          SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v.1]
      have hle := hmin (fun v' => positiveSimilarity s u (g ((patchEquiv h hQ).symm v'))) hg'
      rw [hEf, vectorEnergy_patch_transport h hQ g] at hle
      exact (ENNReal.mul_le_mul_iff_right hs2 ENNReal.ofReal_ne_top).1 hle
  · rintro ⟨hfin, hbd, hmin⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hEf]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    · intro v' hv'
      obtain ⟨v, rfl⟩ := (patchEquiv h hQ).surjective v'
      change relabel v.1 ∈ boundaryVertices (decode e') Q' at hv'
      change transportField s u relabel f (relabel v.1) = cellCentroid (decode e') (relabel v.1)
      rw [transportField_apply, hbd v ((hB v.1).1 hv'),
        SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v.1]
    · intro g' hg'
      obtain ⟨g, rfl⟩ : ∃ g : patchVertices (decode e) Q → Plane,
          (fun v' => positiveSimilarity s u (g ((patchEquiv h hQ).symm v'))) = g' := by
        refine ⟨fun v => positiveSimilarity s⁻¹ (-s • u) (g' (patchEquiv h hQ v)), ?_⟩
        funext v'
        change positiveSimilarity s u (positiveSimilarity s⁻¹ (-s • u)
          (g' (patchEquiv h hQ ((patchEquiv h hQ).symm v')))) = g' v'
        rw [Equiv.apply_symm_apply, positiveSimilarity_inverse_right s u _ hs]
      have hgb : ∀ v : patchVertices (decode e) Q,
          (v : Vertex e.val) ∈ boundaryVertices (decode e) Q →
            g v = cellCentroid (decode e) v.1 := by
        intro v hv
        apply SimilarityCentroidCovariance.positiveSimilarity_injective hs u
        have hv' := hg' (patchEquiv h hQ v) ((hB v.1).2 hv)
        change positiveSimilarity s u (g ((patchEquiv h hQ).symm (patchEquiv h hQ v)))
          = cellCentroid (decode e') (relabel v.1) at hv'
        rw [Equiv.symm_apply_apply] at hv'
        rw [hv', SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v.1]
      rw [hEf, vectorEnergy_patch_transport h hQ g]
      exact (ENNReal.mul_le_mul_iff_right hs2 ENNReal.ofReal_ne_top).2 (hmin g hgb)

/-- **The block-interpolation specification is similarity covariant.** -/
theorem isBlockInterpolation_transport_iff (h : IsSimilarityRelabel s u hs e e' relabel)
    (D : Grid) (m : ℕ) (f : Vertex e.val → Plane) :
    IsBlockInterpolation (decode e') (gridSimilarity s hs u D) m (transportField s u relabel f)
      ↔ IsBlockInterpolation (decode e) D m f := by
  have hF := decode_geometry e
  have hG : gridSimilarity s hs u D = dilate s hs (translate u D) := rfl
  rw [hG]
  by_cases hm : m = 0
  · rw [IsBlockInterpolation, IsBlockInterpolation, if_pos hm, if_pos hm]
    constructor
    · intro H
      funext v
      apply SimilarityCentroidCovariance.positiveSimilarity_injective hs u
      have hv := congrFun H (relabel v)
      rwa [transportField_apply, SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v]
        at hv
    · intro H
      funext v'
      obtain ⟨v, rfl⟩ := relabel.surjective v'
      rw [transportField_apply, H, SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v]
  · rw [IsBlockInterpolation, IsBlockInterpolation, if_neg hm, if_neg hm]
    refine and_congr ?_ ?_
    · constructor
      · intro H v hv
        apply SimilarityCentroidCovariance.positiveSimilarity_injective hs u
        have hv' := H (relabel v) ((mem_skeleton_relabel_iff h D (m : ℝ) v).2 hv)
        rwa [transportField_apply,
          SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v] at hv'
      · intro H v' hv'
        obtain ⟨v, rfl⟩ := relabel.surjective v'
        rw [transportField_apply, H v ((mem_skeleton_relabel_iff h D (m : ℝ) v).1 hv'),
          SimilarityCentroidCovariance.cellCentroid_similarityRelabel h hF v]
    · constructor
      · intro H c hsel
        exact (centroidTraceMinimizer_transport_iff h (preimage_square_squareMap hs u D c) f).1
          (H (squareMap s u D c) ((selected_squareMap_iff h D (m : ℝ) c).2 hsel))
      · intro H c' hsel
        obtain ⟨c, rfl⟩ := exists_squareMap_eq s u D c'
        exact (centroidTraceMinimizer_transport_iff h (preimage_square_squareMap hs u D c) f).2
          (H c ((selected_squareMap_iff h D (m : ℝ) c).1 hsel))

end Transport

/-! ### The closed inputs -/

/-- **`BlockInterpolationSimilarityCovariant` holds.** -/
theorem blockInterpolationSimilarityCovariant : BlockInterpolationSimilarityCovariant :=
  fun _ _ _ _ _ _ h D m f => isBlockInterpolation_transport_iff h D m f

end ReflectedGMS.BlockInterpolationSimilarity
