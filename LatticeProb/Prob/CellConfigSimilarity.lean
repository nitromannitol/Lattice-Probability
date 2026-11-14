import LatticeProb.Prob.DyadicCellConfig
import LatticeProb.Prob.DyadicCappedCovariance
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-!
# Cell masses and capped squares of a similar cell configuration

For a cell configuration `H` in `Plane` (Gwynne, Miller and Sheffield, *Harmonic functions on
mated-CRT maps*, arXiv 1807.07511, Definition 1.15) and a positive similarity `z ↦ s (z - u)` of
`Plane`, the configuration `C(H - u)` (`CellConfig.similarity`) has as cells the images of the cells
of `H`. In the coordinates `ℂ` of `planeCoord` the similarity reads `T z = s • z + b` with
`b = -(s • planeCoord⁻¹ u)`.

We show that the pulled-back cells of `C(H - u)` are the images under `T` of the pulled-back cells
of `H`, so that the cell mass is invariant under `T`, and that the capped squares `S_m^w` of
Gwynne, Miller and Sheffield (*An invariance principle for ergodic scale-free random environments*,
arXiv 1807.07515, (2.1)) are covariant: the capped square of `C(H - u)` around `T w` for the
transformed dyadic system is the image under `T` of the capped square of `H` around `w`. Since
Lebesgue measure is multiplied by `s²` under `T`, the uniform density `|S_m^w|⁻¹ 1_{S_m^w}` is
multiplied by `s⁻²`.

## Main statements

* `LatticeProb.CellConfigCappedSquare.complexCells_similarity`: the cells of `C(H - u)` are the
  images of the cells of `H`.
* `LatticeProb.CellConfigCappedSquare.cellMass_complexCells_similarity_image`: invariance of the
  cell mass.
* `LatticeProb.CellConfigCappedSquare.cappedSquare_complexCells_similarity`: covariance of the
  capped squares, for the dyadic coordinates transformed by `similarityCoord`.
* `LatticeProb.CellConfigCappedSquare.uniformDensity_cappedSquare_similarity`: the uniform density
  on the capped square is multiplied by `s⁻²`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- The translation part of the similarity `z ↦ s (z - u)` of `Plane` in the coordinates `ℂ`:
`b = -(s • planeCoord⁻¹ u)`. -/
noncomputable def similarityOffset (s : ℝ) (u : Plane) : ℂ := -(s • planeCoord.symm u)

/-- The similarity `z ↦ s (z - u)` of `Plane` reads `z ↦ s • z + b` in the coordinates `ℂ`. -/
theorem planeCoord_smul_add_similarityOffset (s : ℝ) (u : Plane) (z : ℂ) :
    planeCoord (s • z + similarityOffset s u) = positiveSimilarity s u (planeCoord z) := by
  rw [positiveSimilarity_apply, similarityOffset, map_add, map_neg, map_smul, map_smul,
    LinearIsometryEquiv.apply_symm_apply, smul_sub, sub_eq_add_neg]

/-- Lebesgue measure of `ℂ` is multiplied by `s²` under `z ↦ s • z + b`. -/
theorem volume_image_smul_add_similarityOffset (s : ℝ) (u : Plane) (A : Set ℂ) :
    volume ((fun z : ℂ => s • z + similarityOffset s u) '' A) =
      ENNReal.ofReal (s ^ 2) * volume A := by
  rw [addHaar_image_smul_add volume s (similarityOffset s u) A, Complex.finrank_real_complex,
    abs_of_nonneg (sq_nonneg s)]

/-- The transformed dyadic coordinates: the image of the dyadic system with coordinates
`q = (t, o₁, o₂)` under `z ↦ s • z + b` is the dyadic system with coordinates
`similarityCoord s u q` (scale coordinate `fract (t + log₂ s)`, offsets dilated by
`⌊t + log₂ s⌋` generations and then shifted by `2^{-fract (t + log₂ s)} b`). -/
noncomputable def similarityCoord (s : ℝ) (u : Plane) (q : ℝ × (ℕ → ℝ) × (ℕ → ℝ)) :
    ℝ × (ℕ → ℝ) × (ℕ → ℝ) :=
  (Int.fract (q.1 + Real.logb 2 s),
    shiftOffsets ((2 : ℝ) ^ (-Int.fract (q.1 + Real.logb 2 s)) * (similarityOffset s u).re)
      (dilateOffsets ⌊q.1 + Real.logb 2 s⌋ q.2.1),
    shiftOffsets ((2 : ℝ) ^ (-Int.fract (q.1 + Real.logb 2 s)) * (similarityOffset s u).im)
      (dilateOffsets ⌊q.1 + Real.logb 2 s⌋ q.2.2))

variable {H : CellConfig} (s : ℝ) (u : Plane) (hs : 0 < s)

/-- **The pulled-back cells of `C(H - u)` are the images of the pulled-back cells of `H`** under
`z ↦ s • z + b`, through the correspondence of cells `CellConfig.similarityCellEquiv`. -/
theorem complexCells_similarity (K : H.cells) :
    complexCells (H.similarity s u hs) (CellConfig.similarityCellEquiv s u hs K) =
      (fun z : ℂ => s • z + similarityOffset s u) '' complexCells H K := by
  ext z
  show planeCoord z ∈ (positiveSimilarityHomeomorph s u hs) '' (K.1 : Set Plane) ↔
    z ∈ (fun z : ℂ => s • z + similarityOffset s u) '' complexCells H K
  constructor
  · rintro ⟨p, hp, hpz⟩
    refine ⟨planeCoord.symm p, ?_, ?_⟩
    · show planeCoord (planeCoord.symm p) ∈ (K.1 : Set Plane)
      rwa [LinearIsometryEquiv.apply_symm_apply]
    · apply planeCoord.injective
      rw [planeCoord_smul_add_similarityOffset, LinearIsometryEquiv.apply_symm_apply]
      exact hpz
  · rintro ⟨y, hy, rfl⟩
    exact ⟨planeCoord y, hy, (planeCoord_smul_add_similarityOffset s u y).symm⟩

/-- The cell mass of `C(H - u)` in the coordinates `ℂ` is the cell mass of the images of the cells
of `H` under `z ↦ s • z + b`. -/
theorem cellMass_complexCells_similarity :
    cellMass volume (complexCells (H.similarity s u hs)) =
      cellMass volume fun K : H.cells =>
        (fun z : ℂ => s • z + similarityOffset s u) '' complexCells H K := by
  funext S
  unfold cellMass
  refine ((CellConfig.similarityCellEquiv s u hs).tsum_eq _).symm.trans (tsum_congr fun K => ?_)
  simp only [complexCells_similarity]

/-- **Invariance of the cell mass under a similarity**: the cell mass of `T S` for `C(H - u)` is
the cell mass of `S` for `H`. -/
theorem cellMass_complexCells_similarity_image (S : Set ℂ) :
    cellMass volume (complexCells (H.similarity s u hs))
        ((fun z : ℂ => s • z + similarityOffset s u) '' S) =
      cellMass volume (complexCells H) S := by
  rw [cellMass_complexCells_similarity]
  exact cellMass_image_smul_add volume (complexCells H) hs.ne' (similarityOffset s u) S

/-- **Covariance of the capped squares under a similarity**: `S_m^{T w}` of `C(H - u)` for the
dyadic system with coordinates `similarityCoord s u q` is `T S_m^w` of `H` for the dyadic system
with coordinates `q`, where `T z = s • z + b`. -/
theorem cappedSquare_complexCells_similarity (q : ℝ × (ℕ → ℝ) × (ℕ → ℝ))
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w : ℂ) :
    cappedSquare
        (dyadicSquares (similarityCoord s u q).1 (similarityCoord s u q).2.1
          (similarityCoord s u q).2.2)
        (cellMass volume (complexCells (H.similarity s u hs))) m (s • w + similarityOffset s u) =
      (fun z : ℂ => s • z + similarityOffset s u) ''
        cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume (complexCells H)) m w := by
  have h2 : (2 : ℝ) ^ Real.logb 2 s = s := Real.rpow_logb (by norm_num) (by norm_num) hs
  have h := cappedSquare_dyadicSquares_image_smul_add (c := complexCells H) h₁ h₂
    (Real.logb 2 s) q.1 (similarityOffset s u) m w
  rw [h2] at h
  rw [cellMass_complexCells_similarity]
  exact h

include hs in
/-- The uniform density `|T A|⁻¹ 1_{T A}` at `T w` is `s⁻²` times the uniform density
`|A|⁻¹ 1_A` at `w`, for `T z = s • z + b`. -/
theorem inv_volume_mul_indicator_image (A : Set ℂ) (w : ℂ) :
    (volume ((fun z : ℂ => s • z + similarityOffset s u) '' A))⁻¹ *
        ((fun z : ℂ => s • z + similarityOffset s u) '' A).indicator (fun _ => (1 : ℝ≥0∞))
          (s • w + similarityOffset s u) =
      (ENNReal.ofReal (s ^ 2))⁻¹ * ((volume A)⁻¹ * A.indicator (fun _ => (1 : ℝ≥0∞)) w) := by
  have hinj : Function.Injective fun z : ℂ => s • z + similarityOffset s u :=
    injective_smul_add hs.ne' _
  have hmem : (s • w + similarityOffset s u ∈
      (fun z : ℂ => s • z + similarityOffset s u) '' A) ↔ w ∈ A :=
    hinj.mem_set_image
  have hs2 : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hs 2)).ne'
  rw [volume_image_smul_add_similarityOffset,
    ENNReal.mul_inv (Or.inl hs2) (Or.inl ENNReal.ofReal_ne_top), mul_assoc]
  by_cases hw : w ∈ A
  · rw [indicator_of_mem (hmem.2 hw), indicator_of_mem hw]
  · rw [indicator_of_notMem (mt hmem.1 hw), indicator_of_notMem hw]

/-- **Covariance of the uniform density on the capped square**: for `T z = s • z + b`, the density
`|S_m^{T w₀}|⁻¹ 1_{S_m^{T w₀}}` of `C(H - u)` for the transformed dyadic system, at `T w₁`, is `s⁻²`
times the density `|S_m^{w₀}|⁻¹ 1_{S_m^{w₀}}` of `H`, at `w₁`. -/
theorem uniformDensity_cappedSquare_similarity (q : ℝ × (ℕ → ℝ) × (ℕ → ℝ))
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w₀ w₁ : ℂ) :
    (volume (cappedSquare
        (dyadicSquares (similarityCoord s u q).1 (similarityCoord s u q).2.1
          (similarityCoord s u q).2.2)
        (cellMass volume (complexCells (H.similarity s u hs))) m
        (s • w₀ + similarityOffset s u)))⁻¹ *
      (cappedSquare
        (dyadicSquares (similarityCoord s u q).1 (similarityCoord s u q).2.1
          (similarityCoord s u q).2.2)
        (cellMass volume (complexCells (H.similarity s u hs))) m
        (s • w₀ + similarityOffset s u)).indicator (fun _ => (1 : ℝ≥0∞))
          (s • w₁ + similarityOffset s u) =
      (ENNReal.ofReal (s ^ 2))⁻¹ *
        ((volume (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
            (cellMass volume (complexCells H)) m w₀))⁻¹ *
          (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
            (cellMass volume (complexCells H)) m w₀).indicator (fun _ => (1 : ℝ≥0∞)) w₁) := by
  rw [cappedSquare_complexCells_similarity s u hs q h₁ h₂ m w₀]
  exact inv_volume_mul_indicator_image s u hs _ w₁

end LatticeProb.CellConfigCappedSquare
