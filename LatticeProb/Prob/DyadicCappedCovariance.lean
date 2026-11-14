import LatticeProb.Prob.DyadicCappedSquare
import LatticeProb.Euclidean.CellMass

/-!
# Covariance of the capped squares of the dyadic system under similarities

Let `𝒟` be a family of squares, `c` a family of cells and `Ŝ_m^w(𝒟, c)` the largest square of `𝒟`
containing `w` whose cell mass `∑_i |c_i ∩ S| / |c_i|` is at most `m` (Gwynne, Miller and
Sheffield, *An invariance principle for ergodic scale-free random environments*,
arXiv 1807.07515, (2.1)). Area ratios are invariant under similarities, so for
`T z = r • z + b` with `r ≠ 0`,

  `Ŝ_m^{T w}(T 𝒟, T c) = T (Ŝ_m^w(𝒟, c))`.

For the dyadic system of the plane with scale coordinate `s` and offset sequences `o₁, o₂`, the
image under `z ↦ 2^t • z + b` is again a dyadic system, with scale coordinate `fract (s + t)` and
offsets dilated by `⌊s + t⌋` generations and then shifted by `b`. This gives the covariance of
`Ŝ_m^w` in the coordinates of the uniform dyadic system, whose law is invariant under this change
of coordinates (Lemma 2.1 of the paper cited above).

## Main statements

* `LatticeProb.CappedSquare.isCappedSquare_cellMass_image_smul_add`,
  `LatticeProb.CappedSquare.cappedSquare_cellMass_image_smul_add`: covariance under a similarity.
* `LatticeProb.DyadicOffset.image_dyadicSquares_smul_add`: the image of the dyadic system under
  `z ↦ 2^t • z + b`, in coordinates.
* `LatticeProb.DyadicOffset.isCappedSquare_dyadicSquares_image_smul_add`,
  `LatticeProb.DyadicOffset.cappedSquare_dyadicSquares_image_smul_add`: covariance of the capped
  squares of the dyadic system.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace LatticeProb.CappedSquare

open CellMass

section Similarity

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : ι → Set V) {r : ℝ}

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem injective_smul_add (hr : r ≠ 0) (b : V) : Injective fun z : V => r • z + b :=
  fun _ _ hxy => smul_right_injective V hr (add_right_cancel hxy)

/-- **Covariance of `Ŝ_m^w` under a similarity**: `S` is the capped square of mass `m` around `w`
for the family `𝒟` and the cells `c` exactly when `T S` is the capped square of mass `m` around
`T w` for the family `T 𝒟` and the cells `T c`, where `T z = r • z + b` with `r ≠ 0`. -/
theorem isCappedSquare_cellMass_image_smul_add (hr : r ≠ 0) (b : V) (𝒟 : Set (Set V))
    (m : ℝ≥0∞) (w : V) (S : Set V) :
    IsCappedSquare (image (fun z => r • z + b) '' 𝒟)
        (cellMass μ fun i => (fun z => r • z + b) '' c i) m (r • w + b)
        ((fun z => r • z + b) '' S) ↔
      IsCappedSquare 𝒟 (cellMass μ c) m w S :=
  isCappedSquare_image (injective_smul_add hr b) (fun S _ => cellMass_image_smul_add μ c hr b S)
    m w S

/-- Covariance of the union of the candidate squares: `Ŝ_m^{T w}(T 𝒟, T c) = T Ŝ_m^w(𝒟, c)`. -/
theorem cappedSquare_cellMass_image_smul_add (hr : r ≠ 0) (b : V) (𝒟 : Set (Set V))
    (m : ℝ≥0∞) (w : V) :
    cappedSquare (image (fun z => r • z + b) '' 𝒟)
        (cellMass μ fun i => (fun z => r • z + b) '' c i) m (r • w + b) =
      (fun z => r • z + b) '' cappedSquare 𝒟 (cellMass μ c) m w :=
  cappedSquare_image (injective_smul_add hr b) (fun S _ => cellMass_image_smul_add μ c hr b S) m w

end Similarity

end LatticeProb.CappedSquare

namespace LatticeProb.DyadicOffset

open CellMass CappedSquare

variable {o₁ o₂ : ℕ → ℝ}

/-- The image of the dyadic system with coordinates `(s, o₁, o₂)` under `z ↦ 2^t • z + b` is the
dyadic system with scale coordinate `fract (s + t)` and the offsets dilated by `⌊s + t⌋`
generations and then shifted by `2^{-fract (s + t)} b`. -/
theorem image_dyadicSquares_smul_add (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) (t s : ℝ)
    (b : ℂ) :
    image (fun z : ℂ => (2 : ℝ) ^ t • z + b) '' dyadicSquares s o₁ o₂ =
      dyadicSquares (Int.fract (s + t))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.re) (dilateOffsets ⌊s + t⌋ o₁))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.im) (dilateOffsets ⌊s + t⌋ o₂)) := by
  have h : image (fun z : ℂ => (2 : ℝ) ^ t • z + b) =
      image (fun z : ℂ => z + b) ∘ image (fun z : ℂ => (2 : ℝ) ^ t • z) := by
    funext S
    simp only [comp_apply, image_image]
  rw [h, image_comp, image_dyadicSquares_smul h₁ h₂, image_dyadicSquares_add]

variable {ι : Type*} (c : ι → Set ℂ)

/-- **Covariance of the capped squares of the dyadic system** under `T z = 2^t • z + b`: `S` is
the capped square of mass `m` around `w` for the system `(s, o₁, o₂)` and the cells `c` exactly
when `T S` is the capped square of mass `m` around `T w` for the transformed system and the cells
`T c`. -/
theorem isCappedSquare_dyadicSquares_image_smul_add (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    (t s : ℝ) (b : ℂ) (m : ℝ≥0∞) (w : ℂ) (S : Set ℂ) :
    IsCappedSquare
        (dyadicSquares (Int.fract (s + t))
          (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.re) (dilateOffsets ⌊s + t⌋ o₁))
          (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.im) (dilateOffsets ⌊s + t⌋ o₂)))
        (cellMass volume fun i => (fun z : ℂ => (2 : ℝ) ^ t • z + b) '' c i) m
        ((2 : ℝ) ^ t • w + b) ((fun z : ℂ => (2 : ℝ) ^ t • z + b) '' S) ↔
      IsCappedSquare (dyadicSquares s o₁ o₂) (cellMass volume c) m w S := by
  rw [← image_dyadicSquares_smul_add h₁ h₂]
  exact isCappedSquare_cellMass_image_smul_add volume c (by positivity) b _ m w S

/-- Covariance of `Ŝ_m^w` for the dyadic system: `Ŝ_m^{T w}` of the transformed system and cells
is `T Ŝ_m^w`. -/
theorem cappedSquare_dyadicSquares_image_smul_add (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    (t s : ℝ) (b : ℂ) (m : ℝ≥0∞) (w : ℂ) :
    cappedSquare
        (dyadicSquares (Int.fract (s + t))
          (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.re) (dilateOffsets ⌊s + t⌋ o₁))
          (shiftOffsets ((2 : ℝ) ^ (-Int.fract (s + t)) * b.im) (dilateOffsets ⌊s + t⌋ o₂)))
        (cellMass volume fun i => (fun z : ℂ => (2 : ℝ) ^ t • z + b) '' c i) m
        ((2 : ℝ) ^ t • w + b) =
      (fun z : ℂ => (2 : ℝ) ^ t • z + b) '' cappedSquare (dyadicSquares s o₁ o₂)
        (cellMass volume c) m w := by
  rw [← image_dyadicSquares_smul_add h₁ h₂]
  exact cappedSquare_cellMass_image_smul_add volume c (by positivity) b _ m w

end LatticeProb.DyadicOffset
