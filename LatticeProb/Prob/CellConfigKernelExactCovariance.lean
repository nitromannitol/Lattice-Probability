import LatticeProb.Prob.CellConfigKernelCovariance

/-!
# Exact covariance of the capped-square kernel for compatible dyadic systems

Let `D` be the dyadic system of the plane with coordinates `q = (t, o¹, o²)` (scale coordinate and
two offset sequences), and let `T z = 2^τ • z + b`. The image of `D` under `T` is the dyadic system
with coordinates `(fract (t + τ), o¹', o²')`, the offsets dilated by `⌊t + τ⌋` generations and then
shifted (`image_dyadicSquares_smul_add`). This file proves that, for compatible offsets, the
correspondence holds square by square and generation by generation: the square of generation `j`
around `w` is carried by `T` onto the square of generation `j + ⌊t + τ⌋` around `T w` of the image
system. Consequently the uniform-average kernel `|Ŝ_m^{w₀}|⁻¹ 1(w₁ ∈ Ŝ_m^{w₀})` of a cell
configuration, in its measurable selected-sum form, is covariant under a similarity
`H ↦ C(H - u)` for *every* compatible dyadic system, not only almost surely
(compare `ae_averageKernel_similarity`).

## Main results
* `LatticeProb.DyadicOffset.gridFloor_similarity`: covariance of the left ends of the grid
  intervals under `x ↦ 2^τ x + c`.
* `LatticeProb.DyadicOffset.squareAt_similarity`: `T (Q_j(w)) = Q'_{j + ⌊t + τ⌋}(T w)`.
* `LatticeProb.CellConfigCappedSquare.averageKernel_similarity`: if `H'` is `C(H - u)` and the
  offsets of `q` are compatible, the kernel of `H'` for the transformed coordinates at
  `(T w₀, T w₁)` is `s⁻²` times the kernel of `H` at `(w₀, w₁)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-- The side `2^{fract (t + τ) + j + ⌊t + τ⌋}` of the generation `j + ⌊t + τ⌋` of the image system
is `2^τ` times the side `2^{t + j}` of the generation `j`. -/
theorem two_rpow_fract_add_floor (τ t : ℝ) (j : ℤ) :
    (2 : ℝ) ^ (Int.fract (t + τ) + (((j + ⌊t + τ⌋ : ℤ)) : ℝ)) =
      (2 : ℝ) ^ τ * (2 : ℝ) ^ (t + (j : ℝ)) := by
  rw [← Real.rpow_add two_pos]
  congr 1
  have h := Int.fract_add_floor (t + τ)
  push_cast
  linarith

/-- **Covariance of the grid points of one coordinate** under `x ↦ 2^τ x + c`, for compatible
offsets: `2^τ x + c` is a grid point of generation `j + ⌊t + τ⌋` of the image system exactly when
`x` is a grid point of generation `j`. -/
theorem mem_gridPoints_similarity {o : ℕ → ℝ} (ho : IsCompatible o) (τ t c : ℝ) (j : ℤ) (x : ℝ) :
    (2 : ℝ) ^ τ * x + c ∈ gridPoints (Int.fract (t + τ))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (t + τ)) * c) (dilateOffsets ⌊t + τ⌋ o))
        (j + ⌊t + τ⌋) ↔
      x ∈ gridPoints t o j := by
  rw [mem_gridPoints_shiftOffsets, ← image_two_rpow_mul_gridPoints_eq ho τ t j]
  have hc : (2 : ℝ) ^ τ * x + c -
      (2 : ℝ) ^ Int.fract (t + τ) * ((2 : ℝ) ^ (-Int.fract (t + τ)) * c) = (2 : ℝ) ^ τ * x := by
    rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
    ring
  rw [hc]
  exact (mul_right_injective₀ (by positivity : (2 : ℝ) ^ τ ≠ 0)).mem_set_image

/-- **Covariance of the grid floor** under `x ↦ 2^τ x + c`, for compatible offsets. -/
theorem gridFloor_similarity {o : ℕ → ℝ} (ho : IsCompatible o) (τ t c : ℝ) (j : ℤ) (x : ℝ) :
    gridFloor (Int.fract (t + τ))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (t + τ)) * c) (dilateOffsets ⌊t + τ⌋ o))
        (j + ⌊t + τ⌋) ((2 : ℝ) ^ τ * x + c) =
      (2 : ℝ) ^ τ * gridFloor t o j x + c := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (t + (j : ℝ)) := by positivity
  have hτ : (0 : ℝ) < (2 : ℝ) ^ τ := by positivity
  have hp' : (0 : ℝ) < (2 : ℝ) ^ (Int.fract (t + τ) + (((j + ⌊t + τ⌋ : ℤ)) : ℝ)) := by
    positivity
  have hmem := (mem_gridPoints_similarity ho τ t c j (gridFloor t o j x)).2 (gridFloor_mem t o j x)
  have hle : gridFloor t o j x ≤ x := latticeFloor_le hp _ x
  have hlt : x < gridFloor t o j x + (2 : ℝ) ^ (t + (j : ℝ)) := lt_latticeFloor_add hp _ x
  have h1 : (2 : ℝ) ^ τ * gridFloor t o j x + c ≤ (2 : ℝ) ^ τ * x + c := by
    have h := mul_le_mul_of_nonneg_left hle hτ.le
    linarith
  have h2 : (2 : ℝ) ^ τ * x + c < (2 : ℝ) ^ τ * gridFloor t o j x + c +
      (2 : ℝ) ^ (Int.fract (t + τ) + (((j + ⌊t + τ⌋ : ℤ)) : ℝ)) := by
    rw [two_rpow_fract_add_floor]
    have h := mul_lt_mul_of_pos_left hlt hτ
    rw [mul_add] at h
    linarith
  exact (eq_latticeFloor hp' hmem h1 h2).symm

/-- The image of a corner square under `z ↦ r • z + b`, `r > 0`. -/
theorem image_smul_add_cornerSquare {r : ℝ} (hr : 0 < r) (b : ℂ) (a a' ℓ : ℝ) :
    (fun z : ℂ => r • z + b) '' cornerSquare a a' ℓ =
      cornerSquare (r * a + b.re) (r * a' + b.im) (r * ℓ) := by
  have h : (fun z : ℂ => r • z + b) = (fun z : ℂ => z + b) ∘ (fun z : ℂ => r • z) := rfl
  rw [h, image_comp, image_smul_cornerSquare hr]
  ext z
  simp only [mem_image, mem_cornerSquare]
  constructor
  · rintro ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [Complex.add_re, Complex.add_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨z - b, ⟨?_, ?_, ?_, ?_⟩, sub_add_cancel z b⟩ <;>
      simp only [Complex.sub_re, Complex.sub_im] <;> linarith

/-- **Covariance of the squares around a point**: for compatible offsets and `T z = 2^τ • z + b`,
the square of generation `j + ⌊t + τ⌋` around `T w` of the image system is the image under `T` of
the square of generation `j` around `w`. -/
theorem squareAt_similarity {o₁ o₂ : ℕ → ℝ} (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    (τ t : ℝ) (b : ℂ) (j : ℤ) (w : ℂ) :
    squareAt (Int.fract (t + τ))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (t + τ)) * b.re) (dilateOffsets ⌊t + τ⌋ o₁))
        (shiftOffsets ((2 : ℝ) ^ (-Int.fract (t + τ)) * b.im) (dilateOffsets ⌊t + τ⌋ o₂))
        (j + ⌊t + τ⌋) ((2 : ℝ) ^ τ • w + b) =
      (fun z : ℂ => (2 : ℝ) ^ τ • z + b) '' squareAt t o₁ o₂ j w := by
  have hre : ((2 : ℝ) ^ τ • w + b).re = (2 : ℝ) ^ τ * w.re + b.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have him : ((2 : ℝ) ^ τ • w + b).im = (2 : ℝ) ^ τ * w.im + b.im := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  have hτ : (0 : ℝ) < (2 : ℝ) ^ τ := by positivity
  unfold squareAt
  rw [hre, him, gridFloor_similarity h₁, gridFloor_similarity h₂, two_rpow_fract_add_floor,
    image_smul_add_cornerSquare hτ]

end LatticeProb.DyadicOffset

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- **Covariance of the squares around a point under a similarity**: for compatible offsets, the
square of generation `j + ⌊t + log₂ s⌋` around `T w` of the dyadic system `similarityCoord s u q` is
`T` of the square of generation `j` around `w` of the system `q`, where `T z = s • z + b`. -/
theorem squareAt_similarityCoord (s : ℝ) (u : Plane) (hs : 0 < s) (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (j : ℤ) (w : ℂ) :
    squareAt (similarityCoord s u q).1 (similarityCoord s u q).2.1 (similarityCoord s u q).2.2
        (j + ⌊q.1 + Real.logb 2 s⌋) (s • w + similarityOffset s u) =
      (fun z : ℂ => s • z + similarityOffset s u) '' squareAt q.1 q.2.1 q.2.2 j w := by
  have h2 : (2 : ℝ) ^ Real.logb 2 s = s := Real.rpow_logb (by norm_num) (by norm_num) hs
  have h := squareAt_similarity h₁ h₂ (Real.logb 2 s) q.1 (similarityOffset s u) j w
  rw [h2] at h
  exact h

variable {s : ℝ} {u : Plane} {hs : 0 < s} {H H' : GMSSpace}

/-- **Covariance of the selected generations**: if `H'` is `C(H - u)` and the offsets of `q` are
compatible, the generation `j + ⌊t + log₂ s⌋` is selected at `T w` for `H'` and the transformed
system exactly when `j` is selected at `w` for `H` and `q`. -/
theorem mem_selectionSet_similarity (hHH' : IsSimilar s u hs H H') (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w : ℂ) (j : ℤ) :
    j + ⌊q.1 + Real.logb 2 s⌋ ∈ selectionSet (complexCells H'.1) m (similarityCoord s u q)
        (s • w + similarityOffset s u) ↔
      j ∈ selectionSet (complexCells H.1) m q w := by
  have hH' : H'.1 = H.1.similarity s u hs := hHH'
  have e : j + ⌊q.1 + Real.logb 2 s⌋ + 1 = (j + 1) + ⌊q.1 + Real.logb 2 s⌋ := by ring
  simp only [selectionSet, Set.mem_ofPred_eq, e, squareAt_similarityCoord s u hs q h₁ h₂]
  rw [hH', cellMass_complexCells_similarity_image, cellMass_complexCells_similarity_image]

/-- **Covariance of the selected sum**: for compatible offsets, the sum over the selected
generations at `T w` for `H' = C(H - u)` and the transformed system of `g` is the sum over the
selected generations at `w` for `H` and `q` of `S ↦ g (T S)`. -/
theorem selectedSum_similarity (hHH' : IsSimilar s u hs H H') (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w : ℂ)
    (g : Set ℂ → ℝ≥0∞) :
    selectedSum (complexCells H'.1) m (similarityCoord s u q) (s • w + similarityOffset s u) g =
      selectedSum (complexCells H.1) m q w
        fun S => g ((fun z : ℂ => s • z + similarityOffset s u) '' S) := by
  unfold selectedSum
  refine ((Equiv.addRight ⌊q.1 + Real.logb 2 s⌋).tsum_eq _).symm.trans ?_
  refine tsum_congr fun j => ?_
  simp only [Equiv.coe_addRight]
  by_cases hj : j ∈ selectionSet (complexCells H.1) m q w
  · simp only [indicator_of_mem hj,
      indicator_of_mem ((mem_selectionSet_similarity hHH' q h₁ h₂ m w j).2 hj),
      squareAt_similarityCoord s u hs q h₁ h₂]
  · simp only [indicator_of_notMem hj,
      indicator_of_notMem (fun h => hj ((mem_selectionSet_similarity hHH' q h₁ h₂ m w j).1 h))]

/-- A constant factor comes out of the selected sum. -/
theorem selectedSum_const_mul {ι : Type*} (c : ι → Set ℂ) (m : ℝ≥0∞) (q : DyadicCoord) (w : ℂ)
    (a : ℝ≥0∞) (g : Set ℂ → ℝ≥0∞) :
    selectedSum c m q w (fun S => a * g S) = a * selectedSum c m q w g := by
  unfold selectedSum
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  by_cases hj : j ∈ selectionSet c m q w
  · simp only [indicator_of_mem hj]
  · simp only [indicator_of_notMem hj, mul_zero]

/-- **Exact covariance of the uniform-average kernel**: if `H'` is `C(H - u)` and the offsets of
`q` are compatible, then for every mass `m` and all points `w₀, w₁` the kernel of `H'` for the
transformed coordinates at `(T w₀, T w₁)` is `s⁻²` times the kernel of `H` at `(w₀, w₁)`, where
`T z = s • z + b`. -/
theorem averageKernel_similarity (hHH' : IsSimilar s u hs H H') (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (m : ℝ≥0∞) (w₀ w₁ : ℂ) :
    averageKernel m (H', (similarityCoord s u q, s • w₀ + similarityOffset s u),
        s • w₁ + similarityOffset s u) =
      ENNReal.ofReal ((s ^ 2)⁻¹) * averageKernel m (H, (q, w₀), w₁) := by
  show selectedSum (complexCells H'.1) m (similarityCoord s u q) (s • w₀ + similarityOffset s u)
      (fun S => (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) (s • w₁ + similarityOffset s u)) =
    ENNReal.ofReal ((s ^ 2)⁻¹) * selectedSum (complexCells H.1) m q w₀
      (fun S => (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) w₁)
  rw [selectedSum_similarity hHH' q h₁ h₂ m w₀]
  simp only [inv_volume_mul_indicator_image s u hs]
  rw [selectedSum_const_mul, ENNReal.ofReal_inv_of_pos (pow_pos hs 2)]

end LatticeProb.CellConfigCappedSquare
