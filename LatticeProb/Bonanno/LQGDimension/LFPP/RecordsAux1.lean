/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordsAux1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
* square grids of side `s` (`gridIdx`, `gridPt`) and the count of grid points in a ball;
* polygons given by a vertex function `f : ℕ → ℂ` (the list `f 0, …, f m`): edges, length,
  normalized arclength average;
* membership of actual configurations in the similarity images of the normalized local
  families `smallFamily`, `largeFamily`;
* the vertex-deviation bound for polygons whose edges but the last have length `R / M`.
-/

noncomputable section

open Real
open scoped Classical ComplexConjugate

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

/-! ## Square grids -/

/-- Index of the grid square of side `s` containing `z`. -/
def gridIdx (s : ℝ) (z : ℂ) : ℤ × ℤ := (⌊z.re / s⌋, ⌊z.im / s⌋)

/-- Lower-left corner of the grid square of side `s` with index `a`. -/
def gridPt (s : ℝ) (a : ℤ × ℤ) : ℂ := ⟨(a.1 : ℝ) * s, (a.2 : ℝ) * s⟩

theorem floor_mul_bounds {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (⌊t / s⌋ : ℝ) * s ≤ t ∧ t < (⌊t / s⌋ : ℝ) * s + s := by
  have a1 := Int.floor_le (t / s)
  have a2 := Int.lt_floor_add_one (t / s)
  constructor
  · rwa [le_div_iff₀ hs] at a1
  · rw [div_lt_iff₀ hs] at a2; linarith

theorem abs_sub_floor_mul_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |t - (⌊t / s⌋ : ℝ) * s| ≤ s := by
  obtain ⟨h1, h2⟩ := floor_mul_bounds hs t
  rw [abs_le]; constructor <;> linarith

theorem norm_sub_gridPt_le {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ‖z - gridPt s (gridIdx s z)‖ ≤ 2 * s := by
  calc ‖z - gridPt s (gridIdx s z)‖
      ≤ |(z - gridPt s (gridIdx s z)).re| + |(z - gridPt s (gridIdx s z)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - (⌊z.re / s⌋ : ℝ) * s| + |z.im - (⌊z.im / s⌋ : ℝ) * s| := by
        simp [gridPt, gridIdx]
    _ ≤ s + s := add_le_add (abs_sub_floor_mul_le hs _) (abs_sub_floor_mul_le hs _)
    _ = 2 * s := by ring

/-- The integer box containing all grid indices whose corner lies within `ρ` of `q`. -/
def gridBox (s : ℝ) (q : ℂ) (ρ : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌈(q.re - ρ) / s⌉ ⌊(q.re + ρ) / s⌋ ×ˢ Finset.Icc ⌈(q.im - ρ) / s⌉ ⌊(q.im + ρ) / s⌋

theorem mem_gridBox {s ρ : ℝ} (hs : 0 < s) {q : ℂ} {a : ℤ × ℤ}
    (h : ‖gridPt s a - q‖ ≤ ρ) : a ∈ gridBox s q ρ := by
  have hre : |(a.1 : ℝ) * s - q.re| ≤ ρ := by
    have := (Complex.abs_re_le_norm (gridPt s a - q)).trans h
    simpa [gridPt] using this
  have him : |(a.2 : ℝ) * s - q.im| ≤ ρ := by
    have := (Complex.abs_im_le_norm (gridPt s a - q)).trans h
    simpa [gridPt] using this
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  simp only [gridBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Int.ceil_le, div_le_iff₀ hs]; linarith
  · rw [Int.le_floor, le_div_iff₀ hs]; linarith
  · rw [Int.ceil_le, div_le_iff₀ hs]; linarith
  · rw [Int.le_floor, le_div_iff₀ hs]; linarith

theorem card_Icc_ceil_floor_le {x y : ℝ} (h : x ≤ y) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  rcases le_or_gt 0 (⌊y⌋ + 1 - ⌈x⌉) with hz | hz
  · have e : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
    rw [e]
    push_cast
    linarith [Int.floor_le y, Int.le_ceil x]
  · rw [Int.toNat_of_nonpos hz.le]
    simp; linarith

theorem card_gridBox_le {s ρ : ℝ} (hs : 0 < s) (hρ : 0 ≤ ρ) (q : ℂ) :
    ((gridBox s q ρ).card : ℝ) ≤ (2 * ρ / s + 1) ^ 2 := by
  have hle : ∀ t : ℝ, (t - ρ) / s ≤ (t + ρ) / s := fun t =>
    div_le_div_of_nonneg_right (by linarith) hs.le
  have key : ∀ t : ℝ, (t + ρ) / s - (t - ρ) / s + 1 = 2 * ρ / s + 1 := by
    intro t; field_simp; ring
  rw [gridBox, Finset.card_product, Nat.cast_mul, sq]
  have h1 := card_Icc_ceil_floor_le (hle q.re)
  have h2 := card_Icc_ceil_floor_le (hle q.im)
  rw [key] at h1 h2
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)

/-! ## Polygons given by vertex functions -/

/-! ## Normalization by similarities -/

/-! ## Vertex deviation of polygons with small excess -/

end LQGDimension.LFPPRecords
