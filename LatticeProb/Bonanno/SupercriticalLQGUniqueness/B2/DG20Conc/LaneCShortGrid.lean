/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCShortGrid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

def laneCShortBlocks : Finset (ℤ × ℤ) :=
  Finset.Icc (-24 : ℤ) 32 ×ˢ Finset.Icc (-24 : ℤ) 32

open Classical in
def laneCShortRects : Finset (Circle × ℂ) :=
  laneCShortBlocks.biUnion (T20D.shortJ 3)

open Classical in
theorem laneCShortRects_eq :
    laneCShortRects = laneCShortBlocks.biUnion (T20D.shortJ 3) := rfl

 

theorem laneC_short_grid_covers {z : ℂ}
    (hre : z.re ∈ Icc (-3 : ℝ) 4)
    (him : z.im ∈ Icc (-3 : ℝ) 4) :
    ∃ b ∈ laneCShortBlocks, z ∈ T20.dyBlock 3 b := by
  let b : ℤ × ℤ := (⌊8 * z.re⌋, ⌊8 * z.im⌋)
  have hxlo : (-24 : ℤ) ≤ b.1 := by
    dsimp [b]
    apply Int.le_floor.mpr
    push_cast
    linarith [hre.1]
  have hxhi : b.1 ≤ (32 : ℤ) := by
    dsimp [b]
    apply Int.floor_le_iff.mpr
    push_cast
    linarith [hre.2]
  have hylo : (-24 : ℤ) ≤ b.2 := by
    dsimp [b]
    apply Int.le_floor.mpr
    push_cast
    linarith [him.1]
  have hyhi : b.2 ≤ (32 : ℤ) := by
    dsimp [b]
    apply Int.floor_le_iff.mpr
    push_cast
    linarith [him.2]
  refine ⟨b, ?_, ?_⟩
  · simp only [laneCShortBlocks, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
  · simp only [T20.dyBlock, pow_succ, pow_zero, Complex.mem_reProdIm, mem_Icc]
    constructor <;> constructor <;> dsimp [b] <;> push_cast <;>
      nlinarith [Int.floor_le (8 * z.re), Int.lt_floor_add_one (8 * z.re),
        Int.floor_le (8 * z.im), Int.lt_floor_add_one (8 * z.im)]

theorem laneC_shortRects_card_le : (laneCShortRects.card : ℝ) ≤ 12996 := by
  classical
  have hcard : laneCShortRects.card ≤
      ∑ b ∈ laneCShortBlocks, (T20D.shortJ 3 b).card := Finset.card_biUnion_le
  have hsum : (∑ b ∈ laneCShortBlocks, (T20D.shortJ 3 b).card) ≤
      4 * laneCShortBlocks.card := by
    calc
      _ ≤ ∑ _b ∈ laneCShortBlocks, 4 :=
        Finset.sum_le_sum (fun b _ => T20D.card_shortJ_le 3 b)
      _ = _ := by simp [mul_comm]
  have hblocks : laneCShortBlocks.card = 3249 := by
    simp [laneCShortBlocks, Int.card_Icc]
  exact_mod_cast (by omega : laneCShortRects.card ≤ 12996)

 

theorem laneC_short_hatBox_dist_lt_half {b : ℤ × ℤ} {x y : ℂ}
    (hx : x ∈ T20.dyBlock 3 b) (hy : y ∈ T20D.hatBox 3 b) :
    dist x y < (1 / 2 : ℝ) := by
  have hs : (2 : ℝ)⁻¹ ^ (3 : ℕ) = 1 / 8 := by norm_num
  have hx' :
      (b.1 : ℝ) / 8 ≤ x.re ∧ x.re ≤ ((b.1 : ℝ) + 1) / 8 ∧
      (b.2 : ℝ) / 8 ≤ x.im ∧ x.im ≤ ((b.2 : ℝ) + 1) / 8 := by
    simpa [T20.dyBlock, hs, Complex.mem_reProdIm, mem_Icc, div_eq_mul_inv, and_assoc]
      using hx
  have hy' := T20D.mem_hatBox hy
  rw [hs] at hy'
  have hre : -1 / 4 ≤ (y - x).re ∧ (y - x).re ≤ (1 / 4 : ℝ) := by
    simp only [Complex.sub_re]
    constructor <;> nlinarith [hx'.1, hx'.2.1, hy'.1, hy'.2.1]
  have him : -1 / 4 ≤ (y - x).im ∧ (y - x).im ≤ (1 / 4 : ℝ) := by
    simp only [Complex.sub_im]
    constructor <;> nlinarith [hx'.2.2.1, hx'.2.2.2, hy'.2.2.1, hy'.2.2.2]
  have hreSq : (y - x).re ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ (1 / 4 : ℝ) - (y - x).re)
      (by linarith : 0 ≤ (1 / 4 : ℝ) + (y - x).re)]
  have himSq : (y - x).im ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ (1 / 4 : ℝ) - (y - x).im)
      (by linarith : 0 ≤ (1 / 4 : ℝ) + (y - x).im)]
  have hnorm : ‖y - x‖ ^ 2 = (y - x).re ^ 2 + (y - x).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hlt : ‖y - x‖ < (1 / 2 : ℝ) := by
    nlinarith [norm_nonneg (y - x)]
  calc
    dist x y = ‖x - y‖ := dist_eq_norm x y
    _ = ‖y - x‖ := norm_sub_rev x y
    _ < 1 / 2 := hlt

attribute [irreducible] laneCShortBlocks laneCShortRects

end SupercriticalLQGUniqueness.B2.DG20Conc
