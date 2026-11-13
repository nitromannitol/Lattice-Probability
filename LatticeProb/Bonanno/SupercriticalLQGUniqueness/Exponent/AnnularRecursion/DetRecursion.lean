/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.DetRecursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.FineUnion




 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 
theorem corner_mem_tile {a : ℝ} (ha : 0 ≤ a) (ij : ℤ × ℤ) : corner a ij ∈ tile a ij := by
  refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩⟩ <;> simp only [corner] <;> nlinarith

 
theorem norm_sub_corner_le {a : ℝ} (ha : 0 ≤ a) (ij : ℤ × ℤ) {z : ℂ}
    (hz : z ∈ block a ij) : ‖z - corner a ij‖ ≤ 4 * a := by
  rw [mem_block_iff] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |(z - corner a ij).re| ≤ 2 * a := by
    rw [Complex.sub_re, abs_le]; simp only [corner]; constructor <;> nlinarith
  have him : |(z - corner a ij).im| ≤ 2 * a := by
    rw [Complex.sub_im, abs_le]; simp only [corner]; constructor <;> nlinarith
  linarith

theorem thirtyTwo_sqrt_two_le : 32 * Real.sqrt 2 ≤ 46 := by
  have h : Real.sqrt 2 ≤ 1.4143 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

 
theorem det_recursion (m : ℕ) (hm : 8 ≤ m) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (F : Exponent.PolygonalCost.RatPolygonFamily) (hF : F.Admitted) {φ : ℂ → ℝ} (ψ : ℂ → ℝ)
    (hφ : ContDiff ℝ 1 φ) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ z ∈ Exponent.InwardMap.gradientBox, ‖fderiv ℝ φ z‖ ≤ G) (w : ℤ × ℤ → ℝ≥0∞)
    (hw : ∀ ij, ∀ z ∈ block (((2 : ℝ) ^ m)⁻¹) ij, ENNReal.ofReal (Real.exp (ξ * φ z)) ≤ w ij)
    (hwup : ∀ ij ∈ longTiles m (imageFamily (aQ m) F),
      w ij ≤ ENNReal.ofReal (Real.exp (ξ * (φ (corner (((2 : ℝ) ^ m)⁻¹) ij) +
        4 * ((2 : ℝ) ^ m)⁻¹ * G)))) :
    Exponent.PolygonalCost.polyAnnularCost ξ (fun z => φ z + ψ z) ≤
        ∑ ij ∈ longTiles m (imageFamily (aQ m) F), w ij *
          ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
            Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z)) ∧
      ∑ ij ∈ longTiles m (imageFamily (aQ m) F), ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * w ij ≤
        20 * ENNReal.ofReal (Real.exp (54 * ξ * (((2 : ℝ) ^ m)⁻¹ * G))) * F.cost ξ φ := by
  set a : ℝ := ((2 : ℝ) ^ m)⁻¹ with ha_def
  have ha : 0 < a := by positivity
  set F' := imageFamily (aQ m) F
  set L := longTiles m F'
  obtain ⟨hadm, hcl⟩ := imageFamily_admitted (aQ m) (aQ_pos m) (aQ_le m hm) F hF
  rw [aQ_cast] at hcl
  have hLsep := longTiles_disconnects m F' hm hcl hadm.2
  have hLA := fun ij (hij : ij ∈ L) => longTiles_block_subset m F' hm hcl hij
  refine ⟨fine_union_le m L hLsep (fun ij hij => (hLA ij hij).1) ξ φ ψ w
    (fun ij _ => hw ij) fun ij hij => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hwup ij hij), ?_⟩
  
  have hdiff : ∀ z ∈ Exponent.InwardMap.gradientBox, DifferentiableAt ℝ φ z :=
    fun z _ => (hφ.differentiable (by norm_num)).differentiableAt
  have hmv : ∀ ij ∈ L, ∀ z ∈ block a ij, φ (corner a ij) - 4 * a * G ≤ φ z := by
    intro ij hij z hz
    have hcB : corner a ij ∈ block a ij := tile_subset_block ha.le ij (corner_mem_tile ha.le ij)
    have hmv := Exponent.InwardMap.convex_gradientBox.norm_image_sub_le_of_norm_fderiv_le hdiff hG
      ((hLA ij hij).2 hcB) ((hLA ij hij).2 hz)
    have hd := norm_sub_corner_le ha.le ij hz
    have h1 : |φ z - φ (corner a ij)| ≤ G * (4 * a) := by
      rw [← Real.norm_eq_abs]
      exact hmv.trans (mul_le_mul_of_nonneg_left hd hG0)
    linarith [neg_abs_le (φ z - φ (corner a ij))]
  have hcount := longTiles_count m F' hξ hφ.continuous (fun ij => φ (corner a ij) - 4 * a * G) hmv
  have hFcl : F.trace ⊆ Exponent.PolygonalCost.closedSquareAnnulus := hF.1.trans openSquareAnnulus_subset_closed
  have himg := imageFamily_cost_le (aQ m) (aQ_pos m).le (aQ_le m hm) ξ G hξ hG0 φ hdiff hG F hFcl
  rw [aQ_cast] at himg
  have hstep : ∀ ij ∈ L, ENNReal.ofReal a * w ij ≤
      ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) *
        (ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * (φ (corner a ij) - 4 * a * G)))) := by
    intro ij hij
    calc ENNReal.ofReal a * w ij ≤ ENNReal.ofReal a *
        ENNReal.ofReal (Real.exp (ξ * (φ (corner a ij) + 4 * a * G))) := by
          gcongr; exact hwup ij hij
      _ = ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) *
          (ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * (φ (corner a ij) - 4 * a * G)))) := by
          rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul ha.le,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [show ξ * (φ (corner a ij) + 4 * a * G) =
            8 * ξ * (a * G) + ξ * (φ (corner a ij) - 4 * a * G) by ring, Real.exp_add]
          ring
  have hfac : (16 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) *
      ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * (a * G))) ≤
      20 * ENNReal.ofReal (Real.exp (54 * ξ * (a * G))) := by
    have hx : 0 ≤ ξ * (a * G) := mul_nonneg hξ (mul_nonneg ha.le hG0)
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
      show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (8 * ξ * (a * G)) * Real.exp (32 * Real.sqrt 2 * ξ * (a * G)) ≤
        Real.exp (54 * ξ * (a * G)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := thirtyTwo_sqrt_two_le
      nlinarith
    nlinarith [Real.exp_pos (8 * ξ * (a * G)), Real.exp_pos (32 * Real.sqrt 2 * ξ * (a * G))]
  calc ∑ ij ∈ L, ENNReal.ofReal a * w ij ≤
      ∑ ij ∈ L, ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) *
        (ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * (φ (corner a ij) - 4 * a * G)))) :=
        Finset.sum_le_sum hstep
    _ = ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) * ∑ ij ∈ L,
        ENNReal.ofReal a * ENNReal.ofReal (Real.exp (ξ * (φ (corner a ij) - 4 * a * G))) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) * (16 * F'.cost ξ φ) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) * (16 *
        (ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * (a * G))) *
          F.cost ξ φ)) := by gcongr
    _ = 16 * ENNReal.ofReal (Real.exp (8 * ξ * (a * G))) *
        ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * (a * G))) *
          F.cost ξ φ := by ring
    _ ≤ 20 * ENNReal.ofReal (Real.exp (54 * ξ * (a * G))) * F.cost ξ φ := by gcongr



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
