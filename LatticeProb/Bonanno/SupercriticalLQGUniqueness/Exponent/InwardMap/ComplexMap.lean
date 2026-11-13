/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.ComplexMap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.LatticeMap
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.FourBand




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def inwardAxis (a t : ℝ) : ℝ := 1/2 + inwardCoord a (t-1/2)

theorem inwardMap_re (a : ℝ) (z : ℂ) : (inwardMap a z).re = inwardAxis a z.re := rfl
theorem inwardMap_im (a : ℝ) (z : ℂ) : (inwardMap a z).im = inwardAxis a z.im := rfl

theorem inwardAxis_neg_one (a : ℝ) : inwardAxis a (-1) = -1+32*a := by
  norm_num [inwardAxis, inwardCoord]
  ring

theorem inwardAxis_zero (a : ℝ) : inwardAxis a 0 = -32*a := by
  norm_num [inwardAxis, inwardCoord]
  ring

theorem inwardAxis_one (a : ℝ) : inwardAxis a 1 = 1+32*a := by
  norm_num [inwardAxis, inwardCoord]
  ring

theorem inwardAxis_two (a : ℝ) : inwardAxis a 2 = 2-32*a := by
  norm_num [inwardAxis, inwardCoord]
  ring

theorem inwardAxis_displacement (a t : ℝ) (ha0 : 0 ≤ a) :
    -32*a ≤ inwardAxis a t - t ∧ inwardAxis a t - t ≤ 32*a := by
  have h := inwardCoord_displacement a (t-1/2) ha0
  unfold inwardAxis
  constructor <;> linarith [h.1, h.2]

theorem inwardAxis_strictMono (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    StrictMono (inwardAxis a) := by
  intro x y hxy
  unfold inwardAxis
  have h := (inwardCoord_strictMono a ha0 ha) (sub_lt_sub_right hxy (1/2))
  linarith

theorem inwardMap_displacement (a : ℝ) (ha0 : 0 ≤ a) (z : ℂ) :
    ‖inwardMap a z - z‖ ≤ 32 * Real.sqrt 2 * a := by
  have hr := inwardAxis_displacement a z.re ha0
  have hi := inwardAxis_displacement a z.im ha0
  have hR : |(inwardMap a z - z).re| ≤ 32*a := by
    rw [Complex.sub_re, inwardMap_re]
    exact abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  have hI : |(inwardMap a z - z).im| ≤ 32*a := by
    rw [Complex.sub_im, inwardMap_im]
    exact abs_le.mpr ⟨by linarith [hi.1], hi.2⟩
  calc
    ‖inwardMap a z - z‖ ≤ Real.sqrt 2 *
        max |(inwardMap a z - z).re| |(inwardMap a z - z).im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (32*a) :=
      mul_le_mul_of_nonneg_left (max_le hR hI) (Real.sqrt_nonneg _)
    _ = 32 * Real.sqrt 2 * a := by ring

theorem inwardMap_lipschitz (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    LipschitzWith (5/4 : NNReal) (inwardMap a) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  let Fz := inwardMap a z
  let Fw := inwardMap a w
  have hcoord := inwardCoord_lipschitz a ha0 ha
  have hr : |Fz.re - Fw.re| ≤ (5/4 : ℝ) * |z.re - w.re| := by
    have h := hcoord.dist_le_mul (z.re-1/2) (w.re-1/2)
    dsimp [Fz, Fw, inwardMap, inwardAxis]
    simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat,
      add_sub_add_left_eq_sub, sub_sub_sub_cancel_right] using h
  have hi : |Fz.im - Fw.im| ≤ (5/4 : ℝ) * |z.im - w.im| := by
    have h := hcoord.dist_le_mul (z.im-1/2) (w.im-1/2)
    dsimp [Fz, Fw, inwardMap, inwardAxis]
    simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat,
      add_sub_add_left_eq_sub, sub_sub_sub_cancel_right] using h
  have hr2 : (Fz.re-Fw.re)^2 ≤ ((5/4:ℝ)^2) * (z.re-w.re)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).2 hr
    simpa only [sq_abs, mul_pow] using h
  have hi2 : (Fz.im-Fw.im)^2 ≤ ((5/4:ℝ)^2) * (z.im-w.im)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).2 hi
    simpa only [sq_abs, mul_pow] using h
  have hsum : (Fz.re-Fw.re)^2+(Fz.im-Fw.im)^2 ≤
      ((5/4:ℝ)^2) * ((z.re-w.re)^2+(z.im-w.im)^2) := by
    nlinarith [hr2, hi2]
  change dist Fz Fw ≤ (5/4:ℝ) * dist z w
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  calc
    Real.sqrt ((Fz.re-Fw.re)^2+(Fz.im-Fw.im)^2) ≤
        Real.sqrt (((5/4:ℝ)^2) * ((z.re-w.re)^2+(z.im-w.im)^2)) :=
      Real.sqrt_le_sqrt hsum
    _ = (5/4:ℝ) * Real.sqrt ((z.re-w.re)^2+(z.im-w.im)^2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      norm_num

theorem inwardAxis_surjective (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    Function.Surjective (inwardAxis a) := by
  intro y
  obtain ⟨x, hx⟩ := inwardCoord_surjective a ha0 ha (y-1/2)
  refine ⟨x+1/2, ?_⟩
  dsimp [inwardAxis]
  convert congrArg (fun t : ℝ => 1/2+t) hx using 1 <;> ring

theorem inwardAxis_isHomeomorph (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    IsHomeomorph (inwardAxis a) := by
  have hs := inwardAxis_surjective a ha0 ha
  apply isHomeomorph_iff_isEmbedding_surjective.mpr
  refine ⟨(inwardAxis_strictMono a ha0 ha).isEmbedding_of_ordConnected ?_, hs⟩
  rw [hs.range_eq]
  exact Set.ordConnected_univ

theorem inwardMap_isHomeomorph (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    IsHomeomorph (inwardMap a) := by
  let e := Complex.equivRealProdCLM.toHomeomorph
  have he : IsHomeomorph e := e.isHomeomorph
  have heinv : IsHomeomorph e.symm := e.symm.isHomeomorph
  have hprod := (inwardAxis_isHomeomorph a ha0 ha).prodMap
    (inwardAxis_isHomeomorph a ha0 ha)
  have h := heinv.comp (hprod.comp he)
  convert h using 1
  funext z
  apply Complex.ext
  · simp [e, inwardMap, inwardAxis, Complex.equivRealProdCLM_symm_apply]
  · simp [e, inwardMap, inwardAxis, Complex.equivRealProdCLM_symm_apply]

 
def clearedSquareAnnulus (a : ℝ) : Set ℂ :=
  (Icc (-1+32*a) (2-32*a) ×ℂ Icc (-1+32*a) (2-32*a)) \
    (Ioo (-32*a) (1+32*a) ×ℂ Ioo (-32*a) (1+32*a))

theorem inwardMap_closed_to_cleared (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256)
    {z : ℂ} (hz : z ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    inwardMap a z ∈ clearedSquareAnnulus a := by
  simp only [Exponent.PolygonalCost.closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm,
    mem_Icc, mem_Ioo] at hz
  simp only [clearedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm,
    mem_Icc, mem_Ioo, inwardMap_re, inwardMap_im]
  have hm := (inwardAxis_strictMono a ha0 ha).monotone
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · simpa only [inwardAxis_neg_one] using hm hz.1.1.1
  · simpa only [inwardAxis_two] using hm hz.1.1.2
  · simpa only [inwardAxis_neg_one] using hm hz.1.2.1
  · simpa only [inwardAxis_two] using hm hz.1.2.2
  · intro hinner
    apply hz.2
    have hmono := inwardAxis_strictMono a ha0 ha
    have hcoord {t : ℝ} (ht : -32*a < inwardAxis a t ∧ inwardAxis a t < 1+32*a) :
        0 < t ∧ t < 1 := by
      constructor
      · by_contra h
        have hle : t ≤ 0 := le_of_not_gt h
        have hb := hmono.monotone hle
        rw [inwardAxis_zero] at hb
        linarith
      · by_contra h
        have hle : 1 ≤ t := le_of_not_gt h
        have hb := hmono.monotone hle
        rw [inwardAxis_one] at hb
        linarith
    exact ⟨hcoord hinner.1, hcoord hinner.2⟩

theorem clearedSquareAnnulus_subset_open (a : ℝ) (ha0 : 0 < a)
    (z : ℂ) (hz : z ∈ clearedSquareAnnulus a) :
    z ∈ Exponent.PolygonalCost.openSquareAnnulus := by
  simp only [clearedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm,
    mem_Icc, mem_Ioo] at hz
  simp only [Exponent.PolygonalCost.openSquareAnnulus, Exponent.PaidDuality.outerOpenSquare, Exponent.PaidDuality.innerSquare,
    mem_sdiff, Complex.mem_reProdIm, mem_Ioo, mem_Icc]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [hz.1.1.1]
  · linarith [hz.1.1.2]
  · linarith [hz.1.2.1]
  · linarith [hz.1.2.2]
  · intro hinner
    apply hz.2
    exact ⟨⟨by linarith [hinner.1.1], by linarith [hinner.1.2]⟩,
      ⟨by linarith [hinner.2.1], by linarith [hinner.2.2]⟩⟩

theorem inwardMap_closed_to_open (a : ℝ) (ha0 : 0 < a) (ha : a ≤ 1/256)
    {z : ℂ} (hz : z ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    inwardMap a z ∈ Exponent.PolygonalCost.openSquareAnnulus :=
  clearedSquareAnnulus_subset_open a ha0 _
    (inwardMap_closed_to_cleared a ha0.le ha hz)


end SupercriticalLQGUniqueness.Exponent.InwardMap
