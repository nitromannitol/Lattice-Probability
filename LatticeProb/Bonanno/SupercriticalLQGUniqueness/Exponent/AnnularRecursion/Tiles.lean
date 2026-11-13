/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Tiles at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Reroute
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.PolygonFull
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar




 















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 
def tile (a : ℝ) (ij : ℤ × ℤ) : Set ℂ :=
  rectC ((ij.1 : ℝ) * a) (((ij.1 : ℝ) + 1) * a) ((ij.2 : ℝ) * a) (((ij.2 : ℝ) + 1) * a)

 
def block (a : ℝ) (ij : ℤ × ℤ) : Set ℂ :=
  rectC (((ij.1 : ℝ) - 1) * a) (((ij.1 : ℝ) + 2) * a) (((ij.2 : ℝ) - 1) * a)
    (((ij.2 : ℝ) + 2) * a)

 
def corner (a : ℝ) (ij : ℤ × ℤ) : ℂ := ⟨(ij.1 : ℝ) * a, (ij.2 : ℝ) * a⟩

 
def segLen (B : Set ℂ) (p q : ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, B.indicator (fun _ => ENNReal.ofReal ‖q - p‖) (segPath p q t)

 
def segCostIn (ξ : ℝ) (φ : ℂ → ℝ) (B : Set ℂ) (p q : ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1,
    B.indicator (fun z => ENNReal.ofReal (Real.exp (ξ * φ z) * ‖q - p‖)) (segPath p q t)

theorem isClosed_block (a : ℝ) (ij : ℤ × ℤ) : IsClosed (block a ij) := isClosed_rectC _ _ _ _

theorem continuous_segPath (p q : ℂ) : Continuous (segPath p q) := by
  unfold segPath; fun_prop

theorem segCost_eq_lintegral (ξ : ℝ) (φ : ℂ → ℝ) (p q : ℂ) :
    segCost ξ φ p q = ∫⁻ t in Icc (0 : ℝ) 1,
      ENNReal.ofReal (Real.exp (ξ * φ (segPath p q t)) * ‖q - p‖) := by
  unfold segCost lfppLen
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [(hasDerivAt_segPath p q t).deriv]

 

theorem mem_block_iff {a : ℝ} (ij : ℤ × ℤ) (z : ℂ) :
    z ∈ block a ij ↔ ((ij.1 : ℝ) - 1) * a ≤ z.re ∧ z.re ≤ ((ij.1 : ℝ) + 2) * a ∧
      ((ij.2 : ℝ) - 1) * a ≤ z.im ∧ z.im ≤ ((ij.2 : ℝ) + 2) * a := by
  simp only [block, rectC, Complex.mem_reProdIm, mem_Icc, and_assoc]

private theorem index_mem {a : ℝ} (ha : 0 < a) {i : ℤ} {x : ℝ}
    (h1 : ((i : ℝ) - 1) * a ≤ x) (h2 : x ≤ ((i : ℝ) + 2) * a) :
    i ∈ Finset.Icc (⌈x / a⌉ - 2) (⌈x / a⌉ + 1) := by
  rw [Finset.mem_Icc]
  constructor
  · have : x / a ≤ (i : ℝ) + 2 := by rw [div_le_iff₀ ha]; linarith
    have h := Int.ceil_le.2 (show x / a ≤ ((i + 2 : ℤ) : ℝ) by push_cast; exact this)
    omega
  · have : (i : ℝ) - 1 ≤ x / a := by rw [le_div_iff₀ ha]; linarith
    have h := (this.trans (Int.le_ceil (x / a)))
    have h' : (i : ℝ) ≤ ((⌈x / a⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'

open Classical in
theorem card_filter_block_le {a : ℝ} (ha : 0 < a) (s : Finset (ℤ × ℤ)) (z : ℂ) :
    (s.filter (fun ij => z ∈ block a ij)).card ≤ 16 := by
  classical
  set k := ⌈z.re / a⌉
  set l := ⌈z.im / a⌉
  have hsub : s.filter (fun ij => z ∈ block a ij) ⊆
      Finset.Icc (k - 2) (k + 1) ×ˢ Finset.Icc (l - 2) (l + 1) := by
    intro ij hij
    rw [Finset.mem_filter, mem_block_iff] at hij
    obtain ⟨-, h1, h2, h3, h4⟩ := hij
    exact Finset.mem_product.2 ⟨index_mem ha h1 h2, index_mem ha h3 h4⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have e1 : (k + 1 + 1 - (k - 2)).toNat = 4 := by omega
  have e2 : (l + 1 + 1 - (l - 2)).toNat = 4 := by omega
  rw [e1, e2]

theorem sum_indicator_block_le {a : ℝ} (ha : 0 < a) (s : Finset (ℤ × ℤ))
    (g : ℂ → ℝ≥0∞) (z : ℂ) :
    ∑ ij ∈ s, (block a ij).indicator g z ≤ 16 * g z := by
  classical
  have e : ∑ ij ∈ s, (block a ij).indicator g z =
      ∑ ij ∈ s.filter (fun ij => z ∈ block a ij), g z := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ij _ => ?_
    by_cases h : z ∈ block a ij
    · simp [h]
    · simp [h]
  rw [e, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  have h16 := card_filter_block_le ha s z
  exact_mod_cast h16

 
theorem sum_segCostIn_block_le {a : ℝ} (ha : 0 < a) (s : Finset (ℤ × ℤ)) (ξ : ℝ)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (p q : ℂ) :
    ∑ ij ∈ s, segCostIn ξ φ (block a ij) p q ≤ 16 * segCost ξ φ p q := by
  have hmeas : ∀ ij ∈ s, Measurable fun t => (block a ij).indicator
      (fun z => ENNReal.ofReal (Real.exp (ξ * φ z) * ‖q - p‖)) (segPath p q t) := by
    intro ij _
    have hg : Measurable fun z => ENNReal.ofReal (Real.exp (ξ * φ z) * ‖q - p‖) :=
      (((hφ.const_mul ξ).rexp).mul continuous_const).measurable.ennreal_ofReal
    exact (hg.indicator (isClosed_block a ij).measurableSet).comp
      (continuous_segPath p q).measurable
  unfold segCostIn
  rw [← lintegral_finsetSum s hmeas, segCost_eq_lintegral,
    ← lintegral_const_mul' _ _ (by norm_num)]
  exact lintegral_mono fun t => sum_indicator_block_le ha s _ _

 
theorem segLen_le_segCostIn {ξ : ℝ} (hξ : 0 ≤ ξ) {φ : ℂ → ℝ} {B : Set ℂ} {m : ℝ}
    (hm : ∀ z ∈ B, m ≤ φ z) (p q : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * m)) * segLen B p q ≤ segCostIn ξ φ B p q := by
  unfold segLen segCostIn
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  by_cases h : segPath p q t ∈ B
  · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hm _ h) hξ)
  · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]

 
def segParam (B : Set ℂ) (p q : ℂ) : Set ℝ := Icc (0 : ℝ) 1 ∩ segPath p q ⁻¹' B

theorem segLen_eq {B : Set ℂ} (hB : MeasurableSet B) (p q : ℂ) :
    segLen B p q = ENNReal.ofReal ‖q - p‖ * volume (segParam B p q) := by
  unfold segLen segParam
  have e : (fun t => B.indicator (fun _ => ENNReal.ofReal ‖q - p‖) (segPath p q t)) =
      (segPath p q ⁻¹' B).indicator (fun _ => ENNReal.ofReal ‖q - p‖) := by
    funext t
    by_cases h : segPath p q t ∈ B
    · rw [indicator_of_mem h, indicator_of_mem (show t ∈ segPath p q ⁻¹' B from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show t ∉ segPath p q ⁻¹' B from h)]
  rw [e, lintegral_indicator_const (hB.preimage (continuous_segPath p q).measurable),
    Measure.restrict_apply (hB.preimage (continuous_segPath p q).measurable), inter_comm]

theorem exists_mem_of_segLen_ne_zero {B : Set ℂ} {p q : ℂ} (h : segLen B p q ≠ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, segPath p q t ∈ B := by
  by_contra hno
  push Not at hno
  apply h
  unfold segLen
  rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Icc
    (fun t ht => indicator_of_notMem (hno t ht) _), lintegral_zero]

 

theorem volume_image_affine (c d : ℝ) (J : Set ℝ) :
    volume ((fun t => c + t * d) '' J) = ENNReal.ofReal |d| * volume J := by
  have e : (fun t => c + t * d) '' J = (fun x => c + x) '' (d • J) := by
    rw [← Set.image_smul, Set.image_image]
    simp only [smul_eq_mul, mul_comm]
  rw [e, Set.image_add_left, measure_preimage_add, Measure.addHaar_smul, Module.finrank_self,
    pow_one]

theorem segment_inter_eq_image {B : Set ℂ} (p q : ℂ) :
    [p -[ℝ] q] ∩ B = segPath p q '' segParam B p q := by
  rw [← Exponent.PaidDuality.segPath_trace]
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    exact ⟨t, ⟨ht, hz⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, hz⟩

theorem volume_re_image_le {B : Set ℂ} (hB : MeasurableSet B) (p q : ℂ) :
    volume (Complex.re '' ([p -[ℝ] q] ∩ B)) ≤ segLen B p q := by
  rw [segment_inter_eq_image, Set.image_image, segLen_eq hB]
  have e : (fun t => (segPath p q t).re) = fun t => p.re + t * (q.re - p.re) := by
    funext t; simp [segPath]
  rw [e, volume_image_affine]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  rw [← Complex.sub_re]
  exact Complex.abs_re_le_norm _

theorem volume_im_image_le {B : Set ℂ} (hB : MeasurableSet B) (p q : ℂ) :
    volume (Complex.im '' ([p -[ℝ] q] ∩ B)) ≤ segLen B p q := by
  rw [segment_inter_eq_image, Set.image_image, segLen_eq hB]
  have e : (fun t => (segPath p q t).im) = fun t => p.im + t * (q.im - p.im) := by
    funext t; simp [segPath]
  rw [e, volume_image_affine]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  rw [← Complex.sub_im]
  exact Complex.abs_im_le_norm _

private theorem exists_not_mem_of_volume_lt {S : Set ℝ} {u v : ℝ} (h : volume S < ENNReal.ofReal (v - u)) :
    ∃ c ∈ Ioo u v, c ∉ S := by
  by_contra hno
  push Not at hno
  have := measure_mono (μ := volume) hno
  rw [Real.volume_Ioo] at this
  exact (not_le.2 h) this

 
theorem short_block_loop {a : ℝ} (ha : 0 < a) (ij : ℤ × ℤ) {ι : Type*} (E : Finset ι)
    (p q : ι → ℂ) (hshort : ∑ e ∈ E, segLen (block a ij) (p e) (q e) < ENNReal.ofReal a) :
    ∃ c₁ c₂ d₁ d₂ : ℝ, c₁ ∈ Ioo (((ij.1 : ℝ) - 1) * a) ((ij.1 : ℝ) * a) ∧
      c₂ ∈ Ioo (((ij.1 : ℝ) + 1) * a) (((ij.1 : ℝ) + 2) * a) ∧
      d₁ ∈ Ioo (((ij.2 : ℝ) - 1) * a) ((ij.2 : ℝ) * a) ∧
      d₂ ∈ Ioo (((ij.2 : ℝ) + 1) * a) (((ij.2 : ℝ) + 2) * a) ∧
      Disjoint (rectSides c₁ c₂ d₁ d₂) (⋃ e ∈ E, [p e -[ℝ] q e]) := by
  set B := block a ij
  have hB : MeasurableSet B := (isClosed_block a ij).measurableSet
  set K := ⋃ e ∈ E, [p e -[ℝ] q e]
  have hKB : K ∩ B = ⋃ e ∈ E, ([p e -[ℝ] q e] ∩ B) := by
    simp only [K, iUnion_inter]
  have hre : volume (Complex.re '' (K ∩ B)) < ENNReal.ofReal a := by
    rw [hKB, image_iUnion₂]
    refine lt_of_le_of_lt (measure_biUnion_finset_le E _) (lt_of_le_of_lt ?_ hshort)
    exact Finset.sum_le_sum fun e _ => volume_re_image_le hB _ _
  have him : volume (Complex.im '' (K ∩ B)) < ENNReal.ofReal a := by
    rw [hKB, image_iUnion₂]
    refine lt_of_le_of_lt (measure_biUnion_finset_le E _) (lt_of_le_of_lt ?_ hshort)
    exact Finset.sum_le_sum fun e _ => volume_im_image_le hB _ _
  have hlen : ∀ u : ℝ, ENNReal.ofReal a = ENNReal.ofReal ((u + 1) * a - u * a) := by
    intro u; congr 1; ring
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_not_mem_of_volume_lt
    (u := ((ij.1 : ℝ) - 1) * a) (v := (ij.1 : ℝ) * a)
    (hre.trans_eq (by rw [hlen ((ij.1 : ℝ) - 1)]; ring_nf))
  obtain ⟨c₂, hc₂, hc₂'⟩ := exists_not_mem_of_volume_lt
    (u := ((ij.1 : ℝ) + 1) * a) (v := ((ij.1 : ℝ) + 2) * a)
    (hre.trans_eq (by rw [hlen ((ij.1 : ℝ) + 1)]; ring_nf))
  obtain ⟨d₁, hd₁, hd₁'⟩ := exists_not_mem_of_volume_lt
    (u := ((ij.2 : ℝ) - 1) * a) (v := (ij.2 : ℝ) * a)
    (him.trans_eq (by rw [hlen ((ij.2 : ℝ) - 1)]; ring_nf))
  obtain ⟨d₂, hd₂, hd₂'⟩ := exists_not_mem_of_volume_lt
    (u := ((ij.2 : ℝ) + 1) * a) (v := ((ij.2 : ℝ) + 2) * a)
    (him.trans_eq (by rw [hlen ((ij.2 : ℝ) + 1)]; ring_nf))
  refine ⟨c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, ?_⟩
  have hsubB : rectSides c₁ c₂ d₁ d₂ ⊆ B := by
    refine (rectSides_subset_rectC (by nlinarith [hc₁.2, hc₂.1])
      (by nlinarith [hd₁.2, hd₂.1])).trans ?_
    rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨by linarith [hc₁.1], by linarith [hc₂.2]⟩, ⟨by linarith [hd₁.1], by linarith [hd₂.2]⟩⟩
  rw [Set.disjoint_left]
  intro z hz hzK
  have hzKB : z ∈ K ∩ B := ⟨hzK, hsubB hz⟩
  rcases hz with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
  · exact hd₁' ⟨z, hzKB, h⟩
  · exact hc₁' ⟨z, hzKB, h⟩
  · exact hd₂' ⟨z, hzKB, h⟩
  · exact hc₂' ⟨z, hzKB, h⟩



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
