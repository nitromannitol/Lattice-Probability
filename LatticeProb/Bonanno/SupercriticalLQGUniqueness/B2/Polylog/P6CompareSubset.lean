/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P6CompareSubset at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P3PaidGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P5CompareIterate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLACompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P8RatioUniform

 



























set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric (circleAvg)
open Uniqueness.BiLipschitz.PaidSeparators (sepAnn)

 

 

lemma twenty_mul_le_of_mem_plRadiusSet {ζ : ℝ} {ε r : Set.Ioi (0 : ℝ)}
    (hr : r ∈ plRadiusSet ζ ε) : 20 * (r : ℝ) ≤ (ε : ℝ) ^ (1 - ζ) := by
  unfold plRadiusSet at hr
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
  show 20 * ((10 : ℝ) ^ (-((i : ℝ) + 2)) * (ε : ℝ) ^ (1 - ζ)) ≤ (ε : ℝ) ^ (1 - ζ)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h1 : (10 : ℝ) ^ (-((i : ℝ) + 2)) ≤ (10 : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (10 : ℝ) ^ (-(2 : ℝ)) = 1 / 100 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  have h3 : 0 < (ε : ℝ) ^ (1 - ζ) := Real.rpow_pos_of_pos ε.2 _
  rw [h2] at h1
  nlinarith

 
lemma exists_plLatticePt_near {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∃ j k : ℤ, dist y (plLatticePt ε j k) ≤ ε / 100 := by
  have hδ : 0 < ε / 100 := by positivity
  have hδne : ε / 100 ≠ 0 := hδ.ne'
  have hround : ∀ t : ℝ, |t - ε / 100 * (round (t / (ε / 100)) : ℝ)| ≤ ε / 100 / 2 := by
    intro t
    have h := abs_sub_round (t / (ε / 100))
    have heq : t - ε / 100 * (round (t / (ε / 100)) : ℝ) =
        ε / 100 * (t / (ε / 100) - round (t / (ε / 100))) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hδ]
    nlinarith
  refine ⟨round (y.re / (ε / 100)), round (y.im / (ε / 100)), ?_⟩
  rw [dist_eq_norm]
  calc ‖y - plLatticePt ε (round (y.re / (ε / 100))) (round (y.im / (ε / 100)))‖
      ≤ |(y - plLatticePt ε (round (y.re / (ε / 100))) (round (y.im / (ε / 100)))).re| +
          |(y - plLatticePt ε (round (y.re / (ε / 100))) (round (y.im / (ε / 100)))).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ε / 100 / 2 + ε / 100 / 2 := add_le_add (hround y.re) (hround y.im)
    _ = ε / 100 := by ring

 
lemma finite_plLattice_of_isBounded {ε : ℝ} (hε : 0 < ε) {V : Set ℂ}
    (hV : Bornology.IsBounded V) : {p : ℤ × ℤ | plLatticePt ε p.1 p.2 ∈ V}.Finite := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall 0
  refine ((Set.finite_Icc (-⌈100 * R / ε⌉) ⌈100 * R / ε⌉).prod
    (Set.finite_Icc (-⌈100 * R / ε⌉) ⌈100 * R / ε⌉)).subset ?_
  have hbound : ∀ n : ℤ, |ε / 100 * (n : ℝ)| ≤ R →
      n ∈ Icc (-⌈100 * R / ε⌉) ⌈100 * R / ε⌉ := by
    intro n hn
    rw [abs_mul, abs_of_pos (by positivity : 0 < ε / 100)] at hn
    have h1 : |(n : ℝ)| ≤ 100 * R / ε := by
      rw [le_div_iff₀ hε]
      nlinarith
    have h3 := abs_le.1 (h1.trans (Int.le_ceil _))
    exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩
  rintro ⟨j, k⟩ hp
  have hn : ‖plLatticePt ε j k‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hR hp
  have hj : |ε / 100 * (j : ℝ)| ≤ R := (Complex.abs_re_le_norm (plLatticePt ε j k)).trans hn
  have hk : |ε / 100 * (k : ℝ)| ≤ R := (Complex.abs_im_le_norm (plLatticePt ε j k)).trans hn
  exact ⟨hbound j hj, hbound k hk⟩

 

lemma ratio_bound_aux {b c e C M : ℝ} (hc : 0 < c) (he : 0 < e) (hC : 0 < C)
    (hb : b ≤ M * c) : (b⁻¹ * e)⁻¹ * C ≤ C ^ 2 * M * ((c⁻¹ * e)⁻¹ * C⁻¹) := by
  have _hc := hc
  rw [mul_inv, mul_inv, inv_inv, inv_inv,
    show C ^ 2 * M * (c * e⁻¹ * C⁻¹) = M * c * (e⁻¹ * C) * (C * C⁻¹) by ring,
    mul_inv_cancel₀ hC.ne', mul_one, show b * e⁻¹ * C = b * (e⁻¹ * C) by ring]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

 

 



theorem compareSubsetHolds_of_compareIterateHolds (ξ : ℝ) (D : DistC → LSCMetric)
    (c m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {U : Set ℂ} (hU : Bornology.IsBounded U) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (Rt : Finset (Set.Ioi (0 : ℝ))) (hne : Rt.Nonempty) (hsub : Rt ⊆ plRadiusSet ζ ⟨ε, hε.1⟩)
    {C : ℝ} (hC : 1 ≤ C) (g : DistC) (hg : compareIterateHolds ξ D c m q U ε hε Rt C g) :
    compareSubsetHolds ξ D c m q ζ U ε hε Rt hne (2 * C ^ 2) g := by
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCne : C ≠ 0 := hC0.ne'
  let ι := {p : ℤ × ℤ // plLatticePt ε p.1 p.2 ∈ thickening 1 U}
  have : Finite ι := (finite_plLattice_of_isBounded hε.1 hU.thickening).to_subtype
  have hex : ∀ p : ι, ∃ r ∈ Rt, g ∈ plEventLoc ξ D c m q (plLatticePt ε p.1.1 p.1.2) ε hε r C :=
    fun p => hg p.1.1 p.1.2 p.2
  choose R hRmem hRev using hex
  let x : ι → ℂ := fun p => plLatticePt ε p.1.1 p.1.2
  let r : ι → ℝ := fun p => (R p : ℝ)
  have hr : ∀ p, 0 < r p := fun p => (R p).2
  have hρ : 0 < ε ^ (1 - ζ) := Real.rpow_pos_of_pos hε.1 _
  have hrρ : ∀ p, 20 * r p ≤ ε ^ (1 - ζ) :=
    fun p => twenty_mul_le_of_mem_plRadiusSet (hsub (hRmem p))
  have hcover : ∀ y ∈ U, ∃ p : ι, dist y (x p) < r p / 2 := by
    intro y hy
    obtain ⟨j, k, hjk⟩ := exists_plLatticePt_near hε.1 y
    have hmem : plLatticePt ε j k ∈ thickening 1 U :=
      mem_thickening_iff.2 ⟨y, hy, by rw [dist_comm]; linarith [hε.2]⟩
    refine ⟨⟨(j, k), hmem⟩, ?_⟩
    have hεr := (mem_plRadiusSet_bounds hζ0 hζ1 hε (hsub (hRmem ⟨(j, k), hmem⟩))).1
    show dist y (plLatticePt ε j k) < (R ⟨(j, k), hmem⟩ : ℝ) / 2
    linarith [hε.1]
  
  have hratio_pos : ∀ s, 0 < ratioBC m c ⟨ε, hε.1⟩ s :=
    fun s => div_pos (lfppScaleFactor_pos m _ s) (c s).2
  obtain ⟨s₀, hs₀⟩ := id hne
  have hMx_pos : 0 < Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩) :=
    (hratio_pos s₀).trans_le (Finset.le_sup' _ hs₀)
  have hmn_pos : 0 < Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩) := by
    obtain ⟨s, -, hseq⟩ := Finset.exists_mem_eq_inf' hne (ratioBC m c ⟨ε, hε.1⟩)
    rw [hseq]
    exact hratio_pos s
  
  let xc : ι → ℝ := fun p => ((c (R p) : ℝ))⁻¹ * Real.exp (-(ξ * circleAvg g (R p) (x p)))
  let xb : ι → ℝ := fun p =>
    (lfppScaleFactor m ⟨ε, hε.1⟩ (R p))⁻¹ * Real.exp (-(ξ * circleAvg g (R p) (x p)))
  have hcpos : ∀ p, (0 : ℝ) < (c (R p) : ℝ) := fun p => (c (R p)).2
  have hbpos : ∀ p, (0 : ℝ) < lfppScaleFactor m ⟨ε, hε.1⟩ (R p) :=
    fun p => lfppScaleFactor_pos m _ _
  have hxc : ∀ p, 0 < xc p := fun p => by have := hcpos p; positivity
  have hxb : ∀ p, 0 < xb p := fun p => by have := hbpos p; positivity
  
  have hev : ∀ p : ι,
      ENNReal.ofReal ((xc p)⁻¹ * C⁻¹) ≤ acrossIn (D g) (x p) (r p) (2 * r p) ∧
      aroundDist (D g) (sepAnn (x p) (r p) (hr p)) ≤ ENNReal.ofReal ((xc p)⁻¹ * C) ∧
      ENNReal.ofReal ((xb p)⁻¹ * C⁻¹) ≤
        acrossIn (plLocMetric ξ q m ε hε g) (x p) (r p) (2 * r p) ∧
      aroundDist (plLocMetric ξ q m ε hε g) (sepAnn (x p) (r p) (hr p)) ≤
        ENNReal.ofReal ((xb p)⁻¹ * C) := by
    intro p
    obtain ⟨h1, h2, h3, h4⟩ := hRev p
    exact ⟨ofReal_inv_mul_le_of_le_ofReal_mul (hxc p) h1,
      le_ofReal_inv_mul_of_ofReal_mul_le (hxc p) h2,
      ofReal_inv_mul_le_of_le_ofReal_mul (hxb p) h3,
      le_ofReal_inv_mul_of_ofReal_mul_le (hxb p) h4⟩
  have hexp : ∀ p, 0 < Real.exp (-(ξ * circleAvg g (R p) (x p))) := fun p => Real.exp_pos _
  intro z w hz hw
  constructor
  · 
    have hgood : ∀ p, GoodSiteIn (D g) (plLocMetric ξ q m ε hε g)
        (C ^ 2 * Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩)) (x p) (r p) ((xc p)⁻¹ * C⁻¹) (hr p) := by
      intro p
      have hb : lfppScaleFactor m ⟨ε, hε.1⟩ (R p) ≤
          Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩) * (c (R p) : ℝ) :=
        (div_le_iff₀ (hcpos p)).1 (Finset.le_sup' (ratioBC m c ⟨ε, hε.1⟩) (hRmem p))
      have hxc' := hxc p
      refine ⟨by positivity, (hev p).1, (hev p).2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact ratio_bound_aux (hcpos p) (hexp p) hC0 hb
    have h := internalSetDist_le_of_goodSites (D g) (plLocMetric ξ q m ε hε g)
      (by positivity) hρ hU x r _ hr hrρ hgood hcover z w hz hw
    rwa [show 2 * (C ^ 2 * Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩)) =
      2 * C ^ 2 * Rt.sup' hne (ratioBC m c ⟨ε, hε.1⟩) by ring] at h
  · 
    have hgood : ∀ p, GoodSiteIn (plLocMetric ξ q m ε hε g) (D g)
        (C ^ 2 * (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹) (x p) (r p) ((xb p)⁻¹ * C⁻¹)
        (hr p) := by
      intro p
      have h1 : Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩) * (c (R p) : ℝ) ≤
          lfppScaleFactor m ⟨ε, hε.1⟩ (R p) :=
        (le_div_iff₀ (hcpos p)).1 (Finset.inf'_le (ratioBC m c ⟨ε, hε.1⟩) (hRmem p))
      have hc : (c (R p) : ℝ) ≤
          (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹ * lfppScaleFactor m ⟨ε, hε.1⟩ (R p) := by
        calc (c (R p) : ℝ) = (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹ *
              (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩) * (c (R p) : ℝ)) := by
                field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hmn_pos.le)
      have hxb' := hxb p
      refine ⟨by positivity, (hev p).2.2.1, (hev p).2.1.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact ratio_bound_aux (hbpos p) (hexp p) hC0 hc
    have h := internalSetDist_le_of_goodSites (plLocMetric ξ q m ε hε g) (D g)
      (by positivity) hρ hU x r _ hr hrρ hgood hcover z w hz hw
    rwa [show 2 * (C ^ 2 * (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹) =
      2 * C ^ 2 * (Rt.inf' hne (ratioBC m c ⟨ε, hε.1⟩))⁻¹ by ring] at h

 

 


theorem plCompareSubset_of_compareIterate (hCI : PLCompareIterate) : PLCompareSubset := by
  intro ξ Q hQ D c hD m hm q hq ζ hζ0 hζ1
  obtain ⟨C₅, hC₅, hU⟩ := hCI ξ Q hQ D c hD m hm q hq ζ hζ0 hζ1
  refine ⟨2 * C₅ ^ 2, by positivity, fun U _ _ hUb => ?_⟩
  obtain ⟨c₀, ε₀, hc₀, hε₀, hε₀1, hP⟩ := hU U hUb
  refine ⟨1, c₀, ε₀, one_pos, hc₀, hε₀, hε₀1, ?_⟩
  intro Ω _ P _ h hh ε hε hεε₀ Rt hne hsub hcard
  calc P {ω | ¬ compareSubsetHolds (ξ : ℝ) D c m q ζ U ε hε Rt hne (2 * C₅ ^ 2) (h ω)}
      ≤ P {ω | ¬ compareIterateHolds (ξ : ℝ) D c m q U ε hε Rt C₅ (h ω)} :=
        measure_mono fun ω hω hci => hω
          (compareSubsetHolds_of_compareIterateHolds (ξ : ℝ) D c m q ζ hζ0 hζ1 hUb ε hε Rt hne
            hsub hC₅ (h ω) hci)
    _ ≤ ENNReal.ofReal (c₀ * ε) := hP P h hh ε hε hεε₀ Rt hsub hcard
    _ = ENNReal.ofReal (c₀ * ε ^ (1 : ℝ)) := by rw [Real.rpow_one]

 

theorem plCompareSubset_of_inputs (hPerc : Iface.DG20PercEstimate') (hS4 : Iface.DG20Section4) :
    PLCompareSubset :=
  plCompareSubset_of_compareIterate (plCompareIterate_of_inputs hPerc hS4)

end SupercriticalLQGUniqueness.B2.Polylog
