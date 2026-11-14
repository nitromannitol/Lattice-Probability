/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J3LowerGeom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.Separator
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path

 











set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 
theorem j3_mem_dyBlock_floor (K : ℕ) (x : ℂ) :
    x ∈ T20.dyBlock K (⌊x.re * 2 ^ K⌋, ⌊x.im * 2 ^ K⌋) := by
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  have hq : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [← mul_pow]; norm_num
  have key : ∀ r : ℝ, (⌊r * 2 ^ K⌋ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ r ∧
      r ≤ ((⌊r * 2 ^ K⌋ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by
    intro r
    have h1 := Int.floor_le (r * 2 ^ K)
    have h2 := Int.lt_floor_add_one (r * 2 ^ K)
    have hi : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
    constructor
    · calc (⌊r * 2 ^ K⌋ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ r * 2 ^ K * (2 : ℝ)⁻¹ ^ K :=
            mul_le_mul_of_nonneg_right h1 hi.le
        _ = r := by rw [mul_assoc, hq, mul_one]
    · calc r = r * 2 ^ K * (2 : ℝ)⁻¹ ^ K := by rw [mul_assoc, hq, mul_one]
        _ ≤ ((⌊r * 2 ^ K⌋ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K :=
            mul_le_mul_of_nonneg_right h2.le hi.le
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc]
  exact ⟨key x.re, key x.im⟩

 



theorem j3_lower_geometry {K₁ K₂ : Set ℂ} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne : K₁.Nonempty) (hdisj : Disjoint K₁ K₂) :
    ∃ (K : ℕ) (F : Finset (Circle × ℂ)), ∀ (ξ : ℝ) (f : ℂ → ℝ) (U : Set ℂ) (a : ℝ),
      crossLenIn ξ f U K₁ K₂ < ENNReal.ofReal a →
        ∃ j ∈ F, T20B.mrectLen ξ f K j.1 j.2 1 3 < a := by
  classical
  obtain ⟨d, hd, hgap⟩ := exists_positive_infDist_gap hK₁ hK₂ hne hdisj
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (12 / d) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  have hsmall : 12 * (2 : ℝ)⁻¹ ^ K ≤ d := by
    have h12 : 12 < d * 2 ^ K := by
      have := (div_lt_iff₀ hd).mp hK
      linarith
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hp]
    linarith
  obtain ⟨R₀, hR₀⟩ := hK₁.isBounded.subset_closedBall 0
  set N : ℤ := ⌈(R₀ + d) * 2 ^ K⌉ + 1 with hN
  set box : Finset (ℤ × ℤ) := Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N with hbox
  refine ⟨K, box.biUnion (T20D.shortJ K), fun ξ f U a hlt => ?_⟩
  
  have hinf : (⨅ b ∈ box, ⨅ j ∈ T20D.shortJ K b,
      crossLenIn ξ f (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j)) ≤ crossLenIn ξ f U K₁ K₂ := by
    apply le_crossLenIn
    intro G hG
    obtain ⟨z, hz, w, hw, hpath, -⟩ := hG
    have hGc := hpath.continuousOn
    have hG0 : G 0 = z := hpath.source
    have hG1 : G 1 = w := hpath.target
    
    have hcont : ContinuousOn (fun t => infDist (G t) K₁) (Icc 0 1) :=
      (continuous_infDist_pt K₁).comp_continuousOn hGc
    have h0 : infDist (G 0) K₁ = 0 := by rw [hG0]; exact infDist_zero_of_mem hz
    have h1 : d ≤ infDist (G 1) K₁ := by rw [hG1]; exact hgap w hw
    have hmem : d / 2 ∈ Icc (infDist (G 0) K₁) (infDist (G 1) K₁) :=
      ⟨by rw [h0]; linarith, by linarith⟩
    obtain ⟨t, ht, htd⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont hmem
    have htd' : infDist (G t) K₁ = d / 2 := htd
    set x := G t with hx
    set b : ℤ × ℤ := (⌊x.re * 2 ^ K⌋, ⌊x.im * 2 ^ K⌋) with hb
    have hin : G t ∈ T20.dyBlock K b := j3_mem_dyBlock_floor K x
    
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ K₁, dist x y < d := by
      have : infDist x K₁ < d := by rw [htd']; linarith
      exact (infDist_lt_iff hne).mp this
    have hxR : ‖x‖ ≤ R₀ + d := by
      have hyR : ‖y‖ ≤ R₀ := by simpa using hR₀ hy
      have := norm_sub_norm_le x y
      rw [← dist_eq_norm] at this
      linarith
    have hbB : b ∈ box := by
      have hre : |x.re| ≤ R₀ + d := (Complex.abs_re_le_norm x).trans hxR
      have him : |x.im| ≤ R₀ + d := (Complex.abs_im_le_norm x).trans hxR
      have hc : (R₀ + d) * 2 ^ K ≤ ⌈(R₀ + d) * 2 ^ K⌉ := Int.le_ceil _
      have bnd : ∀ r : ℝ, |r| ≤ R₀ + d → -N ≤ ⌊r * 2 ^ K⌋ ∧ ⌊r * 2 ^ K⌋ ≤ N := by
        intro r hr
        have hr' := abs_le.mp hr
        constructor
        · have : -((R₀ + d) * 2 ^ K) ≤ r * 2 ^ K := by nlinarith
          have h2 : (-(N : ℝ)) ≤ (⌊r * 2 ^ K⌋ : ℝ) := by
            have := Int.lt_floor_add_one (r * 2 ^ K)
            push_cast [hN]; linarith
          exact_mod_cast h2
        · have : r * 2 ^ K ≤ (R₀ + d) * 2 ^ K := by nlinarith
          have h2 : (⌊r * 2 ^ K⌋ : ℝ) ≤ N := by
            have := Int.floor_le (r * 2 ^ K)
            push_cast [hN]; linarith
          exact_mod_cast h2
      simp only [hbox, Finset.mem_product, Finset.mem_Icc]
      exact ⟨bnd x.re hre, bnd x.im him⟩
    
    have hout : G 1 ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
        Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
      intro hG1box
      rw [Complex.mem_reProdIm] at hG1box
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hG1box
      obtain ⟨xr1, xr2, xi1, xi2⟩ := S6.mem_dyBlock hin
      have hdre : |(G 1).re - x.re| < 2 * (2 : ℝ)⁻¹ ^ K := by
        rw [abs_lt]; constructor <;> nlinarith
      have hdim : |(G 1).im - x.im| < 2 * (2 : ℝ)⁻¹ ^ K := by
        rw [abs_lt]; constructor <;> nlinarith
      have hdist : dist (G 1) x < 4 * (2 : ℝ)⁻¹ ^ K := by
        rw [dist_eq_norm]
        calc ‖G 1 - x‖ ≤ |(G 1 - x).re| + |(G 1 - x).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |(G 1).re - x.re| + |(G 1).im - x.im| := by simp
          _ < 4 * (2 : ℝ)⁻¹ ^ K := by linarith
      have htri := infDist_le_infDist_add_dist (x := G 1) (y := x) (s := K₁)
      have : infDist x K₁ = d / 2 := htd'
      linarith
    obtain ⟨u, v, htu, huv, hv1, -, j, hj, hadm⟩ := T20D.piece_of_cross hpath ht hin hout
    have hcross := crossLenIn_le_lfppLen (ξ := ξ) (f := f) hadm
    have hsub : lfppLen ξ f (subPath G u v) ≤ lfppLen ξ f G := by
      rw [lfppLen_subPath G huv, lfppLen_eq]
      exact lintegral_mono_set (Icc_subset_Icc (ht.1.trans htu) hv1)
    exact (iInf₂_le b hbB).trans ((iInf₂_le j hj).trans (hcross.trans hsub))
  have h := hinf.trans_lt hlt
  obtain ⟨b, hb'⟩ := iInf_lt_iff.mp h
  obtain ⟨hb, hj'⟩ := iInf_lt_iff.mp hb'
  obtain ⟨j, hj''⟩ := iInf_lt_iff.mp hj'
  obtain ⟨hj, hlt'⟩ := iInf_lt_iff.mp hj''
  exact ⟨j, Finset.mem_biUnion.2 ⟨b, hb, hj⟩, ENNReal.toReal_lt_of_lt_ofReal hlt'⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
