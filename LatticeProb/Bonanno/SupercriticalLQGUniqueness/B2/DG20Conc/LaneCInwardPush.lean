/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInwardPush at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

private def laneCPushWeight (d q : ℝ) : ℝ := 1 + d * (5 - q)

 


theorem laneC_push_radius {d r q : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1 / 1000)
    (hrlo : 3 / 2 ≤ r) (hrhi : r ≤ 5 / 2)
    (hqlo : r ^ 2 ≤ q) (hqhi : q ≤ 2 * r ^ 2) :
    3 / 2 < laneCPushWeight d q * r ∧
      laneCPushWeight d q * r < 5 / 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 : r ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hqmax : q ≤ 25 / 2 := by nlinarith
  have hq0 : 0 ≤ q := by nlinarith
  have hwpos : 0 < laneCPushWeight d q := by
    unfold laneCPushWeight
    by_cases h : q ≤ 5
    · nlinarith [mul_nonneg (le_of_lt hd) (sub_nonneg.2 h)]
    · have hprod : d * (q - 5) ≤ (1 / 1000 : ℝ) * (25 / 2 - 5) := by
        have h1 : d * (q - 5) ≤ (1 / 1000 : ℝ) * (q - 5) :=
          mul_le_mul_of_nonneg_right hdsmall (by linarith)
        have h2 : (1 / 1000 : ℝ) * (q - 5) ≤
            (1 / 1000 : ℝ) * (25 / 2 - 5) :=
          mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        exact h1.trans h2
      nlinarith
  constructor
  · by_cases hq5 : q ≤ 5
    · have hwge : 1 ≤ laneCPushWeight d q := by
        unfold laneCPushWeight
        nlinarith [mul_nonneg (le_of_lt hd) (sub_nonneg.2 hq5)]
      by_cases hrstrict : 3 / 2 < r
      · nlinarith [mul_nonneg (sub_nonneg.2 hwge) hr0]
      · have hre : r = 3 / 2 := by linarith
        subst r
        have hqstrict : q < 5 := by nlinarith [hqhi]
        have hprod : 0 < d * (5 - q) := mul_pos hd (by linarith)
        unfold laneCPushWeight
        nlinarith
    · have hrstrict : 31 / 20 < r := by
        by_contra h
        have hrbound : r ≤ 31 / 20 := by linarith
        have hr2bound : r ^ 2 ≤ (31 / 20 : ℝ) ^ 2 := by nlinarith
        nlinarith [hqhi]
      have hprod : d * (q - 5) ≤ (1 / 1000 : ℝ) * (25 / 2 - 5) := by
        have h1 : d * (q - 5) ≤ (1 / 1000 : ℝ) * (q - 5) :=
          mul_le_mul_of_nonneg_right hdsmall (by linarith)
        have h2 : (1 / 1000 : ℝ) * (q - 5) ≤
            (1 / 1000 : ℝ) * (25 / 2 - 5) :=
          mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        exact h1.trans h2
      have hwge : 397 / 400 ≤ laneCPushWeight d q := by
        unfold laneCPushWeight
        nlinarith
      have hscale : (397 / 400 : ℝ) * r ≤ laneCPushWeight d q * r :=
        mul_le_mul_of_nonneg_right hwge hr0
      nlinarith
  · by_cases hq5 : 5 ≤ q
    · have hwle : laneCPushWeight d q ≤ 1 := by
        unfold laneCPushWeight
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (by linarith : 5 - q ≤ 0)]
      by_cases hrstrict : r < 5 / 2
      · nlinarith [mul_nonneg (sub_nonneg.2 hwpos.le) hr0,
          mul_le_mul_of_nonneg_right hwle hr0]
      · have hre : r = 5 / 2 := by linarith
        subst r
        have hqstrict : 5 < q := by nlinarith [hqlo]
        have hprod : d * (5 - q) < 0 := mul_neg_of_pos_of_neg hd (by linarith)
        unfold laneCPushWeight
        nlinarith
    · have hrstrict : r < 23 / 10 := by
        by_contra h
        have hrbound : 23 / 10 ≤ r := by linarith
        have hr2bound : (23 / 10 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
        nlinarith [hqlo]
      have hwle : laneCPushWeight d q ≤ 201 / 200 := by
        unfold laneCPushWeight
        have h1 : d * (5 - q) ≤ (1 / 1000 : ℝ) * (5 - q) :=
          mul_le_mul_of_nonneg_right hdsmall (by linarith)
        have h2 : (1 / 1000 : ℝ) * (5 - q) ≤ (1 / 1000 : ℝ) * 5 :=
          mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        nlinarith [h1.trans h2]
      have hscale : laneCPushWeight d q * r ≤ (201 / 200 : ℝ) * r :=
        mul_le_mul_of_nonneg_right hwle hr0
      nlinarith

 
def laneCSquareX (z : ℂ) : ℝ := z.re - 1 / 2
def laneCSquareY (z : ℂ) : ℝ := z.im - 1 / 2
def laneCSquareRadius (z : ℂ) : ℝ := max |laneCSquareX z| |laneCSquareY z|
def laneCSquareNormSq (z : ℂ) : ℝ := laneCSquareX z ^ 2 + laneCSquareY z ^ 2
def laneCSquareCenter : ℂ := ⟨1 / 2, 1 / 2⟩

 
def laneCInwardPush (d : ℝ) (z : ℂ) : ℂ :=
  let w := laneCPushWeight d (laneCSquareNormSq z)
  ⟨1 / 2 + w * laneCSquareX z, 1 / 2 + w * laneCSquareY z⟩

theorem laneC_inwardPush_continuous (d : ℝ) : Continuous (laneCInwardPush d) := by
  unfold laneCInwardPush laneCPushWeight laneCSquareNormSq laneCSquareX laneCSquareY
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

theorem laneC_inwardPush_contDiff (d : ℝ) : ContDiff ℝ 1 (laneCInwardPush d) := by
  let a : ℂ → ℝ := fun z =>
    1 / 2 + laneCPushWeight d (laneCSquareNormSq z) * laneCSquareX z
  let b : ℂ → ℝ := fun z =>
    1 / 2 + laneCPushWeight d (laneCSquareNormSq z) * laneCSquareY z
  have hre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have ha : ContDiff ℝ 1 a := by
    dsimp [a, laneCPushWeight, laneCSquareNormSq, laneCSquareX, laneCSquareY]
    fun_prop
  have hb : ContDiff ℝ 1 b := by
    dsimp [b, laneCPushWeight, laneCSquareNormSq, laneCSquareX, laneCSquareY]
    fun_prop
  have hc : ContDiff ℝ 1 (fun z : ℂ => (a z : ℂ) + (b z : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp ha).add
      ((Complex.ofRealCLM.contDiff.comp hb).mul contDiff_const)
  convert hc using 1
  funext z
  exact Complex.mk_eq_add_mul_I (a z) (b z)

theorem laneC_inwardPush_zero (z : ℂ) : laneCInwardPush 0 z = z := by
  apply Complex.ext <;>
    simp [laneCInwardPush, laneCPushWeight, laneCSquareNormSq,
      laneCSquareX, laneCSquareY]

theorem laneC_inwardPush_tendsto (z : ℂ) :
    Filter.Tendsto (fun d : ℝ => laneCInwardPush d z) (nhds 0) (nhds z) := by
  have hc : Continuous (fun d : ℝ => laneCInwardPush d z) := by
    unfold laneCInwardPush laneCPushWeight
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  simpa only [laneC_inwardPush_zero] using (hc.tendsto (0 : ℝ))

 
theorem laneC_closed_ring_radius (z : ℂ) (hz : z ∈ laneCDoublePrimeCross) :
    3 / 2 ≤ laneCSquareRadius z ∧ laneCSquareRadius z ≤ 5 / 2 ∧
      laneCSquareRadius z ^ 2 ≤ laneCSquareNormSq z ∧
      laneCSquareNormSq z ≤ 2 * laneCSquareRadius z ^ 2 := by
  have hinner : interior laneCInnerCluster =
      Set.Ioo (-1 : ℝ) 2 ×ℂ Set.Ioo (-1 : ℝ) 2 := by
    simp [laneCInnerCluster, Complex.interior_reProdIm, interior_Icc]
  obtain ⟨houter, hnot⟩ := hz
  simp only [laneCOuterCluster, Complex.mem_reProdIm, Set.mem_Icc] at houter
  rw [hinner] at hnot
  simp only [Complex.mem_reProdIm, Set.mem_Ioo, not_and] at hnot
  let x := laneCSquareX z
  let y := laneCSquareY z
  let r := laneCSquareRadius z
  have hxabs : |x| ≤ 5 / 2 := abs_le.mpr
    ⟨by dsimp [x, laneCSquareX]; linarith [houter.1.1],
      by dsimp [x, laneCSquareX]; linarith [houter.1.2]⟩
  have hyabs : |y| ≤ 5 / 2 := abs_le.mpr
    ⟨by dsimp [y, laneCSquareY]; linarith [houter.2.1],
      by dsimp [y, laneCSquareY]; linarith [houter.2.2]⟩
  have hrhi : r ≤ 5 / 2 := by
    dsimp [r, laneCSquareRadius]
    exact max_le hxabs hyabs
  have hrlo : 3 / 2 ≤ r := by
    by_contra h
    have hrlt : r < 3 / 2 := lt_of_not_ge h
    have hxlt : |x| < 3 / 2 :=
      (le_max_left (|x|) (|y|)).trans_lt (by simpa [r, laneCSquareRadius] using hrlt)
    have hylt : |y| < 3 / 2 :=
      (le_max_right (|x|) (|y|)).trans_lt (by simpa [r, laneCSquareRadius] using hrlt)
    have hxlo := (abs_lt.mp hxlt).1
    have hxhi := (abs_lt.mp hxlt).2
    have hylo := (abs_lt.mp hylt).1
    have hyhi := (abs_lt.mp hylt).2
    dsimp [x, y, laneCSquareX, laneCSquareY] at hxlo hxhi hylo hyhi
    exact hnot ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  have hxle : |x| ≤ r := by
    dsimp [r, laneCSquareRadius]
    exact le_max_left _ _
  have hyle : |y| ≤ r := by
    dsimp [r, laneCSquareRadius]
    exact le_max_right _ _
  have hr0 : 0 ≤ r := by linarith
  have hx2 : x ^ 2 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxle)
      (add_nonneg hr0 (abs_nonneg x)), sq_abs x]
  have hy2 : y ^ 2 ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hyle)
      (add_nonneg hr0 (abs_nonneg y)), sq_abs y]
  have hqhi : laneCSquareNormSq z ≤ 2 * r ^ 2 := by
    dsimp [laneCSquareNormSq]
    nlinarith
  have hqlo : r ^ 2 ≤ laneCSquareNormSq z := by
    by_cases hxy : |x| ≤ |y|
    · have hre : r = |y| := by
        change max |x| |y| = |y|
        exact max_eq_right hxy
      rw [hre]
      dsimp [laneCSquareNormSq]
      nlinarith [sq_nonneg x, sq_abs y]
    · have hre : r = |x| := by
        change max |x| |y| = |x|
        exact max_eq_left (le_of_lt (lt_of_not_ge hxy))
      rw [hre]
      dsimp [laneCSquareNormSq]
      nlinarith [sq_nonneg y, sq_abs x]
  exact ⟨hrlo, hrhi, hqlo, hqhi⟩

 

theorem laneC_inwardPush_mem_open {d : ℝ} (hd : 0 < d)
    (hdsmall : d ≤ 1 / 1000) {z : ℂ} (hz : z ∈ laneCDoublePrimeCross) :
    laneCInwardPush d z ∈ laneCDoublePrimeAround := by
  let x := laneCSquareX z
  let y := laneCSquareY z
  let r := laneCSquareRadius z
  let w := laneCPushWeight d (laneCSquareNormSq z)
  obtain ⟨hrlo, hrhi, hqlo, hqhi⟩ := laneC_closed_ring_radius z hz
  have hpr := laneC_push_radius hd hdsmall hrlo hrhi hqlo hqhi
  have hr0 : 0 ≤ r := by linarith
  have hw : 0 < w := by
    by_contra h
    have hwr := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hr0
    linarith [hpr.1]
  have hxle : |x| ≤ r := by
    dsimp [r, laneCSquareRadius]
    exact le_max_left _ _
  have hyle : |y| ≤ r := by
    dsimp [r, laneCSquareRadius]
    exact le_max_right _ _
  have hxout : |w * x| < 5 / 2 := by
    rw [abs_mul, abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left hxle hw.le).trans_lt hpr.2
  have hyout : |w * y| < 5 / 2 := by
    rw [abs_mul, abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left hyle hw.le).trans_lt hpr.2
  have hinside : 3 / 2 < |w * x| ∨ 3 / 2 < |w * y| := by
    by_cases hxy : |x| ≤ |y|
    · right
      have hre : r = |y| := by
        change max |x| |y| = |y|
        exact max_eq_right hxy
      rw [abs_mul, abs_of_pos hw, ← hre]
      exact hpr.1
    · left
      have hre : r = |x| := by
        change max |x| |y| = |x|
        exact max_eq_left (le_of_lt (lt_of_not_ge hxy))
      rw [abs_mul, abs_of_pos hw, ← hre]
      exact hpr.1
  have hre : (laneCInwardPush d z).re = 1 / 2 + w * x := rfl
  have him : (laneCInwardPush d z).im = 1 / 2 + w * y := rfl
  have houter : laneCInwardPush d z ∈ interior laneCOuterCluster := by
    have hxa := abs_lt.mp hxout
    have hya := abs_lt.mp hyout
    simp only [laneCOuterCluster, Complex.interior_reProdIm, interior_Icc,
      Complex.mem_reProdIm, Set.mem_Ioo]
    rw [hre, him]
    exact ⟨⟨by linarith [hxa.1], by linarith [hxa.2]⟩,
      ⟨by linarith [hya.1], by linarith [hya.2]⟩⟩
  have hnot : laneCInwardPush d z ∉ laneCInnerCluster := by
    intro hzinner
    simp only [laneCInnerCluster, Complex.mem_reProdIm, Set.mem_Icc] at hzinner
    rw [hre, him] at hzinner
    rcases hinside with h | h
    · have habs : |w * x| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hzinner.1.1],
        by linarith [hzinner.1.2]⟩
      linarith
    · have habs : |w * y| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hzinner.2.1],
        by linarith [hzinner.2.2]⟩
      linarith
  exact ⟨houter, hnot⟩

 
theorem laneC_inwardPush_piecewise (d : ℝ) {γ : ℝ → ℂ} {z₀ z₁ : ℂ}
    (hγ : LQGMetric.IsPiecewiseC1Path γ z₀ z₁) :
    LQGMetric.IsPiecewiseC1Path (laneCInwardPush d ∘ γ)
      (laneCInwardPush d z₀) (laneCInwardPush d z₁) := by
  obtain ⟨F, hF⟩ := hγ.exists_pcwC1
  refine LQGMetric.IsPiecewiseC1Path.of_pcwC1 (F := F)
    (by simp [Function.comp, hγ.source]) (by simp [Function.comp, hγ.target])
    ((laneC_inwardPush_continuous d).comp_continuousOn hγ.continuousOn) ?_
  intro a b ha hab hb hFb
  exact (laneC_inwardPush_contDiff d).contDiffOn.comp (hF a b ha hab hb hFb)
    (fun _ _ => Set.mem_univ _)

 
theorem laneC_inwardPush_path_open {d : ℝ} (hd : 0 < d)
    (hdsmall : d ≤ 1 / 1000) {γ : ℝ → ℂ}
    (hγ : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) laneCDoublePrimeCross) :
    Set.MapsTo (laneCInwardPush d ∘ γ) (Set.Icc (0 : ℝ) 1)
      laneCDoublePrimeAround := by
  intro t ht
  exact laneC_inwardPush_mem_open hd hdsmall (hγ ht)

 

end SupercriticalLQGUniqueness.B2.DG20Conc
