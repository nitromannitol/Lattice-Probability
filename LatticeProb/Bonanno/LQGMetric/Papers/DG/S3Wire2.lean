/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3Wire2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17 Steps with DG L3.19 on `[1/6,5/6]²` (task P2-DGWIRE)

Source: Ding–Gwynne arXiv:1807.01072, proof of Prop 3.17, DG:1523–1591 (Step 3: DG:1587–1589).

**Box mismatch** (as in S3Wire1): `p17v_lb` / `dgP317Show_of_V` (S3P17V3, S3P17V5) take
`DGLem319Scaled` on `[1/12,11/12]²`, which is not available for `μ_ĥ = muHat … p18_hK0`
(restricted to `K₀ = [1/10,9/10]²`). In `p17v_lb` the box enters only through
`cthickening a (T K') ⊆ Q` with `T K' ⊆ [1/4,3/4]²` and `a ≤ 1/6`; taking `a ≤ 1/12` the
thickening lies in `[1/6,5/6]²`.

* `wire_p17v_lb` — `p17v_lb` with `h319` on `[1/6,5/6]²` (`a = min (r/2) (1/12)`);
* `wire_dgP317Show_of_Lb` — the proof of `dgP317Show_of_V` with its L3.19 step replaced by the
  lower bound `DGP317Lb` itself (verbatim otherwise);
* `wire_dgP317Show_of_muHat` — `dgP317Show_of_muHat` with `h319` on `[1/6,5/6]²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω]

lemma wire_Q19_bdd : Bornology.IsBounded (p39Box p18c0 (1 / 3) (1 / 6)) :=
  (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)

section
variable {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`p17v_lb` with DG L3.19 on `[1/6,5/6]²`** (DG:1587–1589; proof of `p17v_lb` with
`a = min (r/2) (1/12)`) -/
theorem wire_p17v_lb (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d)
    {μ : Ω → Measure ℂ}
    (h319 : DGLem319Scaled P (p17vW W) μ γ d (p39Box p18c0 (1 / 3) (1 / 6))) :
    DGP317Lb P (p17vMu μ) d (p39Box 0 1 (1 / 6)) := by
  intro K' U' hK' hU' hKU' hU'S ζ hζ
  obtain ⟨r, hr, hthick⟩ := hK'.exists_thickening_subset_open hU' hKU'
  set a := min (r / 2) (1 / 12) with ha_def
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hlb := dgP317Lb_of (isWhiteNoise_p17vW hW) hγ hd wire_Q19_bdd 0 h319
  have hsq : ∀ y ∈ K', 1 / 4 ≤ (p17vT y).re ∧ (p17vT y).re ≤ 3 / 4 ∧
      1 / 4 ≤ (p17vT y).im ∧ (p17vT y).im ≤ 3 / 4 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := hU'S (hKU' hy)
    rw [p17vT_re, p17vT_im]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hA : p17vT '' K' ⊆ p17lReg 0 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hsq y hy
    simp only [p17lReg, Complex.mem_reProdIm, mem_Ico, Complex.zero_re, Complex.zero_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hAQ : cthickening a (p17vT '' K') ⊆ p39Box p18c0 (1 / 3) (1 / 6) := by
    rw [(hK'.image continuous_p17vT).cthickening_eq_biUnion_closedBall ha.le]
    simp only [iUnion_subset_iff]
    rintro _ ⟨y, hy, rfl⟩ z hz
    obtain ⟨h1, h2, h3, h4⟩ := hsq y hy
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre := (Complex.abs_re_le_norm (z - p17vT y)).trans hz
    have him := (Complex.abs_im_le_norm (z - p17vT y)).trans hz
    rw [Complex.sub_re, abs_le] at hre
    rw [Complex.sub_im, abs_le] at him
    have ha6 : a ≤ 1 / 12 := min_le_right _ _
    simp only [p39Box, p18c0, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hre.1, hre.2, him.1, him.2]
  obtain ⟨p, C, ε₀, hp, hε₀, h⟩ := hlb (p17vT '' K') a ha hA hAQ ζ hζ
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε => (measure_mono fun ω hω => ?_).trans (h ε hε)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  intro hn
  apply hω
  intro y hy y' hy'
  have hfar : r ≤ ‖y' - y‖ := by
    by_contra hlt
    rw [not_le] at hlt
    exact hy' (hthick (mem_thickening_iff.2 ⟨y, hy, by rwa [dist_eq_norm]⟩))
  have h1 := hn (p17vT y) ⟨y, hy, rfl⟩ (p17vT y')
    (by rw [norm_p17vT_sub]; linarith [min_le_left (r / 2) (1 / 12)])
    (p17vTinv ⁻¹' p39Box 0 1 (1 / 6))
  refine h1.trans (ENat.toENNReal_le.2 ?_)
  have := p17v_lgd_up (μ ω) ε (p17vTinv ⁻¹' p39Box 0 1 (1 / 6)) y y'
  rwa [p17v_pre_pre] at this

end

/-- **`dgP317Show_of_V` from the lower bound `DGP317Lb`** (DG:1527–1591; proof verbatim) -/
theorem wire_dgP317Show_of_Lb {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hd : 1 ≤ dGamma γ) {μ : Ω → Measure ℂ}
    (h311 : DGLem311Scaled P (p17vW W) μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h311v : DGLem311ScaledV P (p17vW W) μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (hLb : DGP317Lb P (p17vMu μ) (dGamma γ) (p39Box 0 1 (1 / 6))) :
    DGP317Show P W γ := by
  have hW' := isWhiteNoise_p17vW hW
  intro K U hK hU hKU hUS ζ hζ
  rcases K.eq_empty_or_nonempty with rfl | -
  · exact ⟨1, 0, 1, one_pos, one_pos, fun δ _ => by simp⟩
  obtain ⟨r₀, hr₀, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  set d := dGamma γ with hdd
  have hd0 : 0 < d := by linarith
  set η := p17sEta γ ζ with hηd
  set η' := p17sEta' γ d ζ with hη'd
  have hη0 : 0 < η := p17sEta_pos hγ hζ.1
  have hη64 : η ≤ ζ / 64 := p17sEta_le hγ hζ.1
  have hη1 : η < 1 := hη64.trans_lt (by linarith [hζ.2])
  have hη'0 : 0 < η' := p17sEta'_pos hγ hd0 hζ.1
  have hη'1 : η' ≤ η := p17sEta'_le hγ hd0 hζ.1
  set B := (2 + γ) ^ 2 with hB
  have hB0 : 0 < B := by positivity
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set r : ℝ := 1 / 6 with hr
  have hr0 : 0 < r := by norm_num
  obtain ⟨lam1, C1, hlam1, h1⟩ := p17v_lemma313 hW hγ hd h311 hη0 hη1
  obtain ⟨lam2, C2, hlam2, h2⟩ := p17v_lemma313V hW hγ hd h311v hη0 hη1
  obtain ⟨K3, d3, hd3, h3⟩ := dg_lemma35 hW p17s_sq_bdd hη'0
  obtain ⟨K4, d4, hd4, h4⟩ := dg_lemma36 hW p17s_sq_bdd (ζ := η' / 2) (by positivity)
    (by linarith) (le_refl (1 : ℝ)) one_pos
  obtain ⟨p5, C5, e5, hp5, he5, h5⟩ := hLb (cthickening (r₀ / 3) K) (thickening (2 * r₀ / 3) K)
    hK.cthickening isOpen_thickening
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
    ((thickening_mono (by linarith) K).trans (hthick.trans hUS)) η ⟨hη0, hη1⟩
  obtain ⟨C6, d6, hd6, h6⟩ := p17v_window hW (ζ := η' / 2) (by positivity)
  obtain ⟨d7, hd7, h7⟩ := p17v_cub (d := d) hγ hd hη0 hη1
  set q := min (min (lam1 / Real.log 2) (lam2 / Real.log 2)) (min η' (min 1 (B * p5))) with hqd
  have hq : 0 < q := lt_min (lt_min (div_pos hlam1 hl2) (div_pos hlam2 hl2))
    (lt_min hη'0 (lt_min one_pos (mul_pos hB0 hp5)))
  have hq1 : q ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  set δ₀ := min (min (min (min (Real.exp (-4)) d3) (min d4 (e5 ^ (1 / B))))
    (min (min r (r₀ / 6)) (min ((1 / 12 : ℝ) ^ (1 / (ζ / 2)))
      (((ζ / 8) ^ 3 / 768) ^ (1 / (ζ / 8)))))) (min d6 d7) with hδ₀d
  have hζ0 := hζ.1
  have hζ1 := hζ.2
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (lt_min (lt_min (Real.exp_pos _) hd3)
    (lt_min hd4 (Real.rpow_pos_of_pos he5 _)))
    (lt_min (lt_min hr0 (by positivity)) (lt_min (by positivity) (by positivity))))
    (lt_min hd6 hd7)
  refine ⟨q, |C1| + |C2| + |K3| + |K4| + |C5| + |C6|, δ₀, hq, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδlt⟩ := hδ
  simp only [hδ₀d, lt_min_iff] at hδlt
  obtain ⟨⟨⟨⟨hδe4, hδ3⟩, hδ4, hδ5⟩, ⟨hδr, hδr₀⟩, hδs1, hδs2⟩, hδ6, hδ7⟩ := hδlt
  have hδe : δ ≤ Real.exp (-1) := hδe4.le.trans (Real.exp_le_exp.2 (by norm_num))
  have hδ1 : δ < 1 := hδe.trans_lt (by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this)
  set M := Blueprint.dgM δ with hM
  obtain ⟨hM1, hM2, hM3, -⟩ := p17s_dgM hδ0 hδ1
  set ε := δ ^ B with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hδ0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le hB0.le
  have hε5 : ε < e5 := by
    have := Real.rpow_lt_rpow hδ0.le hδ5 hB0
    rwa [← Real.rpow_mul he5.le, one_div_mul_cancel hB0.ne', Real.rpow_one] at this
  -- `A = δ 2^{m}` for Lemma 3.6
  set A := δ * (2 : ℝ) ^ (M + 1) with hA
  have h22 : (2 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ ^ M = 2 := by
    rw [pow_succ, mul_comm ((2 : ℝ) ^ M) 2, mul_assoc, ← mul_pow]; norm_num
  have hpow : 0 < (2 : ℝ) ^ (M + 1) := by positivity
  have hA1 : 1 < A := by
    have := mul_le_mul_of_nonneg_right hM1 hpow.le; rw [hA]; linarith
  have hA4 : A < 4 := by
    have := mul_lt_mul_of_pos_right hM2 hpow; rw [hA]; linarith
  have hL4 : 4 ≤ Real.log δ⁻¹ := by
    rw [Real.log_inv, le_neg]
    exact (Real.log_le_log hδ0 hδe4.le).trans_eq (Real.log_exp _)
  have hA2 : A < Real.exp (Real.log δ⁻¹ ^ (1 - η' / 2)) := by
    have e4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    have hp2 : 2 ≤ Real.log δ⁻¹ ^ (1 - η' / 2) :=
      calc (2 : ℝ) = (4 : ℝ) ^ ((1 : ℝ) / 2) := e4.symm
        _ ≤ Real.log δ⁻¹ ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hL4 (by norm_num)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
    exact hA4.trans_le (he2.trans (Real.exp_le_exp.2 hp2))
  have hδA : δ / A = (2 : ℝ)⁻¹ ^ (M + 1) := by
    rw [hA, inv_pow]; field_simp
  -- the six estimates and the null set
  have b1 := p17s_abs_bd (Real.exp_pos _).le
    (p17s_exp_m (m := M + 1) hδ0 hlam1 (by push_cast; linarith))
    (h1 (M + 1) ε hε0 hε1 (h7 δ hδ0 hδ7 hδ1))
  have b2 := p17s_abs_bd (Real.exp_pos _).le
    (p17s_exp_m (m := M + 1) hδ0 hlam2 (by push_cast; linarith))
    (h2 (M + 1) ε hε0 hε1 (h7 δ hδ0 hδ7 hδ1))
  have b3 := p17s_abs_bd (Real.rpow_nonneg hδ0.le _) le_rfl (h3 δ ⟨hδ0, hδ3⟩)
  have b4 := p17s_abs_bd (Real.rpow_nonneg hδ0.le _) le_rfl (h4 δ ⟨hδ0, hδ4⟩ A hA1 hA2)
  have b5 := p17s_abs_bd (Real.rpow_nonneg hε0.le p5)
    (by rw [hε, ← Real.rpow_mul hδ0.le]) (h5 ε ⟨hε0, hε5⟩)
  have b6 := p17s_abs_bd (Real.rpow_nonneg hδ0.le _)
    (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hq1) (h6 δ ⟨hδ0, hδ6⟩)
  have hd2 : 2 * p39d (M + 1 + 1) ≤ 1 := by
    rw [p17v_two_p39d]; exact pow_le_one₀ (by norm_num) (by norm_num)
  set N := {ω | ¬ ∀ y, DDDF.phiVer (p17vW W) P (p39d (M + 1 + 1)) 1 y ω =
      DDDF.phiVer W P (2 * p39d (M + 1 + 1)) 1 (p17vTinv y) ω +
        DDDF.phiVer W P 1 2 (p17vTinv y) ω} with hNd
  have hN : P N = 0 := by
    have h := ae_phiVer_p17vW hW (p39d_pos (M + 1 + 1)) hd2
    rwa [ae_iff] at h
  have hch := p17s_union2' (by positivity) (abs_nonneg _) hδ0 hδ1.le
    (p17s_union2' (by positivity) (abs_nonneg _) hδ0 hδ1.le
    (p17s_union2' (by positivity) (abs_nonneg _) hδ0 hδ1.le
      (p17s_union2' (by positivity) (abs_nonneg _) hδ0 hδ1.le
        (p17s_union2' (abs_nonneg _) (abs_nonneg _) hδ0 hδ1.le b1 b2
          (min_le_left _ _ |>.trans (min_le_left _ _))
          (min_le_left _ _ |>.trans (min_le_right _ _))) b3 le_rfl
        (min_le_right _ _ |>.trans (min_le_left _ _))) b4 le_rfl
      (min_le_right _ _ |>.trans ((min_le_right _ _).trans (min_le_left _ _)))) b5 le_rfl
    (min_le_right _ _ |>.trans ((min_le_right _ _).trans (min_le_right _ _)))) b6 le_rfl le_rfl
  refine le_trans (measure_mono ?_) ((measure_union_le _ N).trans
    ((add_le_add_left hch _).trans (by rw [hN, add_zero])))
  -- the good event
  intro ω hω
  by_contra hn
  simp only [mem_union, not_or] at hn
  obtain ⟨⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, nN⟩ := hn
  simp only [hNd, mem_ofPred_eq, not_exists, not_and, not_not, not_lt, not_le] at n1 n2 n3 n4 n5 n6 nN
  apply hω
  have ht0 := p39d_pos (M + 1 + 1)
  have ht1 : p39d (M + 1 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc := ((DDDF.isPhiVersion_phiVer hW' ht0 ht1).cont ω).comp continuous_p17vT
  have hBw := DDDF.isPhiVersion_phiVer (P := P) hW one_pos (by norm_num : (1 : ℝ) ≤ 2)
  refine p17s_good (r := r) (r₀ := r₀) (Q := p39Box 0 1 (1 / 6)) (μ := p17vMu μ ω)
    (φt := fun z => DDDF.phiVer (p17vW W) P (p39d (M + 1 + 1)) 1 (p17vT z) ω)
    hγ hd hζ.1 hζ.2 hδ0 hδe hδr.le hδr₀.le
    (p17s_rpow_small (by positivity) (by norm_num) hδ0 hδs1.le)
    (p17s_rpow_small (by positivity) (by positivity) hδ0 hδs2.le) subset_rfl hc n1 n2 n3
    (fun z hz => ?_) hU hKU hUS hthick n5
  have e := nN (p17vT z)
  rw [p17vTinv_T, p17v_two_p39d] at e
  have hw := (p17v_abs_le_iSup (hBw.cont ω) hz).trans n6.le
  have h4' := n4 z hz z hz (by simp; positivity)
  rw [hδA] at h4'
  rw [e]
  calc |DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (M + 1)) 1 z ω + DDDF.phiVer W P 1 2 z ω -
        DDDF.phiVer W P δ 1 z ω|
      ≤ |DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ (M + 1)) 1 z ω - DDDF.phiVer W P δ 1 z ω| +
          |DDDF.phiVer W P 1 2 z ω| := by
        rw [show ∀ a b c : ℝ, a + b - c = (a - c) + b by intros; ring]
        exact abs_add_le _ _
    _ ≤ η' / 2 * Real.log δ⁻¹ + η' / 2 * Real.log δ⁻¹ := add_le_add h4' hw
    _ = η' * Real.log δ⁻¹ := by ring

/-- **`dgP317Show_of_muHat` with DG L3.19 on `[1/6,5/6]²`** (D121 item 3) -/
theorem wire_dgP317Show_of_muHat {γ : ℝ} (hγ : 0 < γ) (hd : 1 ≤ dGamma γ)
    (hin : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W),
      DGLem311Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)) ∧
      DGLem311ScaledV P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)) ∧
      DGLem319Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) : DGP317Show P W γ := by
  obtain ⟨h1, h2, h3⟩ := hin P (p17vW W) (isWhiteNoise_p17vW hW)
  exact wire_dgP317Show_of_Lb hW hγ hd h1 h2 (wire_p17v_lb hW hγ hd h3)

end LQGMetric.DG
