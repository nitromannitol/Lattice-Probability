/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P8RatioUniform at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P8Chain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Trunc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Prob
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight

 
























set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

theorem scale_across_annAt (ξ : ℝ) (a a' : Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} (r : Ioi (0 : ℝ))
    (k₀ : ℝ) (hφ : ∀ u, φ' u = φ ((r : ℂ) * u) + k₀) (c : ℂ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) :
    acrossDist (Median.lfppMetric ξ a' φ') (annAt c s t hs hst) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) / ((a' : ℝ) * r)) *
        acrossDist (Median.lfppMetric ξ a φ) (annAt ((r : ℝ) • c) (r * s) (r * t)
          (mul_pos r.2 hs) (mul_lt_mul_of_pos_left hst r.2)) := by
  have hr : (0 : ℝ) < r := r.2
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  obtain ⟨-, h2, h3⟩ := image_dilate_annAt hr c s t hs hst
  exact acrossDist_comp_mul
    (by simpa using (by positivity : (0 : ℝ) < a * Real.exp (ξ * k₀) / (a' * r)))
    ENNReal.ofReal_ne_top (dilateHomeo hr) (lfppMetric_scale ξ a a' hr k₀ hφ) _ _ h2 h3

 

theorem scale_around_annAt (ξ : ℝ) (a a' : Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} (r : Ioi (0 : ℝ))
    (k₀ : ℝ) (hφ : ∀ u, φ' u = φ ((r : ℂ) * u) + k₀) (c : ℂ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) :
    aroundDist (Median.lfppMetric ξ a' φ') (annAt c s t hs hst) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) / ((a' : ℝ) * r)) *
        aroundDist (Median.lfppMetric ξ a φ) (annAt ((r : ℝ) • c) (r * s) (r * t)
          (mul_pos r.2 hs) (mul_lt_mul_of_pos_left hst r.2)) := by
  have hr : (0 : ℝ) < r := r.2
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  obtain ⟨h1, h2, h3⟩ := image_dilate_annAt hr c s t hs hst
  exact aroundDist_comp_mul
    (by simpa using (by positivity : (0 : ℝ) < a * Real.exp (ξ * k₀) / (a' * r)))
    ENNReal.ofReal_ne_top (dilateHomeo hr) (lfppMetric_scale ξ a a' hr k₀ hφ) _ _ h1 h2 h3

 
lemma le_ofReal_inv_mul_of_ofReal_mul_le {x M : ℝ} (hx : 0 < x) {A : ℝ≥0∞}
    (h : ENNReal.ofReal x * A ≤ ENNReal.ofReal M) : A ≤ ENNReal.ofReal (x⁻¹ * M) := by
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hx.le)]
  exact le_inv_mul_of_mul_le hx h

 
lemma ofReal_inv_mul_le_of_le_ofReal_mul {x M : ℝ} (hx : 0 < x) {A : ℝ≥0∞}
    (h : ENNReal.ofReal M ≤ ENNReal.ofReal x * A) : ENNReal.ofReal (x⁻¹ * M) ≤ A := by
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hx.le)]
  calc ENNReal.ofReal x⁻¹ * ENNReal.ofReal M ≤ ENNReal.ofReal x⁻¹ * (ENNReal.ofReal x * A) :=
        mul_le_mul_right h _
    _ = A := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hx.le), inv_mul_cancel₀ hx.ne',
          ENNReal.ofReal_one, one_mul]

lemma annAt_dilate_eq (c : ℂ) {s t : ℝ} (hs : 0 < s) (hst : s < t) (r : Ioi (0 : ℝ)) :
    (annAt c s t hs hst).dilate r r.2 = annAt ((r : ℝ) • c) (r * s) (r * t)
      (mul_pos r.2 hs) (mul_lt_mul_of_pos_left hst r.2) := rfl

 
def netAnn (b : Bool) (i : Fin 9) : EuclideanAnnulus :=
  annAt (netPt b i) (1 / 8) (1 / 4) (by norm_num) (by norm_num)


 





theorem pl_ratio_uniform_of_inputs (hP2 : PLHeatAnnulusTight) (hP6 : PLCompareSubset)
    (hS4 : Iface.DG20Section4) : PLRatioUniform := by
  intro ξ Q hQ D c hD m hm ζ hζ0 hζ1
  obtain ⟨Cm, hCm, hthm⟩ := thm_lqg_lfpp_of_inputs hP2 hP6 hS4 ξ Q hQ hD m hm hζ0 hζ1
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  set θ : ℝ := 1 / 40 with hθdef
  have hθ : 0 < θ := by norm_num [θ]
  have hXex : ∀ δ : Ioi (0 : ℝ), ∃ X : DistC → C(ℂ, ℝ), IsHeatSmoothing μ id δ X :=
    fun δ => by
      obtain ⟨X, -, hX⟩ := exists_heatVersion hμ δ δ.2
      exact ⟨X, hX⟩
  choose X0 hX0 using hXex
  set A12 : EuclideanAnnulus := annAt 0 1 2 one_pos one_lt_two with hA12
  
  have hV := hD.2.2.2.2.2.2 μ id hμ (fun r g => circleAvg g r 0)
    (fun r => Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hμ.1 r 0)
  obtain ⟨MDA, hMDA, hMDAb⟩ := (hV A12).2.2 θ hθ
  have hnD : ∀ (b : Bool) (i : Fin 9), ∃ M : ℝ, 0 < M ∧ ∀ r : Ioi (0 : ℝ),
      μ {g | ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
        acrossDist (D g) ((netAnn b i).dilate r r.2) < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal θ := by
    intro b i
    obtain ⟨M, hM, hMb⟩ := (hV (netAnn b i)).1.2 θ hθ
    exact ⟨M, hM, fun r => (hMb r).2⟩
  choose MND hMND hMNDb using hnD
  
  obtain ⟨MLA, hMLA, hMLAb⟩ := (hP2 ξ Q hQ m hm μ id hμ X0 hX0 A12).2 θ hθ
  have hnL : ∀ (b : Bool) (i : Fin 9), ∃ M : ℝ, 0 < M ∧ ∀ δ : Ioi (0 : ℝ), (δ : ℝ) ≤ 1 →
      μ {g | acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (X0 δ g)) (netAnn b i) <
        ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal θ := by
    intro b i
    obtain ⟨M, hM, hMb⟩ := (hP2 ξ Q hQ m hm μ id hμ X0 hX0 (netAnn b i)).2 θ hθ
    exact ⟨M, hM, fun δ hδ => (hMb δ hδ).1⟩
  choose MNL hMNL hMNLb using hnL
  
  set Sn : ℝ := ∑ b : Bool, ∑ i : Fin 9, (MND b i + MNL b i) with hSn
  have hSle : ∀ b i, MND b i + MNL b i ≤ Sn := by
    intro b i
    refine le_trans ?_ (Finset.single_le_sum (f := fun b => ∑ i : Fin 9, (MND b i + MNL b i))
      (fun b _ => Finset.sum_nonneg fun i _ => add_nonneg (hMND b i).le (hMNL b i).le)
      (Finset.mem_univ b))
    exact Finset.single_le_sum (f := fun i => MND b i + MNL b i)
      (fun i _ => add_nonneg (hMND b i).le (hMNL b i).le) (Finset.mem_univ i)
  have hS0 : 0 ≤ Sn := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ =>
    add_nonneg (hMND b i).le (hMNL b i).le
  set S : ℝ := MDA + MLA + Sn with hSdef
  have hS : 0 < S := by positivity
  have hSDA : MDA ≤ S := by linarith
  have hSLA : MLA ≤ S := by linarith
  have hSND : ∀ b i, MND b i ≤ S := fun b i => by linarith [hSle b i, hMNL b i]
  have hSNL : ∀ b i, MNL b i ≤ S := fun b i => by linarith [hSle b i, hMND b i]
  set Cf : ℝ := 2 * Cm * S ^ 2 + 2 with hCfdef
  have hCf : 1 < Cf := by have : 0 ≤ 2 * Cm * S ^ 2 := by positivity
                          linarith
  refine ⟨Cf, hCf, fun R hR => ?_⟩
  
  have hT := hthm (ball (0 : ℂ) (3 * R)) isOpen_ball (isConnected_ball (by linarith))
    isBounded_ball μ id hμ X0 hX0
  have hev := (ENNReal.tendsto_nhds_zero.1 hT) (ENNReal.ofReal θ) (ENNReal.ofReal_pos.2 hθ)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨εR, hεR, hεRb⟩ := hev
  refine ⟨min (εR / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_⟩
  intro ε r hε h100 hrR
  have hε0 : (0 : ℝ) < ε := ε.2
  have hε12 : (ε : ℝ) ≤ 1 / 2 := hε.trans (min_le_right _ _)
  have hεR' : (ε : ℝ) < εR := lt_of_le_of_lt (hε.trans (min_le_left _ _)) (by linarith)
  have hεI : (ε : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨hε0, by linarith⟩
  have hr0 : (0 : ℝ) < r := r.2
  set ρ : ℝ := (ε : ℝ) ^ (1 - ζ) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hε0 _
  have hρr : ρ ≤ r / 16 := by linarith
  have hερ : (ε : ℝ) ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge hε0 (by linarith : (ε : ℝ) ≤ 1)
      (by linarith : 1 - ζ ≤ 1)
    simpa using this
  have hδ1 : (ε : ℝ) / r ≤ 1 := by rw [div_le_one hr0]; linarith
  set δ : Ioi (0 : ℝ) := ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos (Set.mem_Ioi.mp ε.2)
    (Set.mem_Ioi.mp r.2))⟩ with hδdef
  
  have hcmpP : μ {g | ¬ compareHolds (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (D g) ρ
      (ball (0 : ℂ) (3 * R)) Cm} ≤ ENNReal.ofReal θ := by
    have h1 := hεRb (y := (ε : ℝ))
      (by rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hε0]; exact hεR') hε0
    simp only [hεI, ↓reduceDIte] at h1
    exact h1
  
  set cr : DistC → ℝ := fun g => circleAvg (affineComp r 0 g) 1 0 with hcrdef
  set Y : DistC → C(ℂ, ℝ) := fun g => unitField (X0 ε g) r (cr g) with hYdef
  have hYv : ∀ᵐ g ∂μ, ∀ u, Y g u = heatMollify (δ : ℝ) (gScale r g) u := by
    filter_upwards [ae_heatMollify_gScale hμ ε r (X0 ε) (hX0 ε)] with g hg u
    exact (hg u).symm
  have hXv : ∀ᵐ g ∂μ, ∀ u, X0 δ g u = heatMollify (δ : ℝ) g u :=
    DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ δ (X0 δ) (hX0 δ)
  have hsc := isWholePlaneGFF_gScale hμ.1 hr0
  have hmapsc : μ.map (gScale r) = μ := by
    have := map_gScale hμ hr0; rw [Measure.map_id] at this; exact this
  
  set B1 : Set DistC := {g | ENNReal.ofReal MDA <
    ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
      aroundDist (D g) (A12.dilate r r.2)} with hB1
  set B2 : Bool × Fin 9 → Set DistC := fun p => {g |
    ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
      acrossDist (D g) ((netAnn p.1 p.2).dilate r r.2) < ENNReal.ofReal (MND p.1 p.2)⁻¹}
    with hB2
  set B3 : Set DistC := {g | ENNReal.ofReal MLA <
    aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) A12} with hB3
  set B4 : Bool × Fin 9 → Set DistC := fun p => {g |
    acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) (Y g)) (netAnn p.1 p.2) <
      ENNReal.ofReal (MNL p.1 p.2)⁻¹} with hB4
  set B5 : Set DistC := {g | ¬ compareHolds (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (D g) ρ
      (ball (0 : ℂ) (3 * R)) Cm} with hB5
  have hP1 : μ B1 ≤ ENNReal.ofReal θ := (hMDAb r).1
  have hP2' : ∀ p, μ (B2 p) ≤ ENNReal.ofReal θ := fun p => hMNDb p.1 p.2 r
  have hP3 : μ B3 ≤ ENNReal.ofReal θ := by
    refine (measure_le_of_scaled_version hsc.measurable.aemeasurable hmapsc (δ : ℝ) Y (X0 δ) hYv
      hXv (fun φ => ENNReal.ofReal MLA <
        aroundDist (Median.lfppMetric (ξ : ℝ) (m δ) φ) A12)).trans ?_
    exact (hMLAb δ hδ1).2
  have hP4 : ∀ p, μ (B4 p) ≤ ENNReal.ofReal θ := by
    intro p
    refine (measure_le_of_scaled_version hsc.measurable.aemeasurable hmapsc (δ : ℝ) Y (X0 δ) hYv
      hXv (fun φ => acrossDist (Median.lfppMetric (ξ : ℝ) (m δ) φ) (netAnn p.1 p.2) <
        ENNReal.ofReal (MNL p.1 p.2)⁻¹)).trans ?_
    exact hMNLb p.1 p.2 δ hδ1
  have hP5 : μ B5 ≤ ENNReal.ofReal θ := hcmpP
  set Bad : Set DistC := B1 ∪ (⋃ p, B2 p) ∪ B3 ∪ (⋃ p, B4 p) ∪ B5 with hBad
  have hU18 : ∀ (F : Bool × Fin 9 → Set DistC), (∀ p, μ (F p) ≤ ENNReal.ofReal θ) →
      μ (⋃ p, F p) ≤ ENNReal.ofReal (18 * θ) := by
    intro F hF
    calc μ (⋃ p, F p) ≤ ∑ p, μ (F p) := measure_iUnion_fintype_le μ F
      _ ≤ ∑ _p : Bool × Fin 9, ENNReal.ofReal θ := Finset.sum_le_sum fun p _ => hF p
      _ = ENNReal.ofReal (18 * θ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have hBadlt : μ Bad < 1 := by
    calc μ Bad ≤ μ B1 + μ (⋃ p, B2 p) + μ B3 + μ (⋃ p, B4 p) + μ B5 := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal θ + ENNReal.ofReal (18 * θ) + ENNReal.ofReal θ +
            ENNReal.ofReal (18 * θ) + ENNReal.ofReal θ := by
          gcongr
          · exact hU18 B2 hP2'
          · exact hU18 B4 hP4
      _ = ENNReal.ofReal (39 * θ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ < 1 := by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
                    (by norm_num [θ])
  obtain ⟨g, hgB, hcr⟩ := exists_good_point hBadlt (CircleAvg.ae_circleAvg_affineComp hμ.1 hr0 0)
  simp only [id] at hcr
  simp only [hBad, mem_union, mem_iUnion, not_or, not_exists] at hgB
  obtain ⟨⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩, hg5⟩ := hgB
  
  set hc : ℝ := circleAvg g r 0 with hhc
  set bb : ℝ := lfppScaleFactor m ε r with hbb
  have hbb0 : 0 < bb := lfppScaleFactor_pos m ε r
  have hbbδ : bb = (r : ℝ) * (m δ : ℝ) / (m ε : ℝ) := rfl
  have hcr0 : (0 : ℝ) < c r := (c r).2
  have he0 : 0 < Real.exp ((ξ : ℝ) * hc) := Real.exp_pos _
  set xD : ℝ := (c r : ℝ) * Real.exp ((ξ : ℝ) * hc) with hxD
  set xL : ℝ := bb * Real.exp ((ξ : ℝ) * hc) with hxL
  have hxD0 : 0 < xD := mul_pos hcr0 he0
  have hxL0 : 0 < xL := mul_pos hbb0 he0
  have hnD : (c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * hc)) = xD⁻¹ := by
    rw [hxD, mul_inv, Real.exp_neg]
  have hκ : (m ε : ℝ) * Real.exp ((ξ : ℝ) * -cr g) / ((m δ : ℝ) * r) = xL⁻¹ := by
    have hcrg : cr g = hc := hcr
    have h1 : (0 : ℝ) < m ε := (m ε).2
    have h2 : (0 : ℝ) < m δ := (m δ).2
    rw [hcrg, hxL, hbbδ, mul_neg, Real.exp_neg]
    field_simp
  have hφY : ∀ u, Y g u = X0 ε g ((r : ℂ) * u) + -cr g := fun u => rfl
  
  have hAD : aroundDist (D g) (annAt 0 (r * 1) (r * 2) (mul_pos hr0 one_pos)
      (mul_lt_mul_of_pos_left one_lt_two hr0)) < ENNReal.ofReal (2 * (xD * MDA)) := by
    have h1 := hg1
    simp only [hB1, mem_ofPred_eq, not_lt] at h1
    rw [hnD, hA12, annAt_dilate_eq, smul_zero] at h1
    have h2 := le_ofReal_inv_mul_of_ofReal_mul_le (inv_pos.2 hxD0) h1
    rw [inv_inv] at h2
    exact lt_of_le_of_lt h2 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (by nlinarith [mul_pos hxD0 hMDA]))
  
  have hnetD : ∀ b : Bool, ∀ i : ℕ, i < 9 → ENNReal.ofReal (xD * S⁻¹) ≤
      acrossDist (D g) (annAt ((r : ℝ) • netPt b i) (r * (1 / 8)) (r * (1 / 4))
        (mul_pos hr0 (by norm_num)) (mul_lt_mul_of_pos_left (by norm_num) hr0)) := by
    intro b i hi
    have h1 := hg2 (b, ⟨i, hi⟩)
    simp only [hB2, mem_ofPred_eq, not_lt] at h1
    rw [hnD] at h1
    have h2 := ofReal_inv_mul_le_of_le_ofReal_mul (inv_pos.2 hxD0) h1
    rw [inv_inv] at h2
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hS (hMND b ⟨i, hi⟩)).2 (hSND b ⟨i, hi⟩)) hxD0.le
  
  have hAL : aroundDist (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (annAt 0 (r * 1) (r * 2)
      (mul_pos hr0 one_pos) (mul_lt_mul_of_pos_left one_lt_two hr0)) <
        ENNReal.ofReal (2 * (xL * MLA)) := by
    have h1 := hg3
    simp only [hB3, mem_ofPred_eq, not_lt] at h1
    rw [hA12, scale_around_annAt (ξ : ℝ) (m ε) (m δ) r (-cr g) hφY 0 one_pos one_lt_two, hκ,
      smul_zero] at h1
    have h2 := le_ofReal_inv_mul_of_ofReal_mul_le (inv_pos.2 hxL0) h1
    rw [inv_inv] at h2
    exact lt_of_le_of_lt h2 ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (by nlinarith [mul_pos hxL0 hMLA]))
  
  have hnetL : ∀ b : Bool, ∀ i : ℕ, i < 9 → ENNReal.ofReal (xL * S⁻¹) ≤
      acrossDist (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (annAt ((r : ℝ) • netPt b i)
        (r * (1 / 8)) (r * (1 / 4)) (mul_pos hr0 (by norm_num))
        (mul_lt_mul_of_pos_left (by norm_num) hr0)) := by
    intro b i hi
    have h1 := hg4 (b, ⟨i, hi⟩)
    simp only [hB4, mem_ofPred_eq, not_lt] at h1
    rw [netAnn, scale_across_annAt (ξ : ℝ) (m ε) (m δ) r (-cr g) hφY, hκ] at h1
    have h2 := ofReal_inv_mul_le_of_le_ofReal_mul (inv_pos.2 hxL0) h1
    rw [inv_inv] at h2
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ hS (hMNL b ⟨i, hi⟩)).2 (hSNL b ⟨i, hi⟩)) hxL0.le
  
  have hcmp : compareHolds (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (D g) ρ
      (ball (0 : ℂ) (3 * R)) Cm := by
    have h1 := hg5
    simp only [hB5, mem_ofPred_eq, not_not] at h1
    exact h1
  
  have hup := chain_scale (D g) (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) hr0 hrR hρ0 hρr
    hAD hnetL (fun z w hz hw => (hcmp z w hz hw).1)
  have hlow := chain_scale (Median.lfppMetric (ξ : ℝ) (m ε) (X0 ε g)) (D g) hr0 hrR hρ0 hρr
    hAL hnetD (fun z w hz hw => (hcmp z w hz hw).2)
  rw [← ENNReal.ofReal_mul hCm.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hup hlow
  
  have hup' : bb * S⁻¹ ≤ 2 * Cm * (c r : ℝ) * MDA := by
    have : bb * S⁻¹ * Real.exp ((ξ : ℝ) * hc) ≤
        2 * Cm * (c r : ℝ) * MDA * Real.exp ((ξ : ℝ) * hc) := by
      calc bb * S⁻¹ * Real.exp ((ξ : ℝ) * hc) = xL * S⁻¹ := by rw [hxL]; ring
        _ ≤ Cm * (2 * (xD * MDA)) := hup
        _ = _ := by rw [hxD]; ring
    exact le_of_mul_le_mul_right this he0
  have hlow' : (c r : ℝ) * S⁻¹ ≤ 2 * Cm * bb * MLA := by
    have : (c r : ℝ) * S⁻¹ * Real.exp ((ξ : ℝ) * hc) ≤
        2 * Cm * bb * MLA * Real.exp ((ξ : ℝ) * hc) := by
      calc (c r : ℝ) * S⁻¹ * Real.exp ((ξ : ℝ) * hc) = xD * S⁻¹ := by rw [hxD]; ring
        _ ≤ Cm * (2 * (xL * MLA)) := hlow
        _ = _ := by rw [hxL]; ring
    exact le_of_mul_le_mul_right this he0
  have hkey : (r : ℝ) * (m δ : ℝ) / ((c r : ℝ) * (m ε : ℝ)) = bb / (c r : ℝ) := by
    have h1 : (0 : ℝ) < m ε := (m ε).2
    rw [hbbδ]; field_simp
  rw [hkey]
  have hS2 : 2 * Cm * S * S ≤ Cf := by
    have : 2 * Cm * S * S = 2 * Cm * S ^ 2 := by ring
    rw [this, hCfdef]; linarith
  have hCf0 : 0 < Cf := by linarith
  constructor
  · 
    have hc_le : (c r : ℝ) ≤ Cf * bb := by
      have h1 : (c r : ℝ) ≤ 2 * Cm * bb * MLA * S := by
        have := mul_le_mul_of_nonneg_right hlow' hS.le
        rwa [mul_assoc, inv_mul_cancel₀ hS.ne', mul_one] at this
      calc (c r : ℝ) ≤ 2 * Cm * bb * MLA * S := h1
        _ = (2 * Cm * bb * S) * MLA := by ring
        _ ≤ (2 * Cm * bb * S) * S := mul_le_mul_of_nonneg_left hSLA (by positivity)
        _ = (2 * Cm * S * S) * bb := by ring
        _ ≤ Cf * bb := mul_le_mul_of_nonneg_right hS2 hbb0.le
    rw [le_div_iff₀ hcr0]
    calc Cf⁻¹ * (c r : ℝ) ≤ Cf⁻¹ * (Cf * bb) :=
          mul_le_mul_of_nonneg_left hc_le (inv_nonneg.2 hCf0.le)
      _ = bb := by field_simp
  · 
    have hb_le : bb ≤ Cf * (c r : ℝ) := by
      have h1 : bb ≤ 2 * Cm * (c r : ℝ) * MDA * S := by
        have := mul_le_mul_of_nonneg_right hup' hS.le
        rwa [mul_assoc, inv_mul_cancel₀ hS.ne', mul_one] at this
      calc bb ≤ 2 * Cm * (c r : ℝ) * MDA * S := h1
        _ = (2 * Cm * (c r : ℝ) * S) * MDA := by ring
        _ ≤ (2 * Cm * (c r : ℝ) * S) * S := mul_le_mul_of_nonneg_left hSDA (by positivity)
        _ = (2 * Cm * S * S) * (c r : ℝ) := by ring
        _ ≤ Cf * (c r : ℝ) := mul_le_mul_of_nonneg_right hS2 hcr0.le
    rw [div_le_iff₀ hcr0]
    exact hb_le

 
end SupercriticalLQGUniqueness.B2.Polylog
