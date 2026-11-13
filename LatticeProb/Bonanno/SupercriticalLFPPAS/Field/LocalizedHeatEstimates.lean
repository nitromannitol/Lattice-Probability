/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.LocalizedHeatEstimates at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedPolarFormula
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedApproximation
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedTail

/-!
# Quantitative localized heat-field estimates

The Gaussian estimates here use the DFGPS integrable Gaussian weight after rescaling by the heat
scale. This keeps constants independent of the scale.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open SupercriticalLQGUniqueness.B2.Polylog
open LQGMetric.DFGPS

namespace SupercriticalLFPPAS.Field

/-- Integrability of a bounded-profile polar integrand under the DFGPS circle-average growth
bound. -/
theorem integrableOn_polarIntegrand_gauss {ε A C : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {F w : ℝ → ℝ}
    (hF : ∀ r, 0 < r → |F r| ≤ C * (A / r + r + 1))
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hw : ∀ r, |w r| ≤ 1) (hwc : ContinuousOn w (Ioi (0 : ℝ))) :
    IntegrableOn (fun r => r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)) (Ioi 0) := by
  have hc : 0 < (1 / ε ^ 2 : ℝ) := by positivity
  have hmajor := (integrableOn_gaussW A hc).const_mul C
  have hcont : ContinuousOn
      (fun r : ℝ => r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)) (Ioi 0) := by
    exact ((continuousOn_id.mul hFc).mul hwc).mul
      (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const (ε ^ 2))).continuousOn
  refine Integrable.mono' hmajor (hcont.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_))
  have hr : 0 < r := hr
  have he : Real.exp (-r ^ 2 / ε ^ 2) = Real.exp (-(1 / ε ^ 2) * r ^ 2) := by
    congr 1
    field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr,
    abs_of_pos (Real.exp_pos _), he]
  calc r * |F r| * |w r| * Real.exp (-(1 / ε ^ 2) * r ^ 2)
      ≤ r * (C * (A / r + r + 1)) * 1 * Real.exp (-(1 / ε ^ 2) * r ^ 2) := by
        gcongr
        · exact hF r hr
        · exact hw r
    _ = C * ((A + r ^ 2 + r) * Real.exp (-(1 / ε ^ 2) * r ^ 2)) := by
        field_simp [ne_of_gt hr]

/-- A full polar heat integral with circle averages bounded by `C(A/r + r + 1)` is at most
`2 C tailK(A) / ε`. -/
theorem abs_polarInt_gauss_le {ε A C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {F w : ℝ → ℝ}
    (hF : ∀ r, 0 < r → |F r| ≤ C * (A / r + r + 1))
    (hw : ∀ r, |w r| ≤ 1) :
    |2 / ε ^ 2 * ∫ r in Ioi (0 : ℝ), r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤
      C * (2 / ε * tailK A) := by
  let W : ℝ → ℝ := fun u => tailW A u
  let v : ℝ := ε⁻¹
  let c : ℝ := 1 / (2 * ε ^ 2)
  have hv1 : 1 ≤ v := by
    exact (one_le_inv₀ hε).2 hε1
  have hv2 : 1 ≤ v ^ 2 := by nlinarith [sq_nonneg (v - 1)]
  have hv3 : v ≤ v ^ 2 := by nlinarith [sq_nonneg (v - 1)]
  have hc : 0 < c := by positivity
  have hbase := integrableOn_gaussW A hc
  have hWint : IntegrableOn (fun r : ℝ => C * W (r / ε)) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' (hbase.const_mul (C * v ^ 2)) ?_ ?_
    · have hcont : Continuous (fun r : ℝ => C * W (r / ε)) := by
        dsimp [W, tailW]
        fun_prop
      exact hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      have hpoly : A + (r / ε) ^ 2 + r / ε ≤ v ^ 2 * (A + r ^ 2 + r) := by
        have hvA := mul_nonneg hA (sub_nonneg.mpr hv2)
        have hvr := mul_nonneg hr.le (sub_nonneg.mpr hv3)
        have hvr2 := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hv2)
        dsimp [v] at *
        rw [div_eq_mul_inv]
        nlinarith
      have hexp : Real.exp (-(r / ε) ^ 2 / 2) = Real.exp (-c * r ^ 2) := by
        congr 1
        dsimp [c]
        field_simp
      have hexp' : Real.exp (-(1 / 2 : ℝ) * (r / ε) ^ 2) = Real.exp (-c * r ^ 2) := by
        have heq : -(1 / 2 : ℝ) * (r / ε) ^ 2 = -(r / ε) ^ 2 / 2 := by ring
        rw [heq, hexp]
      have hW : W (r / ε) =
          (A + (r / ε) ^ 2 + r / ε) * Real.exp (-c * r ^ 2) := by
        simp only [W, tailW]
        rw [hexp']
      rw [hW, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc C * ((A + (r / ε) ^ 2 + r / ε) * Real.exp (-c * r ^ 2))
          = (C * (A + (r / ε) ^ 2 + r / ε)) * Real.exp (-c * r ^ 2) := by ring
        _ ≤ (C * (v ^ 2 * (A + r ^ 2 + r))) * Real.exp (-c * r ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC)
            (Real.exp_pos _).le
        _ = C * v ^ 2 * ((A + r ^ 2 + r) * Real.exp (-c * r ^ 2)) := by ring
  have hbound : ∀ r ∈ Ioi (0 : ℝ),
      ‖r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)‖ ≤ C * W (r / ε) := by
    intro r hr
    have hr : 0 < r := hr
    have hFr := hF r hr
    have hrε : r ≤ r / ε := by
      rw [div_eq_mul_inv]
      have hε0 : 0 ≤ 1 - ε := by linarith
      nlinarith [mul_nonneg hr.le hε0]
    have hsq : r ^ 2 ≤ (r / ε) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrε) (add_nonneg (by positivity : 0 ≤ r / ε) hr.le)]
    have hpoly : A + r ^ 2 + r ≤ A + (r / ε) ^ 2 + r / ε := by nlinarith
    have he : Real.exp (-r ^ 2 / ε ^ 2) =
        Real.exp (-(r / ε) ^ 2 / 2) * Real.exp (-(r / ε) ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have he1 : Real.exp (-(r / ε) ^ 2 / 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
    have hW : W (r / ε) =
        (A + (r / ε) ^ 2 + r / ε) * Real.exp (-(r / ε) ^ 2 / 2) := by
      simp only [W, tailW]
      congr 1
      ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr,
      abs_of_pos (Real.exp_pos _), he]
    calc r * |F r| * |w r| *
          (Real.exp (-(r / ε) ^ 2 / 2) * Real.exp (-(r / ε) ^ 2 / 2))
        ≤ r * (C * (A / r + r + 1)) * 1 *
            (Real.exp (-(r / ε) ^ 2 / 2) * Real.exp (-(r / ε) ^ 2 / 2)) := by
              gcongr
              exact hw r
      _ = C * (A + r ^ 2 + r) *
            (Real.exp (-(r / ε) ^ 2 / 2) * Real.exp (-(r / ε) ^ 2 / 2)) := by
              field_simp [ne_of_gt hr]
      _ ≤ C * (A + (r / ε) ^ 2 + r / ε) * Real.exp (-(r / ε) ^ 2 / 2) := by
            have hE0 : 0 ≤ Real.exp (-(r / ε) ^ 2 / 2) := (Real.exp_pos _).le
            calc C * (A + r ^ 2 + r) *
                  (Real.exp (-(r / ε) ^ 2 / 2) * Real.exp (-(r / ε) ^ 2 / 2))
                ≤ C * (A + r ^ 2 + r) * Real.exp (-(r / ε) ^ 2 / 2) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_of_le_one_right (Real.exp_pos _).le he1)
                    (by positivity)
                _ ≤ C * (A + (r / ε) ^ 2 + r / ε) * Real.exp (-(r / ε) ^ 2 / 2) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hpoly hC) hE0
      _ = C * W (r / ε) := by rw [hW]; ring
  have hint := norm_integral_le_of_norm_le hWint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
  have hsub := integral_comp_mul_left_Ioi W (0 : ℝ) (show 0 < v by positivity)
  have hsub' : ∫ r in Ioi (0 : ℝ), W (r / ε) = ε * tailK A := by
    have hsub'' : ∫ r in Ioi (0 : ℝ), W (v * r) = v⁻¹ • ∫ u in Ioi (v * 0), W u := hsub
    calc ∫ r in Ioi (0 : ℝ), W (r / ε)
        = ∫ r in Ioi (0 : ℝ), W (v * r) := by congr 1; funext r; simp [v, div_eq_mul_inv, mul_comm]
      _ = ε * tailK A := by simpa [W, tailK, v, smul_eq_mul, one_div] using hsub''
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / ε ^ 2), ← Real.norm_eq_abs]
  calc 2 / ε ^ 2 * ‖∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)‖
      ≤ 2 / ε ^ 2 * (C * ∫ r in Ioi 0, W (r / ε)) := by
        have hval : ∫ r in Ioi 0, C * W (r / ε) = C * ∫ r in Ioi 0, W (r / ε) := by
          rw [integral_const_mul]
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = C * (2 / ε * tailK A) := by rw [hsub']; field_simp

/-- A tail profile vanishing through radius `a` gains a Gaussian exponential. The widened heat
scale is only used to express the remaining integral with the reusable full Gaussian bound. -/
theorem abs_polarInt_gauss_tail_le {ε a A C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (ha : 0 < a) (hA : 0 ≤ A) (hC : 0 ≤ C) {F w : ℝ → ℝ}
    (hF : ∀ r, 0 < r → |F r| ≤ C * (A / r + r + 1))
    (hw : ∀ r, |w r| ≤ 1)
    (hw0 : ∀ r, 0 < r → r ≤ a → w r = 0) :
    |2 / ε ^ 2 * ∫ r in Ioi (0 : ℝ), r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤
      4 * Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
        (C * (2 / (2 * ε) * tailK A)) := by
  let w' : ℝ → ℝ := fun r =>
    if a ≤ r then w r * Real.exp (-((3 / 4 : ℝ) * r ^ 2 - a ^ 2 / 2) / ε ^ 2) else 0
  have hε' : 0 < 2 * ε := by positivity
  have hε'1 : 2 * ε ≤ 1 := by linarith
  have hw' : ∀ r, |w' r| ≤ 1 := by
    intro r
    by_cases hr : a ≤ r
    · have hr2 : a ^ 2 ≤ r ^ 2 := by nlinarith [ha.le, hr]
      have harg : 0 ≤ (3 / 4 : ℝ) * r ^ 2 - a ^ 2 / 2 := by nlinarith
      have hexp : Real.exp (-((3 / 4 : ℝ) * r ^ 2 - a ^ 2 / 2) / ε ^ 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr harg) (by positivity))
      dsimp [w']
      rw [if_pos hr, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |w r| * Real.exp (-((3 / 4 : ℝ) * r ^ 2 - a ^ 2 / 2) / ε ^ 2)
          ≤ 1 * 1 := mul_le_mul (hw r) hexp (Real.exp_pos _).le (by norm_num)
        _ = 1 := by ring
    · dsimp [w']
      rw [if_neg hr]
      norm_num
  have hpoint : ∀ r ∈ Ioi (0 : ℝ),
      r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) =
        Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
          (r * F r * w' r * Real.exp (-r ^ 2 / (2 * ε) ^ 2)) := by
    intro r hr
    have hr : 0 < r := hr
    by_cases hle : a ≤ r
    · have hres : Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
          Real.exp (-((3 / 4 : ℝ) * r ^ 2 - a ^ 2 / 2) / ε ^ 2) *
          Real.exp (-r ^ 2 / (2 * ε) ^ 2) = Real.exp (-r ^ 2 / ε ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring
      dsimp [w']
      rw [if_pos hle, ← hres]
      ring
    · have hrlt : r < a := lt_of_not_ge hle
      have hwzero := hw0 r hr (le_of_lt hrlt)
      simp [w', hle, hwzero]
  have hInt := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpoint
  have hInt' : ∫ r in Ioi (0 : ℝ), r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) =
      Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
        ∫ r in Ioi (0 : ℝ), r * F r * w' r * Real.exp (-r ^ 2 / (2 * ε) ^ 2) := by
    rw [hInt, integral_const_mul]
  have hscale := abs_polarInt_gauss_le (ε := 2 * ε) hε' hε'1 hA hC hF hw'
  have hformula : 2 / ε ^ 2 *
      ∫ r in Ioi (0 : ℝ), r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) =
      4 * Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
        (2 / (2 * ε) ^ 2 *
          ∫ r in Ioi (0 : ℝ), r * F r * w' r * Real.exp (-r ^ 2 / (2 * ε) ^ 2)) := by
    rw [hInt']
    field_simp
    ring
  rw [hformula, abs_mul, abs_of_pos (by positivity :
    0 < 4 * Real.exp (-a ^ 2 / (2 * ε ^ 2)))]
  calc 4 * Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
        |2 / (2 * ε) ^ 2 *
          ∫ r in Ioi (0 : ℝ), r * F r * w' r * Real.exp (-r ^ 2 / (2 * ε) ^ 2)|
      ≤ 4 * Real.exp (-a ^ 2 / (2 * ε ^ 2)) *
        (C * (2 / (2 * ε) * tailK A)) := by
          exact mul_le_mul_of_nonneg_left hscale (by positivity)

/-- Two jointly continuous versions of circle averages agree simultaneously at every positive
radius and center, almost surely. -/
theorem ae_circleAverageVersions_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistC)
    (H H' : ℝ → ℂ → Ω → ℝ)
    (hH : LQGMetric.DFGPS.IsCircleAvgVersion h P H)
    (hH' : LQGMetric.DFGPS.IsCircleAvgVersion h P H') :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : ℂ, H r z ω = H' r z ω := by
  let S : Set (ℝ × ℂ) := Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have hD : ∀ᵐ ω ∂P, ∀ p ∈ D,
      H p.val.1 p.val.2 ω = H' p.val.1 p.val.2 ω := by
    refine (ae_ball_iff hDc).2 fun p hp => ?_
    have hr : 0 < p.val.1 := (mem_prod.mp p.property).1
    filter_upwards [hH.ae_eq p.val.1 hr p.val.2,
      hH'.ae_eq p.val.1 hr p.val.2] with ω h1 h2
    rw [h1, h2]
  filter_upwards [hD] with ω hω
  have hEqOn : EqOn (S.domRestrict (fun p : ℝ × ℂ => H p.1 p.2 ω))
      (S.domRestrict (fun p => H' p.1 p.2 ω)) D := by
    intro p hp
    exact hω p hp
  have hEq := Continuous.ext_on hDd
      (continuousOn_iff_continuous_domRestrict.1 (hH.cont ω))
      (continuousOn_iff_continuous_domRestrict.1 (hH'.cont ω)) hEqOn
  intro r hr z
  exact congrFun hEq ⟨(r, z), ⟨hr, mem_univ _⟩⟩

/-- The heat radial formula can be used with any chosen continuous circle-average version. -/
theorem ae_heatMollify_eq_polarInt_forVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistC)
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P)
    (H : ℝ → ℂ → Ω → ℝ)
    (hH : LQGMetric.DFGPS.IsCircleAvgVersion h P H) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ z : ℂ,
      LQGMetric.heatMollify δ (h ω) z =
        polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := by
  obtain ⟨H₀, hH₀, hHeat⟩ := ae_heatMollify_eq_radialIntegral P h hh
  filter_upwards [hHeat, ae_circleAverageVersions_eq P h H₀ H hH₀ hH] with ω hHeat hEq
  intro δ hδ z
  have hInt : ∫ r in Ioi (0 : ℝ), r * H₀ r z ω * Real.exp (-r ^ 2 / δ ^ 2) =
      ∫ r in Ioi (0 : ℝ), r * H r z ω * Real.exp (-r ^ 2 / δ ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr' : 0 < r := hr
    change r * H₀ r z ω * Real.exp (-r ^ 2 / δ ^ 2) =
      r * H r z ω * Real.exp (-r ^ 2 / δ ^ 2)
    rw [hEq r hr' z]
  rw [hHeat δ hδ z, hInt]
  simp [polarInt]

/-- Uniform cutoff radii `δ L`, for every `L ≥ log δ⁻¹`, approximate the heat field at a
Gaussian rate in `log δ⁻¹`. The proved rate is `C_K exp(-(log δ⁻¹)^2/16)` for
`log δ⁻¹ ≥ 16`. -/
theorem ae_uniformLocalizedHeatField_error_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistC)
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGMetric.DFGPS.IsCircleAvgVersion h P H ∧
      ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
        ∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1,
          16 ≤ Real.log δ⁻¹ → ∀ L : ℝ, Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
            |uniformLocalizedHeatField δ L hδ (h ω) z - LQGMetric.heatMollify δ (h ω) z| ≤
              C * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) := by
  obtain ⟨H, hH, hPol⟩ := ae_plMollify_eq_polarInt_allExponent P h hh
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨A, hA, hAb⟩ := LQGMetric.DFGPS.lem2_2 hh.1 hH R
  have hGrow := hAb (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hHeat := ae_heatMollify_eq_polarInt_forVersion P h hh H hH
  refine ⟨H, hH, ?_⟩
  filter_upwards [hPol, hHeat, hGrow] with ω hPolω hHeatω hGrowω
  obtain ⟨C₀, hC₀⟩ := hGrowω
  let C : ℝ := |C₀|
  have hC : 0 ≤ C := abs_nonneg C₀
  have hKtail : 0 ≤ tailK A := by
    unfold tailK
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    simp [tailW]
    positivity
  refine ⟨16 * C * tailK A, by positivity, ?_⟩
  intro δ hδ hℓ L hL z hz
  let ℓ : ℝ := Real.log δ⁻¹
  have hℓ' : 16 ≤ ℓ := hℓ
  have hℓ0 : 0 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓ'
  have hL' : 0 < L := lt_of_lt_of_le hℓpos hL
  have hδInv : Real.exp ℓ = δ⁻¹ := by
    dsimp [ℓ]
    exact Real.exp_log (inv_pos.mpr hδ.1)
  have hExp16 : 17 ≤ Real.exp 16 := by
    have := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hInv17 : 17 ≤ δ⁻¹ := by
    rw [← hδInv]
    exact hExp16.trans (Real.exp_le_exp.mpr hℓ')
  have hδhalf : δ ≤ 1 / 2 := by
    have hInv2 : 2 ≤ 1 / δ := by
      have hInv2' : 2 ≤ δ⁻¹ := by linarith
      simpa [one_div] using hInv2'
    have hmul : 2 * δ ≤ 1 := (le_div_iff₀ hδ.1).1 hInv2
    linarith
  let q : ℝ := uniformLocalizationExponent δ L
  have hrad : plRad q δ = δ * L :=
    plRad_uniform_eq δ L (by linarith [hℓ']) hL
  have hlog : 1 < Real.log δ⁻¹ := by dsimp [ℓ] at hℓ'; linarith
  have hLoc : plZ q δ hδ * uniformLocalizedHeatField δ L hδ (h ω) z =
      polarInt (plProf q) (fun r z => H r z ω) (δ, z) := by
    simpa [uniformLocalizedHeatField, q] using hPolω δ hδ hlog z q
  have hHeat' : LQGMetric.heatMollify δ (h ω) z =
      polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := hHeatω δ hδ.1 z
  have hF : ∀ r : ℝ, 0 < r → |H r z ω| ≤ C * (A / r + r + 1) := by
    intro r hr
    exact abs_le_of_lem2_2 hA.le hr (hC₀ r hr z (hR hz))
  have hprof : ∀ r : ℝ, |plProf q δ r| ≤ 1 := fun r => abs_plProf_le q δ r
  have htail : ∀ r : ℝ, |1 - plProf q δ r| ≤ 1 := by
    intro r
    have hp := plProf_mem_Icc q δ r
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2]
  let w : ℝ → ℝ → ℝ := fun _ r => 1 - plProf q δ r
  have hzero : ∀ r : ℝ, 0 < r → r ≤ δ * L / 2 → w δ r = 0 := by
    intro r hr hra
    have hn : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hrad' : r ≤ plRad q δ / 2 := by rw [hrad]; linarith
    have hp : plProf q δ r = 1 := by
      rw [plProf_eq q δ hδ]
      exact plBump_eq_one q δ hδ (by rw [hn]; exact hrad')
    simp [w, hp]
  have hTailExp : Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) =
      Real.exp (-L ^ 2 / 8) := by
    congr 1
    field_simp [ne_of_gt hδ.1]
    ring
  have ha : 0 < δ * L / 2 := by exact div_pos (mul_pos hδ.1 hL') (by norm_num)
  have hTail₀ := abs_polarInt_gauss_tail_le hδ.1 hδhalf ha hA.le hC hF htail
      (fun r hr hra => hzero r hr hra)
  have hTailRaw : |polarInt w (fun r z => H r z ω) (δ, z)| ≤
      4 * Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) *
        (C * (2 / (2 * δ) * tailK A)) := by
    simpa [polarInt, w] using hTail₀
  have hTail : |polarInt w (fun r z => H r z ω) (δ, z)| ≤
      4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK A)) := by
    calc |polarInt w (fun r z => H r z ω) (δ, z)|
        ≤ 4 * Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) *
            (C * (2 / (2 * δ) * tailK A)) := hTailRaw
      _ = 4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK A)) := by
        rw [hTailExp]
        congr 2 <;> ring
  have hI : |polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z)| ≤
      C * (2 / δ * tailK A) := by
    have hI₀ := abs_polarInt_gauss_le (ε := δ) (A := A) (C := C)
      hδ.1 hδ.2.le hA.le hC (F := fun r => H r z ω) (w := fun _ => 1) hF
      (fun _ => by norm_num)
    simpa [polarInt] using hI₀
  have hZtail₀ := one_sub_plZ_le q δ hδ
  have hradDiv : plRad q δ ^ 2 / (8 * δ ^ 2) = L ^ 2 / 8 := by
    rw [hrad]
    field_simp [ne_of_gt hδ.1]
  have hZtail : 1 - plZ q δ hδ ≤ 2 * Real.exp (-L ^ 2 / 8) := by
    rw [hradDiv] at hZtail₀
    convert hZtail₀ using 1 <;> congr 1 <;> ring
  have hExpTail : Real.exp (-L ^ 2 / 8) ≤ Real.exp (-8) := by
    apply Real.exp_le_exp.mpr
    have hL16 : 16 ≤ L := hℓ'.trans hL
    nlinarith [sq_nonneg (L - 16)]
  have hExpNeg : Real.exp (-8) ≤ 1 / 9 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (8 : ℝ))).2
    have := Real.add_one_le_exp (8 : ℝ)
    nlinarith
  have hZlow : 1 / 2 ≤ plZ q δ hδ := by
    have hmass := hZtail.trans (mul_le_mul_of_nonneg_left
      (hExpTail.trans hExpNeg) (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hZpos : 0 < plZ q δ hδ := plZ_pos q δ hδ
  have hZinv : (plZ q δ hδ)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hZpos]
    linarith
  have hZnonneg : 0 ≤ 1 - plZ q δ hδ := by
    linarith [plZ_le_one q δ hδ]
  have hZabs : |1 - plZ q δ hδ| ≤ 2 * Real.exp (-L ^ 2 / 8) := by
    rw [abs_of_nonneg hZnonneg]
    exact hZtail
  have hcontF : ContinuousOn (fun r : ℝ => H r z ω) (Ioi (0 : ℝ)) :=
    (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hcontProf : ContinuousOn (fun r : ℝ => plProf q δ r) (Ioi (0 : ℝ)) := by
    have hc := (contDiff_plBump q δ hδ).continuous.comp Complex.continuous_ofReal
    have heq : (fun r : ℝ => plProf q δ r) = fun r : ℝ => plBump q δ hδ (r : ℂ) := by
      funext r
      exact plProf_eq q δ hδ r
    rw [heq]
    exact hc.continuousOn
  have hcontTail : ContinuousOn (fun r : ℝ => w δ r) (Ioi (0 : ℝ)) := by
    dsimp [w]
    exact continuousOn_const.sub hcontProf
  have hIntProf := integrableOn_polarIntegrand_gauss hδ.1 hA.le hC hF hcontF hprof hcontProf
  have hIntTail := integrableOn_polarIntegrand_gauss hδ.1 hA.le hC hF hcontF
      (fun r => htail r) hcontTail
  have hsum : polarInt (plProf q) (fun r z => H r z ω) (δ, z) +
      polarInt w (fun r z => H r z ω) (δ, z) =
      polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := by
    simp only [polarInt]
    rw [← mul_add, ← integral_add hIntProf hIntTail]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [w]
    ring
  let Z : ℝ := plZ q δ hδ
  let N : ℝ := polarInt (plProf q) (fun r z => H r z ω) (δ, z)
  let T : ℝ := polarInt w (fun r z => H r z ω) (δ, z)
  let I : ℝ := polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z)
  have hNI : N - I = -T := by change N + T = I at hsum; linarith
  have hLocEq : uniformLocalizedHeatField δ L hδ (h ω) z = Z⁻¹ * N := by
    have hLocMul : Z * uniformLocalizedHeatField δ L hδ (h ω) z = N := by
      simpa [Z, N] using hLoc
    calc uniformLocalizedHeatField δ L hδ (h ω) z =
          uniformLocalizedHeatField δ L hδ (h ω) z * (Z * Z⁻¹) := by
            rw [mul_inv_cancel₀ hZpos.ne']
            ring
      _ = Z⁻¹ * (Z * uniformLocalizedHeatField δ L hδ (h ω) z) := by ring
      _ = Z⁻¹ * N := by rw [hLocMul]
  have hErrorDecomp : uniformLocalizedHeatField δ L hδ (h ω) z -
      LQGMetric.heatMollify δ (h ω) z = Z⁻¹ * (-T + (1 - Z) * I) := by
    rw [hLocEq, hHeat']
    change Z⁻¹ * N - I = Z⁻¹ * (-T + (1 - Z) * I)
    have hZZ : Z⁻¹ * Z = 1 := inv_mul_cancel₀ hZpos.ne'
    calc Z⁻¹ * N - I = Z⁻¹ * (N - Z * I) := by
          rw [mul_sub, ← mul_assoc, hZZ]
          ring
      _ = Z⁻¹ * (N - I + (1 - Z) * I) := by congr 1 <;> ring
      _ = Z⁻¹ * (-T + (1 - Z) * I) := by rw [hNI]
  have hErrAbs : |uniformLocalizedHeatField δ L hδ (h ω) z -
      LQGMetric.heatMollify δ (h ω) z| ≤
      2 * (|T| + |1 - Z| * |I|) := by
    rw [hErrorDecomp, abs_mul, abs_of_nonneg (inv_nonneg.mpr hZpos.le)]
    calc Z⁻¹ * |-T + (1 - Z) * I|
        ≤ 2 * (|-T| + |(1 - Z) * I|) :=
          mul_le_mul hZinv (abs_add_le _ _) (abs_nonneg _) (by norm_num)
      _ = 2 * (|T| + |1 - Z| * |I|) := by rw [abs_neg, abs_mul]
  have hB : 0 ≤ C * (2 / δ * tailK A) :=
    mul_nonneg hC (mul_nonneg (div_nonneg (by norm_num) hδ.1.le) hKtail)
  have hTbound : |T| ≤ 2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK A)) := by
    dsimp [T] at hTail ⊢
    have heq : 4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK A)) =
        2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK A)) := by ring
    rw [heq] at hTail
    exact hTail
  have hIbound : |I| ≤ C * (2 / δ * tailK A) := by simpa [I] using hI
  have hErrBound : |uniformLocalizedHeatField δ L hδ (h ω) z -
      LQGMetric.heatMollify δ (h ω) z| ≤
      8 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK A)) := by
    calc |uniformLocalizedHeatField δ L hδ (h ω) z -
          LQGMetric.heatMollify δ (h ω) z|
        ≤ 2 * (|T| + |1 - Z| * |I|) := hErrAbs
      _ ≤ 2 * (2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK A)) +
            (2 * Real.exp (-L ^ 2 / 8)) * (C * (2 / δ * tailK A))) := by
          gcongr
      _ = 8 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK A)) := by ring
  have hδinvEq : 1 / δ = Real.exp ℓ := by
    simpa [one_div] using hδInv.symm
  have hErrBound' : |uniformLocalizedHeatField δ L hδ (h ω) z -
      LQGMetric.heatMollify δ (h ω) z| ≤
      16 * C * tailK A * Real.exp (ℓ - L ^ 2 / 8) := by
    have hErrBound₁ := hErrBound
    rw [show 2 / δ = 2 * (1 / δ) by ring, hδinvEq] at hErrBound₁
    have hEq : 8 * Real.exp (-L ^ 2 / 8) * (C * (2 * Real.exp ℓ * tailK A)) =
        16 * C * tailK A * Real.exp (ℓ - L ^ 2 / 8) := by
      calc 8 * Real.exp (-L ^ 2 / 8) * (C * (2 * Real.exp ℓ * tailK A))
          = 16 * C * tailK A * (Real.exp ℓ * Real.exp (-L ^ 2 / 8)) := by ring
        _ = 16 * C * tailK A * Real.exp (ℓ - L ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          ring
    rw [hEq] at hErrBound₁
    exact hErrBound₁
  have hLsq : ℓ ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ hℓ0 hL'.le).2 (by simpa [ℓ] using hL)
  have hExpArg : ℓ - L ^ 2 / 8 ≤ -(ℓ ^ 2) / 16 := by
    calc ℓ - L ^ 2 / 8 ≤ ℓ - ℓ ^ 2 / 8 := by nlinarith only [hLsq]
      _ ≤ -(ℓ ^ 2) / 16 := by
        have hm : 0 ≤ (ℓ - 16) * ℓ :=
          mul_nonneg (by linarith [hℓ']) hℓ0
        nlinarith only [hm]
  have hExpCmp : Real.exp (ℓ - L ^ 2 / 8) ≤ Real.exp (-(ℓ ^ 2) / 16) :=
    Real.exp_le_exp.mpr hExpArg
  have hFactor : 0 ≤ 16 * C * tailK A := by positivity
  calc |uniformLocalizedHeatField δ L hδ (h ω) z -
        LQGMetric.heatMollify δ (h ω) z|
      ≤ 16 * C * tailK A * Real.exp (ℓ - L ^ 2 / 8) := hErrBound'
    _ ≤ 16 * C * tailK A * Real.exp (-(ℓ ^ 2) / 16) :=
      mul_le_mul_of_nonneg_left hExpCmp hFactor


end SupercriticalLFPPAS.Field
