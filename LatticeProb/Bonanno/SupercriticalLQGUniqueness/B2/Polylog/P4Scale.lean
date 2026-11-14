/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Scale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Translate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6

 





















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 
theorem acrossDist_comp_mul {m M : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ∞)
    (T : ℂ ≃ₜ ℂ) (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (A A' : EuclideanAnnulus)
    (hin : T '' A.innerBoundary = A'.innerBoundary)
    (hout : T '' A.outerBoundary = A'.outerBoundary) :
    acrossDist m A = k * acrossDist M A' := by
  unfold acrossDist
  rw [← hin, ← hout]
  simp only [hm, ENNReal.mul_iInf_of_ne hk0 hkt, iInf_image]

lemma annAt_congr {z z' : ℂ} {a a' b b' : ℝ} (hz : z = z') (ha : a = a') (hb : b = b')
    (h₁ : 0 < a) (h₁₂ : a < b) (h₁' : 0 < a') (h₁₂' : a' < b') :
    annAt z a b h₁ h₁₂ = annAt z' a' b' h₁' h₁₂' := by
  subst hz ha hb; rfl

lemma annAt_dilate (r : Set.Ioi (0 : ℝ)) (a b : ℝ) (h₁ : 0 < a) (h₁₂ : a < b) :
    (annAt 0 a b h₁ h₁₂).dilate r r.2 =
      annAt 0 (r * a) (r * b) (mul_pos r.2 h₁) (mul_lt_mul_of_pos_left h₁₂ r.2) := by
  apply Subtype.ext
  show ((r : ℝ) • (0 : ℂ), (r : ℝ) * a, (r : ℝ) * b) = ((0 : ℂ), (r : ℝ) * a, (r : ℝ) * b)
  rw [smul_zero]

 
lemma lfppMetric_scale (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {r : ℝ} (hr : 0 < r)
    (k₀ : ℝ) (hφ : ∀ u, φ' u = φ ((r : ℂ) * u) + k₀) (u v : ℂ) :
    Median.lfppMetric ξ a' φ' (u, v) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) / ((a' : ℝ) * r)) *
        Median.lfppMetric ξ a φ (dilateHomeo hr u, dilateHomeo hr v) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [lfppMetric_affine ξ a a' (b := 0) (c := (r : ℂ)) hr0 k₀ (fun x => by rw [zero_add]; exact hφ x)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, zero_add, zero_add, dilateHomeo_apply,
    dilateHomeo_apply, Complex.real_smul, Complex.real_smul]

 
theorem unitScale_across_eq (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    (r : Set.Ioi (0 : ℝ)) (k₀ : ℝ) (hφ : ∀ u, φ' u = φ ((r : ℂ) * u) + k₀) :
    acrossDist (Median.lfppMetric ξ a' φ') (annAt 0 1 2 one_pos one_lt_two) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) / ((a' : ℝ) * r)) *
        acrossDist (Median.lfppMetric ξ a φ) (annAt 0 r (2 * r) r.2 (by
          have := r.2; simp only [mem_Ioi] at this; linarith)) := by
  have hr : (0 : ℝ) < r := r.2
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  obtain ⟨-, h2, h3⟩ := image_dilate_annAt hr 0 1 2 one_pos one_lt_two
  refine (acrossDist_comp_mul (by simpa using (by positivity : (0 : ℝ) < a * Real.exp (ξ * k₀) / (a' * r)))
    ENNReal.ofReal_ne_top (dilateHomeo hr) (lfppMetric_scale ξ a a' hr k₀ hφ) _ _ h2 h3).trans ?_
  congr 2
  exact annAt_congr (smul_zero _) (mul_one _) (mul_comm _ _) _ _ _ _

 
theorem unitScale_around_eq (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    (r : Set.Ioi (0 : ℝ)) (k₀ : ℝ) (hφ : ∀ u, φ' u = φ ((r : ℂ) * u) + k₀) :
    aroundDist (Median.lfppMetric ξ a' φ') (annAt 0 2 3 two_pos (by norm_num)) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) / ((a' : ℝ) * r)) *
        aroundDist (Median.lfppMetric ξ a φ) (annAround 0 r) := by
  have hr : (0 : ℝ) < r := r.2
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  obtain ⟨h1, h2, h3⟩ := image_dilate_annAt hr 0 2 3 two_pos (by norm_num)
  refine (aroundDist_comp_mul (by simpa using (by positivity : (0 : ℝ) < a * Real.exp (ξ * k₀) / (a' * r)))
    ENNReal.ofReal_ne_top (dilateHomeo hr) (lfppMetric_scale ξ a a' hr k₀ hφ) _ _ h1 h2 h3).trans ?_
  congr 2
  exact annAt_congr (smul_zero _) (mul_comm _ _) (mul_comm _ _) _ _ _ _

 

 

def gScale (r : ℝ) (g : DistC) : DistC := addConst (affineComp r 0 g) (-circleAvg (affineComp r 0 g) 1 0)

theorem isWholePlaneGFF_gScale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    IsWholePlaneGFF (fun ω => gScale r (h ω)) P :=
  (hh.affineComp hr 0).addConst
    ((measurable_circleAvg_left 1 0).comp (hh.affineComp hr 0).measurable).neg

theorem map_gScale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => gScale r (h ω)) = P.map h :=
  map_affine_normalized_of_candidate hh hr 0

 


theorem ae_heatMollify_gScale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (ε : Set.Ioi (0 : ℝ)) (r : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h ε X) :
    ∀ᵐ ω ∂P, ∀ u : ℂ, heatMollify ((ε : ℝ) / r) (gScale r (h ω)) u =
      X ω ((r : ℂ) * u) + -circleAvg (affineComp r 0 (h ω)) 1 0 := by
  have hr : (0 : ℝ) < r := r.2
  have hε : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hεr : (ε : ℝ) / r ≠ 0 := div_ne_zero hε hr.ne'
  filter_upwards [DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh ε X hX,
    DFGPS.ae_heatMollify_affineComp hh.1 hε hr,
    (hh.1.affineComp hr 0).ae_tendstoLocallyUniformly_heatMollify ((ε : ℝ) / r) hεr] with
    ω hX' hA hconv u
  rw [gScale, DFGPS.heatMollify_addConst_of_tendsto hεr
    ((tendstoLocallyUniformlyOn_univ.2 hconv.1).tendsto_at (mem_univ u)), hA u, hX' _]

 


theorem measure_le_of_scaled_version {μ : Measure DistC} {r : ℝ}
    (hmeas : AEMeasurable (gScale r) μ) (hlaw : μ.map (gScale r) = μ) (δ : ℝ)
    (Y X : DistC → C(ℂ, ℝ)) (hY : ∀ᵐ g ∂μ, ∀ u, Y g u = heatMollify δ (gScale r g) u)
    (hX : ∀ᵐ g ∂μ, ∀ u, X g u = heatMollify δ g u) (Ψ : C(ℂ, ℝ) → Prop) :
    μ {g | Ψ (Y g)} ≤ μ {g | Ψ (X g)} := by
  set B : Set DistC := {g' | ∃ φ : C(ℂ, ℝ), (∀ u, φ u = heatMollify δ g' u) ∧ Ψ φ}
  calc μ {g | Ψ (Y g)} ≤ μ (gScale r ⁻¹' B) := by
        refine measure_mono_ae ?_
        filter_upwards [hY] with g hg hΨ
        exact ⟨Y g, hg, hΨ⟩
    _ ≤ (μ.map (gScale r)) B := Measure.le_map_apply hmeas B
    _ = μ B := by rw [hlaw]
    _ ≤ μ {g | Ψ (X g)} := by
        refine measure_mono_ae ?_
        filter_upwards [hX] with g hg hB
        obtain ⟨φ, hφ, hΨ⟩ := hB
        have : φ = X g := ContinuousMap.ext fun u => by rw [hφ u, hg u]
        rw [← this]
        exact hΨ

end SupercriticalLQGUniqueness.B2.Polylog
