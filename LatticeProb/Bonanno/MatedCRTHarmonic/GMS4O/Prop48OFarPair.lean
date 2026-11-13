/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OFarPair at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_eq_lintegral_rpow_enorm_toReal takes the measurability argument; the non-integrable case (conditional expectation 0) is treated first. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48FarA3
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CircleConditioning
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ExteriorLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OKernelGeneric

/-!
# The far-pair covariance of [18] Proposition 4.8 with a shared IG phase

[18] (4.35)–(4.37) bounds the covariance of the
centred localized observables at two distant centres by Lemma A.3. On the frozen coupling the
observables also read the shared IG phase `U`. Per the conditional mean conditions on the
triple `((h_r(z), g_r(z)), U)`.

`p48o_far_pair_frozen_A3` is the whole-plane statement: for independent normalized whole-plane GFFs
`h, g`, a phase `U` independent of `(h, g)`, and Borel local factors of the local field observation
and the phase, the covariance of `X_z − E[X_z | T_z]` and `X_w − E[X_w | T_w]` obeys the integrated
two-field A.3 bound. The proof freezes the phase (`p48o_condValueG_frozen`), applies the
`prop48_twoField_far_pair_of_lemmaA3` at every frozen value, and integrates over the phase with
Hölder's inequality, so only **unconditional** moments enter.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter LQGMetric LQGMetric.Blueprint
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4O

/-! ### Moment helpers -/

section Moments

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Jensen for concave powers on a probability space: `∫ φ^θ ≤ (∫ φ)^θ` for `θ ∈ (0, 1]`. -/
lemma p48o_lintegral_rpow_le_rpow_lintegral [IsProbabilityMeasure μ] {φ : α → ℝ≥0∞}
    (hφ : AEMeasurable φ μ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∫⁻ a, φ a ^ θ ∂μ ≤ (∫⁻ a, φ a ∂μ) ^ θ := by
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · subst h1; simp
  · have hpq : (1 / θ).HolderConjugate (1 / (1 - θ)) := by
      rw [Real.holderConjugate_iff]
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hθ0]; linarith
      · field_simp
        ring
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hφ.pow_const θ)
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
    refine h.trans (le_of_eq ?_)
    have e : ∫⁻ a, (φ a ^ θ) ^ (1 / θ) ∂μ = ∫⁻ a, φ a ∂μ := by
      refine lintegral_congr fun a => ?_
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one]
    rw [e, one_div_one_div]

/-- Lower moments decrease with the exponent on a probability space. -/
lemma p48o_lintegral_abs_rpow_le [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) {p p₀ : ℝ} (hp : 0 < p) (hpp₀ : p ≤ p₀) :
    ∫⁻ a, ENNReal.ofReal |f a| ^ p ∂μ ≤ (∫⁻ a, ENNReal.ofReal |f a| ^ p₀ ∂μ) ^ (p / p₀) := by
  have hp₀ : 0 < p₀ := hp.trans_le hpp₀
  have hφ : AEMeasurable (fun a => ENNReal.ofReal |f a| ^ p₀) μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hf.abs).pow_const p₀
  have h := p48o_lintegral_rpow_le_rpow_lintegral hφ (θ := p / p₀) (div_pos hp hp₀)
    ((div_le_one hp₀).2 hpp₀)
  refine le_of_eq_of_le ?_ h
  refine lintegral_congr fun a => ?_
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- A finite `p`-th lower moment with `p ≥ 1` gives integrability on a probability space. -/
lemma p48o_integrable_of_lintegral_rpow [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p)
    (hfp : ∫⁻ a, ENNReal.ofReal |f a| ^ p ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  rw [HasFiniteIntegral]
  have h := p48o_lintegral_abs_rpow_le hf.aemeasurable (p := 1) (p₀ := p) one_pos hp
  simp only [ENNReal.rpow_one] at h
  have e : ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal |f a| ∂μ :=
    lintegral_congr fun a => Real.enorm_eq_ofReal_abs (f a)
  rw [e]
  exact lt_of_le_of_lt h (ENNReal.rpow_lt_top_of_nonneg (by positivity) hfp)

/-- Hölder integrability of a product from finite conjugate lower moments. -/
lemma p48o_integrable_mul_of_lintegral {f g : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hfp : ∫⁻ a, ENNReal.ofReal |f a| ^ p ∂μ ≠ ⊤)
    (hgq : ∫⁻ a, ENNReal.ofReal |g a| ^ q ∂μ ≠ ⊤) :
    Integrable (fun a => f a * g a) μ := by
  refine ⟨hf.mul hg, ?_⟩
  rw [HasFiniteIntegral]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable.abs)
    (ENNReal.measurable_ofReal.comp_aemeasurable hg.aemeasurable.abs)
  have e : ∫⁻ a, ‖f a * g a‖ₑ ∂μ =
      ∫⁻ a, ENNReal.ofReal |f a| * ENNReal.ofReal |g a| ∂μ := by
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  rw [e]
  refine lt_of_le_of_lt h (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hpq.pos; positivity) hfp
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hpq.symm.pos; positivity) hgq

/-- Conditional expectation does not increase lower moments of order `p ≥ 1`. -/
lemma p48o_lintegral_abs_rpow_condExp_le [IsProbabilityMeasure μ] {m : MeasurableSpace α}
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ a, ENNReal.ofReal |μ[f | m] a| ^ p ∂μ ≤ ∫⁻ a, ENNReal.ofReal |f a| ^ p ∂μ := by
  have hp0 : 0 < p := one_pos.trans_le hp
  by_cases hfi : Integrable f μ
  swap
  · rw [condExp_of_not_integrable hfi]
    simp [ENNReal.zero_rpow_of_pos hp0]
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hle := eLpNorm_condExp_le_eLpNorm (m := m) (μ := μ) f hpE
  have hne0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top
      integrable_condExp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hfi.1,
    ENNReal.toReal_ofReal hp0.le] at hle
  have hle' := ENNReal.rpow_le_rpow hle hp0.le
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
    ENNReal.rpow_one] at hle'
  have e1 : ∫⁻ a, ‖μ[f | m] a‖ₑ ^ p ∂μ = ∫⁻ a, ENNReal.ofReal |μ[f | m] a| ^ p ∂μ :=
    lintegral_congr fun a => by rw [Real.enorm_eq_ofReal_abs]
  have e2 : ∫⁻ a, ‖f a‖ₑ ^ p ∂μ = ∫⁻ a, ENNReal.ofReal |f a| ^ p ∂μ :=
    lintegral_congr fun a => by rw [Real.enorm_eq_ofReal_abs]
  rw [e1, e2] at hle'
  exact hle'

/-- Convexity bound for differences: `∫ |f − g|^q ≤ 2^{q−1} (∫ |f|^q + ∫ |g|^q)`. -/
lemma p48o_lintegral_abs_sub_rpow_le {f g : α → ℝ} (hf : AEMeasurable f μ) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ a, ENNReal.ofReal |f a - g a| ^ q ∂μ ≤
      (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ a, ENNReal.ofReal |f a| ^ q ∂μ +
        ∫⁻ a, ENNReal.ofReal |g a| ^ q ∂μ) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  calc ∫⁻ a, ENNReal.ofReal |f a - g a| ^ q ∂μ
      ≤ ∫⁻ a, (2 : ℝ≥0∞) ^ (q - 1) *
          (ENNReal.ofReal |f a| ^ q + ENNReal.ofReal |g a| ^ q) ∂μ := by
        refine lintegral_mono fun a => ?_
        have h1 : ENNReal.ofReal |f a - g a| ≤ ENNReal.ofReal |f a| + ENNReal.ofReal |g a| := by
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
        exact (ENNReal.rpow_le_rpow h1 hq0).trans (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq)
    _ = (2 : ℝ≥0∞) ^ (q - 1) * ∫⁻ a, (ENNReal.ofReal |f a| ^ q + ENNReal.ofReal |g a| ^ q) ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
    _ = (2 : ℝ≥0∞) ^ (q - 1) * (∫⁻ a, ENNReal.ofReal |f a| ^ q ∂μ +
          ∫⁻ a, ENNReal.ofReal |g a| ^ q ∂μ) := by
        have hm : AEMeasurable (fun a => ENNReal.ofReal |f a| ^ q) μ :=
          (ENNReal.measurable_ofReal.comp_aemeasurable hf.abs).pow_const q
        rw [lintegral_add_left' hm]

end Moments

/-! ### The whole-plane far pair with a frozen phase -/

/-- The local field observation of [18] (4.22) as a function of the pair of fields. -/
def p48oLocObsOf (ℓ r : ℝ) (z : ℂ) (v : DistC × DistC) :
    (DistOn (ballO z ℓ) × DistOn (ballO z ℓ)) × (ℝ × ℝ) :=
  ((restrictTo (ballO z ℓ) v.1, restrictTo (ballO z ℓ) v.2), (circleAvg v.1 r z, circleAvg v.2 r z))

lemma measurable_p48oLocObsOf (ℓ r : ℝ) (z : ℂ) : Measurable (p48oLocObsOf ℓ r z) :=
  (((measurable_restrictTo (ballO z ℓ)).comp measurable_fst).prodMk
    ((measurable_restrictTo (ballO z ℓ)).comp measurable_snd)).prodMk
    (((measurable_circleAvg_left r z).comp measurable_fst).prodMk
      ((measurable_circleAvg_left r z).comp measurable_snd))

/-- The pair of circle averages as a function of the pair of fields. -/
def p48oAvgOf (r : ℝ) (z : ℂ) (v : DistC × DistC) : ℝ × ℝ :=
  (circleAvg v.1 r z, circleAvg v.2 r z)

lemma measurable_p48oAvgOf (r : ℝ) (z : ℂ) : Measurable (p48oAvgOf r z) :=
  ((measurable_circleAvg_left r z).comp measurable_fst).prodMk
    ((measurable_circleAvg_left r z).comp measurable_snd)

lemma p48o_ballO_subset_compl_ball_of_far {r δ : ℝ} (hδ1 : δ ≤ 1) (hr : 0 < r) {z w : ℂ}
    (hfar : 2 * r < dist z w) :
    (ballO w (r * δ) : Set ℂ) ⊆ (Metric.ball z r)ᶜ := by
  intro y hy
  simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt]
  have hy' : dist y w < r * δ := hy
  have hrδ : r * δ ≤ r := by nlinarith
  have := dist_triangle z y w
  rw [dist_comm z y] at this
  linarith [dist_comm y w]

lemma p48o_sphere_subset_compl_ball_of_far {r : ℝ} (hr : 0 < r) {z w : ℂ}
    (hfar : 2 * r < dist z w) :
    Metric.sphere w |r| ⊆ (Metric.ball z r)ᶜ := by
  intro y hy
  simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt]
  have hy' : dist y w = r := by rw [Metric.mem_sphere] at hy; rw [hy, abs_of_pos hr]
  have := dist_triangle z y w
  rw [dist_comm z y] at this
  linarith [dist_comm y w]

lemma p48o_measurable_localObs {Ω : Type} [MeasurableSpace Ω] {h g : Ω → DistC}
    (hh : Measurable h) (hg : Measurable g) (ℓ r : ℝ) (z : ℂ) :
    Measurable (GMS4.prop48LocalFieldObservation h g ℓ r z) :=
  (measurable_p48oLocObsOf ℓ r z).comp (hh.prodMk hg)

/-- **Two-field A.3 at a fixed phase**, with an arbitrary version `cY` of the circle-average
conditional mean and finite moments as the only analytic premises. -/
lemma p48o_far_pair_A3_fixed
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h g : Ω → DistC} (hh : IsNormalizedWPGFF h P) (hg : IsNormalizedWPGFF g P)
    (hind : IndepFun h g P)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z w : ℂ} (hsmall : r + ‖z‖ < 1)
    (hfar : 2 * r < dist z w)
    {p p₀ s q : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδa : δ ≤ GMSAppA.a3aN p p₀ 2) (hpq : p.HolderConjugate q)
    {fY : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) × (ℝ × ℝ)) → ℝ}
    (hfY : Measurable fY)
    {Zf : ((DistOn (ballO w (r * δ)) × DistOn (ballO w (r * δ))) × (ℝ × ℝ)) → ℝ}
    (hZf : Measurable Zf) {cY : Ω → ℝ}
    (hcY : cY =ᵐ[P] P[fun ω => fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω) |
      MeasurableSpace.comap (GMS4.prop48CircleAverageObservation h g r z) inferInstance])
    (hYp₀ : ∫⁻ ω, ENNReal.ofReal |fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω)| ^ p₀
      ∂P ≠ ⊤)
    (hZq : ∫⁻ ω, ENNReal.ofReal |Zf (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω)| ^ q
      ∂P ≠ ⊤) :
    ENNReal.ofReal |∫ ω, (fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω) - cY ω) *
        Zf (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω) ∂P| ≤
      (ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω)| ^ p
              ∂P +
          ENNReal.ofReal (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal
              |fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω)| ^ p₀ ∂P) ^ (p / p₀)))
          ^ (1 / p) *
      (∫⁻ ω, ENNReal.ofReal |Zf (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω)| ^ q
        ∂P) ^ (1 / q) := by
  set Y : Ω → ℝ := fun ω => fY (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω) with hYdef
  set Z : Ω → ℝ := fun ω => Zf (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω) with hZdef
  have hObsz := p48o_measurable_localObs hh.1.measurable hg.1.measurable (r * δ) r z
  have hObsw := p48o_measurable_localObs hh.1.measurable hg.1.measurable (r * δ) r w
  have hYm : Measurable Y := hfY.comp hObsz
  have hZm : Measurable Z := hZf.comp hObsw
  have hp₀1 : 1 ≤ p₀ := hp.trans hpp₀.le
  have hYi : Integrable Y P := p48o_integrable_of_lintegral_rpow hYm.aestronglyMeasurable hp₀1 hYp₀
  have hYp : ∫⁻ ω, ENNReal.ofReal |Y ω| ^ p ∂P ≠ ⊤ :=
    ((p48o_lintegral_abs_rpow_le hYm.aemeasurable (by linarith) hpp₀.le).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by have := hpq.pos; positivity) hYp₀)).ne
  have hYZi : Integrable (Y * Z) P :=
    p48o_integrable_mul_of_lintegral hYm.aestronglyMeasurable hZm.aestronglyMeasurable hpq hYp hZq
  set cA : Ω → ℝ := P[Y | GMSAppA.cSigmaN (GMS4.prop48AffineFieldFamily h g r z)] with hcA
  have hcAp : ∫⁻ ω, ENNReal.ofReal |cA ω| ^ p ∂P ≠ ⊤ :=
    ((p48o_lintegral_abs_rpow_condExp_le hp).trans_lt (lt_top_iff_ne_top.2 hYp)).ne
  have hAZi : Integrable (cA * Z) P :=
    p48o_integrable_mul_of_lintegral integrable_condExp.aestronglyMeasurable
      hZm.aestronglyMeasurable hpq hcAp hZq
  have hZext : StronglyMeasurable[GMS4.prop48ExteriorSigma h g r z] Z :=
    (hZf.comp (GMS4.prop48_localObservation_exterior_measurable h g (r * δ) r r z w
      (p48o_ballO_subset_compl_ball_of_far hδ1 hr hfar)
      (p48o_sphere_subset_compl_ball_of_far hr hfar))).stronglyMeasurable
  have hA3 := GMS4.prop48_twoField_far_pair_of_lemmaA3 hh hg hind hr z hsmall hp hpp₀ hs hδ hδa
    hpq hfY (ae_eq_refl Y) hYp₀ hYi hYZi hAZi hZext
  have hCE := GMS4.prop48_affine_condExp_eq_source_circle_condExp hh hg hr z hYi
  have hcen : (fun ω => (Y ω - cY ω) * Z ω) =ᵐ[P] fun ω => (Y ω - cA ω) * Z ω := by
    filter_upwards [hcY, hCE] with ω h1 h2
    rw [h1, ← h2]
  rw [integral_congr_ae hcen]
  exact hA3

/-- **The far pair with a shared independent phase** . For independent normalized whole-plane
GFFs `h, g`, a phase `U ⟂ (h, g)`, nonnegative Borel factors `f_z, f_w` of the local observation and
The phase, and versions `m_z, m_w` of the conditional means given the triples
`((h_r, g_r), U)`, the centred covariance obeys the integrated two-field A.3 bound, with
**unconditional** moments only. -/
theorem p48o_far_pair_frozen_A3
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h g : Ω → DistC} (hh : IsNormalizedWPGFF h P) (hg : IsNormalizedWPGFF g P)
    (hind : IndepFun h g P) {U : Ω → ℝ} (hU : Measurable U)
    (hindU : IndepFun (fun ω => (h ω, g ω)) U P)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z w : ℂ} (hsmall : r + ‖z‖ < 1)
    (hfar : 2 * r < dist z w)
    {p p₀ s q : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδa : δ ≤ GMSAppA.a3aN p p₀ 2) (hpq : p.HolderConjugate q)
    {fz : ((DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) × (ℝ × ℝ)) × ℝ → ℝ}
    {fw : ((DistOn (ballO w (r * δ)) × DistOn (ballO w (r * δ))) × (ℝ × ℝ)) × ℝ → ℝ}
    (hfz : Measurable fz) (hfw : Measurable fw) (hfz0 : ∀ x, 0 ≤ fz x) (hfw0 : ∀ x, 0 ≤ fw x)
    {mz mw : Ω → ℝ}
    (hmz : mz =ᵐ[P] P[fun ω => fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω) |
      MeasurableSpace.comap (fun ω => (GMS4.prop48CircleAverageObservation h g r z ω, U ω))
        inferInstance])
    (hmw : mw =ᵐ[P] P[fun ω => fw (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω, U ω) |
      MeasurableSpace.comap (fun ω => (GMS4.prop48CircleAverageObservation h g r w ω, U ω))
        inferInstance])
    (hXz : ∫⁻ ω, ENNReal.ofReal
      |fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω)| ^ p₀ ∂P ≠ ⊤)
    (hXw : ∫⁻ ω, ENNReal.ofReal
      |fw (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω, U ω)| ^ q ∂P ≠ ⊤) :
    ENNReal.ofReal |∫ ω,
        (fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω) - mz ω) *
        (fw (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω, U ω) - mw ω) ∂P| ≤
      (ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal
              |fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω)| ^ p ∂P +
          ENNReal.ofReal (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal
              |fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω)| ^ p₀ ∂P)
                ^ (p / p₀))) ^ (1 / p) *
      (∫⁻ ω, ENNReal.ofReal
        |fw (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω, U ω) - mw ω| ^ q ∂P)
          ^ (1 / q) := by
  -- notation
  set V : Ω → DistC × DistC := fun ω => (h ω, g ω) with hVdef
  have hVm : Measurable V := hh.1.measurable.prodMk hg.1.measurable
  set Fz : (DistC × DistC) × ℝ → ℝ := fun x => fz (p48oLocObsOf (r * δ) r z x.1, x.2) with hFzdef
  set Fw : (DistC × DistC) × ℝ → ℝ := fun x => fw (p48oLocObsOf (r * δ) r w x.1, x.2) with hFwdef
  have hFz : Measurable Fz :=
    hfz.comp (((measurable_p48oLocObsOf (r * δ) r z).comp measurable_fst).prodMk measurable_snd)
  have hFw : Measurable Fw :=
    hfw.comp (((measurable_p48oLocObsOf (r * δ) r w).comp measurable_fst).prodMk measurable_snd)
  have hFz0 : ∀ x, 0 ≤ Fz x := fun x => hfz0 _
  have hFw0 : ∀ x, 0 ≤ Fw x := fun x => hfw0 _
  set az : DistC × DistC → ℝ × ℝ := p48oAvgOf r z with hazdef
  set aw : DistC × DistC → ℝ × ℝ := p48oAvgOf r w with hawdef
  have haz : Measurable az := measurable_p48oAvgOf r z
  have haw : Measurable aw := measurable_p48oAvgOf r w
  set Gz : ℝ × (ℝ × ℝ) → ℝ :=
    p48oCondValueG P (fun ω (_ψ : ℝ) => az (V ω)) (fun ω ψ => Fz (V ω, ψ)) with hGzdef
  set Gw : ℝ × (ℝ × ℝ) → ℝ :=
    p48oCondValueG P (fun ω (_ψ : ℝ) => aw (V ω)) (fun ω ψ => Fw (V ω, ψ)) with hGwdef
  have hGz : Measurable Gz := measurable_p48oCondValueG P _ _
  have hGw : Measurable Gw := measurable_p48oCondValueG P _ _
  have hp₀1 : 1 ≤ p₀ := hp.trans hpp₀.le
  have hp0 : 0 < p := one_pos.trans_le hp
  have hq1 : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := one_pos.trans hq1
  -- the two observables
  set Xz : Ω → ℝ := fun ω => Fz (V ω, U ω) with hXzdef
  set Xw : Ω → ℝ := fun ω => Fw (V ω, U ω) with hXwdef
  have hXzm : Measurable Xz := hFz.comp (hVm.prodMk hU)
  have hXwm : Measurable Xw := hFw.comp (hVm.prodMk hU)
  have hXzi : Integrable Xz P := p48o_integrable_of_lintegral_rpow hXzm.aestronglyMeasurable hp₀1 hXz
  have hXwi : Integrable Xw P := p48o_integrable_of_lintegral_rpow hXwm.aestronglyMeasurable
    hq1.le hXw
  -- frozen versions of the conditional means
  have hfrz := p48o_condValueG_frozen hVm hU hindU haz hFz hFz0 hXzi
  have hfrw := p48o_condValueG_frozen hVm hU hindU haw hFw hFw0 hXwi
  have hmz' : mz =ᵐ[P] fun ω => Gz (U ω, az (V ω)) := hmz.trans hfrz.symm
  have hmw' : mw =ᵐ[P] fun ω => Gw (U ω, aw (V ω)) := hmw.trans hfrw.symm
  -- moments of the centred variables
  have hXzp : ∫⁻ ω, ENNReal.ofReal |Xz ω| ^ p ∂P ≠ ⊤ :=
    ((p48o_lintegral_abs_rpow_le hXzm.aemeasurable hp0 hpp₀.le).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hXz)).ne
  have hcz : ∫⁻ ω, ENNReal.ofReal |mz ω| ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal |Xz ω| ^ p ∂P := by
    have e : ∫⁻ ω, ENNReal.ofReal |mz ω| ^ p ∂P = ∫⁻ ω, ENNReal.ofReal
        |(P[fun ω => fz (GMS4.prop48LocalFieldObservation h g (r * δ) r z ω, U ω) |
          MeasurableSpace.comap (fun ω => (GMS4.prop48CircleAverageObservation h g r z ω, U ω))
            inferInstance]) ω| ^ p ∂P :=
      lintegral_congr_ae (by filter_upwards [hmz] with ω hω; rw [hω])
    rw [e]
    exact p48o_lintegral_abs_rpow_condExp_le hp
  have hcw : ∫⁻ ω, ENNReal.ofReal |mw ω| ^ q ∂P ≤ ∫⁻ ω, ENNReal.ofReal |Xw ω| ^ q ∂P := by
    have e : ∫⁻ ω, ENNReal.ofReal |mw ω| ^ q ∂P = ∫⁻ ω, ENNReal.ofReal
        |(P[fun ω => fw (GMS4.prop48LocalFieldObservation h g (r * δ) r w ω, U ω) |
          MeasurableSpace.comap (fun ω => (GMS4.prop48CircleAverageObservation h g r w ω, U ω))
            inferInstance]) ω| ^ q ∂P :=
      lintegral_congr_ae (by filter_upwards [hmw] with ω hω; rw [hω])
    rw [e]
    exact p48o_lintegral_abs_rpow_condExp_le hq1.le
  have hdz : ∫⁻ ω, ENNReal.ofReal |Xz ω - mz ω| ^ p ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (p48o_lintegral_abs_sub_rpow_le hXzm.aemeasurable hp)
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) ?_
    exact ENNReal.add_ne_top.2 ⟨hXzp, ne_top_of_le_ne_top hXzp hcz⟩
  have hdw : ∫⁻ ω, ENNReal.ofReal |Xw ω - mw ω| ^ q ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (p48o_lintegral_abs_sub_rpow_le hXwm.aemeasurable hq1.le)
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top) ?_
    exact ENNReal.add_ne_top.2 ⟨hXw, ne_top_of_le_ne_top hXw hcw⟩
  -- the covariance integrand as a function of `(V, U)`
  set Φ : (DistC × DistC) × ℝ → ℝ := fun x =>
    (Fz x - Gz (x.2, az x.1)) * (Fw x - Gw (x.2, aw x.1)) with hΦdef
  have hΦ : Measurable Φ :=
    (hFz.sub (hGz.comp (measurable_snd.prodMk (haz.comp measurable_fst)))).mul
      (hFw.sub (hGw.comp (measurable_snd.prodMk (haw.comp measurable_fst))))
  have hcov : (fun ω => (Xz ω - mz ω) * (Xw ω - mw ω)) =ᵐ[P] fun ω => Φ (V ω, U ω) := by
    filter_upwards [hmz', hmw'] with ω h1 h2
    simp only [hΦdef, hXzdef, hXwdef]
    rw [h1, h2]
  have ez : ∫⁻ ω, ENNReal.ofReal |Xz ω - Gz (U ω, az (V ω))| ^ p ∂P =
      ∫⁻ ω, ENNReal.ofReal |Xz ω - mz ω| ^ p ∂P :=
    lintegral_congr_ae (by filter_upwards [hmz'] with ω hω; rw [hω])
  have ew : ∫⁻ ω, ENNReal.ofReal |Xw ω - Gw (U ω, aw (V ω))| ^ q ∂P =
      ∫⁻ ω, ENNReal.ofReal |Xw ω - mw ω| ^ q ∂P :=
    lintegral_congr_ae (by filter_upwards [hmw'] with ω hω; rw [hω])
  have hdz' : ∫⁻ ω, ENNReal.ofReal |Xz ω - Gz (U ω, az (V ω))| ^ p ∂P ≠ ⊤ := by
    rw [ez]; exact hdz
  have hdw' : ∫⁻ ω, ENNReal.ofReal |Xw ω - Gw (U ω, aw (V ω))| ^ q ∂P ≠ ⊤ := by
    rw [ew]; exact hdw
  have hΦint : Integrable (fun ω => Φ (V ω, U ω)) P :=
    p48o_integrable_mul_of_lintegral
      (hXzm.sub (hGz.comp (hU.prodMk (haz.comp hVm)))).aestronglyMeasurable
      (hXwm.sub (hGw.comp (hU.prodMk (haw.comp hVm)))).aestronglyMeasurable hpq hdz' hdw'
  -- Fubini over the independent phase
  have hlaw : P.map (fun ω => (V ω, U ω)) = (P.map V).prod (P.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hVm.aemeasurable hU.aemeasurable).1 hindU
  have : IsProbabilityMeasure (P.map V) :=
    (Measure.isProbabilityMeasure_map_iff hVm.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have hΦprod : Integrable Φ ((P.map V).prod (P.map U)) := by
    rw [← hlaw]
    exact (integrable_map_measure hΦ.aestronglyMeasurable (hVm.prodMk hU).aemeasurable).2 hΦint
  have hsplitI : ∫ ω, Φ (V ω, U ω) ∂P = ∫ ψ, ∫ ω, Φ (V ω, ψ) ∂P ∂(P.map U) := by
    rw [← integral_map (hVm.prodMk hU).aemeasurable hΦ.aestronglyMeasurable, hlaw,
      integral_prod_symm _ hΦprod]
    refine integral_congr_ae (Eventually.of_forall fun ψ => ?_)
    exact integral_map (f := fun v => Φ (v, ψ)) hVm.aemeasurable
      (hΦ.comp measurable_prodMk_right).aestronglyMeasurable
  -- moments along the phase
  have hAbs : ∀ {F : (DistC × DistC) × ℝ → ℝ}, Measurable F → ∀ t : ℝ,
      Measurable fun x : (DistC × DistC) × ℝ => ENNReal.ofReal |F x| ^ t := fun hF t =>
    (ENNReal.measurable_ofReal.comp hF.abs).pow_const t
  have hsplitz₀ := p48o_lintegral_indep_split hVm hU hindU (hAbs hFz p₀)
  have hsplitzp := p48o_lintegral_indep_split hVm hU hindU (hAbs hFz p)
  set Fd : (DistC × DistC) × ℝ → ℝ := fun x => Fw x - Gw (x.2, aw x.1) with hFddef
  have hFd : Measurable Fd :=
    hFw.sub (hGw.comp (measurable_snd.prodMk (haw.comp measurable_fst)))
  have hsplitw := p48o_lintegral_indep_split hVm hU hindU (hAbs hFd q)
  have hm₀ : Measurable fun ψ => ∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p₀ ∂P := by
    have h := ((hAbs hFz p₀).comp ((hVm.comp measurable_fst).prodMk
      (measurable_snd : Measurable fun x : Ω × ℝ => x.2))).lintegral_prod_left' (μ := P)
    exact h
  have hmp : Measurable fun ψ => ∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p ∂P := by
    have h := ((hAbs hFz p).comp ((hVm.comp measurable_fst).prodMk
      (measurable_snd : Measurable fun x : Ω × ℝ => x.2))).lintegral_prod_left' (μ := P)
    exact h
  have hmd : Measurable fun ψ => ∫⁻ ω, ENNReal.ofReal |Fd (V ω, ψ)| ^ q ∂P := by
    have h := ((hAbs hFd q).comp ((hVm.comp measurable_fst).prodMk
      (measurable_snd : Measurable fun x : Ω × ℝ => x.2))).lintegral_prod_left' (μ := P)
    exact h
  have hfz₀ : ∀ᵐ ψ ∂(P.map U), ∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p₀ ∂P ≠ ⊤ := by
    have h := ae_lt_top (μ := P.map U) hm₀ (by rw [← hsplitz₀]; exact hXz)
    filter_upwards [h] with ψ hψ
    exact hψ.ne
  have hZψq : ∀ᵐ ψ ∂(P.map U), ∫⁻ ω, ENNReal.ofReal |Fd (V ω, ψ)| ^ q ∂P ≠ ⊤ := by
    have h := ae_lt_top (μ := P.map U) hmd (by rw [← hsplitw]; exact hdw')
    filter_upwards [h] with ψ hψ
    exact hψ.ne
  have hfzint : ∀ᵐ ψ ∂(P.map U), Integrable (fun ω => Fz (V ω, ψ)) P := by
    filter_upwards [hfz₀] with ψ hψ
    exact p48o_integrable_of_lintegral_rpow
      (hFz.comp (hVm.prodMk measurable_const)).aestronglyMeasurable hp₀1 hψ
  -- the frozen bound
  set Aψ : ℝ → ℝ≥0∞ := fun ψ => ENNReal.ofReal (GMSAppA.a3C p p₀) *
    (ENNReal.ofReal (δ ^ (s * p)) * ∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p ∂P +
      ENNReal.ofReal (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
        (∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p₀ ∂P) ^ (p / p₀)) with hAψdef
  set Bψ : ℝ → ℝ≥0∞ := fun ψ => ∫⁻ ω, ENNReal.ofReal |Fd (V ω, ψ)| ^ q ∂P with hBψdef
  have hpt : ∀ᵐ ψ ∂(P.map U),
      ENNReal.ofReal |∫ ω, Φ (V ω, ψ) ∂P| ≤ Aψ ψ ^ (1 / p) * Bψ ψ ^ (1 / q) := by
    filter_upwards [hfz₀, hZψq, hfzint] with ψ h1 h2 h3
    have hYfr : Measurable fun x : Ω × ℝ => (fun ω (_ψ : ℝ) => az (V ω)) x.1 x.2 :=
      haz.comp (hVm.comp measurable_fst)
    have hXfr : Measurable fun x : Ω × ℝ => (fun ω ψ => Fz (V ω, ψ)) x.1 x.2 :=
      hFz.comp ((hVm.comp measurable_fst).prodMk measurable_snd)
    have hcY := p48o_condValueG_ae_eq_condExp (Y := fun ω (_ψ : ℝ) => az (V ω))
      (X := fun ω ψ => Fz (V ω, ψ)) P hYfr hXfr ψ (fun ω => hFz0 _) h3
    have hfY : Measurable fun o : (DistOn (ballO z (r * δ)) × DistOn (ballO z (r * δ))) ×
        (ℝ × ℝ) => fz (o, ψ) := hfz.comp measurable_prodMk_right
    have hZf : Measurable fun o : (DistOn (ballO w (r * δ)) × DistOn (ballO w (r * δ))) ×
        (ℝ × ℝ) => fw (o, ψ) - Gw (ψ, o.2) :=
      (hfw.comp measurable_prodMk_right).sub (hGw.comp (measurable_const.prodMk measurable_snd))
    exact p48o_far_pair_A3_fixed hh hg hind hr hδ hδ1 hsmall hfar hp hpp₀ hs hδa hpq hfY hZf
      hcY h1 h2
  -- integrate over the phase with Hölder
  have hAm : Measurable Aψ :=
    measurable_const.mul ((measurable_const.mul hmp).add (measurable_const.mul (hm₀.pow_const _)))
  have hBm : Measurable Bψ := hmd
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.map U) hpq
    (hAm.pow_const (1 / p)).aemeasurable (hBm.pow_const (1 / q)).aemeasurable
  have hrp : ∀ x : ℝ≥0∞, (x ^ (1 / p)) ^ p = x := fun x => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hrq : ∀ x : ℝ≥0∞, (x ^ (1 / q)) ^ q = x := fun x => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, hrp, hrq] at hHolder
  -- the integrated `A`
  have hθ0 : 0 < p / p₀ := div_pos hp0 (hp0.trans hpp₀)
  have hθ1 : p / p₀ ≤ 1 := (div_le_one (hp0.trans hpp₀)).2 hpp₀.le
  have hintA : ∫⁻ ψ, Aψ ψ ∂(P.map U) ≤ ENNReal.ofReal (GMSAppA.a3C p p₀) *
      (ENNReal.ofReal (δ ^ (s * p)) * ∫⁻ ω, ENNReal.ofReal |Xz ω| ^ p ∂P +
        ENNReal.ofReal (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
          (∫⁻ ω, ENNReal.ofReal |Xz ω| ^ p₀ ∂P) ^ (p / p₀)) := by
    have hmp' : Measurable fun ψ => ENNReal.ofReal (δ ^ (s * p)) *
        ∫⁻ ω, ENNReal.ofReal |Fz (V ω, ψ)| ^ p ∂P := by
      have h := (measurable_const (a := ENNReal.ofReal (δ ^ (s * p)))).mul hmp
      exact h
    rw [hAψdef, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left hmp',
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    · exact le_of_eq hsplitzp.symm
    · refine (p48o_lintegral_rpow_le_rpow_lintegral hm₀.aemeasurable hθ0 hθ1).trans ?_
      rw [← hsplitz₀]
  have hintB : ∫⁻ ψ, Bψ ψ ∂(P.map U) = ∫⁻ ω, ENNReal.ofReal |Xw ω - mw ω| ^ q ∂P := by
    rw [hBψdef, ← hsplitw]
    exact ew
  calc ENNReal.ofReal |∫ ω, (Xz ω - mz ω) * (Xw ω - mw ω) ∂P|
      = ENNReal.ofReal |∫ ψ, ∫ ω, Φ (V ω, ψ) ∂P ∂(P.map U)| := by
        rw [integral_congr_ae hcov, hsplitI]
    _ ≤ ∫⁻ ψ, ENNReal.ofReal |∫ ω, Φ (V ω, ψ) ∂P| ∂(P.map U) := by
        rw [← Real.enorm_eq_ofReal_abs]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun ψ => ?_
        rw [Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ ψ, Aψ ψ ^ (1 / p) * Bψ ψ ^ (1 / q) ∂(P.map U) := lintegral_mono_ae hpt
    _ ≤ (∫⁻ ψ, Aψ ψ ∂(P.map U)) ^ (1 / p) * (∫⁻ ψ, Bψ ψ ∂(P.map U)) ^ (1 / q) := hHolder
    _ ≤ _ := by
        rw [hintB]
        exact mul_le_mul' (ENNReal.rpow_le_rpow hintA (by positivity)) le_rfl

end MatedCRTHarmonic.GMS4O
