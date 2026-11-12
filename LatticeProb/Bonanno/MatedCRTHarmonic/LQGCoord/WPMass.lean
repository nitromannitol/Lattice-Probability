/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPMass at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPCirc

/-!
# Normalized area masses of the whole-plane GFF and the two-radius rate

Fix a **window**: a scale
`δ > 0` and a measurable set `S ⊆ B̄(0, δ/4)` (`Win S δ`), and a bounded measurable `f` vanishing off
`S` (`WinFun S f M`). For a whole-plane GFF `X` and a radius `s ≤ δ/2` the normalized density and
mass are

  `wDens γ X δ s z = s^{γ²/2} e^{γ (X_s(z) − X_δ(0))}`, `wMass γ X δ f s = ∫ f · wDens`,

so that `∫ f d(areaS γ X s) = e^{γ X_δ(0)} wMass γ X δ f s`. Results:

* `integral_wDens`: `E wDens = δ^{γ²/2}` exactly (`Var(X_s(z) − X_δ(0)) = log(δ/s)`);
* `integral_abs_wMass_sub_le` (**two-radius rate**, uniform in the window): for radii
  `ε₁ ≤ ε₂ ≤ 2ε₁`, `ε₂ ≤ δ/2`,
  `E|wMass ε₂ − wMass ε₁| ≤ wConst γ · M · δ^{2+γ²/2} · (ε₂/δ)^{β}`, `β = areaRate γ > 0`
  (QuantumZipper's planar two-radius lemma `trlC_bound_area` with the hypotheses `trlHyp_pair`);
* `exists_dyadic_limit`: a.s. convergence of `wMass` along `δ 2^{-k}` with an `L¹` rate, and the
  offset rate `E|wMass (c δ 2^{-k}) − L| ≤ C M δ^{2+γ²/2} 2^{-βk}` for `c ∈ [1, 2]`
  (`lintegral_abs_wMass_offset_sub_lim_le`).

Source: Duplantier–Sheffield arXiv:0808.1560 §3 (the `L¹` Cauchy estimate behind Prop. 1.1); the
constants depend only on `γ` and scale exactly with `δ`, which is used at the cone point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper QuantumZipper.TwoRadius QuantumZipper.TwoRadiusC

/-! ## Windows -/

/-- A window: scale `δ > 0` and a measurable `S ⊆ B̄(0, δ/4)`. -/
structure Win (S : Set ℂ) (δ : ℝ) : Prop where
  meas : MeasurableSet S
  pos : 0 < δ
  sub : ∀ z ∈ S, ‖z‖ ≤ δ / 4

/-- A bounded measurable test function on the window. -/
structure WinFun (S : Set ℂ) (f : ℂ → ℝ) (M : ℝ) : Prop where
  meas : Measurable f
  bdd : ∀ z, |f z| ≤ M
  zero : ∀ z ∉ S, f z = 0

namespace Win

variable {S : Set ℂ} {δ : ℝ}

lemma subset (h : Win S δ) : S ⊆ closedBall 0 (δ / 4) := fun z hz => by
  rw [mem_closedBall, dist_zero_right]; exact h.sub z hz

lemma volume_lt_top (h : Win S δ) : volume S < ⊤ :=
  (measure_mono h.subset).trans_lt measure_closedBall_lt_top

lemma volumeReal_le (h : Win S δ) : volume.real S ≤ π * (δ / 4) ^ 2 := by
  have h1 : volume S ≤ volume (closedBall (0 : ℂ) (δ / 4)) := measure_mono h.subset
  rw [Complex.volume_closedBall] at h1
  rw [measureReal_def]
  have hfin : ENNReal.ofReal (δ / 4) ^ 2 * (NNReal.pi : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
  refine (ENNReal.toReal_mono hfin h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith [h.pos])]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

lemma norm_add_le (h : Win S δ) {z : ℂ} (hz : z ∈ S) {s : ℝ} (hs : s ≤ δ / 2) : ‖z‖ + s ≤ δ := by
  have := h.sub z hz; linarith [h.pos]

end Win

lemma WinFun.M_nonneg {S : Set ℂ} {f : ℂ → ℝ} {M : ℝ} (hf : WinFun S f M) : 0 ≤ M :=
  (abs_nonneg _).trans (hf.bdd 0)

/-! ## Densities and masses -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- The normalized density at radius `s`: `s^{γ²/2} e^{γ (X_s(z) − X_δ(0))}`. -/
def wDens (γ : ℝ) (X : Ω → DistC) (δ s : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  s ^ (γ ^ 2 / 2) * Real.exp (γ * cInc X s z δ 0 ω)

/-- The normalized mass `∫ f(z) s^{γ²/2} e^{γ (X_s(z) − X_δ(0))} dz`. -/
def wMass (γ : ℝ) (X : Ω → DistC) (δ : ℝ) (f : ℂ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z * wDens γ X δ s z ω

omit [MeasurableSpace Ω] in
lemma wDens_pos (γ δ : ℝ) {s : ℝ} (hs : 0 < s) (z : ℂ) (ω : Ω) : 0 < wDens γ X δ s z ω :=
  mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)

lemma measurable_wDens (hX : IsWholePlaneGFF X P) (γ δ s : ℝ) :
    Measurable (fun p : Ω × ℂ => wDens γ X δ s p.2 p.1) := by
  have h1 : Measurable fun p : Ω × ℂ => circleAvg (X p.1) s p.2 :=
    measurable_circleAvg.comp (f := fun p : Ω × ℂ => (X p.1, s, p.2))
      ((hX.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have h2 : Measurable fun p : Ω × ℂ => circleAvg (X p.1) δ 0 :=
    measurable_circleAvg.comp (f := fun p : Ω × ℂ => (X p.1, δ, (0 : ℂ)))
      ((hX.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_const))
  have h : Measurable fun p : Ω × ℂ => cInc X s p.2 δ 0 p.1 := h1.sub h2
  exact measurable_const.mul (Real.measurable_exp.comp (h.const_mul γ))

/-- **Exact first moment:** `E wDens = δ^{γ²/2}`. -/
lemma integral_wDens (hX : IsWholePlaneGFF X P) (γ : ℝ) {δ s : ℝ} (hs : 0 < s) {z : ℂ}
    (h : ‖z‖ + s ≤ δ) :
    Integrable (wDens γ X δ s z) P ∧ ∫ ω, wDens γ X δ s z ω ∂P = δ ^ (γ ^ 2 / 2) := by
  have hδ : 0 < δ := by linarith [norm_nonneg z]
  have hL := hasLaw_cInc_inner hX hs h
  have h0 : 0 ≤ Real.log (δ / s) :=
    Real.log_nonneg ((one_le_div hs).2 (by linarith [norm_nonneg z]))
  have hi : Integrable (fun ω => Real.exp (0 + γ * cInc X s z δ 0 ω)) P :=
    hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ γ 0)
  simp only [zero_add] at hi
  refine ⟨hi.const_mul _, ?_⟩
  have h1 : ∫ ω, Real.exp (0 + γ * cInc X s z δ 0 ω) ∂P =
      Real.exp (0 + (Real.log (δ / s)).toNNReal * γ ^ 2 / 2) := by
    rw [← integral_exp_mul_add_gaussianReal]
    exact hL.integral_comp (f := fun x => Real.exp (0 + γ * x)) (by fun_prop)
  simp only [zero_add] at h1
  simp only [wDens]
  rw [integral_const_mul, h1, Real.coe_toNNReal _ h0,
    show Real.log (δ / s) * γ ^ 2 / 2 = Real.log (δ / s) * (γ ^ 2 / 2) by ring,
    ← Real.rpow_def_of_pos (div_pos hδ hs), ← Real.mul_rpow hs.le (div_pos hδ hs).le]
  congr 1
  field_simp

variable {S : Set ℂ} {δ : ℝ} {f : ℂ → ℝ} {M : ℝ}

lemma integrable_fDens_prod (hX : IsWholePlaneGFF X P) (γ : ℝ) (hW : Win S δ)
    (hf : WinFun S f M) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ / 2) :
    Integrable (fun p : Ω × ℂ => f p.2 * wDens γ X δ s p.2 p.1) (P.prod (volume.restrict S)) := by
  have := hX.gaussian.isProbabilityMeasure
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hW.volume_lt_top.ne
  have hmeas : Measurable (fun p : Ω × ℂ => f p.2 * wDens γ X δ s p.2 p.1) :=
    (hf.meas.comp measurable_snd).mul (measurable_wDens hX γ δ s)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hW.meas]
    refine ae_of_all _ fun z hz => ?_
    exact (integral_wDens hX γ hs (hW.norm_add_le hz hsδ)).1.const_mul (f z)
  · refine Integrable.mono' (integrable_const (M * δ ^ (γ ^ 2 / 2))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hW.meas]
      refine ae_of_all _ fun z hz => ?_
      have e : ∀ ω, ‖f z * wDens γ X δ s z ω‖ = |f z| * wDens γ X δ s z ω := fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (wDens_pos γ δ hs z ω)]
      simp_rw [e]
      have hδp : 0 ≤ δ ^ (γ ^ 2 / 2) := Real.rpow_nonneg hW.pos.le _
      rw [integral_const_mul, (integral_wDens hX γ hs (hW.norm_add_le hz hsδ)).2,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hδp)]
      exact mul_le_mul_of_nonneg_right (hf.bdd z) hδp

omit [MeasurableSpace Ω] in
lemma wMass_eq_setIntegral (hf : WinFun S f M) (γ δ s : ℝ) (ω : Ω) :
    wMass γ X δ f s ω = ∫ z in S, f z * wDens γ X δ s z ω :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [hf.zero z hz, zero_mul]).symm

lemma integrable_wMass (hX : IsWholePlaneGFF X P) (γ : ℝ) (hW : Win S δ) (hf : WinFun S f M)
    {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ / 2) : Integrable (wMass γ X δ f s) P := by
  have e : wMass γ X δ f s = fun ω => ∫ z in S, f z * wDens γ X δ s z ω :=
    funext (wMass_eq_setIntegral hf γ δ s)
  rw [e]
  exact (integrable_fDens_prod hX γ hW hf hs hsδ).integral_prod_left

/-! ## The two-radius rate -/

/-- the constant of the two-radius rate (depends only on `γ`) -/
def wConst (γ : ℝ) : ℝ := π / 2 * √(1 + Real.exp ((2 * γ) ^ 2 / 4 * Real.log 2)) + π / 8

lemma wConst_nonneg (γ : ℝ) : 0 ≤ wConst γ := by unfold wConst; positivity

omit [MeasurableSpace Ω] in
/-- the density difference in the form of QuantumZipper's `dC` -/
lemma wDens_sub_eq (γ : ℝ) {δ ε₁ ε₂ : ℝ} (hδ : 0 < δ) (hε₁ : 0 < ε₁) (h12 : ε₁ ≤ ε₂)
    (f : ℂ → ℝ) (t : ℂ) (ω : Ω) :
    f t * wDens γ X δ ε₂ t ω - f t * wDens γ X δ ε₁ t ω =
      δ ^ (γ ^ 2 / 2) * dC (2 * γ) f (fun _ => 1 / 2 * Real.log (δ / ε₂))
        (fun _ => (Real.log (ε₂ / ε₁)).toNNReal) (fun t ω => cInc X ε₂ t δ 0 ω)
        (fun t ω => cInc X ε₁ t ε₂ t ω) t ω := by
  have hε₂ : 0 < ε₂ := hε₁.trans_le h12
  have h0 : 0 ≤ Real.log (ε₂ / ε₁) := Real.log_nonneg ((one_le_div hε₁).2 h12)
  set A := cInc X ε₂ t δ 0 ω with hA
  set B := cInc X ε₁ t ε₂ t ω with hB
  have hAB : cInc X ε₁ t δ 0 ω = A + B := by simp only [hA, hB, cInc]; ring
  set E1 := Real.exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * Real.log (δ / ε₂)) + 2 * γ / 2 * A)
  set E2 := Real.exp (-((2 * γ) ^ 2 / 8 * Real.log (ε₂ / ε₁)) + 2 * γ / 2 * B)
  have e1 : ε₂ ^ (γ ^ 2 / 2) * Real.exp (γ * A) = δ ^ (γ ^ 2 / 2) * E1 := by
    rw [Real.rpow_def_of_pos hε₂, Real.rpow_def_of_pos hδ, ← Real.exp_add, ← Real.exp_add,
      Real.log_div hδ.ne' hε₂.ne']
    congr 1; ring
  have e2 : ε₁ ^ (γ ^ 2 / 2) * Real.exp (γ * (A + B)) = δ ^ (γ ^ 2 / 2) * (E1 * E2) := by
    rw [Real.rpow_def_of_pos hε₁, Real.rpow_def_of_pos hδ, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, Real.log_div hδ.ne' hε₂.ne', Real.log_div hε₂.ne' hε₁.ne']
    congr 1; ring
  simp only [wDens, dC, tiltY, Real.coe_toNNReal _ h0, hAB]
  rw [e1, e2]
  ring

/-- the algebra of the two-radius bound -/
lemma trl_rhs_le {γ : ℝ} {M δ ε₂ V : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hε₂ : 0 < ε₂) (h2δ : ε₂ ≤ δ) (hV0 : 0 ≤ V) (hV : V ≤ π * (δ / 4) ^ 2) :
    √(M ^ 2 * ((1 + Real.exp ((2 * γ) ^ 2 / 4 * Real.log 2)) *
        (Real.exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 * 0 / 2) *
        Real.exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) * (1 / 2 * Real.log (δ / ε₂))))) *
        (π * (2 * ε₂) ^ 2 * V))
      + M * (2 * (Real.exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 * 0 / 2) *
        Real.exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * Real.log (δ / ε₂))))) * V
    ≤ wConst γ * M * δ ^ 2 * (ε₂ / δ) ^ AreaExist.areaRate γ := by
  set θ := max 0 ((3 * γ - 2) / 2) with hθ
  set A := 1 + Real.exp ((2 * γ) ^ 2 / 4 * Real.log 2) with hAdef
  set L := 1 / 2 * Real.log (δ / ε₂) with hLdef
  set β := AreaExist.areaRate γ with hβdef
  have hA0 : 0 ≤ A := by positivity
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log (δ / ε₂) := Real.log_nonneg ((one_le_div hε₂).2 h2δ)
    rw [hLdef]; linarith
  have hβ1 : β ≤ (2 - γ ^ 2 + θ ^ 2 / 2) / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 8 := min_le_right _ _
  have hε₂e : ε₂ = δ * Real.exp (-2 * L) := by
    rw [hLdef, show -2 * (1 / 2 * Real.log (δ / ε₂)) = Real.log (ε₂ / δ) by
      rw [Real.log_div hδ.ne' hε₂.ne', Real.log_div hε₂.ne' hδ.ne']; ring,
      Real.exp_log (div_pos hε₂ hδ)]
    field_simp
  have hxβ : (ε₂ / δ) ^ β = Real.exp (-(2 * β) * L) := by
    rw [Real.rpow_def_of_pos (div_pos hε₂ hδ), hLdef, Real.log_div hε₂.ne' hδ.ne',
      Real.log_div hδ.ne' hε₂.ne']
    congr 1; ring
  rw [hxβ]
  simp only [mul_zero, zero_div, Real.exp_zero, one_mul]
  set B := π / 2 * √A * M * δ ^ 2 * Real.exp (-(2 * β) * L) with hBdef
  have hB0 : 0 ≤ B := by positivity
  -- first term
  have hexp1 : Real.exp ((2 * γ ^ 2 - θ ^ 2) * L) * Real.exp (-2 * L) ^ 2 ≤
      Real.exp (-(2 * β) * L) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith
  have h1 : M ^ 2 * (A * Real.exp ((2 * γ ^ 2 - θ ^ 2) * L)) * (π * (2 * ε₂) ^ 2 * V) ≤ B ^ 2 := by
    have hVb : π * (2 * ε₂) ^ 2 * V ≤ π * (2 * ε₂) ^ 2 * (π * (δ / 4) ^ 2) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    calc M ^ 2 * (A * Real.exp ((2 * γ ^ 2 - θ ^ 2) * L)) * (π * (2 * ε₂) ^ 2 * V)
        ≤ M ^ 2 * (A * Real.exp ((2 * γ ^ 2 - θ ^ 2) * L)) *
            (π * (2 * ε₂) ^ 2 * (π * (δ / 4) ^ 2)) :=
          mul_le_mul_of_nonneg_left hVb (by positivity)
      _ = (π / 2) ^ 2 * A * M ^ 2 * (δ ^ 2) ^ 2 *
            (Real.exp ((2 * γ ^ 2 - θ ^ 2) * L) * Real.exp (-2 * L) ^ 2) := by
          rw [hε₂e]; ring
      _ ≤ (π / 2) ^ 2 * A * M ^ 2 * (δ ^ 2) ^ 2 * Real.exp (-(2 * β) * L) ^ 2 :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = B ^ 2 := by
          rw [hBdef, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA0]
  have t1 : √(M ^ 2 * (A * Real.exp ((2 * γ ^ 2 - θ ^ 2) * L)) * (π * (2 * ε₂) ^ 2 * V)) ≤ B :=
    (Real.sqrt_le_sqrt h1).trans (Real.sqrt_sq hB0).le
  -- second term
  have hexp2 : Real.exp (-((2 - γ) ^ 2 / 4) * L) ≤ Real.exp (-(2 * β) * L) :=
    Real.exp_le_exp.2 (by nlinarith)
  have t2 : M * (2 * Real.exp (-((2 - γ) ^ 2 / 4) * L)) * V ≤
      π / 8 * M * δ ^ 2 * Real.exp (-(2 * β) * L) := by
    calc M * (2 * Real.exp (-((2 - γ) ^ 2 / 4) * L)) * V
        ≤ M * (2 * Real.exp (-(2 * β) * L)) * (π * (δ / 4) ^ 2) := by
          gcongr
      _ = π / 8 * M * δ ^ 2 * Real.exp (-(2 * β) * L) := by ring
  calc _ ≤ B + π / 8 * M * δ ^ 2 * Real.exp (-(2 * β) * L) := add_le_add t1 t2
    _ = wConst γ * M * δ ^ 2 * Real.exp (-(2 * β) * L) := by rw [hBdef, wConst]; ring

/-- **The two-radius rate**, uniform in the window: for `ε₁ ≤ ε₂ ≤ 2ε₁`, `ε₂ ≤ δ/2`,
`E|wMass ε₂ − wMass ε₁| ≤ wConst γ · M · δ^{2+γ²/2} · (ε₂/δ)^β`. -/
theorem integral_abs_wMass_sub_le (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hW : Win S δ) (hf : WinFun S f M) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (h12 : ε₁ ≤ ε₂)
    (h21 : ε₂ ≤ 2 * ε₁) (h2δ : ε₂ ≤ δ / 2) :
    ∫ ω, |wMass γ X δ f ε₂ ω - wMass γ X δ f ε₁ ω| ∂P ≤
      wConst γ * M * δ ^ (2 + γ ^ 2 / 2) * (ε₂ / δ) ^ AreaExist.areaRate γ := by
  have := hX.gaussian.isProbabilityMeasure
  have hε₂ : 0 < ε₂ := hε₁.trans_le h12
  have hδ := hW.pos
  have hH := trlHyp_pair hX hδ hε₁ h12 h21 (fun t ht => hW.norm_add_le ht h2δ)
  have hb := trlC_bound_area hγ hγ2 (δ := 2 * ε₂) (by positivity) hW.meas hW.volume_lt_top
    hf.meas hf.bdd hH
  set D : Ω → ℝ := fun ω => ∫ t in S, dC (2 * γ) f (fun _ => 1 / 2 * Real.log (δ / ε₂))
    (fun _ => (Real.log (ε₂ / ε₁)).toNNReal) (fun t ω => cInc X ε₂ t δ 0 ω)
    (fun t ω => cInc X ε₁ t ε₂ t ω) t ω with hD
  have hid : (fun ω => |wMass γ X δ f ε₂ ω - wMass γ X δ f ε₁ ω|) =ᵐ[P]
      fun ω => δ ^ (γ ^ 2 / 2) * |D ω| := by
    filter_upwards [(integrable_fDens_prod hX γ hW hf hε₂ h2δ).prod_right_ae,
      (integrable_fDens_prod hX γ hW hf hε₁ (h12.trans h2δ)).prod_right_ae] with ω h1 h2
    rw [wMass_eq_setIntegral hf, wMass_eq_setIntegral hf, ← integral_sub h1 h2]
    simp_rw [wDens_sub_eq γ hδ hε₁ h12 f]
    rw [integral_const_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hδ _)]
  rw [integral_congr_ae hid, integral_const_mul]
  have hδp : 0 < δ ^ (γ ^ 2 / 2) := Real.rpow_pos_of_pos hδ _
  have hr := trl_rhs_le (γ := γ) hf.M_nonneg hδ hε₂ (by linarith) measureReal_nonneg
    hW.volumeReal_le
  have e : δ ^ (2 + γ ^ 2 / 2) = δ ^ (γ ^ 2 / 2) * δ ^ 2 := by
    rw [Real.rpow_add hδ, Real.rpow_two]; ring
  rw [e]
  calc δ ^ (γ ^ 2 / 2) * ∫ ω, |D ω| ∂P
      ≤ δ ^ (γ ^ 2 / 2) * (wConst γ * M * δ ^ 2 * (ε₂ / δ) ^ AreaExist.areaRate γ) :=
        mul_le_mul_of_nonneg_left (hb.trans hr) hδp.le
    _ = _ := by ring

end MatedCRTHarmonic.LQGCoord
