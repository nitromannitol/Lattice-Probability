/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112N3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L2

/-!
# `CONFHarmLowZB` (task P2-CONFHLZ)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), Lemma 3.3, Step 2
(C:1217–1234), harmonic bound of C:1169–1172 ("by translation and scale invariance of the law of
`h` modulo additive constant").

**`confHarmLowZB : CONFHarmLowZB`**, exactly as stated in S3D112L2, for every version `X` of the
zero-boundary part (no uniqueness of the Markov decomposition is needed). Proof: with
`h̃ = h(r · + z) − h_r(z)` (a normalized whole-plane GFF) and `X̃ = X(r · + z)` (`X̃|_{U₀}` a
zero-boundary GFF on `U₀`, `IsZeroBoundaryGFF.affine`), the function `f = 𝔥(r · + z) − (h − h_ρ(w))_r(z)`
is a harmonic representative of `(h̃ − X̃)|_{U₀}` (change of variables as in
`isHarmPart_affineComp`, S3L35B5), and `hlz_unit` (S3D112N2) bounds `|f|` on `cl V₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GFFInv

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- a zero-boundary GFF is one up to null sets -/
theorem hlz_isZeroBoundaryGFF_congr {V : Opens ℂ} {Z Y : Ω → DistOn V}
    (hZ : IsZeroBoundaryGFF V Z P) (hY : Measurable Y) (hae : Y =ᵐ[P] Z) :
    IsZeroBoundaryGFF V Y P := by
  have hφ : ∀ φ : TestOn V, (fun ω => Y ω φ) =ᵐ[P] fun ω => Z ω φ := fun φ => by
    filter_upwards [hae] with ω hω; rw [hω]
  refine ⟨hY, ⟨fun φ => (measurable_distOn_apply φ).comp hY,
    hZ.process.gaussian.congr fun φ => (hφ φ).symm, fun φ => ?_, fun φ ψ => ?_⟩⟩
  · rw [integral_congr_ae (hφ φ)]; exact hZ.process.centered φ
  · rw [CircleAvg.covariance_congr_ae (hφ φ) (hφ ψ)]; exact hZ.process.covariance_eq φ ψ

/-- `h(r · + z) − h_r(z)` is a normalized whole-plane GFF (as `isNormalizedWPGFF_rescale`) -/
theorem hlz_rescale [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {r : ℝ}
    (hr : 0 < r) (c : ℂ) :
    IsNormalizedWPGFF (fun ω => addConst (affineComp r c (h ω)) (-circleAvg (h ω) r c)) P := by
  have hg : IsWholePlaneGFF (fun ω => affineComp r c (h ω)) P := hh.affineComp hr c
  have hcm : Measurable fun ω => circleAvg (h ω) r c :=
    (measurable_circleAvg_left r c).comp hh.measurable
  refine ⟨hg.addConst hcm.neg, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst hg 0 one_pos,
    CircleAvg.ae_circleAvg_affineComp hh hr c] with ω h1 h2
  rw [h1, h2]; ring

/-- `X(r · + z)|_{U₀}` is the transported zero-boundary GFF -/
theorem hlz_restrict_affine {r : ℝ} (hr : 0 < r) (z : ℂ) (U₀ : Opens ℂ) (T : DistC) :
    restrictTo U₀ (affineComp r z T) =
      distAffine r z hr.ne' (restrictTo (affOpens r z U₀) T) := by
  ext φ
  rw [distAffine_apply]
  show affineComp r z T (TestFunction.monoCLM ℝ φ) = (r ^ 2)⁻¹ * T (TestFunction.monoCLM ℝ _)
  rw [GFFInv.affineComp_apply]
  congr 2
  ext x
  rw [testAffinePull_apply r z hr.ne']
  simp [TestFunction.monoCLM_apply]
  show (φ : ℂ → ℝ) ((x - z) / r) = φ (affMap r z x)
  rw [affMap, Complex.real_smul, ← sub_eq_add_neg, div_eq_inv_mul, Complex.ofReal_inv]

/-- **CONF L3.3 Step 2, the harmonic lower bound** (C:1169–1172, C:1217–1234) -/
theorem confHarmLowZB : CONFHarmLowZB := by
  intro U₀ V₀ hU₀b hV₀U₀ β hβ
  set K := closure (V₀ : Set ℂ)
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hU₀b.subset hV₀U₀)
  obtain ⟨A, hA0, HA⟩ := hlz_unit hU₀b hKc hV₀U₀ hβ
  refine ⟨A, ?_⟩
  intro Ω _ P _ h hh ρ w r hr z X hX
  set U := affOpens r z U₀
  obtain ⟨hXm, -, hh₀, hz, hsum, hXz, hharm, hzb, -⟩ := hX
  -- the rescaled fields
  set ht : Ω → DistC := fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)
  set Xt : Ω → DistC := fun ω => affineComp r z (X ω)
  have hht : IsNormalizedWPGFF ht P := hlz_rescale hh hr z
  have hXtm : Measurable Xt := (measurable_affineComp r z).comp hXm
  have hzbX : IsZeroBoundaryGFF U (fun ω => restrictTo U (X ω)) P := by
    refine hlz_isZeroBoundaryGFF_congr hzb ((measurable_restrictTo U).comp hXm) ?_
    filter_upwards [hXz] with ω hω; rw [hω]; rfl
  have hzbt : IsZeroBoundaryGFF U₀ (fun ω => restrictTo U₀ (Xt ω)) P := by
    have := hzbX.affine (U := U₀) hr.ne'
    have e : (fun ω => restrictTo U₀ (Xt ω)) =
        fun ω => distAffine r z hr.ne' (restrictTo U (X ω)) := by
      funext ω; exact hlz_restrict_affine hr z U₀ (X ω)
    rw [e]; exact this
  have Hu := HA P ht Xt hht hXtm hzbt
  refine le_trans (measure_mono_ae ?_) Hu
  filter_upwards [hXz, hharm, CircleAvg.ae_circleAvg_addConst hh z hr] with ω hω1 hω2 hω3
  rintro hbad
  obtain ⟨𝔥, h𝔥, hrep⟩ := hω2
  set c₀ := circleAvg (recField h ρ w ω) r z with hc₀
  have hc₀e : c₀ = circleAvg (h ω) r z - circleAvg (h ω) ρ w := by
    rw [hc₀, recField, hω3]; ring
  have hrep' : ∀ φ : TestOn (toOpens U U.isOpen),
      restrictTo (toOpens U U.isOpen) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x := by
    intro φ
    rw [← hrep φ, hω1, hsum ω, add_sub_cancel_right]
  -- some `u ∈ rV₀ + z` violates the bound
  have hex : ∃ u ∈ (affOpens r z V₀ : Set ℂ), 𝔥 u < c₀ - A := by
    by_contra hne
    push Not at hne
    exact hbad ⟨𝔥, h𝔥, hrep', hne⟩
  obtain ⟨u, hu, hlt⟩ := hex
  -- the unit-scale representative
  set f : ℂ → ℝ := fun x => 𝔥 (r • x + z) - c₀
  have hA : Continuous fun x : ℂ => r • x + z := by fun_prop
  have hfh : HarmonicOnNhd f U₀ := by
    have h1 := harmonicOnNhd_comp_holo U.isOpen U₀.isOpen h𝔥 (f := fun x => r • x + z) (by
        have : (fun x : ℂ => r • x + z) = fun x => (r : ℂ) * x + z := by
          funext x; rw [Complex.real_smul]
        rw [this]; fun_prop) (fun x hx => by
          show affMap r z (r • x + z) ∈ (U₀ : Set ℂ)
          rw [affMap, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
          exact hx)
    exact h1.sub (harmonicOnNhd_const c₀)
  refine ⟨f, hfh, fun φ => ?_, affMap r z u, subset_closure hu, ?_⟩
  · -- the change of variables
    set ϕ : TestC := TestFunction.monoCLM ℝ φ
    have hϕ : (ϕ : ℂ → ℝ) = φ := by ext x; simp [ϕ, TestFunction.monoCLM_apply]
    set ϕ' := affPush r z ϕ with hϕ'def
    have hϕ'U : tsupport (ϕ' : ℂ → ℝ) ⊆ (U : Set ℂ) := fun y hy => by
      have := tsupport_affPush_subset hr z ϕ (S := U₀) (by rw [hϕ]; exact φ.tsupport_subset) hy
      show r⁻¹ • (y + -z) ∈ (U₀ : Set ℂ)
      have e : r⁻¹ • (y + -z) = (y - z) / r := by
        rw [Complex.real_smul, ← sub_eq_add_neg, div_eq_inv_mul, Complex.ofReal_inv]
      rw [e]; exact this
    set ϕU : TestOn (toOpens U U.isOpen) := ⟨ϕ', ϕ'.contDiff, ϕ'.hasCompactSupport, hϕ'U⟩
    have hpair := hrep' ϕU
    have hl : restrictTo (toOpens U U.isOpen) (recField h ρ w ω - X ω) ϕU =
        (recField h ρ w ω - X ω) ϕ' := by
      show (recField h ρ w ω - X ω) (TestFunction.monoCLM ℝ ϕU) = _
      congr 1
      ext y
      simp [TestFunction.monoCLM_apply, ϕU]
      rfl
    rw [hl] at hpair
    have hchg : ∫ x, 𝔥 x * ϕU x = ∫ x, 𝔥 (r • x + z) * ϕ x := by
      show ∫ x, 𝔥 x * ϕ' x = _
      rw [integral_eq_smul_add _ hr z, ← integral_const_mul]
      congr 1
      funext v
      simp only [ϕ', affPush, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        testAffinePull_apply r z hr.ne', div_affMap_cancel hr]
      field_simp
    have hint : ∫ x, ϕ' x = ∫ x, ϕ x := integral_affPush hr z ϕ
    have hcont : ∀ y ∈ (U₀ : Set ℂ), ContinuousAt (fun x => 𝔥 (r • x + z)) y := fun y hy =>
      ((h𝔥 _ (show r • y + z ∈ (U : Set ℂ) by
        show affMap r z (r • y + z) ∈ (U₀ : Set ℂ)
        rw [affMap, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
        exact hy)).1.continuousAt).comp (f := fun x : ℂ => r • x + z) (g := 𝔥) (x := y)
        hA.continuousAt
    have hi1 := GM.integrable_mul_testOn hcont φ
    have hi2 : Integrable fun x => c₀ * φ x :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul c₀
    have e1 : ∫ x, f x * φ x = (∫ x, 𝔥 (r • x + z) * φ x) - c₀ * ∫ x, φ x := by
      rw [show (fun x => f x * φ x) = fun x => 𝔥 (r • x + z) * φ x - c₀ * φ x from by
        funext x; simp only [f]; ring, integral_sub hi1 hi2, integral_const_mul]

    rw [e1]
    show (ht ω - Xt ω) ϕ = _
    simp only [ht, Xt, sub_apply, addConst_apply, affineComp_apply_eq_affPush]
    have e2 : (h ω) ϕ' = (recField h ρ w ω - X ω) ϕ' + X ω ϕ' +
        circleAvg (h ω) ρ w * ∫ x, ϕ' x := by
      simp only [recField, sub_apply, addConst_apply]; ring
    rw [← hϕ'def, e2, hpair, hchg, hint, hc₀e]
    simp only [hϕ]
    ring
  · -- the violating point
    have e : r • affMap r z u + z = u := by
      rw [affMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, neg_add_cancel_right]
    show A < |𝔥 (r • affMap r z u + z) - c₀|
    rw [e, abs_sub_comm, abs_of_pos (by linarith)]
    linarith

end LQGMetric.CONF
