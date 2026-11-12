/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112N2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112N1

/-!
# `CONFHarmLowZB`, part 2: `hlz_unit` (task P2-CONFHLZ)

See `S3D112N1.lean` for the source (CONF C:1169–1172, C:1217–1234; Ding–Gwynne Lemma 2.2 (2.4)
in the form `dg_tail_unif`, S3L35B7) and the plan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM LM MarkovNorm MarkovGauss MarkovZB DG DG.L22 QuantumZipper HeatSq

/-- exponential moment of a centred Gaussian with variance at most `v` -/
theorem hlz_gauss_mom {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY : HasGaussianLaw Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    {v : ℝ} (hv : Var[Y; P] ≤ v) (a : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Y ω|)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (v * a ^ 2 / 2)) := by
  refine (lintegral_exp_abs_le (Z := fun _ => (0 : ℝ)) hYm measurable_const
    (indepFun_const_right Y 0) (integrable_const _) (by simp) hY hY0
    (Eventually.of_forall fun ω => add_zero _) a).trans ?_
  gcongr

/-- **the unit-scale bound**: for every normalized whole-plane GFF `h` and every measurable `X`
with `X|_V` a zero-boundary GFF on `V`, harmonic representatives of `(h − X)|_V` are bounded on
`K` by `A` except with probability `≤ β`; `A` depends only on `V`, `K`, `β`. -/
theorem hlz_unit {V : Opens ℂ} (hVb : Bornology.IsBounded (V : Set ℂ)) {K : Set ℂ}
    (hK : IsCompact K) (hKV : K ⊆ V) {β : ℝ} (hβ : 0 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h X : Ω → DistC), IsNormalizedWPGFF h P → Measurable X →
      IsZeroBoundaryGFF V (fun ω => restrictTo V (X ω)) P →
      P {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧
        (∀ φ : TestOn V, restrictTo V (h ω - X ω) φ = ∫ x, g x * φ x) ∧ ∃ x ∈ K, A < |g x|} ≤
        ENNReal.ofReal β := by
  rcases K.eq_empty_or_nonempty with hK0 | ⟨c, hc⟩
  · refine ⟨0, le_rfl, fun {Ω} _ P _ h X _ _ _ => ?_⟩
    refine (measure_mono (t := ∅) fun ω hω => ?_).trans (by simp)
    obtain ⟨g, -, -, z, hz, -⟩ := hω
    rw [hK0] at hz; exact hz
  obtain ⟨ε, hε, hεV⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set S := cthickening δ K with hSdef
  have hSc : IsCompact S := hK.cthickening
  have hSV : ∀ y ∈ S, closedBall y δ ⊆ (V : Set ℂ) := fun y hy =>
    (closedBall_subset_cthickening hy δ).trans
      ((cthickening_cthickening_subset hδ.le hδ.le K).trans
        (by rw [show δ + δ = ε by rw [hδdef]; ring]; exact hεV))
  have hKS : ∀ u ∈ K, closedBall u δ ⊆ S := fun u hu => closedBall_subset_cthickening hu δ
  have hcS : c ∈ S := self_subset_cthickening K hc
  obtain ⟨ρ, hρ⟩ := hSc.isBounded.subset_closedBall c
  have hρ0 : 0 ≤ ρ := by
    have := hρ hcS; rw [mem_closedBall, dist_self] at this; exact this
  have hS0 : volume S ≠ 0 := fun h0 =>
    (measure_closedBall_pos volume c hδ).ne' (measure_mono_null (hKS c hc) h0)
  set m := (volume S).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hS0 hSc.measure_lt_top.ne
  have hI := integral_radProf_pos hδ
  set I := ∫ y, radProf δ y
  set κ₀ := expNegInvGlue (δ ^ 2) / I / I with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := div_nonneg (div_nonneg (expNegInvGlue.nonneg _) hI.le) hI.le
  set ψc := radBump δ hδ.le c
  -- the reference variance of `h(ψ_c)` and the zero-boundary bound
  obtain ⟨Ω₀, m₀, P₀, h₀, hP₀, hh₀⟩ := GFFExist.exists_wholePlaneGFF
  obtain ⟨hg₀, hn₀⟩ := DFGPS.isNormalizedAt_recenter hh₀ one_pos 0
  set g₀ : Ω₀ → DistC := fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)
  obtain ⟨ρ₀, -, hρ₀⟩ := HarmLoc.exists_unit_test isOpen_univ univ_nonempty
  set v := Var[fun T : DistC => T ψc; P₀.map g₀]
  obtain ⟨vX, hvX⟩ := hlz_zbVar_bound hVb hδ
  set M₀ := |radK δ ρ| + |v| + |vX| + 1 with hM₀
  set B := M₀ * (κ₀ * m) ^ 2 / 2 + 1 with hBdef
  have hB : 0 < B := by positivity
  have hBle : ∀ (M t : ℝ), M ≤ M₀ → M * (t * κ₀ * m) ^ 2 / 2 ≤ B * t ^ 2 := by
    intro M t hM
    have h1 := mul_le_mul_of_nonneg_right hM (sq_nonneg (t * κ₀ * m))
    have e : B * t ^ 2 = M₀ * (t * κ₀ * m) ^ 2 / 2 + t ^ 2 := by rw [hBdef]; ring
    rw [e]; nlinarith [sq_nonneg t]
  obtain ⟨A₀, hA₀, HA₀⟩ := hlz_tail_level hB (by positivity : 0 < β / 3)
  refine ⟨3 * A₀, by positivity, ?_⟩
  intro Ω _ P _ h X hh hXm hzb
  -- the pieces
  set Xc : Ω → ℝ := fun ω => h ω ψc
  set F : Ω → ℂ → ℝ := fun ω y => |h ω (radDiff hδ.le y c).1|
  set FX : Ω → ℂ → ℝ := fun ω y => |X ω (radBump δ hδ.le y)|
  set Φ : Ω → ℝ := fun ω => ∫ y in S, F ω y
  set ΦX : Ω → ℝ := fun ω => ∫ y in S, FX ω y
  have hFeq : ∀ ω y, h ω (radDiff hδ.le y c).1 = h ω (radBump δ hδ.le y) - h ω ψc := by
    intro ω y; simp only [radDiff, map_sub, ψc]
  have hFc : ∀ ω, Continuous (F ω) := fun ω => by
    have : F ω = fun y => |h ω (radBump δ hδ.le y) - h ω ψc| := by
      funext y; simp only [F]; rw [hFeq]
    rw [this]
    exact (((map_continuous (h ω)).comp (continuous_radBump δ hδ.le)).sub continuous_const).abs
  have hFXc : ∀ ω, Continuous (FX ω) := fun ω =>
    ((map_continuous (X ω)).comp (continuous_radBump δ hδ.le)).abs
  have hFm : Measurable (Function.uncurry F) := by
    have h1 := (measurable_apply_radBump δ hδ.le).comp
      ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun p : Ω × ℂ => h p.1 ψc :=
      (measurable_eval_distC ψc).comp (hh.1.measurable.comp measurable_fst)
    have : Function.uncurry F = fun p : Ω × ℂ => |h p.1 (radBump δ hδ.le p.2) - h p.1 ψc| := by
      funext p; simp only [Function.uncurry, F]; rw [hFeq]
    rw [this]; exact continuous_abs.measurable.comp (h1.sub h2)
  have hFXm : Measurable (Function.uncurry FX) :=
    continuous_abs.measurable.comp ((measurable_apply_radBump δ hδ.le).comp
      ((hXm.comp measurable_fst).prodMk measurable_snd))
  have hXcm : Measurable Xc := (measurable_eval_distC ψc).comp hh.1.measurable
  have hΦm : Measurable Φ :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable
  have hΦXm : Measurable ΦX :=
    (hFXm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable
  -- moments
  have hmomD : ∀ y ∈ S, ∀ a : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * F ω y)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (radK δ ρ * a ^ 2 / 2)) := by
    intro y hy a
    set φ := radDiff hδ.le y c
    obtain ⟨hYg, hY0⟩ := normalized_pair_gauss hh φ.1
    have hmh : Measurable (fun ω => h ω φ.1) :=
      (measurable_eval_distC φ.1).comp hh.1.measurable
    have hvar : Var[fun ω => h ω φ.1; P] = logCov φ.1 φ.1 := by
      rw [← covariance_self hmh.aemeasurable]
      exact hh.1.covariance_eq φ φ
    refine hlz_gauss_mom hmh hYg hY0 ?_ a
    rw [hvar]
    exact logCov_radDiff_le hδ hρ0 (by rw [← dist_eq_norm]; exact hρ hy)
  have hmomX : ∀ y ∈ S, ∀ a : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * FX ω y)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (vX * a ^ 2 / 2)) := by
    intro y hy a
    set φ := bumpOn hδ (hSV y hy)
    have e : (fun ω => X ω (radBump δ hδ.le y)) = fun ω => restrictTo V (X ω) φ := by
      funext ω; rw [restrictTo_bumpOn]
    have hmX : Measurable (fun ω => X ω (radBump δ hδ.le y)) := by
      rw [e]; exact hzb.process.measurable φ
    have hYg : HasGaussianLaw (fun ω => X ω (radBump δ hδ.le y)) P := by
      rw [e]; exact hzb.process.gaussian.hasGaussianLaw_eval φ
    have hY0 : ∫ ω, X ω (radBump δ hδ.le y) ∂P = 0 := by
      rw [e]; exact hzb.process.centered φ
    have hvar : Var[fun ω => X ω (radBump δ hδ.le y); P] ≤ vX := by
      rw [← covariance_self hmX.aemeasurable, e, hzb.process.covariance_eq φ φ]
      exact hvX y (hSV y hy)
    exact hlz_gauss_mom hmX hYg hY0 hvar a
  have hlaw : P.map h = P₀.map g₀ :=
    GFFLaw.map_eq_of_normalized_ae hρ₀ (measurable_circleAvg_left 1 0) hh.1 hg₀
      (CircleAvg.ae_circleAvg_addConst hh.1 0 one_pos)
      (CircleAvg.ae_circleAvg_addConst hg₀ 0 one_pos) hh.2 hn₀
  have hvc : Var[fun ω => h ω ψc; P] ≤ v := by
    refine le_of_eq ?_
    rw [show v = Var[fun T : DistC => T ψc; P.map h] by rw [hlaw],
      variance_map (GFFInv.measurable_pair ψc).aemeasurable hh.1.measurable.aemeasurable]
    rfl
  have hmomC : ∀ a : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Xc ω|)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (v * a ^ 2 / 2)) := by
    obtain ⟨hYg, hY0⟩ := normalized_pair_gauss hh ψc
    exact hlz_gauss_mom hXcm hYg hY0 hvc
  -- the three tails
  have hA3 : ∀ A : ℝ, A₀ ≤ A → ENNReal.ofReal (2 * Real.exp (-(1 / (4 * B)) * A ^ 2)) ≤
      ENNReal.ofReal (β / 3) := fun A hA => ENNReal.ofReal_le_ofReal (HA₀ A hA)
  have hT1 : P {ω | A₀ < κ₀ * Φ ω} ≤ ENNReal.ofReal (β / 3) := by
    refine (tail_of_lintegral_exp (hΦm.const_mul κ₀) hB (fun t _ => ?_) A₀ hA₀).trans
      (hA3 A₀ le_rfl)
    have := lintegral_exp_setIntegral_le hSc hS0 hFc hFm hmomD (t * κ₀)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    rw [← hm]
    exact hBle _ t (by linarith [le_abs_self (radK δ ρ), abs_nonneg v, abs_nonneg vX])
  have hT2 : P {ω | A₀ < κ₀ * m * |Xc ω|} ≤ ENNReal.ofReal (β / 3) := by
    refine (tail_of_lintegral_exp ((continuous_abs.measurable.comp hXcm).const_mul (κ₀ * m)) hB
      (fun t _ => ?_) A₀ hA₀).trans (hA3 A₀ le_rfl)
    have := hmomC (t * κ₀ * m)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    exact hBle _ t (by linarith [le_abs_self v, abs_nonneg (radK δ ρ), abs_nonneg vX])
  have hT3 : P {ω | A₀ < κ₀ * ΦX ω} ≤ ENNReal.ofReal (β / 3) := by
    refine (tail_of_lintegral_exp (hΦXm.const_mul κ₀) hB (fun t _ => ?_) A₀ hA₀).trans
      (hA3 A₀ le_rfl)
    have := lintegral_exp_setIntegral_le hSc hS0 hFXc hFXm hmomX (t * κ₀)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    rw [← hm]
    exact hBle _ t (by linarith [le_abs_self vX, abs_nonneg (radK δ ρ), abs_nonneg v])
  -- the pointwise bound
  have hsub : {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧
      (∀ φ : TestOn V, restrictTo V (h ω - X ω) φ = ∫ x, g x * φ x) ∧
        ∃ x ∈ K, 3 * A₀ < |g x|} ⊆
      ({ω | A₀ < κ₀ * Φ ω} ∪ {ω | A₀ < κ₀ * m * |Xc ω|}) ∪ {ω | A₀ < κ₀ * ΦX ω} := by
    rintro ω ⟨g, hg, hrep, z, hz, hAz⟩
    have hpt : ∀ y ∈ S, g y = (h ω - X ω) (radBump δ hδ.le y) / I := fun y hy => by
      rw [pair_radBump_of_harmonic hg hrep hδ (hSV y hy)]; field_simp; rfl
    have hgS : ContinuousOn g S := fun y hy =>
      (hg y (hSV y hy (mem_closedBall_self hδ.le))).1.continuousAt.continuousWithinAt
    have h1 := abs_sub_le_integral_of_harmonic V.isOpen hg hδ (hSV z (hKS z hz
      (mem_closedBall_self hδ.le))) 0
    simp only [sub_zero] at h1
    have hiS : IntegrableOn (fun y => |g y|) S := hgS.abs.integrableOn_compact hSc
    have h2 : ∫ y in closedBall z δ, |g y| ≤ ∫ y in S, |g y| :=
      setIntegral_mono_set hiS (Eventually.of_forall fun y => abs_nonneg _)
        (Eventually.of_forall (hKS z hz))
    have hiF : IntegrableOn (F ω) S := (hFc ω).continuousOn.integrableOn_compact hSc
    have hiFX : IntegrableOn (FX ω) S := (hFXc ω).continuousOn.integrableOn_compact hSc
    have h3 : ∫ y in S, |g y| ≤ ∫ y in S, (F ω y + |Xc ω| + FX ω y) / I := by
      refine setIntegral_mono_on hiS
        (((hiF.add (integrableOn_const hSc.measure_lt_top.ne)).add hiFX).div_const I)
        hSc.isClosed.measurableSet fun y hy => ?_
      rw [hpt y hy, abs_div, abs_of_pos hI]
      gcongr
      simp only [F, Xc, FX]; rw [hFeq]
      calc |(h ω - X ω) (radBump δ hδ.le y)|
          = |((h ω (radBump δ hδ.le y) - h ω ψc) + h ω ψc) - X ω (radBump δ hδ.le y)| := by
            rw [sub_apply]; ring_nf
        _ ≤ |(h ω (radBump δ hδ.le y) - h ω ψc) + h ω ψc| + |X ω (radBump δ hδ.le y)| :=
            abs_sub _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    have h4 : ∫ y in S, (F ω y + |Xc ω| + FX ω y) / I = (Φ ω + m * |Xc ω| + ΦX ω) / I := by
      have e1 : ∫ y in S, (F ω y + |Xc ω| + FX ω y) =
          (∫ y in S, (F ω y + |Xc ω|)) + ∫ y in S, FX ω y :=
        integral_add (hiF.add (integrableOn_const hSc.measure_lt_top.ne)) hiFX
      have e2 : ∫ y in S, (F ω y + |Xc ω|) = (∫ y in S, F ω y) + ∫ _ in S, |Xc ω| :=
        integral_add hiF (integrableOn_const hSc.measure_lt_top.ne)
      rw [integral_div, e1, e2, setIntegral_const, smul_eq_mul, measureReal_def]
    have h5 : 3 * A₀ < κ₀ * Φ ω + κ₀ * m * |Xc ω| + κ₀ * ΦX ω := by
      have : |g z| ≤ κ₀ * (Φ ω + m * |Xc ω| + ΦX ω) := by
        refine h1.trans ?_
        calc expNegInvGlue (δ ^ 2) / I * ∫ y in closedBall z δ, |g y|
            ≤ expNegInvGlue (δ ^ 2) / I * ((Φ ω + m * |Xc ω| + ΦX ω) / I) :=
              mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4.le))
                (div_nonneg (expNegInvGlue.nonneg _) hI.le)
          _ = _ := by rw [hκ₀]; ring
      linarith
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hc
    linarith [hc.1.1, hc.1.2, hc.2]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add hT1 hT2)) hT3).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end LQGMetric.CONF
