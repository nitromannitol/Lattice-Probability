/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L35B7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B6
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2B

/-!
# DG Lemma 2.2 (2.4) with constants uniform in the field (task P2-CONF35b)

Ding–Gwynne (`metric-comparison-final.tex`, Lemma 2.2, DG:618–640), (2.4), as formalized in
`DG.L22.dg_lemma22_tail` (Papers/DG/L2_2B.lean, task P2-DG3E). The proof there produces the
constants `a₀ = 4`, `a₁ = 1/(16B)` with `B` depending only on `K`, `V` and the variance
`Var[h(ψ_c)]` of one fixed pairing; here the same proof (copied, with the quantifiers reordered)
states this dependence: `∃ ψ_c, ∀ v, ∃ a₁, ∀` fields with `Var[h(ψ_c)] ≤ v`. Used for the
uniformity over fields in `CONFHarmTailN` (CONF C:1170–1172).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM LM MarkovNorm MarkovGauss MarkovZB DG DG.L22

/-- **`DG.L22.dg_lemma22_tail` with uniform constants** -/
theorem dg_tail_unif {V : Opens ℂ} {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ ψc : TestC, ∀ v : ℝ, ∃ a₁ : ℝ, 0 < a₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h G hz : Ω → DistC}, IsNormalizedWPGFF h P → Measurable G →
        (∀ᵐ ω ∂P, h ω = G ω + hz ω) → IndepFun G hz P →
        IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P →
        Var[fun ω => h ω ψc; P] ≤ v → ∀ A : ℝ, 0 ≤ A →
        P {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧
          (∀ φ : TestOn V, restrictTo V (G ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ≤
          ENNReal.ofReal (4 * Real.exp (-a₁ * A ^ 2)) := by
  rcases K.eq_empty_or_nonempty with hK0 | ⟨c, hc⟩
  · refine ⟨0, fun _ => ⟨1, one_pos, fun {Ω} _ {P} _ {h G hz} _ _ _ _ _ _ A _ => ?_⟩⟩
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
  -- the two random variables
  set ψc := radBump δ hδ.le c
  refine ⟨ψc, fun v => ?_⟩
  set B := (|radK δ ρ| + |v| + 1) * (κ₀ * m) ^ 2 / 2 + 1 with hBdef
  have hB : 0 < B := by positivity
  refine ⟨1 / (16 * B), by positivity, ?_⟩
  intro Ω _ P _ h G hz hh hG hdec hind hzb hv A hA
  set Xc : Ω → ℝ := fun ω => G ω ψc
  set F : Ω → ℂ → ℝ := fun ω y => |G ω (radDiff hδ.le y c).1|
  set Φ : Ω → ℝ := fun ω => ∫ y in S, F ω y
  have hFeq : ∀ ω y, G ω (radDiff hδ.le y c).1 = G ω (radBump δ hδ.le y) - G ω ψc := by
    intro ω y; simp only [radDiff, map_sub, ψc]
  have hFc : ∀ ω, Continuous (F ω) := fun ω => by
    have : F ω = fun y => |G ω (radBump δ hδ.le y) - G ω ψc| := by
      funext y; simp only [F]; rw [hFeq]
    rw [this]
    exact (((map_continuous (G ω)).comp (continuous_radBump δ hδ.le)).sub continuous_const).abs
  have hFm : Measurable (Function.uncurry F) := by
    have h1 := (measurable_apply_radBump δ hδ.le).comp
      ((hG.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun p : Ω × ℂ => G p.1 ψc :=
      (measurable_eval_distC ψc).comp (hG.comp measurable_fst)
    have : Function.uncurry F = fun p : Ω × ℂ => |G p.1 (radBump δ hδ.le p.2) - G p.1 ψc| := by
      funext p; simp only [Function.uncurry, F]; rw [hFeq]
    rw [this]; exact continuous_abs.measurable.comp (h1.sub h2)
  have hXcm : Measurable Xc := (measurable_eval_distC ψc).comp hG
  have hΦm : Measurable Φ :=
    (hFm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable
  -- moments of the pieces
  have hmomD : ∀ y ∈ S, ∀ a : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * F ω y)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (radK δ ρ * a ^ 2 / 2)) := by
    intro y hy a
    obtain ⟨hZ1m, hZ1i, hZ10⟩ := zb_bump hzb hδ (hSV y hy)
    obtain ⟨hZ2m, hZ2i, hZ20⟩ := zb_bump hzb hδ (hSV c hcS)
    set φ := radDiff hδ.le y c
    have hYg : HasGaussianLaw (fun ω => h ω φ.1) P := hh.1.gaussian.hasGaussianLaw_eval φ
    have hvar : Var[fun ω => h ω φ.1; P] = logCov φ.1 φ.1 := by
      have hmh : AEMeasurable (fun ω => h ω φ.1) P :=
        ((measurable_eval_distC φ.1).comp hh.1.measurable).aemeasurable
      rw [← covariance_self hmh]
      exact hh.1.covariance_eq φ φ
    have hZeq : (fun ω => hz ω φ.1) =
        fun ω => hz ω (radBump δ hδ.le y) - hz ω (radBump δ hδ.le c) := by
      funext ω; simp only [φ, radDiff, map_sub]
    have key := lintegral_exp_abs_le (X := fun ω => G ω φ.1) (Z := fun ω => hz ω φ.1)
      ((measurable_eval_distC φ.1).comp hG) (by rw [hZeq]; exact hZ1m.sub hZ2m)
      (hind.comp (measurable_eval_distC φ.1) (measurable_eval_distC φ.1))
      (by rw [hZeq]; exact hZ1i.sub hZ2i)
      (by rw [hZeq, integral_sub hZ1i hZ2i, hZ10, hZ20, sub_zero]) hYg (hh.1.centered φ)
      (by filter_upwards [hdec] with ω hω; rw [hω]; rfl) a
    refine key.trans ?_
    rw [hvar]
    gcongr
    exact logCov_radDiff_le hδ hρ0 (by rw [← dist_eq_norm]; exact hρ hy)
  set vc := Var[fun ω => h ω ψc; P]
  have hmomC : ∀ a : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |Xc ω|)) ∂P ≤
      2 * ENNReal.ofReal (Real.exp (vc * a ^ 2 / 2)) := by
    intro a
    obtain ⟨hZm, hZi, hZ0⟩ := zb_bump hzb hδ (hSV c hcS)
    obtain ⟨hYg, hY0⟩ := normalized_pair_gauss hh ψc
    exact lintegral_exp_abs_le hXcm hZm (hind.comp (measurable_eval_distC ψc)
      (measurable_eval_distC ψc)) hZi hZ0 hYg hY0
      (by filter_upwards [hdec] with ω hω; rw [hω]; rfl) a
  -- the common sub-Gaussian constant
  have hBle : ∀ (M t : ℝ), M ≤ |radK δ ρ| + |v| + 1 →
      M * (t * κ₀ * m) ^ 2 / 2 ≤ B * t ^ 2 := by
    intro M t hM
    have h1 := mul_le_mul_of_nonneg_right hM (sq_nonneg (t * κ₀ * m))
    have e : B * t ^ 2 = (|radK δ ρ| + |v| + 1) * (t * κ₀ * m) ^ 2 / 2 + t ^ 2 := by
      rw [hBdef]; ring
    rw [e]; nlinarith [sq_nonneg t]
  have hT1 : ∀ A : ℝ, 0 ≤ A → P {ω | A < κ₀ * Φ ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / (4 * B)) * A ^ 2)) := by
    refine tail_of_lintegral_exp (hΦm.const_mul κ₀) hB fun t _ => ?_
    have := lintegral_exp_setIntegral_le hSc hS0 hFc hFm hmomD (t * κ₀)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    rw [← hm]
    exact hBle _ t (by linarith [le_abs_self (radK δ ρ), abs_nonneg v])
  have hT2 : ∀ A : ℝ, 0 ≤ A → P {ω | A < κ₀ * m * |Xc ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / (4 * B)) * A ^ 2)) := by
    refine tail_of_lintegral_exp ((continuous_abs.measurable.comp hXcm).const_mul (κ₀ * m)) hB fun t _ => ?_
    have := hmomC (t * κ₀ * m)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    exact hBle _ t (by linarith [hv, le_abs_self v, abs_nonneg (radK δ ρ)])
  -- the pointwise bound
  have hsub : {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧
      (∀ φ : TestOn V, restrictTo V (G ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ⊆
      {ω | A / 2 < κ₀ * Φ ω} ∪ {ω | A / 2 < κ₀ * m * |Xc ω|} := by
    rintro ω ⟨g, hg, hrep, z, hz, hAz⟩
    have hpt : ∀ y ∈ S, g y = G ω (radBump δ hδ.le y) / I := fun y hy => by
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
    have h3 : ∫ y in S, |g y| ≤ ∫ y in S, (F ω y + |Xc ω|) / I := by
      refine setIntegral_mono_on hiS ((hiF.add (integrableOn_const hSc.measure_lt_top.ne)).div_const I)
        hSc.isClosed.measurableSet fun y hy => ?_
      rw [hpt y hy, abs_div, abs_of_pos hI]
      gcongr
      simp only [F, Xc]; rw [hFeq]
      calc |G ω (radBump δ hδ.le y)| = |(G ω (radBump δ hδ.le y) - G ω ψc) + G ω ψc| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : ∫ y in S, (F ω y + |Xc ω|) / I = (Φ ω + m * |Xc ω|) / I := by
      rw [integral_div, integral_add hiF (integrableOn_const hSc.measure_lt_top.ne),
        setIntegral_const, smul_eq_mul, measureReal_def]
    have h5 : A < κ₀ * Φ ω + κ₀ * m * |Xc ω| := by
      have : |g z| ≤ κ₀ * (Φ ω + m * |Xc ω|) := by
        refine h1.trans ?_
        calc expNegInvGlue (δ ^ 2) / I * ∫ y in closedBall z δ, |g y|
            ≤ expNegInvGlue (δ ^ 2) / I * ((Φ ω + m * |Xc ω|) / I) :=
              mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4.le))
                (div_nonneg (expNegInvGlue.nonneg _) hI.le)
          _ = _ := by rw [hκ₀]; ring
      linarith
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hc
    linarith [hc.1, hc.2]
  have hA2 : 0 ≤ A / 2 := by linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hT1 _ hA2) (hT2 _ hA2)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have : -(1 / (4 * B)) * (A / 2) ^ 2 = -(1 / (16 * B)) * A ^ 2 := by field_simp; ring
  rw [this]; ring



end LQGMetric.CONF
