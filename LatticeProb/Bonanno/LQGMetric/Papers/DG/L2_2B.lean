/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L2_2B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L2_2

/-!
# Ding–Gwynne Lemma 2.2, (2.4): the tail bound (task P2-DG3E)

DG (`metric-comparison-final.tex`, Lemma 2.2, DG:618–640), (2.4): `P[max_K |𝔥| ≤ A] ≥
1 − a₀ e^{−a₁A²}` for the harmonic part `𝔥` of the Markov decomposition of a normalized
whole-plane GFF, `K ⊆ U` compact (DG: `K = V̄`). Route: see the docstring of `DG.L2_2`
(own argument replacing DG's IG1 Lemma 6.4 + Borell–TIS; proposed deviation DG3E-2).

* `bumpOn`, `restrictTo_bumpOn` — `radBump δ x` as a test function on `V` when `B̄(x,δ) ⊆ V`.
* **`dg_lemma22_tail`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric
namespace DG
namespace L22

open Blueprint GM LM MarkovNorm MarkovGauss MarkovZB

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `radBump δ x` as a test function on `V` -/
def bumpOn {V : Opens ℂ} {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hB : closedBall x δ ⊆ V) : TestOn V :=
  ⟨radBump δ hδ.le x, (radBump δ hδ.le x).contDiff, (radBump δ hδ.le x).hasCompactSupport, by
    refine (closure_minimal (fun y hy => ?_) isClosed_closedBall).trans hB
    by_contra hy'
    rw [mem_closedBall, dist_eq_norm, not_le] at hy'
    exact hy (radProf_eq_zero hδ.le hy'.le)⟩

lemma restrictTo_bumpOn {V : Opens ℂ} {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hB : closedBall x δ ⊆ V)
    (T : DistC) : restrictTo V T (bumpOn hδ hB) = T (radBump δ hδ.le x) := by
  show T (TestFunction.monoCLM ℝ _) = _
  congr 1
  ext y
  simp [TestFunction.monoCLM_apply, bumpOn]
  rfl

/-- the facts on the zero-boundary pairing `h^U(ψ_x)` used below -/
lemma zb_bump {hz : Ω → DistC} {V : Opens ℂ}
    (hzb : IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P) {δ : ℝ} (hδ : 0 < δ) {x : ℂ}
    (hB : closedBall x δ ⊆ V) :
    Measurable (fun ω => hz ω (radBump δ hδ.le x)) ∧
      Integrable (fun ω => hz ω (radBump δ hδ.le x)) P ∧
      ∫ ω, hz ω (radBump δ hδ.le x) ∂P = 0 := by
  have e : (fun ω => hz ω (radBump δ hδ.le x)) =
      fun ω => restrictTo V (hz ω) (bumpOn hδ hB) := by
    funext ω; rw [restrictTo_bumpOn]
  rw [e]
  exact ⟨hzb.process.measurable _,
    (hzb.process.gaussian.hasGaussianLaw_eval (bumpOn hδ hB)).memLp_two.integrable one_le_two,
    hzb.process.centered _⟩

/-- every pairing of a normalized whole-plane GFF is a centred Gaussian (`MarkovNorm`) -/
lemma normalized_pair_gauss {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (φ : TestC) :
    HasGaussianLaw (fun ω => h ω φ) P ∧ ∫ ω, h ω φ ∂P = 0 := by
  have hc := isCGauss_of_mem_gaussSpace hh.1.gaussian hh.1.centered (memLp_pair hh.1)
    (pairVec_mem_gaussSpace hh φ)
  exact ⟨hc.1.congr (pairVec_ae hh φ), by rw [← integral_congr_ae (pairVec_ae hh φ)]; exact hc.2⟩

/-- **DG Lemma 2.2, (2.4)**: for a decomposition `h = G + h^U` (a.s.) of a normalized whole-plane
GFF with `G ⫫ h^U` and `h^U|_V` a zero-boundary GFF on `V`, and every compact `K ⊆ V`, there are
`a₀, a₁ > 0` with `P[∃ z ∈ K, |𝔥(z)| > A] ≤ a₀ e^{−a₁A²}`, `𝔥` any harmonic representative of
`G|_V`. -/
theorem dg_lemma22_tail {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {V : Opens ℂ}
    {G hz : Ω → DistC} (hG : Measurable G) (hdec : ∀ᵐ ω ∂P, h ω = G ω + hz ω)
    (hind : IndepFun G hz P) (hzb : IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P)
    {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ a₀ a₁ : ℝ, 0 < a₁ ∧ ∀ A : ℝ, 0 ≤ A →
      P {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g V ∧
        (∀ φ : TestOn V, restrictTo V (G ω) φ = ∫ x, g x * φ x) ∧ ∃ z ∈ K, A < |g z|} ≤
        ENNReal.ofReal (a₀ * Real.exp (-a₁ * A ^ 2)) := by
  rcases K.eq_empty_or_nonempty with hK0 | ⟨c, hc⟩
  · refine ⟨0, 1, one_pos, fun A _ => ?_⟩
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
  set B := (|radK δ ρ| + |vc| + 1) * (κ₀ * m) ^ 2 / 2 + 1 with hBdef
  have hB : 0 < B := by positivity
  have hBle : ∀ (M t : ℝ), M ≤ |radK δ ρ| + |vc| + 1 →
      M * (t * κ₀ * m) ^ 2 / 2 ≤ B * t ^ 2 := by
    intro M t hM
    have h1 := mul_le_mul_of_nonneg_right hM (sq_nonneg (t * κ₀ * m))
    have e : B * t ^ 2 = (|radK δ ρ| + |vc| + 1) * (t * κ₀ * m) ^ 2 / 2 + t ^ 2 := by
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
    exact hBle _ t (by linarith [le_abs_self (radK δ ρ), abs_nonneg vc])
  have hT2 : ∀ A : ℝ, 0 ≤ A → P {ω | A < κ₀ * m * |Xc ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / (4 * B)) * A ^ 2)) := by
    refine tail_of_lintegral_exp ((continuous_abs.measurable.comp hXcm).const_mul (κ₀ * m)) hB fun t _ => ?_
    have := hmomC (t * κ₀ * m)
    simp_rw [← mul_assoc]
    refine this.trans ?_
    gcongr
    exact hBle _ t (by linarith [le_abs_self vc, abs_nonneg (radK δ ρ)])
  -- the pointwise bound
  refine ⟨4, 1 / (16 * B), by positivity, fun A hA => ?_⟩
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

end L22
end DG
end LQGMetric
