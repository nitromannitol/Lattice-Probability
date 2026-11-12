/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127I4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127I3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127G6
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3Sec3W2

/-!
# (L4) of D127: the white-noise model `CONFZBCoarseModel` and CONF Lemma 2.10 at `confU`
(packet P-127I, P2-HEATI)

CONF (arXiv:1905.00381, `confluence-final.tex`) C:719–742, proof of Lemma 2.10: on the white-noise
space, `h^U = h_{0,t} + h_{t,∞}` with `h_{t,∞}` continuous, measurable for the white noise at
times `> t` and positively correlated, and `h_{0,t}` independent of it (C:722–731). Here, on
`(ℕ → ℝ, stdP)` with the white noise of `WhiteNoise.exists_isWhiteNoise` and the filtration
`ℱ n = σ(W g : g supported in (4^{-n}, ∞) × ℂ)` (`GMCIdent.wnFil`), for a bounded open `U` with
`ZBHeatRepr U` ((L1), D39 at `U`) and the Hölder bound of the coarse kernels ((L2)):

* `X₀ = X₀'` is the random distribution of `exists_zbDistU_filt` ((L3), S3D127H4), measurable for
  `⨆ ℱ n`, an `IsZBExtField` by `isZBExtField_of_zbDistU`;
* `S` (level `n`, `t = 4^{-n}`) is the `ℱ n`-measurable continuous version of `wnField W U (Ioi t)`
  (`exists_coarseVersion`), with covariance `π ∫_t^∞ p_U ≥ 0` (`DZZ.cov_wnField`);
* `R = X₀ − S`, whose pairings are `√π W(K^{(0,t]}(φ 1_U))` a.s. (`uKerL2_split`,
  `ae_integral_mul_coarse`), hence independent of `ℱ n` (`GMCIdent.indep_wnSigma_compl`,
  `indep_distC_of_pairings`).

**`confZBCoarseModel_of`** is the model; **`confLem2_10AtConfU_of`** the leaf
`CONFLem2_10AtConfU` from (L1) (hypothesis `hL1`, the form of `zbHeatRepr_confU`) and (L2)
(`coarseKer_holder_confU`, S3D127G6). The degenerate parameters are handled directly:
`confU r δ z T = ∅` for `r ≤ 0`, and `= confU r 1 z ∅` (the annulus) for `r > 0 ≥ δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ Blueprint

/-- (L2): Hölder bounds for the coarse kernels `K^{(t,∞)}_x` on `U` -/
def CoarseKerHolder (U : Set ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ K α : ℝ, 0 ≤ K ∧ 0 < α ∧ ∀ x x' : ℂ,
    ‖wndKernelL2 U (Ioi t) x - wndKernelL2 U (Ioi t) x'‖ ^ 2 ≤ K * ‖x - x'‖ ^ α

lemma tendsto_cutoff_I : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 := h.pow 2
  rwa [zero_pow two_ne_zero] at h2

/-- **The white-noise model of the coarse/fine splitting on `U`** (CONF C:722–738) -/
theorem confZBCoarseModel_of {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) (hH : ZBHeatRepr U) (hK : CoarseKerHolder U) :
    CONFZBCoarseModel (toOpens U hU) := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hP := hW.isProbabilityMeasure
  set ℱ := GMCIdent.wnFil hW with hℱ
  have hm' : (⨆ n, ℱ n : MeasurableSpace (ℕ → ℝ)) ≤ MeasurableSpace.pi := iSup_le fun n => ℱ.le n
  obtain ⟨X, hXm', hXv, -⟩ := exists_zbDistU_filt hU hUR hW hm' tendsto_cutoff_I
    (fun n g hg => (GMCIdent.measurable_wnSigma (S := GMCIdent.coarseSet n) hg).mono
      (le_iSup (fun n => ℱ n) n) le_rfl)
  have hXm : Measurable X := hXm'.mono hm' le_rfl
  have hZB : IsZBExtField (toOpens U hU) X LQGDimension.ExistAsm.stdP :=
    isZBExtField_of_zbDistU hU hUR hW hH hXm hXv
  refine ⟨ℕ → ℝ, inferInstance, inferInstance, LQGDimension.ExistAsm.stdP, hP, X, X, ℱ, hZB, hXm',
    ae_eq_refl _, fun n => ?_⟩
  set t : ℝ := ((2 : ℝ)⁻¹ ^ n) ^ 2 with ht_def
  have ht : 0 < t := by positivity
  obtain ⟨K, α, hK0, hα, hF⟩ := hK t ht
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_coarseVersion hW (ℱ.le n)
    (fun x => GMCIdent.measurable_wnSigma (S := GMCIdent.coarseSet n)
      (GMCIdent.supportedIn_wndKernelL2 U measurableSet_Ioi x)) hK0 hα hF
  have hYm' : ∀ x, Measurable (Y x) := fun x => (hYm x).mono (ℱ.le n) le_rfl
  set S : (ℕ → ℝ) → C(ℂ, ℝ) := fun ω => ⟨fun x => Y x ω, hYc ω⟩ with hS
  have hSm : Measurable[ℱ n] S := measurable_mkC hYc hYm
  have hSm' : Measurable S := hSm.mono (ℱ.le n) le_rfl
  set Rf : (ℕ → ℝ) → DistC := fun ω => X ω - ofCont (S ω) with hRf
  have hRm : Measurable Rf := measurable_distOn_iff.2 fun φ => by
    simp only [hRf, ContinuousLinearMap.sub_apply]
    exact ((measurable_distOn_apply φ).comp hXm).sub ((measurable_ofCont_apply φ).comp hSm')
  -- the fine pairings
  set V : TestC → (ℕ → ℝ) → ℝ := fun φ ω =>
    Real.sqrt Real.pi * W (uKerL2 U (Ioc 0 t) (U.indicator φ)) ω with hV
  have hRV : ∀ φ, (fun ω => Rf ω φ) =ᵐ[LQGDimension.ExistAsm.stdP] V φ := by
    intro φ
    obtain ⟨C, hC⟩ := testC_abs_le φ
    obtain ⟨m1, b1, i1⟩ := indicator_props hU φ hC
    have hsplit := uKerL2_split hU hR hUR ht m1 b1 i1
    filter_upwards [hXv φ, ae_integral_mul_coarse hW hU hR hUR ht hK0 hα hF hYc hYm' hYW φ,
      hW.add_ae (uKerL2 U (Ioc 0 t) (U.indicator φ)) (uKerL2 U (Ioi t) (U.indicator φ)),
      hW.smul_ae (Real.sqrt Real.pi) (uKerL2 U (Ioi t) (U.indicator φ))] with ω e1 e2 e3 e4
    have e5 : ofCont (S ω) φ = ∫ x, φ x * Y x ω := ofCont_apply _ _
    simp only [hRf, hV, ContinuousLinearMap.sub_apply, e5, e1, e2, e4, zbProcU]
    rw [hsplit, e3]
    ring
  have hsub : Ioc 0 t ×ˢ (univ : Set ℂ) ⊆ (GMCIdent.coarseSet n)ᶜ := by
    rintro p ⟨hp, -⟩ ⟨hp', -⟩
    exact absurd hp.2 (not_le.2 hp')
  have hVind : ∀ s : Finset TestC, Indep (ℱ n)
      (MeasurableSpace.comap (fun ω (φ : s) => V φ ω) MeasurableSpace.pi)
      LQGDimension.ExistAsm.stdP := by
    intro s
    refine indep_of_indep_of_le_right (GMCIdent.indep_wnSigma_compl hW (GMCIdent.coarseSet n)).symm
      ?_
    have hmeas : Measurable[GMCIdent.wnSigma W (GMCIdent.coarseSet n)ᶜ]
        (fun ω (φ : s) => V φ ω) := by
      let _ : MeasurableSpace (ℕ → ℝ) := GMCIdent.wnSigma W (GMCIdent.coarseSet n)ᶜ
      exact measurable_pi_iff.2 fun φ => (measurable_const_mul _).comp
        (GMCIdent.measurable_wnSigma (GMCIdent.supportedIn_mono hsub
          (supportedIn_uKerL2 (U := U) measurableSet_Ioc _)))
    exact hmeas.comap_le
  refine ⟨S, Rf, ⟨hSm, hRm, indep_distC_of_pairings (ℱ.le n) hRm hRV hVind, ?_, fun x y => ?_,
    Eventually.of_forall fun ω => ?_⟩⟩
  · refine (hW.isGaussianProcess_comp fun x => Real.sqrt Real.pi • wndKernelL2 U (Ioi t) x).congr
      fun x => ?_
    filter_upwards [hYW x, hW.smul_ae (Real.sqrt Real.pi) (wndKernelL2 U (Ioi t) x)] with ω h1 h2
    rw [h2]
    exact h1.symm
  · show 0 ≤ cov[fun ω => Y x ω, fun ω => Y y ω; LQGDimension.ExistAsm.stdP]
    rw [DDDF.covariance_congr_ae (hYW x) (hYW y),
      cov_wnField hW hU hR hUR measurableSet_Ioi ht subset_rfl x y]
    exact mul_nonneg Real.pi_pos.le
      (setIntegral_nonneg measurableSet_Ioi fun s _ => killedHeat_nonneg _ _ _ _)
  · show X ω = X ω - ofCont (S ω) + ofCont (S ω)
    rw [sub_add_cancel]

end LQGMetric.CONF.ZBM
