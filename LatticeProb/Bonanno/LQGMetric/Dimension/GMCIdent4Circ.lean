/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4Circ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentMain

/-!
# Identification for the white-noise field, part 1: the circle step and the DCT step
(P2-GMCID4, D85)

Copies of `GMCIdent.setIntegral_exp_circle` and `GMCIdent.tendsto_setIntegral_areaApprox` for the
white-noise field `wnField W` (handoff/P2-GMCID3.md, items 3–5). The zero-boundary GFF `X` on
another probability space `(Ω, P)` enters only through deterministic facts (the circle variance
`−log r + hS(z,z)`, the bound on `hS(z,z)`) and through the law of its circle family
(`map_circVec_eq`):

* `pi_sq_norm_measKerL2_circle`: `π‖K_{σ_{z,r}}‖² = −log r + hS(z,z)` (from `circleCov_same`,
  `circleCov_eq_kernel` and `GMCIdent2.pi_inner_measKerL2_circle`);
* `setIntegral_exp_circle_wn`: the circle step (`avgReg_ae_eq_wn` replaces `avgReg_ae_eq` + `hC`);
* `integrable_fDens_sq_wn`: transfer of `integrable_fDens_sq` through
  `Measure.map (Prod.map wnCircVec id)` and `Measure.map_prod_map`;
* `tendsto_setIntegral_areaApprox_wn`.

Source of the argument: Berestycki (arXiv:1506.09113, §4, l. 683–687), as in `GMCIdentCirc`,
`GMCIdentDCT`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric QuantumZipper
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent4

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

/-- the white-noise variance of a circle average: `π‖K_{σ_{z,r}}‖² = −log r + hS(z,z)` -/
lemma pi_sq_norm_measKerL2_circle (hX : IsZeroBoundaryGFFOn openSquare X P) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hB : closedBall z r ⊆ openSquare) :
    Real.pi * ‖measKerL2 openSquare (Ioi 0) (foldedCircle z r)‖ ^ 2 = -Real.log r + hS z z := by
  have h := circleCov_same hX hr hr hB hB
  rw [max_self, circleCov_eq_kernel hX hr hr hB hB, ← pi_inner_measKerL2_circle hr hr hB hB,
    real_inner_self_eq_norm_sq] at h
  rw [foldedCircle_eq_of_inSq (inSq_of_closedBall hr hB) hr]
  exact h

/-- **The circle step** for the white-noise field (copy of `setIntegral_exp_circle`). -/
theorem setIntegral_exp_circle_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) (γ : ℝ) (n k : ℕ) {z : ℂ}
    (hB : closedBall z (2 * radius k) ⊆ openSquare) {B : Set Ω'}
    (hBm : MeasurableSet[wnFil hW n] B) :
    ∫ ω in B, radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (wnField W ω) k z) ∂P' =
      Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi *
        ‖measKerL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) (foldedCircle z (radius k))‖ ^ 2)) *
      ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
        W (measKerL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) (foldedCircle z (radius k))) ω)) ∂P' := by
  have hP := hW.isProbabilityMeasure
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  have hB' : closedBall z r ⊆ openSquare :=
    (closedBall_subset_closedBall (by linarith)).trans hB
  have hfc := foldedCircle_eq_of_inSq (inSq_of_closedBall hr hB') hr
  set μ := foldedCircle z r
  have hμ := foldedCircle_compl_closedBall hr hB'
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n
  have hδ : 0 < δ := by positivity
  set c : ℝ := δ ^ 2
  have hc : 0 < c := by positivity
  have hmem : MemLp (measKer openSquare (Ioi 0) μ) 2 volume := by
    rw [hfc]; exact memLp_measKer_circle hr hB'
  obtain ⟨hm₂, -⟩ := norm_measKerL2_sub_tildeKer_le hW hδ μ hμ
  have hm₁ : MemLp (measKer openSquare (Ioc 0 c) μ) 2 volume := by
    refine hmem.mono (measurable_measKer isOpen_openSquare measurableSet_Ioc μ).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hs := congrFun (measKer_split isOpen_openSquare hc μ) p
    simp only [Pi.add_apply] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (measKer_nonneg _ _ _ _),
      abs_of_nonneg (measKer_nonneg _ _ _ _), hs]
    linarith [measKer_nonneg openSquare (Ioi c) μ p]
  set K := measKerL2 openSquare (Ioi 0) μ
  set K₁ := measKerL2 openSquare (Ioc 0 c) μ
  set K₂ := measKerL2 openSquare (Ioi c) μ
  have hsplit : K = K₁ + K₂ := measKerL2_split isOpen_openSquare hc μ hm₁ hm₂
  have h₁ : SupportedIn (coarseSet n)ᶜ K₁ :=
    supportedIn_mono (fine_subset_compl_coarseSet n) (supportedIn_measKerL2 _ measurableSet_Ioc μ)
  have h₂ : SupportedIn (coarseSet n) K₂ := supportedIn_measKerL2 _ measurableSet_Ioi μ
  -- the variance identity
  have hvar : Real.pi * ‖K₁‖ ^ 2 = -Real.log r + hS z z - Real.pi * ‖K₂‖ ^ 2 := by
    have hK := pi_sq_norm_measKerL2_circle hX hr hB'
    rw [show measKerL2 openSquare (Ioi 0) (foldedCircle z r) = K from rfl, hsplit,
      @norm_add_sq_real, inner_eq_zero_of_supportedIn disjoint_compl_left h₁ h₂] at hK
    linarith
  -- conditioning on `𝓖_n`
  have hce := condExp_exp_wn hW (γ * Real.sqrt Real.pi) hsplit h₁ h₂
  have hint := integrable_exp_wn hW (γ * Real.sqrt Real.pi) K
  have hle := wnSigma_le hW (coarseSet n)
  have hlhs : (fun ω => r ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (wnField W ω) k z)) =ᵐ[P']
      fun ω => r ^ (γ ^ 2 / 2) * Real.exp (γ * Real.sqrt Real.pi * W K ω) := by
    filter_upwards [avgReg_ae_eq_wn hX hW hB] with ω h1
    rw [h1, mul_assoc, ← hfc]
  have hBm' : MeasurableSet[wnSigma W (coarseSet n)] B := hBm
  rw [setIntegral_congr_ae (hle B hBm') (hlhs.mono fun ω h _ => h), integral_const_mul,
    ← setIntegral_condExp hle hint hBm',
    setIntegral_congr_ae (hle B hBm') (hce.mono fun ω h _ => h)]
  simp_rw [Real.exp_add]
  rw [integral_mul_const]
  have hI : ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi * W K₂ ω)) ∂P' =
      ∫ ω in B, Real.exp (γ * Real.sqrt Real.pi * W K₂ ω) ∂P' := by
    simp_rw [mul_assoc]
  have hconst : r ^ (γ ^ 2 / 2) * Real.exp ((γ * Real.sqrt Real.pi) ^ 2 / 2 * ‖K₁‖ ^ 2) =
      Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi * ‖K₂‖ ^ 2)) := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
    congr 1
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    linear_combination (γ ^ 2 / 2) * hvar
  rw [hI, ← hconst]
  ring

/-- the density `f(z) r_k^{γ²/2} e^{γ h_{r_k}(z)}` as a function of the circle family -/
def fDensC (γ : ℝ) (k : ℕ) (f : ℂ → ℝ) (q : (CircIdx → ℝ) × ℂ) : ℝ :=
  f q.2 * (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (circExt q.1) k q.2))

lemma measurable_fDensC (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (fDensC γ k f) :=
  (hf.comp measurable_snd).mul (measurable_const.mul (Real.measurable_exp.comp
    (((measurable_avgReg k).comp ((measurable_circExt.comp measurable_fst).prodMk
      measurable_snd)).const_mul γ)))

/-- joint integrability of the density for the white-noise field (transfer of
`integrable_fDens_sq`) -/
theorem integrable_fDens_sq_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {s : ℝ} (hs : 0 < s) (γ : ℝ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) {k : ℕ} (hk : 4 * radius k ≤ s) :
    Integrable (fun p : Ω' × ℂ => f p.2 * sDens γ (wnField W) k p.2 p.1)
      (P'.prod (volume.restrict (sqIn s))) := by
  have hP' := hW.isProbabilityMeasure
  set ν := volume.restrict (sqIn s)
  have hSm : MeasurableSet (sqIn s) := (isClosed_sqIn s).measurableSet
  have hSf : volume (sqIn s) < ∞ := (isCompact_sqIn hs).measure_lt_top
  have hG := measurable_fDensC γ k hf
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hm' := measurable_wnCircVec hW
  have hX1 := integrable_fDens_sq hX hSm hSf subset_rfl γ hf hM hk
  have hres : P.prod ν = (P.prod volume).restrict (univ ×ˢ sqIn s) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hX2 : Integrable (fun p : Ω × ℂ => fDensC γ k f (circVec (X p.1), p.2)) (P.prod ν) := by
    refine hX1.congr ?_
    rw [hres]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod hSm)] with p hp
    simp only [fDensC, sDens, sU]
    rw [avgReg_circExt (by linarith [radius_pos k]) hp.2]
  have e1 : (circLaw P X).prod ν = (P.prod ν).map (Prod.map (fun ω => circVec (X ω)) id) := by
    rw [← Measure.map_prod_map _ _ hm measurable_id, Measure.map_id]
  have e2 : (P'.map (wnCircVec W)).prod ν = (P'.prod ν).map (Prod.map (wnCircVec W) id) := by
    rw [← Measure.map_prod_map _ _ hm' measurable_id, Measure.map_id]
  have h3 : Integrable (fDensC γ k f) ((circLaw P X).prod ν) := by
    rw [e1, integrable_map_measure hG.aestronglyMeasurable (hm.prodMap measurable_id).aemeasurable]
    exact hX2
  rw [show circLaw P X = P'.map (wnCircVec W) from map_circVec_eq hX hW, e2,
    integrable_map_measure hG.aestronglyMeasurable (hm'.prodMap measurable_id).aemeasurable] at h3
  exact h3

/-- **`E[μ_k(f) 1_B] → ∫ f · limDens`** for the white-noise field (copy of
`tendsto_setIntegral_areaApprox`). -/
theorem tendsto_setIntegral_areaApprox_wn [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ)
    {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M) {s : ℝ} (hs : 0 < s)
    (hfS : ∀ z ∉ sqIn s, f z = 0) {B : Set Ω'} (hBm : MeasurableSet[wnFil hW n] B) :
    Tendsto (fun k => ∫ ω in B, ∫ z, f z ∂(areaApprox γ (wnField W ω) k) ∂P') atTop
      (𝓝 (∫ z in sqIn s, f z * limDens W P' γ n B z)) := by
  have hP := hW.isProbabilityMeasure
  have hBm' : MeasurableSet B := wnSigma_le hW _ B hBm
  set S := sqIn s
  have hSm : MeasurableSet S := (isClosed_sqIn s).measurableSet
  have hSf : volume S < ∞ := (isCompact_sqIn hs).measure_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hs
  obtain ⟨c, hc⟩ := exists_hS_diag_le hX hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n
  have hδ : 0 < δ := by positivity
  set F : ℕ → ℂ → ℝ := fun k z => ∫ ω in B, f z * sDens γ (wnField W) k z ω ∂P'
  have hint : ∀ k, k₀ ≤ k → Integrable (fun p : Ω' × ℂ => f p.2 * sDens γ (wnField W) k p.2 p.1)
      ((P'.restrict B).prod (volume.restrict S)) := by
    intro k hk
    have h := integrable_fDens_sq_wn hX hW hs γ hf hM (hk₀ k hk)
    have e : (P'.restrict B).prod (volume.restrict S) =
        (P'.prod (volume.restrict S)).restrict (B ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]; exact h.restrict
  -- (1) Fubini
  have h1 : ∀ k, k₀ ≤ k → ∫ ω in B, ∫ z, f z ∂(areaApprox γ (wnField W ω) k) ∂P' =
      ∫ z in S, F k z := by
    intro k hk
    simp_rw [integral_areaApprox_sq (X := wnField W) γ k (sqIn_subset_H hs) hfS]
    exact integral_integral_swap (f := fun ω z => f z * sDens γ (wnField W) k z ω) (hint k hk)
  -- (2) the circle step
  have h2 : ∀ k, k₀ ≤ k → ∀ z ∈ S, F k z = f z * (Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi *
      ‖measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))‖ ^ 2)) *
      ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
        W (measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))) ω)) ∂P') := by
    intro k hk z hz
    have hr := radius_pos k
    have hB : closedBall z (2 * radius k) ⊆ openSquare :=
      closedBall_subset_of_sqIn hz (by linarith [hk₀ k hk])
    simp only [F, sDens, sU]
    rw [integral_const_mul, setIntegral_exp_circle_wn hX hW γ n k hB hBm]
  -- the bound
  have hG : ∀ k, k₀ ≤ k → ∀ z ∈ S, |Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi *
      ‖measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))‖ ^ 2)) *
      ∫ ω in B, Real.exp (γ * (Real.sqrt Real.pi *
        W (measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))) ω)) ∂P'| ≤
        Real.exp (γ ^ 2 / 2 * c) := by
    intro k hk z hz
    set K₂ := measKerL2 openSquare (Ioi (δ ^ 2)) (foldedCircle z (radius k))
    have hi : Integrable (fun ω => Real.exp (γ * (Real.sqrt Real.pi * W K₂ ω))) P' := by
      simpa [mul_assoc] using integrable_exp_wn hW (γ * Real.sqrt Real.pi) K₂
    have hE : ∫ ω, Real.exp (γ * (Real.sqrt Real.pi * W K₂ ω)) ∂P' =
        Real.exp (Real.pi * γ ^ 2 / 2 * ‖K₂‖ ^ 2) := by
      have := integral_exp_wn hW (γ * Real.sqrt Real.pi) K₂
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le] at this
      simp_rw [← mul_assoc]; rw [this]; ring_nf
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (setIntegral_nonneg hBm' fun _ _ => (Real.exp_pos _).le))]
    calc _ ≤ Real.exp (γ ^ 2 / 2 * (hS z z - Real.pi * ‖K₂‖ ^ 2)) *
          ∫ ω, Real.exp (γ * (Real.sqrt Real.pi * W K₂ ω)) ∂P' :=
          mul_le_mul_of_nonneg_left (setIntegral_le_integral hi
            (Eventually.of_forall fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = Real.exp (γ ^ 2 / 2 * hS z z) := by
          rw [hE, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hc z hz) (by positivity))
  -- (3) dominated convergence
  have hDCT : Tendsto (fun k => ∫ z in S, F k z) atTop
      (𝓝 (∫ z in S, f z * limDens W P' γ n B z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M * Real.exp (γ ^ 2 / 2 * c))
      ?_ ?_ (integrable_const _) ?_
    · filter_upwards [eventually_ge_atTop k₀] with k hk
      exact (hint k hk).aestronglyMeasurable.prod_swap.integral_prod_right'
    · filter_upwards [eventually_ge_atTop k₀] with k hk
      filter_upwards [ae_restrict_mem hSm] with z hz
      rw [h2 k hk z hz, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hM z) (hG k hk z hz) (abs_nonneg _) hM0
    · filter_upwards [ae_restrict_mem hSm] with z hz
      have hzl : ∀ᶠ k in atTop, foldedCircle z (radius k) (closedBall z (radius k))ᶜ = 0 := by
        filter_upwards [eventually_ge_atTop k₀] with k hk
        exact foldedCircle_compl_closedBall (radius_pos k)
          (closedBall_subset_of_sqIn hz (by linarith [hk₀ k hk, radius_pos k]))
      refine (tendsto_const_nhds.mul (tendsto_coarse_circle hW hδ hzl γ (hS z z) B)).congr' ?_
      filter_upwards [eventually_ge_atTop k₀] with k hk
      exact (h2 k hk z hz).symm
  refine hDCT.congr' ?_
  filter_upwards [eventually_ge_atTop k₀] with k hk
  exact (h1 k hk).symm

end GMCIdent4
end LQGMetric
