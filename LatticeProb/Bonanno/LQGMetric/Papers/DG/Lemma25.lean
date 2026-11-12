/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Lemma25 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Coupling
import LatticeProb.Bonanno.LQGMetric.Papers.DG.LFPPMeas
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss

/-!
# DG Lemma 2.5 (monotonicity of re-scaled LFPP distances)

Ding–Gwynne, arXiv:1807.01072, Lemma 2.5 (`lem-lfpp-mono`, DG:736–745): for `0 < ξ < ξ̃` there
is a coupling of two whole-plane GFFs `h =ᵈ h̃` such that
`P[δ^{ξ̃²/2} D^{ξ̃,δ}_{h̃}(z,w;U) ≤ C δ^{ξ²/2} D^{ξ,δ}_h(z,w;U)] ≥ 1 − O_C(1/C)` uniformly in `δ`.
Proof (DG:747–770), followed step by step: `h̃ = ξ̃⁻¹(ξ h + √(ξ̃²−ξ²) h′)` (`Coupling.lean`);
for a path `P` (chosen for `h`), `E[δ^{ξ̃²/2} ∫ e^{ξ̃ h̃_δ(P)} |P′| | h] = δ^{ξ̃²/2} ∫ e^{ξ h_δ(P)}
|P′| E[e^{√(ξ̃²−ξ²) h′_δ(P)}] ≤ c δ^{ξ²/2} ∫ e^{ξ h_δ(P)} |P′|` (`Lemma25Gauss.lean`), then infimum
over `P` and Markov's inequality. The conditional expectation given `h` is realized as the
inner integral over the second factor of `Ω × Ω` (Tonelli), and the infimum over paths is taken
after integrating (no measurable path selection is needed).

Scope (proposed deviation DG-B4): proved for LQGDimension's domain `U = (−2,2)²`, `z = 0`,
`w = 1` (the only case used) and `δ ∈ (0,1)` (DG's "uniform in δ" is for small `δ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi hf]
  · rw [integral_undef hi]; simp

lemma aemeasurable_marginal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℝ → ℂ → Ω → ℝ} (hY : LQGDimension.IsGFFCircleAverage Y μ) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) : AEMeasurable (Y δ z) μ :=
  ((LQGDimension.SegLaw.isGaussianProcess_slice hY hδ).hasGaussianLaw_eval z).aemeasurable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}

/-- The constant `e^{s² log 4}` with `s² = ξ̃² − ξ²`. -/
def lem25K (ξ ξt : ℝ) : ℝ := Real.exp ((ξt ^ 2 - ξ ^ 2) * Real.log 4)

/-- One path: `E′[e^{ξ̃ h̃}-length of P] ≤ K δ^{−s²/2} (e^{ξ h}-length of P)` (DG:752–766). -/
lemma lintegral_coupled_length_le (hG : LQGDimension.IsGFFCircleAverage hc P) {ξ ξt : ℝ}
    (h0 : 0 < ξ) (h1 : ξ ≤ ξt) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ω : Ω) {γ : ℝ → ℂ}
    (hγ : LQGDimension.IsAdmissiblePath γ) :
    ∫⁻ ω', ENNReal.ofReal (LQGDimension.lfppLength ξt
        (fun z => coupledCA ξ ξt hc δ z (ω, ω')) γ) ∂P ≤
      ENNReal.ofReal (lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) *
        LQGDimension.lfppLength ξ (fun z => hc δ z ω) γ) := by
  have := hG.isProbabilityMeasure
  have hξt : 0 < ξt := h0.trans_le h1
  set s := √(ξt ^ 2 - ξ ^ 2) with hs_def
  have hs2 : s ^ 2 = ξt ^ 2 - ξ ^ 2 := Real.sq_sqrt (by nlinarith)
  set a : ℝ → ℝ := fun t => Real.exp (ξ * hc δ (γ t) ω) * ‖deriv γ t‖ with ha_def
  set b : ℝ → Ω → ℝ := fun t ω' => Real.exp (s * hc δ (γ t) ω') with hb_def
  set c : ℝ := lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) with hc_def
  have ha0 : ∀ t, 0 ≤ a t := fun t => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  -- pointwise factorization `e^{ξ̃ h̃} |γ'| = a · b`
  have hfac : ∀ ω' t, Real.exp (ξt * coupledCA ξ ξt hc δ (γ t) (ω, ω')) * ‖deriv γ t‖ =
      a t * b t ω' := by
    intro ω' t
    simp only [coupledCA, ha_def, hb_def]
    have : ξt * (ξ / ξt * hc δ (γ t) ω + s / ξt * hc δ (γ t) ω') =
        ξ * hc δ (γ t) ω + s * hc δ (γ t) ω' := by field_simp
    rw [this, Real.exp_add]; ring
  -- measurability of `a` on `(0,1]`
  have hγm : AEMeasurable γ (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hγ.continuousOn.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hcont : ∀ ω₀, Continuous fun z => hc δ z ω₀ := fun ω₀ => hG.continuous δ hδ ω₀
  have haM : AEMeasurable a (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have hc1 : ContinuousOn (fun t => Real.exp (ξ * hc δ (γ t) ω)) (Ioc 0 1) :=
      Real.continuous_exp.comp_continuousOn ((continuous_const.mul (hcont ω)).comp_continuousOn
        (hγ.continuousOn.mono Ioc_subset_Icc_self))
    exact (hc1.aemeasurable measurableSet_Ioc).mul (measurable_deriv γ).norm.aemeasurable
  -- joint measurability of `(ω', t) ↦ b t ω'`
  have hG2 : AEMeasurable (fun p : Ω × ℝ => hc δ (γ p.2) p.1) (P.prod (volume.restrict (Ioc 0 1))) := by
    have hT := aemeasurable_toContMap (μ := P) (hc δ) (fun z => aemeasurable_marginal hG hδ z) hcont
    have hpair : AEMeasurable (fun p : Ω × ℝ => (toContMap (hc δ) hcont p.1, γ p.2))
        (P.prod (volume.restrict (Ioc 0 1))) :=
      (hT.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        (hγm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact continuous_eval.measurable.comp_aemeasurable hpair
  have hF : AEMeasurable (Function.uncurry fun (ω' : Ω) (t : ℝ) =>
      ENNReal.ofReal (a t) * ENNReal.ofReal (b t ω')) (P.prod (volume.restrict (Ioc 0 1))) := by
    refine ((ENNReal.measurable_ofReal.comp_aemeasurable
      (haM.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))).mul ?_
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.continuous_exp.measurable.comp_aemeasurable (hG2.const_mul s))
  -- the Gaussian bound at each `t ∈ (0,1]`
  have hgauss : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ ω', ENNReal.ofReal (b t ω') ∂P ≤ ENNReal.ofReal c := by
    intro t ht
    rw [hb_def]; dsimp only
    rw [lintegral_exp_circleAvg hG hδ (γ t) s]
    refine ENNReal.ofReal_le_ofReal ?_
    have h3 := LQGDimension.LowerAsm.norm_le_three_of_mem_U' (hγ.mapsTo (Ioc_subset_Icc_self ht))
    have hv := gffCircleCov_self_le hδ hδ1 h3
    have hle : LQGDimension.gffCircleCov δ (γ t) δ (γ t) * s ^ 2 / 2 ≤
        (-Real.log δ + 2 * Real.log 4) * s ^ 2 / 2 := by
      have : 0 ≤ s ^ 2 := sq_nonneg s
      nlinarith
    refine (Real.exp_le_exp.2 hle).trans (le_of_eq ?_)
    rw [hc_def, lem25K, Real.rpow_def_of_pos hδ, ← Real.exp_add, hs2]
    ring_nf
  -- integrability of `a` on `(0,1]`
  have haI : IntegrableOn a (Ioc 0 1) := by
    have hD := LQGDimension.LowerAsm.deriv_intervalIntegrable' hγ
    have hc1 : ContinuousOn (fun t => Real.exp (ξ * hc δ (γ t) ω)) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul (hcont ω)).comp_continuousOn hγ.continuousOn)
    have := (hD.norm.continuousOn_mul hc1)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
  calc ∫⁻ ω', ENNReal.ofReal (LQGDimension.lfppLength ξt
          (fun z => coupledCA ξ ξt hc δ z (ω, ω')) γ) ∂P
      ≤ ∫⁻ ω', (∫⁻ t in Ioc 0 1, ENNReal.ofReal (a t) * ENNReal.ofReal (b t ω')) ∂P := by
        refine lintegral_mono fun ω' => ?_
        rw [LQGDimension.lfppLength, intervalIntegral.integral_of_le zero_le_one]
        refine (ofReal_integral_le_lintegral (ae_of_all _ fun t =>
          mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).trans (le_of_eq ?_)
        refine lintegral_congr fun t => ?_
        rw [hfac ω' t, ENNReal.ofReal_mul (ha0 t)]
    _ = ∫⁻ t in Ioc 0 1, ∫⁻ ω', ENNReal.ofReal (a t) * ENNReal.ofReal (b t ω') ∂P :=
        lintegral_lintegral_swap hF
    _ = ∫⁻ t in Ioc 0 1, ENNReal.ofReal (a t) * ∫⁻ ω', ENNReal.ofReal (b t ω') ∂P := by
        refine lintegral_congr fun t => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ t in Ioc 0 1, ENNReal.ofReal (a t) * ENNReal.ofReal c :=
        setLIntegral_mono' measurableSet_Ioc fun t ht => by gcongr; exact hgauss t ht
    _ = ENNReal.ofReal (∫ t in Ioc 0 1, a t) * ENNReal.ofReal c := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal haI (ae_of_all _ ha0)]
    _ = ENNReal.ofReal (c * LQGDimension.lfppLength ξ (fun z => hc δ z ω) γ) := by
        rw [LQGDimension.lfppLength, intervalIntegral.integral_of_le zero_le_one, mul_comm c,
          ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_Ioc fun t _ => ha0 t)]

/-- Infimum over paths (DG:766–768): `E′[D^{ξ̃}_{h̃}] ≤ K δ^{−s²/2} D^ξ_h`. -/
lemma lintegral_coupled_dist_le (hG : LQGDimension.IsGFFCircleAverage hc P) {ξ ξt : ℝ}
    (h0 : 0 < ξ) (h1 : ξ ≤ ξt) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ω : Ω) :
    ∫⁻ ω', ENNReal.ofReal (LQGDimension.lfppDistance ξt
        (fun z => coupledCA ξ ξt hc δ z (ω, ω'))) ∂P ≤
      ENNReal.ofReal (lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) *
        LQGDimension.lfppDistance ξ (fun z => hc δ z ω)) := by
  set c := lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) with hc_def
  have hc0 : 0 < c := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hδ _)
  set A := ∫⁻ ω', ENNReal.ofReal (LQGDimension.lfppDistance ξt
        (fun z => coupledCA ξ ξt hc δ z (ω, ω'))) ∂P
  have hpath : ∀ γ : {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ},
      A ≤ ENNReal.ofReal (c * LQGDimension.lfppLength ξ (fun z => hc δ z ω) γ.1) := fun γ =>
    (lintegral_mono fun ω' => ENNReal.ofReal_le_ofReal (ciInf_le (bddBelow_ld _ _) γ)).trans
      (lintegral_coupled_length_le hG h0 h1 hδ hδ1 ω γ.2)
  have : Nonempty {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ} :=
    ⟨⟨_, LQGDimension.LowerAsm.admissible_ofReal⟩⟩
  have hAfin : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hpath ⟨_, LQGDimension.LowerAsm.admissible_ofReal⟩)
  have hle : A.toReal / c ≤ LQGDimension.lfppDistance ξ (fun z => hc δ z ω) := by
    refine le_ciInf fun γ => ?_
    rw [div_le_iff₀ hc0]
    have := ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hc0.le (lfppLength_nonneg _ _ _)) (hpath γ)
    linarith
  rw [div_le_iff₀ hc0] at hle
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-- **DG Lemma 2.5** (`lem-lfpp-mono`, DG:736–745), for `U = (−2,2)²`, `z = 0`, `w = 1`: under
the coupling `h̃ = ξ̃⁻¹(ξh + √(ξ̃²−ξ²)h′)` on `Ω × Ω`, for all `δ ∈ (0,1)` and `C > 0`,
`P[C δ^{ξ²/2} D^{ξ,δ}_h < δ^{ξ̃²/2} D^{ξ̃,δ}_{h̃}] ≤ K/C`. -/
theorem dg_lemma25 (hG : LQGDimension.IsGFFCircleAverage hc P) {ξ ξt : ℝ} (h0 : 0 < ξ)
    (h1 : ξ ≤ ξt) :
    ∃ K : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ C : ℝ, 0 < C →
      (P.prod P) {p | C * δ ^ (ξ ^ 2 / 2) *
          LQGDimension.lfppDistance ξ (fun z => fstCA hc δ z p) <
        δ ^ (ξt ^ 2 / 2) * LQGDimension.lfppDistance ξt (fun z => coupledCA ξ ξt hc δ z p)} ≤
        ENNReal.ofReal (K / C) := by
  have := hG.isProbabilityMeasure
  refine ⟨lem25K ξ ξt, fun δ hδ C hC => ?_⟩
  have hδ0 := hδ.1
  have hG1 := isGFFCircleAverage_fstCA hG
  have hG2 := isGFFCircleAverage_coupledCA hG h0 h1
  set X1 : Ω × Ω → ℝ := fun p => LQGDimension.lfppDistance ξ (fun z => fstCA hc δ z p)
  set X2 : Ω × Ω → ℝ := fun p =>
    LQGDimension.lfppDistance ξt (fun z => coupledCA ξ ξt hc δ z p)
  have hX1 : ∀ p, 0 < X1 p := fun p =>
    LQGDimension.LowerAsm.lfppDistance_pos ξ (hG1.continuous δ hδ0 p)
  set D : Ω × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (C * δ ^ (ξ ^ 2 / 2) * X1 p)
  set N : Ω × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (δ ^ (ξt ^ 2 / 2) * X2 p)
  have hDpos : ∀ p, 0 < C * δ ^ (ξ ^ 2 / 2) * X1 p := fun p =>
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hδ0 _)) (hX1 p)
  have hD0 : ∀ p, D p ≠ 0 := fun p => (ENNReal.ofReal_pos.2 (hDpos p)).ne'
  have hsub : {p | C * δ ^ (ξ ^ 2 / 2) * X1 p < δ ^ (ξt ^ 2 / 2) * X2 p} ⊆
      {p | 1 ≤ N p / D p} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    rw [ENNReal.le_div_iff_mul_le (Or.inl (hD0 p)) (Or.inl ENNReal.ofReal_ne_top), one_mul]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hm1 : AEMeasurable X1 (P.prod P) := aemeasurable_lfppDistance ξ (fun z => fstCA hc δ z)
    (fun z => aemeasurable_marginal hG1 hδ0 z) (fun p => hG1.continuous δ hδ0 p)
  have hm2 : AEMeasurable X2 (P.prod P) := aemeasurable_lfppDistance ξt
    (fun z => coupledCA ξ ξt hc δ z) (fun z => aemeasurable_marginal hG2 hδ0 z)
    (fun p => hG2.continuous δ hδ0 p)
  have hY : AEMeasurable (fun p => N p / D p) (P.prod P) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable (hm2.const_mul _)).div
      (ENNReal.measurable_ofReal.comp_aemeasurable (hm1.const_mul _))
  have hMarkov := mul_meas_ge_le_lintegral₀ hY 1
  rw [one_mul] at hMarkov
  refine (measure_mono hsub).trans (hMarkov.trans ?_)
  rw [lintegral_prod _ hY]
  have hinner : ∀ ω, ∫⁻ ω', N (ω, ω') / D (ω, ω') ∂P ≤ ENNReal.ofReal (lem25K ξ ξt / C) := by
    intro ω
    have hDω : ∀ ω', D (ω, ω') = D (ω, ω) := fun _ => rfl
    simp only [hDω, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hD0 (ω, ω)))]
    have hN : ∫⁻ ω', N (ω, ω') ∂P ≤ ENNReal.ofReal (δ ^ (ξt ^ 2 / 2) *
        (lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) *
          LQGDimension.lfppDistance ξ (fun z => hc δ z ω))) := by
      simp only [N, X2]
      simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ0.le _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (lintegral_coupled_dist_le hG h0 h1 hδ0 hδ.2.le ω)
    have hexp : δ ^ (ξt ^ 2 / 2) * (lem25K ξ ξt * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) *
        LQGDimension.lfppDistance ξ (fun z => hc δ z ω)) =
        lem25K ξ ξt * δ ^ (ξ ^ 2 / 2) * X1 (ω, ω) := by
      have : δ ^ (ξt ^ 2 / 2) * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2)) = δ ^ (ξ ^ 2 / 2) := by
        rw [← Real.rpow_add hδ0]; congr 1; ring
      calc _ = lem25K ξ ξt * (δ ^ (ξt ^ 2 / 2) * δ ^ (-((ξt ^ 2 - ξ ^ 2) / 2))) *
            LQGDimension.lfppDistance ξ (fun z => hc δ z ω) := by ring
        _ = _ := by rw [this]; rfl
    rw [hexp] at hN
    refine (mul_le_mul' hN le_rfl).trans (le_of_eq ?_)
    rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (hDpos (ω, ω))]
    congr 1
    have := hX1 (ω, ω)
    have := Real.rpow_pos_of_pos hδ0 (ξ ^ 2 / 2)
    field_simp
  calc ∫⁻ ω, ∫⁻ ω', N (ω, ω') / D (ω, ω') ∂P ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (lem25K ξ ξt / C) ∂P :=
        lintegral_mono hinner
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end DG
end LQGMetric
